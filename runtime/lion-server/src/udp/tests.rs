use super::*;
use std::future::{poll_fn, Future};

fn run(future: impl Future<Output = ()>) {
    lion::Runtime::new().unwrap().block_on(async {
        lion::time::timeout(Duration::from_secs(10), future)
            .await
            .expect("UDP transport stalled");
    });
}

fn localhost() -> SocketAddr {
    SocketAddr::from((Ipv4Addr::LOCALHOST, 0))
}

fn wire(destination: SocketAddr, bytes: Vec<u8>) -> WirePacket {
    WirePacket {
        peer: endpoint(destination),
        bytes,
    }
}

async fn flush(transport: &mut UdpTransport) -> Vec<(SocketAddr, i32)> {
    let mut dropped = Vec::new();
    while !transport.pending.is_empty() || !transport.frames.is_empty() {
        match poll_fn(|cx| transport.poll_send(cx)).await.unwrap() {
            SendOutcome::Sent => {}
            SendOutcome::Dropped { peer, error } => {
                dropped.push((peer, error.raw_os_error().unwrap()))
            }
        }
        transport.drain_recycled().for_each(drop);
        lion::task::yield_now().await;
    }
    dropped
}

#[test]
fn oversized_member_message_crosses_udp_without_changing_ordinary_datagrams() {
    run(async {
        let mut receiver = UdpTransport::bind(localhost(), &[]).unwrap();
        let destination = receiver.local_addr().unwrap();
        let mut sender = UdpTransport::bind(localhost(), &[endpoint(destination)]).unwrap();
        let source = sender.local_addr().unwrap();
        receiver.reassembly.members.insert(source);
        let large: Vec<u8> = (0..180_001).map(|index| (index * 17 + 3) as u8).collect();
        sender
            .enqueue(wire(destination, b"before".to_vec()))
            .unwrap();
        sender.enqueue(wire(destination, large.clone())).unwrap();
        sender
            .enqueue(wire(destination, b"after".to_vec()))
            .unwrap();
        let mut packets: Vec<_> = (0..MAX_BATCH_SIZE).map(|_| Datagram::default()).collect();
        let mut complete = Vec::new();
        while complete.len() < 3 {
            let count = poll_fn(|cx| {
                if let Poll::Ready(result) = receiver.poll_recv(cx, &mut packets) {
                    return Poll::Ready(Some(result.unwrap()));
                }
                match sender.poll_send(cx) {
                    Poll::Ready(Ok(SendOutcome::Sent)) => Poll::Ready(None),
                    Poll::Ready(Ok(SendOutcome::Dropped { error, .. })) => panic!("{error}"),
                    Poll::Ready(Err(error)) => panic!("{error}"),
                    Poll::Pending => Poll::Pending,
                }
            })
            .await;
            if let Some(count) = count {
                for packet in &mut packets[..count] {
                    if let Some(message) = receiver.decode(packet, Instant::now()).unwrap() {
                        assert_eq!(message.peer, endpoint(source));
                        complete.push(message.bytes);
                    }
                }
            }
            sender.drain_recycled().for_each(drop);
            lion::task::yield_now().await;
        }
        assert_eq!(complete, [b"before".to_vec(), large, b"after".to_vec()]);
        assert_eq!(receiver.reassembly.retained_bytes, 0);
    });
}

#[test]
fn packet_error_preserves_sent_prefix_and_delivers_following_packet() {
    run(async {
        let mut receiver = BatchUdp::bind(localhost()).unwrap();
        let destination = receiver.local_addr().unwrap();
        let mut sender = UdpTransport::bind(localhost(), &[]).unwrap();
        let invalid = localhost(); // Linux rejects UDP destination port zero.
        sender
            .enqueue(wire(destination, b"before".to_vec()))
            .unwrap();
        sender.enqueue(wire(invalid, b"rejected".to_vec())).unwrap();
        sender
            .enqueue(wire(destination, b"after".to_vec()))
            .unwrap();
        assert_eq!(flush(&mut sender).await, [(invalid, libc::EINVAL)]);
        let mut received = [Datagram::default(), Datagram::default()];
        let mut count = 0;
        while count < 2 {
            count += receiver.recv_batch(&mut received[count..]).await.unwrap();
        }
        assert_eq!(received[0].bytes, b"before");
        assert_eq!(received[1].bytes, b"after");
        poll_fn(|cx| {
            assert!(receiver.poll_recv_batch(cx, &mut received).is_pending());
            Poll::Ready(())
        })
        .await;
    });
}

fn fragment(
    peer: SocketAddr,
    id: [u8; 16],
    total: usize,
    offset: usize,
    payload: &[u8],
) -> Datagram {
    let mut bytes = MAGIC.to_vec();
    bytes.extend_from_slice(&id);
    bytes.extend_from_slice(&(total as u32).to_be_bytes());
    bytes.extend_from_slice(&(offset as u32).to_be_bytes());
    bytes.extend_from_slice(payload);
    Datagram::new(peer, bytes)
}

fn fragments(peer: SocketAddr, id: [u8; 16], bytes: &[u8]) -> Vec<Datagram> {
    bytes
        .chunks(FRAGMENT_BYTES)
        .enumerate()
        .map(|(index, part)| fragment(peer, id, bytes.len(), index * FRAGMENT_BYTES, part))
        .collect()
}

#[test]
fn reassembly_handles_reordering_duplicates_and_separate_peer_identities() {
    let peers = [
        SocketAddr::from((Ipv4Addr::LOCALHOST, 42001)),
        SocketAddr::from((Ipv4Addr::LOCALHOST, 42002)),
    ];
    let mut receiver = Reassembly::new(peers.into_iter().collect());
    let bytes: Vec<_> = (0..70_013).map(|index| (index * 13) as u8).collect();
    let second = vec![0x34; bytes.len()];
    let mut first_fragments = fragments(peers[0], [1; 16], &bytes);
    let mut second_fragments = fragments(peers[1], [1; 16], &second);
    let now = Instant::now();
    let mut delivered = Vec::new();
    for (a, b) in first_fragments
        .iter_mut()
        .rev()
        .zip(second_fragments.iter_mut())
    {
        for packet in [a, b] {
            if let Some(message) = receiver.receive(packet, now).unwrap() {
                delivered.push(message);
            } else {
                assert!(receiver.receive(packet, now).unwrap().is_none());
            }
        }
    }
    assert_eq!(delivered.len(), 2);
    for message in delivered {
        if message.peer == endpoint(peers[0]) {
            assert_eq!(message.bytes, bytes);
        } else {
            assert_eq!(message.peer, endpoint(peers[1]));
            assert_eq!(message.bytes, second);
        }
    }
    assert_eq!(receiver.retained_bytes, 0);
}

#[test]
fn malformed_foreign_and_conflicting_fragments_cannot_corrupt_an_assembly() {
    let member = SocketAddr::from((Ipv4Addr::LOCALHOST, 42001));
    let outsider = SocketAddr::from((Ipv4Addr::LOCALHOST, 42002));
    let mut receiver = Reassembly::new([member].into_iter().collect());
    let bytes = vec![0x71; MAX_PLAIN_BYTES + 1];
    let mut pieces = fragments(member, [7; 16], &bytes);
    let now = Instant::now();
    let mut foreign = fragment(outsider, [7; 16], bytes.len(), 0, &bytes[..FRAGMENT_BYTES]);
    assert!(receiver.receive(&mut foreign, now).is_err());
    let mut too_large = fragment(
        member,
        [7; 16],
        MAX_MESSAGE_BYTES + 1,
        0,
        &bytes[..FRAGMENT_BYTES],
    );
    assert!(receiver.receive(&mut too_large, now).is_err());
    let mut misaligned = fragment(member, [7; 16], bytes.len(), 1, &bytes[..FRAGMENT_BYTES]);
    assert!(receiver.receive(&mut misaligned, now).is_err());
    assert_eq!(receiver.retained_bytes, 0);
    assert!(receiver.receive(&mut pieces[0], now).unwrap().is_none());
    let mut conflict = fragment(member, [7; 16], bytes.len(), 0, &vec![0; FRAGMENT_BYTES]);
    assert!(receiver.receive(&mut conflict, now).is_err());
    let mut delivered = None;
    for piece in &mut pieces[1..] {
        if let Some(message) = receiver.receive(piece, now).unwrap() {
            assert!(delivered.replace(message).is_none());
        }
    }
    assert_eq!(delivered.unwrap().bytes, bytes);
}

#[test]
fn incomplete_messages_expire_and_capacity_does_not_block_a_later_transfer() {
    let member = SocketAddr::from((Ipv4Addr::LOCALHOST, 42001));
    let mut receiver = Reassembly::new([member].into_iter().collect());
    let bytes = vec![0x55; MAX_PLAIN_BYTES + 1];
    let now = Instant::now();
    for index in 0..MAX_PEER_REASSEMBLIES {
        let mut first = fragment(
            member,
            [index as u8; 16],
            bytes.len(),
            0,
            &bytes[..FRAGMENT_BYTES],
        );
        assert!(receiver.receive(&mut first, now).unwrap().is_none());
    }
    let mut next = fragments(member, [99; 16], &bytes);
    assert!(receiver.receive(&mut next[0], now).is_err());
    let later = now + REASSEMBLY_TIMEOUT;
    receiver.expire(later);
    assert_eq!(receiver.retained_bytes, 0);
    let mut completed = None;
    for packet in &mut next {
        if let Some(message) = receiver.receive(packet, later).unwrap() {
            assert!(completed.replace(message).is_none());
        }
    }
    assert_eq!(completed.unwrap().bytes, bytes);
    assert_eq!(receiver.retained_bytes, 0);
}

#[test]
fn reassembly_byte_budget_rejects_new_allocations_until_expiry() {
    let peers: HashSet<_> = (0..9)
        .map(|index| SocketAddr::from((Ipv4Addr::LOCALHOST, 42100 + index)))
        .collect();
    let mut receiver = Reassembly::new(peers.clone());
    let now = Instant::now();
    let mut peers = peers.into_iter();
    for _ in 0..MAX_REASSEMBLY_BYTES / MAX_MESSAGE_BYTES {
        let mut first = fragment(
            peers.next().unwrap(),
            [1; 16],
            MAX_MESSAGE_BYTES,
            0,
            &[7; FRAGMENT_BYTES],
        );
        assert!(receiver.receive(&mut first, now).unwrap().is_none());
    }
    assert_eq!(receiver.retained_bytes, MAX_REASSEMBLY_BYTES);
    let mut last = fragment(
        peers.next().unwrap(),
        [1; 16],
        MAX_MESSAGE_BYTES,
        0,
        &[7; FRAGMENT_BYTES],
    );
    assert!(receiver.receive(&mut last, now).is_err());
    receiver.expire(now + REASSEMBLY_TIMEOUT);
    assert_eq!(receiver.retained_bytes, 0);
    assert!(receiver
        .receive(&mut last, now + REASSEMBLY_TIMEOUT)
        .unwrap()
        .is_none());
    assert_eq!(receiver.retained_bytes, MAX_MESSAGE_BYTES);
}
