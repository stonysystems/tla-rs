use super::*;
use std::future::Future;
use std::pin::pin;
use std::time::Duration;

fn run(future: impl Future<Output = ()>) {
    lion::Runtime::new().unwrap().block_on(async {
        lion::time::timeout(Duration::from_secs(5), future)
            .await
            .expect("UDP test stalled waiting for reactor readiness");
    });
}

fn bind_v4() -> BatchUdp {
    BatchUdp::bind(SocketAddr::from((Ipv4Addr::LOCALHOST, 0))).unwrap()
}

fn receive_slots(count: usize) -> Vec<Datagram> {
    (0..count).map(|_| Datagram::default()).collect()
}

async fn receive_exact(socket: &mut BatchUdp, packets: &mut [Datagram]) {
    let mut received = 0;
    while received < packets.len() {
        let count = socket.recv_batch(&mut packets[received..]).await.unwrap();
        assert!(
            count > 0,
            "a nonempty receive cannot complete without a datagram"
        );
        received += count;
    }
}

async fn assert_empty(socket: &mut BatchUdp) {
    let mut packets = [Datagram::default()];
    poll_fn(|cx| {
        assert!(socket.poll_recv_batch(cx, &mut packets).is_pending());
        Poll::Ready(())
    })
    .await;
}

#[test]
fn preserves_datagram_boundaries_empty_packets_and_peer_addresses() {
    run(async {
        let mut sender = bind_v4();
        let mut receiver = bind_v4();
        let source = sender.local_addr().unwrap();
        let destination = receiver.local_addr().unwrap();
        let outgoing = [
            Datagram::new(destination, b"first".to_vec()),
            Datagram::new(destination, Vec::new()),
            Datagram::new(destination, vec![0x7a; 65_507]),
            Datagram::new(destination, b"last".to_vec()),
        ];
        assert_eq!(sender.send_batch(&outgoing).await.unwrap(), outgoing.len());
        let mut incoming: Vec<_> = (0..outgoing.len())
            .map(|_| Datagram::new(source, Vec::new()))
            .collect();
        receive_exact(&mut receiver, &mut incoming).await;
        for (sent, received) in outgoing.iter().zip(&incoming) {
            assert_eq!(received.peer, source);
            assert_eq!(received.bytes, sent.bytes);
        }
        assert_empty(&mut receiver).await;

        // Reuse buffers containing previous payloads: a shorter payload must
        // not expose stale trailing bytes, and an empty packet is not EOF.
        let next = [
            Datagram::new(destination, vec![3]),
            Datagram::new(destination, Vec::new()),
        ];
        assert_eq!(sender.send_batch(&next).await.unwrap(), 2);
        receive_exact(&mut receiver, &mut incoming[..2]).await;
        assert_eq!(incoming[0].bytes, [3]);
        assert_eq!(incoming[1].bytes, []);
    });
}

#[test]
fn empty_batches_do_not_consume_or_send_datagrams() {
    run(async {
        let mut sender = bind_v4();
        let mut receiver = bind_v4();
        let outgoing = [Datagram::new(
            receiver.local_addr().unwrap(),
            b"queued".to_vec(),
        )];
        assert_eq!(sender.send_batch(&[]).await.unwrap(), 0);
        assert_empty(&mut receiver).await;
        assert_eq!(sender.send_batch(&outgoing).await.unwrap(), 1);
        assert_eq!(receiver.recv_batch(&mut []).await.unwrap(), 0);
        let mut incoming = [Datagram::default()];
        receive_exact(&mut receiver, &mut incoming).await;
        assert_eq!(incoming[0].bytes, b"queued");
    });
}

#[test]
fn batches_return_only_a_bounded_prefix_without_duplicates() {
    run(async {
        let mut sender = bind_v4();
        let mut receiver = bind_v4();
        let destination = receiver.local_addr().unwrap();
        let outgoing: Vec<_> = (0..MAX_BATCH_SIZE + 3)
            .map(|index| Datagram::new(destination, (index as u32).to_be_bytes().to_vec()))
            .collect();
        let sent = sender.send_batch(&outgoing).await.unwrap();
        assert_eq!(sent, MAX_BATCH_SIZE);
        let mut incoming = receive_slots(outgoing.len());
        assert_eq!(
            receiver.recv_batch(&mut incoming).await.unwrap(),
            MAX_BATCH_SIZE
        );
        for (sent, received) in outgoing[..sent].iter().zip(&incoming) {
            assert_eq!(received.bytes, sent.bytes);
        }
        assert_eq!(sender.send_batch(&outgoing[sent..]).await.unwrap(), 3);
        receive_exact(&mut receiver, &mut incoming[sent..]).await;
        for (sent, received) in outgoing.iter().zip(&incoming) {
            assert_eq!(received.bytes, sent.bytes);
        }
        assert_empty(&mut receiver).await;
    });
}

#[test]
fn partial_send_preserves_progress_and_reports_next_packet_error() {
    run(async {
        let mut sender = bind_v4();
        let mut receiver = bind_v4();
        let destination = receiver.local_addr().unwrap();
        let outgoing = [
            Datagram::new(destination, b"before".to_vec()),
            Datagram::new(destination, vec![1; MAX_DATAGRAM_BYTES + 1]),
            Datagram::new(destination, b"after".to_vec()),
        ];
        assert_eq!(sender.send_batch(&outgoing).await.unwrap(), 1);
        let mut incoming = [Datagram::default()];
        receive_exact(&mut receiver, &mut incoming).await;
        assert_eq!(incoming[0].bytes, b"before");
        let error = sender.send_batch(&outgoing[1..]).await.unwrap_err();
        assert_eq!(error.raw_os_error(), Some(libc::EMSGSIZE));
        assert_empty(&mut receiver).await;
        assert_eq!(sender.send_batch(&outgoing[2..]).await.unwrap(), 1);
        receive_exact(&mut receiver, &mut incoming).await;
        assert_eq!(incoming[0].bytes, b"after");
        assert_empty(&mut receiver).await;
    });
}

#[test]
fn truncation_discards_incomplete_payload_and_socket_remains_usable() {
    run(async {
        let mut sender = bind_v4();
        let mut receiver = bind_v4();
        let destination = receiver.local_addr().unwrap();
        let mut incoming = [Datagram::new(destination, Vec::with_capacity(4))];
        let oversized = vec![9; incoming[0].bytes.capacity() + 1];
        assert_eq!(
            sender
                .send_batch(&[Datagram::new(destination, oversized)])
                .await
                .unwrap(),
            1
        );
        let error = receiver.recv_batch(&mut incoming).await.unwrap_err();
        assert_eq!(error.kind(), io::ErrorKind::InvalidData);
        assert!(incoming[0].bytes.is_empty());
        assert_eq!(
            sender
                .send_batch(&[Datagram::new(destination, b"good".to_vec())])
                .await
                .unwrap(),
            1
        );
        receive_exact(&mut receiver, &mut incoming).await;
        assert_eq!(incoming[0].bytes, b"good");
        assert_empty(&mut receiver).await;
    });
}

#[test]
fn mixed_truncation_preserves_complete_packets_then_reports_error() {
    run(async {
        let mut sender = bind_v4();
        let mut receiver = bind_v4();
        let destination = receiver.local_addr().unwrap();
        let mut incoming: Vec<_> = (0..4)
            .map(|_| Datagram::new(destination, Vec::with_capacity(4)))
            .collect();
        let oversized = vec![9; incoming[0].bytes.capacity() + 1];
        let outgoing = [
            Datagram::new(destination, oversized.clone()),
            Datagram::new(destination, b"ok".to_vec()),
            Datagram::new(destination, oversized),
            Datagram::new(destination, Vec::new()),
        ];
        assert_eq!(sender.send_batch(&outgoing).await.unwrap(), 4);
        assert_eq!(receiver.recv_batch(&mut incoming).await.unwrap(), 2);
        assert_eq!(incoming[0].bytes, b"ok");
        assert_eq!(incoming[1].bytes, []);
        assert_eq!(incoming[0].peer, sender.local_addr().unwrap());
        assert_eq!(incoming[1].peer, sender.local_addr().unwrap());

        // Reporting a deferred error must not accidentally receive/drop this
        // newer packet, nor be consumed by an empty receive call.
        assert_eq!(
            sender
                .send_batch(&[Datagram::new(destination, b"next".to_vec())])
                .await
                .unwrap(),
            1
        );
        assert_eq!(receiver.recv_batch(&mut []).await.unwrap(), 0);
        assert_eq!(
            receiver.recv_batch(&mut incoming).await.unwrap_err().kind(),
            io::ErrorKind::InvalidData
        );
        assert_eq!(receiver.recv_batch(&mut incoming).await.unwrap(), 1);
        assert_eq!(incoming[0].bytes, b"next");
        assert_empty(&mut receiver).await;
    });
}

#[test]
fn cancelled_receive_rearms_for_later_packets_and_bidirectional_io() {
    run(async {
        let mut receiver = bind_v4();
        let peer = std::net::UdpSocket::bind((Ipv4Addr::LOCALHOST, 0)).unwrap();
        peer.set_nonblocking(true).unwrap();
        let destination = receiver.local_addr().unwrap();
        let source = peer.local_addr().unwrap();
        let mut discarded = [Datagram::default()];
        {
            let mut cancelled = pin!(receiver.recv_batch(&mut discarded));
            poll_fn(|cx| {
                assert!(cancelled.as_mut().poll(cx).is_pending());
                Poll::Ready(())
            })
            .await;
        }

        // Use the poll APIs together on the same task: a read parked on
        // WouldBlock must not clear or steal write readiness.
        let outgoing = [Datagram::new(source, b"request".to_vec())];
        let mut incoming = [Datagram::default()];
        poll_fn(|cx| {
            assert!(receiver.poll_recv_batch(cx, &mut incoming).is_pending());
            receiver.poll_send_batch(cx, &outgoing)
        })
        .await
        .map(|sent| assert_eq!(sent, 1))
        .unwrap();
        let mut buffer = [0; 16];
        let (length, from) = peer.recv_from(&mut buffer).unwrap();
        assert_eq!(&buffer[..length], b"request");
        assert_eq!(from, destination);

        // A separate Lion task sends only after the receiver has suspended.
        // A second round also proves rearming after the ready queue drains.
        for bytes in [b"reply-1", b"reply-2"] {
            let peer = peer.try_clone().unwrap();
            let send = lion::spawn(async move {
                lion::time::sleep(Duration::from_millis(10)).await;
                assert_eq!(peer.send_to(bytes, destination).unwrap(), bytes.len());
            });
            receive_exact(&mut receiver, &mut incoming).await;
            assert_eq!(incoming[0].bytes, bytes);
            assert_eq!(incoming[0].peer, source);
            send.await.unwrap();
            assert_empty(&mut receiver).await;
        }
    });
}

#[test]
fn ipv6_round_trip_preserves_addresses_and_empty_datagram() {
    run(async {
        let mut sender = BatchUdp::bind(SocketAddr::from((Ipv6Addr::LOCALHOST, 0))).unwrap();
        let mut receiver = BatchUdp::bind(SocketAddr::from((Ipv6Addr::LOCALHOST, 0))).unwrap();
        let source = sender.local_addr().unwrap();
        let outgoing = [
            Datagram::new(receiver.local_addr().unwrap(), b"ipv6".to_vec()),
            Datagram::new(receiver.local_addr().unwrap(), Vec::new()),
        ];
        assert_eq!(sender.send_batch(&outgoing).await.unwrap(), 2);
        let mut incoming = receive_slots(2);
        receive_exact(&mut receiver, &mut incoming).await;
        assert_eq!(incoming[0].bytes, b"ipv6");
        assert!(incoming[1].bytes.is_empty());
        assert_eq!(incoming[0].peer, source);
        assert_eq!(incoming[1].peer, source);
    });
}
