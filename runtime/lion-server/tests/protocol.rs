use std::collections::VecDeque;
use tla_protocol::{NativeReplica, WirePacket};

fn endpoint(port: u16) -> Vec<u8> {
    let mut endpoint = vec![127, 0, 0, 1];
    endpoint.extend_from_slice(&port.to_be_bytes());
    endpoint
}

fn request(sequence: u64) -> Vec<u8> {
    let mut bytes = vec![1];
    bytes.extend_from_slice(&sequence.to_le_bytes());
    bytes.push(0); // Counter increment, the existing RSL wire operation.
    bytes
}

struct Cluster {
    nodes: Vec<NativeReplica>,
    peers: Vec<Vec<u8>>,
    packets: VecDeque<(usize, WirePacket)>,
    now: u64,
    clock_step: u64,
}

impl Cluster {
    fn new() -> Self {
        let peers: Vec<_> = (4001..4004).map(endpoint).collect();
        let nodes = peers
            .iter()
            .map(|me| NativeReplica::new("rsl", me.clone(), peers.clone()).unwrap())
            .collect();
        Self {
            nodes,
            peers,
            packets: VecDeque::new(),
            now: 0,
            clock_step: 1,
        }
    }

    fn collect(&mut self, source: usize, replies: &mut Vec<Vec<u8>>, client: &[u8]) {
        let packets: Vec<_> = self.nodes[source].outbound().drain(..).collect();
        for mut packet in packets {
            if let Some(destination) = self.peers.iter().position(|peer| *peer == packet.peer) {
                packet.peer.clone_from(&self.peers[source]);
                self.packets.push_back((destination, packet));
            } else if packet.peer == client {
                replies.push(packet.bytes);
            } else {
                panic!("unexpected destination");
            }
        }
    }

    fn increment(&mut self, client: &[u8], sequence: u64) -> u64 {
        self.packets.push_back((
            0,
            WirePacket {
                peer: client.to_vec(),
                bytes: request(sequence),
            },
        ));
        let mut replies = Vec::new();
        for _ in 0..1000 {
            for node in 0..self.nodes.len() {
                self.nodes[node].step(self.now, None).unwrap();
                self.collect(node, &mut replies, client);
            }
            for _ in 0..1000 {
                let Some((destination, packet)) = self.packets.pop_front() else {
                    break;
                };
                self.nodes[destination]
                    .step(self.now, Some(packet))
                    .unwrap();
                self.collect(destination, &mut replies, client);
            }
            self.now += self.clock_step;
            for reply in replies.drain(..) {
                assert_eq!(reply.len(), 18);
                assert_eq!(reply[0], 7);
                if u64::from_le_bytes(reply[1..9].try_into().unwrap()) == sequence {
                    assert_eq!(reply[9], 1);
                    return u64::from_le_bytes(reply[10..18].try_into().unwrap());
                }
            }
        }
        panic!("native RSL cluster did not commit the request");
    }
}

#[test]
fn rsl_single_requests_commit_without_a_batch_timer_or_duplicate_reexecution() {
    let mut cluster = Cluster::new();
    let client = endpoint(5001);
    assert_eq!(cluster.increment(&client, 0), 1);
    // Once initialized, a lone request must commit without waiting for a
    // batching deadline. Repeating it must still leave the counter unchanged.
    cluster.clock_step = 0;
    assert_eq!(cluster.increment(&client, 0), 1);
    assert_eq!(cluster.increment(&client, 1), 2);
}

#[test]
fn native_clock_rejects_backward_time_without_accepting_input() {
    let peers = vec![endpoint(4001), endpoint(4002), endpoint(4003)];
    let mut replica = NativeReplica::new("rsl", peers[0].clone(), peers).unwrap();
    replica.step(100, None).unwrap();
    assert!(replica
        .step(
            99,
            Some(WirePacket {
                peer: endpoint(5001),
                bytes: request(0)
            })
        )
        .is_err());
    replica.step(101, None).unwrap();
    assert!(replica
        .outbound()
        .iter()
        .all(|packet| packet.peer != endpoint(5001)));
}

#[test]
fn empty_network_packet_does_not_prevent_later_commits() {
    let mut cluster = Cluster::new();
    let client = endpoint(5001);
    cluster.packets.push_back((
        0,
        WirePacket {
            peer: client.clone(),
            bytes: Vec::new(),
        },
    ));
    assert_eq!(cluster.increment(&client, 0), 1);
}

fn generic_requests_commit(protocol: &str, count: u16, request_tag: u64, reply_tag: u64) {
    let peers: Vec<_> = (4001..4001 + count).map(endpoint).collect();
    let mut nodes: Vec<_> = peers
        .iter()
        .map(|me| NativeReplica::new(protocol, me.clone(), peers.clone()).unwrap())
        .collect();
    let clients = [endpoint(5001), endpoint(5002)];
    let mut queue = VecDeque::new();
    for (index, client) in clients.iter().enumerate() {
        let mut bytes = request_tag.to_le_bytes().to_vec();
        bytes.extend_from_slice(&(41 + index as u64).to_le_bytes());
        nodes[0]
            .step(
                0,
                Some(WirePacket {
                    peer: client.clone(),
                    bytes,
                }),
            )
            .unwrap();
        queue.extend(nodes[0].outbound().drain(..).map(|packet| (0, packet)));
    }
    let mut replied = [false; 2];
    for turn in 0..100 {
        // Generic hosts guard retransmissions with Instant, independently of
        // the supplied RSL clock. Let those real guards become enabled.
        std::thread::sleep(std::time::Duration::from_millis(1));
        for (source, node) in nodes.iter_mut().enumerate() {
            node.step(turn, None).unwrap();
            queue.extend(node.outbound().drain(..).map(|packet| (source, packet)));
        }
        for _ in 0..1000 {
            let Some((source, mut packet)) = queue.pop_front() else {
                break;
            };
            if let Some(destination) = peers.iter().position(|peer| *peer == packet.peer) {
                packet.peer.clone_from(&peers[source]);
                nodes[destination].step(turn, Some(packet)).unwrap();
                queue.extend(
                    nodes[destination]
                        .outbound()
                        .drain(..)
                        .map(|packet| (destination, packet)),
                );
            } else {
                let client = clients
                    .iter()
                    .position(|peer| *peer == packet.peer)
                    .expect("unknown client");
                assert_eq!(packet.bytes.len(), 16);
                assert_eq!(
                    u64::from_le_bytes(packet.bytes[..8].try_into().unwrap()),
                    reply_tag
                );
                assert_eq!(
                    u64::from_le_bytes(packet.bytes[8..].try_into().unwrap()),
                    41 + client as u64,
                    "reply must retain its request's client association"
                );
                replied[client] = true;
            }
            if replied.iter().all(|reply| *reply) {
                return;
            }
        }
        // EPaxos is a single-instance host: clients retry requests dropped while busy.
        if protocol == "epaxos" {
            for (index, client) in clients
                .iter()
                .enumerate()
                .filter(|(index, _)| !replied[*index])
            {
                let mut bytes = request_tag.to_le_bytes().to_vec();
                bytes.extend_from_slice(&(41 + index as u64).to_le_bytes());
                nodes[0]
                    .step(
                        turn,
                        Some(WirePacket {
                            peer: client.clone(),
                            bytes,
                        }),
                    )
                    .unwrap();
                queue.extend(nodes[0].outbound().drain(..).map(|packet| (0, packet)));
            }
        }
    }
    panic!("{protocol} stranded clients under bounded native scheduling: {replied:?}");
}

#[test]
fn epaxos_ready_quorum_survives_bounded_native_turns() {
    generic_requests_commit("epaxos", 3, 6, 7);
}

#[test]
fn pbft_concurrent_requests_keep_their_clients_and_make_progress() {
    generic_requests_commit("pbft", 4, 4, 5);
}
