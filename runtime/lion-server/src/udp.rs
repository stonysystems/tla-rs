//! Native UDP policy above the datagram-preserving Lion socket.
//!
//! Ordinary protocol packets retain their wire format. Oversized member packets
//! use 1,232-byte fragment datagrams (including a versioned header), small enough
//! for IPv6's minimum MTU. Reassembly is bounded and expires incomplete messages;
//! loss/retry remains the protocol's responsibility, just as for plain UDP.
use crate::config::endpoint;
use std::collections::{HashMap, HashSet, VecDeque};
use std::io;
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};
use std::task::{Context, Poll};
use std::time::{Duration, Instant};
use tla_protocol::WirePacket;
use tla_rs_lion_io::{BatchUdp, Datagram, MAX_BATCH_SIZE};

const MAX_PLAIN_BYTES: usize = 65_507;
pub const MAX_MESSAGE_BYTES: usize = 8 * 1024 * 1024;
const MAX_QUEUED_MESSAGES: usize = 4096;
const MAX_QUEUED_BYTES: usize = 64 * 1024 * 1024;
const MAX_REASSEMBLY_BYTES: usize = 64 * 1024 * 1024;
const MAX_REASSEMBLIES: usize = 64;
const MAX_PEER_REASSEMBLIES: usize = 4;
const REASSEMBLY_TIMEOUT: Duration = Duration::from_secs(5);
// This reserved prefix is not a message tag of any supported native protocol.
const MAGIC: &[u8; 8] = b"\xffTLAFRG1";
const HEADER_BYTES: usize = 32;
const FRAGMENT_BYTES: usize = 1200;

type MessageKey = (SocketAddr, [u8; 16]);

struct Assembly {
    bytes: Vec<u8>,
    present: Vec<bool>,
    remaining: usize,
    expires: Instant,
}

struct Reassembly {
    members: HashSet<SocketAddr>,
    messages: HashMap<MessageKey, Assembly>,
    retained_bytes: usize,
    next_expiry: Option<Instant>,
}

impl Reassembly {
    fn new(members: HashSet<SocketAddr>) -> Self {
        Self {
            members,
            messages: HashMap::new(),
            retained_bytes: 0,
            next_expiry: None,
        }
    }

    fn expire(&mut self, now: Instant) {
        if self.next_expiry.is_none_or(|deadline| now < deadline) {
            return;
        }
        self.messages.retain(|_, assembly| {
            if now >= assembly.expires {
                self.retained_bytes -= assembly.bytes.len();
                false
            } else {
                true
            }
        });
        self.next_expiry = self
            .messages
            .values()
            .map(|assembly| assembly.expires)
            .min();
    }

    fn receive(
        &mut self,
        packet: &mut Datagram,
        now: Instant,
    ) -> Result<Option<WirePacket>, String> {
        self.expire(now);
        if !packet.bytes.starts_with(MAGIC) {
            return Ok(Some(WirePacket {
                peer: endpoint(packet.peer),
                bytes: std::mem::take(&mut packet.bytes),
            }));
        }
        if !self.members.contains(&packet.peer) {
            return Err("UDP fragments are accepted only from configured members".into());
        }
        let frame = &packet.bytes;
        if frame.len() < HEADER_BYTES {
            return Err("truncated UDP fragment header".into());
        }
        let id: [u8; 16] = frame[8..24].try_into().unwrap();
        let total = u32::from_be_bytes(frame[24..28].try_into().unwrap()) as usize;
        let offset = u32::from_be_bytes(frame[28..32].try_into().unwrap()) as usize;
        if total <= MAX_PLAIN_BYTES
            || total > MAX_MESSAGE_BYTES
            || offset >= total
            || offset % FRAGMENT_BYTES != 0
            || frame.len() - HEADER_BYTES != FRAGMENT_BYTES.min(total - offset)
        {
            return Err("invalid UDP fragment length or offset".into());
        }
        let key = (packet.peer, id);
        if !self.messages.contains_key(&key) {
            if self.messages.len() >= MAX_REASSEMBLIES
                || self.retained_bytes + total > MAX_REASSEMBLY_BYTES
                || self
                    .messages
                    .keys()
                    .filter(|(peer, _)| *peer == packet.peer)
                    .count()
                    >= MAX_PEER_REASSEMBLIES
            {
                return Err("UDP reassembly capacity reached".into());
            }
            let count = total.div_ceil(FRAGMENT_BYTES);
            let expires = now + REASSEMBLY_TIMEOUT;
            self.messages.insert(
                key,
                Assembly {
                    bytes: vec![0; total],
                    present: vec![false; count],
                    remaining: count,
                    expires,
                },
            );
            self.retained_bytes += total;
            self.next_expiry = Some(
                self.next_expiry
                    .map_or(expires, |current| current.min(expires)),
            );
        }
        let assembly = self.messages.get_mut(&key).unwrap();
        if assembly.bytes.len() != total {
            return Err("conflicting UDP fragment message length".into());
        }
        let index = offset / FRAGMENT_BYTES;
        let payload = &frame[HEADER_BYTES..];
        let destination = &mut assembly.bytes[offset..offset + payload.len()];
        if assembly.present[index] {
            if destination != payload {
                return Err("conflicting duplicate UDP fragment".into());
            }
            return Ok(None);
        }
        destination.copy_from_slice(payload);
        assembly.present[index] = true;
        assembly.remaining -= 1;
        if assembly.remaining != 0 {
            return Ok(None);
        }
        let assembly = self.messages.remove(&key).unwrap();
        self.retained_bytes -= total;
        Ok(Some(WirePacket {
            peer: endpoint(packet.peer),
            bytes: assembly.bytes,
        }))
    }
}

struct Pending {
    packet: WirePacket,
    destination: SocketAddr,
    id: [u8; 16],
    offset: usize,
}

pub enum SendOutcome {
    Sent,
    Dropped { peer: SocketAddr, error: io::Error },
}

/// One owning Lion task drives both directions. At most one syscall batch of
/// fragments is materialized; large packets do not expand into an unbounded
/// queue of datagrams. Raw payloads and endpoint allocations are returned to
/// the protocol's existing recycle pool after transmission.
pub struct UdpTransport {
    socket: BatchUdp,
    reassembly: Reassembly,
    pending: VecDeque<Pending>,
    queued_bytes: usize,
    frames: Vec<Datagram>,
    sources: Vec<Option<WirePacket>>,
    sent_prefix: usize,
    fragment_buffers: Vec<Vec<u8>>,
    recycled: Vec<WirePacket>,
    session: [u8; 8],
    sequence: u64,
}

impl UdpTransport {
    pub fn bind(bind: SocketAddr, members: &[Vec<u8>]) -> Result<Self, String> {
        let members = members
            .iter()
            .map(|peer| address(peer))
            .collect::<Result<_, _>>()?;
        let socket = BatchUdp::bind(bind).map_err(|error| format!("binding UDP: {error}"))?;
        let mut session = [0; 8];
        openssl::rand::rand_bytes(&mut session)
            .map_err(|error| format!("UDP session identity: {error}"))?;
        Ok(Self {
            socket,
            reassembly: Reassembly::new(members),
            pending: VecDeque::new(),
            queued_bytes: 0,
            frames: Vec::with_capacity(MAX_BATCH_SIZE),
            sources: Vec::with_capacity(MAX_BATCH_SIZE),
            sent_prefix: 0,
            fragment_buffers: Vec::with_capacity(MAX_BATCH_SIZE),
            recycled: Vec::with_capacity(MAX_BATCH_SIZE),
            session,
            sequence: 0,
        })
    }

    pub fn local_addr(&self) -> io::Result<SocketAddr> {
        self.socket.local_addr()
    }

    pub fn enqueue(&mut self, packet: WirePacket) -> Result<(), String> {
        let destination = address(&packet.peer)?;
        let size = packet.bytes.len();
        if size > MAX_MESSAGE_BYTES {
            return Err(format!(
                "UDP protocol message exceeds {MAX_MESSAGE_BYTES}-byte limit"
            ));
        }
        if self.pending.len() >= MAX_QUEUED_MESSAGES || self.queued_bytes + size > MAX_QUEUED_BYTES
        {
            return Err("UDP outbound queue capacity reached".into());
        }
        let mut id = [0; 16];
        if size > MAX_PLAIN_BYTES {
            if !self.reassembly.members.contains(&destination) {
                return Err(
                    "oversized UDP messages require a configured member destination".into(),
                );
            }
            self.sequence = self
                .sequence
                .checked_add(1)
                .ok_or("UDP message identity exhausted")?;
            id[..8].copy_from_slice(&self.session);
            id[8..].copy_from_slice(&self.sequence.to_be_bytes());
        }
        self.queued_bytes += size;
        self.pending.push_back(Pending {
            packet,
            destination,
            id,
            offset: 0,
        });
        Ok(())
    }

    fn fill_batch(&mut self) {
        while self.frames.len() < MAX_BATCH_SIZE {
            let Some(pending) = self.pending.front_mut() else {
                break;
            };
            let total = pending.packet.bytes.len();
            if total <= MAX_PLAIN_BYTES {
                let mut pending = self.pending.pop_front().unwrap();
                self.queued_bytes -= total;
                self.frames.push(Datagram::new(
                    pending.destination,
                    std::mem::take(&mut pending.packet.bytes),
                ));
                self.sources.push(Some(pending.packet));
            } else {
                let end = total.min(pending.offset + FRAGMENT_BYTES);
                let mut bytes = self
                    .fragment_buffers
                    .pop()
                    .unwrap_or_else(|| Vec::with_capacity(HEADER_BYTES + FRAGMENT_BYTES));
                bytes.clear();
                bytes.extend_from_slice(MAGIC);
                bytes.extend_from_slice(&pending.id);
                bytes.extend_from_slice(&(total as u32).to_be_bytes());
                bytes.extend_from_slice(&(pending.offset as u32).to_be_bytes());
                bytes.extend_from_slice(&pending.packet.bytes[pending.offset..end]);
                self.frames.push(Datagram::new(pending.destination, bytes));
                self.sources.push(None);
                pending.offset = end;
                if end == total {
                    self.queued_bytes -= total;
                    self.recycled.push(self.pending.pop_front().unwrap().packet);
                }
            }
        }
    }

    fn retire(&mut self, count: usize) {
        for index in self.sent_prefix..self.sent_prefix + count {
            let bytes = std::mem::take(&mut self.frames[index].bytes);
            if let Some(mut packet) = self.sources[index].take() {
                packet.bytes = bytes;
                self.recycled.push(packet);
            } else {
                self.fragment_buffers.push(bytes);
            }
        }
        self.sent_prefix += count;
        if self.sent_prefix == self.frames.len() {
            self.frames.clear();
            self.sources.clear();
            self.sent_prefix = 0;
        }
    }

    pub fn poll_send(&mut self, cx: &mut Context<'_>) -> Poll<io::Result<SendOutcome>> {
        if self.frames.is_empty() {
            self.fill_batch();
        }
        if self.frames.is_empty() {
            return Poll::Pending;
        }
        match self
            .socket
            .poll_send_batch(cx, &self.frames[self.sent_prefix..])
        {
            Poll::Ready(Ok(0)) => Poll::Ready(Err(io::Error::new(
                io::ErrorKind::WriteZero,
                "UDP batch send made no progress",
            ))),
            Poll::Ready(Ok(count)) => {
                self.retire(count);
                Poll::Ready(Ok(SendOutcome::Sent))
            }
            Poll::Ready(Err(error)) if packet_local_error(&error) => {
                // sendmmsg reports a successful prefix separately. At this point
                // no datagram in this call was sent; discard only its first one.
                let peer = self.frames[self.sent_prefix].peer;
                self.retire(1);
                Poll::Ready(Ok(SendOutcome::Dropped { peer, error }))
            }
            other => other.map(|result| result.map(|_| SendOutcome::Sent)),
        }
    }

    pub fn poll_recv(
        &mut self,
        cx: &mut Context<'_>,
        packets: &mut [Datagram],
    ) -> Poll<io::Result<usize>> {
        self.socket.poll_recv_batch(cx, packets)
    }

    pub fn decode(
        &mut self,
        packet: &mut Datagram,
        now: Instant,
    ) -> Result<Option<WirePacket>, String> {
        self.reassembly.receive(packet, now)
    }

    pub fn expire(&mut self, now: Instant) {
        self.reassembly.expire(now);
    }

    pub fn drain_recycled(&mut self) -> std::vec::Drain<'_, WirePacket> {
        self.recycled.drain(..)
    }
}

fn packet_local_error(error: &io::Error) -> bool {
    matches!(
        error.raw_os_error(),
        Some(
            libc::EMSGSIZE
                | libc::EHOSTUNREACH
                | libc::ENETUNREACH
                | libc::EHOSTDOWN
                | libc::ENETDOWN
                | libc::ECONNREFUSED
                | libc::EACCES
                | libc::EPERM
                | libc::EADDRNOTAVAIL
                | libc::EAFNOSUPPORT
                | libc::ENOBUFS
                | libc::EINVAL
        )
    )
}

fn address(bytes: &[u8]) -> Result<SocketAddr, String> {
    match bytes.len() {
        6 => Ok(SocketAddr::new(
            IpAddr::V4(Ipv4Addr::new(bytes[0], bytes[1], bytes[2], bytes[3])),
            u16::from_be_bytes([bytes[4], bytes[5]]),
        )),
        18 => Ok(SocketAddr::new(
            IpAddr::V6(Ipv6Addr::from(<[u8; 16]>::try_from(&bytes[..16]).unwrap())),
            u16::from_be_bytes([bytes[16], bytes[17]]),
        )),
        _ => Err(format!("invalid UDP endpoint length {}", bytes.len())),
    }
}

#[cfg(test)]
mod tests;
