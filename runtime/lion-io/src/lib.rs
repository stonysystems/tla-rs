//! Linux batched UDP on the calling Lion executor, without a bridge thread.
//!
//! The syscall/pointer glue is a trusted boundary, just like Lion's UDP glue.
//! Readiness decisions reuse Lion's verified `IoKernel`: only WouldBlock clears
//! a direction, and every Pending result arms that direction's reactor waker.
//! Socket ownership, readiness flags and kernel state stay on one thread.

#[cfg(not(target_os = "linux"))]
compile_error!("tla-rs-lion-io requires Linux recvmmsg/sendmmsg");

use lion_executor::create_reactor_waker_for_current;
use lion_reactor::{readiness, Interest, IoResult, ReactorHandle, ResourceId, Source, Waker};
use lion_utility::net::tcp::kernel::{IoAction, IoKernel};
use lion_utility::net::tcp::method::IoMethod;
use socket2::{Domain, Protocol, Socket, Type};
use std::future::poll_fn;
use std::io;
use std::marker::PhantomData;
use std::mem::{size_of, zeroed};
use std::net::{Ipv4Addr, Ipv6Addr, SocketAddr, SocketAddrV4, SocketAddrV6};
use std::os::fd::AsRawFd;
use std::ptr;
use std::rc::Rc;
use std::task::{Context, Poll};

/// Maximum datagrams processed by one poll, bounding memory and executor work.
pub const MAX_BATCH_SIZE: usize = 64;
/// Receive buffer bound, sufficient for any ordinary IPv4 or IPv6 UDP datagram.
pub const MAX_DATAGRAM_BYTES: usize = 65_535;
const RECEIVE_BUFFER_BYTES: usize = 8 * 1024 * 1024;

/// An owned datagram. Receive calls reuse the byte allocation.
///
/// `Default` allocates a full-size receive buffer. An explicitly supplied,
/// nonzero `bytes.capacity()` is the receive limit, capped at
/// [`MAX_DATAGRAM_BYTES`]; a zero-capacity buffer grows to that bound on receive.
/// Send calls use `bytes.len()`, including zero for an empty datagram.
#[derive(Debug)]
pub struct Datagram {
    pub peer: SocketAddr,
    pub bytes: Vec<u8>,
}

impl Datagram {
    pub fn new(peer: SocketAddr, bytes: Vec<u8>) -> Self {
        Self { peer, bytes }
    }
}

impl Default for Datagram {
    fn default() -> Self {
        Self {
            peer: SocketAddr::from((Ipv4Addr::UNSPECIFIED, 0)),
            bytes: Vec::with_capacity(MAX_DATAGRAM_BYTES),
        }
    }
}

struct Headers {
    messages: [libc::mmsghdr; MAX_BATCH_SIZE],
    vectors: [libc::iovec; MAX_BATCH_SIZE],
    addresses: [libc::sockaddr_storage; MAX_BATCH_SIZE],
}

impl Headers {
    fn new() -> Box<Self> {
        // SAFETY: these C structs contain only integers and raw pointers. Null
        // pointers are replaced before a nonempty syscall uses an entry.
        Box::new(unsafe { zeroed() })
    }

    fn prepare(&mut self, index: usize, bytes: *mut u8, length: usize, addr_len: libc::socklen_t) {
        self.vectors[index] = libc::iovec {
            iov_base: bytes.cast(),
            iov_len: length,
        };
        self.messages[index] = libc::mmsghdr {
            msg_hdr: libc::msghdr {
                msg_name: ptr::addr_of_mut!(self.addresses[index]).cast(),
                msg_namelen: addr_len,
                msg_iov: ptr::addr_of_mut!(self.vectors[index]),
                msg_iovlen: 1,
                msg_control: ptr::null_mut(),
                msg_controllen: 0,
                msg_flags: 0,
            },
            msg_len: 0,
        };
    }
}

/// A thread-affine socket registered with the current Lion reactor.
///
/// Bind, poll and drop it inside the same Lion runtime. It is deliberately
/// neither Send nor Sync; use `Runtime::block_on` to drive it on that executor.
/// There is no internal packet queue and no additional reactor or OS thread.
/// Header storage is fixed at [`MAX_BATCH_SIZE`]; packet storage belongs to the
/// caller. Read and write readiness/wakers are independent.
pub struct BatchUdp {
    socket: mio::net::UdpSocket,
    resource_id: ResourceId,
    kernel: IoKernel,
    headers: Box<Headers>,
    receive_error: Option<io::Error>,
    _thread_affine: PhantomData<Rc<()>>,
}

impl BatchUdp {
    /// Bind a nonblocking UDP socket in the current Lion runtime context.
    pub fn bind(addr: SocketAddr) -> io::Result<Self> {
        let domain = if addr.is_ipv4() {
            Domain::IPV4
        } else {
            Domain::IPV6
        };
        let socket = Socket::new(domain, Type::DGRAM, Some(Protocol::UDP))?;
        // The kernel may clamp the requested queue size. Failure to enlarge it
        // is not a failure to bind, matching the previous transport policy.
        let _ = socket.set_recv_buffer_size(RECEIVE_BUFFER_BYTES);
        socket.set_nonblocking(true)?;
        socket.bind(&addr.into())?;
        let mut socket = mio::net::UdpSocket::from_std(socket.into());
        let mut source = Source::new(&mut socket as &mut dyn mio::event::Source);
        let resource_id = match ReactorHandle::new()
            .register_io_resource(&mut source, Interest::READABLE_WRITABLE)
        {
            IoResult::Ok(id) => id,
            IoResult::Err(error) => return Err(io::Error::other(format!("{error:?}"))),
        };
        readiness::init_readiness(resource_id);
        Ok(Self {
            socket,
            resource_id,
            kernel: IoKernel::new(resource_id.0),
            headers: Headers::new(),
            receive_error: None,
            _thread_affine: PhantomData,
        })
    }

    pub fn local_addr(&self) -> io::Result<SocketAddr> {
        self.socket.local_addr()
    }

    /// Receive up to `min(packets.len(), MAX_BATCH_SIZE)` complete datagrams.
    ///
    /// Only the returned prefix contains new packets, in arrival order. Empty
    /// datagrams count as one packet. Empty input returns zero immediately.
    /// Truncated datagrams are discarded, never exposed as complete packets.
    /// Other complete datagrams in that batch are returned first, followed by
    /// an InvalidData error on the next nonempty receive; if none are complete,
    /// the error is immediate. Slots outside the returned prefix are scratch.
    ///
    /// Cancellation at Pending consumes no datagrams and retains no buffer
    /// borrows. A subsequent receive replaces the read waker on this resource.
    pub async fn recv_batch(&mut self, packets: &mut [Datagram]) -> io::Result<usize> {
        poll_fn(|cx| self.poll_recv_batch(cx, packets)).await
    }

    /// Send a prefix, returning the number of complete datagrams accepted by
    /// the kernel, not an acknowledgement from their peers.
    ///
    /// Partial success is returned even if the next datagram fails. Retry only
    /// `packets[sent..]`; the next call then reports a persistent error on its
    /// first packet. Empty input returns zero; a packet with empty bytes still
    /// sends a datagram. Cancellation at Pending has sent no packets.
    pub async fn send_batch(&mut self, packets: &[Datagram]) -> io::Result<usize> {
        poll_fn(|cx| self.poll_send_batch(cx, packets)).await
    }

    /// Poll receive from the owning Lion task. This registers Lion's reactor
    /// waker for that task, as upstream Lion UDP does, rather than a child
    /// combinator's waker. Suitable for direct `poll_fn`/select event loops.
    pub fn poll_recv_batch(
        &mut self,
        _cx: &mut Context<'_>,
        packets: &mut [Datagram],
    ) -> Poll<io::Result<usize>> {
        if packets.is_empty() {
            return Poll::Ready(Ok(0));
        }
        if let Some(error) = self.receive_error.take() {
            return Poll::Ready(Err(error));
        }
        let was_ready = readiness::is_readable(self.resource_id);
        let mut result = Poll::Pending;
        let mut would_block = false;
        if was_ready {
            match self.receive(packets) {
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                    readiness::clear_readable(self.resource_id);
                    would_block = true;
                }
                completed => result = Poll::Ready(completed),
            }
        }
        match self
            .kernel
            .poll_step(IoMethod::Read, was_ready, would_block)
        {
            IoAction::Arm => {
                self.arm(Interest::READABLE);
                Poll::Pending
            }
            IoAction::Complete => result,
        }
    }

    /// Poll send from the owning Lion task; see [`Self::poll_recv_batch`] for
    /// the task-waker contract and [`Self::send_batch`] for partial completion.
    pub fn poll_send_batch(
        &mut self,
        _cx: &mut Context<'_>,
        packets: &[Datagram],
    ) -> Poll<io::Result<usize>> {
        if packets.is_empty() {
            return Poll::Ready(Ok(0));
        }
        let was_ready = readiness::is_writable(self.resource_id);
        let mut result = Poll::Pending;
        let mut would_block = false;
        if was_ready {
            match self.send(packets) {
                Err(error) if error.kind() == io::ErrorKind::WouldBlock => {
                    readiness::clear_writable(self.resource_id);
                    would_block = true;
                }
                completed => result = Poll::Ready(completed),
            }
        }
        match self
            .kernel
            .poll_step(IoMethod::Write, was_ready, would_block)
        {
            IoAction::Arm => {
                self.arm(Interest::WRITABLE);
                Poll::Pending
            }
            IoAction::Complete => result,
        }
    }

    fn arm(&self, interest: Interest) {
        // The reactor runs on this same thread, so it cannot deliver an event
        // between the readiness check/clear and installing this waker. Kernel
        // readiness arriving meanwhile remains queued in the existing poller.
        ReactorHandle::new().set_waker(
            self.resource_id,
            interest,
            Waker::from_std(create_reactor_waker_for_current()),
        );
    }

    fn receive(&mut self, packets: &mut [Datagram]) -> io::Result<usize> {
        let count = packets.len().min(MAX_BATCH_SIZE);
        for (index, packet) in packets[..count].iter_mut().enumerate() {
            if packet.bytes.capacity() == 0 {
                packet.bytes.reserve_exact(MAX_DATAGRAM_BYTES);
            }
            let capacity = packet.bytes.capacity().min(MAX_DATAGRAM_BYTES);
            self.headers.prepare(
                index,
                packet.bytes.as_mut_ptr(),
                capacity,
                size_of::<libc::sockaddr_storage>() as libc::socklen_t,
            );
        }
        let received = loop {
            // SAFETY: each entry points to a distinct caller-owned Vec's live
            // allocation, an aligned address slot and an initialized iovec.
            // The boxes/Vecs do not move or reallocate during this syscall.
            // MSG_DONTWAIT and a null timeout prevent blocking the executor.
            let result = unsafe {
                libc::recvmmsg(
                    self.socket.as_raw_fd(),
                    self.headers.messages.as_mut_ptr(),
                    count as libc::c_uint,
                    libc::MSG_DONTWAIT | libc::MSG_TRUNC,
                    ptr::null_mut(),
                )
            };
            if result >= 0 {
                break result as usize;
            }
            let error = io::Error::last_os_error();
            if error.kind() != io::ErrorKind::Interrupted {
                return Err(error);
            }
        };
        let mut complete = 0;
        for index in 0..received {
            let message = &self.headers.messages[index];
            let length = message.msg_len as usize;
            let capacity = self.headers.vectors[index].iov_len;
            if message.msg_hdr.msg_flags & libc::MSG_TRUNC != 0 || length > capacity {
                packets[index].bytes.clear();
                self.receive_error.get_or_insert_with(|| {
                    io::Error::new(
                        io::ErrorKind::InvalidData,
                        "UDP datagram exceeds receive buffer",
                    )
                });
                continue;
            }
            let peer = decode_address(&self.headers.addresses[index], message.msg_hdr.msg_namelen);
            let Some(peer) = peer else {
                packets[index].bytes.clear();
                self.receive_error.get_or_insert_with(|| {
                    io::Error::new(
                        io::ErrorKind::InvalidData,
                        "UDP datagram has invalid peer address",
                    )
                });
                continue;
            };
            // SAFETY: recvmmsg initialized exactly this many bytes, and the
            // length was checked against the allocation's bounded iovec.
            unsafe { packets[index].bytes.set_len(length) };
            packets[index].peer = peer;
            if complete != index {
                packets.swap(complete, index);
            }
            complete += 1;
        }
        if complete == 0 {
            if let Some(error) = self.receive_error.take() {
                return Err(error);
            }
        }
        Ok(complete)
    }

    fn send(&mut self, packets: &[Datagram]) -> io::Result<usize> {
        let count = packets.len().min(MAX_BATCH_SIZE);
        for (index, packet) in packets[..count].iter().enumerate() {
            let addr_len = encode_address(&mut self.headers.addresses[index], packet.peer);
            self.headers.prepare(
                index,
                packet.bytes.as_ptr().cast_mut(),
                packet.bytes.len(),
                addr_len,
            );
        }
        loop {
            // SAFETY: sendmmsg only reads the payload/address buffers. The
            // writable header array and its iovecs are exclusive to this call.
            // Every pointer remains valid until the nonblocking syscall exits.
            let result = unsafe {
                libc::sendmmsg(
                    self.socket.as_raw_fd(),
                    self.headers.messages.as_mut_ptr(),
                    count as libc::c_uint,
                    libc::MSG_DONTWAIT | libc::MSG_NOSIGNAL,
                )
            };
            if result >= 0 {
                return Ok(result as usize);
            }
            let error = io::Error::last_os_error();
            if error.kind() != io::ErrorKind::Interrupted {
                return Err(error);
            }
        }
    }
}

impl Drop for BatchUdp {
    fn drop(&mut self) {
        let mut source = Source::new(&mut self.socket as &mut dyn mio::event::Source);
        let _ = ReactorHandle::new().deregister_io_resource(self.resource_id, &mut source);
        self.kernel.drop_step();
    }
}

fn encode_address(storage: &mut libc::sockaddr_storage, peer: SocketAddr) -> libc::socklen_t {
    match peer {
        SocketAddr::V4(peer) => {
            let address = libc::sockaddr_in {
                sin_family: libc::AF_INET as libc::sa_family_t,
                sin_port: peer.port().to_be(),
                sin_addr: libc::in_addr {
                    s_addr: u32::from_ne_bytes(peer.ip().octets()),
                },
                sin_zero: [0; 8],
            };
            // SAFETY: sockaddr_storage is large and aligned enough for either
            // IP sockaddr type; only the returned length is used by the kernel.
            unsafe { ptr::write(ptr::from_mut(storage).cast::<libc::sockaddr_in>(), address) };
            size_of::<libc::sockaddr_in>() as libc::socklen_t
        }
        SocketAddr::V6(peer) => {
            let address = libc::sockaddr_in6 {
                sin6_family: libc::AF_INET6 as libc::sa_family_t,
                sin6_port: peer.port().to_be(),
                sin6_flowinfo: peer.flowinfo(),
                sin6_addr: libc::in6_addr {
                    s6_addr: peer.ip().octets(),
                },
                sin6_scope_id: peer.scope_id(),
            };
            // SAFETY: same storage size/alignment invariant as the IPv4 case.
            unsafe { ptr::write(ptr::from_mut(storage).cast::<libc::sockaddr_in6>(), address) };
            size_of::<libc::sockaddr_in6>() as libc::socklen_t
        }
    }
}

fn decode_address(storage: &libc::sockaddr_storage, length: libc::socklen_t) -> Option<SocketAddr> {
    match i32::from(storage.ss_family) {
        libc::AF_INET if length as usize >= size_of::<libc::sockaddr_in>() => {
            // SAFETY: family/length checked, storage has the necessary alignment.
            let address = unsafe { &*ptr::from_ref(storage).cast::<libc::sockaddr_in>() };
            Some(SocketAddr::V4(SocketAddrV4::new(
                Ipv4Addr::from(address.sin_addr.s_addr.to_ne_bytes()),
                u16::from_be(address.sin_port),
            )))
        }
        libc::AF_INET6 if length as usize >= size_of::<libc::sockaddr_in6>() => {
            // SAFETY: family/length checked, storage has the necessary alignment.
            let address = unsafe { &*ptr::from_ref(storage).cast::<libc::sockaddr_in6>() };
            Some(SocketAddr::V6(SocketAddrV6::new(
                Ipv6Addr::from(address.sin6_addr.s6_addr),
                u16::from_be(address.sin6_port),
                address.sin6_flowinfo,
                address.sin6_scope_id,
            )))
        }
        _ => None,
    }
}

#[cfg(test)]
mod tests;
