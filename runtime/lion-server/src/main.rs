use tla_rs_lion_runtime::{config, stream};

use config::{Config, Transport};
use std::future::{poll_fn, Future};
use std::net::{IpAddr, Ipv4Addr, Ipv6Addr, SocketAddr};
use std::pin::pin;
use std::sync::atomic::{AtomicBool, Ordering};
use std::task::Poll;
use std::time::{Duration, Instant};
use tla_protocol::{NativeReplica, WirePacket};
use tla_rs_lion_io::{BatchUdp, Datagram, MAX_BATCH_SIZE, MAX_DATAGRAM_BYTES};

static STOP: AtomicBool = AtomicBool::new(false);
const MAX_PENDING: usize = 4096;

extern "C" fn stop(_: libc::c_int) {
    STOP.store(true, Ordering::Relaxed);
}

fn main() {
    if let Err(error) = run() {
        eprintln!("ERROR: {error}");
        std::process::exit(1);
    }
}

fn run() -> Result<(), String> {
    let config = Config::load(std::env::args().skip(1))?;
    // The handler only performs an atomic store. Socket/task cleanup stays on
    // the owning Lion thread, never in a signal handler.
    unsafe {
        libc::signal(libc::SIGINT, stop as *const () as libc::sighandler_t);
        libc::signal(libc::SIGTERM, stop as *const () as libc::sighandler_t);
    }
    let runtime = lion::runtime::Builder::new_current_thread()
        .enable_all()
        .build()
        .map_err(|error| format!("creating Lion runtime: {error}"))?;
    runtime.block_on(async {
        match config.transport {
            Transport::Udp => run_udp(config).await,
            Transport::Tcp => run_stream(config).await,
        }
    })
}

fn millis(start: Instant) -> u64 {
    start.elapsed().as_millis().min(u64::MAX as u128) as u64
}

fn report_config(replica: &NativeReplica, protocol: &str, transport: &str, tls: bool) {
    let parameters = replica.rsl_parameters();
    println!(
        "[[CONFIG]] {}",
        serde_json::json!({
            "runtime": "native-lion",
            "protocol": protocol,
            "transport": transport,
            "tls": tls,
            "batch_size": parameters.as_ref().map(|p| p.max_batch_size),
            "max_batch_delay_ms": parameters.as_ref().map(|p| p.max_batch_delay),
            "max_log_length": parameters.as_ref().map(|p| p.max_log_length),
            "baseline_view_timeout_ms": parameters.as_ref().map(|p| p.baseline_view_timeout_period),
            "heartbeat_period_ms": parameters.as_ref().map(|p| p.heartbeat_period),
            "tcp_nodelay": (transport == "tcp").then_some(true),
        })
    );
}

fn endpoint(address: SocketAddr) -> Vec<u8> {
    let mut bytes = Vec::with_capacity(if address.is_ipv4() { 6 } else { 18 });
    match address.ip() {
        IpAddr::V4(ip) => bytes.extend_from_slice(&ip.octets()),
        IpAddr::V6(ip) => bytes.extend_from_slice(&ip.octets()),
    }
    bytes.extend_from_slice(&address.port().to_be_bytes());
    bytes
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

fn collect_outbound(
    replica: &mut NativeReplica,
    pending: &mut Vec<Datagram>,
    endpoints: &mut Vec<Vec<u8>>,
    staging: &mut Vec<WirePacket>,
) -> Result<(), String> {
    if pending.len() + replica.outbound().len() > MAX_PENDING {
        return Err("native transport outbound limit reached".to_owned());
    }
    std::mem::swap(replica.outbound(), staging);
    for packet in staging.drain(..) {
        let peer = address(&packet.peer)?;
        pending.push(Datagram::new(peer, packet.bytes));
        endpoints.push(packet.peer);
    }
    Ok(())
}

enum UdpEvent {
    Received(usize),
    Sent(usize),
    Timer,
    Stop,
}

async fn run_udp(config: Config) -> Result<(), String> {
    let mut socket = BatchUdp::bind(config.bind).map_err(|e| format!("binding UDP: {e}"))?;
    let local = socket.local_addr().map_err(|e| e.to_string())?;
    let mut replica = NativeReplica::new(&config.protocol, endpoint(local), config.peers)?;
    let mut receiving: Vec<_> = (0..MAX_BATCH_SIZE).map(|_| Datagram::default()).collect();
    let mut sending = Vec::with_capacity(MAX_PENDING);
    let mut send_endpoints = Vec::with_capacity(MAX_PENDING);
    let mut staging = Vec::with_capacity(64);
    let mut sent_prefix = 0;
    let start = Instant::now();
    println!(
        "Native {} server: Lion batched UDP on {local}",
        config.protocol
    );
    report_config(&replica, &config.protocol, "udp", false);
    println!("[[READY]]");
    replica.step(0, None)?;
    collect_outbound(
        &mut replica,
        &mut sending,
        &mut send_endpoints,
        &mut staging,
    )?;

    while !STOP.load(Ordering::Relaxed) {
        let now = millis(start);
        let deadline = replica.next_deadline(now).min(now.saturating_add(100));
        let delay = lion::time::sleep(Duration::from_millis(deadline.saturating_sub(now)));
        let mut delay = pin!(delay);
        let event = poll_fn(|cx| {
            if STOP.load(Ordering::Relaxed) {
                return Poll::Ready(Ok(UdpEvent::Stop));
            }
            if sent_prefix < sending.len() {
                match socket.poll_send_batch(cx, &sending[sent_prefix..]) {
                    Poll::Ready(Ok(count)) => return Poll::Ready(Ok(UdpEvent::Sent(count))),
                    Poll::Ready(Err(error)) => return Poll::Ready(Err(error)),
                    Poll::Pending => {}
                }
            }
            if millis(start) >= deadline || delay.as_mut().poll(cx).is_ready() {
                return Poll::Ready(Ok(UdpEvent::Timer));
            }
            match socket.poll_recv_batch(cx, &mut receiving) {
                Poll::Ready(Ok(count)) => Poll::Ready(Ok(UdpEvent::Received(count))),
                Poll::Ready(Err(error)) => Poll::Ready(Err(error)),
                Poll::Pending => Poll::Pending,
            }
        })
        .await
        .map_err(|error: std::io::Error| format!("Lion UDP I/O: {error}"))?;

        match event {
            UdpEvent::Stop => break,
            UdpEvent::Sent(count) => {
                if count == 0 {
                    return Err("UDP batch send made no progress".to_owned());
                }
                for index in sent_prefix..sent_prefix + count {
                    replica.recycle(WirePacket {
                        peer: std::mem::take(&mut send_endpoints[index]),
                        bytes: std::mem::take(&mut sending[index].bytes),
                    });
                }
                sent_prefix += count;
                if sent_prefix == sending.len() {
                    sending.clear();
                    send_endpoints.clear();
                    sent_prefix = 0;
                }
            }
            UdpEvent::Received(count) => {
                for packet in &mut receiving[..count] {
                    let incoming = WirePacket {
                        peer: endpoint(packet.peer),
                        bytes: std::mem::take(&mut packet.bytes),
                    };
                    replica.step(millis(start), Some(incoming))?;
                    packet.bytes = replica.take_buffer();
                    packet.bytes.reserve(MAX_DATAGRAM_BYTES);
                }
                collect_outbound(
                    &mut replica,
                    &mut sending,
                    &mut send_endpoints,
                    &mut staging,
                )?;
            }
            UdpEvent::Timer => {
                replica.step(millis(start), None)?;
                collect_outbound(
                    &mut replica,
                    &mut sending,
                    &mut send_endpoints,
                    &mut staging,
                )?;
            }
        }
        // A hot socket must not monopolize the executor or prevent its reactor
        // from observing newly ready resources and timer deadlines.
        lion::task::yield_now().await;
    }
    println!("[[EXIT]]");
    Ok(())
}

async fn run_stream(config: Config) -> Result<(), String> {
    let mut transport = stream::StreamTransport::bind(&config).await?;
    let mut replica = NativeReplica::new(&config.protocol, config.me, config.peers)?;
    let start = Instant::now();
    let mut outgoing = Vec::with_capacity(64);
    println!(
        "Native {} server: Lion stream transport on {}",
        config.protocol, config.bind
    );
    report_config(&replica, &config.protocol, "tcp", config.service.use_ssl);
    println!("[[READY]]");
    replica.step(0, None)?;
    while !STOP.load(Ordering::Relaxed) {
        std::mem::swap(replica.outbound(), &mut outgoing);
        for packet in outgoing.drain(..) {
            if let Err(error) = transport.enqueue_owned(&packet.peer, packet.bytes) {
                eprintln!("TCP packet not queued: {error}");
            }
        }
        let now = millis(start);
        let deadline = replica.next_deadline(now).min(now.saturating_add(100));
        tokio::select! {
            received = transport.recv() => {
                match received {
                    Ok((peer, bytes)) => replica.step(millis(start), Some(WirePacket { peer, bytes }))?,
                    Err(stream::ReceiveError::Peer(error)) => eprintln!("TCP peer disconnected/rejected: {error}"),
                    Err(stream::ReceiveError::Fatal(error)) => return Err(error),
                }
            }
            _ = lion::time::sleep(Duration::from_millis(deadline.saturating_sub(now))) => {
                replica.step(millis(start), None)?;
            }
        }
        lion::task::yield_now().await;
    }
    println!("[[EXIT]]");
    Ok(())
}
