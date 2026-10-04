use std::collections::BTreeMap;
use std::fs::{self, File, OpenOptions};
use std::io::{self, Write};
use std::net::{SocketAddr, UdpSocket};
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};
use std::sync::{Arc, Barrier, OnceLock};
use std::thread;
use std::time::{Duration, Instant, SystemTime, UNIX_EPOCH};

use tla_rs_lion_runtime::{config, stream};

#[derive(Clone, Copy)]
enum Protocol {
    Rsl,
    IronFleetRsl,
    Raft,
    PrimaryBackup,
    Pbft,
    Epaxos,
}

impl Protocol {
    // Same datagrams as IronRSLClientUDP/MultiPaxos.cs and
    // IronGenericClient/SyncClient.cs; no server codec is replaced here.
    fn request(self, out: &mut [u8; 32], client: u64, seq: u64) -> usize {
        if matches!(self, Self::Rsl) {
            out[0] = 1;
            out[1..9].copy_from_slice(&seq.to_le_bytes());
            out[9] = 0; // CAppIncrement
            return 10;
        }
        if matches!(self, Self::IronFleetRsl) {
            out[..8].fill(0); // Original IronFleet RSL request discriminant.
            out[8..16].copy_from_slice(&seq.to_be_bytes());
            out[16..24].copy_from_slice(&8u64.to_be_bytes());
            out[24..32].fill(0); // Counter command 0: increment.
            return 32;
        }
        let tag: u64 = match self {
            Self::Raft => 5,
            Self::PrimaryBackup => 3,
            Self::Pbft => 4,
            Self::Epaxos => 6,
            Self::Rsl | Self::IronFleetRsl => unreachable!(),
        };
        out[..8].copy_from_slice(&tag.to_le_bytes());
        if matches!(self, Self::Raft) {
            out[8..16].copy_from_slice(&client.to_le_bytes());
            out[16..24].copy_from_slice(&seq.to_le_bytes());
            out[24..32].copy_from_slice(&seq.to_le_bytes());
            32
        } else {
            out[8..16].copy_from_slice(&seq.to_le_bytes());
            16
        }
    }

    fn reply(self, data: &[u8], client: u64, seq: u64) -> Reply {
        let word = |offset| u64::from_le_bytes(data[offset..offset + 8].try_into().unwrap());
        let be_word = |offset| u64::from_be_bytes(data[offset..offset + 8].try_into().unwrap());
        match self {
            Self::Rsl if data.len() == 18 && data[0] == 7 => {
                if word(1) != seq {
                    Reply::Stale
                } else if data[9] != 1 {
                    Reply::Invalid
                } else {
                    Reply::Success(Some(word(10)))
                }
            }
            Self::IronFleetRsl if data.len() == 32 && be_word(0) == 6 && be_word(16) == 8 => {
                if be_word(8) != seq {
                    Reply::Stale
                } else {
                    Reply::Success(Some(be_word(24)))
                }
            }
            Self::Raft if data.len() == 32 && word(0) == 6 => {
                if word(8) != client || word(16) != seq {
                    Reply::Stale
                } else if word(24) == 0 {
                    Reply::Rejected
                } else if word(24) == 1 {
                    Reply::Success(None)
                } else {
                    Reply::Invalid
                }
            }
            Self::PrimaryBackup | Self::Pbft | Self::Epaxos if data.len() == 16 => {
                let tag = match self {
                    Self::PrimaryBackup => 4,
                    Self::Pbft => 5,
                    _ => 7,
                };
                if word(0) != tag {
                    Reply::Invalid
                } else if word(8) != seq {
                    Reply::Stale
                } else {
                    Reply::Success(None)
                }
            }
            _ => Reply::Invalid,
        }
    }
}

enum Reply {
    Success(Option<u64>),
    Stale,
    Rejected,
    Invalid,
}

// Logarithmic nanosecond histogram: upper-bound percentiles, <0.8% bucket width.
// Fixed storage avoids retaining/allocating one latency sample per operation.
const BUCKETS: usize = 8192;
struct Stats {
    completed: u64,
    attempts: u64,
    timeouts: u64,
    rejected: u64,
    errors: u64,
    invalid: u64,
    stale: u64,
    unfinished: u64,
    latency_ns: u128,
    histogram: Box<[u64; BUCKETS]>,
}
impl Default for Stats {
    fn default() -> Self {
        Self {
            completed: 0,
            attempts: 0,
            timeouts: 0,
            rejected: 0,
            errors: 0,
            invalid: 0,
            stale: 0,
            unfinished: 0,
            latency_ns: 0,
            histogram: Box::new([0; BUCKETS]),
        }
    }
}
impl Stats {
    fn record(&mut self, elapsed: Duration) {
        let ns = elapsed.as_nanos().min(u64::MAX as u128) as u64;
        let shift = (63 - ns.max(1).leading_zeros() as usize).saturating_sub(7);
        let bucket = if shift == 0 {
            ns as usize
        } else {
            (shift + 1) * 128 + (ns >> shift) as usize - 128
        };
        self.histogram[bucket] += 1;
        self.completed += 1;
        self.latency_ns += ns as u128;
    }
    fn merge(&mut self, other: Self) {
        self.completed += other.completed;
        self.attempts += other.attempts;
        self.timeouts += other.timeouts;
        self.rejected += other.rejected;
        self.errors += other.errors;
        self.invalid += other.invalid;
        self.stale += other.stale;
        self.unfinished += other.unfinished;
        self.latency_ns += other.latency_ns;
        for (a, b) in self.histogram.iter_mut().zip(other.histogram.iter()) {
            *a += b;
        }
    }
    fn percentile_ms(&self, percent: u64) -> f64 {
        if self.completed == 0 {
            return 0.0;
        }
        let rank = (self.completed as u128 * percent as u128).div_ceil(100);
        let mut count = 0_u128;
        for (i, n) in self.histogram.iter().enumerate() {
            count += *n as u128;
            if count >= rank {
                let upper = if i < 256 {
                    i as u128
                } else {
                    let shift = i / 128 - 1;
                    (((i % 128 + 129) as u128) << shift) - 1
                };
                return upper as f64 / 1_000_000.0;
            }
        }
        unreachable!()
    }
}

// Reserve before sending: even an aborted run must never lend its request
// numbers to a later owner of the same UDP endpoint. Gaps are legal in RSL.
const SEQUENCE_RANGE: u64 = 1 << 32;

fn sequence_directory() -> Result<Arc<PathBuf>, String> {
    let base = std::env::var_os("XDG_STATE_HOME")
        .map(PathBuf::from)
        .filter(|path| path.is_absolute())
        .or_else(|| {
            std::env::var_os("HOME")
                .map(|home| PathBuf::from(home).join(".local/state"))
        })
        .ok_or("UDP RSL requires XDG_STATE_HOME or HOME for persistent request sequences")?;
    Ok(Arc::new(base.join("tla-rs")))
}

fn reserve_sequence_range(directory: &Path, floor: u64) -> io::Result<(u64, u64)> {
    fs::create_dir_all(directory)?;
    // Keep the lock on a separate inode: the checkpoint is replaced atomically.
    let lock = OpenOptions::new()
        .read(true)
        .write(true)
        .create(true)
        .truncate(false)
        .mode(0o600)
        .open(directory.join("rsl-sequence.lock"))?;
    lock.lock()?;
    let checkpoint = directory.join("rsl-sequence");
    let first = match fs::read_to_string(&checkpoint) {
        Ok(value) => value
            .trim()
            .parse::<u64>()
            .map_err(|_| io::Error::new(io::ErrorKind::InvalidData, "invalid RSL sequence checkpoint"))?
            .max(floor),
        Err(error) if error.kind() == io::ErrorKind::NotFound => floor.max(1),
        Err(error) => return Err(error),
    };
    let end = first
        .checked_add(SEQUENCE_RANGE)
        .ok_or_else(|| io::Error::other("RSL request sequence space exhausted"))?;
    let pending = directory.join("rsl-sequence.next");
    let mut file = OpenOptions::new()
        .write(true)
        .create(true)
        .truncate(true)
        .mode(0o600)
        .open(&pending)?;
    writeln!(file, "{end}")?;
    file.sync_all()?;
    fs::rename(pending, checkpoint)?;
    File::open(directory)?.sync_all()?;
    Ok((first, end))
}

struct RequestSequence {
    value: u64,
    end: u64,
    directory: Option<Arc<PathBuf>>,
}

impl RequestSequence {
    fn transient(value: u64) -> Self {
        Self { value, end: u64::MAX, directory: None }
    }

    fn persistent(directory: Arc<PathBuf>) -> Result<Self, String> {
        let floor = SystemTime::now()
            .duration_since(UNIX_EPOCH)
            .map_err(|error| error.to_string())?
            .as_nanos()
            .try_into()
            .map_err(|_| "system time exceeds the RSL sequence space")?;
        let (value, end) = reserve_sequence_range(&directory, floor)
            .map_err(|error| format!("reserving RSL sequences in {}: {error}", directory.display()))?;
        Ok(Self { value, end, directory: Some(directory) })
    }

    fn advance(&mut self) -> Result<(), String> {
        self.value = self.value.checked_add(1).ok_or("request sequence exhausted")?;
        if self.value == self.end {
            if let Some(directory) = &self.directory {
                *self = Self::persistent(directory.clone())?;
            }
        }
        Ok(())
    }
}

struct Worker {
    socket: Option<UdpSocket>,
    stream: Option<stream::StreamTransport>,
    peers: Arc<Vec<SocketAddr>>,
    peer_ids: Arc<Vec<Vec<u8>>>,
    protocol: Protocol,
    client: u64,
    seq: RequestSequence,
    server: usize,
    last_value: Option<u64>,
    timeout: Duration,
}
impl Worker {
    async fn phase(&mut self, deadline: Instant, stats: &mut Stats) -> Result<(), String> {
        let mut request = [0; 32];
        let mut response = [0; 65536];
        let mut stream_response;
        while Instant::now() < deadline {
            let len = self.protocol.request(&mut request, self.client, self.seq.value);
            let began = Instant::now();
            let mut resend = true;
            let mut retry_at = began;
            let mut completed = false;
            while Instant::now() < deadline {
                if resend {
                    stats.attempts += 1;
                    let sent = if let Some(socket) = &self.socket {
                        socket
                            .send_to(&request[..len], self.peers[self.server])
                            .map(|n| n == len)
                            .unwrap_or(false)
                    } else {
                        let remaining = deadline.saturating_duration_since(Instant::now());
                        let phase_limited = remaining <= self.timeout;
                        // Lion floors both its clock and Duration to whole ms.
                        // Two ticks keep a sub-ms budget from expiring early.
                        let budget = remaining.min(self.timeout) + Duration::from_millis(2);
                        match lion::time::timeout(
                            budget,
                            self.stream
                                .as_ref()
                                .unwrap()
                                .send(&self.peer_ids[self.server], &request[..len]),
                        )
                        .await
                        {
                            Ok(Ok(())) => true,
                            Ok(Err(error)) => {
                                eprintln!("client send error: {error}");
                                false
                            }
                            // Classify by the deadline that bounded the send,
                            // not the time at which this task next gets polled.
                            Err(_) if phase_limited => break,
                            Err(_) => {
                                eprintln!(
                                    "client send timed out after {} ms",
                                    self.timeout.as_millis()
                                );
                                false
                            }
                        }
                    };
                    if !sent {
                        // Failed TCP connections during failover are retryable,
                        // but remain visible in the transport-error counter.
                        stats.errors += 1;
                    }
                    retry_at = Instant::now() + self.timeout;
                    resend = false;
                }
                let received = if let Some(socket) = &self.socket {
                    socket.recv_from(&mut response).map(|(len, sender)| {
                        (
                            &response[..len],
                            self.peers.iter().position(|peer| *peer == sender),
                        )
                    })
                } else {
                    match lion::time::timeout(
                        Duration::from_millis(5),
                        self.stream.as_mut().unwrap().recv(),
                    )
                    .await
                    {
                        Ok(Ok((sender, bytes))) => {
                            stream_response = bytes;
                            Ok((
                                stream_response.as_slice(),
                                self.peer_ids.iter().position(|peer| *peer == sender),
                            ))
                        }
                        Ok(Err(e)) => Err(io::Error::other(e)),
                        Err(_) => Err(io::Error::from(io::ErrorKind::TimedOut)),
                    }
                };
                match received {
                    Ok((data, sender)) => {
                        if Instant::now() >= deadline {
                            break;
                        }
                        let Some(_) = sender else {
                            stats.invalid += 1;
                            continue;
                        };
                        match self.protocol.reply(data, self.client, self.seq.value) {
                            Reply::Success(value) => {
                                if let Some(value) = value {
                                    if self.last_value.is_some_and(|last| value <= last) {
                                        stats.invalid += 1;
                                        return Err(
                                            "RSL application counter did not increase".into()
                                        );
                                    }
                                    self.last_value = Some(value);
                                }
                                // Any executor may reply; its address is not
                                // a leader hint. Keep the successful target.
                                stats.record(began.elapsed());
                                completed = true;
                                break;
                            }
                            Reply::Stale => stats.stale += 1,
                            Reply::Invalid => stats.invalid += 1,
                            Reply::Rejected => {
                                stats.rejected += 1;
                                self.server = (self.server + 1) % self.peers.len();
                                resend = true;
                            }
                        }
                    }
                    Err(e)
                        if matches!(
                            e.kind(),
                            io::ErrorKind::WouldBlock
                                | io::ErrorKind::TimedOut
                                | io::ErrorKind::Interrupted
                        ) => {}
                    Err(e) if self.stream.is_some() => {
                        // A failed connection does not end a quorum workload.
                        // StreamTransport reports connection failures through recv.
                        stats.errors += 1;
                        eprintln!("client connection error: {e}");
                        self.server = (self.server + 1) % self.peers.len();
                        resend = true;
                    }
                    Err(e) => return Err(format!("receiving workload reply: {e}")),
                }
                if !resend && Instant::now() >= retry_at {
                    stats.timeouts += 1;
                    self.server = (self.server + 1) % self.peers.len();
                    resend = true;
                }
            }
            if !completed {
                stats.unfinished += 1;
            }
            self.seq.advance()?;
        }
        Ok(())
    }
}

fn run() -> Result<(), String> {
    let mut options = BTreeMap::new();
    for arg in std::env::args().skip(1) {
        let (key, value) = arg.split_once('=').ok_or("expected key=value arguments")?;
        let endpoint = key
            .strip_prefix("ip")
            .or_else(|| key.strip_prefix("port"))
            .is_some_and(|n| n.parse::<usize>().is_ok_and(|n| n > 0));
        if !endpoint
            && !matches!(
                key,
                "protocol"
                    | "transport"
                    | "wire"
                    | "service"
                    | "nservers"
                    | "nthreads"
                    | "duration"
                    | "warmup"
                    | "settle"
                    | "timeout_ms"
                    | "connect_all"
                    | "bind"
            )
        {
            return Err(format!("unknown option {key}"));
        }
        if options.insert(key.to_owned(), value.to_owned()).is_some() {
            return Err(format!("duplicate option {key}"));
        }
    }
    let get =
        |key: &str, default: &str| options.get(key).cloned().unwrap_or_else(|| default.into());
    let transport = get("transport", "udp");
    if transport != "udp" && transport != "tcp" {
        return Err("transport must be udp or tcp".into());
    }
    let protocol_name = get("protocol", "rsl");
    let wire = get("wire", "native");
    if wire != "native" && wire != "ironfleet" {
        return Err("wire must be native or ironfleet".into());
    }
    if wire == "ironfleet" && (protocol_name != "rsl" || transport != "tcp") {
        return Err("wire=ironfleet requires protocol=rsl transport=tcp".into());
    }
    let connect_all = match get("connect_all", "false").as_str() {
        "false" => false,
        "true" if transport == "tcp" => true,
        _ => return Err("connect_all must be false, or true with transport=tcp".into()),
    };
    let protocol = match protocol_name.as_str() {
        "rsl" if wire == "ironfleet" => Protocol::IronFleetRsl,
        "rsl" => Protocol::Rsl,
        "raft" => Protocol::Raft,
        "primarybackup" => Protocol::PrimaryBackup,
        "pbft" => Protocol::Pbft,
        "epaxos" => Protocol::Epaxos,
        _ => return Err(format!("no end-to-end workload for {protocol_name}")),
    };
    let integer = |key: &str, default: &str| -> Result<u64, String> {
        get(key, default)
            .parse()
            .map_err(|_| format!("invalid {key}"))
    };
    let threads = integer("nthreads", "32")? as usize;
    let duration = integer("duration", "10")?;
    let warmup = integer("warmup", "2")?;
    let settle = integer("settle", "0")?;
    let timeout = integer("timeout_ms", "100")?;
    if threads == 0
        || threads > 4096
        || duration == 0
        || duration > 86400
        || warmup > 86400
        || settle > 86400
        || timeout == 0
        || timeout > 60000
    {
        return Err(
            "require 1..4096 threads, 1..86400 duration, 0..86400 warmup/settle, 1..60000 timeout_ms"
                .into(),
        );
    }
    let mut peers = Vec::new();
    let mut stream_service = None;
    let mut peer_ids = Vec::new();
    if let Some(path) = options.get("service") {
        let service = config::ServiceIdentity::load(path)?;
        if service.use_ssl && transport == "udp" {
            return Err("TLS service requires transport=tcp; refusing UDP downgrade".into());
        }
        for server in &service.servers {
            peers.push(config::resolve(&server.host_name_or_address, server.port)?);
            peer_ids.push(openssl::sha::sha256(&server.public_key).to_vec());
        }
        if transport == "tcp" {
            stream_service = Some(service);
        }
    } else {
        if transport == "tcp" {
            return Err("TCP requires service=FILE for server identities".into());
        }
        let count = integer("nservers", "3")?;
        if count == 0 || count > 1024 {
            return Err("nservers must be in 1..1024".into());
        }
        for i in 1..=count {
            let port = integer(&format!("port{i}"), &(4000 + i).to_string())?;
            let port = u16::try_from(port)
                .ok()
                .filter(|p| *p > 0)
                .ok_or("invalid port")?;
            peers.push(config::resolve(&get(&format!("ip{i}"), "127.0.0.1"), port)?);
        }
    }
    if peers.is_empty() {
        return Err("service has no servers".into());
    }
    let ipv4 = peers[0].is_ipv4();
    if peers.iter().any(|p| p.is_ipv4() != ipv4) {
        return Err("mixed IPv4/IPv6 servers unsupported".into());
    }
    let bind = get("bind", if ipv4 { "0.0.0.0" } else { "::" });
    let bind = config::resolve(&bind, 0)?;
    let peers = Arc::new(peers);
    let peer_ids = Arc::new(peer_ids);
    let mut workers = Vec::with_capacity(threads);
    let sequence_directory = if transport == "udp" && matches!(protocol, Protocol::Rsl) {
        Some(sequence_directory()?)
    } else {
        None
    };
    // Generic values include the local port plus an epoch. RSL UDP instead
    // reserves durable ranges because its endpoint identity can be reused.
    let epoch = SystemTime::now()
        .duration_since(UNIX_EPOCH)
        .map_err(|e| e.to_string())?
        .as_micros() as u64;
    for index in 0..threads {
        let socket = if transport == "udp" {
            let socket = UdpSocket::bind(bind).map_err(|e| format!("binding client: {e}"))?;
            socket
                .set_read_timeout(Some(Duration::from_millis(5)))
                .map_err(|e| e.to_string())?;
            Some(socket)
        } else {
            None
        };
        let client = match &socket {
            Some(socket) => socket.local_addr().map_err(|e| e.to_string())?.port() as u64,
            None => epoch.wrapping_add(index as u64),
        };
        let seq = if let Some(directory) = &sequence_directory {
            RequestSequence::persistent(directory.clone())?
        } else if matches!(
            protocol,
            Protocol::Rsl | Protocol::IronFleetRsl | Protocol::Raft
        ) {
            RequestSequence::transient(1)
        } else {
            RequestSequence::transient(
                (epoch.wrapping_mul(65537) ^ (client << 32)) & 0x3fff_ffff_ffff_ffff,
            )
        };
        workers.push((socket, client, seq));
    }
    let barrier = Arc::new(Barrier::new(threads + 1));
    let start = Arc::new(OnceLock::<Option<Instant>>::new());
    let (ready_tx, ready_rx) = std::sync::mpsc::channel();
    let mut handles = Vec::with_capacity(threads);
    for (socket, client, seq) in workers {
        let barrier = barrier.clone();
        let start = start.clone();
        let ready_tx = ready_tx.clone();
        let service = stream_service.clone();
        let peers = peers.clone();
        let peer_ids = peer_ids.clone();
        handles.push(thread::spawn(move || {
            let runtime = match lion::Runtime::new() {
                Ok(runtime) => runtime,
                Err(e) => {
                    let _ = ready_tx.send(false);
                    drop(ready_tx);
                    barrier.wait();
                    return Err(format!("creating client executor: {e}"));
                }
            };
            runtime.block_on(async move {
                let stream = match service {
                    Some(service) => {
                        stream::StreamTransport::client(service)
                            .await
                            .and_then(|stream| {
                                if connect_all {
                                    stream.connect_members()?;
                                }
                                Ok(Some(stream))
                            })
                    }
                    None => Ok(None),
                };
                if stream.is_ok() && settle > 0 {
                    // Give eager handshakes and the replicas' initial election
                    // an idle interval before any application requests.
                    lion::time::sleep(Duration::from_secs(settle)).await;
                }
                let mut warm = Stats::default();
                let mut measured = Stats::default();
                let _ = ready_tx.send(stream.is_ok());
                drop(ready_tx);
                barrier.wait();
                let stream = stream?;
                let began = start.get().unwrap().ok_or("worker initialization failed")?;
                let mut worker = Worker {
                    socket,
                    stream,
                    peers,
                    peer_ids,
                    protocol,
                    client,
                    seq,
                    server: 0,
                    last_value: None,
                    timeout: Duration::from_millis(timeout),
                };
                let measure_start = began + Duration::from_secs(warmup);
                worker.phase(measure_start, &mut warm).await?;
                worker
                    .phase(measure_start + Duration::from_secs(duration), &mut measured)
                    .await?;
                Ok::<_, String>((warm, measured, Instant::now()))
            })
        }));
    }
    drop(ready_tx);
    let ready: Vec<_> = ready_rx.iter().collect();
    let initialized = ready.len() == threads && ready.iter().all(|ok| *ok);
    let began = Instant::now();
    start.set(initialized.then_some(began)).unwrap();
    if initialized {
        println!("Client protocol={protocol_name} transport={transport} wire={wire} workers={threads} warmup_seconds={warmup} measurement_seconds={duration}");
        println!("[[READY]]");
    }
    barrier.wait();
    let measure_start = began + Duration::from_secs(warmup);
    if initialized {
        thread::sleep(measure_start.saturating_duration_since(Instant::now()));
        println!("[[MEASURE_START]]");
        io::stdout().flush().map_err(|error| error.to_string())?;
    }
    let mut ended = measure_start;
    let mut warm = Stats::default();
    let mut measured = Stats::default();
    let mut failures = Vec::new();
    let mut active_workers = 0;
    for handle in handles {
        match handle.join() {
            Ok(Ok((w, m, end))) => {
                active_workers += usize::from(m.completed > 0);
                warm.merge(w);
                measured.merge(m);
                ended = ended.max(end);
            }
            Ok(Err(e)) => failures.push(e),
            Err(_) => failures.push("worker panicked".into()),
        }
    }
    if initialized {
        println!("[[MEASURE_END]]");
        io::stdout().flush().map_err(|error| error.to_string())?;
    }
    let elapsed = ended.saturating_duration_since(measure_start).as_secs_f64();
    let throughput = if elapsed > 0.0 {
        measured.completed as f64 / elapsed
    } else {
        0.0
    };
    let avg = if measured.completed > 0 {
        measured.latency_ns as f64 / measured.completed as f64 / 1_000_000.0
    } else {
        0.0
    };
    println!(
        "{}",
        serde_json::json!({
            "protocol": protocol_name, "transport": transport, "workers": threads,
            "wire": wire,
            "tls": stream_service.as_ref().is_some_and(|service| service.use_ssl),
            "timeout_ms": timeout, "connect_all": connect_all,
            "settle_seconds": settle,
            "active_workers": active_workers, "warmup_seconds": warmup,
            "warmup_completed": warm.completed, "completed": measured.completed,
            "warmup_errors": warm.errors, "warmup_timeouts": warm.timeouts,
            "warmup_invalid_replies": warm.invalid,
            "elapsed_seconds": elapsed, "throughput_ops_s": throughput,
            "avg_latency_ms": avg, "p50_latency_ms": measured.percentile_ms(50),
            "p95_latency_ms": measured.percentile_ms(95), "p99_latency_ms": measured.percentile_ms(99),
            "percentile_relative_error_max": 0.008, "attempts": measured.attempts,
            "timeouts": measured.timeouts, "rejected": measured.rejected,
            "errors": measured.errors + failures.len() as u64, "invalid_replies": measured.invalid,
            "stale_replies": measured.stale, "unfinished": measured.unfinished,
            "worker_failures": failures,
        })
    );
    if !failures.is_empty() || active_workers != threads || measured.invalid > 0 || warm.invalid > 0
    {
        return Err("workload failed: every worker must complete measured requests without invalid replies; see counters above".into());
    }
    Ok(())
}

fn main() {
    if let Err(error) = run() {
        eprintln!("tla-rs-client: {error}");
        std::process::exit(1);
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    struct SequenceDirectory(PathBuf);

    impl SequenceDirectory {
        fn new() -> Self {
            use std::sync::atomic::{AtomicUsize, Ordering};
            static NEXT: AtomicUsize = AtomicUsize::new(0);
            loop {
                let path = std::env::temp_dir().join(format!(
                    "tla-rs-client-sequences-{}-{}",
                    std::process::id(),
                    NEXT.fetch_add(1, Ordering::Relaxed)
                ));
                match fs::create_dir(&path) {
                    Ok(()) => return Self(path),
                    Err(error) if error.kind() == io::ErrorKind::AlreadyExists => {}
                    Err(error) => panic!("{error}"),
                }
            }
        }
    }

    impl Drop for SequenceDirectory {
        fn drop(&mut self) {
            fs::remove_dir_all(&self.0).unwrap();
        }
    }

    #[test]
    fn restarted_rsl_client_rejects_cached_reply_even_after_clock_rollback() {
        let directory = SequenceDirectory::new();
        let (old, old_end) = reserve_sequence_range(&directory.0, 1000).unwrap();
        // A new allocator, with an earlier clock, must abandon the entire old
        // reservation, including requests that might have been in flight.
        let (new, _) = reserve_sequence_range(&directory.0, 999).unwrap();
        assert!(new >= old_end);
        let mut reply = [0; 18];
        reply[0] = 7;
        reply[1..9].copy_from_slice(&old.to_le_bytes());
        reply[9] = 1;
        reply[10..18].copy_from_slice(&13205u64.to_le_bytes());
        assert!(matches!(Protocol::Rsl.reply(&reply, 0, new), Reply::Stale));
        reply[1..9].copy_from_slice(&new.to_le_bytes());
        assert!(matches!(
            Protocol::Rsl.reply(&reply, 0, new),
            Reply::Success(Some(13205))
        ));
    }

    #[test]
    fn concurrent_rsl_sequence_reservations_do_not_overlap() {
        let directory = SequenceDirectory::new();
        let barrier = Arc::new(Barrier::new(8));
        let handles: Vec<_> = (0..8).map(|_| {
            let path = directory.0.clone();
            let barrier = barrier.clone();
            thread::spawn(move || {
                barrier.wait();
                reserve_sequence_range(&path, 1).unwrap()
            })
        }).collect();
        let mut ranges: Vec<_> = handles.into_iter().map(|handle| handle.join().unwrap()).collect();
        ranges.sort_unstable();
        for pair in ranges.windows(2) {
            assert!(pair[0].1 <= pair[1].0);
        }
    }

    #[test]
    fn rsl_sequence_rollover_skips_another_workers_reservation() {
        let directory = SequenceDirectory::new();
        let path = Arc::new(directory.0.clone());
        let mut first = RequestSequence::persistent(path.clone()).unwrap();
        let other = RequestSequence::persistent(path).unwrap();
        first.value = first.end - 1;
        first.advance().unwrap();
        assert!(first.value >= other.end);
        let next = first.value + 1;
        first.advance().unwrap();
        assert_eq!(first.value, next);
    }

    #[test]
    fn corrupt_or_exhausted_rsl_sequence_checkpoint_fails_closed() {
        let directory = SequenceDirectory::new();
        let checkpoint = directory.0.join("rsl-sequence");
        for value in ["corrupt".to_owned(), u64::MAX.to_string()] {
            fs::write(&checkpoint, &value).unwrap();
            assert!(reserve_sequence_range(&directory.0, 1).is_err());
            assert_eq!(fs::read_to_string(&checkpoint).unwrap(), value);
        }
    }

    #[test]
    fn ironfleet_reply_checks_sequence_length_and_big_endian_counter() {
        let mut reply = [0u8; 32];
        for (part, value) in reply.chunks_exact_mut(8).zip([6u64, 7, 8, 256]) {
            part.copy_from_slice(&value.to_be_bytes());
        }
        assert!(matches!(
            Protocol::IronFleetRsl.reply(&reply, 0, 7),
            Reply::Success(Some(256))
        ));
        assert!(matches!(
            Protocol::IronFleetRsl.reply(&reply, 0, 8),
            Reply::Stale
        ));
        for length in 0..reply.len() {
            assert!(matches!(
                Protocol::IronFleetRsl.reply(&reply[..length], 0, 7),
                Reply::Invalid
            ));
        }
        reply[23] = 9; // Declared payload length must match the counter payload.
        assert!(matches!(
            Protocol::IronFleetRsl.reply(&reply, 0, 7),
            Reply::Invalid
        ));
    }
}
