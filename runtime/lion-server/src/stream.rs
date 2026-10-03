//! Lion TCP transport with the original IoFramework wire format. TLS peers prove
//! possession of their certificate key; configured members are pinned by the
//! .NET EncodedKeyValue bytes and exact CN. Plain TCP deliberately retains the
//! legacy unauthenticated, one-way public-key introduction (never a TLS fallback).
use crate::config::{
    certificate_public_key, check_name, resolve, Config, Identity, PublicIdentity, ServiceIdentity,
};
use lion::net::{TcpListener, TcpStream};
use openssl::sha::sha256;
use openssl::ssl::{Ssl, SslContext, SslContextBuilder, SslMethod, SslVerifyMode, SslVersion};
use openssl::x509::X509Ref;
use parking_lot::Mutex;
use std::collections::HashMap;
use std::io;
use std::net::SocketAddr;
use std::pin::Pin;
use std::sync::atomic::{AtomicU64, Ordering};
use std::sync::Arc;
use std::task::{Context, Poll};
use std::time::Duration;
use tokio::io::{AsyncRead, AsyncReadExt, AsyncWrite, AsyncWriteExt, ReadBuf};
use tokio::sync::{mpsc, oneshot, watch, OwnedSemaphorePermit, Semaphore};
use tokio_openssl::SslStream;

const MAX_FRAME_BYTES: usize = 8 * 1024 * 1024;
const MAX_KEY_BYTES: usize = 16 * 1024;
const CONNECTION_QUEUE: usize = 32;
const RECEIVE_QUEUE: usize = 256;
const MAX_CONNECTIONS: usize = 256;
const HANDSHAKE_TIMEOUT: Duration = Duration::from_secs(5);
const WRITE_TIMEOUT: Duration = Duration::from_secs(10);
type Packet = (Vec<u8>, Vec<u8>);
type Received = Result<Packet, ReceiveError>;

#[derive(Debug)]
pub enum ReceiveError {
    Peer(String),
    Fatal(String),
}

impl std::fmt::Display for ReceiveError {
    fn fmt(&self, out: &mut std::fmt::Formatter<'_>) -> std::fmt::Result {
        match self {
            Self::Peer(message) | Self::Fatal(message) => out.write_str(message),
        }
    }
}

impl std::error::Error for ReceiveError {}

struct SendRequest {
    bytes: Vec<u8>,
    completion: Option<oneshot::Sender<Result<(), String>>>,
}

#[derive(Clone)]
struct ConnectionSlot {
    id: u64,
    sender: mpsc::Sender<SendRequest>,
}

#[derive(Clone)]
struct Remote {
    identity: PublicIdentity,
    address: SocketAddr,
}

struct Shared {
    identity: Identity,
    tls: Option<SslContext>,
    known: Arc<HashMap<Vec<u8>, Remote>>,
    connections: Mutex<HashMap<Vec<u8>, ConnectionSlot>>,
    incoming: mpsc::Sender<Received>,
    shutdown: watch::Receiver<bool>,
    permits: Arc<Semaphore>,
    next_id: AtomicU64,
}

pub struct StreamTransport {
    shared: Arc<Shared>,
    incoming: mpsc::Receiver<Received>,
    shutdown: watch::Sender<bool>,
    local_addr: Option<SocketAddr>,
}

impl StreamTransport {
    pub async fn bind(config: &Config) -> Result<Self, String> {
        let listener = TcpListener::bind(config.bind)
            .await
            .map_err(|e| format!("binding TCP {}: {e}", config.bind))?;
        let address = listener.local_addr().map_err(|e| e.to_string())?;
        let mut transport = Self::new(config.identity.clone(), &config.service)?;
        transport.local_addr = Some(address);
        let shared = transport.shared.clone();
        lion::spawn(async move {
            let mut shutdown = shared.shutdown.clone();
            loop {
                tokio::select! {
                    _ = shutdown.changed() => return,
                    result = listener.accept() => match result {
                        Ok((socket, address)) => {
                            let permit = match shared.permits.clone().try_acquire_owned() {
                                Ok(permit) => permit,
                                Err(_) => {
                                    report(&shared, ReceiveError::Peer(format!("TCP connection limit reached; rejecting {address}"))).await;
                                    continue;
                                }
                            };
                            let shared = shared.clone();
                            lion::spawn(async move { accept_connection(shared, socket, address, permit).await; });
                        }
                        Err(error) => {
                            report(&shared, ReceiveError::Fatal(format!("accepting TCP connection: {error}"))).await;
                            return;
                        }
                    }
                }
            }
        });
        Ok(transport)
    }

    /// Clients do not listen; replies travel over the same bidirectional stream.
    pub async fn client(service: ServiceIdentity) -> Result<Self, String> {
        Self::new(Identity::generate("client", 2048)?, &service)
    }

    /// Start a connection to every configured replica. Handshakes run on the
    /// owning Lion executor; failures still arrive through `recv`.
    pub fn connect_members(&self) -> Result<(), String> {
        for peer in self.shared.known.keys() {
            self.route(peer)?;
        }
        Ok(())
    }

    fn new(identity: Identity, service: &ServiceIdentity) -> Result<Self, String> {
        let mut known = HashMap::with_capacity(service.servers.len());
        for member in &service.servers {
            let peer = sha256(&member.public_key).to_vec();
            let remote = Remote {
                identity: member.clone(),
                address: resolve(&member.host_name_or_address, member.port)?,
            };
            if known.insert(peer, remote).is_some() {
                return Err("duplicate TCP member public key".into());
            }
        }
        let known = Arc::new(known);
        let tls = if service.use_ssl {
            Some(tls_context(&identity, known.clone())?)
        } else {
            None
        };
        let (sender, incoming) = mpsc::channel(RECEIVE_QUEUE);
        let (shutdown, receiver) = watch::channel(false);
        Ok(Self {
            shared: Arc::new(Shared {
                identity,
                tls,
                known,
                connections: Mutex::new(HashMap::new()),
                incoming: sender,
                shutdown: receiver,
                permits: Arc::new(Semaphore::new(MAX_CONNECTIONS)),
                next_id: AtomicU64::new(1),
            }),
            incoming,
            shutdown,
            local_addr: None,
        })
    }

    pub fn local_addr(&self) -> Option<SocketAddr> {
        self.local_addr
    }

    /// Cancellation-safe: partial frames remain owned by the connection task.
    pub async fn recv(&mut self) -> Received {
        self.incoming
            .recv()
            .await
            .ok_or_else(|| ReceiveError::Fatal("TCP transport stopped".to_owned()))?
    }

    pub async fn send(&self, peer: &[u8], bytes: &[u8]) -> Result<(), String> {
        self.send_owned(peer, bytes.to_vec()).await
    }

    /// Bounded backpressure; success means the complete frame was written, not
    /// merely queued. Cancellation after enqueue does not truncate a frame.
    pub async fn send_owned(&self, peer: &[u8], bytes: Vec<u8>) -> Result<(), String> {
        if bytes.len() > MAX_FRAME_BYTES {
            return Err("TCP message exceeds frame limit".into());
        }
        let sender = self.route(peer)?;
        let (completion, result) = oneshot::channel();
        sender
            .send(SendRequest {
                bytes,
                completion: Some(completion),
            })
            .await
            .map_err(|_| "TCP connection closed before message could be queued".to_owned())?;
        result
            .await
            .map_err(|_| "TCP connection closed before write completed".to_owned())?
    }

    /// Protocol sends are unreliable, as in the original network contract.
    /// Queue without waiting for a peer's handshake or write; failures arrive
    /// through recv(). Backpressure is bounded and never stalls protocol timers.
    pub fn enqueue_owned(&self, peer: &[u8], bytes: Vec<u8>) -> Result<(), String> {
        if bytes.len() > MAX_FRAME_BYTES {
            return Err("TCP message exceeds frame limit".into());
        }
        self.route(peer)?
            .try_send(SendRequest {
                bytes,
                completion: None,
            })
            .map_err(|error| format!("queuing TCP frame: {error}"))
    }

    fn route(&self, peer: &[u8]) -> Result<mpsc::Sender<SendRequest>, String> {
        Ok({
            let mut connections = self.shared.connections.lock();
            if let Some(connection) = connections.get(peer) {
                connection.sender.clone()
            } else {
                let remote = self
                    .shared
                    .known
                    .get(peer)
                    .cloned()
                    .ok_or("no connected client or configured member for destination")?;
                let permit = self
                    .shared
                    .permits
                    .clone()
                    .try_acquire_owned()
                    .map_err(|_| "TCP connection limit reached")?;
                let (sender, receiver) = mpsc::channel(CONNECTION_QUEUE);
                let id = self.shared.next_id.fetch_add(1, Ordering::Relaxed);
                let peer = peer.to_vec();
                connections.insert(
                    peer.clone(),
                    ConnectionSlot {
                        id,
                        sender: sender.clone(),
                    },
                );
                let shared = self.shared.clone();
                lion::spawn(async move {
                    connect_connection(shared, remote, peer, id, receiver, permit).await;
                });
                sender
            }
        })
    }
}

impl Drop for StreamTransport {
    fn drop(&mut self) {
        // Closing the owner's signal cancels listener, handshakes and active IO.
        self.shutdown.send_replace(true);
    }
}

fn validate_certificate(
    certificate: &X509Ref,
    expected: Option<&PublicIdentity>,
    known: &HashMap<Vec<u8>, Remote>,
) -> Result<Vec<u8>, String> {
    let key = certificate_public_key(certificate)?;
    let peer = sha256(&key).to_vec();
    if let Some(expected) = expected {
        if key != expected.public_key {
            return Err("TLS peer public key does not match pinned member".into());
        }
        check_name(certificate, &expected.friendly_name)?;
    } else if let Some(member) = known.get(&peer) {
        check_name(certificate, &member.identity.friendly_name)?;
    }
    Ok(peer)
}

fn tls_context(
    identity: &Identity,
    known: Arc<HashMap<Vec<u8>, Remote>>,
) -> Result<SslContext, String> {
    let mut builder = SslContextBuilder::new(SslMethod::tls()).map_err(|e| e.to_string())?;
    builder
        .set_min_proto_version(Some(SslVersion::TLS1_2))
        .map_err(|e| e.to_string())?;
    builder
        .set_certificate(&identity.certificate)
        .map_err(|e| e.to_string())?;
    builder
        .set_private_key(&identity.private_key)
        .map_err(|e| e.to_string())?;
    builder.check_private_key().map_err(|e| e.to_string())?;
    // IoFramework uses self-signed identities, not a CA. Ignore chain trust
    // exactly as it does, but require a certificate and pin recognized members.
    builder.set_verify_callback(
        SslVerifyMode::PEER | SslVerifyMode::FAIL_IF_NO_PEER_CERT,
        move |_, context| {
            context.error_depth() != 0
                || context
                    .current_cert()
                    .is_some_and(|cert| validate_certificate(cert, None, &known).is_ok())
        },
    );
    Ok(builder.build())
}

async fn report(shared: &Shared, error: ReceiveError) {
    let mut shutdown = shared.shutdown.clone();
    tokio::select! {
        _ = shutdown.changed() => {},
        _ = shared.incoming.send(Err(error)) => {},
    }
}

async fn accept_connection(
    shared: Arc<Shared>,
    socket: TcpStream,
    address: SocketAddr,
    permit: OwnedSemaphorePermit,
) {
    let mut shutdown = shared.shutdown.clone();
    let handshake = async {
        socket.set_nodelay(true).map_err(|e| e.to_string())?;
        if let Some(context) = &shared.tls {
            let ssl = Ssl::new(context).map_err(|e| e.to_string())?;
            let mut stream = SslStream::new(ssl, socket).map_err(|e| e.to_string())?;
            Pin::new(&mut stream)
                .accept()
                .await
                .map_err(|e| format!("TLS handshake: {e}"))?;
            let certificate = stream
                .ssl()
                .peer_certificate()
                .ok_or("TLS peer supplied no certificate")?;
            let peer = validate_certificate(&certificate, None, &shared.known)?;
            Ok((Connection::Tls(stream), peer))
        } else {
            let mut stream = Connection::Plain(socket);
            let key = read_frame(&mut stream, MAX_KEY_BYTES)
                .await
                .map_err(|e| format!("public-key introduction: {e}"))?;
            if key.is_empty() {
                return Err("empty public-key introduction".to_owned());
            }
            Ok((stream, sha256(&key).to_vec()))
        }
    };
    let result = tokio::select! {
        _ = shutdown.changed() => return,
        result = lion::time::timeout(HANDSHAKE_TIMEOUT, handshake) => result
            .map_err(|_| "TCP/TLS introduction timed out".to_owned()).and_then(|r| r),
    };
    let (stream, peer) = match result {
        Ok(value) => value,
        Err(error) => {
            report(
                &shared,
                ReceiveError::Peer(format!("accepting {address}: {error}")),
            )
            .await;
            return;
        }
    };
    let (sender, receiver) = mpsc::channel(CONNECTION_QUEUE);
    let id = shared.next_id.fetch_add(1, Ordering::Relaxed);
    // Multiple simultaneous connections are valid in IoFramework. Replacing
    // the route leaves the old connection draining its already queued frames.
    shared
        .connections
        .lock()
        .insert(peer.clone(), ConnectionSlot { id, sender });
    run_connection(shared, stream, peer, id, receiver, permit).await;
}

async fn connect_connection(
    shared: Arc<Shared>,
    remote: Remote,
    peer: Vec<u8>,
    id: u64,
    mut receiver: mpsc::Receiver<SendRequest>,
    permit: OwnedSemaphorePermit,
) {
    let mut shutdown = shared.shutdown.clone();
    let handshake = async {
        let socket = TcpStream::connect(remote.address)
            .await
            .map_err(|e| format!("connecting {}: {e}", remote.address))?;
        socket.set_nodelay(true).map_err(|e| e.to_string())?;
        if let Some(context) = &shared.tls {
            let mut ssl = Ssl::new(context).map_err(|e| e.to_string())?;
            ssl.set_hostname(&remote.identity.friendly_name)
                .map_err(|e| e.to_string())?;
            let expected = remote.identity.clone();
            let known = shared.known.clone();
            ssl.set_verify_callback(SslVerifyMode::PEER, move |_, context| {
                context.error_depth() != 0
                    || context.current_cert().is_some_and(|cert| {
                        validate_certificate(cert, Some(&expected), &known).is_ok()
                    })
            });
            let mut stream = SslStream::new(ssl, socket).map_err(|e| e.to_string())?;
            Pin::new(&mut stream)
                .connect()
                .await
                .map_err(|e| format!("TLS handshake: {e}"))?;
            let certificate = stream
                .ssl()
                .peer_certificate()
                .ok_or("TLS peer supplied no certificate")?;
            validate_certificate(&certificate, Some(&remote.identity), &shared.known)?;
            Ok(Connection::Tls(stream))
        } else {
            let mut stream = Connection::Plain(socket);
            write_frame(&mut stream, &shared.identity.public_key)
                .await
                .map_err(|e| format!("public-key introduction: {e}"))?;
            Ok(stream)
        }
    };
    let result = tokio::select! {
        _ = shutdown.changed() => Err("TCP transport stopped".to_owned()),
        result = lion::time::timeout(HANDSHAKE_TIMEOUT, handshake) => result
            .map_err(|_| "TCP/TLS connection timed out".to_owned()).and_then(|r| r),
    };
    match result {
        Ok(stream) => run_connection(shared, stream, peer, id, receiver, permit).await,
        Err(error) => {
            remove_connection(&shared, &peer, id);
            fail_queued(&mut receiver, &error);
            report(&shared, ReceiveError::Peer(error)).await;
        }
    }
}

fn remove_connection(shared: &Shared, peer: &[u8], id: u64) {
    let mut connections = shared.connections.lock();
    if connections
        .get(peer)
        .is_some_and(|connection| connection.id == id)
    {
        connections.remove(peer);
    }
}

fn fail_queued(receiver: &mut mpsc::Receiver<SendRequest>, error: &str) {
    receiver.close();
    while let Ok(request) = receiver.try_recv() {
        // A caller may have cancelled its send; the error still reaches recv().
        if let Some(completion) = request.completion {
            let _ = completion.send(Err(error.to_owned()));
        }
    }
}

async fn run_connection(
    shared: Arc<Shared>,
    stream: Connection,
    peer: Vec<u8>,
    id: u64,
    mut receiver: mpsc::Receiver<SendRequest>,
    _permit: OwnedSemaphorePermit,
) {
    let (mut reader, mut writer) = tokio::io::split(stream);
    let mut shutdown = shared.shutdown.clone();
    let receive = async {
        loop {
            let bytes = read_frame(&mut reader, MAX_FRAME_BYTES)
                .await
                .map_err(|e| format!("reading TCP frame: {e}"))?;
            shared
                .incoming
                .send(Ok((peer.clone(), bytes)))
                .await
                .map_err(|_| "TCP receiver stopped".to_owned())?;
        }
        #[allow(unreachable_code)]
        Ok::<(), String>(())
    };
    let send = async {
        while let Some(request) = receiver.recv().await {
            let result =
                lion::time::timeout(WRITE_TIMEOUT, write_frame(&mut writer, &request.bytes))
                    .await
                    .map_err(|_| "writing TCP frame timed out".to_owned())
                    .and_then(|r| r.map_err(|e| format!("writing TCP frame: {e}")));
            let failed = result.as_ref().err().cloned();
            if let Some(completion) = request.completion {
                let _ = completion.send(result);
            }
            if let Some(error) = failed {
                return Err(error);
            }
        }
        // Losing the preferred outbound route must not interrupt inbound data
        // on a still-live connection (e.g. simultaneous reciprocal connects).
        std::future::pending::<Result<(), String>>().await
    };
    let result = tokio::select! {
        _ = shutdown.changed() => Ok(()),
        result = receive => result,
        result = send => result,
    };
    remove_connection(&shared, &peer, id);
    let error = result
        .err()
        .unwrap_or_else(|| "TCP transport stopped".into());
    fail_queued(&mut receiver, &error);
    if !*shared.shutdown.borrow() {
        report(&shared, ReceiveError::Peer(error)).await;
    }
}

async fn read_frame(reader: &mut (impl AsyncRead + Unpin), limit: usize) -> io::Result<Vec<u8>> {
    let length = reader.read_u64().await?;
    if length > limit as u64 {
        return Err(io::Error::new(
            io::ErrorKind::InvalidData,
            "frame exceeds configured limit",
        ));
    }
    let mut bytes = vec![0; length as usize];
    reader.read_exact(&mut bytes).await?;
    Ok(bytes)
}

async fn write_frame(writer: &mut (impl AsyncWrite + Unpin), bytes: &[u8]) -> io::Result<()> {
    writer
        .write_all(&(bytes.len() as u64).to_be_bytes())
        .await?;
    writer.write_all(bytes).await?;
    writer.flush().await
}

enum Connection {
    Plain(TcpStream),
    Tls(SslStream<TcpStream>),
}

impl AsyncRead for Connection {
    fn poll_read(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        buffer: &mut ReadBuf<'_>,
    ) -> Poll<io::Result<()>> {
        match self.get_mut() {
            Self::Plain(stream) => Pin::new(stream).poll_read(cx, buffer),
            Self::Tls(stream) => Pin::new(stream).poll_read(cx, buffer),
        }
    }
}

impl AsyncWrite for Connection {
    fn poll_write(
        self: Pin<&mut Self>,
        cx: &mut Context<'_>,
        bytes: &[u8],
    ) -> Poll<io::Result<usize>> {
        match self.get_mut() {
            Self::Plain(stream) => Pin::new(stream).poll_write(cx, bytes),
            Self::Tls(stream) => Pin::new(stream).poll_write(cx, bytes),
        }
    }

    fn poll_flush(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        match self.get_mut() {
            Self::Plain(stream) => Pin::new(stream).poll_flush(cx),
            Self::Tls(stream) => Pin::new(stream).poll_flush(cx),
        }
    }

    fn poll_shutdown(self: Pin<&mut Self>, cx: &mut Context<'_>) -> Poll<io::Result<()>> {
        match self.get_mut() {
            Self::Plain(stream) => Pin::new(stream).poll_shutdown(cx),
            Self::Tls(stream) => Pin::new(stream).poll_shutdown(cx),
        }
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn framing_is_big_endian_and_rejects_oversized_input() {
        lion::Runtime::new().unwrap().block_on(async {
            let mut output = Vec::new();
            write_frame(&mut output, b"abc").await.unwrap();
            assert_eq!(output, [0, 0, 0, 0, 0, 0, 0, 3, b'a', b'b', b'c']);
            assert_eq!(read_frame(&mut output.as_slice(), 3).await.unwrap(), b"abc");
            assert_eq!(
                read_frame(&mut output.as_slice(), 2)
                    .await
                    .unwrap_err()
                    .kind(),
                io::ErrorKind::InvalidData
            );
            let truncated = &output[..output.len() - 1];
            assert_eq!(
                read_frame(&mut &truncated[..], 3).await.unwrap_err().kind(),
                io::ErrorKind::UnexpectedEof
            );
        });
    }

    #[test]
    fn tls_pins_public_key_and_member_subject() {
        let identity = Identity::generate("server1", 2048).unwrap();
        let other = Identity::generate("server1", 2048).unwrap();
        let mut public = PublicIdentity {
            friendly_name: "server1".into(),
            public_key: identity.public_key.clone(),
            host_name_or_address: "127.0.0.1".into(),
            port: 1234,
        };
        let known = HashMap::new();
        assert_eq!(
            validate_certificate(&identity.certificate, Some(&public), &known).unwrap(),
            sha256(&identity.public_key)
        );
        assert!(validate_certificate(&other.certificate, Some(&public), &known).is_err());
        public.friendly_name = "server2".into();
        assert!(validate_certificate(&identity.certificate, Some(&public), &known).is_err());
    }

    #[test]
    fn plain_and_tls_streams_exchange_frames_with_anonymous_clients() {
        let identity = Identity::generate("server1", 2048).unwrap();
        for use_ssl in [false, true] {
            lion::Runtime::new().unwrap().block_on(async {
                let public = PublicIdentity {
                    friendly_name: "server1".into(),
                    public_key: identity.public_key.clone(),
                    host_name_or_address: "127.0.0.1".into(),
                    port: 0,
                };
                let mut service = ServiceIdentity {
                    friendly_name: "test".into(),
                    service_type: "IronRSL".into(),
                    servers: vec![public],
                    use_ssl,
                };
                let peer = sha256(&identity.public_key).to_vec();
                let config = Config {
                    protocol: "rsl".into(),
                    transport: crate::config::Transport::Tcp,
                    bind: "127.0.0.1:0".parse().unwrap(),
                    me: peer.clone(),
                    peers: vec![peer.clone()],
                    verbose: false,
                    identity: identity.clone(),
                    service: service.clone(),
                    servers: Vec::new(),
                };
                let mut server = StreamTransport::bind(&config).await.unwrap();
                service.servers[0].port = server.local_addr().unwrap().port();
                let mut client = StreamTransport::client(service.clone()).await.unwrap();
                client.send(&peer, b"request").await.unwrap();
                let (client_peer, bytes) =
                    lion::time::timeout(Duration::from_secs(2), server.recv())
                        .await
                        .unwrap()
                        .unwrap();
                assert_eq!(bytes, b"request");
                server.send(&client_peer, b"response").await.unwrap();
                let (sender, bytes) = lion::time::timeout(Duration::from_secs(2), client.recv())
                    .await
                    .unwrap()
                    .unwrap();
                assert_eq!(sender, peer);
                assert_eq!(bytes, b"response");
                if use_ssl {
                    let mut untrusted = service.clone();
                    untrusted.servers[0].public_key =
                        Identity::generate("server1", 2048).unwrap().public_key;
                    let wrong_peer = sha256(&untrusted.servers[0].public_key);
                    let client = StreamTransport::client(untrusted).await.unwrap();
                    let result = lion::time::timeout(
                        Duration::from_secs(2),
                        client.send(&wrong_peer, b"must reject"),
                    )
                    .await
                    .unwrap();
                    assert!(
                        result.is_err(),
                        "TLS must reject a server with an unpinned key"
                    );
                } else {
                    service.use_ssl = true;
                    let client = StreamTransport::client(service).await.unwrap();
                    let result = lion::time::timeout(
                        Duration::from_secs(2),
                        client.send(&peer, b"must reject"),
                    )
                    .await
                    .unwrap();
                    assert!(
                        result.is_err(),
                        "TLS must not fall back to a plain TCP server"
                    );
                }
            });
        }
    }
}
