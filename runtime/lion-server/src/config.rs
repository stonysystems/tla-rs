use base64::engine::general_purpose::STANDARD as BASE64;
use base64::Engine;
use openssl::asn1::Asn1Time;
use openssl::bn::{BigNum, MsbOption};
use openssl::hash::MessageDigest;
use openssl::nid::Nid;
use openssl::pkcs12::Pkcs12;
use openssl::pkey::{PKey, Private};
use openssl::rsa::Rsa;
use openssl::sha::sha256;
use openssl::x509::{X509NameBuilder, X509Ref, X509};
use serde::{Deserialize, Serialize};
use std::collections::HashSet;
use std::fs;
use std::net::{IpAddr, SocketAddr, ToSocketAddrs};
use std::path::Path;

pub const PROTOCOLS: &[&str] = &[
    "rsl",
    "twophase",
    "leaderelection",
    "primarybackup",
    "chainreplication",
    "paxos",
    "verticalpaxos",
    "raft",
    "pbft",
    "epaxos",
];

mod base64_bytes {
    use super::*;

    pub fn serialize<S: serde::Serializer>(bytes: &[u8], serializer: S) -> Result<S::Ok, S::Error> {
        serializer.serialize_str(&BASE64.encode(bytes))
    }

    pub fn deserialize<'de, D: serde::Deserializer<'de>>(
        deserializer: D,
    ) -> Result<Vec<u8>, D::Error> {
        let encoded = String::deserialize(deserializer)?;
        BASE64.decode(encoded).map_err(serde::de::Error::custom)
    }
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "PascalCase")]
pub struct PublicIdentity {
    pub friendly_name: String,
    #[serde(with = "base64_bytes")]
    pub public_key: Vec<u8>,
    pub host_name_or_address: String,
    pub port: u16,
}

#[derive(Serialize, Deserialize)]
#[serde(rename_all = "PascalCase")]
pub struct PrivateIdentity {
    pub friendly_name: String,
    #[serde(with = "base64_bytes")]
    pub pkcs12: Vec<u8>,
    pub host_name_or_address: String,
    pub port: u16,
}

#[derive(Clone, Debug, Serialize, Deserialize)]
#[serde(rename_all = "PascalCase")]
pub struct ServiceIdentity {
    pub friendly_name: String,
    pub service_type: String,
    pub servers: Vec<PublicIdentity>,
    #[serde(default)]
    pub use_ssl: bool,
}

impl ServiceIdentity {
    pub fn load(path: impl AsRef<Path>) -> Result<Self, String> {
        let service: Self = load_json(path)?;
        if service.servers.is_empty() {
            return Err("service has no servers".into());
        }
        Ok(service)
    }
}

pub fn load_json<T: serde::de::DeserializeOwned>(path: impl AsRef<Path>) -> Result<T, String> {
    let path = path.as_ref();
    let bytes = fs::read(path).map_err(|e| format!("reading {}: {e}", path.display()))?;
    serde_json::from_slice(&bytes).map_err(|e| format!("parsing {}: {e}", path.display()))
}

#[derive(Clone)]
pub struct Identity {
    pub certificate: X509,
    pub private_key: PKey<Private>,
    pub public_key: Vec<u8>,
}

impl Identity {
    pub fn from_private(private: &PrivateIdentity) -> Result<Self, String> {
        let parsed = Pkcs12::from_der(&private.pkcs12)
            .and_then(|p| p.parse2(""))
            .map_err(|e| format!("importing PKCS#12 identity: {e}"))?;
        let certificate = parsed.cert.ok_or("PKCS#12 has no certificate")?;
        let private_key = parsed.pkey.ok_or("PKCS#12 has no private key")?;
        let cert_key = certificate.public_key().map_err(|e| e.to_string())?;
        if !cert_key.public_eq(&private_key) {
            return Err("PKCS#12 certificate and private key do not match".into());
        }
        check_name(&certificate, &private.friendly_name)?;
        let public_key = certificate_public_key(&certificate)?;
        Ok(Self {
            certificate,
            private_key,
            public_key,
        })
    }

    pub fn generate(name: &str, bits: u32) -> Result<Self, String> {
        fn generate(name: &str, bits: u32) -> Result<Identity, openssl::error::ErrorStack> {
            let private_key = PKey::from_rsa(Rsa::generate(bits)?)?;
            let mut subject = X509NameBuilder::new()?;
            subject.append_entry_by_nid(Nid::COMMONNAME, name)?;
            let subject = subject.build();
            let mut serial = BigNum::new()?;
            serial.rand(128, MsbOption::MAYBE_ZERO, false)?;
            let serial = serial.to_asn1_integer()?;
            let mut certificate = X509::builder()?;
            certificate.set_version(2)?;
            certificate.set_serial_number(&serial)?;
            certificate.set_subject_name(&subject)?;
            certificate.set_issuer_name(&subject)?;
            certificate.set_pubkey(&private_key)?;
            certificate.set_not_before(Asn1Time::days_from_now(0)?.as_ref())?;
            certificate.set_not_after(Asn1Time::days_from_now(3650)?.as_ref())?;
            certificate.sign(&private_key, MessageDigest::sha256())?;
            let certificate = certificate.build();
            // .NET EncodedKeyValue.RawData is the RSA PKCS#1 key, not SPKI.
            let public_key = private_key.rsa()?.public_key_to_der_pkcs1()?;
            Ok(Identity {
                certificate,
                private_key,
                public_key,
            })
        }
        generate(name, bits).map_err(|e| format!("generating identity: {e}"))
    }

    pub fn pkcs12(&self, name: &str) -> Result<Vec<u8>, String> {
        Pkcs12::builder()
            .name(name)
            .pkey(&self.private_key)
            .cert(&self.certificate)
            .build2("")
            .and_then(|p| p.to_der())
            .map_err(|e| format!("exporting PKCS#12: {e}"))
    }
}

/// The BIT STRING contents of SubjectPublicKeyInfo, exactly matching
/// X509Certificate2.PublicKey.EncodedKeyValue.RawData (without its unused-bit byte).
pub fn certificate_public_key(certificate: &X509Ref) -> Result<Vec<u8>, String> {
    let der = certificate
        .public_key()
        .and_then(|key| key.public_key_to_der())
        .map_err(|e| format!("exporting certificate public key: {e}"))?;
    fn element<'a>(input: &mut &'a [u8], tag: u8) -> Result<&'a [u8], String> {
        if input.len() < 2 || input[0] != tag {
            return Err("invalid public key DER tag".into());
        }
        let first = input[1];
        let (header, length) = if first & 0x80 == 0 {
            (2, first as usize)
        } else {
            let n = (first & 0x7f) as usize;
            if n == 0 || n > std::mem::size_of::<usize>() || input.len() < 2 + n {
                return Err("invalid public key DER length".into());
            }
            let mut length = 0usize;
            for &byte in &input[2..2 + n] {
                length = length
                    .checked_mul(256)
                    .and_then(|l| l.checked_add(byte as usize))
                    .ok_or("public key DER length overflow")?;
            }
            (2 + n, length)
        };
        let end = header
            .checked_add(length)
            .ok_or("public key DER length overflow")?;
        if end > input.len() {
            return Err("truncated public key DER".into());
        }
        let body = &input[header..end];
        *input = &input[end..];
        Ok(body)
    }
    let mut outer = der.as_slice();
    let mut sequence = element(&mut outer, 0x30)?;
    element(&mut sequence, 0x30)?;
    let bit_string = element(&mut sequence, 0x03)?;
    if !outer.is_empty() || !sequence.is_empty() || bit_string.first() != Some(&0) {
        return Err("invalid certificate public key bit string".into());
    }
    Ok(bit_string[1..].to_vec())
}

pub fn check_name(certificate: &X509Ref, expected: &str) -> Result<(), String> {
    let mut entries = certificate.subject_name().entries();
    let first = entries.next().ok_or("certificate subject is empty")?;
    if first.object().nid() != Nid::COMMONNAME
        || entries.next().is_some()
        || first.data().as_slice() != expected.as_bytes()
    {
        return Err(format!("certificate subject does not match CN={expected}"));
    }
    Ok(())
}

#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub enum Transport {
    Udp,
    Tcp,
}

#[derive(Clone)]
pub struct ResolvedServer {
    pub identity: PublicIdentity,
    pub address: SocketAddr,
    pub peer: Vec<u8>,
}

pub struct Config {
    pub protocol: String,
    pub transport: Transport,
    pub bind: SocketAddr,
    pub me: Vec<u8>,
    pub peers: Vec<Vec<u8>>,
    pub verbose: bool,
    pub service: ServiceIdentity,
    pub identity: Identity,
    pub servers: Vec<ResolvedServer>,
}

pub fn resolve(host: &str, port: u16) -> Result<SocketAddr, String> {
    if let Ok(ip) = host.parse::<IpAddr>() {
        return Ok(SocketAddr::new(ip, port));
    }
    let addresses = (host, port)
        .to_socket_addrs()
        .map_err(|e| format!("resolving {host}:{port}: {e}"))?;
    let mut first_v6 = None;
    for address in addresses {
        if address.is_ipv4() {
            return Ok(address);
        }
        first_v6.get_or_insert(address);
    }
    first_v6.ok_or_else(|| format!("no addresses for {host}:{port}"))
}

pub fn endpoint(address: SocketAddr) -> Vec<u8> {
    let mut bytes = match address.ip() {
        IpAddr::V4(ip) => ip.octets().to_vec(),
        IpAddr::V6(ip) => ip.octets().to_vec(),
    };
    bytes.extend_from_slice(&address.port().to_be_bytes());
    bytes
}

pub fn parse_bool(value: &str) -> Result<bool, String> {
    match value {
        "true" => Ok(true),
        "false" => Ok(false),
        _ => Err(format!("expected true or false, got {value}")),
    }
}

impl Config {
    pub fn load(mut args: impl Iterator<Item = String>) -> Result<Self, String> {
        let service_path = args
            .next()
            .ok_or("usage: tla-rs-server <service.json> <private.json> [key=value]...")?;
        let private_path = args.next().ok_or("missing private identity file")?;
        let service = ServiceIdentity::load(service_path)?;
        let private: PrivateIdentity = load_json(private_path)?;
        let mut protocol = None;
        let mut transport = if service.use_ssl {
            Transport::Tcp
        } else {
            Transport::Udp
        };
        let mut host = private.host_name_or_address.clone();
        let mut port = private.port;
        let mut verbose = false;
        for arg in args {
            let (key, value) = arg
                .split_once('=')
                .ok_or_else(|| format!("expected key=value: {arg}"))?;
            match key.to_ascii_lowercase().as_str() {
                "protocol" => protocol = Some(value.to_ascii_lowercase()),
                "transport" => {
                    transport = match value {
                        "udp" => Transport::Udp,
                        "tcp" => Transport::Tcp,
                        _ => return Err(format!("unknown transport {value}; expected udp or tcp")),
                    }
                }
                "addr" => {
                    if !value.is_empty() {
                        host = value.to_owned();
                    }
                }
                "port" => {
                    let value: u16 = value.parse().map_err(|_| "invalid bind port")?;
                    if value != 0 {
                        port = value;
                    }
                }
                "verbose" => verbose = parse_bool(value)?,
                _ => return Err(format!("unknown option {key}")),
            }
        }
        let protocol = protocol
            .or_else(|| (service.service_type == "IronRSL").then(|| "rsl".into()))
            .ok_or("protocol=<name> is required for an IronProtocol service")?;
        if !PROTOCOLS.contains(&protocol.as_str()) {
            return Err(format!(
                "unknown protocol {protocol}; expected {}",
                PROTOCOLS.join(", ")
            ));
        }
        let expected_type = if protocol == "rsl" {
            "IronRSL"
        } else {
            "IronProtocol"
        };
        if service.service_type != expected_type {
            return Err(format!(
                "protocol {protocol} requires service type {expected_type}, got {}",
                service.service_type
            ));
        }
        if transport == Transport::Udp && service.use_ssl {
            return Err("UseSsl=true requires transport=tcp; UDP does not provide TLS".into());
        }
        if port == 0 {
            return Err("identity port must be nonzero".into());
        }
        let bind = resolve(&host, port)?;
        let identity = Identity::from_private(&private)?;
        let mut seen = HashSet::new();
        let mut servers = Vec::with_capacity(service.servers.len());
        let mut my_index = None;
        for (index, public) in service.servers.iter().enumerate() {
            if public.port == 0 || public.public_key.is_empty() {
                return Err(format!(
                    "server {} has an empty key or zero port",
                    index + 1
                ));
            }
            let address = resolve(&public.host_name_or_address, public.port)?;
            let peer = match transport {
                Transport::Udp => endpoint(address),
                Transport::Tcp => sha256(&public.public_key).to_vec(),
            };
            if !seen.insert(peer.clone()) {
                return Err("service contains duplicate server identities/endpoints".into());
            }
            if public.public_key == identity.public_key {
                if my_index.replace(index).is_some() {
                    return Err("private identity matches multiple service members".into());
                }
                check_name(&identity.certificate, &public.friendly_name)?;
            }
            servers.push(ResolvedServer {
                identity: public.clone(),
                address,
                peer,
            });
        }
        let my_index = my_index.ok_or("private identity is not a member of the service")?;
        let me = servers[my_index].peer.clone();
        let peers = servers.iter().map(|s| s.peer.clone()).collect();
        Ok(Self {
            protocol,
            transport,
            bind,
            me,
            peers,
            verbose,
            service,
            identity,
            servers,
        })
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn dotnet_key_encoding_and_pkcs12_round_trip() {
        let identity = Identity::generate("test.server1", 2048).unwrap();
        let pkcs1 = identity
            .private_key
            .rsa()
            .unwrap()
            .public_key_to_der_pkcs1()
            .unwrap();
        assert_eq!(
            certificate_public_key(&identity.certificate).unwrap(),
            pkcs1
        );
        assert_ne!(identity.private_key.public_key_to_der().unwrap(), pkcs1);
        let private = PrivateIdentity {
            friendly_name: "test.server1".into(),
            pkcs12: identity.pkcs12("test.server1").unwrap(),
            host_name_or_address: "127.0.0.1".into(),
            port: 1234,
        };
        let json = serde_json::to_value(&private).unwrap();
        assert_eq!(
            BASE64.decode(json["Pkcs12"].as_str().unwrap()).unwrap(),
            private.pkcs12
        );
        let imported = Identity::from_private(&private).unwrap();
        assert_eq!(imported.public_key, identity.public_key);
        assert!(imported.private_key.public_eq(&identity.private_key));
    }

    #[test]
    fn certificate_subject_is_bound_to_member_name() {
        let identity = Identity::generate("test.server1", 2048).unwrap();
        assert!(check_name(&identity.certificate, "test.server1").is_ok());
        assert!(check_name(&identity.certificate, "test.server2").is_err());
    }

    #[test]
    fn endpoint_matches_csharp_network_order() {
        assert_eq!(
            endpoint("192.0.2.1:258".parse().unwrap()),
            vec![192, 0, 2, 1, 1, 2]
        );
        let mut expected = vec![0; 18];
        expected[15] = 1;
        expected[16] = 1;
        expected[17] = 2;
        assert_eq!(endpoint("[::1]:258".parse().unwrap()), expected);
    }

    #[test]
    fn configuration_binds_membership_and_never_downgrades_ssl() {
        use std::sync::atomic::{AtomicUsize, Ordering};
        static NEXT: AtomicUsize = AtomicUsize::new(0);
        struct Directory(std::path::PathBuf);
        impl Drop for Directory {
            fn drop(&mut self) {
                let _ = fs::remove_dir_all(&self.0);
            }
        }
        let directory = Directory(std::env::temp_dir().join(format!(
            "tla-native-identity-{}-{}",
            std::process::id(),
            NEXT.fetch_add(1, Ordering::Relaxed),
        )));
        fs::create_dir(&directory.0).unwrap();
        let service_path = directory.0.join("service.json");
        let private_path = directory.0.join("private.json");
        let identity = Identity::generate("test.server1", 2048).unwrap();
        let private = PrivateIdentity {
            friendly_name: "test.server1".into(),
            pkcs12: identity.pkcs12("test.server1").unwrap(),
            host_name_or_address: "127.0.0.1".into(),
            port: 1234,
        };
        let mut service = ServiceIdentity {
            friendly_name: "test".into(),
            service_type: "IronRSL".into(),
            use_ssl: true,
            servers: vec![PublicIdentity {
                friendly_name: private.friendly_name.clone(),
                public_key: identity.public_key.clone(),
                host_name_or_address: private.host_name_or_address.clone(),
                port: private.port,
            }],
        };
        fs::write(&private_path, serde_json::to_vec(&private).unwrap()).unwrap();
        fs::write(&service_path, serde_json::to_vec(&service).unwrap()).unwrap();
        let args = || {
            vec![
                service_path.to_str().unwrap().to_owned(),
                private_path.to_str().unwrap().to_owned(),
            ]
        };
        let config = Config::load(args().into_iter()).unwrap();
        assert_eq!(config.transport, Transport::Tcp);
        assert_eq!(config.me, sha256(&identity.public_key));
        let mut udp = args();
        udp.push("transport=udp".into());
        assert!(Config::load(udp.into_iter()).is_err());
        service.use_ssl = false;
        fs::write(&service_path, serde_json::to_vec(&service).unwrap()).unwrap();
        let config = Config::load(args().into_iter()).unwrap();
        assert_eq!(config.me, vec![127, 0, 0, 1, 4, 210]);
        service.servers[0].public_key = Identity::generate("other", 2048).unwrap().public_key;
        fs::write(&service_path, serde_json::to_vec(&service).unwrap()).unwrap();
        assert!(Config::load(args().into_iter()).is_err());
    }
}
