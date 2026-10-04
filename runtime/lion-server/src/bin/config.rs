use std::collections::BTreeMap;
use std::fs::{self, OpenOptions};
use std::io::Write;
use std::os::unix::fs::OpenOptionsExt;
use std::path::{Path, PathBuf};
use tla_rs_lion_runtime::config::{
    parse_bool, Identity, PrivateIdentity, PublicIdentity, ServiceIdentity,
};

fn main() {
    if let Err(error) = run(std::env::args().skip(1)) {
        eprintln!("ERROR: {error}");
        std::process::exit(1);
    }
}

fn run(args: impl Iterator<Item = String>) -> Result<(), String> {
    let mut output = PathBuf::from(".");
    let mut name = "MyIronfleetService".to_owned();
    let mut service_type = "IronRSL".to_owned();
    let mut use_ssl = false;
    let mut verbose = false;
    let mut addresses = BTreeMap::new();
    let mut ports = BTreeMap::new();
    for arg in args {
        if arg == "--help" || arg == "-h" {
            println!("Usage: tla-rs-config outputdir=DIR name=NAME type=IronRSL|IronProtocol usessl=true|false addr1=HOST port1=PORT [addr2=HOST port2=PORT ...] [verbose=true|false]");
            println!("Defaults: name=MyIronfleetService type=IronRSL outputdir=. usessl=false verbose=false. UseSsl=true selects TLS over TCP; UDP is unencrypted and rejects UseSsl=true.");
            return Ok(());
        }
        let (key, value) = arg
            .split_once('=')
            .ok_or_else(|| format!("expected key=value: {arg}"))?;
        let key = key.to_ascii_lowercase();
        match key.as_str() {
            "outputdir" => output = PathBuf::from(value),
            "name" => name = value.into(),
            "type" => service_type = value.into(),
            "usessl" => use_ssl = parse_bool(value)?,
            "verbose" => verbose = parse_bool(value)?,
            _ => {
                if let Some(index) = key.strip_prefix("addr") {
                    let index = server_index(index)?;
                    if value.is_empty() {
                        return Err(format!("{key} cannot be empty"));
                    }
                    if addresses.insert(index, value.to_owned()).is_some() {
                        return Err(format!("duplicate {key}"));
                    }
                } else if let Some(index) = key.strip_prefix("port") {
                    let index = server_index(index)?;
                    let port: u16 = value.parse().map_err(|_| format!("invalid port {value}"))?;
                    if port == 0 {
                        return Err(format!("{key} must be nonzero"));
                    }
                    if ports.insert(index, port).is_some() {
                        return Err(format!("duplicate {key}"));
                    }
                } else {
                    return Err(format!("unknown option {key}"));
                }
            }
        }
    }
    if name.is_empty() || name.contains(['/', '\\']) || name == "." || name == ".." {
        return Err("name must be a nonempty file name without directory separators".into());
    }
    if !matches!(service_type.as_str(), "IronRSL" | "IronProtocol") {
        return Err("type must be IronRSL or IronProtocol".into());
    }
    let count = addresses
        .keys()
        .chain(ports.keys())
        .max()
        .copied()
        .ok_or("supply at least addr1 and port1")?;
    for index in 1..=count {
        if !addresses.contains_key(&index) {
            return Err(format!("missing addr{index}"));
        }
        if !ports.contains_key(&index) {
            return Err(format!("missing port{index}"));
        }
    }
    fs::create_dir_all(&output).map_err(|e| format!("creating {}: {e}", output.display()))?;
    let mut servers = Vec::with_capacity(count);
    for index in 1..=count {
        let friendly_name = format!("{name}.{service_type}.server{index}");
        let identity = Identity::generate(&friendly_name, 4096)?;
        let private = PrivateIdentity {
            friendly_name: friendly_name.clone(),
            pkcs12: identity.pkcs12(&friendly_name)?,
            host_name_or_address: addresses[&index].clone(),
            port: ports[&index],
        };
        let path = output.join(format!("{friendly_name}.private.txt"));
        write_json(&path, &private, true)?;
        if verbose {
            println!("Wrote {}", path.display());
        }
        servers.push(PublicIdentity {
            friendly_name,
            public_key: identity.public_key,
            host_name_or_address: private.host_name_or_address,
            port: private.port,
        });
    }
    let service = ServiceIdentity {
        friendly_name: name.clone(),
        service_type: service_type.clone(),
        servers,
        use_ssl,
    };
    let path = output.join(format!("{name}.{service_type}.service.txt"));
    write_json(&path, &service, false)?;
    println!("Wrote {}", path.display());
    Ok(())
}

fn server_index(value: &str) -> Result<usize, String> {
    let index: usize = value
        .parse()
        .map_err(|_| format!("invalid server index {value}"))?;
    if !(1..10000).contains(&index) {
        return Err("server indices must be between 1 and 9999".into());
    }
    Ok(index)
}

fn write_json(path: &Path, value: &impl serde::Serialize, private: bool) -> Result<(), String> {
    let mut options = OpenOptions::new();
    options
        .write(true)
        .create(true)
        .truncate(true)
        .mode(if private { 0o600 } else { 0o644 });
    let mut file = options
        .open(path)
        .map_err(|e| format!("opening {}: {e}", path.display()))?;
    if private {
        use std::os::unix::fs::PermissionsExt;
        file.set_permissions(fs::Permissions::from_mode(0o600))
            .map_err(|e| format!("securing {}: {e}", path.display()))?;
    }
    serde_json::to_writer_pretty(&mut file, value)
        .map_err(|e| format!("writing {}: {e}", path.display()))?;
    file.write_all(b"\n")
        .map_err(|e| format!("writing {}: {e}", path.display()))
}
