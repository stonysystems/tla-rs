#!/usr/bin/env python3
"""Build or exec the pinned, benchmark-only original Dafny/C# IoScheduler server."""

import argparse
import hashlib
import json
import os
from pathlib import Path
import platform
import re
import shutil
import subprocess
import sys
import tarfile
import tempfile
import urllib.request
import zipfile

PIN = "aa5bebe74369003b16193d73d43727e95dcf4ea0"
REPOSITORY = "https://github.com/stonysystems/lion"
APP = "lion-benchmark/ironfleet/ironrsl-app"
SDK = "6.0.428"
DAFNY = "3.4.0"
SCONS = "4.8.1"


def fail(message):
    raise RuntimeError(message)


def sha256(path):
    return hashlib.sha256(Path(path).read_bytes()).hexdigest()


def capture(args, **kwargs):
    return subprocess.check_output([str(a) for a in args], text=True, **kwargs).strip()


def run(args, **kwargs):
    subprocess.run([str(a) for a in args], check=True, **kwargs)


def download(url, destination):
    print(f"Downloading {url}", file=sys.stderr)
    with urllib.request.urlopen(url) as response, destination.open("wb") as target:
        shutil.copyfileobj(response, target)


def executable(candidates):
    for candidate in candidates:
        if candidate and Path(candidate).is_file() and os.access(candidate, os.X_OK):
            return Path(candidate).resolve()
    return None


def extract_tar(archive, destination):
    with tarfile.open(archive) as contents:
        # Refuse archive traversal even on Python versions without extraction filters.
        root = destination.resolve()
        for member in contents.getmembers():
            target = (root / member.name).resolve()
            if not target.is_relative_to(root) or member.issym() or member.islnk():
                fail(f"Unsafe archive member: {member.name}")
        contents.extractall(destination)


def prerequisites(args, cache):
    tools = cache / "tools"
    tools.mkdir(parents=True, exist_ok=True)
    home = Path.home()
    dotnet = executable([args.dotnet, tools / f"dotnet-{SDK}/dotnet",
                         home / ".local/share/dotnet6/dotnet", home / ".dotnet/dotnet",
                         shutil.which("dotnet")])
    dafny = next((Path(p).resolve() for p in [args.dafny_path,
                  tools / f"dafny-{DAFNY}/dafny", home / f".dafny/dafny-{DAFNY}/dafny"]
                  if p and ((Path(p) / "Dafny.dll").is_file() or
                            (Path(p) / "dafny.dll").is_file())), None)
    scons = executable([args.scons, tools / f"scons-{SCONS}/bin/scons",
                        home / ".local/bin/scons",
                        home / ".local/share/lion-scons-venv/bin/scons", shutil.which("scons")])
    acquisitions = []
    missing = [name for name, value in [(".NET 6 SDK", dotnet), ("Dafny 3.4.0", dafny),
                                       ("SCons", scons)] if value is None]
    if missing and not args.install_prerequisites:
        fail("Missing " + ", ".join(missing) + ". Supply --dotnet/--dafny-path/--scons, "
             "or explicitly pass --install-prerequisites to acquire pinned tools in " + str(tools))
    if dotnet is None:
        destination = tools / f"dotnet-{SDK}"
        archive = tools / f"dotnet-sdk-{SDK}-linux-x64.tar.gz"
        metadata_url = "https://dotnetcli.blob.core.windows.net/dotnet/release-metadata/6.0/releases.json"
        with urllib.request.urlopen(metadata_url) as response:
            releases = json.load(response)
        sdk = next(sdk for release in releases["releases"] for sdk in release.get("sdks", [])
                   if sdk["version"] == SDK)
        asset = next(asset for asset in sdk["files"] if asset["rid"] == "linux-x64"
                     and asset["name"].endswith(".tar.gz"))
        download(asset["url"], archive)
        if hashlib.sha512(archive.read_bytes()).hexdigest() != asset["hash"].lower():
            fail(".NET SDK SHA512 does not match Microsoft's release metadata")
        destination.mkdir(exist_ok=True)
        extract_tar(archive, destination)
        dotnet = destination / "dotnet"
        acquisitions.append({"tool": "dotnet", "url": asset["url"], "sha512": asset["hash"]})
    if dafny is None:
        archive = tools / f"dafny-{DAFNY}.zip"
        url = f"https://github.com/dafny-lang/dafny/releases/download/v{DAFNY}/dafny-{DAFNY}-x64-ubuntu-16.04.zip"
        download(url, archive)
        destination = tools / f"dafny-{DAFNY}"
        destination.mkdir(exist_ok=True)
        with zipfile.ZipFile(archive) as contents:
            for name in contents.namelist():
                if not (destination / name).resolve().is_relative_to(destination.resolve()):
                    fail(f"Unsafe zip member: {name}")
            contents.extractall(destination)
        dafny = destination / "dafny"
        acquisitions.append({"tool": "dafny", "url": url, "sha256": sha256(archive)})
    if scons is None:
        destination = tools / f"scons-{SCONS}"
        run([sys.executable, "-m", "venv", destination])
        run([destination / "bin/python", "-m", "pip", "install", f"SCons=={SCONS}"])
        scons = destination / "bin/scons"
        acquisitions.append({"tool": "scons", "package": f"SCons=={SCONS}"})
    env = os.environ.copy()
    env.update(DOTNET_ROOT=str(dotnet.parent), DOTNET_MULTILEVEL_LOOKUP="0",
               DOTNET_ROLL_FORWARD="Major", DOTNET_CLI_TELEMETRY_OPTOUT="1",
               DOTNET_SKIP_FIRST_TIME_EXPERIENCE="1", DOTNET_CLI_HOME=str(cache / "dotnet-home"),
               NUGET_PACKAGES=str(cache / "nuget-packages"),
               PATH=str(dotnet.parent) + os.pathsep + env["PATH"])
    # Dafny 3.4 targets an older runtime; Major permits it to run on the private .NET 6.
    # The built net6 server itself only permits patch-level runtime roll-forward.
    sdk_list = capture([dotnet, "--list-sdks"], env=env)
    if not any(line.startswith(SDK + " ") for line in sdk_list.splitlines()):
        fail(f"Selected dotnet lacks SDK {SDK}: {dotnet}; use the pinned SDK or a separate cache")
    dll = dafny / "Dafny.dll"
    if not dll.is_file():
        dll = dafny / "dafny.dll"
    version = capture([dotnet, dll, "/version"], env=env)
    if not re.search(r"\b3\.4\.0(?:\.|\b)", version):
        fail(f"Expected Dafny 3.4.0, got: {version}")
    provenance = {"dotnet": {"path": str(dotnet), "sha256": sha256(dotnet),
                              "sdk": SDK, "info": capture([dotnet, "--info"], env=env)},
                  "dafny": {"path": str(dll), "sha256": sha256(dll), "version": version},
                  "scons": {"path": str(scons), "sha256": sha256(scons),
                            "version": capture([scons, "--version"], env=env)},
                  "python": {"path": sys.executable, "version": sys.version},
                  "acquisitions": acquisitions}
    return dotnet, dafny, scons, env, provenance


def build(arguments):
    parser = argparse.ArgumentParser(description=__doc__, epilog=(
        "Builds only original IronRSLCounterServer in a fresh private cache directory; "
        "never invokes upstream run.sh or modifies the Lion checkout. Compilation skips "
        "Dafny re-verification. Output: tla-rs-csharp-reference + reference.json. "
        "Use RUNTIMES='native csharp' REFERENCE_SERVER=/printed/path with the benchmark. "
        "Required tools: Linux x86_64, Python 3.9+, git, .NET SDK 6.0.428, Dafny 3.4.0, "
        "SCons; MathNet.Numerics 4.15.0 is restored in the isolated NuGet cache. "
        "--install-prerequisites downloads missing pinned tools into cache, never globally."))
    parser.add_argument("--cache", type=Path, default=Path(os.environ.get("XDG_CACHE_HOME", str(Path.home() / ".cache"))) / "tla-rs/lion-reference")
    parser.add_argument("--source", type=Path, help="Existing Lion git checkout (reads pinned git objects, not worktree files)")
    parser.add_argument("--dotnet", default=os.environ.get("REFERENCE_DOTNET"), help="Path to dotnet with SDK 6.0.428")
    parser.add_argument("--dafny-path", default=os.environ.get("REFERENCE_DAFNY_PATH"), help="Directory containing Dafny.dll 3.4.0")
    parser.add_argument("--scons", default=os.environ.get("REFERENCE_SCONS"), help="Path to SCons executable")
    parser.add_argument("--install-prerequisites", action="store_true")
    args = parser.parse_args(arguments)
    if platform.system() != "Linux" or platform.machine() not in ("x86_64", "amd64"):
        fail("The reference acquisition and memfd launcher currently require Linux x86_64")
    cache = args.cache.expanduser().resolve()
    repository = Path(__file__).resolve().parent.parent
    if cache.is_relative_to(repository):
        fail("Reference cache/output must be outside the production repository")
    cache.mkdir(parents=True, exist_ok=True)
    dotnet, dafny, scons, env, tools = prerequisites(args, cache)
    source = args.source
    if source is None:
        cargo = Path(os.environ.get("CARGO_HOME", str(Path.home() / ".cargo")))
        candidates = sorted(cargo.glob("git/checkouts/lion-*/aa5bebe"))
        source = next((p for p in candidates if (p / ".git").exists()), None)
    if source is None:
        source = cache / "lion.git"
        if not source.exists():
            run(["git", "clone", "--bare", REPOSITORY + ".git", source])
    source = source.resolve()
    resolved = capture(["git", "-C", source, "rev-parse", PIN + "^{commit}"])
    if resolved != PIN:
        fail("Lion source does not contain the exact pinned commit")
    build_dir = Path(tempfile.mkdtemp(prefix="build-" + PIN[:7] + "-", dir=cache))
    # Export committed objects, so neither dirty source files nor stale generated C# leak in.
    archive = build_dir / "source.tar"
    run(["git", "-C", source, "archive", "--format=tar", "--output", archive, PIN, APP])
    extract_tar(archive, build_dir)
    app = build_dir / APP
    sources = {str(p.relative_to(app)): sha256(p) for p in sorted(app.rglob("*")) if p.is_file()}
    framework = (app / "src/Dafny/Distributed/Common/Native/IoFramework.cs").read_text()
    if framework.count("client.NoDelay = true;") != 2:
        fail("Pinned IoScheduler does not contain both expected TCP_NODELAY fixes")
    # global.json constrains SDK selection even when another SDK is installed.
    (build_dir / "global.json").write_text(json.dumps({"sdk": {"version": SDK, "rollForward": "disable"}}))
    command = [str(scons), "--no-verify", "--dafny-path=" + str(dafny), "bin/IronRSLCounterServer.dll"]
    run(command, cwd=app, env=env)
    output = build_dir / "reference"
    output.mkdir()
    shutil.copytree(app / "bin", output / "app")
    launcher = output / "tla-rs-csharp-reference"
    shutil.copyfile(Path(__file__).resolve(), launcher)
    launcher.chmod(0o755)
    binaries = [{"path": str(p), "sha256": sha256(p)}
                for p in sorted((output / "app").rglob("*")) if p.is_file()]
    binaries.append({"path": str(launcher), "sha256": sha256(launcher)})
    metadata = {
        "schema_version": 1, "runtime": "csharp-ironfleet", "protocol": "rsl",
        "transport": "tcp", "tls": False, "wire": "ironfleet",
        "lion": False, "safeguard": False, "tcp_nodelay": True,
        "max_batch_size": 1, "max_log_length": 1000,
        "baseline_view_timeout_ms": 1000, "heartbeat_period_ms": 100,
        "max_batch_delay_ms": 10, "max_integer_val": 9223372036854775807,
        "source_repository": REPOSITORY, "source_revision": PIN, "source_subdirectory": APP,
        "source_archive_sha256": sha256(archive), "source_hashes": sources,
        "source_patches": [], "generated_csharp_sha256": sha256(app / "src/Dafny/Distributed/Services/RSL/Main.i.cs"),
        "build_command": command, "build_configuration": "Release", "dafny_verification": False,
        "toolchains": tools, "binaries": binaries,
        "server_assembly": str(output / "app/IronRSLCounterServer.dll"),
        "dotnet": str(dotnet), "service_type_normalization": "IronRSL -> IronRSLCounter only",
        "comparison_scope": "End-to-end Rust/Verus versus Dafny/C# services, not identical protocol binaries",
        "wire_encoding": {"tcp_length": "u64be", "identity": "RSA PKCS#1 DER, SHA256 identifier",
                          "request": "u64be(0),u64be(sequence),u64be(8),u64be(0)",
                          "reply": "u64be(6),u64be(sequence),u64be(8),u64be(counter)"},
    }
    (output / "reference.json").write_text(json.dumps(metadata, indent=2) + "\n")
    print(f"REFERENCE_SERVER={launcher}")


def launch(arguments):
    if len(arguments) < 2:
        fail("Usage: tla-rs-csharp-reference SERVICE PRIVATE [protocol=rsl transport=tcp verbose=false]")
    service_path, private_path = map(lambda p: Path(p).resolve(), arguments[:2])
    verbose = "false"
    seen = set()
    for arg in arguments[2:]:
        key, sep, value = arg.partition("=")
        if not sep or key in seen:
            fail(f"Invalid or duplicate reference option: {arg}")
        seen.add(key)
        allowed = {"protocol": {"rsl"}, "transport": {"tcp"}, "verbose": {"true", "false"},
                   "tls": {"false"}, "ssl": {"false"}, "lion": {"false"}, "safeguard": {"false"}}
        if key not in allowed or value not in allowed[key]:
            fail(f"Unsupported reference option: {arg}; only RSL / plaintext TCP / original C# IO is supported")
        if key == "verbose":
            verbose = value
    service = json.loads(service_path.read_text())
    if service.get("ServiceType") not in ("IronRSL", "IronRSLCounter"):
        fail("Reference requires an IronRSL counter service")
    if service.get("UseSsl") is not False:
        fail("Reference requires explicit UseSsl=false in the shared service identity")
    if service.get("Transport", "tcp") != "tcp":
        fail("Reference does not support UDP service identities")
    if not private_path.is_file():
        fail(f"Private identity does not exist: {private_path}")
    service["ServiceType"] = "IronRSLCounter"
    # An inherited anonymous file avoids modifying input, stale normalized copies, and
    # wrapper processes. .NET reads this exact service JSON, while PID stays unchanged.
    fd = os.memfd_create("ironrsl-reference-service", flags=0)
    with os.fdopen(os.dup(fd), "w") as normalized:
        json.dump(service, normalized)
    os.set_inheritable(fd, True)
    metadata = json.loads((Path(__file__).resolve().parent / "reference.json").read_text())
    dotnet = metadata["dotnet"]
    env = os.environ.copy()
    env.update(DOTNET_ROOT=str(Path(dotnet).parent), DOTNET_MULTILEVEL_LOOKUP="0",
               DOTNET_ROLL_FORWARD="LatestPatch", DOTNET_CLI_TELEMETRY_OPTOUT="1")
    os.execve(dotnet, [dotnet, metadata["server_assembly"], f"/proc/self/fd/{fd}", str(private_path),
                      "lion=false", "safeguard=false", "verbose=" + verbose], env)


if __name__ == "__main__":
    try:
        if Path(sys.argv[0]).name == "tla-rs-csharp-reference":
            launch(sys.argv[1:])
        elif len(sys.argv) > 1 and sys.argv[1] == "build":
            build(sys.argv[2:])
        else:
            fail("Use build_lion_reference.sh to build the isolated reference")
    except (RuntimeError, OSError, ValueError, subprocess.CalledProcessError, StopIteration) as error:
        print(f"Lion reference: {error}", file=sys.stderr)
        sys.exit(1)
