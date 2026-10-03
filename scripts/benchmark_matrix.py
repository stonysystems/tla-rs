#!/usr/bin/env python3
"""Local Lion-methodology matrix with owned children and interval /proc accounting."""
import csv
import hashlib
import json
import math
import os
from pathlib import Path
import platform
import selectors
import shutil
import signal
import subprocess
import sys
import time

ROOT = Path(__file__).resolve().parent.parent
METRICS = ["completed", "elapsed_seconds", "throughput_ops_s", "avg_latency_ms",
           "p50_latency_ms", "p95_latency_ms", "p99_latency_ms", "timeouts",
           "rejected", "errors", "invalid_replies", "stale_replies", "unfinished",
           "active_workers", "warmup_completed"]
CSV_FIELDS = ["runtime", "protocol", "transport", "tls", "wire", "configuration", "workers",
              "trial", "arm_order"] + METRICS + [
              "server_cpu_seconds", "cpu_sample_seconds", "server_cpu_percent",
              "server_rss_peak_bytes", "server_threads_peak", "cell_evidence"]


def fail(message):
    raise RuntimeError(message)


def integer(name, default, minimum=1):
    value = os.environ.get(name, str(default))
    if not value.isdecimal() or int(value) < minimum:
        fail(f"{name} must be an integer >= {minimum}")
    return int(value)


def words(name, default, allowed):
    values = os.environ.get(name, default).split()
    if not values or len(values) != len(set(values)) or any(v not in allowed for v in values):
        fail(f"{name} must be a nonempty, nonrepeating selection of {sorted(allowed)}")
    return values


def digest(path):
    with open(path, "rb") as source:
        return hashlib.file_digest(source, "sha256").hexdigest()


def save(path, value):
    path.write_text(json.dumps(value, indent=2, sort_keys=True) + "\n")


def command_output(command):
    try:
        result = subprocess.run(command, capture_output=True, text=True, check=False)
        return {"command": command, "returncode": result.returncode,
                "stdout": result.stdout.strip(), "stderr": result.stderr.strip()}
    except OSError as error:
        return {"command": command, "unavailable": str(error)}


def topology():
    allowed = sorted(os.sched_getaffinity(0))
    cpus = []
    for cpu in allowed:
        base = Path(f"/sys/devices/system/cpu/cpu{cpu}/topology")
        cpus.append({"cpu": cpu, "package": int((base / "physical_package_id").read_text()),
                     "core": int((base / "core_id").read_text()),
                     "thread_siblings": (base / "thread_siblings_list").read_text().strip()})
    distinct = {}
    for cpu in cpus:
        distinct.setdefault((cpu["package"], cpu["core"]), cpu["cpu"])
    return {"allowed_cpus": allowed, "allowed_cpu_topology": cpus,
            "distinct_physical_core_representatives": list(distinct.values())}


def proc_snapshot(pid):
    # stat fields 14/15 are process user/system ticks, NOT lifetime ps %CPU.
    fields = Path(f"/proc/{pid}/stat").read_text().rsplit(")", 1)[1].split()
    return {"pid": pid, "cpu_ticks": int(fields[11]) + int(fields[12]),
            "threads": int(fields[17]), "rss_bytes": int(fields[21]) * os.sysconf("SC_PAGE_SIZE"),
            "start_ticks": int(fields[19]), "affinity": sorted(os.sched_getaffinity(pid))}


def process_identity(pid):
    return {"pid": pid, "exe": os.readlink(f"/proc/{pid}/exe"),
            "cmdline": Path(f"/proc/{pid}/cmdline").read_bytes().replace(b"\0", b" ").decode(errors="replace"),
            "affinity": sorted(os.sched_getaffinity(pid))}


def client_connections(pid):
    inodes = set()
    for entry in Path(f"/proc/{pid}/fd").iterdir():
        try:
            target = os.readlink(entry)
        except FileNotFoundError:
            continue
        if target.startswith("socket:["):
            inodes.add(target[8:-1])
    connections = []
    for family in ("tcp", "tcp6"):
        for line in Path(f"/proc/{pid}/net/{family}").read_text().splitlines()[1:]:
            fields = line.split()
            if fields[3] == "01" and fields[9] in inodes:
                connections.append({"local_kernel_address": fields[1],
                                    "remote_kernel_address": fields[2],
                                    "remote_port": int(fields[2].split(":")[1], 16)})
    return connections


class Children:
    def __init__(self):
        self.processes = []
        self.logs = []

    def launch(self, command, log=None, cpu=None):
        if cpu is not None:
            command = ["taskset", "--cpu-list", str(cpu)] + command
        output = subprocess.PIPE
        if log is not None:
            output = log.open("wb")
            self.logs.append(output)
        process = subprocess.Popen(command, stdout=output, stderr=subprocess.STDOUT)
        self.processes.append(process)
        return process

    def stop(self):
        # Popen handles only processes this matrix started; never pkill/name matching.
        for process in reversed(self.processes):
            if process.poll() is None:
                process.terminate()
        deadline = time.monotonic() + 3
        for process in reversed(self.processes):
            try:
                process.wait(timeout=max(0, deadline - time.monotonic()))
            except subprocess.TimeoutExpired:
                process.kill()
                process.wait()
            if process.stdout is not None:
                process.stdout.close()
        for log in self.logs:
            log.close()
        self.processes.clear()
        self.logs.clear()


def alive(servers):
    for process in servers:
        if process.poll() is not None:
            fail(f"server PID {process.pid} exited with {process.returncode}")


def ready(servers, logs, timeout):
    deadline = time.monotonic() + timeout
    while time.monotonic() < deadline:
        alive(servers)
        if all("[[READY]]" in log.read_text(errors="replace").splitlines() for log in logs):
            return
        time.sleep(0.05)
    fail(f"server readiness deadline exceeded; inspect {logs}")


def native_config(logs, protocol, transport, tls, batch_size):
    configs = []
    for log in logs:
        rows = [json.loads(line.removeprefix("[[CONFIG]]").strip())
                for line in log.read_text().splitlines() if line.startswith("[[CONFIG]]")]
        if len(rows) != 1:
            fail(f"missing actual [[CONFIG]] in {log}; rebuild native binaries")
        config = rows[0]
        required = {"runtime": "native-lion", "protocol": protocol, "transport": transport,
                    "tls": tls, "tcp_nodelay": True if transport == "tcp" else None}
        if protocol == "rsl":
            required.update(batch_size=batch_size, max_log_length=1000, max_batch_delay_ms=10,
                            baseline_view_timeout_ms=1000, heartbeat_period_ms=100)
        for key, value in required.items():
            if key not in config or config[key] != value:
                fail(f"native configuration mismatch in {log}: expected {key}={value!r}, got {config.get(key)!r}")
        configs.append(config)
    return configs


def reference_metadata(launcher):
    path = launcher.parent / "reference.json"
    metadata = json.loads(path.read_text())
    required = {"runtime": "csharp-ironfleet", "protocol": "rsl", "transport": "tcp",
                "tls": False, "max_batch_size": 1, "max_log_length": 1000,
                "tcp_nodelay": True, "lion": False, "safeguard": False, "wire": "ironfleet",
                "max_batch_delay_ms": 10, "baseline_view_timeout_ms": 1000,
                "heartbeat_period_ms": 100}
    for key, value in required.items():
        if key not in metadata or metadata[key] != value:
            fail(f"reference.json must establish {key}={value!r}; unknown/mismatched baselines are not comparable")
    assets = metadata.get("binaries")
    if not isinstance(assets, list) or not assets:
        fail("reference.json must list pinned binaries with absolute path and sha256")
    for asset in assets:
        binary = Path(asset["path"])
        if not binary.is_absolute() or digest(binary) != asset["sha256"]:
            fail(f"reference binary identity mismatch: {binary}")
    return {"path": str(path), "sha256": digest(path), "configuration": metadata,
            "launcher": {"path": str(launcher), "sha256": digest(launcher)}}


def measure(children, servers, command, path, cpu, duration, warmup, ready_timeout, settle):
    client = children.launch(command, cpu=cpu)
    selector = selectors.DefaultSelector()
    selector.register(client.stdout, selectors.EVENT_READ)
    buffer = b""
    samples = []
    start = end = None
    ready_at = None
    client_identity = None
    rows = []
    deadline = time.monotonic() + settle + warmup + duration + ready_timeout + 20
    ticks_per_second = os.sysconf("SC_CLK_TCK")

    def sample():
        alive(servers)
        return {"monotonic_seconds": time.monotonic(),
                "servers": [proc_snapshot(server.pid) for server in servers]}

    def line_received(line):
        nonlocal start, end, ready_at, client_identity
        if line == "[[READY]]":
            if ready_at is not None:
                fail("duplicate client readiness marker")
            ready_at = time.monotonic()
            client_identity = process_identity(client.pid)
            expected_affinity = [cpu] if cpu is not None else sorted(os.sched_getaffinity(0))
            if client_identity["affinity"] != expected_affinity:
                fail("client actual affinity differs from selected affinity")
        elif line == "[[MEASURE_START]]":
            if ready_at is None or start is not None:
                fail("client measurement start without readiness, or duplicate start")
            start = sample()
            start["client_connections"] = client_connections(client.pid)
            samples.append(start)
        elif line == "[[MEASURE_END]]":
            if start is None or end is not None:
                fail("client measurement end without start, or duplicate end")
            end = sample()
            samples.append(end)
        elif line.startswith("{"):
            rows.append(json.loads(line))

    try:
        with path.open("wb") as log:
            while selector.get_map():
                alive(servers)
                if time.monotonic() >= deadline:
                    fail(f"client exceeded bounded workload deadline; inspect {path}")
                for key, _ in selector.select(timeout=0.1):
                    chunk = os.read(key.fd, 65536)
                    if not chunk:
                        selector.unregister(key.fileobj)
                        if buffer:
                            line_received(buffer.decode().strip())
                            buffer = b""
                        continue
                    log.write(chunk)
                    log.flush()
                    buffer += chunk
                    while b"\n" in buffer:
                        line, buffer = buffer.split(b"\n", 1)
                        line_received(line.decode().strip())
                if start is not None and end is None:
                    samples.append(sample())
        code = client.wait(timeout=max(0.01, deadline - time.monotonic()))
        if code != 0:
            fail(f"client exited with {code}; inspect {path}")
        if start is None or end is None or len(rows) != 1:
            fail(f"missing measurement markers or unique client metrics in {path}; rebuild client")
        metrics = rows[0]
        if any(key not in metrics for key in METRICS) or metrics["completed"] <= 0:
            fail(f"missing/nonproductive client metrics in {path}")
        elapsed = metrics["elapsed_seconds"]
        if not isinstance(elapsed, (int, float)) or not math.isfinite(elapsed) or elapsed <= 0:
            fail("client actual elapsed_seconds must be finite and positive")
        if not math.isclose(metrics["throughput_ops_s"], metrics["completed"] / elapsed, rel_tol=1e-5):
            fail("client throughput does not use actual elapsed time")
        seconds = end["monotonic_seconds"] - start["monotonic_seconds"]
        if seconds <= 0:
            fail("invalid CPU sampler interval")
        per_server = []
        for index, (before, after) in enumerate(zip(start["servers"], end["servers"])):
            if before["start_ticks"] != after["start_ticks"]:
                fail("server PID identity changed during measurement")
            cpu_seconds = (after["cpu_ticks"] - before["cpu_ticks"]) / ticks_per_second
            per_server.append({"pid": before["pid"], "cpu_seconds": cpu_seconds,
                               "cpu_percent": 100 * cpu_seconds / seconds,
                               "rss_peak_bytes": max(s["servers"][index]["rss_bytes"] for s in samples),
                               "threads_peak": max(s["servers"][index]["threads"] for s in samples)})
        cpu_seconds = sum(row["cpu_seconds"] for row in per_server)
        measurement = {"method": "Linux /proc/PID/stat user+system tick deltas at client marker arrival",
                       "scope": "server processes only; excludes client and launcher startup",
                       "ticks_per_second": ticks_per_second, "server_cpu_seconds": cpu_seconds,
                       "cpu_sample_seconds": seconds, "server_cpu_percent": 100 * cpu_seconds / seconds,
                       "client_actual_elapsed_seconds": elapsed,
                       "warmup_marker_interval_seconds": start["monotonic_seconds"] - ready_at,
                       "client_process": client_identity,
                       "client_connections_at_start": start["client_connections"],
                       "server_rss_peak_bytes": max(sum(p["rss_bytes"] for p in s["servers"]) for s in samples),
                       "server_threads_peak": max(sum(p["threads"] for p in s["servers"]) for s in samples),
                       "per_server_cpu": per_server, "boundary_samples": [start, end]}
        return metrics, measurement
    finally:
        selector.close()


def main():
    if platform.system() != "Linux":
        fail("the matrix requires Linux /proc and sched_getaffinity")
    protocol = os.environ.get("PROTOCOL", "rsl")
    if protocol not in {"rsl", "raft", "primarybackup", "pbft", "epaxos"}:
        fail(f"no native workload for {protocol}")
    runtimes = words("RUNTIMES", "native", {"native", "csharp"})
    configs = words("CONFIGS", "unpin 1core", {"unpin", "1core"})
    transport = os.environ.get("TRANSPORT", "tcp" if protocol == "rsl" else "udp")
    if transport not in {"tcp", "udp"}:
        fail("TRANSPORT must be tcp or udp")
    ssl = os.environ.get("USE_SSL", "false")
    if ssl not in {"true", "false"} or (ssl == "true" and transport != "tcp"):
        fail("USE_SSL must be true/false; TLS requires TCP")
    tls = ssl == "true"
    workers = integer("CLIENT_THREADS", 2)
    native_batch_size = integer("NATIVE_BATCH_SIZE", 1)
    if protocol != "rsl" and native_batch_size != 1:
        fail("NATIVE_BATCH_SIZE applies only to RSL")
    duration = integer("DURATION", 30)
    trials = integer("TRIALS", 3)
    warmup = integer("WARMUP_SECONDS", 5, 0)
    settle = integer("SETTLE_SECONDS", 3 if protocol == "rsl" else 0, 0)
    request_timeout = integer("REQUEST_TIMEOUT_MS", 1000 if protocol == "rsl" else 100)
    if request_timeout > 60000:
        fail("REQUEST_TIMEOUT_MS must be at most 60000")
    ready_timeout = integer("READY_TIMEOUT", 30)
    base_port = integer("BASE_PORT", 18401)
    nodes = 4 if protocol == "pbft" else 3
    if base_port + nodes - 1 > 65535:
        fail("BASE_PORT out of range")
    bin_dir = Path(os.environ.get("BIN_DIR", str(ROOT / "bin"))).resolve()
    binaries = {name: bin_dir / f"tla-rs-{name}" for name in ("server", "client", "config")}
    for path in binaries.values():
        if not path.is_file() or not os.access(path, os.X_OK):
            fail(f"missing native executable {path}")
    reference = None
    launcher = None
    if "csharp" in runtimes:
        if protocol != "rsl" or transport != "tcp" or tls:
            fail("the C# reference requires RSL, plaintext TCP")
        if native_batch_size != 1:
            fail("the pinned C# reference has batch size 1; native batch variants require a native-only sweep")
        value = os.environ.get("REFERENCE_SERVER", "")
        if not value or not Path(value).is_absolute():
            fail("explicit csharp runtime requires absolute REFERENCE_SERVER")
        launcher = Path(value).resolve()
        if not launcher.is_file() or not os.access(launcher, os.X_OK):
            fail(f"REFERENCE_SERVER is not executable: {launcher}")
        reference = reference_metadata(launcher)
    machine = topology()
    cores = machine["distinct_physical_core_representatives"]
    if "1core" in configs:
        if not shutil.which("taskset"):
            fail("1core requires taskset")
        if len(cores) < nodes:
            fail(f"1core needs {nodes} allowed distinct physical replica cores; found {len(cores)}")
    output = Path(os.environ.get("OUTPUT_DIR", str(ROOT / "reports/benchmarks/lion-runtime" / str(time.time_ns())))).resolve()
    output.mkdir(parents=True, exist_ok=True)
    if (output / "metadata.json").exists() or (output / "results.csv").exists():
        fail(f"refusing to overwrite existing benchmark results in {output}")
    machine.update(hostname=platform.node(), platform=platform.platform(),
                   cpuinfo=Path("/proc/cpuinfo").read_text(),
                   cgroup=Path("/proc/self/cgroup").read_text())
    metadata = {"schema_version": 1, "status": "running", "scope": "local-loopback",
                "started_at_utc": time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()),
                "comparison_kind": ("end-to-end Rust/Verus versus Dafny/C# service; different protocol wire codecs"
                                    if len(runtimes) > 1 else "single-runtime local service measurement"),
                "paper_reproduction": False, "protocol": protocol, "transport": transport, "tls": tls,
                "runtimes": runtimes, "configurations": configs, "workers": workers,
                "expected_native_batch_size": native_batch_size,
                "duration_requested_seconds": duration, "warmup_seconds": warmup, "trials": trials,
                "request_timeout_ms": request_timeout, "client_connect_all": transport == "tcp",
                "client_initial_idle_seconds": settle,
                "replicas": nodes, "base_port": base_port, "topology": machine,
                "affinity_policy": "unpin: inherited allowed CPUs; 1core: each replica on a distinct physical core; client remains unpinned in both",
                "selected_1core_cpus": cores[:nodes] if "1core" in configs else [],
                "runtime_labels": {"native": "native-lion", "csharp": "csharp-ironfleet"},
                "binaries": {name: {"path": str(path), "sha256": digest(path)} for name, path in binaries.items()},
                "driver": {"path": str(Path(__file__).resolve()), "sha256": digest(__file__)},
                "source": {"revision": command_output(["git", "-C", str(ROOT), "rev-parse", "HEAD"]),
                           "working_tree_patch": command_output(["git", "-C", str(ROOT), "diff", "HEAD", "--", "src", "runtime", "scripts"])},
                "toolchains": {"rustc": command_output(["rustc", "--version"]),
                               "python": sys.version}, "reference": reference, "schedule": [], "cells": []}
    save(output / "metadata.json", metadata)
    children = Children()
    previous_handlers = {}

    def interrupted(signum, _frame):
        raise InterruptedError(f"benchmark interrupted by signal {signum}")

    for signum in (signal.SIGINT, signal.SIGTERM):
        previous_handlers[signum] = signal.signal(signum, interrupted)
    results = []
    try:
        with (output / "results.csv").open("w", newline="") as csv_file:
            writer = csv.DictWriter(csv_file, fieldnames=CSV_FIELDS)
            writer.writeheader()
            csv_file.flush()
            for trial in range(1, trials + 1):
                # Alternate both configuration and runtime order to limit temporal bias.
                config_order = configs if trial % 2 else list(reversed(configs))
                runtime_order = runtimes if trial % 2 else list(reversed(runtimes))
                for configuration in config_order:
                    pair = output / f"trial-{trial}-{configuration}"
                    pair.mkdir()
                    service_type = "IronRSL" if protocol == "rsl" else "IronProtocol"
                    config_command = [str(binaries["config"]), f"outputdir={pair}", "name=Cluster",
                                      f"type={service_type}", f"usessl={ssl}"]
                    for node in range(1, nodes + 1):
                        config_command += [f"addr{node}=127.0.0.1", f"port{node}={base_port + node - 1}"]
                    with (pair / "config.log").open("wb") as log:
                        subprocess.run(config_command, stdout=log, stderr=subprocess.STDOUT, check=True,
                                       timeout=ready_timeout)
                    service = pair / f"Cluster.{service_type}.service.txt"
                    service_hash = digest(service)
                    for order, runtime in enumerate(runtime_order, 1):
                        cell = pair / runtime
                        cell.mkdir()
                        metadata["schedule"].append({"trial": trial, "configuration": configuration,
                                                     "runtime": runtime, "arm_order": order})
                        save(output / "metadata.json", metadata)
                        servers = []
                        logs = []
                        try:
                            for node in range(1, nodes + 1):
                                private = pair / f"Cluster.{service_type}.server{node}.private.txt"
                                log = cell / f"server{node}.log"
                                command = [str(binaries["server"] if runtime == "native" else launcher),
                                           str(service), str(private), f"protocol={protocol}",
                                           f"transport={transport}", "verbose=false"]
                                servers.append(children.launch(command, log, cores[node - 1] if configuration == "1core" else None))
                                logs.append(log)
                            ready(servers, logs, ready_timeout)
                            observed_config = native_config(logs, protocol, transport, tls, native_batch_size) if runtime == "native" else reference["configuration"]
                            wire = "native" if runtime == "native" else "ironfleet"
                            evidence = {"runtime": metadata["runtime_labels"][runtime], "trial": trial,
                                        "configuration": configuration, "wire": wire, "service_sha256": service_hash,
                                        "service_path": str(service), "server_configuration": observed_config,
                                        "server_processes": [process_identity(p.pid) for p in servers],
                                        "client_binary": metadata["binaries"]["client"],
                                        "client_affinity": machine["allowed_cpus"]}
                            for node, process in enumerate(evidence["server_processes"]):
                                expected_affinity = [cores[node]] if configuration == "1core" else machine["allowed_cpus"]
                                if process["affinity"] != expected_affinity:
                                    fail(f"server {node + 1} actual affinity differs from selected affinity")
                            client_command = [str(binaries["client"]), f"protocol={protocol}", f"transport={transport}",
                                              f"service={service}", f"nthreads={workers}", f"duration={duration}",
                                              f"warmup={warmup}", f"wire={wire}", f"timeout_ms={request_timeout}",
                                              f"connect_all={str(transport == 'tcp').lower()}", f"settle={settle}"]
                            evidence["client_command"] = client_command
                            save(cell / "evidence.json", evidence)
                            metrics, measurement = measure(children, servers, client_command, cell / "client.log",
                                                           None,
                                                           duration, warmup, ready_timeout, settle)
                            if metrics.get("protocol") != protocol or metrics.get("workers") != workers:
                                fail("client reported unexpected protocol/concurrency")
                            alive(servers)
                            evidence.update(metrics=metrics, measurement=measurement)
                            save(cell / "evidence.json", evidence)
                            if metrics.get("timeout_ms") != request_timeout or metrics.get("connect_all") != (transport == "tcp"):
                                fail("client reported unexpected timeout/connection policy")
                            if transport == "tcp":
                                observed_ports = sorted(c["remote_port"] for c in measurement["client_connections_at_start"])
                                expected_ports = sorted(port for port in range(base_port, base_port + nodes) for _ in range(workers))
                                if observed_ports != expected_ports:
                                    fail("client did not establish the matched all-replica TCP connection set")
                            row = {"runtime": evidence["runtime"], "protocol": protocol, "transport": transport,
                                   "tls": tls, "wire": wire, "configuration": configuration, "workers": workers,
                                   "trial": trial, "arm_order": order, "cell_evidence": str(cell / "evidence.json")}
                            row.update({key: metrics[key] for key in METRICS})
                            row.update({key: measurement[key] for key in CSV_FIELDS if key in measurement})
                            writer.writerow(row)
                            csv_file.flush()
                            results.append(row)
                            metadata["cells"].append(str(cell / "evidence.json"))
                            print(f"{runtime} {configuration} trial={trial}: {metrics['throughput_ops_s']:.2f} ops/s, actual={metrics['elapsed_seconds']:.6f}s", flush=True)
                            failures = {key: metrics[key] for key in ("timeouts", "rejected", "errors", "invalid_replies") if metrics[key]}
                            if failures:
                                print(f"WARNING workload failures in {cell}: {failures}", file=sys.stderr, flush=True)
                            if metrics["errors"] or metrics["invalid_replies"]:
                                fail(f"workload transport/protocol errors; measured evidence retained in {cell}")
                        finally:
                            children.stop()
        expected = trials * len(configs) * len(runtimes)
        if len(results) != expected:
            fail(f"incomplete matrix: {len(results)}/{expected} cells")
        # No ratios are emitted for unverified external services or unmatched cells.
        ratios = []
        if set(runtimes) == {"native", "csharp"}:
            for configuration in configs:
                for trial in range(1, trials + 1):
                    pair = [row for row in results if row["configuration"] == configuration and row["trial"] == trial]
                    native = next(row for row in pair if row["runtime"] == "native-lion")
                    csharp = next(row for row in pair if row["runtime"] == "csharp-ironfleet")
                    ratios.append({"configuration": configuration, "trial": trial,
                                   "native_over_csharp_throughput": native["throughput_ops_s"] / csharp["throughput_ops_s"],
                                   "native_cell": native["cell_evidence"], "csharp_cell": csharp["cell_evidence"]})
        metadata.update(status="complete", matched_ratios=ratios,
                        finished_at_utc=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
        save(output / "metadata.json", metadata)
        print(f"Measured results: {output / 'results.csv'}", flush=True)
    except BaseException as error:
        metadata.update(status="failed", error=f"{type(error).__name__}: {error}",
                        finished_at_utc=time.strftime("%Y-%m-%dT%H:%M:%SZ", time.gmtime()))
        save(output / "metadata.json", metadata)
        raise
    finally:
        children.stop()
        for signum, handler in previous_handlers.items():
            signal.signal(signum, handler)


if __name__ == "__main__":
    try:
        main()
    except (RuntimeError, OSError, ValueError, subprocess.SubprocessError) as error:
        print(f"ERROR: {error}", file=sys.stderr)
        sys.exit(1)
