#!/usr/bin/env python3
"""Require proof failures for weakened Mako transaction and producer rules."""
import os
from pathlib import Path
import shutil
import subprocess
import tempfile

ROOT = Path(__file__).resolve().parents[1]
VERUS = shutil.which(os.environ.get("VERUS_PATH", "verus"))
if VERUS is None:
    raise SystemExit("Set VERUS_PATH to a Verus executable")

CONTROLS = [
    (
        "INF over a pending install", "model.rs", "invariants",
        "!s.busy.dom().contains(k) && s.progress[k] == s.tail[k]",
        "s.progress[k] == s.tail[k]",
        "close_no_pending",
    ),
    (
        "cross-epoch read of an unstable version", "model.rs", "invariants",
        "(s.tx[d].epoch < t.epoch ==> below_wm(c, s, s.tx[d]))",
        "true",
        "begin_old_dependency",
    ),
    (
        "acknowledgment before the watermark", "model.rs", "invariants",
        "s.tx.dom().contains(id) && below_wm(c, s, s.tx[id])",
        "s.tx.dom().contains(id)",
        "step_decisions",
    ),
    (
        "maximum instead of minimum across workers", "watermark_math.rs", "watermark_math",
        "bmin(minimum(v, e, sh, (count - 1) as nat), v[worker(e, sh, count as int - 1)])",
        "bmax(minimum(v, e, sh, (count - 1) as nat), v[worker(e, sh, count as int - 1)])",
        "minimum_lower",
    ),
    (
        "gossip relabeled with the receiver's current epoch", "production.rs", "production_proof",
        "views: s.views.insert((m.dst, m.epoch, m.shard),",
        "views: s.views.insert((m.dst, s.core.epoch, m.shard),",
        "receive_isolated",
    ),
    (
        "stale gossip overwrites newer progress", "production.rs", "production_proof",
        "bmax(s.views[(m.dst, m.epoch, m.shard)], m.value)",
        "m.value",
        "receive_monotone",
    ),
    (
        "OCC validates without comparing versions", "occ.rs", "occ_proof",
        "s.data[s.tx[id].reads[j].key].vc == s.tx[id].reads[j].version.vc",
        "true", "validation_correct",
    ),
    (
        "OCC validates through another writer's lock", "occ.rs", "occ_proof",
        "&&& unlocked_or_own(s, id, s.tx[id].reads[j].key)",
        "&&& true", "validation_prior_writer",
    ),
    (
        "OCC checks before acquiring every write lock", "occ.rs", "occ_proof",
        "Action::Check { id } => s.tx.dom().contains(id) && s.tx[id].phase is Locking && all_locked(s, id)",
        "Action::Check { id } => s.tx.dom().contains(id) && s.tx[id].phase is Locking",
        "step_locking",
    ),
    (
        "OCC certifies without validating every read", "occ.rs", "occ_proof",
        "s.tx[id].phase is Checking && all_checked(s.tx[id])",
        "s.tx[id].phase is Checking", "step_shape",
    ),
    (
        "OCC omits read dependencies from the version vector", "occ.rs", "occ_vectors",
        "max(if t.tickets.dom().contains(sh) { t.tickets[sh] } else { 0 }, read_max(t.reads, sh, t.reads.len()))",
        "if t.tickets.dom().contains(sh) { t.tickets[sh] } else { 0 }",
        "merged_covers_read",
    ),
]

for name, filename, module, before, after, lemma in CONTROLS:
    with tempfile.TemporaryDirectory(prefix="mako-proof-control-") as directory:
        dest = Path(directory)
        for source in (ROOT / "src/protocol/Mako").glob("*.rs"):
            shutil.copy2(source, dest / source.name)
        model = dest / filename
        original = model.read_text()
        if original.count(before) != 1:
            raise SystemExit(f"{name}: mutation anchor is not unique")
        model.write_text(original.replace(before, after))
        result = subprocess.run(
            [VERUS, "--crate-type=lib", "harness.rs", "--no-cheating",
             "--verify-only-module", module, "--verify-function", lemma,
             "--triggers-mode", "selective"],
            cwd=dest, text=True, stdout=subprocess.PIPE, stderr=subprocess.STDOUT,
            timeout=180,
        )
        # A compiler error, timeout, or solver resource limit is not evidence
        # that the intended proof obligation rejected the weakened protocol.
        output = result.stdout
        proof_failure = "assertion failed" in output or "postcondition not satisfied" in output or "precondition not satisfied" in output
        if result.returncode == 0 or not proof_failure or "error[E" in output or "Resource limit" in output:
            raise SystemExit(f"{name}: expected a proof failure\n{output}")
        print(f"PASS: Verus rejects {name}", flush=True)
