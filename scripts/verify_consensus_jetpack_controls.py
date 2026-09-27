#!/usr/bin/env python3
"""Optional Verus proof mutation checks; these do not establish new theorems."""
import os
import shutil
import subprocess
import tempfile
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]


def main():
    verus = os.environ.get("VERUS_PATH", "verus")
    verus_path = shutil.which(verus)
    if verus_path is None:
        raise SystemExit(f"Verus not found: {verus}")
    view_source = (ROOT / "src/protocol/Jetpack/view_change.rs").read_text()
    for name, old, new, theorem in [
        ("marker-without-durable-batch", "durable: s.durable.union(value)",
         "durable: s.durable", "marker_preserves"),
        ("admit-during-view-change", "s.target == s.normal && c.commands.contains(x)",
         "c.commands.contains(x)", "admission_after_recovery"),
    ]:
        assert view_source.count(old) == 1, f"mutation location changed: {name}"
        with tempfile.TemporaryDirectory(prefix="consensus-jetpack-verus-") as directory:
            work = Path(directory)
            (work / "proof_harness.rs").write_text("pub mod recovery;\npub mod view_change;\n")
            shutil.copyfile(ROOT / "src/protocol/Jetpack/recovery.rs", work / "recovery.rs")
            (work / "view_change.rs").write_text(view_source.replace(old, new))
            result = subprocess.run(
                [str(Path(verus_path).resolve()), "--crate-type=lib", "proof_harness.rs",
                 "--triggers-mode", "silent", "--no-cheating", "--verify-only-module", "view_change",
                 "--verify-function", theorem], cwd=work, capture_output=True,
                text=True, timeout=60,
            )
            output = result.stdout + result.stderr
            if result.returncode != 1 or not any(
                failure in output for failure in ["postcondition not satisfied", "assertion failed"]
            ):
                raise SystemExit(f"{name}: expected failed proof\n{output}")
            print(f"{name}: expected {theorem} proof failure found")


if __name__ == "__main__":
    main()
