#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
VERUS_PATH="${VERUS_PATH:-$HOME/verus/verus}"
mode=""
run_tests=false
for option in "$@"; do
    case "$option" in
        --no-verify|--reuse-protocol) mode="$option" ;;
        --test) run_tests=true ;;
        *) printf 'Usage: %s [--no-verify|--reuse-protocol] [--test]\n' "$0" >&2; exit 2 ;;
    esac
done
[[ -x "$VERUS_PATH" ]] || { printf 'Set VERUS_PATH to the Verus executable\n' >&2; exit 1; }
VERUS_PATH="$(realpath "$VERUS_PATH")"
VERUS_DIR="$(dirname "$VERUS_PATH")"
mkdir -p "$ROOT/bin"
if [[ "$mode" != --reuse-protocol ]]; then
    args=(--crate-name tla_protocol --crate-type=rlib -C opt-level=3 --compile)
    if [[ "$mode" == --no-verify ]]; then
        printf 'Compiling protocol without verification (explicit --no-verify).\n'
        args+=(--no-verify)
    fi
    "$VERUS_PATH" "${args[@]}" "$ROOT/src/lib.rs" -o "$ROOT/bin/libtla_protocol.rlib"
fi
[[ -f "$ROOT/bin/libtla_protocol.rlib" ]] || { printf 'Native protocol rlib missing\n' >&2; exit 1; }
# Same Rust toolchain as Verus; owned Rust values never cross a foreign ABI.
# Unit-separator encoding preserves paths containing whitespace.
protocol_flags="-L"$'\x1f'"dependency=$VERUS_DIR"$'\x1f'"-L"$'\x1f'"dependency=$ROOT/bin"$'\x1f'"--extern"$'\x1f'"tla_protocol=$ROOT/bin/libtla_protocol.rlib"
export CARGO_ENCODED_RUSTFLAGS="${CARGO_ENCODED_RUSTFLAGS:+$CARGO_ENCODED_RUSTFLAGS$'\x1f'}$protocol_flags"
export CARGO_ENCODED_RUSTDOCFLAGS="${CARGO_ENCODED_RUSTDOCFLAGS:+$CARGO_ENCODED_RUSTDOCFLAGS$'\x1f'}$protocol_flags"
cargo build --locked --release --manifest-path "$ROOT/runtime/lion-server/Cargo.toml" --bins
if [[ "$run_tests" == true ]]; then
    cargo test --locked --release --manifest-path "$ROOT/runtime/lion-server/Cargo.toml"
    env -u CARGO_ENCODED_RUSTFLAGS -u CARGO_ENCODED_RUSTDOCFLAGS cargo test --locked --manifest-path "$ROOT/runtime/lion-io/Cargo.toml"
fi
for binary in tla-rs-server tla-rs-config tla-rs-client; do
    install -m 0755 "$ROOT/runtime/lion-server/target/release/$binary" "$ROOT/bin/$binary"
done
printf 'Built native Lion server, configuration tool, and client in %s/bin\n' "$ROOT"
