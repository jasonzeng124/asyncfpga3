#!/usr/bin/env bash
# Drift check for probes C-8i (gcd_hw), C-8v (ipow, collatz) and C-8y2 (xorshift): regenerate each imported
# graph and its schedule certificates from the MLIR bdc compiles, and fail if
# they differ from the committed Lean.  A change in bdc's parser, fusion plan or
# lowering, or in a kernel's handshake MLIR, then breaks this check (and, if the
# committed files are regenerated, breaks the hand-written proofs
# Formal/Net/GcdHwProof.lean / IpowHwProof.lean / CollatzHwProof.lean unless the new graph still
# computes the C function).
#   formal/tools/dfimport/check.sh            # diff only (seconds)
#   formal/tools/dfimport/check.sh --lean     # also re-check the Lean files
# bdc's environment knobs are pinned to the build defaults (build_hw.sh /
# build_bench.sh pass none of them; BDC_SELECT_PADS only sets delays).
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
LEAN="$ROOT/formal/lean/Formal/Net"
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
unset BDC_OP_FUSION BDC_CONST_FOLD BDC_FORK_FUSION BDC_MAX_FUSE_NODES BDC_PROBE

# kernel MLIR: build/frontend/<k>/... if present (what the build scripts read),
# else its committed copy under cloud/fixtures (cloud/setup-toolchain.sh
# restores build/frontend from there)
# (C-8y2: when the build copy is byte-identical to the fixture, name the fixture, so the
# generated header -- which records the path -- does not report a false drift)
mlir() {
  local b="$ROOT/build/frontend/$1/comp/handshake_transformed.mlir"
  local f="$ROOT/cloud/fixtures/frontend/$1/comp/handshake_transformed.mlir"
  if [ -f "$b" ] && ! cmp -s "$b" "$f"; then echo "$b"; else echo "$f"; fi
}

# gcd_hw (C-8i): the tool's defaults
python3 "$HERE/mlir2lean.py" "$(mlir gcd)" -o "$TMP/GcdHw.lean" --segments "$TMP/GcdHwSeg.lean"
# ipow (C-8v): same tool, only the Lean names differ
python3 "$HERE/mlir2lean.py" "$(mlir ipow)" -o "$TMP/IpowHw.lean" --segments "$TMP/IpowHwSeg.lean" \
  --ns Formal.Net.IpowHw --graph-module Formal.Net.IpowHw --label ipow_ps --short ipow
# collatz (C-8v): same tool, only the Lean names differ
python3 "$HERE/mlir2lean.py" "$(mlir collatz)" -o "$TMP/CollatzHw.lean" --segments "$TMP/CollatzHwSeg.lean" \
  --ns Formal.Net.CollatzHw --graph-module Formal.Net.CollatzHw --label collatz --short collatz
# xorshift (C-8y2): same tool, only the Lean names differ
python3 "$HERE/mlir2lean.py" "$(mlir xorshift)" -o "$TMP/XorshiftHw.lean" --segments "$TMP/XorshiftHwSeg.lean" \
  --ns Formal.Net.XorshiftHw --graph-module Formal.Net.XorshiftHw --label xorshift --short xorshift

fail=0
for f in GcdHw.lean GcdHwSeg.lean IpowHw.lean IpowHwSeg.lean CollatzHw.lean CollatzHwSeg.lean \
    XorshiftHw.lean XorshiftHwSeg.lean; do
  if ! diff -q "$TMP/$f" "$LEAN/$f" >/dev/null; then
    echo "[dfimport] DRIFT: $f differs from what bdc's graph generates now:"
    diff "$LEAN/$f" "$TMP/$f" | head -20
    fail=1
  else
    echo "[dfimport] ok: $f matches"
  fi
done
if [ "${1:-}" = "--lean" ] && [ $fail -eq 0 ]; then
  "$ROOT/formal/check.sh" Formal/Net/GcdHwLib.lean Formal/Net/GcdHw.lean \
    Formal/Net/GcdHwSeg.lean Formal/Net/GcdHwProof.lean \
    Formal/Net/IpowHw.lean Formal/Net/IpowHwSeg.lean \
    Formal/Net/IpowHwProof.lean Formal/Net/IpowHwLive.lean \
    Formal/Net/CollatzHw.lean Formal/Net/CollatzHwSeg.lean Formal/Net/CollatzHwProof.lean \
    Formal/Net/XorshiftHw.lean Formal/Net/XorshiftHwSeg.lean Formal/Net/XorshiftHwProof.lean || fail=1
fi
exit $fail
