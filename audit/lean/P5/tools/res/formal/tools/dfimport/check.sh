#!/usr/bin/env bash
# Drift check for probe C-8i: regenerate the imported gcd_hw graph and its
# schedule certificates from the MLIR bdc compiles, and fail if they differ from
# the committed Lean.  A change in bdc's parser, fusion plan or lowering, or in
# the kernel's handshake MLIR, then breaks this check (and, if the committed
# files are regenerated, breaks the proofs in Formal/Net/GcdHwProof.lean unless
# the new graph still computes gcdC).
#   formal/tools/dfimport/check.sh            # diff only (seconds)
#   formal/tools/dfimport/check.sh --lean     # also re-check the Lean files
# bdc's environment knobs are pinned to the gcd_hw build defaults.
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../../.." && pwd)"
LEAN="$ROOT/formal/lean/Formal/Net"
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
unset BDC_OP_FUSION BDC_CONST_FOLD BDC_FORK_FUSION BDC_MAX_FUSE_NODES BDC_PROBE
python3 "$HERE/mlir2lean.py" -o "$TMP/GcdHw.lean" --segments "$TMP/GcdHwSeg.lean"
fail=0
for f in GcdHw.lean GcdHwSeg.lean; do
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
    Formal/Net/GcdHwSeg.lean Formal/Net/GcdHwProof.lean || fail=1
fi
exit $fail
