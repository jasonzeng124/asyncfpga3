#!/usr/bin/env bash
# Negative control for probe C-8v (ipow import).  Mutates the ipow handshake MLIR
# in a temporary copy (constant2, the shift amount of `e >> 1`, 1 -> 2), then
#  1. shows formal/tools/dfimport/check.sh-style drift: the regenerated Lean differs;
#  2. compiles the regenerated graph + certificates (they check: they describe
#     the mutated graph) and the UNCHANGED hand-written IpowHwProof.lean against
#     them in an overlay; the proof must FAIL (e2's target no longer matches).
# Nothing under formal/lean/Formal or .lake/build is touched.
# Exit 0 iff both controls fire.
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"
ROOT="$(cd "$HERE/../../../.." && pwd)"
L="$ROOT/formal/lean"
export PATH="$HOME/.elan/bin:$PATH"
TMP="$(mktemp -d)"; trap 'rm -rf "$TMP"' EXIT
unset BDC_OP_FUSION BDC_CONST_FOLD BDC_FORK_FUSION BDC_MAX_FUSE_NODES BDC_PROBE
SRC="$ROOT/cloud/fixtures/frontend/ipow/comp/handshake_transformed.mlir"
sed 's/handshake.name = "constant2", value = 1 : i32/handshake.name = "constant2", value = 2 : i32/' "$SRC" > "$TMP/mut.mlir"
cmp -s "$SRC" "$TMP/mut.mlir" && { echo "[negctl] mutation did not apply"; exit 1; }
mkdir -p "$TMP/src/Formal/Net"
python3 "$ROOT/formal/tools/dfimport/mlir2lean.py" "$TMP/mut.mlir" -o "$TMP/src/Formal/Net/IpowHw.lean" \
  --segments "$TMP/src/Formal/Net/IpowHwSeg.lean" \
  --ns Formal.Net.IpowHw --graph-module Formal.Net.IpowHw --label ipow_ps --short ipow
ok=1
# the docstring names the source path; compare the rest
if diff <(tail -n +8 "$L/Formal/Net/IpowHw.lean") <(tail -n +8 "$TMP/src/Formal/Net/IpowHw.lean") >/dev/null \
   && diff -q "$L/Formal/Net/IpowHwSeg.lean" "$TMP/src/Formal/Net/IpowHwSeg.lean" >/dev/null; then
  echo "[negctl] FAIL: mutation not visible as drift"; ok=0
else
  echo "[negctl] ok: drift detected:"; diff "$L/Formal/Net/IpowHw.lean" "$TMP/src/Formal/Net/IpowHw.lean" | grep '^[<>].*shrsi'
fi
cp "$L/Formal/Net/IpowHwProof.lean" "$TMP/src/Formal/Net/"
CHK="$TMP/chk"; mkdir -p "$CHK"; cp -rs "$L/.lake/build/lib/lean/Formal" "$CHK/"
cd "$L"
for m in IpowHw IpowHwSeg; do
  rm -f "$CHK/Formal/Net/$m.olean" "$CHK/Formal/Net/$m.ilean"
  FORMAL_SLOT_CWD="$L" "$ROOT/formal/slot.sh" lake env sh -c 'LEAN_PATH="$1:$LEAN_PATH" exec lean -o "$2" "$3"' \
    sh "$CHK" "$CHK/Formal/Net/$m.olean" "$TMP/src/Formal/Net/$m.lean" > "$TMP/$m.log" 2>&1 \
    || { echo "[negctl] mutated $m did not compile (unexpected):"; grep error "$TMP/$m.log" | head; ok=0; }
done
rm -f "$CHK/Formal/Net/IpowHwProof.olean"
if FORMAL_SLOT_CWD="$L" "$ROOT/formal/slot.sh" lake env sh -c 'LEAN_PATH="$1:$LEAN_PATH" exec lean -o "$2" "$3"' \
    sh "$CHK" "$CHK/Formal/Net/IpowHwProof.olean" "$TMP/src/Formal/Net/IpowHwProof.lean" > "$TMP/p.log" 2>&1; then
  echo "[negctl] FAIL: the proof still checks against the mutated graph"; ok=0
else
  echo "[negctl] ok: IpowHwProof fails on the mutated graph:"; grep -m3 'error' "$TMP/p.log"
fi
[ $ok -eq 1 ] && echo "[negctl] PASS (both controls fired)" && exit 0
exit 1
