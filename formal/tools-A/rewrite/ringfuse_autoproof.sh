#!/usr/bin/env bash
# ringfuse_autoproof.sh RESEARCH_CHECKOUT OUTDIR [KERNEL...]
# All-inputs Lean proofs that research's ring-fused graphs (BDC_RING_FUSE, with whatever BDC_* the caller sets, e.g.
# BDC_AUTO=1 BDC_RING_FUSE=2) compute their C function: shard C's autoproof (formal/tools/autoproof) on a COPY of the
# formal tools, with two run-time patches (the tools are not edited):
#   - dfimport models bdc's multi-result cell as bdc builds it: one cell whose value packs every result (first in the
#     low bits), a fork, one slice per result (the same patch fuse_check.py applies);
#   - autoproof --combined keeps the caller's BDC_* environment for the graph it writes (it drops it by design).
# bdc and kernels/ come from RESEARCH_CHECKOUT. Writes OUTDIR/Auto<K>RF.lean; check each with
#   cd formal/lean && lake env lean OUTDIR/Auto<K>RF.lean     (Core Lean; prints the axioms of auto_computes)
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"; ROOT="$(cd "$HERE/../../.." && pwd)"
RS=$(cd "$1" && pwd); OUT=$(mkdir -p "$2" && cd "$2" && pwd); shift 2
KS=("${@:-xorshift collatz ipow countloop isprime}"); KS=(${KS[@]})
T=$(mktemp -d); mkdir -p $T/formal/tools
cp -r "$ROOT/formal/tools/autoproof" "$ROOT/formal/tools/dfimport" $T/formal/tools/
ln -s "$RS/bdc" $T/bdc; ln -s "$RS/kernels" $T/kernels
python3 "$HERE/ringfuse_patch.py" $T/formal/tools
declare -A VEC=([xorshift]="-1831433054,4 1,1" [collatz]="6 7 27" [ipow]="3,7 2,10 -3,5" [countloop]="3,5 0,7 10,0 -4,3"
               [isprime]="97 91 2 1 7919")
for k in "${KS[@]}"; do
  N="$(tr '[:lower:]' '[:upper:]' <<< ${k:0:1})${k:1}RF"
  (cd $T && python3 formal/tools/autoproof/autoproof.py "$RS/cloud/fixtures/frontend/$k/comp/handshake_transformed.mlir" \
     "kernels/$k/$k.c" "$k" --name "$N" --graph-ns "Formal.Net.${N}Hw" --combined "$OUT/Auto$N.lean" \
     --dfargs "--ns Formal.Net.${N}Hw --graph-module Formal.Net.${N}Hw --label ${k}_ringfuse --short $k" \
     --vecs "${VEC[$k]:-1}" 2>&1 | grep -v '^emit\|^auto:' | tail -1 | sed "s/^/$k: /") || echo "$k: autoproof failed"
done
rm -rf $T
