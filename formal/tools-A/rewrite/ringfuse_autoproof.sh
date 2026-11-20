#!/usr/bin/env bash
# ringfuse_autoproof.sh RESEARCH_CHECKOUT OUTDIR [KERNEL...]
# All-inputs Lean proofs that research's ring-fused graphs (BDC_RING_FUSE, with whatever BDC_* the caller sets, e.g.
# BDC_AUTO=1 BDC_RING_FUSE=2) compute their C function: shard C's autoproof (formal/tools/autoproof) on a COPY of the
# formal tools, with two run-time patches (the tools are not edited):
#   - dfimport models bdc's multi-result cell as bdc builds it: one cell whose value packs every result (first in the
#     low bits), a fork, one slice per result (the same patch fuse_check.py applies);
#   - autoproof --combined keeps the caller's BDC_* environment for the graph it writes (it drops it by design).
# bdc and kernels/ come from RESEARCH_CHECKOUT; the graphs from RESEARCH_CHECKOUT/cloud/fixtures/${FIXDIR:-frontend}
# (FIXDIR=frontend_exitcond: research's BDC_FE_EXITCOND fixtures). Writes OUTDIR/Auto<K>RF.lean; check each with
#   cd formal/lean && lake env lean OUTDIR/Auto<K>RF.lean     (Core Lean; prints the axioms of auto_computes)
set -euo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"; ROOT="$(cd "$HERE/../../.." && pwd)"
RS=$(cd "$1" && pwd); OUT=$(mkdir -p "$2" && cd "$2" && pwd); shift 2
KS=("${@:-xorshift collatz ipow countloop isprime}"); KS=(${KS[@]})
T=$(mktemp -d); mkdir -p $T/formal/tools
cp -r "${TOOLS:-$ROOT/formal/tools}/autoproof" "${TOOLS:-$ROOT/formal/tools}/dfimport" $T/formal/tools/
ln -s "$RS/bdc" $T/bdc; mkdir $T/kernels; for d in "$RS"/kernels/*/; do ln -s "$d" $T/kernels/; done
# kernels research keeps outside kernels/ (factorial: research/data/suite/dynsrc)
for k in factorial; do [ -e $T/kernels/$k ] || ln -s "$RS/research/data/suite/dynsrc/$k" $T/kernels/$k; done
python3 "$HERE/ringfuse_patch.py" $T/formal/tools
# 2026-11-20 (exit-test proofs of nested / varshift / brhash / quadrec): opt-in patches to the COPY, each gated by env:
#   AP_INEQ=1    autoproof infers inequality invariants (cmpi slt / sle x y = 1), kept only if true on every observation
#                and inductive along the pairing (the reachability fact `i < n` that a `!=` exit test needs);
#   AP_OPSX=1    generated files get a local auto_ops2 tactic (literal folding, masks, xor mod 2^32; lemmas proved in file);
#   CF_IFTEST=1  every C `if` is a test point in cfront (brhash's graph tests `h & 1` in its own segment);
#   CF_MULTIDECL=1 cfront reads `unsigned a = .., b = ..;` as sequential declarations (quadrec).
[ "${AP_INEQ:-}" = 1 ] && python3 "$HERE/patches/ineq_patch.py" $T/formal/tools
[ "${AP_OPSX:-}" = 1 ] && python3 "$HERE/patches/opsx_patch.py" $T/formal/tools
[ "${CF_IFTEST:-}" = 1 ] && python3 "$HERE/patches/iftest_patch.py" $T/formal/tools
[ "${CF_MULTIDECL:-}" = 1 ] && python3 "$HERE/patches/multidecl_patch.py" $T/formal/tools
# 2026-11-20 (lfsrfind / fold64 / twoloops / nest3): AP_OPSX2 (more op lemmas, any-width compares), AP_INEQR (range and
# literal-bound invariants), AP_ENTRYINV (entry invariants), AP_TRUNCINV (trunci x = x invariants); cfront: CF_BREAK,
# CF_DEFINE (#define constants), CF_CONSTTEST (tests constant at loop entry folded), CF_W64 (64-bit C).
for f in AP_OPSX2:opsx2 AP_INEQR:ineqrange CF_BREAK:cfront_break CF_DEFINE:cfront_define CF_CONSTTEST:cfront_consttest \
         AP_ENTRYINV:entryinv AP_TRUNCINV:truncinv CF_W64:cfront_w64; do
  v=${f%%:*}; [ "${!v:-}" = 1 ] && python3 "$HERE/patches/${f#*:}_patch.py" $T/formal/tools
done; true
# 2026-11-20 (isprime / factorial under BDC_SIBLING_FUSE): CF_PPIF (#if/#elif over #define constants), CF_STRLIT (string
# literals lexed, refused in the kernel), AP_XINV (hand hint invariants from patches/xinv_<func>.txt, re-checked by Lean),
# AP_OPSX4 (two proof-search fallbacks; needs AP_OPSX and AP_OPSX2).
for f in CF_PPIF:cfront_ppif CF_STRLIT:cfront_strlit AP_XINV:xinv AP_OPSX4:opsx4; do
  v=${f%%:*}; [ "${!v:-}" = 1 ] && python3 "$HERE/patches/${f#*:}_patch.py" $T/formal/tools
done; true
declare -A VEC=([nest3]="4,5 0,0 3,2 8,8 -1,3" [gcd]="12,18 7,0 0,5 -6,4" [brhash]="5,3 0,0 -1,-2" [quadrec]="3,4 0,0 -2,3" [horner]="2,3 0,0" [varshift]="5,3 0,1" [lfsrfind]="7,9 1,1" [twoloops]="3,4 0,0 -1,2" [nested]="3,2 0,1" [fold64]="5 0" [xorshift]="-1831433054,4 1,1" [collatz]="6 7 27" [ipow]="3,7 2,10 -3,5" [countloop]="3,5 0,7 10,0 -4,3"
               [isprime]="97 91 2 1 7919" [factorial]="5 0 1 2 3 4 7 12 -3")
for k in "${KS[@]}"; do
  N="$(tr '[:lower:]' '[:upper:]' <<< ${k:0:1})${k:1}${NSUF:-RF}"
  (cd $T && python3 formal/tools/autoproof/autoproof.py "$RS/cloud/fixtures/${FIXDIR:-frontend}/$k/comp/handshake_transformed.mlir" \
     "kernels/$k/$k.c" "$k" --name "$N" --graph-ns "Formal.Net.${N}Hw" --combined "$OUT/Auto$N.lean" \
     --dfargs "--ns Formal.Net.${N}Hw --graph-module Formal.Net.${N}Hw --label ${k}_ringfuse --short $k" \
     --vecs "${VEC[$k]:-1}" 2>&1 | grep -v '^emit\|^auto:' | tail -${TAILN:-1} | sed "s/^/$k: /") || echo "$k: autoproof failed"
done
rm -rf $T
