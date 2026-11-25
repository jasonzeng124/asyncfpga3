#!/usr/bin/env bash
# tv_gate.sh RESEARCH_CHECKOUT KERNEL GRAPH.mlir [OUTDIR]   (shard A, 2026-11-20) -- translation-validation gate
# Exit 0 iff formal proves in Lean (standard axioms only) that GRAPH.mlir, imported under the caller's BDC_* knobs (export
# BDC_AUTO=1 etc. before calling), computes KERNEL's C (RESEARCH_CHECKOUT/kernels/KERNEL/KERNEL.c, or EXTRA_C): every
# input where the C returns, every schedule, token level; trusting cfront's reading of the C and dfimport. Use it for an
# UNTRUSTED graph edit (ring_dec_route.py, ...): keep the edit only on exit 0. Tries the flag sets of exitcond_gate.sh,
# each with AP_DEC=1 (the n - 1 candidate). cfront's reading under each CF_* set was tested against gcc on the kernels
# listed in FOR-RESEARCH A28 / A30 / A33; test it again for a new kernel.
set -uo pipefail
export PATH="$HOME/.elan/bin:$PATH"
RS=$(cd "$1" && pwd); K=$2; G=$(readlink -f "$3"); OUT=${4:-$(mktemp -d)}
HERE=$(cd "$(dirname "$0")" && pwd); LEAN=$HERE/../../lean
FX=$(mktemp -d); mkdir -p "$FX/$K/comp"; cp "$G" "$FX/$K/comp/handshake_transformed.mlir"
REL=$(python3 -c "import os,sys; print(os.path.relpath(sys.argv[1], sys.argv[2]))" "$FX" "$RS/cloud/fixtures")
N="$(tr '[:lower:]' '[:upper:]' <<< ${K:0:1})${K:1}TV"
try() {
  local O=$OUT/$2; mkdir -p "$O"
  env $1 AP_DEC=1 FIXDIR="$REL" NSUF=TV "$HERE/ringfuse_autoproof.sh" "$RS" "$O" "$K" > "$O/log" 2>&1 || return 1
  local F=$O/Auto$N.lean; [ -f "$F" ] || return 1
  echo "#print axioms Formal.Net.Auto$N.auto_computes" >> "$F"
  local r; r=$(cd "$LEAN" && lake env lean -DautoImplicit=false "$F" 2>&1) || return 1
  echo "$r" | grep -q "error" && return 1
  echo "$r" | grep -q "depends on axioms: \[propext, Classical.choice, Quot.sound\]" || return 1
  grep -qE "sorry|native_decide|^axiom" "$F" && return 1
  echo "$K: PROVED ($F; flags: ${1:-none})"; return 0
}
try "" s0 && exit 0
try "AP_INEQ=1 AP_OPSX=1 CF_MULTIDECL=1 CF_IFTEST=1" s1 && exit 0
try "AP_INEQ=1 AP_OPSX=1 CF_MULTIDECL=1 CF_W64=1 CF_CONSTTEST=1 CF_BREAK=1 CF_DEFINE=1 AP_OPSX2=1 AP_INEQR=1 AP_ENTRYINV=1 AP_TRUNCINV=1" s2 && exit 0
echo "$K: not proved under any flag set (keep the unedited graph)"; exit 1
