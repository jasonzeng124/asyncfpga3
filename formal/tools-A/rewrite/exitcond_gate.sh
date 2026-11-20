#!/usr/bin/env bash
# exitcond_gate.sh RESEARCH_CHECKOUT KERNEL [OUTDIR]   (shard A, 2026-11-20)
# Translation-validation gate for BDC_FE_EXITCOND: exit 0 iff formal proves, in Lean (standard axioms only), that the
# kernel's frontend_exitcond graph under BDC_AUTO=1 computes the kernel's C (every input where the C returns, every
# schedule; token level; trusting cfront's reading of the C and dfimport). Any failure -> exit 1: keep the default
# fixture. Proved this way on 2026-11-20: brhash countloop fold64 horner isprime lfsrfind nest3 nested quadrec
# twoloops varshift xorshift. gcd fails (its knob graph is a different function on C-overflow inputs, FOR-RESEARCH A28).
# Trust: cfront reads the C differently under each flag set (CF_*); each reading was tested against gcc -fwrapv on the
# 12 kernels above (exitcond_cfront_cdiff*.py), not on a new kernel: run that test for any kernel added later.
# Needs formal/setup.sh's Lean (formal/lean built far enough for Formal.Net.AutoLib).
set -uo pipefail
export PATH="$HOME/.elan/bin:$PATH"
RS=$1; K=$2; OUT=${3:-$(mktemp -d)}
HERE=$(cd "$(dirname "$0")" && pwd); LEAN=$HERE/../../lean
N="$(tr '[:lower:]' '[:upper:]' <<< ${K:0:1})${K:1}EC"
try() {   # $1 = flag set; 0 iff a proof is generated and Lean accepts it with the standard axioms only
  local O=$OUT/$2; mkdir -p "$O"
  env $1 FIXDIR=frontend_exitcond NSUF=EC BDC_AUTO=1 "$HERE/ringfuse_autoproof.sh" "$RS" "$O" "$K" >/dev/null 2>&1 || return 1
  local F=$O/Auto$N.lean; [ -f "$F" ] || return 1
  echo "#print axioms Formal.Net.Auto$N.auto_computes" >> "$F"
  local r; r=$(cd "$LEAN" && lake env lean -DautoImplicit=false "$F" 2>&1) || return 1
  echo "$r" | grep -q "error" && return 1
  echo "$r" | grep -q "depends on axioms: \[propext, Classical.choice, Quot.sound\]" || return 1
  grep -qE "sorry|native_decide|^axiom" "$F" && return 1
  echo "$K: PROVED ($F; flags: ${1:-none})"; return 0
}
# flag sets in the order they were introduced (2026-11-20); the first that proves wins
try "" s0 && exit 0
try "AP_INEQ=1 AP_OPSX=1 CF_MULTIDECL=1 CF_IFTEST=1" s1 && exit 0
try "AP_INEQ=1 AP_OPSX=1 CF_MULTIDECL=1 CF_W64=1 CF_CONSTTEST=1 CF_BREAK=1 CF_DEFINE=1 AP_OPSX2=1 AP_INEQR=1 AP_ENTRYINV=1 AP_TRUNCINV=1" s2 && exit 0
echo "$K: not proved under any flag set"; exit 1
