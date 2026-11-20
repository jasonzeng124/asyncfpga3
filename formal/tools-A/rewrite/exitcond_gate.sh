#!/usr/bin/env bash
# exitcond_gate.sh RESEARCH_CHECKOUT KERNEL [OUTDIR]   (shard A, 2026-11-20)
# Translation-validation gate for BDC_FE_EXITCOND: exit 0 iff formal proves, in Lean (standard axioms only), that the
# kernel's frontend_exitcond graph under BDC_AUTO=1 computes the kernel's C (every input where the C returns, every
# schedule; token level; trusting cfront's reading of the C and dfimport). Any failure -> exit 1: keep the default
# fixture. Proved this way on 2026-11-20: brhash countloop fold64 horner isprime lfsrfind nest3 nested quadrec
# twoloops varshift xorshift. gcd fails (its knob graph is a different function on C-overflow inputs, FOR-RESEARCH A28).
# Needs formal/setup.sh's Lean (formal/lean built far enough for Formal.Net.AutoLib).
set -uo pipefail
export PATH="$HOME/.elan/bin:$PATH"
RS=$1; K=$2; OUT=${3:-$(mktemp -d)}
HERE=$(cd "$(dirname "$0")" && pwd); LEAN=$HERE/../../lean
N="$(tr '[:lower:]' '[:upper:]' <<< ${K:0:1})${K:1}EC"
FLAGS="AP_INEQ=1 AP_OPSX=1 CF_MULTIDECL=1"
case $K in brhash|nested|quadrec|varshift) FLAGS="$FLAGS CF_IFTEST=1";;
  *) FLAGS="$FLAGS CF_W64=1 CF_CONSTTEST=1 CF_BREAK=1 CF_DEFINE=1 AP_OPSX2=1 AP_INEQR=1 AP_ENTRYINV=1 AP_TRUNCINV=1";; esac
env $FLAGS FIXDIR=frontend_exitcond NSUF=EC BDC_AUTO=1 "$HERE/ringfuse_autoproof.sh" "$RS" "$OUT" "$K" || exit 1
F=$OUT/Auto$N.lean; [ -f "$F" ] || { echo "$K: no proof generated"; exit 1; }
echo "#print axioms Formal.Net.Auto$N.auto_computes" >> "$F"
r=$(cd "$LEAN" && lake env lean -DautoImplicit=false "$F" 2>&1) || { echo "$K: lean failed"; echo "$r" | tail -3; exit 1; }
if echo "$r" | grep -q "error"; then echo "$K: Lean error"; echo "$r" | grep error | head -3; exit 1; fi
if echo "$r" | grep -q "depends on axioms: \[propext, Classical.choice, Quot.sound\]" && ! grep -qE "sorry|native_decide|^axiom" "$F"; then
  echo "$K: PROVED ($F)"; exit 0; fi
echo "$K: not proved (axioms: $(echo "$r" | grep 'depends on' | head -1))"; exit 1
