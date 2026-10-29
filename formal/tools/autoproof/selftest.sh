#!/usr/bin/env bash
# Self-test of formal/tools/autoproof (probe C-vk2). Logs in $OUT (default build/autoproof/selftest).
#   formal/tools/autoproof/selftest.sh           # positives (Lean), negative controls, operand-swap sweeps
#   formal/tools/autoproof/selftest.sh --quick   # no Lean: generator verdicts only (~1 min)
set -uo pipefail
HERE="$(cd "$(dirname "$0")" && pwd)"; ROOT="$(cd "$HERE/../../.." && pwd)"; cd "$ROOT"
export PATH="$HOME/.elan/bin:$PATH"
OUT=${OUT:-$ROOT/build/autoproof/selftest}; mkdir -p "$OUT"
QUICK=0; [ "${1:-}" = --quick ] && QUICK=1
A=formal/tools/autoproof/autoproof.py; F=cloud/fixtures/frontend; M=formal/tools/verify/mutate.py
fail=0
ok() { echo "ok    $*"; }
bad() { echo "WRONG $*"; fail=1; }

# 1. positives: the claimed files regenerate identically and check
cp formal/lean/Formal/Net/Auto{Ipow,Collatz,Xorshift,Gcd,GcdSubi0}.lean "$OUT/" 2>/dev/null
"$HERE/gen_claimed.sh" > "$OUT/gen.log" 2>&1 || bad "gen_claimed.sh failed"
for k in Ipow Collatz Xorshift Gcd GcdSubi0; do
  cmp -s "$OUT/Auto$k.lean" "formal/lean/Formal/Net/Auto$k.lean" && ok "Auto$k.lean regenerates identically" \
    || bad "Auto$k.lean differs from the committed one after regeneration"
done
if [ $QUICK = 0 ]; then
  (cd formal && ./check.sh Formal/Net/AutoLib.lean Formal/Net/AutoIpow.lean Formal/Net/AutoCollatz.lean \
    Formal/Net/AutoXorshift.lean Formal/Net/AutoGcd.lean Formal/Net/AutoGcdSubi0Hw.lean \
    Formal/Net/AutoGcdSubi0HwSeg.lean Formal/Net/AutoGcdSubi0.lean) > "$OUT/check.log" 2>&1 \
    && ok "check.sh on the claimed files: $(grep 'declarations checked' "$OUT/check.log")" || bad "check.sh failed (see $OUT/check.log)"
fi

# 2. negative controls: real mutants and a wrong C must not prove
python3 $M $F/gcd/comp/handshake_transformed.mlir "$OUT/gcd_subi1.mlir" --swap subi1 2>/dev/null
python3 $M $F/ipow/comp/handshake_transformed.mlir "$OUT/ipow_c2.mlir" --const constant2=2 2>/dev/null
neg() {  # neg NAME WANT_RC args...
  local name=$1 want=$2; shift 2
  python3 $A "$@" > "$OUT/$name.log" 2>&1; local rc=$?
  [ $rc = "$want" ] && ok "$name: exit $rc $(grep -m1 AUTOPROOF "$OUT/$name.log" | cut -c1-120)" \
    || bad "$name: exit $rc (want $want)"
}
neg neg-gcd-subi1 1 "$OUT/gcd_subi1.mlir" formal/tools/autoproof/ref/gcd_binary.c gcd --name N --graph-ns N --combined /dev/null
neg neg-ipow-c2 1 "$OUT/ipow_c2.mlir" kernels/ipow/ipow.c ipow --name N --graph-ns N --combined /dev/null
neg neg-ipow-wrongC 1 $F/ipow/comp/handshake_transformed.mlir formal/tools/verify/test/ipow_wrong.c ipow --name N --graph-ns N --combined /dev/null
# the proof forced through for the mutant (correspondence of the correct graph): Lean must reject it
python3 $A "$OUT/ipow_c2.mlir" kernels/ipow/ipow.c ipow --name IpowC2 --graph-ns Formal.Net.AutoIpowC2G \
  --corr-from $F/ipow/comp/handshake_transformed.mlir --combined "$OUT/AutoIpowC2.lean" \
  --dfargs "--ns Formal.Net.AutoIpowC2G --graph-module X --label ipow_c2 --short ipow" > "$OUT/forced.log" 2>&1
if [ $QUICK = 0 ]; then
  formal/slot.sh lake env lean "$OUT/AutoIpowC2.lean" > "$OUT/forced-lean.log" 2>&1
  grep -q ": error" "$OUT/forced-lean.log" && ok "forced proof for the ipow const mutant: Lean rejects it ($(grep -c ': error' "$OUT/forced-lean.log") errors)" \
    || bad "Lean ACCEPTED a proof for the ipow constant mutant"
fi

# 3. operand-swap sweeps: every commutative swap (and gcd's subi0) must prove, no other swap may
for k in ipow collatz xorshift gcd; do
  if [ $QUICK = 1 ]; then python3 "$HERE/sweep.py" $k --no-lean --out "$OUT/sweep" > "$OUT/sweep-$k.log" 2>&1
  else python3 "$HERE/sweep.py" $k --out "$OUT/sweep" > "$OUT/sweep-$k.log" 2>&1; fi
  tail -1 "$OUT/sweep-$k.log" | grep -q ': OK' && ok "$(tail -1 "$OUT/sweep-$k.log") ($(grep -c . "$OUT/sweep-$k.log") lines)" \
    || bad "$(tail -1 "$OUT/sweep-$k.log")"
done
[ $fail -eq 0 ] && echo "autoproof selftest: OK" || echo "autoproof selftest: FAIL"
exit $fail
