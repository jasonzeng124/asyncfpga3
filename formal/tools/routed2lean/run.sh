#!/usr/bin/env bash
# Probe C-10d end to end (about 1-3 min):  formal/tools/routed2lean/run.sh [--no-lean]
#  1. fasm2lean (11b's tool, unchanged) on the FASM read back from the seed-1 .bit
#     -> build/ce_pair_s1.f2l.json  (physical LUTs, pips, 4-corner delays, Elmore)
#  2. routed2lean -> three 10a netlists (6 interval variants each) as Lean data:
#       Formal/Timing/RoutedCePairS1Fork.lean   launch = q1's LUT output O6
#       Formal/Timing/RoutedCePairS1Loop.lean   launch = input a at q1's physical pin B4
#       Formal/Timing/RoutedCePairS1Input.lean  launch = input a at its IOB
#     reports (windows per node and variant) -> build/*.txt, copied to fixture/
#  3. compiles the data and Formal/Timing/RoutedCePair.lean (theorems), audits axioms.
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd)
F2L=$HERE/../fasm2lean
LEAN=$(cd "$HERE/../../lean" && pwd)
B=$HERE/build; FIX=$HERE/fixture; mkdir -p "$B" "$FIX"
fail=0
python3 "$F2L/fasm2lean.py" "$F2L/fixture/ce_pair_s1.fromBit.fasm" "$F2L/ce_pair.xdc" --ns X \
    --json "$B/ce_pair_s1.f2l.json" --out /dev/null || exit 1
ROUTED=$F2L/build/ce_pair_s1_routed.json
if [ -f "$ROUTED" ]; then BEL=(--routed "$ROUTED" --belmap "$FIX/ce_pair_s1.bels.json")
else BEL=(--routed "$FIX/ce_pair_s1.bels.json"); fi
R="python3 -I $HERE/routed2lean.py $B/ce_pair_s1.f2l.json --sdf $F2L/fixture/ce_pair_s1.sdf ${BEL[*]}"
$R --launch lut:1 --ns CePairS1Fork --out "$LEAN/Formal/Timing/RoutedCePairS1Fork.lean" --report "$B/fork.txt" \
   --name fb=SLICE_X42Y95.B1 --name q2=SLICE_X42Y94.ALUT.O6 --name q2pin=SLICE_X42Y94.A1 \
   --name lap=SLICE_X42Y95.BLUT.O6@lap --name q1port="port q1 (IOB O)" > /dev/null || fail=1
$R --launch pin:1:B4 --ns CePairS1Loop --out "$LEAN/Formal/Timing/RoutedCePairS1Loop.lean" --report "$B/loop.txt" \
   --name fb=SLICE_X42Y95.B1 --name q1=SLICE_X42Y95.BLUT.O6 --name lap=SLICE_X42Y95.BLUT.O6@lap > /dev/null || fail=1
$R --launch port:a --ns CePairS1Input --out "$LEAN/Formal/Timing/RoutedCePairS1Input.lean" --report "$B/input.txt" \
   --name b4=SLICE_X42Y95.B4 --name q1=SLICE_X42Y95.BLUT.O6 --name q2=SLICE_X42Y94.ALUT.O6 \
   --name q2port="port q2 (IOB O)" > /dev/null || fail=1
cp "$B"/fork.txt "$B"/loop.txt "$B"/input.txt "$FIX/"
[ "${1:-}" = --no-lean ] && exit $fail
export PATH=$HOME/.elan/bin:$PATH
cd "$LEAN"; export LEAN_PATH=$PWD/.lake/build/lib/lean
O=.lake/build/lib/lean/Formal/Timing
python3 ../scan.py Formal/Timing/WinArray.lean Formal/Timing/Routed*.lean || fail=1
for m in WinArray RoutedCePairS1Fork RoutedCePairS1Loop RoutedCePairS1Input RoutedCePair; do
    s=$(date +%s)
    ../slot.sh lean -o $O/$m.olean Formal/Timing/$m.lean > "$B/$m.log" 2>&1 \
        && echo "  ok  Formal/Timing/$m.lean ($(( $(date +%s) - s )) s incl. slot wait)" \
        || { echo "  FAIL Formal/Timing/$m.lean"; grep -A8 error "$B/$m.log" | head -30; fail=1; }
done
cat > "$B/ax.lean" <<'LEAN'
import Formal.Timing.RoutedCePair
LEAN
grep -o '^theorem [A-Za-z0-9_]*' Formal/Timing/WinArray.lean Formal/Timing/RoutedCePair.lean \
  | sed 's/.*theorem /#print axioms Formal.Timing./' >> "$B/ax.lean"
../slot.sh lean "$B/ax.lean" > "$B/ax.log" 2>&1
if grep -q "sorryAx\|ofReduceBool\|ofReduceNat\|error" "$B/ax.log" || grep "depends on axioms" "$B/ax.log" \
     | sed 's/.*\[\(.*\)\]/\1/' | tr ',' '\n' | tr -d ' ' | grep -qv '^\(propext\|Quot.sound\|Classical.choice\)$'; then
    echo "  non-standard axiom:"; cat "$B/ax.log"; fail=1
else echo "  axioms: $(grep -c 'depends on axioms\|does not depend' "$B/ax.log") theorems audited, only propext/Quot.sound/Classical.choice"; fi
[ $fail -eq 0 ] && echo "routed2lean PASS" || { echo "routed2lean FAIL"; exit 1; }
