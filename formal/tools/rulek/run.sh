#!/usr/bin/env bash
# Probe C-10l2:  formal/tools/rulek/run.sh [SEED...]   (default d 2 3 4)
# Rule K (B's bd_mux.bundled_s_hold, launch-based) on the gcd_hw routes in build/tree_SEED
# (made by routeall.sh / route.sh), with the C-10l2 ablations (K10L_ABLATE=1: Kold, Knoblk,
# Knocmax, Knolat), checked by the private tcheck copy tc/ (git HEAD 16e798d + rulek edits
# to rules10l.py only: per-tag meta, per-pin LUT arcs).  -> build/out/k_SEED.{tc,json,out},
# then summ.py (fail counts) and rows.py (per-row table incl. the per-pin LUT-arc correction).
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); cd "$HERE/tc"
export PYTHONPATH=$HERE/../fasm2lean:$HERE/../prjxdelay
EXE=$HERE/tc/.lake/build/bin/tcheck
[ -x "$EXE" ] || { FORMAL_SLOT_CWD=$HERE/tc ../../../slot.sh lake build >/dev/null || exit 1; }
for t in toy toycert toypair toycredit; do
  $EXE test/$t.tc 2>/dev/null | diff -q - test/$t.expected >/dev/null || { echo "self-test $t FAILED"; exit 1; }
done
mkdir -p ../build/out
one() {
  s=$1; O=../build/tree_$s/cells/build/hw/gcd_hw
  [ -f "$O/gcd_hw.sdf" ] || { echo "seed $s: no route"; return; }
  K10L_ABLATE=1 python3 extract.py "$O" gcd_hw --cells ../build/tree_$s/cells --osc dhk --osc invhk --no-hi \
      --rules10l K --out ../build/out/k_$s.tc --json ../build/out/k_$s.json 2> ../build/out/k_$s.log \
      || { tail -n 3 ../build/out/k_$s.log; return; }
  $EXE ../build/out/k_$s.tc > ../build/out/k_$s.out 2> ../build/out/k_$s.err
  rm -f ../build/out/k_$s.tc        # 350 MB each; regenerate when needed
  echo "seed $s: $(tail -n 1 ../build/out/k_$s.err)"
}
SEEDS=${*:-d 2 3 4}
for s in $SEEDS; do one $s & done
wait
cd "$HERE"
python3 summ.py $(for s in $SEEDS; do echo build/out/k_$s.out; done)
