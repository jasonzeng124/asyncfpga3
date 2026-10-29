#!/usr/bin/env bash
# Probe C-10g:  formal/tools/tcheck/run2.sh [SEED...]   (default: d 2 3 4)
# 10e's run.sh steps 0 (drift check, lake build, toy self-test), then per seed:
#   skew.py -v on the route (project rule E, every gate) -> build/skew_v_SEED.log (once)
#   extract.py with 10e's H, I plus --rules2 AEFJ          -> build/obl2_SEED.tc/.json
#   tcheck                                                 -> build/t2_SEED.out
#   compare.py (H, I; tighten) and compare2.py (A, E, F, J) -> build/compare*_SEED.tsv
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); cd "$HERE"
export PATH=$HOME/.elan/bin:$PATH
./sync.sh --check || exit 1
# SKIP_BUILD=1 when the exe is current and the slot semaphore is busy (lake build is a no-op then)
if [ -z "${SKIP_BUILD:-}" ]; then
  FORMAL_SLOT_CWD=$HERE ../../slot.sh lake build 2>&1 | grep -E "error|Build completed" || exit 1
fi
EXE=$HERE/.lake/build/bin/tcheck
$EXE test/toy.tc 2>/dev/null | diff - test/toy.expected && echo "  toy self-test ok" || { echo "  toy self-test FAILED"; exit 1; }
SEEDS=${*:-d 2 3 4}
for s in $SEEDS; do
  O=build/tree_$s/cells/build/hw/gcd_hw
  [ -f "$O/gcd_hw.sdf" ] || { echo "seed $s: no route (run ./route.sh $s)"; continue; }
  [ -s build/skew_v_$s.log ] || (cd build/tree_$s/cells && python3 verify/skew.py "$PWD/build/hw/gcd_hw/gcd_hw.sdf" -v > "$HERE/build/skew_v_$s.log" 2>&1)
  python3 extract.py "$O" gcd_hw --cells "build/tree_$s/cells" --osc dhk --osc invhk --rules2 AEFJ \
      --out build/obl2_$s.tc --json build/obl2_$s.json 2> build/extract2_$s.log || { tail build/extract2_$s.log; continue; }
  tail -1 build/extract2_$s.log
  $EXE build/obl2_$s.tc > build/t2_$s.out 2> build/t2_$s.err; tail -1 build/t2_$s.err
  grep -E "^[HI] " build/t2_$s.out > build/t2hi_$s.out
  python3 compare.py build/t2hi_$s.out build/tighten_$s.log --tsv build/compare2hi_$s.tsv | grep "^#"
  python3 compare2.py $s
done
python3 summarize2.py $SEEDS > /dev/null && cp build/compare2_*.tsv results/ && echo "  results/agree2.tsv disagree2.tsv unchecked2.tsv updated"
