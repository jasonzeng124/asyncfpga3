#!/usr/bin/env bash
# Probe C-10e end to end:  formal/tools/tcheck/run.sh [SEED...]   (default: d 2 3 4)
#  0. drift check of the copied proved modules, lake build (core Lean), toy self-test
#  1. per seed: the route from route.sh (run it first: ./route.sh SEED, ~5-15 min each),
#     extract.py -> build/obl_SEED.tc, tcheck -> build/tcheck_SEED.out,
#     compare.py against that route's tighten.py log -> build/compare_SEED.tsv
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); cd "$HERE"
export PATH=$HOME/.elan/bin:$PATH
./sync.sh --check || exit 1
../../slot.sh lake build 2>&1 | grep -E "error|Build completed" || exit 1
EXE=$HERE/.lake/build/bin/tcheck
$EXE test/toy.tc 2>/dev/null | diff - test/toy.expected && echo "  toy self-test ok" || { echo "  toy self-test FAILED"; exit 1; }
SEEDS=${*:-d 2 3 4}
for s in $SEEDS; do
  O=build/tree_$s/cells/build/hw/gcd_hw
  [ -f "$O/gcd_hw.sdf" ] || { echo "seed $s: no route (run ./route.sh $s)"; continue; }
  python3 extract.py "$O" gcd_hw --cells "build/tree_$s/cells" --osc dhk --osc invhk \
      --out build/obl_$s.tc --json build/obl_$s.json 2> build/extract_$s.log || { cat build/extract_$s.log; continue; }
  tail -1 build/extract_$s.log
  /usr/bin/time -f "  tcheck %es %MkB" $EXE build/obl_$s.tc > build/tcheck_$s.out 2> build/tcheck_$s.err
  tail -2 build/tcheck_$s.err
  python3 compare.py build/tcheck_$s.out build/tighten_$s.log --tsv build/compare_$s.tsv | grep "^#"
done
