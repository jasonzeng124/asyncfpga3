#!/usr/bin/env bash
# Probe C-10h:  formal/tools/tcheck/run4.sh [SEED...]   (default: d 2 3 4)
#  0. sync --check (5 proved modules incl. Unroll), lake build (FORMAL_SLOT_CWD set),
#     toy self-test (10e) and cert self-test (10h)
#  1. per seed, in parallel: ONE extract with every rule (H, I, A, E, F, J, W, R) plus the
#     cert late sides (Hc, Fc, Rc) and the C-10h prjxray additions -> build/obl5_SEED.tc,
#     tcheck -> build/t5_SEED.out, then the comparisons (compare.py, compare2.py,
#     cmpcert.py); finally summarize3.py -> results/*3.tsv
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); cd "$HERE"
export PATH=$HOME/.elan/bin:$PATH
./sync.sh --check || exit 1
if [ -z "${SKIP_BUILD:-}" ]; then
  FORMAL_SLOT_CWD=$HERE ../../slot.sh lake build 2>&1 | grep -E "error|Build completed" || exit 1
fi
EXE=$HERE/.lake/build/bin/tcheck
$EXE test/toy.tc 2>/dev/null | diff - test/toy.expected && echo "  toy self-test ok" || { echo "  toy self-test FAILED"; exit 1; }
$EXE test/toycert.tc 2>/dev/null | diff - test/toycert.expected && echo "  cert self-test ok" || { echo "  cert self-test FAILED"; exit 1; }
SEEDS=${*:-d 2 3 4}
one() {
  s=$1; O=build/tree_$s/cells/build/hw/gcd_hw
  [ -f "$O/gcd_hw.sdf" ] || { echo "seed $s: no route (run ./route.sh $s)"; return; }
  # C-10m: compare2.py needs rule E's verbose log (run2.sh made it; a fresh clone has none)
  [ -s build/skew_v_$s.log ] || (cd build/tree_$s/cells && python3 verify/skew.py "$PWD/build/hw/gcd_hw/gcd_hw.sdf" -v > "$HERE/build/skew_v_$s.log" 2>&1)
  python3 extract.py "$O" gcd_hw --cells "build/tree_$s/cells" --osc dhk --osc invhk --rules2 AEFJWR --cert \
      --out build/obl5_$s.tc --json build/obl5_$s.json 2> build/extract5_$s.log || { tail build/extract5_$s.log; return; }
  $EXE build/obl5_$s.tc > build/t5_$s.out 2> build/t5_$s.err
  grep -E "^[HI] " build/t5_$s.out > build/t5hi_$s.out
  grep -E "^Hc " build/t5_$s.out | sed 's/^Hc /H /' > build/t5hc_$s.out
  python3 compare.py build/t5hi_$s.out build/tighten_$s.log --tsv build/compare5hi_$s.tsv > build/compare5hi_$s.log
  python3 compare.py build/t5hc_$s.out build/tighten_$s.log --tsv build/compare5hc_$s.tsv > build/compare5hc_$s.log
  python3 compare2.py $s 5 > build/compare5_$s.log
  python3 cmpcert.py build/t5_$s.out --tsv build/cmpcert5_$s.tsv > build/cmpcert5_$s.log
  echo "seed $s: $(tail -1 build/extract5_$s.log) / $(tail -1 build/t5_$s.err)"
}
for s in $SEEDS; do one $s & done
wait
python3 summarize3.py $SEEDS
