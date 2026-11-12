#!/usr/bin/env bash
# Probe C-10l:  formal/tools/tcheck/run10l.sh [SEED...]   (default: d 2 3 4)
#  0. sync --check, lake build (FORMAL_SLOT_CWD set), toy + cert + pair + credit self-tests
#  1. per seed, in parallel: extract with rules10l only (credited Xc/Xic/Xm, K = X4 ctl fork,
#     D = Fd diagnostics; --no-hi) -> build/obl10l_SEED.tc (+ .json), tcheck -> build/t10l_SEED.out
#  2. summarize10l.py -> results/r10l_rows.tsv, results/summary10l.txt
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); cd "$HERE"
export PATH=$HOME/.elan/bin:$PATH
./sync.sh --check || exit 1
if [ -z "${SKIP_BUILD:-}" ]; then
  FORMAL_SLOT_CWD=$HERE ../../slot.sh lake build 2>&1 | grep -E "error|Build completed" || exit 1
fi
EXE=$HERE/.lake/build/bin/tcheck
for t in toy toycert toypair toycredit; do
  $EXE test/$t.tc 2>/dev/null | diff - test/$t.expected > /dev/null && echo "  $t self-test ok" \
    || { echo "  $t self-test FAILED"; exit 1; }
done
SEEDS=${*:-d 2 3 4}
one() {
  s=$1; O=build/tree_$s/cells/build/hw/gcd_hw
  [ -f "$O/gcd_hw.sdf" ] || { echo "seed $s: no route"; return; }
  python3 extract.py "$O" gcd_hw --cells "build/tree_$s/cells" --osc dhk --osc invhk --no-hi \
      --rules10l ${RULES10L:-CKD} --out build/obl10l_$s.tc --json build/obl10l_$s.json 2> build/extract10l_$s.log \
      || { tail build/extract10l_$s.log; return; }
  $EXE build/obl10l_$s.tc > build/t10l_$s.out 2> build/t10l_$s.err
  echo "seed $s: $(tail -1 build/extract10l_$s.log) / $(tail -1 build/t10l_$s.err)"
}
for s in $SEEDS; do one $s & done
wait
python3 summarize10l.py $SEEDS
