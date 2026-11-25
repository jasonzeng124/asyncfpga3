#!/usr/bin/env bash
# Probe C-10m: re-run EVERY tcheck row on the 4 gcd_hw routes with the corrected front end
# (OUTMUX split fix in Prjx.split, tie-off starts dropped from rule A), one seed at a time
# (each extract holds ~1 GB; the machine is shared), then the summaries and the cross-checks.
#   formal/tools/tcheck/run10m.sh [SEED...]          (default: d 2 3 4; routes from route.sh)
# Outputs: build/{t5,t10k,t10l}_SEED.out, results/{agree3,disagree3,unchecked3,cert3,fallback3}.tsv,
#   results/r10k_rows.tsv, r10l_rows.tsv, summary10k/10l.txt, results/compare5_SEED.tsv,
#   results/beforeafter10m.tsv (vs results/before10m/ = the committed C-10h/10k/10l tables),
#   results/cmpxrc_j.txt, results/cmpxrc_r.txt (vs the auditor's xrc rows in build/xrc/)
set -uo pipefail
HERE=$(cd "$(dirname "$0")" && pwd); cd "$HERE"
SEEDS=${*:-d 2 3 4}
for s in $SEEDS; do
  diff <(awk '{print $1}' build/sha_$s.txt) <(awk '{print $1}' results/sha_$s.txt) > /dev/null \
    && echo "seed $s: route byte-identical to the C-10e/10h route" || echo "seed $s: ROUTE DIFFERS from results/sha_$s.txt"
  SKIP_BUILD=1 ./run4.sh $s | grep -E "^seed|self-test"
  [ -s build/t5_$s.out ] || { echo "seed $s: run4 produced nothing"; exit 1; }
  SKIP_BUILD=1 ./run10k.sh $s | grep -E "^seed"
  SKIP_BUILD=1 ./run10l.sh $s | grep -E "^seed"
  cp build/compare5_$s.tsv results/
done
python3 summarize3.py $SEEDS > /dev/null
python3 summarize10k.py $SEEDS > /dev/null
python3 summarize10l.py $SEEDS > /dev/null
python3 beforeafter10m.py results/before10m results $SEEDS > results/beforeafter10m.tsv
# the auditor's model and row tables (read-only, from the audit branch)
mkdir -p build/xrc
for f in xrc.py rulej_x.tsv rulej_x_nomux.tsv rtfb_d.tsv rtfb_2.tsv rtfb_3.tsv rtfb_4.tsv; do
  [ -s build/xrc/$f ] || git -C "$HERE" show origin/claude/audit:audit/tc/$f > build/xrc/$f 2>/dev/null || rm -f build/xrc/$f
done
if [ -s build/xrc/rulej_x.tsv ]; then
  python3 cmpxrc.py build/xrc results/compare5_ $SEEDS > results/cmpxrc_j.txt
  python3 cmpxrc_r.py build/xrc build/t5_ $SEEDS > results/cmpxrc_r.txt
fi
echo "done: results/agree3.tsv disagree3.tsv unchecked3.tsv beforeafter10m.tsv cmpxrc_j.txt cmpxrc_r.txt"
