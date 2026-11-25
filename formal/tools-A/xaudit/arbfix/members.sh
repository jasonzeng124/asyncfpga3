#!/usr/bin/env bash
# Probe E8ArbFix: recorded per-pin runs (sim.py) x virtual-core membership (member.py), UNTRUSTED.
#   seeds d 3 4 5 x corners slow fast x delay modes lo hi rand:1 rand:2 x selects 0 1, plus the two
#   mutation controls of member.py on every run (each must give NOT MEMBER somewhere overall).
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
S=${S:-/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad}
W=${W:-$S/e8mux/w}; O=${O:-$S/E8ArbFix/runs}; mkdir -p $O "$HERE/results"
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1
R="$HERE/results/members.txt"; : > $R
for s in ${SEEDS:-d 3 4 5}; do for c in ${CORNERS:-slow fast}; do for m in ${MODES:-lo hi rand:1 rand:2}; do for v in 0 1; do
  i=$W/$s/new; j=$O/run_${s}_${c}_${m/:/}_$v.json
  python3 -I "$HERE/sim.py" $i/skel.json $i/skel_$c.bands.json $v 20000 3000000 --delay=$m --json=$j > $O/sim_${s}_${c}_${m/:/}_$v.txt
  for mut in "" --mut=samectl --mut=noshift; do
    echo "== $s $c $m sel=$v ${mut:-base}" >> $R
    python3 "$HERE/member.py" $i/skel.json $i/skel_$c.bands.json $j $mut 2>&1 | grep -v '^model:' >> $R
  done
done; done; done; done
grep -A0 "^== \|summary" $R | paste - - | awk '{print}' > "$HERE/results/members_summary.txt"
