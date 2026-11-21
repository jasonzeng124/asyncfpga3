#!/usr/bin/env bash
# KapRes2: restore the committed inputs (net + slow + fast band files of gcd_hw seeds d 3 4 5),
# correct the fast bands on the BRKH_INT arcs (check_bands.py fix), then sweep xevents8 over
# corner cells for every seed (kapres2.py).  TAG selects another input set (in$TAG/, runs$TAG/),
# e.g. the E8Mux band files: put them at $KR/in$TAG/<seed>/{net,fast,slow,indep}.bands.json first.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"; X="$HERE/../../xaudit"
KR=${KR:-/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad/KapRes2}
TAG=${TAG:-}
I=$KR/in$TAG; FX=$KR/fix$TAG
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1 KR
# pin the untrusted python tooling: a snapshot of the committed events4/6/7/8 at 591cd51 (other
# probes edit xaudit/ live); kapres2.py forces XA_ARB=old (the Events8 virtual arbiter core)
export XA=$KR/xa
for d in events4 events6 events7 events8; do mkdir -p $XA/$d
  for f in $(git -C "$HERE" ls-tree --name-only 591cd51 ../../xaudit/$d/ | grep '\.py$'); do
    git -C "$HERE" show 591cd51:formal/tools-A/xaudit/$d/$(basename $f) > $XA/$d/$(basename $f); done; done
for s in ${SEEDS:-d 3 4 5}; do
  mkdir -p $I/$s
  if [ $s = d ]; then src=$X/gcd/inputs; nf=$src/net_d.json.xz; else src=$X/events5/inputs; nf=$src/net_$s.json.xz; fi
  [ -e $I/$s/net.json ] || xz -dc $nf > $I/$s/net.json
  for c in slow fast indep; do [ -e $I/$s/$c.bands.json ] || xz -dc $src/bands_${s}_$c.json.xz > $I/$s/$c.bands.json; done
  python3 "$HERE/check_bands.py" check $I/$s/slow.bands.json > $KR/check_in${TAG}_$s.txt 2>&1
  python3 "$HERE/check_bands.py" check $I/$s/fast.bands.json >> $KR/check_in${TAG}_$s.txt 2>&1
  python3 "$HERE/check_bands.py" brkh $I/$s/fast.bands.json $I/$s/slow.bands.json > $KR/brkh${TAG}_$s.txt 2>&1
  python3 "$HERE/check_bands.py" fix $I/$s/fast.bands.json $I/$s/slow.bands.json $I/$s/indep.bands.json $FX/$s
done
for s in ${SEEDS:-d 3 4 5}; do
  python3 "$HERE/kapres2.py" $s --init ${INIT:-8} --depth ${DEPTH:-2} --jobs ${JOBS:-1} ${TAG:+--tag $TAG} > $KR/run${TAG}_$s.log 2>&1 &
done
wait
cat $KR/run${TAG}_*.log
