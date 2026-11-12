#!/usr/bin/env bash
# KapRes2: restore the committed inputs, correct the fast bands (check_bands.py fix), then sweep
# xevents7 over corner cells for every seed (kapres2.py).  xe7.sh allows 2 lean --run at once.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"; X="$HERE/.."
I=/tmp/kapres2/in; FX=/tmp/kapres2/fix
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1
for s in d 3 4 5; do
  mkdir -p $I/$s
  if [ $s = d ]; then src=$X/gcd/inputs; nf=$src/net_d.json.xz; else src=$X/events5/inputs; nf=$src/net_$s.json.xz; fi
  [ -e $I/$s/net.json ] || xz -dc $nf > $I/$s/net.json
  for c in slow fast indep; do [ -e $I/$s/$c.bands.json ] || xz -dc $src/bands_${s}_$c.json.xz > $I/$s/$c.bands.json; done
  python3 "$HERE/check_bands.py" fix $I/$s/fast.bands.json $I/$s/slow.bands.json $I/$s/indep.bands.json $FX/$s
done
mkdir -p /tmp/kapres2/work
for s in ${SEEDS:-d 3 4 5}; do
  python3 "$HERE/kapres2.py" $s --init ${INIT:-8} --depth ${DEPTH:-2} --jobs ${JOBS:-2} > /tmp/kapres2/run_$s.log 2>&1 &
done
wait
cat /tmp/kapres2/run_*.log
