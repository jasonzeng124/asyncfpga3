#!/usr/bin/env bash
# Reproduce A-events5's per-seed tables: skeleton + ana5 (strict, contig5) at slow / fast /
# indep (mixed) / gb (guardband: [0.668*SLOW_MAX, SLOW_MAX], skew.py GUARD_LO/GUARD_HI),
# on gcd_hw R5 seeds d 3 4 5.  Inputs: $O/<seed>/{net.json,<corner>.bands.json}, made by
# routed2x.py from the rebuilt routes (see A-events5 §2).  PYTHONHASHSEED pinned: the
# events4 walk search iterates sets, and its result depends on the order.
set -u
HERE="$(cd "$(dirname "$0")" && pwd)"
O=${O:-/tmp/events5/out}
export PYTHONHASHSEED=0
IN="$HERE/inputs"; G="$HERE/../gcd/inputs"
for s in ${SEEDS:-d 3 4 5}; do   # restore the inputs from the repo if the rebuild scratch is gone
  mkdir -p $O/$s
  [ -e $O/$s/net.json ] || { [ $s = d ] && xz -dc $G/net_d.json.xz > $O/$s/net.json || xz -dc $IN/net_$s.json.xz > $O/$s/net.json; }
  for c in slow fast indep gb; do
    [ -e $O/$s/$c.bands.json ] && continue
    if [ $s = d ] && [ $c != gb ]; then xz -dc $G/bands_d_$c.json.xz > $O/$s/$c.bands.json
    else xz -dc $IN/bands_${s}_$c.json.xz > $O/$s/$c.bands.json; fi
  done
done
for s in ${SEEDS:-d 3 4 5}; do
  for c in slow fast indep gb; do
    python3 "$HERE/../events4/skel.py" $O/$s/net.json $O/$s/$c.bands.json $O/$s/skel.json $O/$s/skel_$c.bands.json > /dev/null
    python3 "$HERE/ana5.py" $O/$s/skel.json $O/$s/skel_$c.bands.json --label ${s}_$c --json $O/$s/ana5_$c.json > "$HERE/ana5_${s}_$c.txt" 2>&1
    tail -1 "$HERE/ana5_${s}_$c.txt"
  done
done
