#!/usr/bin/env bash
# Probe K2: routed collatz_hw -> prjxray per-arc delays -> xaudit netlist + bands, per seed.
#
#   k2/bands_k2.sh [seed ...]     (default: d 4 5 6)
#   OUT=~/k2out  XRAY=~/k2tools/xray_delay.py  PYLIB=~/k2tools/pylib
#
# XRAY is origin/claude/research:cells/gls/fid/xray_delay.py, read with `git show` (this probe
# used 7dc5dde, md5 3e69bf6a..., which also charges the slice routing-BEL muxes; the gcd_hw
# A-events5 bands used 801db02, md5 99b10a6d...).  PYLIB holds simplejson + intervaltree.
# Corners, as for gcd_hw (events5/builds.txt):
#   slow  [SLOW_MIN, SLOW_MAX]   fast [FAST_MIN, FAST_MAX]   indep [FAST_MIN, SLOW_MAX]
#   gb    --corner slowmax --widen 0.332  ([0.668*SLOW_MAX, SLOW_MAX], skew.py GUARD_LO/GUARD_HI)
# The cut is routed2x.py's defaults: --keep-prefix urig. --cut-net rig_rst (collatz_rig is
# instantiated as urig with rig_rst, exactly as gcd_rig in gcd_hw).
set -euo pipefail
K2="$(cd "$(dirname "$0")" && pwd)"
OUT=${OUT:-$HOME/k2out}
XRAY=${XRAY:-$HOME/k2tools/xray_delay.py}
PYLIB=${PYLIB:-$HOME/k2tools/pylib}
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
for s in "${@:-d 4 5 6}"; do
  for t in $s; do
    D=$OUT/$t
    [ -e $D/arcs.tsv ] || PYTHONPATH="$TC/openxc7-src/prjxray:$PYLIB" python3 "$XRAY" \
        --routed $D/collatz_hw_routed.json --sdf $D/collatz_hw.sdf \
        --out $D/collatz_hw_xray.sdf --arcs $D/arcs.tsv > $D/xray.log 2>&1
    echo "$t xray: $(grep -m1 'xray_delay:' $D/xray.log || tail -1 $D/xray.log)"
    for c in slow fast indep; do
      python3 "$K2/../routed2x.py" $D/collatz_hw_routed.json --out $D/net.json --bands $D/$c.bands.json \
          --xray-arcs $D/arcs.tsv --corner $c --report $D/routed2x_$c.txt > /dev/null
    done
    python3 "$K2/../routed2x.py" $D/collatz_hw_routed.json --out $D/net.json --bands $D/gb.bands.json \
        --xray-arcs $D/arcs.tsv --corner slowmax --widen 0.332 --report $D/routed2x_gb.txt > /dev/null
    echo "$t net: $(md5sum < $D/net.json | cut -c1-32)  $(head -3 $D/routed2x_slow.txt | tr '\n' ' ')"
  done
done
