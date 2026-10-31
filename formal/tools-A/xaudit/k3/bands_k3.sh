#!/usr/bin/env bash
# Probe K3: routed <k>_hw -> prjxray per-arc delays -> xaudit netlist + bands, per seed.
#
#   k3/bands_k3.sh <kernel> [seed ...]   (k2/bands_k2.sh generalised; default seeds 1 2 3 5)
#   OUT=~/k3out/<k>  XRAY=~/k3tools/xray_delay.py  PYLIB=~/k3tools/pylib
#
# XRAY is origin/claude/research:cells/gls/fid/xray_delay.py, read with `git show` (this probe
# used 7dc5dde, md5 3e69bf6a..., which also charges the slice routing-BEL muxes; the gcd_hw
# A-events5 bands used 801db02, md5 99b10a6d...).  PYLIB holds simplejson + intervaltree.
# Corners, as for gcd_hw (events5/builds.txt):
#   slow  [SLOW_MIN, SLOW_MAX]   fast [FAST_MIN, FAST_MAX]   indep [FAST_MIN, SLOW_MAX]
#   gb    --corner slowmax --widen 0.332  ([0.668*SLOW_MAX, SLOW_MAX], skew.py GUARD_LO/GUARD_HI)
# The cut is routed2x.py's defaults: --keep-prefix urig. --cut-net rig_rst (<k>_rig is
# instantiated as urig with rig_rst, exactly as gcd_rig in gcd_hw).  The netlist is built by
# k3/routed2x_k3.py (= ../routed2x.py plus --cut-type; byte-identical output without it).  For
# ipow, CUT_TYPE=DSP48E1_DSP48E1 (default): the 6 DSP48E1s of the two muli become hard cells
# whose outputs are FREE inputs (routed2x.py rejects them as "not combinational").
set -euo pipefail
K2="$(cd "$(dirname "$0")" && pwd)"
K=$1; shift; T=${K}_hw
OUT=${OUT:-$HOME/k3out/$K}
XRAY=${XRAY:-$HOME/k3tools/xray_delay.py}
PYLIB=${PYLIB:-$HOME/k3tools/pylib}
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
case $K in ipow) CUT_TYPE=${CUT_TYPE-DSP48E1_DSP48E1} ;; *) CUT_TYPE=${CUT_TYPE-} ;; esac
CT=""; for t in $CUT_TYPE; do CT="$CT --cut-type $t"; done
# prjxray rows with lo > hi (FAST_MIN > FAST_MAX on a few pins, E8Mux): routed2x.py rejects them by
# default; INVERTED=hull (default here, as E8Mux's bands.sh) takes [min, max] and lists them in the report.
CT="$CT --inverted ${INVERTED:-hull}"
python3 "$K2/mk_routed2x_k3.py" > /dev/null   # routed2x_k3.py = the current ../routed2x.py + --cut-type
export XRAY_DB=${XRAY_DB:-$TC/openxc7/share/nextpnr/prjxray-db/zynq7}   # xray_delay.py defaults to /root/dev2/lib/xray/...
for s in "${@:-1 2 3 5}"; do
  for t in $s; do
    D=$OUT/$t
    [ -e $D/arcs.tsv ] || PYTHONPATH="$TC/openxc7-src/prjxray:$PYLIB" python3 "$XRAY" \
        --routed $D/${T}_routed.json --sdf $D/${T}.sdf \
        --out $D/${T}_xray.sdf --arcs $D/arcs.tsv > $D/xray.log 2>&1
    echo "$t xray: $(grep -m1 'xray_delay:' $D/xray.log || tail -1 $D/xray.log)"
    for c in slow fast indep; do
      python3 "$K2/routed2x_k3.py" $D/${T}_routed.json $CT --out $D/net.json --bands $D/$c.bands.json \
          --xray-arcs $D/arcs.tsv --corner $c --report $D/routed2x_$c.txt > /dev/null
    done
    python3 "$K2/routed2x_k3.py" $D/${T}_routed.json $CT --out $D/net.json --bands $D/gb.bands.json \
        --xray-arcs $D/arcs.tsv --corner slowmax --widen 0.332 --report $D/routed2x_gb.txt > /dev/null
    echo "$t net: $(md5sum < $D/net.json | cut -c1-32)  $(head -3 $D/routed2x_slow.txt | tr '\n' ' ')"
  done
done
