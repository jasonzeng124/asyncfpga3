#!/usr/bin/env bash
# E8Mux step 1-2: routed gcd_hw R5 (seeds d 3 4 5, $R/<seed>/{gcd_hw_routed.json,gcd_hw.sdf}) ->
# prjxray arcs with three calculators -> routed2x nets + band files -> events4/skel.py skeletons.
#   old : research 801db02 xray_delay.py (md5 99b10a6d; what every committed band file used)
#   new : e8mux/xray_delay_e8mux.py (= old + OUTMUX hop on O5 / F7 / F8 / CARRY4 xMUX exits)
#   r7  : research 7dc5dde xray_delay.py (md5 3e69bf6a; cross-check of new)
#   hull: new with --rb-o5 hull (sensitivity; seed d only)
# Bands: slow/fast/indep = routed2x --corner; gb = --corner slowmax --widen 0.332; all with
# --inverted hull (lo > hi prjxray rows -> [min, max], listed in the routed2x report).
set -eu
HERE="$(cd "$(dirname "$0")" && pwd)"; X="$HERE/.."
S=${S:-/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad/e8mux}
R=${R:-$S/route}; W=${W:-$S/w}
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
export XRAY_DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7 PYTHONPATH=$TC/openxc7-src/prjxray
export PYTHONHASHSEED=0 PYTHONDONTWRITEBYTECODE=1
mkdir -p $W/tools
git -C "$HERE" show 801db02:cells/gls/fid/xray_delay.py > $W/tools/xray_delay_old.py
git -C "$HERE" show 7dc5dde:cells/gls/fid/xray_delay.py > $W/tools/xray_delay_r7.py
md5sum $W/tools/xray_delay_old.py $W/tools/xray_delay_r7.py "$HERE/xray_delay_e8mux.py"
for s in ${SEEDS:-d 3 4 5}; do
  o=$W/$s; mkdir -p $o
  md5sum $R/$s/gcd_hw.sdf $R/$s/gcd_hw_routed.json
  for v in ${VARIANTS:-old new r7}; do
    case $v in old) T=$W/tools/xray_delay_old.py; F="";; r7) T=$W/tools/xray_delay_r7.py; F="";;
               new) T="$HERE/xray_delay_e8mux.py"; F="";; hull) T="$HERE/xray_delay_e8mux.py"; F="--rb-o5 hull";; esac
    [ -s $o/arcs_$v.tsv ] || python3 $T --routed $R/$s/gcd_hw_routed.json --sdf $R/$s/gcd_hw.sdf \
        --out $o/xray_$v.sdf --arcs $o/arcs_$v.tsv $F 2> $o/xray_$v.log
    echo "$s $v: $(head -1 $o/xray_$v.log) | $(grep -c . $o/arcs_$v.tsv) rows md5 $(md5sum < $o/arcs_$v.tsv | cut -c1-8)"
    for c in slow fast indep gb; do
      if [ $c = gb ]; then CF="--corner slowmax --widen 0.332"; else CF="--corner $c"; fi
      mkdir -p $o/$v
      python3 -I "$X/routed2x.py" $R/$s/gcd_hw_routed.json --xray-arcs $o/arcs_$v.tsv $CF --inverted hull \
        --out $o/$v/net.json --bands $o/$v/$c.bands.json --report $o/$v/routed2x_$c.txt > /dev/null
      python3 "$X/events4/skel.py" $o/$v/net.json $o/$v/$c.bands.json $o/$v/skel.json $o/$v/skel_$c.bands.json > /dev/null
      python3 -I "$HERE/checkbands.py" $o/$v/$c.bands.json $o/$v/skel_$c.bands.json > /dev/null
    done
    echo "$s $v net $(md5sum < $o/$v/net.json | cut -c1-8) skel $(md5sum < $o/$v/skel.json | cut -c1-8)"
  done
done
