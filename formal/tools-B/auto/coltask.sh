#!/usr/bin/env bash
# tools-B/auto/coltask.sh SIZES.vh SEED OUT  (shard B, UNTRUSTED simulation): automatic collatz (BDC_AUTO=1; env KERNEL=xorshift /
# collatz64 for those, with their own vectors / K / long-path checks) built from a
# research checkout ($RS) with SIZES at placer SEED, bits read back (bit2fasm) and decoded, then: col18 32 draws (K 30601..)
# and 32 slow-carry draws (K 30651..), and cchecks.sh (c32hi, preloaded steps counter, two carry slacks). NEARMISS counts
# (storage-LUT output pulses < 200 ps) are summed per draw set. OUT/summary.txt.
set -uo pipefail
Z=$(readlink -f "$1"); S=$2; O=$3; H=$(cd "$(dirname "$0")" && pwd); F=$(cd "$H/../.." && pwd); RS=${RS:-/home/user/rs}
export TC=${TC:-$HOME/dev2/lib/fpgatoolchain}; mkdir -p "$O"; SM=$O/summary.txt; : > "$SM"; say() { echo "$*" | tee -a "$SM"; }
source "$TC/openxc7/export.sh" > /dev/null; K=${KERNEL:-collatz}; T=${K}_bench_gen; B=$RS/cells/build/hw/$T
( cd "$RS/cells" && BDC_AUTO=1 NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES="$Z" PNR_TIMEOUT=3600 ./hw/build_bench.sh $K ) \
  > "$O/build.log" 2>&1 || { say "seed $S BUILD FAILED"; exit 0; }
say "seed $S sizes $(basename "$Z") sdf $(md5sum < "$B/$T.sdf" | cut -c1-8) bits $(md5sum < "$B/$T.bit" | cut -c1-8) ffmux $(python3 "$RS/research/tools/ffmux_scan.py" "$B/$T.fasm" > /dev/null 2>&1; echo $?)"
W=$O/w; mkdir -p "$W"; PRJ=$TC/openxc7-src/prjxray; DB=${XRAY_DB:-$TC/openxc7/share/nextpnr/prjxray-db}/zynq7
[ -d "$DB" ] || DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7
PYTHONPATH="$PRJ:$PRJ/third_party/fasm:$TC/openxc7/lib/python" python3 -W ignore "$PRJ/utils/bit2fasm.py" --db-root "$DB" \
  --part xc7z010clg400-1 --bitread "$TC/openxc7/bin/bitread" "$B/$T.bit" > "$W/raw.fasm" 2> "$O/bit2fasm.log"
if [ -s "$W/raw.fasm" ]; then python3 "$H/fasm_bits.py" "$W/raw.fasm" "$W/$T.fasm" > /dev/null; else cp "$B/$T.fasm" "$W/$T.fasm"; say "(decoded nextpnr FASM: bit2fasm failed)"; fi
rm -f "$W/raw.fasm"; cp "$B/$T.json" "$B/${T}_routed.json" "$RS/cells/build/gen/$T.v" "$RS/cells/build/gen/${K}_kernel_bench.v" "$W/"
bash "$H/decode.sh" "$W" $K > "$O/decode.out" 2>&1; [ -f "$W/m/bnd.json" ] || { say "DECODE FAILED"; exit 0; }
G=$RS/research/data/eventgraph/gate
case $K in collatz) VH=col18; KB=30601;; collatz64) VH=c6419; KB=30501;; xorshift) VH=xor19; KB=30801;; esac
for x in "" 0.8,1.0; do k0=$KB; [ -n "$x" ] && k0=$((KB + 50))
  DRAW_XBAND=$x RS=$RS bash "$H/kdraws.sh" "$W" $K "$G/$VH.hex" $k0 32 ${JOBS:-4} > /dev/null 2>&1
  d=$W/d_${k0}${x:+_x}
  say "draws K $k0..+31${x:+ slow-carry}: $(grep '^draws [0-9]' "$d/log.txt" | cut -c1-40) | nearmiss sum $(grep -o 'nearmiss [0-9]*' "$d/draws.txt" | awk '{s+=$2} END{print s+0}') | last answer mean $(grep -o 'last out0 at [0-9]*' "$d/draws.txt" | awk '{s+=$4} END{if(NR) printf "%.0f", s/NR}') ps"
  cp "$d/draws.txt" "$O/draws_$k0.txt"; done
case $K in
  collatz) RS=$RS bash "$H/cchecks.sh" "$W" $KB 'uaddi1\..*slice\[4\]\.genblk1\.carry4$' 'uaddi0\..*slice\[7\]\.genblk1\.carry4$' > /dev/null 2>&1;;
  collatz64) K=collatz64 RS=$RS bash "$H/cchecks.sh" "$W" $KB 'uaddi1\..*slice\[4\]\.genblk1\.carry4$' 'uaddi0\..*slice\[14\]\.genblk1\.carry4$' > /dev/null 2>&1;;
  xorshift) CS=$(python3 -c "import json,re; c=json.load(open('$W/m/routed.json'))['modules']['top']['cells']; print([v['attributes']['NEXTPNR_BEL'].split('/')[0] for n,v in c.items() if re.search(r'udut\.uaddi0\..*slice\[4\]\.genblk1\.carry4$',n)][0])")
    RS=$RS bash "$H/xorchecks.sh" "$W" "$CS" 4 > /dev/null 2>&1; grep -v "gate classes" "$W/xorchecks.txt" | sed 's/^/xorchecks: /' >> "$SM"
    bash "$H/../preload/carryslack.sh" "$W/m" "$W/cs" xorshift 0x3ffffff0 ulink_n6 "0x92d68ca2,0x40000001 0x13579bdf,0x40000001" 'uaddi0\..*slice\[4\]\.genblk1\.carry4$' 2101 4 30000 2>/dev/null | tail -1 | sed 's/^/counter carry: /' >> "$SM";;
esac
[ -f "$W/cchecks.txt" ] && grep -v "gate classes" "$W/cchecks.txt" | sed 's/^/cchecks: /' >> "$SM"
for d in hi pre pa; do [ -f "$W/$d/draws.txt" ] && echo "$d nearmiss sum $(grep -o 'nearmiss [0-9]*' "$W/$d/draws.txt" 2>/dev/null | awk '{s+=$2} END{print s+0}')" >> "$SM"; done
cat "$SM"
