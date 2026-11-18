#!/usr/bin/env bash
# tools-B/auto/coltask.sh SIZES.vh SEED OUT  (shard B, UNTRUSTED simulation): automatic collatz (BDC_AUTO=1) built from a
# research checkout ($RS) with SIZES at placer SEED, bits read back (bit2fasm) and decoded, then: col18 32 draws (K 30601..)
# and 32 slow-carry draws (K 30651..), and cchecks.sh (c32hi, preloaded steps counter, two carry slacks). NEARMISS counts
# (storage-LUT output pulses < 200 ps) are summed per draw set. OUT/summary.txt.
set -uo pipefail
Z=$(readlink -f "$1"); S=$2; O=$3; H=$(cd "$(dirname "$0")" && pwd); F=$(cd "$H/../.." && pwd); RS=${RS:-/home/user/rs}
export TC=${TC:-$HOME/dev2/lib/fpgatoolchain}; mkdir -p "$O"; SM=$O/summary.txt; : > "$SM"; say() { echo "$*" | tee -a "$SM"; }
source "$TC/openxc7/export.sh" > /dev/null; K=collatz; T=${K}_bench_gen; B=$RS/cells/build/hw/$T
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
for x in "" 0.8,1.0; do k0=30601; [ -n "$x" ] && k0=30651
  DRAW_XBAND=$x RS=$RS bash "$H/kdraws.sh" "$W" $K "$G/col18.hex" $k0 32 ${JOBS:-4} > /dev/null 2>&1
  d=$W/d_${k0}${x:+_x}
  say "draws K $k0..+31${x:+ slow-carry}: $(grep '^draws [0-9]' "$d/log.txt" | cut -c1-40) | nearmiss sum $(grep -o 'nearmiss [0-9]*' "$d/draws.txt" | awk '{s+=$2} END{print s+0}') | last answer mean $(grep -o 'last out0 at [0-9]*' "$d/draws.txt" | awk '{s+=$4} END{if(NR) printf "%.0f", s/NR}') ps"
  cp "$d/draws.txt" "$O/draws_$k0.txt"; done
UA1=$(python3 -c "import json,re; c=json.load(open('$W/m/routed.json'))['modules']['top']['cells']; print(any(re.search(r'uaddi1\..*slice\[4\]\.genblk1\.carry4$',n) for n in c))")
RS=$RS bash "$H/cchecks.sh" "$W" 30601 'uaddi1\..*slice\[4\]\.genblk1\.carry4$' 'uaddi0\..*slice\[7\]\.genblk1\.carry4$' > /dev/null 2>&1
grep -v "gate classes" "$W/cchecks.txt" | sed 's/^/cchecks: /' >> "$SM"
for d in hi pre; do echo "$d nearmiss sum $(grep -o 'nearmiss [0-9]*' "$W/$d/draws.txt" 2>/dev/null | awk '{s+=$2} END{print s+0}')" >> "$SM"; done
cat "$SM"
