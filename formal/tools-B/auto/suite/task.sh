#!/usr/bin/env bash
# tools-B/auto/suite/task.sh K SEED SIZES.vh SDF8 OUT [NDRAWS] [K0]  (shard B, UNTRUSTED simulation): one route of research's
# automatic suite (BDC_AUTO=1, its sizing loop's sizes for that route) rebuilt from a research checkout ($RS, with
# build/frontend from cloud/fixtures), checked to be the same route (sdf md5 prefix SDF8), its bitstream read back by
# prjxray bit2fasm and decoded (tools-B/auto/decode.sh), then NDRAWS (default 32) draws of research's model from K0
# (default 10000 + 100 * SEED + 1, research's suite K) and NDRAWS slow-carry draws (CARRY4 / F7F8 / FF in [0.8, 1.0]) on
# the kernel's own vectors (suite_one.sh's choice) with research's oracle compiled from the C (xdraws.py). OUT/summary.txt.
set -uo pipefail
K=$1; S=$2; Z=$(readlink -f "$3"); M8=$4; O=$5; ND=${6:-32}; K0=${7:-$((10000 + 100 * S + 1))}
H=$(cd "$(dirname "$0")/.." && pwd); F=$(cd "$H/../.." && pwd); RS=${RS:-/home/user/rs}
export TC=${TC:-$HOME/dev2/lib/fpgatoolchain}; mkdir -p "$O"; SM=$O/summary.txt; : > "$SM"
say() { echo "$*" | tee -a "$SM"; }
source "$TC/openxc7/export.sh" > /dev/null
case $K in
  isprime) V=research/data/alltable/isp17.hex; OR="research/tools/fifteen/kernel_oracle.sh isprime";;
  *) V=kernels/$K/vec.hex; [ -f "$RS/$V" ] || V=research/data/suite/vec/$K.hex; OR="research/tools/suite/oracle.sh $K";;
esac
head -1 "$RS/$V" | grep -q '^// benchvec' && { say "$K $S SKIP (memory vectors: not supported by formal's bench boundary yet)"; exit 0; }
( cd "$RS" && $OR < "$V" ) > "$O/exp.txt" 2> "$O/oracle.err" || { say "$K $S NO-ORACLE"; exit 0; }
B=$RS/cells/build/hw/${K}_bench_gen
( cd "$RS/cells" && BDC_AUTO=1 NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES="$Z" PNR_TIMEOUT=${PNR_TIMEOUT:-3600} \
  ./hw/build_bench.sh "$K" ) > "$O/build.log" 2>&1 || { say "$K $S BUILD FAILED: $(grep -m1 -iE 'error|fail' "$O/build.log" | cut -c1-120)"; exit 0; }
md=$(md5sum "$B/${K}_bench_gen.sdf" | cut -c1-8)
say "$K $S sdf $md (research $M8) $([ "$md" = "$M8" ] && echo SAME || echo DIFFERENT) nextpnr $(sha256sum "$TC/openxc7/bin/nextpnr-xilinx" | cut -c1-16)"
[ "$md" = "$M8" ] || [ "$M8" = - ] || exit 0   # SDF8 '-': a new route (a what-if size set), no research route to match
W=$O/w; mkdir -p "$W"; T=${K}_bench_gen; PRJ=$TC/openxc7-src/prjxray; DB=${XRAY_DB:-$TC/openxc7/share/nextpnr/prjxray-db}/zynq7
[ -d "$DB" ] || DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7
PYTHONPATH="$PRJ:$PRJ/third_party/fasm:$TC/openxc7/lib/python" python3 -W ignore "$PRJ/utils/bit2fasm.py" --db-root "$DB" \
  --part xc7z010clg400-1 --bitread "$TC/openxc7/bin/bitread" "$B/$T.bit" > "$W/raw.fasm" 2> "$O/bit2fasm.log"
if [ -s "$W/raw.fasm" ]; then python3 "$H/fasm_bits.py" "$W/raw.fasm" "$W/$T.fasm" > /dev/null; SRC=bits
else cp "$B/$T.fasm" "$W/$T.fasm"; SRC="nextpnr FASM (bit2fasm failed: $(tail -1 "$O/bit2fasm.log" | cut -c1-80))"; fi; rm -f "$W/raw.fasm"
cp "$B/$T.json" "$B/${T}_routed.json" "$RS/cells/build/gen/$T.v" "$RS/cells/build/gen/${K}_kernel_bench.v" "$W/"
say "decoded from $SRC; bits md5 $(md5sum < "$B/$T.bit" | cut -c1-8), ffmux $(python3 "$RS/research/tools/ffmux_scan.py" "$B/$T.fasm" > /dev/null 2>&1; echo $?)"
bash "$H/decode.sh" "$W" "$K" > "$O/decode.out" 2>&1; [ -f "$W/m/bnd.json" ] || { say "DECODE FAILED"; tail -3 "$W/decode.txt" >> "$SM"; exit 0; }
grep -E "operands|dsp_gates" "$O/decode.out" | tee -a "$SM"
OPS=$(grep -o "operands [^ ]* [^ ]*" "$O/decode.out" | head -1)
if [ "$(echo "$OPS" | awk '{print ($2 == $3)}')" = 1 ]; then PAIRS=$(awk 'NF>=1{printf "0x%s,0x%s ", $1, $1}' "$RS/$V")
else PAIRS=$(awk 'NF>=2{printf "0x%s,0x%s ", $1, $2}' "$RS/$V"); fi
J=${JOBS:-4}
for x in "" 0.8,1.0; do
  k0=$K0; [ -n "$x" ] && k0=$((K0 + 50))
  DRAW_XBAND=$x python3 "$H/xdraws.py" "$O/exp.txt" "$W/m/net.json" "$W/m/bnd.json" "$O/d$k0" --kernel "$K" --pairs $PAIRS --draws "$ND" \
    --seed0 "$k0" --jobs "$J" --routed "$W/m/routed.json" --tmax "${TMAX:-400000000}" > "$O/d$k0.log" 2>&1
  say "draws K $k0..$((k0 + ND - 1))${x:+ slow-carry $x}: $(grep '^draws [0-9]' "$O/d$k0.log" | head -1) $(grep -E 'seed [0-9]+ (FAIL|UND)' "$O/d$k0.log" | tr '\n' ' ')"
  cp "$O/d$k0/draws_summary.txt" "$O/draws_summary_$k0.txt" 2>/dev/null; rm -rf "$O/d$k0/net.simx" "$O/d$k0/simx"
done
