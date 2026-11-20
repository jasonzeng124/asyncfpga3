#!/usr/bin/env bash
# margin/trim/trimtask.sh DIR OUT [NDRAWS] (shard C, UNTRUSTED simulation): research's TRIMMED routes (FOR-FORMAL
# 2026-11-20 07:20: matched delay lines shortened after routing by LUT INIT only; research/data/for-formal/trim_<K>_s<S>/).
# DIR = that directory in research's checkout ($RS). Steps:
#  1. the kernel's exit-condition fixture MLIR copied over $RS/build/frontend/<K>/comp (as research's exit1 does);
#  2. tools-B/auto/suite/task.sh rebuilds the route from DIR/sizes_built.vh, seed DIR/seed.txt, checks the sdf md5
#     against DIR/md5.txt, decodes the UNTRIMMED bits and runs NDRAWS + NDRAWS slow-carry draws (OUT/untrimmed);
#  3. research's trim_lines.py applies DIR/trim_record.txt to the routed JSON and the FASM; the trimmed FASM's md5 is
#     checked against DIR/md5.txt (and must differ from the untrimmed one); fasm2frames + xc7frames2bit make the bits;
#  4. the trimmed bits are read back (bit2fasm), decoded and drawn exactly as step 2 (OUT/trimmed; tools-B's steps).
set -uo pipefail
D=$1; O=$(mkdir -p "$2" && cd "$2" && pwd); ND=${3:-32}
RS=${RS:-/home/user/rs}; export RS TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
F=$(cd "$(dirname "$0")/../../.." && pwd); HB=$F/tools-B/auto
n=$(basename "$D"); K=${n#trim_}; S=${K##*_s}; K=${K%_s*}; [ "$(cat "$RS/$D/seed.txt")" = "$S" ] || { echo "seed mismatch"; exit 1; }
SM=$O/summary.txt; : > "$SM"; say() { echo "$*" | tee -a "$SM"; }
FX=${FIXTURES:-frontend_exitcond}
cp "$RS/cloud/fixtures/$FX/$K/comp/"*.mlir "$RS/build/frontend/$K/comp/" || { say "$K $S NO FIXTURE $FX"; exit 0; }
SDF8=$(awk '/\.sdf$/{print substr($1,1,8)}' "$RS/$D/md5.txt"); MT=$(awk '/_bench_gen\.fasm$/{print $1}' "$RS/$D/md5.txt")
MU=$(awk '/untrimmed\.fasm$/{print $1}' "$RS/$D/md5.txt")
say "$K $S fixtures $FX sizes $D/sizes_built.vh sdf $SDF8 trim $(tr '\n' ' ' < "$RS/$D/trim_record.txt")"
bash "$HB/suite/task.sh" "$K" "$S" "$RS/$D/sizes_built.vh" "$SDF8" "$O/untrimmed" "$ND" > "$O/untrimmed.log" 2>&1
sed 's/^/untrimmed: /' "$O/untrimmed/summary.txt" | tee -a "$SM"
grep -q SAME "$O/untrimmed/summary.txt" || { say "route not SAME: stop"; exit 0; }
T=${K}_bench_gen; B=$RS/cells/build/hw/$T; TB=$O/tb; rm -rf "$TB"; mkdir -p "$TB"
say "untrimmed FASM md5 $(md5sum < "$B/$T.fasm" | cut -c1-32) (research $MU)"
source "$TC/openxc7/export.sh" > /dev/null
PRJ=$TC/openxc7-src/prjxray; DB=${XRAY_DB:-$TC/openxc7/share/nextpnr/prjxray-db}/zynq7; [ -d "$DB" ] || DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7
( cd "$RS" && python3 research/tools/auto/trim_lines.py "$B/${T}_routed.json" "$B/$T.fasm" "$TB/${T}_routed.json" "$TB/$T.fasm" \
    $(cat "$RS/$D/trim_record.txt") ) > "$O/trim.log" 2>&1 || { say "TRIM REFUSED: $(tail -2 "$O/trim.log" | tr '\n' ' ')"; exit 0; }
mt=$(md5sum < "$TB/$T.fasm" | cut -c1-32)
say "trimmed FASM md5 $mt (research $MT) $([ "$mt" = "$MT" ] && echo SAME || echo DIFFERENT); $(grep -c . "$O/trim.log") trim lines"
[ "$mt" = "$MT" ] || exit 0
PYTHONPATH="$PRJ:$TC/openxc7/lib/python" python3 "$PRJ/utils/fasm2frames.py" --db-root "$DB" --part xc7z010clg400-1 \
  "$TB/$T.fasm" > "$TB/$T.frames" 2> "$O/frames.log" || { say "FASM2FRAMES FAILED"; exit 0; }
"$TC/openxc7/bin/xc7frames2bit" --part_file "$DB/xc7z010clg400-1/part.yaml" --part_name xc7z010clg400-1 \
  --frm_file "$TB/$T.frames" --output_file "$TB/$T.bit" > "$O/bit.log" 2>&1 || { say "FRAMES2BIT FAILED"; exit 0; }
cp "$B/$T.json" "$TB/"
# step 4: tools-B task.sh's post-build steps, with the trimmed bits / routed JSON (B -> TB)
O2=$O/trimmed; mkdir -p "$O2"; W=$O2/w; mkdir -p "$W"; : > "$O2/summary.txt"
PYTHONPATH="$PRJ:$PRJ/third_party/fasm:$TC/openxc7/lib/python" python3 -W ignore "$PRJ/utils/bit2fasm.py" --db-root "$DB" \
  --part xc7z010clg400-1 --bitread "$TC/openxc7/bin/bitread" "$TB/$T.bit" > "$W/raw.fasm" 2> "$O2/bit2fasm.log"
[ -s "$W/raw.fasm" ] || { say "trimmed: BIT2FASM FAILED"; exit 0; }
python3 "$HB/fasm_bits.py" "$W/raw.fasm" "$W/$T.fasm" > /dev/null; rm -f "$W/raw.fasm"
cp "$TB/$T.json" "$TB/${T}_routed.json" "$RS/cells/build/gen/$T.v" "$RS/cells/build/gen/${K}_kernel_bench.v" "$W/"
say "trimmed: decoded from bits; bits md5 $(md5sum < "$TB/$T.bit" | cut -c1-8)"
bash "$HB/decode.sh" "$W" "$K" > "$O2/decode.out" 2>&1; [ -f "$W/m/bnd.json" ] || { say "trimmed: DECODE FAILED"; exit 0; }
cp "$O/untrimmed/exp.txt" "$O/untrimmed/pairs.txt" "$O2/"; PAIRS=$(cat "$O2/pairs.txt")
K0=$((10000 + 100 * S + 1))
for x in "" 0.8,1.0; do
  k0=$K0; [ -n "$x" ] && k0=$((K0 + 50))
  DRAW_XBAND=$x python3 "$HB/xdraws.py" "$O2/exp.txt" "$W/m/net.json" "$W/m/bnd.json" "$O2/d$k0" --kernel "$K" --pairs $PAIRS --draws "$ND" \
    --seed0 "$k0" --jobs "${JOBS:-4}" --routed "$W/m/routed.json" --tmax "${TMAX:-400000000}" > "$O2/d$k0.log" 2>&1
  say "trimmed: draws K $k0..$((k0 + ND - 1))${x:+ slow-carry $x}: $(grep '^draws [0-9]' "$O2/d$k0.log" | head -1) $(grep -E 'seed [0-9]+ (FAIL|UND)' "$O2/d$k0.log" | head -6 | tr '\n' ' ')"
  cp "$O2/d$k0/draws_summary.txt" "$O2/draws_summary_$k0.txt" 2>/dev/null; cp "$O2/d$k0/draws.txt" "$O2/draws_$k0.txt" 2>/dev/null; rm -rf "$O2/d$k0/net.simx" "$O2/d$k0/simx"
done
