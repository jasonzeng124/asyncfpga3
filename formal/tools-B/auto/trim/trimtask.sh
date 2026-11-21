#!/usr/bin/env bash
# tools-B/auto/trim/trimtask.sh UNTRIMMED_DIR K SEED OUT NDRAWS MACRO=LEN ...  (shard B, UNTRUSTED simulation)
# Research's post-route trim (research/data/trim/README.md): matched-delay lines of a ROUTED design shortened by LUT INIT
# alone (research/tools/auto/trim_lines.py, run from $RSTRIM, a research checkout that has it). This applies the trims
# to a copy of UNTRIMMED_DIR (a build dir: K_bench_gen.{json,_routed.json,fasm}, gen/ with its generated Verilog), makes
# the bitstream as research's trim_shrink.sh does (fasm2frames + xc7frames2bit), then judges THAT bitstream with
# suite/task.sh PREBUILT=...: bits read back by prjxray, decoded, NDRAWS + NDRAWS slow-carry draws of research's model
# (K0 = research's suite K for SEED), research's oracle from the C. No MACRO=LEN: the untrimmed route itself.
set -uo pipefail
U=$(readlink -f "$1"); K=$2; S=$3; O=$4; ND=$5; shift 5
H=$(cd "$(dirname "$0")/.." && pwd); RST=${RSTRIM:-/home/user/rs}; export TC=${TC:-$HOME/dev2/lib/fpgatoolchain}
D=${K}_bench_gen; P=xc7z010clg400-1; DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7; PX=$TC/openxc7-src/prjxray
mkdir -p "$O"; HW=$O/hw; rm -rf "$HW"; cp -r "$U" "$HW"; rm -f "$HW/$D.bit" "$HW/$D.frames"
printf '%s\n' "$@" > "$O/trims.txt"
if [ $# -gt 0 ]; then
  python3 "$RST/research/tools/auto/trim_lines.py" "$U/${D}_routed.json" "$U/$D.fasm" "$HW/${D}_routed.json" "$HW/$D.fasm" "$@" \
    > "$O/trim.log" 2>&1 || { echo "trim_lines FAILED: $(tail -1 "$O/trim.log")" | tee "$O/summary.txt"; exit 1; }
fi
PYTHONPATH="$PX:$PX/third_party/fasm:$TC/openxc7/lib/python" python3 "$PX/utils/fasm2frames.py" --db-root "$DB" --part "$P" \
  "$HW/$D.fasm" > "$HW/$D.frames" 2> "$O/frames.log" && "$TC/openxc7/bin/xc7frames2bit" --part_file "$DB/$P/part.yaml" \
  --part_name "$P" --frm_file "$HW/$D.frames" --output_file "$HW/$D.bit" > "$O/bit.log" 2>&1 \
  || { echo "bitstream FAILED" | tee "$O/summary.txt"; exit 1; }
PREBUILT=$HW bash "$H/suite/task.sh" "$K" "$S" /dev/null - "$O/j" "$ND"
{ echo "trims: $*"; grep -c '^trim ' "$O/trim.log" 2>/dev/null | sed 's/^/chains trimmed: /'; cat "$O/j/summary.txt"; } > "$O/summary.txt"
cat "$O/summary.txt"
