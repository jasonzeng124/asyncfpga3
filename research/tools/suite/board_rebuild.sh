#!/usr/bin/env bash
# board_rebuild.sh SPEC -- rebuild one route of the automatic flow for the board, byte for byte, and put its bitstream
# where cells/hw/loop_cost.sh reads it (cells/build/hw/K_bench_gen/K_bench_gen.bit).  Exit 0 only when the route and
# the trimmed bits are the ones SPEC names; any mismatch exits 1 and copies nothing.
#
# SPEC (research/data/suite/board/*.spec) is a few KEY=VALUE lines:
#   K      the kernel                         SEED   the iteration's placer seed (the loop's seed_I.txt)
#   SIZES  the iteration's sizes (repo path)  TRIMS  the route's recorded trims, MACRO=LEN per line (repo path; may be -)
#   MLIR   formal's proved rewrite (repo path, the flow's AUTO_PROVED_RW memo output) or -
#   ENV    the build's bdc knobs besides BDC_AUTO=1 (the loop's search structure, e.g. BDC_FORK_OUT_LINK=...), and
#          the trim step's naming (TRIM_STAGEFIX=1 / BD_DEFINES=-DBD_SYMTRIM for a route of flows v11 on)
#   SDF    md5 (first 8) of the route's SDF   FASM   md5 (first 8) of the trimmed FASM (the bits the flow judged)
# The build is the flow's own: research/tools/fifteen/lane2.sh with LANE_NORUN=1 (a private worktree at this checkout,
# cells/hw/build_bench.sh with BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=SIZES, NEXTPNR_SEED=SEED,
# BDC_AUTO_REWRITES=0, MLIR_OVERRIDE=MLIR), then the trims by LUT INIT only (research/tools/auto/trim_lines.py
# --partial, as auto_size.sh's trim_route re-applies them) and the bitstream as auto_size.sh's mkbit makes it.
# Needs $TC with cells/verify/toolchain.sh passing (checked first).  Work files: ${BQ_RUNS:-$HOME/runs/bq}/; the build
# worktree is lane ${BQ_LANE:-bq} (one worktree, ~250 MB, reused by every rebuild; set BQ_LANE per worker to run several).
set -uo pipefail
R=$(cd "$(dirname "$0")/../../.." && pwd); SPEC=$(readlink -f "$1")
TC=${TC:-$HOME/dev2/lib/fpgatoolchain}; export TC
get() { sed -n "s/^$1=//p" "$SPEC" | head -1; }
K=$(get K); S=$(get SEED); Z=$(get SIZES); TR=$(get TRIMS); M=$(get MLIR); XE=$(get ENV); WS=$(get SDF); WF=$(get FASM)
[ -n "$K" ] && [ -n "$S" ] && [ -n "$Z" ] && [ -n "$WS" ] && [ -n "$WF" ] || { echo "board_rebuild: $SPEC lacks a key"; exit 2; }
"$R/cells/verify/toolchain.sh" > /dev/null 2>&1 || { echo "board_rebuild: cells/verify/toolchain.sh FAILED: nothing built here is the route"; exit 1; }
export RUNS=${BQ_RUNS:-$HOME/runs/bq}; N=bq_${K}_$S; D=${K}_bench_gen; H=$RUNS/hw/$N
mkdir -p "$RUNS"
cd "$R"
if [ "$M" != - ] && [ -n "$M" ]; then export MLIR_OVERRIDE=$M; else unset MLIR_OVERRIDE; fi
# lane2.sh resolves its VECFILE argument (readlink -f under set -e) even with LANE_NORUN=1, where it is not used: give it
# one that exists (a Dynamatic test kernel has no kernels/K/)
VF=kernels/$K/vec.hex; [ -f "$R/$VF" ] || VF=research/data/suite/vec/$K.hex; [ -f "$R/$VF" ] || VF=$SPEC
env LANE_NORUN=1 BDC_AUTO_REWRITES=0 research/tools/fifteen/lane2.sh "${BQ_LANE:-bq}" "$N" "$K" "$R/$Z" "$S" "$VF" \
  BDC_AUTO=1 $XE > "$RUNS/$N.build.txt" 2>&1 || { echo "board_rebuild: build FAILED ($(tail -1 "$RUNS/$N.build.txt"))"; exit 1; }
sdf=$(md5sum < "$H/$D.sdf" | cut -c1-8)
[ "$sdf" = "$WS" ] || { echo "board_rebuild: sdf $sdf, not $WS: NOT the route judged (do not use it)"; exit 1; }
cp "$H/${D}_routed.json" "$H/${D}_routed.untrimmed.json"; cp "$H/$D.fasm" "$H/$D.untrimmed.fasm"
if [ "$TR" != - ] && [ -n "$TR" ]; then
  # the trims see the spec's ENV, as the flow's trim step saw the flow's: trim_lines.py names a multi-stage link's
  # _SDELAY line by the stage-aware rule only under TRIM_STAGEFIX=1 / AUTO_OVERBUILD / BD_SYMTRIM (flows v11 on), and
  # without them those recorded trims map to no chain (2026-11-22: a v11 late route rebuilt here left 10 stage lines
  # untrimmed -- bits that were never judged; items 42-45, all flow v10 routes, had no refusal)
  env $XE python3 research/tools/auto/trim_lines.py --partial "$H/${D}_routed.untrimmed.json" "$H/$D.untrimmed.fasm" \
    "$H/${D}_routed.json" "$H/$D.fasm" $(cat "$R/$TR") > "$H/trim.log" 2>&1 || { echo "board_rebuild: trim FAILED (see $H/trim.log)"; exit 1; }
  # every recorded trim was applied once on the judged route (the flow records only what it applied), so a refusal
  # here means a different naming or a different route: never the judged bits
  grep -q '^REFUSED' "$H/trim.log" && { echo "board_rebuild: $(grep -c '^REFUSED' "$H/trim.log") recorded trim(s) refused (see $H/trim.log): NOT the bits judged"; exit 1; }
fi
fa=$(md5sum < "$H/$D.fasm" | cut -c1-8)
[ "$fa" = "$WF" ] || { echo "board_rebuild: trimmed fasm $fa, not $WF: NOT the bits judged (do not use them)"; exit 1; }
P=xc7z010clg400-1; DB=$TC/openxc7/share/nextpnr/prjxray-db/zynq7; PX=$TC/openxc7-src/prjxray
PYTHONPATH="$PX:$TC/openxc7/lib/python" python3 "$PX/utils/fasm2frames.py" --db-root "$DB" --part "$P" "$H/$D.fasm" \
  > "$H/$D.frames" 2> "$H/frames.log" &&
"$TC/openxc7/bin/xc7frames2bit" --part_file "$DB/$P/part.yaml" --part_name "$P" --frm_file "$H/$D.frames" \
  --output_file "$H/$D.bit" > "$H/bit.log" 2>&1 || { echo "board_rebuild: bitstream FAILED (see $H/frames.log, bit.log)"; exit 1; }
python3 research/tools/ffmux_scan.py "$H/$D.fasm" > "$H/ffmux_trimmed.txt" 2>&1 || { echo "board_rebuild: ffmux_scan flags the trimmed fasm (see $H/ffmux_trimmed.txt)"; exit 1; }
O=$R/cells/build/hw/$D; mkdir -p "$O"
[ -f "$O/$D.bit" ] && cp "$O/$D.bit" "$O/$D.bit.before_bq"
cp "$H/$D.bit" "$H/$D.sdf" "$H/$D.fasm" "$O/"
echo "board_rebuild: $K seed $S OK -- sdf $sdf, trimmed fasm $fa, bit $(md5sum < "$O/$D.bit" | cut -c1-8) in cells/build/hw/$D/ (an older bit there: $D.bit.before_bq)"
