#!/usr/bin/env bash
# build_route.sh NAME SIZES_VH SEED -- one xorshift bench route exactly as research/cluster/requests/draws2.sh builds item 35
# (eval_task.sh -> lane2.sh's build step, MLIR_OVERRIDE xorshift_predec.mlir, the draws2 BDC_* flags, NEXTPNR_SEED=SEED),
# but in a private tree made with `git archive HEAD` (no git worktree, nothing written into the repo), and without lane2's
# event-graph / corner_audit steps. Output: $RUNS/hw/NAME/{xorshift_bench_gen.{bit,sdf,fasm},_routed.json,kernel.v,
# ffmux.txt} and $RUNS/r/NAME/xray.sdf (the prjxray SDF bench_gate.sh reads). RUNS defaults to /tmp/claude-0/preload/runs.
set -euo pipefail
N=$1; Z=$2; S=$3; K=xorshift
R=$(cd "$(dirname "$0")/../../.." && pwd); RUNS=${RUNS:-/tmp/claude-0/preload/runs}
WT=$RUNS/wt/$N; HW=$RUNS/hw/$N; RD=$RUNS/r/$N
rm -rf "$WT"; mkdir -p "$WT" "$HW" "$RD"
git -C "$R" archive HEAD | tar -x -C "$WT"
mkdir -p "$WT/build"; cp -r "$R/build/frontend" "$WT/build/"
cp "$R/research/data/fifteen/xorshift_predec.mlir" "$WT/build/frontend/$K/comp/handshake_transformed.mlir"
cp "$R/$Z" "$WT/sizes.vh"
source "${TC:-$HOME/dev2/lib/fpgatoolchain}/openxc7/export.sh" > /dev/null
( cd "$WT/cells" && env BD_SKEW_AND_JOIN=1 BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 BDC_LINK_FASTFALL=1 \
    BDC_MERGE_RES_LINK=ucontrol_merge0 BDC_RING_COUNT_OLINKS=1 BDC_FORK_OUT_LINK=n11__0 BDC_MERGE_OUT_LINK=ucontrol_merge0 \
    NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES="$WT/sizes.vh" ./hw/build_bench.sh "$K" ) > "$HW/build.log" 2>&1 \
  || { echo "$N BUILD FAILED (see $HW/build.log)"; exit 1; }
B=$WT/cells/build/hw/${K}_bench_gen
cp "$B/${K}_bench_gen".{bit,sdf,fasm} "$B/${K}_bench_gen_routed.json" "$B/${K}_bench_gen.json" "$WT/cells/build/gen/${K}_kernel_bench.v" "$HW/" 2>/dev/null || \
cp "$B/${K}_bench_gen".{bit,sdf,fasm} "$B/${K}_bench_gen_routed.json" "$WT/cells/build/gen/${K}_kernel_bench.v" "$HW/"
cp "$B/toolchain.txt" "$HW/" 2>/dev/null || true
ff=$(python3 "$R/research/tools/ffmux_scan.py" "$HW/${K}_bench_gen.fasm" > "$HW/ffmux.txt" 2>&1 && echo ffmux-clean || echo FFMUX-FLAG)
PX=${TC:-$HOME/dev2/lib/fpgatoolchain}/openxc7-src/prjxray
PYTHONPATH=$PX python3 "$R/cells/gls/fid/xray_delay.py" --routed "$HW/${K}_bench_gen_routed.json" --sdf "$HW/${K}_bench_gen.sdf" --out "$RD/xray.sdf" > "$RD/xray.log" 2>&1
echo "$N sdf $(md5sum < "$HW/${K}_bench_gen.sdf" | cut -c1-8) bit $(md5sum < "$HW/${K}_bench_gen.bit" | cut -c1-8) xray $(md5sum < "$RD/xray.sdf" | cut -c1-8) $ff"
