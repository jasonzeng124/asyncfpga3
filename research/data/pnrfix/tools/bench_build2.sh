#!/usr/bin/env bash
# bench_build2.sh NAME COMMIT KERNEL SEED TCVARIANT SIZES [ENV...]
# lane2.sh's build recipe (BD_DSP=1 BD_NO_TIGHTEN=1; SIZES "none" -> BD_SIZES=none, else BD_SIZES_GATE=0 BD_SIZES=<repo path>)
# in a private worktree of the pnrfix clone at COMMIT, with the shadow toolchain /tmp/bot/sa/pnrfix/tc-TCVARIANT.
# NEXTPNR_LOG_CONST_HOLDOUTS=1 (log only).  Keeps pnr inputs (JSON, XDC) + outputs in /tmp/bot/sa/pnrfix/runs/hw/NAME.
set -euo pipefail
N=$1; C=$2; K=$3; S=$4; V=$5; Z=$6; shift 6
P=/tmp/bot/sa/pnrfix; CL=$P/repo; WT=$P/wt/$N; HW=$P/runs/hw/$N
mkdir -p $P/wt "$HW"
if [ -d "$WT" ]; then git -C "$WT" checkout -q --detach "$C"; else git -C "$CL" worktree add -q --detach "$WT" "$C"; fi
rm -rf "$WT/build/frontend"; mkdir -p "$WT/build"; cp -r "$CL/build/frontend" "$WT/build/"
[ -n "${MLIR_OVERRIDE:-}" ] && cp "$WT/$MLIR_OVERRIDE" "$WT/build/frontend/$K/comp/handshake_transformed.mlir"
source $P/tc-$V/openxc7/export.sh > /dev/null
if [ "$Z" = none ]; then ZE="BD_SIZES=none"; else ZE="BD_SIZES_GATE=0 BD_SIZES=$WT/$Z"; fi
( cd "$WT/cells" && env "$@" $ZE NEXTPNR_SEED=$S BD_DSP=1 BD_NO_TIGHTEN=1 NEXTPNR_LOG_CONST_HOLDOUTS=1 \
    BD_TOOLCHAIN_LOG=$P/toolchain-scratch.log ./hw/build_bench.sh "$K" ) > "$HW/build.log" 2>&1 || { echo "$N BUILD FAILED (see $HW/build.log)"; exit 1; }
B=$WT/cells/build/hw/${K}_bench_gen
cp "$B/${K}_bench_gen".{bit,sdf,fasm,json,xdc} "$B/${K}_bench_gen_routed.json" "$B/pnr.log" "$WT/cells/build/gen/${K}_kernel_bench.v" "$HW/"
echo "$N sdf $(md5sum < "$HW/${K}_bench_gen.sdf" | cut -c1-8) fasm $(md5sum < "$HW/${K}_bench_gen.fasm" | cut -c1-8) json $(md5sum < "$HW/${K}_bench_gen_routed.json" | cut -c1-8) $(grep -o 'GND_NET: [0-9/]* sinks bridged ([0-9]* left' "$HW/pnr.log")"
grep 'HOLDOUT' "$HW/pnr.log" || true
