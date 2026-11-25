#!/bin/bash
#CLUSTER array=1 cores=4 mem=16G time=60
# Shard B (b_bitcmp): b_suiteauto2 task 1 (countloop seed 2) gave sdf 526cfe59 = research's, but bits md5 1c129c28 with the
# farm's nextpnr 6e5d224472232d5d, while the cloud's local build of the same patch set (sha b8e99a23) gives a7d13c71 for the
# same sdf. Rebuild it and return the nextpnr FASM (xz, base64) and the bit md5, to diff against the cloud's.
set -uo pipefail
mkdir -p $PEER/build/frontend; [ -d $PEER/build/frontend/countloop ] || cp -r $PEER/cloud/fixtures/frontend/* $PEER/build/frontend/
source "$TC/openxc7/export.sh" > /dev/null
Z=$(pwd)/formal/tools-B/auto/suite/sizes/countloop_2.vh
( cd $PEER/cells && BDC_AUTO=1 NEXTPNR_SEED=2 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$Z ./hw/build_bench.sh countloop ) > $RUNS/build.log 2>&1
B=$PEER/cells/build/hw/countloop_bench_gen
{ md5sum $B/countloop_bench_gen.sdf $B/countloop_bench_gen.bit $B/countloop_bench_gen.fasm; sha256sum $TC/openxc7/bin/nextpnr-xilinx | cut -c1-16; } > $OUT/md5.txt
xz -9 -c $B/countloop_bench_gen.fasm | base64 > $OUT/fasm.xz.b64
tail -5 $RUNS/build*.log > $OUT/build_tail.txt
exit 0
