#!/bin/bash
#CLUSTER array=1-16 cores=8 mem=40G time=220
# Shard C: margin tool (formal/tools/margin) full single-pin sweep on gcd_ps_e6bb4aec, LATCH=0, shard $TASK of 16.
set -uo pipefail
W=$RUNS/m; mkdir -p $W
# prjxray-db: the farm's $TC, else $XRAY_DB (root or zynq7 dir) linked into a TC-shaped tree
if [ ! -d "${TC:-/nonexistent}/openxc7/share/nextpnr/prjxray-db/zynq7" ] && [ -n "${XRAY_DB:-}" ]; then
  D=$XRAY_DB; [ -d "$D/zynq7" ] && D=$D/zynq7
  mkdir -p $RUNS/tc/openxc7/share/nextpnr/prjxray-db && ln -sfn "$D" $RUNS/tc/openxc7/share/nextpnr/prjxray-db/zynq7
  export TC=$RUNS/tc
fi
echo "TC=$TC" > $OUT/env.txt; ls "$TC/openxc7/share/nextpnr/prjxray-db/zynq7" | head -3 >> $OUT/env.txt
JOBS=${JOBS:-8} LATCH=0 SHARD=$TASK/16 KHI=0.45 KLO=0.20 W0=1 \
  bash formal/tools/margin/run.sh formal/target/gcd_ps_e6bb4aec.fromBit.fasm.xz $W > $OUT/run.txt 2>&1
rc=$?
for f in margins.txt summary.txt md5.txt run.log sweep_w20.txt sweep_w0.txt; do [ -f $W/$f ] && cp $W/$f $OUT/; done
[ -d $W/witness ] && { mkdir -p $OUT/witness; cp $W/witness/*.txt $W/witness/*.json $OUT/witness/ 2>/dev/null; }
exit $rc
