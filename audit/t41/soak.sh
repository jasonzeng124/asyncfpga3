#!/usr/bin/env bash
# T41: usage soak.sh D   (D=orig -> unmodified soak_fid.py; else the envd copy with SOAK_ENV_DELAY=D). FAST_MIN, fasm --gate.
set -u
D=$1
source /root/audit-tc/openxc7/export.sh
export PYTHONPATH=/root/audit-tc/openxc7-src/prjxray:${PYTHONPATH:-} XRAY_DB=/root/dev2/lib/xray/prjxray-db/zynq7
SD=/root/t41/isp_b/seed30; P=$SD/pnr
cd /root/wt-r34/cells
if [ ! -s /root/t41/xray.sdf ]; then
  python3 gls/fid/xray_delay.py --routed $P/soak_routed.json --sdf $P/soak.sdf --out /root/t41/xray.sdf > /root/t41/xray.log 2>&1; echo "xray exit $?"
fi
md5sum $P/soak.sdf $P/soak.fasm /root/t41/xray.sdf
W=/root/t41/w_D$D; rm -rf $W
if [ "$D" = orig ]; then S=gls/fid/soak_fid.py; E=""; else S=/root/t41/envd/soak_fid_envd.py; E="SOAK_ENV_DELAY=$D"; fi
echo "== D=$D script=$S $(date -u)"
env GLS_MODEL=fid GLS_SDF=/root/t41/xray.sdf GLS_SDF_FIELD=min $E timeout 7000 python3 $S $SD $W fasm --gate; echo "soak exit $? $(date -u)"
rm -f $W/*.vvp
echo ALLDONE
