#!/usr/bin/env bash
# T32: as route_wc_sz.sh but with BDC_LINK_FASTFALL=1 (board list item 3 = BOARD-QUEUE #5: R5 x0.75 + link fast fall).
# chain list (bd_delay source lines, as t17/chain_bels_own.py), then the worst-case gate with run_point2.sh + lapcheck.
set -u
S=$1; L=/root/t19/route_${SZ}ff_$S.log; HW=/root/t19/${SZ}ffs$S/gcd_hw; TAG=${SZ}ff_${S}_wc_s1
source /root/audit-tc/openxc7/export.sh
{ cd /root/wt-r14/cells && echo "research $(git rev-parse HEAD)"
  NEXTPNR_SEED=$S BD_SIZES=../research/data/${SZ:-gcd_hw_sizes_R5}.vh BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 BDC_LINK_FASTFALL=1 ./hw/build_hw.sh gcd_hw
  echo "build exit $?"
  PYTHONPATH=/root/audit-tc/openxc7-src/prjxray python3 gls/fid/xray_delay.py --routed build/hw/gcd_hw/gcd_hw_routed.json --sdf build/hw/gcd_hw/gcd_hw.sdf --out build/hw/gcd_hw/gcd_hw_xray.sdf
  md5sum build/hw/gcd_hw/gcd_hw.bit build/hw/gcd_hw/gcd_hw.sdf build/hw/gcd_hw/gcd_hw_xray.sdf
  rm -rf /root/t19/${SZ}ffs$S; mkdir -p /root/t19/${SZ}ffs$S; cp -r build/hw/gcd_hw /root/t19/${SZ}ffs$S/
} > $L 2>&1
cp $L /home/user/asyncfpga3/audit/t23/
python3 -I - $HW/gcd_hw_routed.json /root/wt-r14/cells/rtl/bd_latch.v /root/t19/chains_${SZ}ffs$S.band <<'PY'
import json, re, sys
m = list(json.load(open(sys.argv[1]))["modules"].values())[0]; src = open(sys.argv[2]).read().split('\n')
lines, cur = set(), None
for i, l in enumerate(src, 1):
    mm = re.match(r'\s*module\s+(\w+)', l)
    if mm: cur = mm.group(1)
    if cur in ('bd_delay', 'bd_delay_gated') and re.search(r'\bLUT\d\b.*\bu\s*\(', l): lines.add(i)
bels = sorted({c["attributes"]["NEXTPNR_BEL"] for c in m["cells"].values()
               if any(re.search(r'bd_latch\.v:%d\.' % ln, c["attributes"].get("src", "")) for ln in lines)})
open(sys.argv[3], 'w').write("# own src-line selection, band 0.21\n" + "".join("%s 0.21\n" % b for b in bels)); print(len(bels), "chain BELs")
PY
HW=$HW /home/user/asyncfpga3/audit/r23/run_point2.sh $TAG 0.02 0.126 all GLS_SDF_BAND=0.288 \
  GLS_SDF_BAND_CELL=CARRY4=1,SELMUX2_1=1,SLICE_FFX=1 GLS_SDF_BAND_INST=@/root/t19/chains_${SZ}ffs$S.band GLS_SCATTER_SEED=1
python3 -I /home/user/asyncfpga3/audit/tools/lapcheck.py /root/r23work/$TAG >> /root/r23work/$TAG.log 2>&1
mv /root/r23work/$TAG.log /home/user/asyncfpga3/audit/t23/; rm -f /home/user/asyncfpga3/audit/r23/$TAG.log; rm -rf /root/r23work/$TAG
cp /root/t19/chains_${SZ}ffs$S.band /home/user/asyncfpga3/audit/t23/
echo ALLDONE >> /home/user/asyncfpga3/audit/t23/$TAG.log
