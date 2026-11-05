#!/usr/bin/env bash
# T19: the combined worst case on an existing own route dir HW (gcd_hw/), own chain list, run_point2 + lapcheck.
# usage: run_wc_hw.sh TAG HWDIR
set -u
TAG=$1; HW=$2
python3 -I - $HW/gcd_hw_routed.json /root/wt-r14/cells/rtl/bd_latch.v /root/t19/chains_$TAG.band <<'PY'
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
  GLS_SDF_BAND_CELL=CARRY4=1,SELMUX2_1=1,SLICE_FFX=1 GLS_SDF_BAND_INST=@/root/t19/chains_$TAG.band GLS_SCATTER_SEED=1
echo "research $(git -C /root/wt-r14 rev-parse HEAD)" >> /root/r23work/$TAG.log
python3 -I /home/user/asyncfpga3/audit/tools/lapcheck.py /root/r23work/$TAG >> /root/r23work/$TAG.log 2>&1
mv /root/r23work/$TAG.log /home/user/asyncfpga3/audit/t19/; rm -f /home/user/asyncfpga3/audit/r23/$TAG.log; rm -rf /root/r23work/$TAG
echo ALLDONE >> /home/user/asyncfpga3/audit/t19/$TAG.log
