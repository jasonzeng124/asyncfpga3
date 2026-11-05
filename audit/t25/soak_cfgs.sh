#!/usr/bin/env bash
# T25: after route_collatz.sh: own xray SDF of the soak route, own chain list (bd_delay source lines), then
# soak_fid.py SEEDDIR WORK fasm --gate at SLOW_MAX, FAST_MIN and the combined worst case (draw 1).
set -u
until grep -q ALLDONE /home/user/asyncfpga3/audit/t25/route.log 2>/dev/null; do sleep 60; done
source /root/audit-tc/openxc7/export.sh
export PYTHONPATH=/root/audit-tc/openxc7-src/prjxray:${PYTHONPATH:-} XRAY_DB=/root/dev2/lib/xray/prjxray-db/zynq7
SD=/root/t25/collatz/seed1; P=$SD/pnr; L=/root/t25/soak.log
{ ls $P; cd /root/wt-r14/cells && python3 gls/fid/xray_delay.py --routed $P/soak_routed.json --sdf $P/soak.sdf --out /root/t25/soak_xray.sdf > /root/t25/xray.log 2>&1; echo "xray exit $?"
  md5sum $P/soak.sdf $P/soak.fasm /root/t25/soak_xray.sdf
  python3 -I - $P/soak_routed.json /root/wt-r14/cells/rtl/bd_latch.v /root/t25/chains.band <<'PY'
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
  for cfg in max min worst; do
    rm -rf /root/t25/w_$cfg
    case $cfg in
      max) E="GLS_SDF_FIELD=max";; min) E="GLS_SDF_FIELD=min";;
      worst) E="GLS_SDF_FIELD=band GLS_SDF_BAND=0.288 GLS_SDF_BAND_CELL=CARRY4=1,SELMUX2_1=1,SLICE_FFX=1 GLS_SDF_BAND_INST=@/root/t25/chains.band GLS_SCATTER_REGION=0.02 GLS_SCATTER=0.126 GLS_SCATTER_MODE=wire GLS_SCATTER_SEED=1";;
    esac
    echo "== $cfg: $E"
    env GLS_MODEL=fid GLS_SDF=/root/t25/soak_xray.sdf $E timeout 7000 python3 gls/fid/soak_fid.py $SD /root/t25/w_$cfg fasm --gate 2>&1 | tail -8
    grep -hE "GLS_SDF_BAND_INST:|GLS_SDF_BAND_CELL:|VERDICT" /root/t25/w_$cfg/*.log 2>/dev/null | head -4
    rm -f /root/t25/w_$cfg/*.vvp
  done; } > $L 2>&1
cp $L /home/user/asyncfpga3/audit/t25/soak.log; echo ALLDONE >> /home/user/asyncfpga3/audit/t25/soak.log
