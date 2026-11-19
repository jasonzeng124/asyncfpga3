#!/usr/bin/env bash
# T166: research e060d7980 (fasm_equiv: dead undriven cells benign) calls cmpchain suite9 s1 (sdf a796dad1, farm task 29,
# commit eaef0dec7) NOT EQUIVALENT a false alarm. Own rebuild at eaef0dec7 with the farm's sizes_final.vh, own patched
# toolchain (/root/audit-tc2: all 10 patch fingerprints incl. const-sinks; nextpnr 7c3bfb9c, research's 6e5d2244), then
# decode the bits (fasm2net.py, research's decoder = the thing under test), OLD (eaef0dec7) and NEW (e060d7980)
# fasm_equiv, own INIT-aware deadness walk (t165/dead.py), own FF scan.
set -u
A=/home/user/asyncfpga3/audit; W=/root/wt-t166; L=/root/t166.log; K=cmpchain
echo "T166 $(date -u)" > $L
git -C /home/user/asyncfpga3 worktree remove --force $W 2>/dev/null; git -C /home/user/asyncfpga3 worktree add -q --detach $W eaef0dec7
mkdir -p $W/build; cp -r $W/cloud/fixtures/frontend $W/build/
source /root/audit-tc2/openxc7/export.sh >/dev/null 2>&1
( cd $W/cells && TC=/root/audit-tc2 BDC_AUTO=1 NEXTPNR_SEED=1 BD_DSP=1 BD_NO_TIGHTEN=1 BD_SIZES_GATE=0 BD_SIZES=$A/t166/cmpchain_s1_sizes_final.vh PNR_TIMEOUT=3600 ./hw/build_bench.sh $K ) > /root/t166_build.log 2>&1
echo "build rc=$?" >> $L
D=$W/cells/build/hw/${K}_bench_gen
echo "sdf $(md5sum $D/${K}_bench_gen.sdf | cut -c1-8) (farm a796dad1)" >> $L
python3 $A/t67/scan_ff_own.py $D/*.fasm > /root/t166_ff.txt 2>&1; echo "ff: $(tail -1 /root/t166_ff.txt)" >> $L
mkdir -p /root/t166w
python3 $W/cells/gls/fid/fasm2net.py --bit $D/${K}_bench_gen.bit --out /root/t166w/fid --names $D/${K}_bench_gen_routed.json --sdf $D/${K}_bench_gen.sdf > /root/t166_decode.log 2>&1
echo "decode rc=$?" >> $L
git -C /home/user/asyncfpga3 show e060d7980:cells/gls/fid/fasm_equiv.py > /root/t166w/fasm_equiv_new.py
for v in old new; do f=$W/cells/gls/fid/fasm_equiv.py; [ $v = new ] && f=/root/t166w/fasm_equiv_new.py
  python3 $f $D/${K}_bench_gen_routed.json /root/t166w/fid/fasm_routed.json /root/t166w/fid/routes.tsv /root/t166w/fid/stubs.tsv --max 40 --out /root/t166w/equiv_$v.txt > /dev/null 2>&1
  echo "$v: $(grep -m1 VERDICT /root/t166w/equiv_$v.txt)" >> $L; done
python3 $A/t165/dead.py $D/${K}_bench_gen_routed.json /root/t166w/dead.json > /root/t166w/dead.out 2> /root/t166w/dead.err; echo "dead.py rc=$?" >> $L
cp /root/t166w/equiv_*.txt /root/t166w/dead.json $A/t166/ 2>/dev/null
echo DONE >> $L
# NOTE (2026-11-19): the decode above lacked --ps7 and TC; the valid decode is:
#   TC=/root/audit-tc2 python3 $W/cells/gls/fid/fasm2net.py --ps7 --bit $D/cmpchain_bench_gen.bit --out /root/t166cmp/fid \
#       --names $D/cmpchain_bench_gen_routed.json --sdf $D/cmpchain_bench_gen.sdf
# then fasm_equiv (eaef0dec7 = old, e060d7980 = new) on fid/{fasm_routed.json,routes.tsv,stubs.tsv} -> equiv_{old,new}_ps7.txt
# control: the same decode of item 41's route (/root/t65/auto_xor_s8) is EQUIVALENT under both.
