#!/usr/bin/env bash
# T126: BOARD-QUEUE items 29 (ipow h4 + select links at 3, seed 19, recipe sdf 4a92cdf3) and 30 (collatz64 h4 + select
# links 3/6/3, pre_eq2, seed 10, recipe sdf 637ff02e). Own build from the research worktree at its HEAD (own build.sh),
# md5 vs recipe, own FF scan, GLS FAST_MIN / worst+scatter / SLOW_MAX with own oracle + t104 monitors, own static rule H
# (t109/rule_h.py) and rule E (t93/sites_any.py); collatz64 period by own run_per.sh. Sequential.
set -u
A=/home/user/asyncfpga3/audit; R=/root/wt-r91
git -C $R fetch -q origin; git -C $R checkout -q --detach origin/claude/research
echo "research $(git -C $R rev-parse --short HEAD) $(date -u)" > /root/t126.log
cd $A/t90
one() { # route kernel oracle vec
  local H=$1 K=$2 O=$3 V=$4
  python3 ../t67/scan_ff_own.py /root/t65/$H/*.fasm > /root/t90/ff_$H.txt 2>&1; echo "ff $H: $(tail -1 /root/t90/ff_$H.txt)" >> /root/t126.log
  export PS_MON_GEN=$A/t104/mon_both1.py MON_KERNEL=/root/t65/$H/${K}_kernel_bench.v
  for c in mon1_fastmin:min mon1_worst:band mon1_slowmax:max; do
    HWD=$H GLS_SDF_FIELD=${c##*:} timeout 5400 bash gate.sh $K ${c%%:*}
    python3 ../t65/oracle_$O.py check ../t65/$V /root/t65/${H}_${c%%:*}.log 2 > /root/t90/${H}_${c%%:*}_oracle.txt 2>&1
    echo "gate $H ${c%%:*}: $(tail -1 /root/t90/${H}_${c%%:*}_oracle.txt); viol $(grep -ciE 'VIOL|HAZ' /root/t65/${H}_${c%%:*}.log)" >> /root/t126.log
  done
  unset PS_MON_GEN MON_KERNEL
  for c in fastmin worst slowmax; do JSON=$A/t126/h_${H}_$c.json PATHS=0 python3 ../t109/rule_h.py /root/t65/work_${H}_mon1_$c /root/t65/$H/${K}_bench_gen_routed.json > $A/t126/rule_h_${H}_$c.txt 2>&1
    echo "ruleH $H $c: $(grep -m1 margin $A/t126/rule_h_${H}_$c.txt | cut -c1-120)" >> /root/t126.log; done
}
# item 29
R=$R bash build.sh ipsel3 19 > /root/t90/build_ipsel3_19.log 2>&1
echo "build ipsel3_19: $(grep -E '\.sdf$' /root/t90/build_ipsel3_19.log | head -1)" >> /root/t126.log
one ipsel3_19 ipow ipow ipow_17.hex
python3 ../t93/sites_any.py ipsel3_19 ipow 29 4a92cdf3 >> /root/t126.log 2>&1
# item 30
F=$R/build/frontend/collatz64/comp/handshake_transformed.mlir
cp $F /root/t126_c64_orig.mlir; cp $R/research/data/fifteen/collatz64_preeq2.mlir $F
R=$R bash build.sh c64sel3 10 > /root/t90/build_c64sel3_10.log 2>&1
cp /root/t126_c64_orig.mlir $F
echo "build c64sel3_10: $(grep -E '\.sdf$' /root/t90/build_c64sel3_10.log | head -1); usinkeq2 $(grep -c usinkeq2 /root/t65/c64sel3_10/collatz64_kernel_bench.v)" >> /root/t126.log
bash run_per.sh collatz64 c64sel3_10; echo "per c64sel3_10: $(grep BENCHRES /root/t90/per_c64sel3_10.log | tail -2 | tr '\n' ' ')" >> /root/t126.log
one c64sel3_10 collatz64 collatz64 collatz64_14.hex
python3 ../t93/sites_any.py c64sel3_10 collatz64 30 637ff02e >> /root/t126.log 2>&1
echo DONE >> /root/t126.log; echo DONE > /root/t126.done
