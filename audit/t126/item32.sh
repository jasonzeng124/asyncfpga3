#!/usr/bin/env bash
# T126f: BOARD-QUEUE item 32 (collatz64 item 30 + proposal round h4s3p, pre_eq2, seed 22, recipe sdf 842dd4d7).
# Builds now; GLS after item 31 (t126c). Own md5 / usinkeq2 / FF scan / period; GLS 3 corners (oracle + t104 monitors);
# mon_sel select classifier at FAST_MIN; own rule H, rule E; bundling select link -> umux0 data -> downstream latches.
set -u
A=/home/user/asyncfpga3/audit; R=/root/wt-r91; L=/root/t126f.log
git -C $R fetch -q origin; git -C $R checkout -q --detach origin/claude/research
cd $A/t90; echo "research $(git -C $R rev-parse --short HEAD) $(date -u)" > $L
F=$R/build/frontend/collatz64/comp/handshake_transformed.mlir
cp $F /root/t126f_orig.mlir; cp $R/research/data/fifteen/collatz64_preeq2.mlir $F
R=$R bash build.sh c64sel3p 22 > /root/t90/build_c64sel3p_22.log 2>&1
cp /root/t126f_orig.mlir $F
H=c64sel3p_22; K=collatz64
echo "build: $(grep -E 'bench_gen.sdf$' /root/t90/build_$H.log | grep -v -- '->'); usinkeq2 $(grep -c usinkeq2 /root/t65/$H/${K}_kernel_bench.v)" >> $L
python3 ../t67/scan_ff_own.py /root/t65/$H/*.fasm > /root/t90/ff_$H.txt 2>&1; echo "ff: $(tail -1 /root/t90/ff_$H.txt)" >> $L
until [ -f /root/t126c.done ]; do sleep 60; done
bash run_per.sh collatz64 $H; echo "per: $(python3 ../t67/period_col.py /root/t90/per_$H.log)" >> $L
export PS_MON_GEN=$A/t104/mon_both1.py MON_KERNEL=/root/t65/$H/${K}_kernel_bench.v
for c in mon1_fastmin:min mon1_worst:band mon1_slowmax:max; do
  HWD=$H GLS_SDF_FIELD=${c##*:} timeout 5400 bash gate.sh $K ${c%%:*}
  python3 ../t65/oracle_collatz64.py check ../t65/collatz64_14.hex /root/t65/${H}_${c%%:*}.log 2 > /root/t90/${H}_${c%%:*}_oracle.txt 2>&1
  echo "gate ${c%%:*}: $(tail -1 /root/t90/${H}_${c%%:*}_oracle.txt); $(grep 'MUXMON t=' /root/t65/${H}_${c%%:*}.log | tail -3 | tr '\n' ' ')" >> $L
done
export PS_MON_GEN=$A/t116/mon_sel.py MON_MUXES=umux0,umux1,umux2 ZACKS=umux0=bridge_i.udut.n14__0_ack,umux2=bridge_i.bench_o_ack
HWD=$H GLS_SDF_FIELD=min timeout 5400 bash gate.sh $K sel_fastmin
echo "sel: $(grep 'SELMON t=\|no z_ack' /root/t65/${H}_sel_fastmin.log | tail -3 | tr '\n' ' ')" >> $L
unset PS_MON_GEN MON_KERNEL MON_MUXES ZACKS
for c in fastmin worst slowmax; do JSON=$A/t126/h_${H}_$c.json PATHS=0 python3 ../t109/rule_h.py /root/t65/work_${H}_mon1_$c /root/t65/$H/${K}_bench_gen_routed.json > $A/t126/rule_h_${H}_$c.txt 2>&1
  echo "ruleH $c: $(grep -m1 margin $A/t126/rule_h_${H}_$c.txt | cut -c1-120)" >> $L; done
python3 ../t93/sites_any.py $H $K 32 842dd4d7 >> $L 2>&1
for c in fastmin worst; do for d in 1 2 3 4; do echo "bundle $c n10__$d: $(python3 ../t128/bundle.py /root/t65/work_${H}_mon1_$c /root/t65/$H/${K}_bench_gen_routed.json "udut\.ulink_n10__$d\$" 'udut\.ulink_n14__0$' 2>&1 | grep overall)" >> $L; done; done
echo DONE >> $L; echo DONE > /root/t126f.done
