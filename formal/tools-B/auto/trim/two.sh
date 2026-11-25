P=/home/user/asyncfpga3/formal/tools-B/auto; RS=/home/user/rsx2; cd /home/user/b/trim
run() { t=$1; shift; d=/home/user/clu/results/exit1/$t; l=$(tail -1 $d/result.txt); K=$(echo $l | cut -d' ' -f1); S=$(echo $l | cut -d' ' -f2)
  M=$(echo $l | grep -o 'sdf=[0-9a-f]*' | cut -d= -f2); IT=$(echo $l | grep -o ' it=[0-9]*' | cut -d= -f2)
  Z=$P/suite/sizes/exit1_${K}_$S.vh; { echo "// from claude/cluster results/exit1/$t/auto/sizes_$IT.vh"; cat $d/auto/sizes_$IT.vh; } > $Z
  EV=$(grep '^ENV ' $d/auto/search.txt 2>/dev/null | tail -1 | cut -c5-); SI=$(grep -o '^search: .* from it [0-9]*' $d/auto/log.txt 2>/dev/null | tail -1 | grep -o '[0-9]*$')
  [ -n "$SI" ] && [ "$IT" -lt "$SI" ] && EV=""
  N=${K}${S}; rm -rf u_$N; env $EV BDC_AUTO_REWRITES=0 RS=$RS JOBS=1 bash $P/suite/task.sh $K $S $Z $M u_$N 1 > /dev/null 2>&1
  cp -r $RS/cells/build/hw/${K}_bench_gen ${N}_untrimmed; mkdir -p ${N}_untrimmed/gen; cp $RS/cells/build/gen/${K}_bench_gen.v $RS/cells/build/gen/${K}_kernel_bench.v ${N}_untrimmed/gen/
  RSTRIM=/home/user/rs RS=$RS JOBS=2 bash $P/trim/trimtask.sh ${N}_untrimmed $K $S t_$N 8 "$@" > /dev/null 2>&1
  echo "$K s$S untrimmed: $(grep -o 'sdf [0-9a-f]* ([^)]*) [A-Z]*' u_$N/summary.txt) | trimmed ($*): $(grep -o 'chains trimmed: [0-9]*' t_$N/summary.txt) $(grep -o 'PASS [0-9]* FAIL [0-9]*' t_$N/j/summary.txt | tr '\n' ' ')" >> two.txt
  for x in u_$N t_$N/j; do echo "  $x $(timeout 2400 python3 $P/steersafe.py $x/w/m --auto 2>&1 | tee $x/steersafe.txt | grep -o '^steers.*') :: $(head -1 $x/steersafe.txt | cut -c1-200)" >> two.txt; bash $P/ctlsweep.sh $x $K >> two.txt 2>&1; done; }
run 8 BD_SZ_BRIDGE_I_UDUT_UCMPI0=10 BD_SZ_BRIDGE_I_UDUT_ULINK_N22__0=2 BD_SZ_BRIDGE_I_UDUT_ULINK_N22__1=1 BD_SZ_BRIDGE_I_UDUT_UMUX0=2 BD_SZ_BRIDGE_I_UDUT_UMUX1=2
run 39 BD_SZ_BRIDGE_I_UDUT_UCMPI1=13 BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE0=2 BD_SZ_BRIDGE_I_UDUT_UMUX1=2 BD_SZ_BRIDGE_I_UDUT_UMUX3=2
