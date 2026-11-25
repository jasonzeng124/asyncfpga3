#!/bin/bash
# tools-B/auto/trim/watch_trim.sh SUITE RS OUTF [NEXPECT] (shard B, UNTRUSTED simulation; local helper, this sandbox's paths)
# For research's farm requests with the trim step (AUTO_TRIM=1, e.g. suite13t): each finished non-array task's shipped
# route is rebuilt from its sizes (sdf checked), judged UNTRIMMED (4 + 4 draws), then the task's own trim record
# (auto/trim_<it>.txt, MACRO=LEN lines) is applied by research's trim_lines.py (trimtask.sh) and the TRIMMED bits are
# judged (8 + 8 draws), with steersafe.py --auto on both and ctlsweep.sh (B21's race) on the trimmed one.
# RS: a research checkout at the request's commit, build/frontend from cloud/fixtures/frontend.
SU=$1; RS=$2; OUTF=$3; NEXP=${4:-240}; P=/home/user/asyncfpga3/formal/tools-B/auto; B=/home/user/b/$SU; mkdir -p $B; touch $OUTF
END=$(( $(date +%s) + 12*3600 ))
while [ $(date +%s) -lt $END ]; do
  (cd /home/user/clu && timeout 300 git fetch -q --depth 1 origin claude/cluster && git reset -q --hard FETCH_HEAD)
  for d in /home/user/clu/results/$SU*/*/; do t=$(basename $(dirname $d))/$(basename $d); [ -f $d/result.txt ] || continue
    grep -q "^T$t " $OUTF && continue
    l=$(tail -1 $d/result.txt); K=$(echo $l | cut -d' ' -f1); S=$(echo $l | cut -d' ' -f2)
    if ! echo "$l" | grep -q 'status=PASS\|status=FAIL'; then echo "T$t $K $S SKIP-STATUS $(echo $l | cut -c1-80)" >> $OUTF; continue; fi
    f=$RS/kernels/$K/vec.hex; [ -f $f ] || f=$RS/research/data/suite/vec/$K.hex
    if head -1 $f 2>/dev/null | grep -q benchvec; then echo "T$t $K $S ARRAY (C's memtask)" >> $OUTF; continue; fi
    M=$(echo $l | grep -o 'sdf=[0-9a-f]*' | cut -d= -f2); IT=$(echo $l | grep -o ' it=[0-9]*' | cut -d= -f2)
    Z=$P/suite/sizes/${SU}_${K}_$S.vh; { echo "// from claude/cluster results/$t/auto/sizes_$IT.vh"; cat $d/auto/sizes_$IT.vh; } > $Z
    EV=$(grep '^ENV ' $d/auto/search.txt 2>/dev/null | tail -1 | cut -c5-)
    SI=$(grep -o '^search: .* from it [0-9]*' $d/auto/log.txt 2>/dev/null | tail -1 | grep -o '[0-9]*$')
    [ -n "$SI" ] && [ "$IT" -lt "$SI" ] && EV=""
    N=$B/${K}_$S; rm -rf $N; mkdir -p $N
    env $EV BDC_AUTO_REWRITES=0 RS=$RS JOBS=3 bash $P/suite/task.sh $K $S $Z $M $N/u 4 > /dev/null 2>&1
    sm=$(grep -o 'sdf [0-9a-f]* ([^)]*) [A-Z]*' $N/u/summary.txt 2>/dev/null); du=$(grep -o 'PASS [0-9]* FAIL [0-9]*' $N/u/summary.txt | tr '\n' ' ')
    TR=$(ls $d/auto/trim_$IT.txt 2>/dev/null || ls $d/auto/trim_*.txt 2>/dev/null | tail -1)
    tr=""; dt=""; st=""; cs=""
    if echo "$sm" | grep -q SAME; then
      cp -r $RS/cells/build/hw/${K}_bench_gen $N/hw0; mkdir -p $N/hw0/gen; cp $RS/cells/build/gen/${K}_bench_gen.v $RS/cells/build/gen/${K}_kernel_bench.v $N/hw0/gen/
      su=$(timeout 2400 python3 $P/steersafe.py $N/u/w/m --auto 2>&1 | tee $N/u/steersafe.txt | grep -o 'min kappa_lo .*')
      if [ -n "$TR" ]; then
        ARGS=$(grep -o '^BD_SZ_[A-Z0-9_]*=[0-9]*' $TR | tr '\n' ' '); tr="trims[$(echo $ARGS | wc -w)]"
        if [ -n "$ARGS" ]; then
          RSTRIM=$RS RS=$RS JOBS=3 bash $P/trim/trimtask.sh $N/hw0 $K $S $N/t 8 $ARGS > /dev/null 2>&1
          dt=$(grep -o 'PASS [0-9]* FAIL [0-9]*' $N/t/j/summary.txt | tr '\n' ' ')
          st=$(timeout 2400 python3 $P/steersafe.py $N/t/j/w/m --auto 2>&1 | tee $N/t/j/steersafe.txt | grep -o 'min kappa_lo .*')
          cs=$(bash $P/ctlsweep.sh $N/t/j $K 2>&1 | grep -o 'ctl slack.*')
        fi
      else tr="no trim record"; fi
      rm -rf $N/hw0/*.frames $N/t/hw/*.frames
    fi
    echo "T$t $K $S | $sm | untrimmed $du steer $su | $tr $dt steer $st | ctl $cs | research: $(echo $l | grep -o 'status=[A-Z]*') $(echo $l | grep -o 'P=[0-9]*\|P_untrimmed=[0-9]*' | tr '\n' ' ')" >> $OUTF
    rm -rf $N/u/d1*/simx $N/u/d1*/net.simx $N/t/j/d1*/simx $N/t/j/d1*/net.simx
  done
  p=$(wc -l < $OUTF); [ $p -ge $NEXP ] && break
  sleep 600
done
echo DONE >> $OUTF
