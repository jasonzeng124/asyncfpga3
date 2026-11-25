#!/bin/bash
# tools-B/auto/suite/watch_suite.sh [SUITE] [RS] [OUTF] [NEXPECT] (shard B, UNTRUSTED simulation; local helper): written for research's suite12, generalised 2026-11-20 for exit1 (RS = a research checkout at the request's commit, build/frontend from its FIXTURES); paths are this sandbox's.
# s12.sh: process research's suite12 (flow v8) routes as they land: rebuild (sizes_<it>.vh + search ENV), 8 + 8 draws, outsafe
SU=${1:-suite12}; RS=${2:-/home/user/rs}; P=/home/user/asyncfpga3/formal/tools-B/auto; OUTF=${3:-/home/user/b/s12_results.txt}; NEXP=${4:-62}; mkdir -p /home/user/b; touch $OUTF
END=$(( $(date +%s) + 10*3600 ))
while [ $(date +%s) -lt $END ]; do
  (cd /home/user/clu && timeout 300 git fetch -q --depth 1 origin claude/cluster && git reset -q --hard FETCH_HEAD)
  for d in /home/user/clu/results/$SU/*/; do t=$(basename $d); [ -f $d/result.txt ] || continue
    grep -q "^T$t " $OUTF && continue
    l=$(tail -1 $d/result.txt); K=$(echo $l | cut -d' ' -f1); S=$(echo $l | cut -d' ' -f2)
    if ! echo "$l" | grep -q 'status=PASS\|status=FAIL'; then echo "T$t $K $S SKIP-STATUS $(echo $l | cut -c1-80)" >> $OUTF; continue; fi
    f=$RS/kernels/$K/vec.hex; [ -f $f ] || f=$RS/research/data/suite/vec/$K.hex
    if head -1 $f 2>/dev/null | grep -q benchvec; then echo "T$t $K $S ARRAY (C's memtask) $(echo $l | grep -o 'status=[A-Z]*')" >> $OUTF; continue; fi
    M=$(echo $l | grep -o 'sdf=[0-9a-f]*' | cut -d= -f2); IT=$(echo $l | grep -o ' it=[0-9]*' | cut -d= -f2)
    Z=$P/suite/sizes/${SU}_${K}_$S.vh; { echo "// from claude/cluster results/$SU/$t/auto/sizes_$IT.vh"; cat $d/auto/sizes_$IT.vh; } > $Z
    EV=$(grep '^ENV ' $d/auto/search.txt 2>/dev/null | tail -1 | cut -c5-)
    SI=$(grep -o '^search: .* from it [0-9]*' $d/auto/log.txt 2>/dev/null | tail -1 | grep -o '[0-9]*$')
    [ -n "$SI" ] && [ "$IT" -lt "$SI" ] && EV=""   # the shipped route predates the search (its knob was rejected): no search ENV
    O=/home/user/b/${SU}_${K}_$S; rm -rf $O
    env $EV RS=$RS JOBS=${JOBS:-4} bash $P/suite/task.sh $K $S $Z $M $O 8 > /dev/null 2>&1
    sm=$(grep -o 'sdf [0-9a-f]* ([^)]*) [A-Z]*' $O/summary.txt 2>/dev/null); dr=$(grep -o 'PASS [0-9]* FAIL [0-9]*' $O/summary.txt 2>/dev/null | tr '\n' ' ')
    nm=$(cat $O/d1*/draws.txt 2>/dev/null | grep -o 'nearmiss [0-9]*' | awk '{s+=$2} END{print s+0}')
    ks=""; [ -f $O/w/m/net.json ] && ks=$(timeout 2400 python3 $P/outsafe.py $O/w/m 2>/dev/null | grep -o 'kappa_lo -\?[0-9.]*' | awk '{print $2}' | sort -g | head -1)
    ss=""; [ -f $O/w/m/net.json ] && ss=$(timeout 2400 python3 $P/steersafe.py $O/w/m --auto 2>/dev/null | grep -o "^steers.*")
    other=$(grep -o 'SKIP\|NO-ORACLE\|DECODE FAILED\|BUILD FAILED' $O/summary.txt 2>/dev/null | head -1)
    echo "T$t $K $S env[$EV] research:$(echo $l | grep -o 'status=[A-Z]*' ) $(echo $l | grep -o 'draws=[0-9/]*') | $sm | $dr| pulses $nm | kappa_lo ${ks:-none} | ${ss:-steers -} $other" >> $OUTF
    rm -rf $O/d1*/simx $O/d1*/net.simx
  done
  n=$(ls -d /home/user/clu/results/$SU/*/ 2>/dev/null | wc -l); p=$(wc -l < $OUTF); [ $p -ge $NEXP ] && break
  sleep 600
done
echo DONE >> $OUTF
