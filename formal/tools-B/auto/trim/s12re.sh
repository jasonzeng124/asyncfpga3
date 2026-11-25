P=/home/user/asyncfpga3/formal/tools-B/auto; RS=/home/user/rs12
for t in 17 12 11 16; do d=/home/user/clu/results/suite12/$t; l=$(tail -1 $d/result.txt); K=$(echo $l | cut -d' ' -f1); S=$(echo $l | cut -d' ' -f2)
  M=$(echo $l | grep -o 'sdf=[0-9a-f]*' | cut -d= -f2); IT=$(echo $l | grep -o ' it=[0-9]*' | cut -d= -f2)
  Z=$P/suite/sizes/suite12_${K}_$S.vh; { echo "// from claude/cluster results/suite12/$t/auto/sizes_$IT.vh"; cat $d/auto/sizes_$IT.vh; } > $Z
  EV=$(grep '^ENV ' $d/auto/search.txt 2>/dev/null | tail -1 | cut -c5-); SI=$(grep -o '^search: .* from it [0-9]*' $d/auto/log.txt 2>/dev/null | tail -1 | grep -o '[0-9]*$')
  [ -n "$SI" ] && [ "$IT" -lt "$SI" ] && EV=""
  O=/home/user/b/suite12_${K}_$S; rm -rf $O
  env $EV RS=$RS JOBS=1 bash $P/suite/task.sh $K $S $Z $M $O 2 > /dev/null 2>&1
  echo "T$t $K $S env[$EV] $(grep -o 'sdf [0-9a-f]* ([^)]*) [A-Z]*' $O/summary.txt) $(grep -o 'PASS [0-9]* FAIL [0-9]*' $O/summary.txt | tr '\n' ' ') | $(timeout 2400 python3 $P/steersafe.py $O/w/m --auto 2>&1 | tee $O/steersafe.txt | grep -o '^steers.*')" >> /home/user/b/s12re.txt
done
