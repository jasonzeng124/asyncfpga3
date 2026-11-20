END=$(( $(date +%s) + 10*3600 ))
while [ $(date +%s) -lt $END ]; do
  cd /home/user/b/suite13t
  for n in */; do n=${n%/}; K=${n%_*}
    [ -f $n/t/j/steersafe.txt ] || continue; grep -q "^$n " ../xtol13.txt 2>/dev/null && continue
    a=$(bash /home/user/asyncfpga3/formal/tools-B/auto/trim/xtol.sh $n/u $K 2>&1 | grep -o 'weakest.*')
    b=$(bash /home/user/asyncfpga3/formal/tools-B/auto/trim/xtol.sh $n/t/j $K 2>&1 | grep -o 'weakest.*')
    echo "$n | untrimmed: $a | trimmed: $b" >> ../xtol13.txt
  done
  sleep 900
done
