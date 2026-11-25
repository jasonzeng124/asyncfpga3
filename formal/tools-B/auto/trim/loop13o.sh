END=$(( $(date +%s) + 10*3600 ))
while [ $(date +%s) -lt $END ]; do
  cd /home/user/b/suite13t
  for n in */; do n=${n%/}; [ -f $n/t/j/w/m/net.json ] && [ -f $n/u/w/m/net.json ] || continue; grep -q "^$n " ../outsafe13.txt 2>/dev/null && continue
    a=$(timeout 2400 python3 /home/user/asyncfpga3/formal/tools-B/auto/outsafe.py $n/u/w/m 2>&1 | grep -o 'kappa_lo -\?[0-9.]*' | awk '{print $2}' | sort -g | head -1)
    b=$(timeout 2400 python3 /home/user/asyncfpga3/formal/tools-B/auto/outsafe.py $n/t/j/w/m 2>&1 | grep -o 'kappa_lo -\?[0-9.]*' | awk '{print $2}' | sort -g | head -1)
    echo "$n | output capture kappa_lo untrimmed ${a:-none} | trimmed ${b:-none}" >> ../outsafe13.txt
  done
  sleep 900
done
