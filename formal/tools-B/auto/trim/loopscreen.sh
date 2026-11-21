END=$(( $(date +%s) + 8*3600 ))
while [ $(date +%s) -lt $END ]; do
  cd /home/user/b
  for d in exit1_*_[0-9]; do [ -f $d/w/m/net.json ] && [ -f $d/pairs.txt ] || continue; [ -f $d/steersafe.txt ] || timeout 1500 python3 /home/user/asyncfpga3/formal/tools-B/auto/steersafe.py $d/w/m --auto > $d/steersafe.txt 2>&1; done
  bash ctlall.sh; bash xtolall.sh
  sleep 1200
done
