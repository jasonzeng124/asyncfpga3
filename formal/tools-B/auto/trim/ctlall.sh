cd /home/user/b
for d in exit1_*_[0-9]; do [ -f $d/w/m/net.json ] && [ -f $d/pairs.txt ] || continue; grep -q "^$d " ctlall.txt 2>/dev/null && continue
  K=$(echo $d | sed 's/exit1_//; s/_[0-9]$//'); bash /home/user/asyncfpga3/formal/tools-B/auto/ctlsweep.sh $d $K >> ctlall.txt 2>&1; done
