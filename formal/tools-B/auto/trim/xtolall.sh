cd /home/user/b
for d in exit1_*_[0-9]; do [ -f $d/w/m/net.json ] && [ -f $d/pairs.txt ] || continue; grep -q "^$d " xtol.txt 2>/dev/null && continue
  K=$(echo $d | sed 's/exit1_//; s/_[0-9]$//'); bash /home/user/asyncfpga3/formal/tools-B/auto/trim/xtol.sh $d $K >> xtol.txt 2>&1; done
