#!/usr/bin/env bash
# formal da84aadb: C's 17 more datapath units (Net/Compute/PS/<Unit>), one unit at a time (lake builds its chunks), disk guard
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
L=/root/build56.log; echo "START $(date -u +%FT%TZ)" >> $L; cd /root/wt-f14/formal/lean
echo "HEAD $(git rev-parse HEAD)" >> $L
for f in $(ls Formal/Net/Compute/PS/*.lean | sort); do mod=$(echo $f | sed 's#/#.#g; s#\.lean$##')
  avail=$(df --output=avail -m /root | tail -1); if [ "$avail" -lt 400 ]; then echo "DISKSTOP $avail MB before $mod" >> $L; break; fi
  /usr/bin/time -f "%e s %M KB" timeout 7000 lake build $mod > /tmp/b56_one.log 2>&1; rc=$?
  echo "MOD $mod rc=$rc $(tail -1 /tmp/b56_one.log)" >> $L
  [ $rc != 0 ] && tail -15 /tmp/b56_one.log >> $L
done
cp $L /home/user/asyncfpga3/audit/lean/T29/build56.log; echo B56DONE >> /home/user/asyncfpga3/audit/lean/T29/build56.log
