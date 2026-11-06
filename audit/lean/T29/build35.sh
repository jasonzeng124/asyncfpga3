#!/usr/bin/env bash
# formal e9780623: C's Lean refutation CexPS (L000-074, X000-074, EncK, KBase, Wit, Refute), one module at a time
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
L=/root/build35.log; : > $L; cd /root/wt-f14/formal/lean
echo "HEAD $(git rev-parse HEAD)" >> $L
for mod in $(ls Formal/Net/CexPS/L*.lean | sort | sed 's#/#.#g; s#\.lean$##') Formal.Net.CexPS.EncK Formal.Net.CexPS.KBase $(ls Formal/Net/CexPS/X*.lean | sort | sed 's#/#.#g; s#\.lean$##') Formal.Net.CexPS.Wit Formal.Net.CexPS.Refute; do
  /usr/bin/time -f "%e s %M KB" timeout 7000 lake build $mod > /tmp/b35_one.log 2>&1; rc=$?
  echo "MOD $mod rc=$rc $(tail -1 /tmp/b35_one.log)" >> $L
  [ $rc != 0 ] && tail -25 /tmp/b35_one.log >> $L
done
echo B35DONE >> $L
