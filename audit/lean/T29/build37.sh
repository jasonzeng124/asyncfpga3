#!/usr/bin/env bash
# formal 0f4cc750: A's FrontierPS (imports C's CexPS, whose oleans were deleted for disk): rebuild CexPS one module at a time, then FrontierPS
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
L=/root/build37.log; : > $L; cd /root/wt-f14/formal/lean
echo "HEAD $(git rev-parse HEAD)" >> $L
for mod in $(ls Formal/Net/CexPS/L*.lean | sort | sed 's#/#.#g; s#\.lean$##') Formal.Net.CexPS.EncK Formal.Net.CexPS.KBase $(ls Formal/Net/CexPS/X*.lean | sort | sed 's#/#.#g; s#\.lean$##') Formal.Net.CexPS.Wit Formal.Net.CexPS.Refute Formal.Target.FrontierPS; do
  /usr/bin/time -f "%e s %M KB" timeout 7000 lake build $mod > /tmp/b37_one.log 2>&1; rc=$?
  echo "MOD $mod rc=$rc $(tail -1 /tmp/b37_one.log)" >> $L
  [ $rc != 0 ] && tail -25 /tmp/b37_one.log >> $L
done
printf 'import Formal.Target.FrontierPS\n#check @Formal.Target.FrontierPS.not_seq_above\n#print axioms Formal.Target.FrontierPS.not_seq_above\n' > /root/A37.lean
timeout 3000 lake env lean /root/A37.lean >> $L 2>&1
echo B37DONE >> $L
