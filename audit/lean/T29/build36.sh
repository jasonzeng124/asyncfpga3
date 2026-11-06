#!/usr/bin/env bash
# formal d2494073: C's CexPS72 (kappa 18/25 refutation) and B's new cell modules, one module at a time
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
L=/root/build36.log; : > $L; cd /root/wt-f14/formal/lean
echo "HEAD $(git rev-parse HEAD)" >> $L
M="$(ls Formal/Net/CexPS72/L*.lean | sort | sed 's#/#.#g; s#\.lean$##') Formal.Net.CexPS72.EncK Formal.Net.CexPS72.KBase $(ls Formal/Net/CexPS72/X*.lean | sort | sed 's#/#.#g; s#\.lean$##') Formal.Net.CexPS72.Wit Formal.Net.CexPS72.Refute"
M="$M Formal.Cells.SpecLatchSep Formal.Cells.SpecCElemWin Formal.Cells.CElemWinView $(ls Formal/Cells/CElemWinViewPS/*.lean | sort | sed 's#/#.#g; s#\.lean$##') Formal.Cells.CElemWinViewPS $(ls Formal/Cells/LatchViewPS/*.lean | sort | sed 's#/#.#g; s#\.lean$##') Formal.Cells.LatchViewPS Formal.Cells.ArbViewPSReset Formal.Cells.GrantExcl Formal.Cells.ArbGrantPS Formal.Cells.AckLow Formal.Cells.ArbAckPS"
for mod in $M; do
  /usr/bin/time -f "%e s %M KB" timeout 7000 lake build $mod > /tmp/b36_one.log 2>&1; rc=$?
  echo "MOD $mod rc=$rc $(tail -1 /tmp/b36_one.log)" >> $L
  [ $rc != 0 ] && tail -25 /tmp/b36_one.log >> $L
done
echo B36DONE >> $L
