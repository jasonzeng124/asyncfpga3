#!/usr/bin/env bash
# Wait for the clean build, then check the P7k audit file and each mutant (expected: audit OK, every mutant FAILS).
L=/home/user/asyncfpga3/audit/logs
until grep -q '^EXIT' $L/formal_build_6863284.log; do sleep 60; done
export PATH=$HOME/audit-lean/lean-4.35.0-linux/bin:$PATH
cd ~/wt-f7/formal/lean
for f in /home/user/asyncfpga3/audit/lean/P7k/P7kAudit.lean /home/user/asyncfpga3/audit/lean/P7k/Mut*.lean; do
  b=$(basename $f .lean); timeout 3600 lake env lean $f > $L/P7k/$b.out 2>&1; echo "$b exit=$?" >> $L/P7k/summary.txt
done
echo DONE >> $L/P7k/summary.txt
