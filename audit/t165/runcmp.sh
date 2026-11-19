#!/bin/bash
source /root/audit-tc/openxc7/export.sh
j=$1; d=$2; n=$(echo $d | tr / _)
for v in old new; do
  nice -n 10 python3 /root/agentH/wt/cells/gls/fid/fasm_equiv_$v.py $j $d/fasm_routed.json $d/routes.tsv $d/stubs.tsv --max 40 --out /root/agentH/cmp/$n.$v.txt > /dev/null 2>&1; echo "$v rc=$? $n"
done
