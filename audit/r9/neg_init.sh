#!/bin/bash
# Negative control: s4_max full-stack netlist with every umux*.udat.pair[0] LUT6 INIT forced to 0 (break_init.py), same tb/judge.
source ~/audit-tc/openxc7/export.sh >/dev/null 2>&1
W=~/r9work/neg_s4_max; GLS=~/r9work/wt-s4/cells/gls; cd $W
iverilog -gspecify -DGLS_TRANSPORT_IC -DGLS_FID -I$GLS -I. -o audit.vvp tb_audit.v netlist_broken.v $GLS/prims.v 2>&1 | grep -v 'procedural continuous'
mkdir -p ajlog
for p in "0 1" "6 12" "13 2"; do for v in $p; do vvp audit.vvp +VEC=$v +TEND=150000 +QUIET=200000 > ajlog/v$v.log 2>&1 & done; wait; done
python3 /home/user/asyncfpga3/audit/r7/judge/check.py /home/user/asyncfpga3/audit/r7/judge/oracle_C.txt ajlog 0 1 2 6 12 13; echo "JUDGE RC $?"
