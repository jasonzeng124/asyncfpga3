#!/usr/bin/env bash
# usage: fid_case.sh NAME FASM   -> work/NAME/{fasm2net.log,equiv.log}
source ~/auditlogs/export_dev2.sh
cd /home/user/asyncfpga3/audit/p2py/fid
HW=/home/user/wt-rb1/cells/build/hw/gcd_hw; W=work/$1; mkdir -p $W
python3 cells/gls/fid/fasm2net.py --fasm "$2" --out $W --names $HW/gcd_hw_routed.json --sdf $HW/gcd_hw.sdf > $W/fasm2net.log 2>&1; echo "fasm2net rc=$?"
python3 cells/gls/fid/fasm_equiv.py $HW/gcd_hw_routed.json $W/fasm_routed.json $W/routes.tsv $W/stubs.tsv --out $W/equiv.txt --max 4 > $W/equiv.log 2>&1; echo "equiv rc=$?"
grep -E "^[0-9]\.|VERDICT" $W/equiv.log; grep -A3 -E "LUT FUNCTION DIFFERS|DRIVER DIFFERS|PIP" $W/equiv.log | head -20
