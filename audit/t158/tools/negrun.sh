#!/usr/bin/env bash
# negrun.sh W FLOW DROP TAG
W=$1 FLOW=$2 DROP=$3 TAG=$4; O=/root/agentC/res/$TAG
cd /root/agentC/$W
if [ "$FLOW" = auto ]; then export BDC_AUTO=1; else unset BDC_AUTO; fi
DROP_STAGE=$DROP nice -n 10 python3 /root/agentC/tools/neg.py build/frontend/quadrec/comp/handshake_transformed.mlir --c-oracle --vecfile kernels/quadrec/vec.hex > $O.out 2>&1
cp cells/build/kernelsim/quadrec_dut.v $O.dut.v
echo "$TAG: $(grep -E '^NEG' $O.out) | $(grep -E 'tb_simcheck_quadrec (PASS|FAIL)' $O.out|head -1) | OBS lines $(grep -c ^OBS $O.out)"
