#!/usr/bin/env bash
# run.sh W K FLOW(default|auto) VECFILE TAG [TIMEOUT_US] -- simcheck_obs in worktree W, then compare OBS with own oracle
W=$1 K=$2 FLOW=$3 VF=$4 TAG=$5 TO=${6:-0}
O=/root/agentC/res/$TAG
cd /root/agentC/$W
if [ "$FLOW" = auto ]; then export BDC_AUTO=1; else unset BDC_AUTO; fi
nice -n 10 python3 bdc/simcheck_obs.py build/frontend/$K/comp/handshake_transformed.mlir --c-oracle --vecfile "$VF" --timeout-us $TO > $O.out 2>&1
rc=$?
cp cells/build/kernelsim/${K}_dut.v $O.dut.v 2>/dev/null
python3 /root/agentC/tools/oracle.py /root/agentC/$W $K "$VF" > $O.exp
grep '^OBS ' $O.out | awk '{print $3}' > $O.obs
nv=$(wc -l < $O.exp); no=$(wc -l < $O.obs)
mism=$(paste $O.obs <(head -n $no $O.exp) | awk '{if (strtonum("0x"$1)!=strtonum("0x"$2)) n++} END{print n+0}')
verdict=$(grep -E "tb_simcheck_$K (PASS|FAIL)" $O.out | head -1)
floor=$(grep -c "token floor" $O.out)
echo "$TAG rc=$rc simcheck='$verdict' obs=$no/$nv own_mismatch=$mism floorlines=$floor"
