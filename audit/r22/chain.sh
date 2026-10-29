#!/bin/bash
# sequential (one sim at a time): wait for s6 new-resolver run, then s6 OLD resolver, then s7 new resolver
R=/home/user/asyncfpga3/audit/r22
until grep -q "run rc=" $R/s6_max/run_fid.log 2>/dev/null; do sleep 20; done
rm -f /root/r22work/s6_max/run_baked.vvp
R22_GLSFID=/root/wt-r12/cells/gls/fid $R/fullstack.sh /root/wt-r22/cells/build/hw/gcd_hw /root/r22work/s6_max_old max $R/s6_max_old
rm -f /root/r22work/s6_max_old/run_baked.vvp
$R/fullstack.sh /root/wt-r22s7/cells/build/hw/gcd_hw /root/r22work/s7_max max $R/s7_max
rm -f /root/r22work/s7_max/run_baked.vvp
echo CHAIN DONE
