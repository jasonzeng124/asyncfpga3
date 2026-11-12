#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t65
for s in 2 3; do bash ../t67/build_ipowfm.sh $s > ../t67/build_ipowfm_$s.log 2>&1; ln -sfn /root/t67/ipowfm_$s /root/t65/ipowfm_$s; done &
wait
for s in 2 3; do (HWD=ipowfm_$s GLS_SDF_FIELD=min bash run2.sh ipow fastmin; HWD=ipowfm_$s bash run2.sh ipow worst) & done
wait; echo DONE > lanes73.done
