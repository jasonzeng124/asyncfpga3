#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t65
HWD=pmf_5 GLS_SDF_FIELD=min bash run2.sh xorshift fastmin &
bash ../t67/build_ipowfm.sh 4 > ../t67/build_ipowfm_4.log 2>&1; ln -sfn /root/t67/ipowfm_4 /root/t65/ipowfm_4
HWD=ipowfm_4 GLS_SDF_FIELD=min bash run2.sh ipow fastmin
wait; echo DONE > lanes79.done
