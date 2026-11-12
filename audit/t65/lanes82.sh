#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t65
HWD=pmr_1 GLS_SDF_FIELD=min bash run2.sh xorshift fastmin &
HWD=pmr_1 bash run2.sh xorshift worst
wait; HWD=pmr_1 GLS_SDF_FIELD=max bash run2.sh xorshift slowmax
echo DONE > lanes82.done
