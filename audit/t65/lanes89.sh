#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t65
until [ -f lanes88.done ]; do sleep 30; done
HWD=l3_1 GLS_SDF_FIELD=min bash run2.sh xorshift fastmin & HWD=l3_1 bash run2.sh xorshift worst; wait
HWD=l3_1 GLS_SDF_FIELD=max bash run2.sh xorshift slowmax
echo DONE > lanes89.done
