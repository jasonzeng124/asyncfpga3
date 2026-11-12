#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t65
for s in 3 4; do (HWD=pmf_$s GLS_SDF_FIELD=min bash run2.sh xorshift fastmin; HWD=pmf_$s bash run2.sh xorshift worst) & done
wait; echo DONE > lanes75.done
