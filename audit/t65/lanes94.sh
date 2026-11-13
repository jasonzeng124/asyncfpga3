#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t65
HWD=colr_1 GLS_SDF_FIELD=min bash run2.sh collatz fastmin; HWD=colr_1 bash run2.sh collatz worst; HWD=colr_1 GLS_SDF_FIELD=max bash run2.sh collatz slowmax
echo DONE > lanes94.done
