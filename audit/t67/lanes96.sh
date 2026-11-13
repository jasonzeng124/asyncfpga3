#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t67
until [ -f ../t65/lanes95.done ]; do sleep 30; done
for s in 1 3; do bash run.sh l7_$s; done
echo DONE > lanes96.done
