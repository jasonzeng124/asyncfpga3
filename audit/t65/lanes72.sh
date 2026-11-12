#!/usr/bin/env bash
cd /home/user/asyncfpga3/audit/t65
until [ -f lanes71.done ] || grep -q BUILDDONE ../t67/build_colb_1.log 2>/dev/null; do sleep 20; done
bash build_cdbffs7.sh > build_cdbffs7.log 2>&1
grep -c "FASTFALL(1)\|RFAST(1)" /root/wt-r65/cells/build/gen/collatz64_kernel_bench.v > cdbffs7_ffcount.txt
HWD=cdbffs7 GLS_SDF_FIELD=min bash run2.sh collatz64 fastmin
echo DONE > lanes72.done
