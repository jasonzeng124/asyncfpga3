#!/usr/bin/env bash
# Run research's oracle.sh / oracle_mem.sh from a private copy (rh/) of the needed parts of /root/wt-rh.
set -u; A=/root/agentA; cd $A
rm -rf rh rhout; mkdir -p rh/research/tools rh/research/data rh/cells rhout
cp -r /root/wt-rh/research/tools/suite rh/research/tools/; cp -r /root/wt-rh/research/data/suite rh/research/data/
cp -r /root/wt-rh/kernels rh/; cp -r /root/wt-rh/cells/hw rh/cells/; cp -r /root/wt-rh/bdc rh/
for k in factorial iterative_division iterative_sqrt test_int16; do rh/research/tools/suite/oracle.sh $k < rh/research/data/suite/vec/$k.hex > rhout/$k.exp; done
for k in test_loop_free if_loop_1 if_loop_2 sumi3_mem fir test_bitint; do rh/research/tools/suite/oracle_mem.sh $k rh/research/data/suite/vec/$k.hex > rhout/$k.exp; done
for k in dot2 gather memsum; do rh/research/tools/suite/oracle_mem.sh $k rh/kernels/$k/vec.hex > rhout/$k.exp; done
rh/research/tools/suite/oracle_mem.sh unused_arg rh/research/data/suite/vec/unused_arg.hex > rhout/unused_arg.exp 2>rhout/unused_arg.nobuild.log || echo "unused_arg: refused without build/frontend (expected): $(cat rhout/unused_arg.nobuild.log)"
mkdir -p rh/build/frontend/unused_arg && cp -r /root/wt-rh/cloud/fixtures/frontend/unused_arg/comp rh/build/frontend/unused_arg/
rh/research/tools/suite/oracle_mem.sh unused_arg rh/research/data/suite/vec/unused_arg.hex > rhout/unused_arg.exp
