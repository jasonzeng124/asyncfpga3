#!/bin/bash
# run from a worktree root: compile out the bench's 64x16 latency histogram (an observer only:
# its write data becomes 0, so yosys removes the 1024 flops; HIST reads 0).  Nothing the FSM,
# the synchronisers or the kernel see changes.  Needed because BD_RLOC=v4 does not place in the
# full bench (nextpnr's RLOC repair strands the uori2/uori4 columns, then asserts).
set -e
f=cells/hw/gen_bench.py
[ -f $f.orig0 ] || cp $f $f.orig0
sed -i "s|hist\[bucket_q2\] <= hist_rd + 16\\\\'d1;|hist[bucket_q2] <= 16\\\\'b0;  // nohist.sh|" $f
grep -q 'nohist.sh' $f || { echo "nohist.sh: did not apply"; exit 1; }
echo "nohist.sh: histogram compiled out"
