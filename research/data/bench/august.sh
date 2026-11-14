#!/bin/bash
# run from a worktree root: revert the bench synchroniser fix in gen_bench.py, exactly as
# cells/verify/cdc_bench.sh's "august" negative control does on the generated Verilog
# (i_ack_l_s / o_req_l_s read the async-set latches directly, as the August 2026 harness did).
set -e
f=cells/hw/gen_bench.py
cp $f $f.orig
sed -i -e 's|P("    wire i_ack_l_s = sync_i_ackl\[1\];")|P("    wire i_ack_l_s = i_ack_latched;")|' \
       -e 's|P("    wire o_req_l_s = sync_o_reql\[1\];")|P("    wire o_req_l_s = o_req_latched;")|' $f
n=$(diff $f.orig $f | grep -c '^>' || true)
[ "$n" = 2 ] || { echo "august.sh: expected 2 changed lines, got $n"; exit 1; }
echo "august.sh: synchroniser reverted (2 lines)"
