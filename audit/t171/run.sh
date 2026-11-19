#!/usr/bin/env bash
# T171: formal A c68d896ed mr_verilog_check.py (answers T170: does the packed-cell model match bdc's emitted Verilog?).
# Negative control the tool itself does not use: research's BDC_RING_FUSE_NEGCTL=1 (packed cell corrupted:
# z_data {w_n36, w_n38} -> {{{31{1'b0}}, w_n38}, w_n38}; the circuit wedges, T170).
# Formal worktree /root/wt-fhead = origin/claude/formal; research bdc /root/wt-rhead = 34bde912c.
mkdir -p /root/t171/fx1/xorshift/comp; cp /root/wt-rhead/cloud/fixtures/frontend/xorshift/comp/handshake_transformed.mlir /root/t171/fx1/xorshift/comp/
cd /root/wt-fhead/formal/tools-A/rewrite
python3 mr_verilog_check.py /root/t171/fx1 /root/wt-rhead/bdc BDC_RING_FUSE_NEGCTL=1; echo "rc=$?"
python3 mr_verilog_check.py /root/t171/fx1 /root/wt-rhead/bdc; echo "rc=$?"
