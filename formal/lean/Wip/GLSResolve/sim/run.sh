#!/bin/sh
# iverilog cross-check of Formal/Core/Delay/GLSResolve.lean (notes/A-gls-resolve.md §3).
# Research sources are taken read-only from origin/claude/research into a temp dir.
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"; T="$(mktemp -d)"; cd "$T"
git -C "$HERE" show origin/claude/research:cells/gls/fid_core.vh > fid_core.vh
git -C "$HERE" show origin/claude/research:cells/gls/prims.v > prims.v
cp "$HERE"/tb_c2.v "$HERE"/tb_lost.v "$HERE"/check_c2.py .
iverilog -g2012 -gspecify -DGLS_FID -DGLS_TRANSPORT_IC -o tb_c2.vvp tb_c2.v prims.v
for s in $(seq 0 39); do vvp -n tb_c2.vvp +META_SEED=$s +META_VERBOSE=2 > out_s$s.log; done
python3 -I check_c2.py out_s*.log                       # expect: mismatches: 0
vvp -n tb_c2.vvp +META_OFF=1 > off.log; python3 -I check_c2.py off.log | tail -1   # negative control: mismatches > 0
iverilog -g2012 -gspecify -DGLS_FID -DGLS_TRANSPORT_IC -o tb_lost.vvp tb_lost.v prims.v
for s in 0 1 2; do vvp -n tb_lost.vvp +META_SEED=$s +META_VERBOSE=2 | grep -v VCD; done
vvp -n tb_lost.vvp +META_OFF=1
rm -rf "$T"
