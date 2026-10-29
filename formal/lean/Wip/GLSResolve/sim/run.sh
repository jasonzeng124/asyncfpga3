#!/bin/sh
# iverilog cross-check of Formal/Core/Delay/GLSResolve.lean (notes/A-gls-resolve.md §3).
# Research sources are taken read-only from origin/claude/research into a temp dir.
set -e
HERE="$(cd "$(dirname "$0")" && pwd)"; T="$(mktemp -d)"; cd "$T"
git -C "$HERE" show origin/claude/research:cells/gls/fid_core.vh > fid_core.vh
git -C "$HERE" show origin/claude/research:cells/gls/prims.v > prims.v
cp "$HERE"/tb_c2.v "$HERE"/tb_lost.v "$HERE"/check_c2.py "$HERE"/tb_arb.v "$HERE"/check_arb.py "$HERE"/tb_late.v "$HERE"/check_late.py .
iverilog -g2012 -gspecify -DGLS_FID -DGLS_TRANSPORT_IC -o tb_c2.vvp tb_c2.v prims.v
for s in $(seq 0 39); do vvp -n tb_c2.vvp +META_SEED=$s +META_VERBOSE=2 > out_s$s.log; done
python3 -I check_c2.py out_s*.log                       # expect: mismatches: 0
vvp -n tb_c2.vvp +META_OFF=1 > off.log; python3 -I check_c2.py off.log | tail -1   # negative control: mismatches > 0
iverilog -g2012 -gspecify -DGLS_FID -DGLS_TRANSPORT_IC -o tb_lost.vvp tb_lost.v prims.v
for s in 0 1 2; do vvp -n tb_lost.vvp +META_SEED=$s +META_VERBOSE=2 | grep -v VCD; done
vvp -n tb_lost.vvp +META_OFF=1
# GLSResolve2: the arbiter (GLSResolveGen.arb_near_tie / arb_double_ack / arb_gap_closed)
for W in 130 150 170; do for S in 100 300 500 800; do
  iverilog -g2012 -gspecify -DGLS_FID -DGLS_TRANSPORT_IC -Ptb_arb.W=$W -Ptb_arb.SMIN=$S -o b.vvp tb_arb.v prims.v
  for s in $(seq 0 9); do vvp -n b.vvp +META_SEED=$s +META_VERBOSE=2 > o_${W}_${S}_$s.log; done; done; done
python3 -I check_arb.py o_*.log | tail -1                 # expect: mismatches: 0
vvp -n b.vvp +META_OFF=1 > off_arb.log; python3 -I check_arb.py off_arb.log | tail -1   # negative control: mismatches: 1
# GLSResolve2: the late runt (GLSResolveGen.late_runt)
for W2 in 250 300 350 400; do
  iverilog -g2012 -gspecify -DGLS_FID -DGLS_TRANSPORT_IC -Ptb_late.W2=$W2 -o l.vvp tb_late.v prims.v
  for s in $(seq 0 39); do vvp -n l.vvp +META_SEED=$s +META_VERBOSE=2 > l_${W2}_$s.log; done; done
python3 -I check_late.py l_*.log | tail -1                # expect: mismatches: 0
CHK_L=210 python3 -I check_late.py l_*.log | tail -1      # negative control: mismatches > 0
rm -rf "$T"
