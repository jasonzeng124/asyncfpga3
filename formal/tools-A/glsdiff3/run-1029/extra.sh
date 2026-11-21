#!/bin/sh
# extra.sh -- this session's experiments beyond the glsdiff suite (called by run.sh).
H=$(cd "$(dirname "$0")" && pwd); W=$H/work; cd $W
fidv() { { echo '`timescale 1ps/1ps'; echo '`define GLS_FID'; cat $1/fid_core.vh; sed 's/^`include "fid_core.vh"//' $1/prims.v; } > $2; }
fidv $H/src prims_fid.v; fidv $H/patch prims_fidC.v
echo "== E1 CARRY4, 7 live pins, all 8 outputs, random arcs: per-(pin,output) transport"
for P in def fid; do echo "-- $P"; python3 -I $H/py/carry_fit.py prims_$P.v 60; done
echo "== E2 FID_RESOLVE 50% point vs TLOOP and WIN (current rule TLOOP - WIN/2)"
for WIRE in 300 500; do
  python3 -I $H/py/gen_meta.py 200 $WIRE > m$WIRE.v
  iverilog -gspecify -DGLS_TRANSPORT_IC -o m$WIRE.vvp m$WIRE.v prims_fid.v
  iverilog -gspecify -DGLS_TRANSPORT_IC -o mC$WIRE.vvp m$WIRE.v prims_fidC.v
done
echo "-- TLOOP 624 (wire 500), WIN 150: expect 50% near 549"
for s in 450 500 530 549 570 600; do vvp -n m500.vvp +S=$s | grep '^S'; done
echo "-- TLOOP 424, +META_WIN=50: expect 50% near 399"
for s in 340 370 390 399 410 420; do vvp -n m300.vvp +S=$s +META_WIN=50 | grep '^S'; done
echo "== E3 patched centre (patch/fid_core_centre.diff, default META_CENTRE_PM=500): expect 50% near TLOOP/2"
echo "-- TLOOP 424: expect 50% near 212"
for s in 100 150 180 200 212 230 250 280 300 360; do vvp -n mC300.vvp +S=$s | grep '^S'; done
echo "-- TLOOP 624: expect 50% near 312"
for s in 250 290 312 340 380; do vvp -n mC500.vvp +S=$s | grep '^S'; done
echo "-- patched, META_CENTRE_PM=-1 (old rule) at TLOOP 424: must equal the suite's sweep"
for s in 300 349 400; do vvp -n mC300.vvp +S=$s +META_CENTRE_PM=-1 | grep '^S'; done
echo "== E4 what fanout sees while the node resolves (one loop, TLOOP 424, s = 349 near the current centre)"
python3 -I $H/py/gen_meta.py 1 300 | sed 's/^initial begin/always @(q[0]) $display("Q %0d %b", $time, q[0]);\ninitial begin/' > m1.v
iverilog -gspecify -DGLS_TRANSPORT_IC -o m1.vvp m1.v prims_fid.v
for sd in 1 2 3; do echo "-- META_SEED=$sd"; vvp -n m1.vvp +S=349 +META_SEED=$sd +META_VERBOSE=1 | grep -v finish | head -8; done
echo "-- META_X=1, META_SEED=1"; vvp -n m1.vvp +S=349 +META_SEED=1 +META_X=1 +META_VERBOSE=1 | grep -v finish | head -8
echo "-- META_OFF=1 (pure transport loop): first edges"; vvp -n m1.vvp +S=349 +META_OFF=1 | head -8
echo "== E5 research tb_f3_meta (arbiter race, 200 trials) with the patched centre: DT = TLOOP/2 = 212 and the test's own DT = 360"
for dt in 212 360; do
  iverilog -gspecify -DGLS_TRANSPORT_IC -DGLS_FID -I$H/patch -Ptb_f3_meta.DT=$dt -o p_meta.vvp $H/src/fid/f3/tb_f3_meta.v $H/patch/prims.v && vvp -n p_meta.vvp | grep -E "^A\.|FAIL A|PASS"
done
echo "-- unpatched, DT 212 and 360"
for dt in 212 360; do
  iverilog -gspecify -DGLS_TRANSPORT_IC -DGLS_FID -I$H/src -Ptb_f3_meta.DT=$dt -o u_meta.vvp $H/src/fid/f3/tb_f3_meta.v $H/src/prims.v && vvp -n u_meta.vvp | grep -E "^A\.|FAIL A|PASS"
done
echo "== E6 Lean involution orbit (Float, not a proof): s*, emitted edges, resolution law"
python3 -I $H/py/orb_tau.py 424
python3 -I $H/py/orb_tau.py 624 | sed -n 2,3p
echo "== E7 flop/latch X patch (patch/prims_x.diff): tb_seq_x, expect L1-L3 0 and F1 F2 x (Lean LDCE_INIT, FDRE_M/FFQ_SYNC)"
cp $H/patch/prims.v pX_def.v; fidv2() { { echo '`timescale 1ps/1ps'; echo '`define GLS_FID'; cat $H/src/fid_core.vh; sed 's/^`include "fid_core.vh"//' $H/patch/prims.v; } > pX_fid.v; }; fidv2
for P in def fid; do iverilog -gspecify -o sx_$P.vvp $H/../../glsdiff/tb_seq_x.v pX_$P.v && echo "-- patched $P" && vvp -n sx_$P.vvp | grep CASE; done
echo "-- research run_f3.sh on the X-patched prims.v (original fid_core.vh)"
rm -rf glsX; mkdir -p glsX/fid; cp -r $H/src/fid/f3 glsX/fid/; cp $H/patch/prims.v $H/src/fid_core.vh glsX/
mkdir -p f3x; F3_OUT=$W/f3x sh glsX/fid/f3/run_f3.sh 2>&1 | grep -v "^        " | grep -v "^logs in"
echo "-- settled-value lines changed by the X patch in research's own x-laden vectors (fid)"
echo "   kleene_ff: $(diff f3/kleene_ff.fid.out f3x/kleene_ff.fid.out | grep -c '^<') of 3000; kleene_c4 (CARRY4+latch): $(diff f3/kleene_c4.fid.out f3x/kleene_c4.fid.out | grep -c '^<') of 3000"
echo "-- retargeted negative control: mutate the patched fid nsf so x CE loads D"
sed "/function nsf/,/endfunction/s/n0 = c ? dd : q;/n0 = (c !== 1'b0) ? dd : q;/" glsX/prims.v > glsX/prims_mut.v
iverilog -gspecify -DGLS_TRANSPORT_IC -DGLS_FID -IglsX -o km.vvp glsX/fid/f3/tb_f3_kleene_ff.v glsX/prims_mut.v && vvp -n km.vvp | grep -v finish > km.out
echo "   mutated differs from patched default on $(diff f3x/kleene_ff.default.out km.out | grep -c '^<') of 3000 lines (must be > 0)"
rm -rf glsX
