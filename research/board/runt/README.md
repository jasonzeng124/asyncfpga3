# H_RUNT rig (board list item 2): runt_top, one route

What it asks: does a C-element LUT loop (bd_c2n, one LUT6 with its own feedback) capture, reject, or circulate a
force-high episode shorter than its own loop? (claude/formal formal/FOR-RESEARCH.md section 3: the transport picture
lets the runt go round for ever and lock the circuit; a runt-killing fabric settles it.)

Build: `cd cells && BD_RLOC=none NEXTPNR_FREQ=50 hw/build_hw.sh runt_top` at acf6957f; nextpnr 9c732bc6303458df, every
patch fingerprint ok (toolchain.txt). 4226 LUT, 6489 FF, 26 CARRY4, 2 BUFGCTRL (tck, rclk); the 128 per-instance edge
counters are clocked from fabric (the cell's own q). rclk 101 MHz max vs its ring (31 links).

Files: runt_top.bit (md5 08529a39), instances.tsv (hw/runt_measure.py --table, physical pins from the routed JSON),
predicted.tsv (md5 c5050e61; research/tools/runt_predict.py on runt_top_xray.sdf, band 0.288), the routed JSON, both
SDFs and the FASM (xz). The predictions were committed before any board run.

Prediction (band 0.288): TEST w = t(b) - t(a) at the cell's pins spans -427..+1542 ps (k=0: -427..338, k=1: 18..795,
k=2: 396..1044, k=3: 522..1542); each cell's own loop (a pin -> O6 -> q pin) 211-633 ps. NEG w -3812..-3220, LONG
+2974..+3784, PULSE (feedback cut; the edge counter's floor) -311..+1456, k=3 >= 1183. In the transport picture the
capture edge is at w = loop; prjxray gives every LUT pin the same arc, so pin-to-pin differences (tens of ps) are not in w.

Not done: a full-stack GLS of this rig (what the fid model predicts per cell); the rig's smoke test (cells/hw/runt_tb.v,
iverilog, behavioural) passes and its injected-defect variant fails.

The netlist decoded from runt_top.bit (fasm2net) is EQUIVALENT to runt_top_routed.json (fasm_equiv, 2026-11-08, after
the two nextpnr constant-pin defects were found; bits_vs_routed_equiv.txt).
