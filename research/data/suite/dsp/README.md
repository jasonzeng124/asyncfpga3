# share_test_2's DSP48E1s: the pre-adder and the B cascade in the decoder and the gate-level model (2026-11-20)

Subagent `dsp` (research bot session cluster-research-29671222-1). share_test_2 was NOT-A-BOARD-ROUTE on every seed:
fasm2net refused DSP48_X0Y27, a combinational DSP48E1 with USE_DPORT=TRUE, INMODE=00100 (the multiplier reads
D + A2), B_INPUT=CASCADE (BCIN from X0Y26's BCOUT) and OPMODE 1010101 (P = (PCIN>>>17) + (D+A)*BCIN): yosys's
xilinx_dsp packed `w_n56 * 0x6f850`'s upper partial-product add into the pre-adder of a cascaded 32-bit multiply.
dsp_table.txt lists all 11 DSPs of the route; only X0Y26 / X0Y27 were outside the model.

## Changed (cells/gls only; cells/rtl untouched)
- dsp_model.py config(): dport / bcasc / bcout -- modelled exactly INMODE=00100 with USE_DPORT=TRUE (AD = D[24:0] +
  A2[24:0], 25 bits, wrapping), BCIN for B, BCOUT = the selected B, combinational only and only in the multiply
  P = Z + M with Z in {0, PCIN, PCIN>>>17}; everything else refused. Semantics from yosys cells_sim.v DSP48E1 (UG479
  itself not reachable from the cluster).
- prims.v DSP48E1_DSP48E1: D, BCIN, BCOUT ports, DPORT / BCASC parameters, their timing paths; GLS_DSP_PREADD_FAULT
  (1 subtract, 2 drop D) for negative controls only.
- gen.py dsp_config() / dsp_ext_conn(): D / BCIN / BCOUT connected only where the routed JSON has them.
- fid/fasm2net.py: D pins traced on a USE_DPORT site, BCIN on a B_INPUT=CASCADE site, a BCOUT output only where a BCIN
  reads it; USE_DPORT / B_INPUT now taken from the bits (they were written FALSE / DIRECT whatever the bits said, and
  config() never saw the USE_DPORT bit). A D pin on a tie-off bit or on an undriven wire is refused.
- fid/xray_delay.py dsp(): a pre-adder cell gets prjxray's USE_DPORT_TRUE timing (it had the non-pre-adder A -> P arc,
  3841 ps at SLOW_MAX, where the pre-adder path is 5201 ps: a delay that was TOO SHORT).
- fid/fasm_equiv.py compares the D / BCIN pins' drivers.
- tb_dsp_dport.v: a hand-check testbench (3007 vectors, 1658 wrapping the pre-adder): 0 differences against UG479's
  formulas and against yosys's own DSP48E1.

## Measured (nextpnr 6e5d224472232d5d; the route: suite12 share_test_2 seed 1 it 6, rebuilt here as st2_6)
- Unchanged elsewhere: the bits stack (xray_delay, fasm2net --bit, fasm_equiv, gen.py) at HEAD and patched on
  pk_gather_1_5, pk_gather_1_6 (3 DSPs each) and pk_xorshift_1_5 (none): all 18 outputs byte-identical
  (regress_compare.log). On st2_6 only X0Y27's A -> P and D -> P arcs change in the SDF.
- st2_6: fasm_equiv **EQUIVALENT** (st2_6_equiv.txt), full stack P = 99.39 ns, ffmux-clean; draws 10101-10104 (as
  suite_one.sh judges seed 1; expected values from oracle_mem.sh, compiled from the C): **PASS 3 / 3 calls each**
  (draws/), every array word read back right, no runts; 10101 with GATE_ANNOTATE=1: ANNOTATE_DONE, 0 SDF warnings.
- Negative controls: the pre-adder made to subtract in a copy of the model: draw 10101 **FAIL 0 / 3** (99 of 100 words
  wrong per call; negsub/); unit check: subtract / drop-D fail 3005 / 3006 of 3007 vectors. Eight mutated copies of
  the route's FASM (pre-adder subtract, ADREG=1, a B register on either cascaded cell, D on a tie-off bit, a D route
  cut, ALUMODE 0100, BCIN undriven): all eight REFUSED by fasm2net with the right reason (mutations_summary.txt).

## Does NOT show
- The D-route assumption: a D pin with no DSP_GND / DSP_VCC tie-off bit set reads its one interconnect wire through
  a connection prjxray has no bit for (prjxray's tile data lists it; its fuzzer drove 10 % of D pins from logic with
  no unexplained per-pin enable bit; nextpnr assumes the same). No bitstream with a routed D pin has run on the board:
  a D-port bit-walk on one DSP would settle it (BOARD-QUEUE candidate).
- The pre-adder's semantics are yosys's model, not silicon; one route, 4 draws, no min / max corners; BCIN carries a
  constant here, so the B cascade's timing is not exercised; iverilog settles a DSP output on its last-changing input's
  arc (true of every cascade already); how the static sizing rule treats D -> P was not examined.
