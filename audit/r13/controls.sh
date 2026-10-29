#!/bin/bash
# auditor r13: commands behind audit/findings/r13.md (re-runnable; big outputs in ~/r13work)
#  1. registered DSP48E1 vs yosys cells_sim: dsp/run_reg.sh, then vvp each ~/r13work/dsp/reg_k.vvp -> dsp/sim_k.log
#     mutation controls (must mismatch): research instance AREG(1)->AREG(2) in tb (mutA);
#     prims.v RSTA clears only A2 (mutR); prims.v PREG CE-over-RST priority (mutP) -> dsp/control_*.log
#  2. routes: mine/build.sh mine | dflt  (probe: cells/verify/fasm/check.sh in a cp of ~/wt-r13, TC=/root/audit-tc)
#     TC=/root/audit-tc python3 cells/gls/fid/bit_control.py ~/r13work/routes/<probe|mine|dflt> dsp_areg --good --work ~/r13work/bc_<x>
#  3. decoder mutant (no-bit state decoded AREG=1 instead of 2): ~/r13work/wtmut fasm2net.py dsp_reg_bits else-branch 2,1 -> 1,1
#     then bit_control on routes/mine -> logs/bcmut_mine_*
#  4. silent default: python3 cells/gls/fid/dsp_latency.py ~/r13work/routes/dflt/dflt_routed.json --work ... -> logs/dsplat.log
echo see comments
