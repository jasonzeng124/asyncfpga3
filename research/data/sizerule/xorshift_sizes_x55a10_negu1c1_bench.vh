// NEGATIVE CONTROL (not a candidate): x55a10 with UADDI0 1 and UCMPI1 1 -- the sibling's request no longer covers the adder
// x55a10 = x55a with UCMPI0 6 -> 10 (formal FOR-RESEARCH C41/C42; per-call delay, no per-iteration cost expected)
// xorshift_sizes_T3s50_fr4a_bench.vh x 0.55 (ceil) only /^(?!BD_SZ_BRIDGE_I_UDUT_UADDI0$)/, research/tools/shrink_sizes.py: 16 sizes moved
// fr4a (2026-11-16): fr4 (item 27) + seed 2's own corner_audit proposal (A' join-peer fix, 1-bit links, rule M; fxd_ps nominal + worst), datapath / mux lines only: uxori1 7 -> 5, uxori2 7 -> 5 (A'), umux3 14 -> 9 (A'), ucmpi0 12 -> 10, uaddi0 13 -> 12. Hold-side trims and select links not taken. The collatz item 31 method (one route's proposal, checked on 32).
// fr4 = fr3 + the rule H / I pads corner_audit reported but could not size (research/tools/fifteen/hold_pads.py over
// xf4 seeds 1/4/7/9/10/21, nominal and worst reports; 2026-11-15). Unverified until the farm's fxf5 / fxs5.
// fr2 + umux2 1 -> 2: the rounds mux missed rule A by 3-56 ps on 3 of 31 fxf3 routes (and on fxf2 / fxne routes); its high
// bits are never toggled by the vectors, so under the full-range rule it must hold statically.
// xorshift_sizes_T3s50_fr_bench.vh + the two rule-A shortfalls of the second static check on the xfr routes (2026-11-14):
// umux0 1 -> 2 (xfr_5: A -62 worst / -35 nominal, the counter mux's high bits), merge1 1 -> 2 (xfr_1: A -153 / -121).
// The hold-rule (H/I) pad proposals of that round diverged (UACKs 66-108, uxori1 6125) and are not taken.
// per-cell max over 10 corner_audit proposals (research/tools/fifteen/max_sizes.py), base research/data/xorshift_sizes_T3s50_bench.vh
//   /home/user/runs/ca/pmfr3_1/out/sizes.vh
//   /home/user/runs/ca/pmfr3_1/out_nom/sizes.vh
//   /home/user/runs/ca/pmfr3_3/out/sizes.vh
//   /home/user/runs/ca/pmfr3_3/out_nom/sizes.vh
//   /home/user/runs/ca/pmfr3_4/out/sizes.vh
//   /home/user/runs/ca/pmfr3_4/out_nom/sizes.vh
//   /home/user/runs/ca/pmfr3_5/out/sizes.vh
//   /home/user/runs/ca/pmfr3_5/out_nom/sizes.vh
//   /home/user/runs/ca/pmfr3_6/out/sizes.vh
//   /home/user/runs/ca/pmfr3_6/out_nom/sizes.vh
`define BD_SZ_BRIDGE_I_UDUT_UADDI0 1
`define BD_SZ_BRIDGE_I_UDUT_UCMPI0 10   // x55a 6; formal C41 (2026-11-17): 6 leaves the loop-entry steer ~0 ps at CARRY/F7 1.0
`define BD_SZ_BRIDGE_I_UDUT_UCMPI1 1
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE0 2   // base 3, per route 1/1/1/1/2/1/1/1/2/1
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE1 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N11__1 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N11__1_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N12__0 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N12__0_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N12__1 5
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N12__1_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N12__1_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N12__2 4
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N12__2_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N1__1_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N25_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N30__1 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N30__1_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N6_SDELAY 3   // base 1, per route 4/3/1/1/1/1/1/1/2/1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N6_UACK 1   // hold_pads.py: was 0; 5 rows below 0 (worst H -39)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N7_UACK 1   // hold_pads.py: was 0; 3 rows below 0 (worst H -274)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N8_UACK 1   // hold_pads.py: was 0; 4 rows below 0 (worst H -211)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_1_SDELAY 2   // hold_pads.py: was 0; 5 rows below 0 (worst I -928)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_1_UACK 4   // base 1, per route 1/1/6/5/1/1/2/2/2/2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_9_SDELAY 2   // base 1, per route 1/1/1/1/1/1/1/1/2/2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_9_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_15 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_15_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_15_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_0_SDELAY 1   // hold_pads.py: was 0; 8 rows below 0 (worst I -620)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_0_UACK 3   // base 1, per route 3/3/5/4/1/1/3/3/4/3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_10_SDELAY 4   // base 1, per route 1/1/3/2/4/3/6/5/3/2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_10_UACK 2   // hold_pads.py: was 0; 9 rows below 0 (worst H -301)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_12_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_2_SDELAY 1   // hold_pads.py: was 0; 8 rows below 0 (worst I -598)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_2_UACK 3   // base 1, per route 5/5/2/1/2/2/1/1/3/3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_6_SDELAY 2   // base 1, per route 1/1/2/1/1/1/1/1/1/1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_6_UACK 1   // hold_pads.py: was 0; 2 rows below 0 (worst H -62)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_8_UACK 1   // hold_pads.py: was 0; 7 rows below 0 (worst H -194)
`define BD_SZ_BRIDGE_I_UDUT_UMUX0 2
`define BD_SZ_BRIDGE_I_UDUT_UMUX1 2
`define BD_SZ_BRIDGE_I_UDUT_UMUX2 2
`define BD_SZ_BRIDGE_I_UDUT_UMUX3 5   // fr4 14
`define BD_SZ_BRIDGE_I_UDUT_UXORI1 3   // fr4 7
`define BD_SZ_BRIDGE_I_UDUT_UXORI2 3   // fr4 7
