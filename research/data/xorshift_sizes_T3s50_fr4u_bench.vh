// fr4u (2026-11-16): fr4 + ULINK_N7F__1_UACK 1 (no macro before: RTL default 6; on item 27's critical cycle, falling, 2.85 ns of 38.6 per two iterations; rule H margin +3763 ps at worst on seed 2, n_need 0) + UCONTROL_MERGE0_OLINK 4 written out (= its RTL default; the stage it feeds is not audited by rule I, so it is not shortened).
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
`define BD_SZ_BRIDGE_I_UDUT_UADDI0 13   // base 6, per route 11/6/8/6/9/6/13/9/10/6
`define BD_SZ_BRIDGE_I_UDUT_UCMPI0 12
`define BD_SZ_BRIDGE_I_UDUT_UCMPI1 9
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE0 2   // base 3, per route 1/1/1/1/2/1/1/1/2/1
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE1 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N11__1 5
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N11__1_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N12__0 5
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N12__0_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N12__1 8
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N12__1_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N12__1_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N12__2 6
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N12__2_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N1__1_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N25_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N30__1 4
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N30__1_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N6_SDELAY 4   // base 1, per route 4/3/1/1/1/1/1/1/2/1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N6_UACK 1   // hold_pads.py: was 0; 5 rows below 0 (worst H -39)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N7_UACK 1   // hold_pads.py: was 0; 3 rows below 0 (worst H -274)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N8_UACK 1   // hold_pads.py: was 0; 4 rows below 0 (worst H -211)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_1_SDELAY 2   // hold_pads.py: was 0; 5 rows below 0 (worst I -928)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_1_UACK 6   // base 1, per route 1/1/6/5/1/1/2/2/2/2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_9_SDELAY 2   // base 1, per route 1/1/1/1/1/1/1/1/2/2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_9_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_15 5
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_15_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_15_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_0_SDELAY 1   // hold_pads.py: was 0; 8 rows below 0 (worst I -620)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_0_UACK 5   // base 1, per route 3/3/5/4/1/1/3/3/4/3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_10_SDELAY 6   // base 1, per route 1/1/3/2/4/3/6/5/3/2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_10_UACK 2   // hold_pads.py: was 0; 9 rows below 0 (worst H -301)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_12_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_2_SDELAY 1   // hold_pads.py: was 0; 8 rows below 0 (worst I -598)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_2_UACK 5   // base 1, per route 5/5/2/1/2/2/1/1/3/3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_6_SDELAY 2   // base 1, per route 1/1/2/1/1/1/1/1/1/1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_6_UACK 1   // hold_pads.py: was 0; 2 rows below 0 (worst H -62)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_8_UACK 1   // hold_pads.py: was 0; 7 rows below 0 (worst H -194)
`define BD_SZ_BRIDGE_I_UDUT_UMUX0 2
`define BD_SZ_BRIDGE_I_UDUT_UMUX1 2
`define BD_SZ_BRIDGE_I_UDUT_UMUX2 2
`define BD_SZ_BRIDGE_I_UDUT_UMUX3 14   // base 1, per route 14/13/11/10/13/12/11/10/12/10
`define BD_SZ_BRIDGE_I_UDUT_UXORI1 7   // base 2, per route 7/6/6/6/7/6/5/5/7/7
`define BD_SZ_BRIDGE_I_UDUT_UXORI2 7   // base 3, per route 7/6/4/3/4/3/3/3/5/4
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N7F__1_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE0_OLINK 4
