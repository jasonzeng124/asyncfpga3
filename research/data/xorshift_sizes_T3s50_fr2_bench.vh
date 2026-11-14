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
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N6_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N7_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N8_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_1_SDELAY 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_1_UACK 6   // base 1, per route 1/1/6/5/1/1/2/2/2/2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_9_SDELAY 2   // base 1, per route 1/1/1/1/1/1/1/1/2/2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_9_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_15 5
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_15_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_15_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_0_SDELAY 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_0_UACK 5   // base 1, per route 3/3/5/4/1/1/3/3/4/3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_10_SDELAY 6   // base 1, per route 1/1/3/2/4/3/6/5/3/2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_10_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_12_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_2_SDELAY 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_2_UACK 5   // base 1, per route 5/5/2/1/2/2/1/1/3/3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_6_SDELAY 2   // base 1, per route 1/1/2/1/1/1/1/1/1/1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_6_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_8_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_UMUX0 2
`define BD_SZ_BRIDGE_I_UDUT_UMUX1 2
`define BD_SZ_BRIDGE_I_UDUT_UMUX2 1
`define BD_SZ_BRIDGE_I_UDUT_UMUX3 14   // base 1, per route 14/13/11/10/13/12/11/10/12/10
`define BD_SZ_BRIDGE_I_UDUT_UXORI1 7   // base 2, per route 7/6/6/6/7/6/5/5/7/7
`define BD_SZ_BRIDGE_I_UDUT_UXORI2 7   // base 3, per route 7/6/4/3/4/3/3/3/5/4
