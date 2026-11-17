// collatz64_sizes_T4cdb_h4s3p_bench.vh x 0.7 (ceil), research/tools/shrink_sizes.py: 13 sizes moved
// h4s3p (2026-11-16): collatz64 h4s3 (select links 3/6/3 by rule E) + the per-cell max of corner_audit proposals over 32 routes x 2 corners (farm fc64eq3_p, A' join-peer fix): uselect0 18 -> 12, uaddi0 25 -> 23, acks trimmed. Kept by hand: UMUX2 1 (its rule A row is the traced false path; the proposal pads it to 16) and ULINK_N13_UACK 3 (formal C8 / C9: ulink_n13's enable is the binding race of item 26 and of the bad nc64_7; not trimmed until that is understood).
// per-cell max over 64 corner_audit proposals (both corners) of farm fc64eq3_p (research/tools/fifteen/farm_max_sizes.py), base research/data/collatz64_sizes_T4cdb_h4s3_bench.vh
`define BD_SZ_BRIDGE_I_UDUT_UADDI0 17   // base 25, max over routes 23, min 11
`define BD_SZ_BRIDGE_I_UDUT_UADDI1 9
`define BD_SZ_BRIDGE_I_UDUT_UCMPI0 4
`define BD_SZ_BRIDGE_I_UDUT_UCMPI2 12
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE0 3   // base 6, max over routes 3, min 1
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE1 2   // base 3, max over routes 2, min 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N10__1_UACK 1   // base 5, max over routes 1, min 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N10__2_UACK 1   // base 2, max over routes 1, min 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N10__3_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N11_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N13_UACK 3   // set by hand (--override), base 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__0 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__0_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__1 5
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__1_SDELAY 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__1_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N1__1 7
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N1__1_UACK 2   // base 3, max over routes 2, min 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N21__0 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N28_UACK 1   // base 3, max over routes 1, min 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N30__1 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N30__1_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N7_SDELAY 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N7_UACK 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N8_SDELAY 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N8_UACK 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_3_SDELAY 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_3_UACK 4
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_5_SDELAY 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_5_UACK 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_7_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_9_SDELAY 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_9_UACK 5
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_11 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_11_SDELAY 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_11_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_4_SDELAY 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_4_UACK 1   // base 2, max over routes 1, min 1
`define BD_SZ_BRIDGE_I_UDUT_UMUX0 2
`define BD_SZ_BRIDGE_I_UDUT_UMUX1 4
`define BD_SZ_BRIDGE_I_UDUT_UMUX2 1   // set by hand (--override), base 1
`define BD_SZ_BRIDGE_I_UDUT_USELECT0 9   // base 18, max over routes 12, min 7
