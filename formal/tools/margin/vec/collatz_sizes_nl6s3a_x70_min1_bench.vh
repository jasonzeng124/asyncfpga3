// collatz_sizes_T3cdb_nl6s3a_bench.vh x 0.7 (ceil), research/tools/shrink_sizes.py: 8 sizes moved
// nl6s3a (2026-11-16, EXPLORATORY, one route): nl6s3m with uselect0 16 -> 7 and uaddi0 12 -> 9, corner_audit's proposal on fcsel3m seed 20 after the A' join-peer fix. Not a sized candidate: the 32-route per-cell max (fcsel3m_p) decides.
// collatz_sizes_T3cdb_nl6s3m (2026-11-15): nl6s1m with the select links (ulink_n14__0, ulink_n14__1, ulink_n_index_11 DELAY) at 3: rule E at the muxes was below 0 on 2 of 29 routes at 2 (fcsel2: -114 / -149 ps worst).
// research/data/collatz_sizes_T3cdb_nl3_bench.vh = collatz_sizes_T3cdb_nl2_bench.vh + the rule H / I pads corner_audit reported but could not size (research/tools/fifteen/hold_pads.py over
// the local colsz / colnl reports, nominal and worst; 2026-11-15). Unverified until farm request fcol3.
// collatz_sizes_T3cdb_nl_bench.vh with ucontrol_merge0 / merge1 back to 2: on the farm's 32 routes (fcolsz) the merges at 1 missed
// rule A on 7 of 31 routes (-4 to -140 ps, merge index). Everything else as nl.
// per-cell max over 8 corner_audit proposals (research/tools/fifteen/max_sizes.py), base research/data/collatz_sizes_T3cdb_bench.vh
//   /home/user/runs/ca/colnl_1/out/sizes.vh
//   /home/user/runs/ca/colnl_2/out/sizes.vh
//   /home/user/runs/ca/colnl_3/out/sizes.vh
//   /home/user/runs/ca/colnl_4/out/sizes.vh
//   /home/user/runs/ca/colnl_5/out/sizes.vh
//   /home/user/runs/ca/colnl_6/out/sizes.vh
//   /home/user/runs/ca/colnl_7/out/sizes.vh
//   /home/user/runs/ca/colnl_8/out/sizes.vh
`define BD_SZ_BRIDGE_I_UDUT_UADDI0 1
`define BD_SZ_BRIDGE_I_UDUT_UADDI1 1
`define BD_SZ_BRIDGE_I_UDUT_UCMPI0 6
`define BD_SZ_BRIDGE_I_UDUT_UCMPI2 12
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE0 1
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE1 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N10__1_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N10__2_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N10__3_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N11_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N13_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__0 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__0_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__1 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__1_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__1_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N1__1 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N1__1_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N26_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N28__1_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N7_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N7_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N8_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N8_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_3_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_3_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_5_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_5_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_7_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_9_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_9_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_11 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_11_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_11_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_4_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_4_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_UMUX0 1
`define BD_SZ_BRIDGE_I_UDUT_UMUX1 1
`define BD_SZ_BRIDGE_I_UDUT_UMUX2 1
`define BD_SZ_BRIDGE_I_UDUT_USELECT0 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N10__4_UACK 1
