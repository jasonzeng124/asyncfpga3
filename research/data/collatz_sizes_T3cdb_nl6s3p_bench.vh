// nl6s3p (2026-11-16): item 28's nl6s3m + the per-cell max of corner_audit's proposals over 32 routes x 2 corners (farm fcsel3m_p, with the A' join-peer fix): uselect0 16 -> 9, five ack / stage lines trimmed. uaddi0 stays 12 (some route needs it).
// per-cell max over 64 corner_audit proposals (both corners) of farm fcsel3m_p (research/tools/fifteen/farm_max_sizes.py), base research/data/collatz_sizes_T3cdb_nl6s3m_bench.vh
`define BD_SZ_BRIDGE_I_UDUT_UADDI0 12
`define BD_SZ_BRIDGE_I_UDUT_UADDI1 10
`define BD_SZ_BRIDGE_I_UDUT_UCMPI0 8
`define BD_SZ_BRIDGE_I_UDUT_UCMPI2 16
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE0 2
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE1 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N10__1_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N10__2_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N10__3_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N11_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N13_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__0 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__0_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__1 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__1_SDELAY 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__1_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N1__1 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N1__1_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N26_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N28__1_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N7_SDELAY 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N7_UACK 1   // base 3, max over routes 1, min 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N8_SDELAY 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N8_UACK 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_3_SDELAY 2   // base 3, max over routes 2, min 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_3_UACK 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_5_SDELAY 1   // base 2, max over routes 1, min 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_5_UACK 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_7_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_9_SDELAY 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_9_UACK 2   // base 3, max over routes 2, min 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_11 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_11_SDELAY 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_11_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_4_SDELAY 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_4_UACK 2   // base 3, max over routes 2, min 1
`define BD_SZ_BRIDGE_I_UDUT_UMUX0 6
`define BD_SZ_BRIDGE_I_UDUT_UMUX1 5
`define BD_SZ_BRIDGE_I_UDUT_UMUX2 11
`define BD_SZ_BRIDGE_I_UDUT_USELECT0 9   // base 16, max over routes 9, min 5
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N10__4_UACK 0
