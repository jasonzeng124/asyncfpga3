// collatz_sizes_T3cd.vh re-keyed for the bench_gen top (BD_SZ_UUT_ -> BD_SZ_BRIDGE_I_UDUT_, soak-harness BD_SZ_UPIPE_* dropped); build with BDC_CONST_DATA=1
// per-cell max of 4 corner_audit.py proposals over collatz_sizes_T3.vh: /tmp/claude-0/-home-user-asyncfpga3/5430fd50-f33d-52a5-8a52-f19d5b6000df/scratchpad/cs/collatz_cd__seed1__b0.288_c1_i0.21/sizes.vh /tmp/claude-0/-home-user-asyncfpga3/5430fd50-f33d-52a5-8a52-f19d5b6000df/scratchpad/cs/collatz_cd__seed2__b0.288_c1_i0.21/sizes.vh /tmp/claude-0/-home-user-asyncfpga3/5430fd50-f33d-52a5-8a52-f19d5b6000df/scratchpad/cs/collatz_cd__seed3__b0.288_c1_i0.21/sizes.vh /tmp/claude-0/-home-user-asyncfpga3/5430fd50-f33d-52a5-8a52-f19d5b6000df/scratchpad/cs/collatz_cd__seed4__b0.288_c1_i0.21/sizes.vh
`define BD_SZ_BRIDGE_I_UDUT_UADDI0 18   // was 29
`define BD_SZ_BRIDGE_I_UDUT_UADDI1 10   // was 13
`define BD_SZ_BRIDGE_I_UDUT_UCMPI0 8   // was 12
`define BD_SZ_BRIDGE_I_UDUT_UCMPI2 16   // was 19
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE0 5   // was 11
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE1 9
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N10__1_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N10__2_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N10__3_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N11_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N13_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__0 13   // was 18
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__0_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__1 18   // was 36
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__1_SDELAY 1   // was 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__1_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N1__1 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N1__1_UACK 2   // was 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N26_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N28__1_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N7_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N7_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N8_SDELAY 1   // was 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N8_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_3_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_3_UACK 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_5_SDELAY 1   // was 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_5_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_7_SDELAY 1   // was 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_9_SDELAY 1   // was 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_9_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_11 12   // was 15
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_11_SDELAY 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_11_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_4_SDELAY 1   // was 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_4_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_UMUX0 1   // was 6
`define BD_SZ_BRIDGE_I_UDUT_UMUX1 5
`define BD_SZ_BRIDGE_I_UDUT_UMUX2 1   // was 2
`define BD_SZ_BRIDGE_I_UDUT_USELECT0 23   // was 31
