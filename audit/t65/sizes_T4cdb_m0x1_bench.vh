// collatz64_sizes_T4cdb.vh re-keyed for the bench_gen top (BD_SZ_UUT_ -> BD_SZ_BRIDGE_I_UDUT_, soak-harness BD_SZ_UPIPE_* dropped); build with BDC_CONST_DATA=1
// collatz64_sizes_T4cd.vh with every mux delay and every linked SELECT channel's DELAY/SDELAY kept at max(candidate, collatz64_sizes_T4.vh) (select links per bdc emit.select_channels: ulink_n14__0, ulink_n14__1, ulink_n_index_11); collatz64 seed 7 failed with umux1's select link shortened (JOURNAL 2026-11-11)
// per-cell max of 4 corner_audit.py proposals on BDC_CONST_DATA=1 routes (seeds 1-4) over collatz64_sizes_T4.vh, with every UMUX* line kept at T4 (the ipow umux3 select race: JOURNAL 2026-11-09); build with BDC_CONST_DATA=1
// per-cell max of 4 corner_audit.py proposals over collatz64_sizes_T4.vh: /tmp/claude-0/-home-user-asyncfpga3/5430fd50-f33d-52a5-8a52-f19d5b6000df/scratchpad/cs/collatz64_cd__seed1__b0.288_c1_i0.21/sizes.vh /tmp/claude-0/-home-user-asyncfpga3/5430fd50-f33d-52a5-8a52-f19d5b6000df/scratchpad/cs/collatz64_cd__seed2__b0.288_c1_i0.21/sizes.vh /tmp/claude-0/-home-user-asyncfpga3/5430fd50-f33d-52a5-8a52-f19d5b6000df/scratchpad/cs/collatz64_cd__seed3__b0.288_c1_i0.21/sizes.vh /tmp/claude-0/-home-user-asyncfpga3/5430fd50-f33d-52a5-8a52-f19d5b6000df/scratchpad/cs/collatz64_cd__seed4__b0.288_c1_i0.21/sizes.vh
`define BD_SZ_BRIDGE_I_UDUT_UADDI0 25   // was 37
`define BD_SZ_BRIDGE_I_UDUT_UADDI1 12
`define BD_SZ_BRIDGE_I_UDUT_UCMPI0 5   // was 11
`define BD_SZ_BRIDGE_I_UDUT_UCMPI2 14   // was 23
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE0 1
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE1 3   // was 5
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N10__1_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N10__2_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N10__3_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N11_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N13_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__0 15   // kept at base (candidate had 11)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__0_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__1 19   // kept at base (candidate had 10)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__1_SDELAY 2   // kept at base (candidate had 1)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N14__1_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N1__1 10
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N1__1_UACK 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N21__0 1   // was 12
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N28_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N30__1 4
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N30__1_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N7_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N7_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N8_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N8_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_3_SDELAY 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_3_UACK 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_5_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_5_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_7_SDELAY 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_9_SDELAY 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_9_UACK 1
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_11 14   // kept at base (candidate had 9)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_11_SDELAY 4   // kept at base (candidate had 1)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_11_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_4_SDELAY 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_4_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_UMUX0 1
`define BD_SZ_BRIDGE_I_UDUT_UMUX1 5   // kept at T4 (corner_audit proposed 1)
`define BD_SZ_BRIDGE_I_UDUT_UMUX2 1
`define BD_SZ_BRIDGE_I_UDUT_USELECT0 18   // was 26
