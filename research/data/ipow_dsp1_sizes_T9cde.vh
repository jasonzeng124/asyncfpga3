// ipow_dsp1_sizes_T9cdd.vh with every mux delay and every linked SELECT channel's DELAY/SDELAY kept at max(candidate, ipow_dsp1_sizes_T9.vh) (select links per bdc emit.select_channels: ulink_n17__0, ulink_n17__1, ulink_n17__2, ulink_n_index_15); collatz64 seed 7 failed with umux1's select link shortened (JOURNAL 2026-11-11)
// ipow_dsp1_sizes_T9cd.vh with UMUX3 restored to 4 (T9)
// per-cell max of 4 corner_audit.py proposals over ipow_dsp1_sizes_T9.vh: /tmp/claude-0/-home-user-asyncfpga3/5430fd50-f33d-52a5-8a52-f19d5b6000df/scratchpad/cs/ipow_cd__seed29__b0.288_c1_i0.21/sizes.vh /tmp/claude-0/-home-user-asyncfpga3/5430fd50-f33d-52a5-8a52-f19d5b6000df/scratchpad/cs/ipow_cd__seed30__b0.288_c1_i0.21/sizes.vh /tmp/claude-0/-home-user-asyncfpga3/5430fd50-f33d-52a5-8a52-f19d5b6000df/scratchpad/cs/ipow_cd__seed31__b0.288_c1_i0.21/sizes.vh /tmp/claude-0/-home-user-asyncfpga3/5430fd50-f33d-52a5-8a52-f19d5b6000df/scratchpad/cs/ipow_cd__seed32__b0.288_c1_i0.21/sizes.vh
`define BD_SZ_UPIPE_SDELAY 2
`define BD_SZ_UPIPE_UACK 0
`define BD_SZ_UUT_UCMPI0 9   // was 14
`define BD_SZ_UUT_UCMPI2 23
`define BD_SZ_UUT_UCONTROL_MERGE0 9
`define BD_SZ_UUT_UCONTROL_MERGE1 6   // was 8
`define BD_SZ_UUT_ULINK_N10__0_UACK 0
`define BD_SZ_UUT_ULINK_N10__1_UACK 0
`define BD_SZ_UUT_ULINK_N10__2_SDELAY 1   // was 2
`define BD_SZ_UUT_ULINK_N10__2_UACK 0
`define BD_SZ_UUT_ULINK_N12__1_UACK 0
`define BD_SZ_UUT_ULINK_N13_SDELAY 1   // was 5
`define BD_SZ_UUT_ULINK_N13_UACK 0
`define BD_SZ_UUT_ULINK_N15_UACK 0
`define BD_SZ_UUT_ULINK_N17__0 20   // kept at base (candidate had 12)
`define BD_SZ_UUT_ULINK_N17__0_SDELAY 4   // kept at base (candidate had 1)
`define BD_SZ_UUT_ULINK_N17__0_UACK 0
`define BD_SZ_UUT_ULINK_N17__1 10   // kept at base (candidate had 7)
`define BD_SZ_UUT_ULINK_N17__1_UACK 0
`define BD_SZ_UUT_ULINK_N17__2 30   // kept at base (candidate had 20)
`define BD_SZ_UUT_ULINK_N17__2_SDELAY 3   // kept at base (candidate had 1)
`define BD_SZ_UUT_ULINK_N17__2_UACK 0
`define BD_SZ_UUT_ULINK_N1__1 7
`define BD_SZ_UUT_ULINK_N1__1_UACK 1   // was 2
`define BD_SZ_UUT_ULINK_N31__1_UACK 0
`define BD_SZ_UUT_ULINK_N7_SDELAY 1   // was 2
`define BD_SZ_UUT_ULINK_N7_UACK 0
`define BD_SZ_UUT_ULINK_N8_SDELAY 1   // was 2
`define BD_SZ_UUT_ULINK_N8_UACK 0
`define BD_SZ_UUT_ULINK_N_FALSERESULT_11_SDELAY 1   // was 3
`define BD_SZ_UUT_ULINK_N_FALSERESULT_11_UACK 0
`define BD_SZ_UUT_ULINK_N_INDEX_15 12   // kept at base (candidate had 9)
`define BD_SZ_UUT_ULINK_N_INDEX_15_SDELAY 4
`define BD_SZ_UUT_ULINK_N_INDEX_15_UACK 0
`define BD_SZ_UUT_ULINK_N_TRUERESULT_0_SDELAY 1
`define BD_SZ_UUT_ULINK_N_TRUERESULT_0_UACK 2
`define BD_SZ_UUT_ULINK_N_TRUERESULT_10_SDELAY 1   // was 2
`define BD_SZ_UUT_ULINK_N_TRUERESULT_10_UACK 0
`define BD_SZ_UUT_ULINK_N_TRUERESULT_12_SDELAY 1   // was 2
`define BD_SZ_UUT_ULINK_N_TRUERESULT_6_SDELAY 1   // was 2
`define BD_SZ_UUT_ULINK_N_TRUERESULT_6_UACK 0
`define BD_SZ_UUT_ULINK_N_TRUERESULT_8_SDELAY 1
`define BD_SZ_UUT_ULINK_N_TRUERESULT_8_UACK 1
`define BD_SZ_UUT_ULINK_N_TRUERESULT_SDELAY 1
`define BD_SZ_UUT_ULINK_N_TRUERESULT_UACK 2
`define BD_SZ_UUT_UMULI1 36   // was 47
`define BD_SZ_UUT_UMUX0 10   // kept at base (candidate had 1)
`define BD_SZ_UUT_UMUX1 11   // kept at base (candidate had 6)
`define BD_SZ_UUT_UMUX2 3   // candidate's (longer than base 2)
`define BD_SZ_UUT_UMUX3 4   // kept at T9: 1 fails once the select precedes the data (umux3 select race; see journal)
`define BD_SZ_UUT_USELECT0 51   // was 52
`define BD_SZ_UUT_USHRSI0 1   // was 30
