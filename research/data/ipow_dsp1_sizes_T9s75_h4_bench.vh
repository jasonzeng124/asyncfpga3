// research/data/ipow_dsp1_sizes_T9s75_h_bench.vh = ipow_dsp1_sizes_T9s75_bench.vh + the rule H / I pads corner_audit reported but could not size (research/tools/fifteen/hold_pads.py over
// the 3 local ipowr routes, nominal and worst; 2026-11-15). Unverified until farm request fipowh.
// ipow_dsp1_sizes_T9s75.vh re-keyed for the bench_gen top (BD_SZ_UUT_ -> BD_SZ_BRIDGE_I_UDUT_, soak-harness BD_SZ_UPIPE_* dropped)
// ipow_dsp1_sizes_T9.vh x 0.75 (ceil), research/tools/shrink_sizes.py: 18 sizes moved
// ipow T8 + 1 link on every compute cell (rule A long tail; seed 24 ushrsi0 ask) 
`define BD_SZ_BRIDGE_I_UDUT_UCMPI0 11
`define BD_SZ_BRIDGE_I_UDUT_UCMPI2 18
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE0 7
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE1 6
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N10__0_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N10__1_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N10__2_SDELAY 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N10__2_UACK 3   // hold_pads_eval.py fipowh: was 2; 1 rows below 0 (worst -5 task 25 worst)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N12__1_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N13_SDELAY 4
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N13_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N15_UACK 1   // hold_pads_eval.py fipowh: was 0; 2 rows below 0 (worst -182 task 14 nom)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N17__0 15
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N17__0_SDELAY 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N17__0_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N17__1 8
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N17__1_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N17__2 23
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N17__2_SDELAY 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N17__2_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N1__1 6
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N1__1_UACK 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N31__1_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N7_SDELAY 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N7_UACK 2   // hold_pads.py: was 0; 2 rows below 0 (worst H -487)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N8_SDELAY 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N8_UACK 4   // hold_pads_eval.py fipowh3: was 3; 2 rows below 0 (worst -194 task 2 worst)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_11_SDELAY 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_FALSERESULT_11_UACK 4   // hold_pads_eval.py fipowh: was 1; 2 rows below 0 (worst -620 task 13 worst)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_15 9
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_15_SDELAY 3
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_15_UACK 0
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_0_SDELAY 2   // hold_pads_eval.py fipowh: was 1; 3 rows below 0 (worst -148 task 13 worst)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_0_UACK 3   // hold_pads_eval.py fipowh2: was 2; 1 rows below 0 (worst -29 task 1 worst)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_10_SDELAY 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_10_UACK 2   // hold_pads.py: was 0; 2 rows below 0 (worst H -431)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_12_SDELAY 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_6_SDELAY 2
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_6_UACK 2   // hold_pads.py: was 0; 2 rows below 0 (worst H -382)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_8_SDELAY 2   // hold_pads_eval.py fipowh2: was 1; 2 rows below 0 (worst -41 task 16 worst)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_8_UACK 2   // hold_pads_eval.py fipowh: was 1; 1 rows below 0 (worst -17 task 24 worst)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_SDELAY 2   // hold_pads_eval.py fipowh: was 1; 4 rows below 0 (worst -90 task 5 worst)
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_UACK 2
`define BD_SZ_BRIDGE_I_UDUT_UMULI1 36
`define BD_SZ_BRIDGE_I_UDUT_UMUX0 8
`define BD_SZ_BRIDGE_I_UDUT_UMUX1 9
`define BD_SZ_BRIDGE_I_UDUT_UMUX2 2
`define BD_SZ_BRIDGE_I_UDUT_UMUX3 3
`define BD_SZ_BRIDGE_I_UDUT_USELECT0 39
`define BD_SZ_BRIDGE_I_UDUT_USHRSI0 23
