// merge_rules.py: per line the largest proposal of rule_0.20, rule_0.31
// corner_audit.py /tmp/task/runs/ca/su_single_loop_1_1/seed1: per-line proposal at corner b0.2_c1_i0.20, guards lo 0.970 hi 1.030, rule-A guard max(0.030*t, 50), slack 0, floor 1; c_lo 179 ps. ONE route: re-route and run the full stack before using it.  [rule_0.20]
// CA_SIZERULE=1 (sizerule1, research/data/sizerule/README.md): c_mlo 335 ps, floor file none  [rule_0.20]
// corner_audit.py /tmp/task/runs/ca/su_single_loop_1_1/seed1: per-line proposal at corner b0.31_c1_i0.20, guards lo 0.970 hi 1.030, rule-A guard max(0.030*t, 50), slack 0, floor 1; c_lo 179 ps. ONE route: re-route and run the full stack before using it.  [rule_0.31]
// CA_SIZERULE=1 (sizerule1, research/data/sizerule/README.md): c_mlo 335 ps, floor file none  [rule_0.31]
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER3_UMEM0_USETUP 3   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER3_UMEM0_UCO 8   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER3_UMEM1_USETUP 4   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER3_UMEM1_UCO 10   // rule_0.31
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER3_UHOLD 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER4_UMEM0_USETUP 8   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER4_UMEM0_UCO 8   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER4_UMEM1_USETUP 7   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER4_UMEM1_UCO 9   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER4_UHOLD 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER5_UMEM0_USETUP 4   // rule_0.31
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER5_UMEM0_UCO 9   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER5_UMEM1_USETUP 7   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER5_UMEM1_UCO 11   // rule_0.31
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER5_UHOLD 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UMUX0 2   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE0 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE0_OLINK 2   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE0_OLINK_UACK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE0_RLINK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE0_RLINK_UACK 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UCMPI0 27   // rule_0.31
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N18_FOLINK 3   // rule_0.31
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N18_FOLINK_UACK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N17__0_FOLINK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N17__0_FOLINK_UACK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UADDI0 6   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N3 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N3_UACK 2   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N6__3 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N6__3_UACK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_DATARESULT 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_DATARESULT_UACK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_DATARESULT_4 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_DATARESULT_4_UACK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_UACK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_UACK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_SDELAY 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_7 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_7_UACK 0   // rule_0.20
