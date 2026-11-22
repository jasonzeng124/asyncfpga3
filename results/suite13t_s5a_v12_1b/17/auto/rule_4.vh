// merge_rules.py: per line the largest proposal of rule_0.20, rule_0.31
// corner_audit.py /tmp/task/runs/ca/su_mul_example_1_4/seed1: per-line proposal at corner b0.2_c1_i0.20, guards lo 0.900 hi 1.100, rule-A guard max(0.030*t, 50), slack 0, floor 1; c_lo 179 ps. ONE route: re-route and run the full stack before using it.  [rule_0.20]
// CA_SIZERULE=1 (sizerule1, research/data/sizerule/README.md): c_mlo 329 ps, floor file none  [rule_0.20]
// corner_audit.py /tmp/task/runs/ca/su_mul_example_1_4/seed1: per-line proposal at corner b0.31_c1_i0.20, guards lo 0.900 hi 1.100, rule-A guard max(0.030*t, 50), slack 0, floor 1; c_lo 179 ps. ONE route: re-route and run the full stack before using it.  [rule_0.31]
// CA_SIZERULE=1 (sizerule1, research/data/sizerule/README.md): c_mlo 329 ps, floor file none  [rule_0.31]
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER1_UMEM0_USETUP 9   // rule_0.31
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER1_UMEM0_UCO 9   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER1_UMEM1_USETUP 5   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER1_UMEM1_UCO 12   // rule_0.31
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER1_UHOLD 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UMUX0 2   // rule_0.31
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE0 2   // rule_0.31
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE0_OLINK 2   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE0_OLINK_UACK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE0_RLINK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE0_RLINK_UACK 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UMULI1 32   // rule_0.31
`define BD_SZ_BRIDGE_I_UDUT_UCMPI0 6   // rule_0.31
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N20_FOLINK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N20_FOLINK_UACK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N17__0_FOLINK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N17__0_FOLINK_UACK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N3 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N3_UACK 2   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N7 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N7_UACK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_DATARESULT 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_DATARESULT_UACK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_UACK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_UACK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_SDELAY 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_2 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_TRUERESULT_2_UACK 0   // rule_0.20
