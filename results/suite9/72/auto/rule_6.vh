// merge_rules.py: per line the largest proposal of rule_0.20, rule_0.31
// corner_audit.py /tmp/task/runs/ca/su_test_loop_free_4_6/seed1: per-line proposal at corner b0.2_c1_i0.20, guards lo 0.970 hi 1.030, rule-A guard max(0.030*t, 50), slack 0, floor 1; c_lo 179 ps. ONE route: re-route and run the full stack before using it.  [rule_0.20]
// CA_SIZERULE=1 (sizerule1, research/data/sizerule/README.md): c_mlo 312 ps, floor file none  [rule_0.20]
// corner_audit.py /tmp/task/runs/ca/su_test_loop_free_4_6/seed1: per-line proposal at corner b0.31_c1_i0.20, guards lo 0.970 hi 1.030, rule-A guard max(0.030*t, 50), slack 0, floor 1; c_lo 179 ps. ONE route: re-route and run the full stack before using it.  [rule_0.31]
// CA_SIZERULE=1 (sizerule1, research/data/sizerule/README.md): c_mlo 312 ps, floor file none  [rule_0.31]
`define BD_SZ_BRIDGE_I_UDUT_UCMPI0 10   // rule_0.31
`define BD_SZ_BRIDGE_I_UDUT_UADDI1 5   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_USELECT0 11   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UMUX0 3   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UCONTROL_MERGE2 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N1__1 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N1__1_UACK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N11 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N11_UACK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N11_SDELAY 2   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N13 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N13_UACK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N13_SDELAY 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N15 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N15_UACK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N15_SDELAY 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N16 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N16_UACK 2   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N16_SDELAY 2   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N22 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N22_UACK 3   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N22_SDELAY 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N6 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N6_UACK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N6_SDELAY 2   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N7 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N7_UACK 2   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N7_SDELAY 2   // rule_0.31
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N8 0   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N8_UACK 3   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N8_SDELAY 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_11 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_11_UACK 1   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_ULINK_N_INDEX_11_SDELAY 1   // rule_0.20
