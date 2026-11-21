// merge_rules.py: per line the largest proposal of rule_0.20, rule_0.31
// corner_audit.py /tmp/task/runs/ca/su_unused_arg_4_1/seed1: per-line proposal at corner b0.2_c1_i0.20, guards lo 0.970 hi 1.030, rule-A guard max(0.030*t, 50), slack 0, floor 1; c_lo 194 ps. ONE route: re-route and run the full stack before using it.  [rule_0.20]
// CA_SIZERULE=1 (sizerule1, research/data/sizerule/README.md): c_mlo 382 ps, floor file none  [rule_0.20]
// corner_audit.py /tmp/task/runs/ca/su_unused_arg_4_1/seed1: per-line proposal at corner b0.31_c1_i0.20, guards lo 0.970 hi 1.030, rule-A guard max(0.030*t, 50), slack 0, floor 1; c_lo 194 ps. ONE route: re-route and run the full stack before using it.  [rule_0.31]
// CA_SIZERULE=1 (sizerule1, research/data/sizerule/README.md): c_mlo 382 ps, floor file none  [rule_0.31]
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER1_UMEM0_USETUP 5   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER1_UMEM0_UCO 10   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER1_UMEM1_USETUP 5   // rule_0.20
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER1_UMEM1_UCO 10   // rule_0.31
`define BD_SZ_BRIDGE_I_UDUT_UMEM_CONTROLLER1_UHOLD 0   // rule_0.20
