import Formal.Timing.ChainSettleExeGcdDData0

/-! C-10o2 GENERATED: kernel-decided verdicts of chunk 0 (see ChainSettleExe.verdict).
Per row: `verdict` at chainck's late side `T`; exact PASS at `T*` and FAIL at `T* - 1`
(margin_exact = T - T*); bridge PASS at `Tb*` and FAIL at `Tb* - 1`. -/

namespace Formal.Timing.ChainSettleExe.GcdD
open Formal.Timing Formal.Timing.ChainSettleExe

theorem v0 :
    verdict r0 = ⟨true, true, 1, 913, 17582, 11505, true, true, true⟩ ∧
    (verdict { r0 with T := 953 }).exact = true ∧
    (verdict { r0 with T := 952 }).exact = false ∧
    (verdict { r0 with T := 985 }).bridge = true ∧
    (verdict { r0 with T := 984 }).bridge = false := by decide +kernel
theorem v1 :
    verdict r1 = ⟨true, true, 1, 1056, 13529, 8846, true, true, true⟩ ∧
    (verdict { r1 with T := 1455 }).exact = true ∧
    (verdict { r1 with T := 1454 }).exact = false ∧
    (verdict { r1 with T := 1455 }).bridge = true ∧
    (verdict { r1 with T := 1454 }).bridge = false := by decide +kernel
theorem v2 :
    verdict r2 = ⟨true, true, 1, 828, 9615, 6125, true, true, true⟩ ∧
    (verdict { r2 with T := 823 }).exact = true ∧
    (verdict { r2 with T := 822 }).exact = false ∧
    (verdict { r2 with T := 878 }).bridge = true ∧
    (verdict { r2 with T := 877 }).bridge = false := by decide +kernel
theorem v3 :
    verdict r3 = ⟨true, true, 1, 1665, 21879, 14421, true, true, true⟩ ∧
    (verdict { r3 with T := 2068 }).exact = true ∧
    (verdict { r3 with T := 2067 }).exact = false ∧
    (verdict { r3 with T := 2068 }).bridge = true ∧
    (verdict { r3 with T := 2067 }).bridge = false := by decide +kernel
theorem v4 :
    verdict r4 = ⟨true, true, 1, 957, 7392, 4704, true, true, true⟩ ∧
    (verdict { r4 with T := 1170 }).exact = true ∧
    (verdict { r4 with T := 1169 }).exact = false ∧
    (verdict { r4 with T := 1170 }).bridge = true ∧
    (verdict { r4 with T := 1169 }).bridge = false := by decide +kernel
theorem v5 :
    verdict r5 = ⟨true, true, 1, 1924, 16879, 11122, true, true, true⟩ ∧
    (verdict { r5 with T := 2880 }).exact = true ∧
    (verdict { r5 with T := 2879 }).exact = false ∧
    (verdict { r5 with T := 2880 }).bridge = true ∧
    (verdict { r5 with T := 2879 }).bridge = false := by decide +kernel
theorem v6 :
    verdict r6 = ⟨true, true, 1, 777, 18720, 14538, true, true, true⟩ ∧
    (verdict { r6 with T := 1111 }).exact = true ∧
    (verdict { r6 with T := 1110 }).exact = false ∧
    (verdict { r6 with T := 1111 }).bridge = true ∧
    (verdict { r6 with T := 1110 }).bridge = false := by decide +kernel
theorem v7 :
    verdict r7 = ⟨true, true, 1, 899, 14401, 11180, true, true, true⟩ ∧
    (verdict { r7 with T := 1559 }).exact = true ∧
    (verdict { r7 with T := 1558 }).exact = false ∧
    (verdict { r7 with T := 1559 }).bridge = true ∧
    (verdict { r7 with T := 1558 }).bridge = false := by decide +kernel
theorem v8 :
    verdict r8 = ⟨true, true, 1, 553, 9744, 7567, true, true, true⟩ ∧
    (verdict { r8 with T := 831 }).exact = true ∧
    (verdict { r8 with T := 830 }).exact = false ∧
    (verdict { r8 with T := 841 }).bridge = true ∧
    (verdict { r8 with T := 840 }).bridge = false := by decide +kernel
theorem v9 :
    verdict r9 = ⟨true, true, 1, 1080, 22656, 17936, true, true, true⟩ ∧
    (verdict { r9 with T := 2256 }).exact = true ∧
    (verdict { r9 with T := 2255 }).exact = false ∧
    (verdict { r9 with T := 2256 }).bridge = true ∧
    (verdict { r9 with T := 2255 }).bridge = false := by decide +kernel
theorem v10 :
    verdict r10 = ⟨true, true, 1, 639, 7488, 5812, true, true, true⟩ ∧
    (verdict { r10 with T := 1187 }).exact = true ∧
    (verdict { r10 with T := 1186 }).exact = false ∧
    (verdict { r10 with T := 1187 }).bridge = true ∧
    (verdict { r10 with T := 1186 }).bridge = false := by decide +kernel
theorem v11 :
    verdict r11 = ⟨true, true, 1, 1248, 17476, 13834, true, true, true⟩ ∧
    (verdict { r11 with T := 2992 }).exact = true ∧
    (verdict { r11 with T := 2991 }).exact = false ∧
    (verdict { r11 with T := 2992 }).bridge = true ∧
    (verdict { r11 with T := 2991 }).bridge = false := by decide +kernel
theorem v12 :
    verdict r12 = ⟨true, true, 1, 1345, 20631, 15320, true, true, true⟩ ∧
    (verdict { r12 with T := 1280 }).exact = true ∧
    (verdict { r12 with T := 1279 }).exact = false ∧
    (verdict { r12 with T := 1403 }).bridge = true ∧
    (verdict { r12 with T := 1402 }).bridge = false := by decide +kernel
theorem v13 :
    verdict r13 = ⟨true, true, 1, 1555, 15876, 11784, true, true, true⟩ ∧
    (verdict { r13 with T := 1907 }).exact = true ∧
    (verdict { r13 with T := 1906 }).exact = false ∧
    (verdict { r13 with T := 1907 }).bridge = true ∧
    (verdict { r13 with T := 1906 }).bridge = false := by decide +kernel
theorem v14 :
    verdict r14 = ⟨true, true, 1, 1117, 12137, 8682, true, true, true⟩ ∧
    (verdict { r14 with T := 1123 }).exact = true ∧
    (verdict { r14 with T := 1122 }).exact = false ∧
    (verdict { r14 with T := 1204 }).bridge = true ∧
    (verdict { r14 with T := 1203 }).bridge = false := by decide +kernel
theorem v15 :
    verdict r15 = ⟨true, true, 1, 2118, 26934, 20153, true, true, true⟩ ∧
    (verdict { r15 with T := 2218 }).exact = true ∧
    (verdict { r15 with T := 2217 }).exact = false ∧
    (verdict { r15 with T := 2290 }).bridge = true ∧
    (verdict { r15 with T := 2289 }).bridge = false := by decide +kernel
theorem v16 :
    verdict r16 = ⟨true, true, 1, 1290, 9334, 6673, true, true, true⟩ ∧
    (verdict { r16 with T := 1393 }).exact = true ∧
    (verdict { r16 with T := 1392 }).exact = false ∧
    (verdict { r16 with T := 1393 }).bridge = true ∧
    (verdict { r16 with T := 1392 }).bridge = false := by decide +kernel
theorem v17 :
    verdict r17 = ⟨true, true, 1, 2447, 20782, 15549, true, true, true⟩ ∧
    (verdict { r17 with T := 3227 }).exact = true ∧
    (verdict { r17 with T := 3226 }).exact = false ∧
    (verdict { r17 with T := 3227 }).bridge = true ∧
    (verdict { r17 with T := 3226 }).bridge = false := by decide +kernel
theorem v18 :
    verdict r18 = ⟨true, true, 1, 1721, 20297, 15280, true, true, true⟩ ∧
    (verdict { r18 with T := 1878 }).exact = true ∧
    (verdict { r18 with T := 1877 }).exact = false ∧
    (verdict { r18 with T := 2001 }).bridge = true ∧
    (verdict { r18 with T := 2000 }).bridge = false := by decide +kernel
theorem v19 :
    verdict r19 = ⟨true, true, 1, 1989, 15619, 11753, true, true, true⟩ ∧
    (verdict { r19 with T := 2169 }).exact = true ∧
    (verdict { r19 with T := 2168 }).exact = false ∧
    (verdict { r19 with T := 2312 }).bridge = true ∧
    (verdict { r19 with T := 2311 }).bridge = false := by decide +kernel
theorem v20 :
    verdict r20 = ⟨true, true, 1, 1374, 11282, 8229, true, true, true⟩ ∧
    (verdict { r20 with T := 1487 }).exact = true ∧
    (verdict { r20 with T := 1486 }).exact = false ∧
    (verdict { r20 with T := 1543 }).bridge = true ∧
    (verdict { r20 with T := 1542 }).bridge = false := by decide +kernel
theorem v21 :
    verdict r21 = ⟨true, true, 1, 2666, 25336, 19077, true, true, true⟩ ∧
    (verdict { r21 with T := 2858 }).exact = true ∧
    (verdict { r21 with T := 2857 }).exact = false ∧
    (verdict { r21 with T := 2983 }).bridge = true ∧
    (verdict { r21 with T := 2982 }).bridge = false := by decide +kernel
theorem v22 :
    verdict r22 = ⟨true, true, 1, 1587, 8675, 6323, true, true, true⟩ ∧
    (verdict { r22 with T := 1717 }).exact = true ∧
    (verdict { r22 with T := 1716 }).exact = false ∧
    (verdict { r22 with T := 1782 }).bridge = true ∧
    (verdict { r22 with T := 1781 }).bridge = false := by decide +kernel
theorem v23 :
    verdict r23 = ⟨true, true, 1, 3080, 19546, 14716, true, true, true⟩ ∧
    (verdict { r23 with T := 3393 }).exact = true ∧
    (verdict { r23 with T := 3392 }).exact = false ∧
    (verdict { r23 with T := 3446 }).bridge = true ∧
    (verdict { r23 with T := 3445 }).bridge = false := by decide +kernel
theorem v24 :
    verdict r24 = ⟨true, true, 1, 1187, 24732, 18868, true, true, true⟩ ∧
    (verdict { r24 with T := 1111 }).exact = true ∧
    (verdict { r24 with T := 1110 }).exact = false ∧
    (verdict { r24 with T := 1187 }).bridge = true ∧
    (verdict { r24 with T := 1186 }).bridge = false := by decide +kernel
theorem v25 :
    verdict r25 = ⟨true, true, 1, 1372, 19026, 14512, true, true, true⟩ ∧
    (verdict { r25 with T := 1636 }).exact = true ∧
    (verdict { r25 with T := 1635 }).exact = false ∧
    (verdict { r25 with T := 1636 }).bridge = true ∧
    (verdict { r25 with T := 1635 }).bridge = false := by decide +kernel
theorem v26 :
    verdict r26 = ⟨true, true, 1, 911, 13460, 10048, true, true, true⟩ ∧
    (verdict { r26 with T := 993 }).exact = true ∧
    (verdict { r26 with T := 992 }).exact = false ∧
    (verdict { r26 with T := 993 }).bridge = true ∧
    (verdict { r26 with T := 992 }).bridge = false := by decide +kernel
theorem v27 :
    verdict r27 = ⟨true, true, 1, 1793, 30918, 23677, true, true, true⟩ ∧
    (verdict { r27 with T := 2536 }).exact = true ∧
    (verdict { r27 with T := 2535 }).exact = false ∧
    (verdict { r27 with T := 2536 }).bridge = true ∧
    (verdict { r27 with T := 2535 }).bridge = false := by decide +kernel
theorem v28 :
    verdict r28 = ⟨true, true, 1, 1052, 10348, 7720, true, true, true⟩ ∧
    (verdict { r28 with T := 1330 }).exact = true ∧
    (verdict { r28 with T := 1329 }).exact = false ∧
    (verdict { r28 with T := 1330 }).bridge = true ∧
    (verdict { r28 with T := 1329 }).bridge = false := by decide +kernel
theorem v29 :
    verdict r29 = ⟨true, true, 1, 2071, 23851, 18265, true, true, true⟩ ∧
    (verdict { r29 with T := 3272 }).exact = true ∧
    (verdict { r29 with T := 3271 }).exact = false ∧
    (verdict { r29 with T := 3272 }).bridge = true ∧
    (verdict { r29 with T := 3271 }).bridge = false := by decide +kernel
theorem v30 :
    verdict r30 = ⟨true, true, 1, 701, 24248, 18472, true, true, true⟩ ∧
    (verdict { r30 with T := 1276 }).exact = true ∧
    (verdict { r30 with T := 1275 }).exact = false ∧
    (verdict { r30 with T := 1276 }).bridge = true ∧
    (verdict { r30 with T := 1275 }).bridge = false := by decide +kernel
theorem v31 :
    verdict r31 = ⟨true, true, 1, 811, 18652, 14204, true, true, true⟩ ∧
    (verdict { r31 with T := 1690 }).exact = true ∧
    (verdict { r31 with T := 1689 }).exact = false ∧
    (verdict { r31 with T := 1690 }).bridge = true ∧
    (verdict { r31 with T := 1689 }).bridge = false := by decide +kernel
theorem v32 :
    verdict r32 = ⟨true, true, 1, 548, 12976, 9743, true, true, true⟩ ∧
    (verdict { r32 with T := 799 }).exact = true ∧
    (verdict { r32 with T := 798 }).exact = false ∧
    (verdict { r32 with T := 799 }).bridge = true ∧
    (verdict { r32 with T := 798 }).bridge = false := by decide +kernel
theorem v33 :
    verdict r33 = ⟨true, true, 1, 1084, 30104, 22923, true, true, true⟩ ∧
    (verdict { r33 with T := 2084 }).exact = true ∧
    (verdict { r33 with T := 2083 }).exact = false ∧
    (verdict { r33 with T := 2084 }).bridge = true ∧
    (verdict { r33 with T := 2083 }).bridge = false := by decide +kernel
theorem v34 :
    verdict r34 = ⟨true, true, 1, 633, 9975, 7487, true, true, true⟩ ∧
    (verdict { r34 with T := 1092 }).exact = true ∧
    (verdict { r34 with T := 1091 }).exact = false ∧
    (verdict { r34 with T := 1092 }).bridge = true ∧
    (verdict { r34 with T := 1091 }).bridge = false := by decide +kernel
theorem v35 :
    verdict r35 = ⟨true, true, 1, 1253, 23219, 17679, true, true, true⟩ ∧
    (verdict { r35 with T := 2712 }).exact = true ∧
    (verdict { r35 with T := 2711 }).exact = false ∧
    (verdict { r35 with T := 2712 }).bridge = true ∧
    (verdict { r35 with T := 2711 }).bridge = false := by decide +kernel
theorem v36 :
    verdict r36 = ⟨true, true, 1, 1253, 24446, 17083, true, true, true⟩ ∧
    (verdict { r36 with T := 2979 }).exact = true ∧
    (verdict { r36 with T := 2978 }).exact = false ∧
    (verdict { r36 with T := 2979 }).bridge = true ∧
    (verdict { r36 with T := 2978 }).bridge = false := by decide +kernel
theorem v37 :
    verdict r37 = ⟨true, true, 1, 1448, 18820, 13144, true, true, true⟩ ∧
    (verdict { r37 with T := 4029 }).exact = true ∧
    (verdict { r37 with T := 4028 }).exact = false ∧
    (verdict { r37 with T := 4029 }).bridge = true ∧
    (verdict { r37 with T := 4028 }).bridge = false := by decide +kernel
theorem v38 :
    verdict r38 = ⟨true, true, 1, 1206, 14210, 10087, true, true, true⟩ ∧
    (verdict { r38 with T := 2244 }).exact = true ∧
    (verdict { r38 with T := 2243 }).exact = false ∧
    (verdict { r38 with T := 2244 }).bridge = true ∧
    (verdict { r38 with T := 2243 }).bridge = false := by decide +kernel
theorem v39 :
    verdict r39 = ⟨true, true, 1, 2133, 30468, 22239, true, true, true⟩ ∧
    (verdict { r39 with T := 4630 }).exact = true ∧
    (verdict { r39 with T := 4629 }).exact = false ∧
    (verdict { r39 with T := 4630 }).bridge = true ∧
    (verdict { r39 with T := 4629 }).bridge = false := by decide +kernel
theorem v40 :
    verdict r40 = ⟨true, true, 1, 1393, 10935, 7756, true, true, true⟩ ∧
    (verdict { r40 with T := 3067 }).exact = true ∧
    (verdict { r40 with T := 3066 }).exact = false ∧
    (verdict { r40 with T := 3067 }).bridge = true ∧
    (verdict { r40 with T := 3066 }).bridge = false := by decide +kernel
theorem v41 :
    verdict r41 = ⟨true, true, 1, 2464, 23507, 17154, true, true, true⟩ ∧
    (verdict { r41 with T := 6128 }).exact = true ∧
    (verdict { r41 with T := 6127 }).exact = false ∧
    (verdict { r41 with T := 6128 }).bridge = true ∧
    (verdict { r41 with T := 6127 }).bridge = false := by decide +kernel
theorem v42 :
    verdict r42 = ⟨true, true, 1, 560, 10777, 6502, true, true, true⟩ ∧
    (verdict { r42 with T := 906 }).exact = true ∧
    (verdict { r42 with T := 905 }).exact = false ∧
    (verdict { r42 with T := 906 }).bridge = true ∧
    (verdict { r42 with T := 905 }).bridge = false := by decide +kernel
theorem v43 :
    verdict r43 = ⟨true, true, 1, 648, 8291, 5002, true, true, true⟩ ∧
    (verdict { r43 with T := 1323 }).exact = true ∧
    (verdict { r43 with T := 1322 }).exact = false ∧
    (verdict { r43 with T := 1323 }).bridge = true ∧
    (verdict { r43 with T := 1322 }).bridge = false := by decide +kernel
theorem v44 :
    verdict r44 = ⟨true, true, 1, 548, 6238, 3763, true, true, true⟩ ∧
    (verdict { r44 with T := 674 }).exact = true ∧
    (verdict { r44 with T := 673 }).exact = false ∧
    (verdict { r44 with T := 674 }).bridge = true ∧
    (verdict { r44 with T := 673 }).bridge = false := by decide +kernel
theorem v45 :
    verdict r45 = ⟨true, true, 1, 1213, 14483, 8954, true, true, true⟩ ∧
    (verdict { r45 with T := 1707 }).exact = true ∧
    (verdict { r45 with T := 1706 }).exact = false ∧
    (verdict { r45 with T := 1707 }).bridge = true ∧
    (verdict { r45 with T := 1706 }).bridge = false := by decide +kernel
theorem v46 :
    verdict r46 = ⟨true, true, 1, 633, 4798, 2892, true, true, true⟩ ∧
    (verdict { r46 with T := 966 }).exact = true ∧
    (verdict { r46 with T := 965 }).exact = false ∧
    (verdict { r46 with T := 966 }).bridge = true ∧
    (verdict { r46 with T := 965 }).bridge = false := by decide +kernel
theorem v47 :
    verdict r47 = ⟨true, true, 1, 1402, 11174, 6907, true, true, true⟩ ∧
    (verdict { r47 with T := 2375 }).exact = true ∧
    (verdict { r47 with T := 2374 }).exact = false ∧
    (verdict { r47 with T := 2375 }).bridge = true ∧
    (verdict { r47 with T := 2374 }).bridge = false := by decide +kernel
theorem v48 :
    verdict r48 = ⟨true, true, 1, 1043, 11654, 6847, true, true, true⟩ ∧
    (verdict { r48 with T := 1051 }).exact = true ∧
    (verdict { r48 with T := 1050 }).exact = false ∧
    (verdict { r48 with T := 1051 }).bridge = true ∧
    (verdict { r48 with T := 1050 }).bridge = false := by decide +kernel
theorem v49 :
    verdict r49 = ⟨true, true, 1, 1206, 8969, 5267, true, true, true⟩ ∧
    (verdict { r49 with T := 1435 }).exact = true ∧
    (verdict { r49 with T := 1434 }).exact = false ∧
    (verdict { r49 with T := 1435 }).bridge = true ∧
    (verdict { r49 with T := 1434 }).bridge = false := by decide +kernel
theorem v50 :
    verdict r50 = ⟨true, true, 1, 833, 6719, 4054, true, true, true⟩ ∧
    (verdict { r50 with T := 746 }).exact = true ∧
    (verdict { r50 with T := 745 }).exact = false ∧
    (verdict { r50 with T := 833 }).bridge = true ∧
    (verdict { r50 with T := 832 }).bridge = false := by decide +kernel
theorem v51 :
    verdict r51 = ⟨true, true, 1, 1790, 15101, 9351, true, true, true⟩ ∧
    (verdict { r51 with T := 1803 }).exact = true ∧
    (verdict { r51 with T := 1802 }).exact = false ∧
    (verdict { r51 with T := 1803 }).bridge = true ∧
    (verdict { r51 with T := 1802 }).bridge = false := by decide +kernel
theorem v52 :
    verdict r52 = ⟨true, true, 1, 963, 5169, 3117, true, true, true⟩ ∧
    (verdict { r52 with T := 1078 }).exact = true ∧
    (verdict { r52 with T := 1077 }).exact = false ∧
    (verdict { r52 with T := 1078 }).bridge = true ∧
    (verdict { r52 with T := 1077 }).bridge = false := by decide +kernel
theorem v53 :
    verdict r53 = ⟨true, true, 1, 2068, 11652, 7214, true, true, true⟩ ∧
    (verdict { r53 with T := 2501 }).exact = true ∧
    (verdict { r53 with T := 2500 }).exact = false ∧
    (verdict { r53 with T := 2501 }).bridge = true ∧
    (verdict { r53 with T := 2500 }).bridge = false := by decide +kernel
theorem v54 :
    verdict r54 = ⟨true, true, 1, 1220, 15199, 11977, true, true, true⟩ ∧
    (verdict { r54 with T := 1222 }).exact = true ∧
    (verdict { r54 with T := 1221 }).exact = false ∧
    (verdict { r54 with T := 1345 }).bridge = true ∧
    (verdict { r54 with T := 1344 }).bridge = false := by decide +kernel
theorem v55 :
    verdict r55 = ⟨true, true, 1, 1410, 11695, 9211, true, true, true⟩ ∧
    (verdict { r55 with T := 1627 }).exact = true ∧
    (verdict { r55 with T := 1626 }).exact = false ∧
    (verdict { r55 with T := 1627 }).bridge = true ∧
    (verdict { r55 with T := 1626 }).bridge = false := by decide +kernel
theorem v56 :
    verdict r56 = ⟨true, true, 1, 1014, 8334, 6420, true, true, true⟩ ∧
    (verdict { r56 with T := 1009 }).exact = true ∧
    (verdict { r56 with T := 1008 }).exact = false ∧
    (verdict { r56 with T := 1064 }).bridge = true ∧
    (verdict { r56 with T := 1063 }).bridge = false := by decide +kernel
theorem v57 :
    verdict r57 = ⟨true, true, 1, 2058, 18997, 15076, true, true, true⟩ ∧
    (verdict { r57 with T := 2209 }).exact = true ∧
    (verdict { r57 with T := 2208 }).exact = false ∧
    (verdict { r57 with T := 2209 }).bridge = true ∧
    (verdict { r57 with T := 2208 }).bridge = false := by decide +kernel
theorem v58 :
    verdict r58 = ⟨true, true, 1, 1172, 6407, 4931, true, true, true⟩ ∧
    (verdict { r58 with T := 1247 }).exact = true ∧
    (verdict { r58 with T := 1246 }).exact = false ∧
    (verdict { r58 with T := 1247 }).bridge = true ∧
    (verdict { r58 with T := 1246 }).bridge = false := by decide +kernel
theorem v59 :
    verdict r59 = ⟨true, true, 1, 2378, 14651, 11625, true, true, true⟩ ∧
    (verdict { r59 with T := 3018 }).exact = true ∧
    (verdict { r59 with T := 3017 }).exact = false ∧
    (verdict { r59 with T := 3018 }).bridge = true ∧
    (verdict { r59 with T := 3017 }).bridge = false := by decide +kernel
theorem v60 :
    verdict r60 = ⟨true, true, 1, 563, 11887, 5874, true, true, true⟩ ∧
    (verdict { r60 with T := 838 }).exact = true ∧
    (verdict { r60 with T := 837 }).exact = false ∧
    (verdict { r60 with T := 838 }).bridge = true ∧
    (verdict { r60 with T := 837 }).bridge = false := by decide +kernel
theorem v61 :
    verdict r61 = ⟨true, true, 1, 651, 9149, 4516, true, true, true⟩ ∧
    (verdict { r61 with T := 1243 }).exact = true ∧
    (verdict { r61 with T := 1242 }).exact = false ∧
    (verdict { r61 with T := 1243 }).bridge = true ∧
    (verdict { r61 with T := 1242 }).bridge = false := by decide +kernel
theorem v62 :
    verdict r62 = ⟨true, true, 1, 580, 6578, 3298, true, true, true⟩ ∧
    (verdict { r62 with T := 698 }).exact = true ∧
    (verdict { r62 with T := 697 }).exact = false ∧
    (verdict { r62 with T := 698 }).bridge = true ∧
    (verdict { r62 with T := 697 }).bridge = false := by decide +kernel
theorem v63 :
    verdict r63 = ⟨true, true, 1, 1251, 14972, 7814, true, true, true⟩ ∧
    (verdict { r63 with T := 1661 }).exact = true ∧
    (verdict { r63 with T := 1660 }).exact = false ∧
    (verdict { r63 with T := 1661 }).bridge = true ∧
    (verdict { r63 with T := 1660 }).bridge = false := by decide +kernel
theorem v64 :
    verdict r64 = ⟨true, true, 1, 670, 5060, 2535, true, true, true⟩ ∧
    (verdict { r64 with T := 991 }).exact = true ∧
    (verdict { r64 with T := 990 }).exact = false ∧
    (verdict { r64 with T := 991 }).bridge = true ∧
    (verdict { r64 with T := 990 }).bridge = false := by decide +kernel
theorem v65 :
    verdict r65 = ⟨true, true, 1, 1445, 11550, 6028, true, true, true⟩ ∧
    (verdict { r65 with T := 2295 }).exact = true ∧
    (verdict { r65 with T := 2294 }).exact = false ∧
    (verdict { r65 with T := 2295 }).bridge = true ∧
    (verdict { r65 with T := 2294 }).bridge = false := by decide +kernel
theorem v66 :
    verdict r66 = ⟨true, true, 1, 1322, 11466, 6628, true, true, true⟩ ∧
    (verdict { r66 with T := 1338 }).exact = true ∧
    (verdict { r66 with T := 1337 }).exact = false ∧
    (verdict { r66 with T := 1462 }).bridge = true ∧
    (verdict { r66 with T := 1461 }).bridge = false := by decide +kernel
theorem v67 :
    verdict r67 = ⟨true, true, 1, 1528, 8827, 5099, true, true, true⟩ ∧
    (verdict { r67 with T := 1647 }).exact = true ∧
    (verdict { r67 with T := 1646 }).exact = false ∧
    (verdict { r67 with T := 1690 }).bridge = true ∧
    (verdict { r67 with T := 1689 }).bridge = false := by decide +kernel
theorem v68 :
    verdict r68 = ⟨true, true, 1, 943, 6255, 3625, true, true, true⟩ ∧
    (verdict { r68 with T := 976 }).exact = true ∧
    (verdict { r68 with T := 975 }).exact = false ∧
    (verdict { r68 with T := 1032 }).bridge = true ∧
    (verdict { r68 with T := 1031 }).bridge = false := by decide +kernel
theorem v69 :
    verdict r69 = ⟨true, true, 1, 1998, 14344, 8490, true, true, true⟩ ∧
    (verdict { r69 with T := 2042 }).exact = true ∧
    (verdict { r69 with T := 2041 }).exact = false ∧
    (verdict { r69 with T := 2166 }).bridge = true ∧
    (verdict { r69 with T := 2165 }).bridge = false := by decide +kernel
theorem v70 :
    verdict r70 = ⟨true, true, 1, 1090, 4812, 2786, true, true, true⟩ ∧
    (verdict { r70 with T := 1278 }).exact = true ∧
    (verdict { r70 with T := 1277 }).exact = false ∧
    (verdict { r70 with T := 1278 }).bridge = true ∧
    (verdict { r70 with T := 1277 }).bridge = false := by decide +kernel
theorem v71 :
    verdict r71 = ⟨true, true, 1, 2309, 11065, 6548, true, true, true⟩ ∧
    (verdict { r71 with T := 2915 }).exact = true ∧
    (verdict { r71 with T := 2914 }).exact = false ∧
    (verdict { r71 with T := 2915 }).bridge = true ∧
    (verdict { r71 with T := 2914 }).bridge = false := by decide +kernel
theorem v72 :
    verdict r72 = ⟨true, true, 1, 978, 11459, 6335, true, true, true⟩ ∧
    (verdict { r72 with T := 838 }).exact = true ∧
    (verdict { r72 with T := 837 }).exact = false ∧
    (verdict { r72 with T := 978 }).bridge = true ∧
    (verdict { r72 with T := 977 }).bridge = false := by decide +kernel
theorem v73 :
    verdict r73 = ⟨true, true, 1, 1131, 8820, 4872, true, true, true⟩ ∧
    (verdict { r73 with T := 1316 }).exact = true ∧
    (verdict { r73 with T := 1315 }).exact = false ∧
    (verdict { r73 with T := 1316 }).bridge = true ∧
    (verdict { r73 with T := 1315 }).bridge = false := by decide +kernel
theorem v74 :
    verdict r74 = ⟨true, true, 1, 718, 6654, 3489, true, true, true⟩ ∧
    (verdict { r74 with T := 665 }).exact = true ∧
    (verdict { r74 with T := 664 }).exact = false ∧
    (verdict { r74 with T := 720 }).bridge = true ∧
    (verdict { r74 with T := 719 }).bridge = false := by decide +kernel
theorem v75 :
    verdict r75 = ⟨true, true, 1, 1618, 15128, 8227, true, true, true⟩ ∧
    (verdict { r75 with T := 1552 }).exact = true ∧
    (verdict { r75 with T := 1551 }).exact = false ∧
    (verdict { r75 with T := 1628 }).bridge = true ∧
    (verdict { r75 with T := 1627 }).bridge = false := by decide +kernel
theorem v76 :
    verdict r76 = ⟨true, true, 1, 829, 5116, 2681, true, true, true⟩ ∧
    (verdict { r76 with T := 946 }).exact = true ∧
    (verdict { r76 with T := 945 }).exact = false ∧
    (verdict { r76 with T := 946 }).bridge = true ∧
    (verdict { r76 with T := 945 }).bridge = false := by decide +kernel
theorem v77 :
    verdict r77 = ⟨true, true, 1, 1869, 11669, 6345, true, true, true⟩ ∧
    (verdict { r77 with T := 2285 }).exact = true ∧
    (verdict { r77 with T := 2284 }).exact = false ∧
    (verdict { r77 with T := 2285 }).bridge = true ∧
    (verdict { r77 with T := 2284 }).bridge = false := by decide +kernel
theorem v78 :
    verdict r78 = ⟨true, true, 1, 569, 10818, 6873, true, true, true⟩ ∧
    (verdict { r78 with T := 988 }).exact = true ∧
    (verdict { r78 with T := 987 }).exact = false ∧
    (verdict { r78 with T := 988 }).bridge = true ∧
    (verdict { r78 with T := 987 }).bridge = false := by decide +kernel
theorem v79 :
    verdict r79 = ⟨true, true, 1, 658, 8325, 5289, true, true, true⟩ ∧
    (verdict { r79 with T := 1417 }).exact = true ∧
    (verdict { r79 with T := 1416 }).exact = false ∧
    (verdict { r79 with T := 1417 }).bridge = true ∧
    (verdict { r79 with T := 1416 }).bridge = false := by decide +kernel
theorem v80 :
    verdict r80 = ⟨true, true, 1, 377, 5858, 3803, true, true, true⟩ ∧
    (verdict { r80 with T := 768 }).exact = true ∧
    (verdict { r80 with T := 767 }).exact = false ∧
    (verdict { r80 with T := 768 }).bridge = true ∧
    (verdict { r80 with T := 767 }).bridge = false := by decide +kernel
theorem v81 :
    verdict r81 = ⟨true, true, 1, 847, 13537, 8903, true, true, true⟩ ∧
    (verdict { r81 with T := 1684 }).exact = true ∧
    (verdict { r81 with T := 1683 }).exact = false ∧
    (verdict { r81 with T := 1684 }).bridge = true ∧
    (verdict { r81 with T := 1683 }).bridge = false := by decide +kernel
theorem v82 :
    verdict r82 = ⟨true, true, 1, 436, 4506, 2926, true, true, true⟩ ∧
    (verdict { r82 with T := 1023 }).exact = true ∧
    (verdict { r82 with T := 1022 }).exact = false ∧
    (verdict { r82 with T := 1023 }).bridge = true ∧
    (verdict { r82 with T := 1022 }).bridge = false := by decide +kernel
theorem v83 :
    verdict r83 = ⟨true, true, 1, 979, 10442, 6867, true, true, true⟩ ∧
    (verdict { r83 with T := 2263 }).exact = true ∧
    (verdict { r83 with T := 2262 }).exact = false ∧
    (verdict { r83 with T := 2263 }).bridge = true ∧
    (verdict { r83 with T := 2262 }).bridge = false := by decide +kernel
theorem v84 :
    verdict r84 = ⟨true, true, 1, 420, 14257, 6285, true, true, true⟩ ∧
    (verdict { r84 with T := 838 }).exact = true ∧
    (verdict { r84 with T := 837 }).exact = false ∧
    (verdict { r84 with T := 838 }).bridge = true ∧
    (verdict { r84 with T := 837 }).bridge = false := by decide +kernel
theorem v85 :
    verdict r85 = ⟨true, true, 1, 486, 10983, 4834, true, true, true⟩ ∧
    (verdict { r85 with T := 1239 }).exact = true ∧
    (verdict { r85 with T := 1238 }).exact = false ∧
    (verdict { r85 with T := 1239 }).bridge = true ∧
    (verdict { r85 with T := 1238 }).bridge = false := by decide +kernel
theorem v86 :
    verdict r86 = ⟨true, true, 1, 492, 8623, 3653, true, true, true⟩ ∧
    (verdict { r86 with T := 912 }).exact = true ∧
    (verdict { r86 with T := 911 }).exact = false ∧
    (verdict { r86 with T := 912 }).bridge = true ∧
    (verdict { r86 with T := 911 }).bridge = false := by decide +kernel
theorem v87 :
    verdict r87 = ⟨true, true, 1, 1074, 17778, 8478, true, true, true⟩ ∧
    (verdict { r87 with T := 2184 }).exact = true ∧
    (verdict { r87 with T := 2183 }).exact = false ∧
    (verdict { r87 with T := 2184 }).bridge = true ∧
    (verdict { r87 with T := 2183 }).bridge = false := by decide +kernel
theorem v88 :
    verdict r88 = ⟨true, true, 1, 568, 6639, 2805, true, true, true⟩ ∧
    (verdict { r88 with T := 1218 }).exact = true ∧
    (verdict { r88 with T := 1217 }).exact = false ∧
    (verdict { r88 with T := 1218 }).bridge = true ∧
    (verdict { r88 with T := 1217 }).bridge = false := by decide +kernel
theorem v89 :
    verdict r89 = ⟨true, true, 1, 1241, 13716, 6537, true, true, true⟩ ∧
    (verdict { r89 with T := 2848 }).exact = true ∧
    (verdict { r89 with T := 2847 }).exact = false ∧
    (verdict { r89 with T := 2848 }).bridge = true ∧
    (verdict { r89 with T := 2847 }).bridge = false := by decide +kernel
theorem v90 :
    verdict r90 = ⟨true, true, 1, 707, 14080, 2661, true, true, true⟩ ∧
    (verdict { r90 with T := 443 }).exact = true ∧
    (verdict { r90 with T := 442 }).exact = false ∧
    (verdict { r90 with T := 707 }).bridge = true ∧
    (verdict { r90 with T := 706 }).bridge = false := by decide +kernel
theorem v91 :
    verdict r91 = ⟨true, true, 1, 818, 10847, 2046, true, true, true⟩ ∧
    (verdict { r91 with T := 704 }).exact = true ∧
    (verdict { r91 with T := 703 }).exact = false ∧
    (verdict { r91 with T := 818 }).bridge = true ∧
    (verdict { r91 with T := 817 }).bridge = false := by decide +kernel
theorem v92 :
    verdict r92 = ⟨true, true, 1, 501, 7659, 1429, true, true, true⟩ ∧
    (verdict { r92 with T := 563 }).exact = true ∧
    (verdict { r92 with T := 562 }).exact = false ∧
    (verdict { r92 with T := 563 }).bridge = true ∧
    (verdict { r92 with T := 562 }).bridge = false := by decide +kernel
theorem v93 :
    verdict r93 = ⟨true, true, 1, 1006, 16303, 3196, true, true, true⟩ ∧
    (verdict { r93 with T := 1314 }).exact = true ∧
    (verdict { r93 with T := 1313 }).exact = false ∧
    (verdict { r93 with T := 1314 }).bridge = true ∧
    (verdict { r93 with T := 1313 }).bridge = false := by decide +kernel
theorem v94 :
    verdict r94 = ⟨true, true, 1, 579, 5899, 1097, true, true, true⟩ ∧
    (verdict { r94 with T := 807 }).exact = true ∧
    (verdict { r94 with T := 806 }).exact = false ∧
    (verdict { r94 with T := 807 }).bridge = true ∧
    (verdict { r94 with T := 806 }).bridge = false := by decide +kernel
theorem v95 :
    verdict r95 = ⟨true, true, 1, 1163, 12580, 2464, true, true, true⟩ ∧
    (verdict { r95 with T := 1821 }).exact = true ∧
    (verdict { r95 with T := 1820 }).exact = false ∧
    (verdict { r95 with T := 1821 }).bridge = true ∧
    (verdict { r95 with T := 1820 }).bridge = false := by decide +kernel
theorem v96 :
    verdict r96 = ⟨true, true, 1, 709, 6710, 2803, true, true, true⟩ ∧
    (verdict { r96 with T := 798 }).exact = true ∧
    (verdict { r96 with T := 797 }).exact = false ∧
    (verdict { r96 with T := 921 }).bridge = true ∧
    (verdict { r96 with T := 920 }).bridge = false := by decide +kernel
theorem v97 :
    verdict r97 = ⟨true, true, 1, 820, 5163, 2155, true, true, true⟩ ∧
    (verdict { r97 with T := 1005 }).exact = true ∧
    (verdict { r97 with T := 1004 }).exact = false ∧
    (verdict { r97 with T := 1065 }).bridge = true ∧
    (verdict { r97 with T := 1064 }).bridge = false := by decide +kernel
theorem v98 :
    verdict r98 = ⟨true, true, 1, 593, 3991, 1648, true, true, true⟩ ∧
    (verdict { r98 with T := 625 }).exact = true ∧
    (verdict { r98 with T := 624 }).exact = false ∧
    (verdict { r98 with T := 680 }).bridge = true ∧
    (verdict { r98 with T := 679 }).bridge = false := by decide +kernel
theorem v99 :
    verdict r99 = ⟨true, true, 1, 1219, 8825, 3698, true, true, true⟩ ∧
    (verdict { r99 with T := 1395 }).exact = true ∧
    (verdict { r99 with T := 1394 }).exact = false ∧
    (verdict { r99 with T := 1433 }).bridge = true ∧
    (verdict { r99 with T := 1432 }).bridge = false := by decide +kernel
theorem v100 :
    verdict r100 = ⟨true, true, 1, 684, 3069, 1266, true, true, true⟩ ∧
    (verdict { r100 with T := 873 }).exact = true ∧
    (verdict { r100 with T := 872 }).exact = false ∧
    (verdict { r100 with T := 873 }).bridge = true ∧
    (verdict { r100 with T := 872 }).bridge = false := by decide +kernel
theorem v101 :
    verdict r101 = ⟨true, true, 1, 1408, 6809, 2852, true, true, true⟩ ∧
    (verdict { r101 with T := 2022 }).exact = true ∧
    (verdict { r101 with T := 2021 }).exact = false ∧
    (verdict { r101 with T := 2022 }).bridge = true ∧
    (verdict { r101 with T := 2021 }).bridge = false := by decide +kernel
theorem v102 :
    verdict r102 = ⟨true, true, 1, 1251, 11225, 3345, true, true, true⟩ ∧
    (verdict { r102 with T := 1127 }).exact = true ∧
    (verdict { r102 with T := 1126 }).exact = false ∧
    (verdict { r102 with T := 1251 }).bridge = true ∧
    (verdict { r102 with T := 1250 }).bridge = false := by decide +kernel
theorem v103 :
    verdict r103 = ⟨true, true, 1, 1446, 8642, 2574, true, true, true⟩ ∧
    (verdict { r103 with T := 1302 }).exact = true ∧
    (verdict { r103 with T := 1301 }).exact = false ∧
    (verdict { r103 with T := 1446 }).bridge = true ∧
    (verdict { r103 with T := 1445 }).bridge = false := by decide +kernel
theorem v104 :
    verdict r104 = ⟨true, true, 1, 1035, 6859, 2076, true, true, true⟩ ∧
    (verdict { r104 with T := 989 }).exact = true ∧
    (verdict { r104 with T := 988 }).exact = false ∧
    (verdict { r104 with T := 1041 }).bridge = true ∧
    (verdict { r104 with T := 1040 }).bridge = false := by decide +kernel
theorem v105 :
    verdict r105 = ⟨true, true, 1, 2069, 15152, 4525, true, true, true⟩ ∧
    (verdict { r105 with T := 1952 }).exact = true ∧
    (verdict { r105 with T := 1951 }).exact = false ∧
    (verdict { r105 with T := 2069 }).bridge = true ∧
    (verdict { r105 with T := 2068 }).bridge = false := by decide +kernel
theorem v106 :
    verdict r106 = ⟨true, true, 1, 1195, 5280, 1597, true, true, true⟩ ∧
    (verdict { r106 with T := 1142 }).exact = true ∧
    (verdict { r106 with T := 1141 }).exact = false ∧
    (verdict { r106 with T := 1203 }).bridge = true ∧
    (verdict { r106 with T := 1202 }).bridge = false := by decide +kernel
theorem v107 :
    verdict r107 = ⟨true, true, 1, 2390, 11694, 3492, true, true, true⟩ ∧
    (verdict { r107 with T := 2254 }).exact = true ∧
    (verdict { r107 with T := 2253 }).exact = false ∧
    (verdict { r107 with T := 2390 }).bridge = true ∧
    (verdict { r107 with T := 2389 }).bridge = false := by decide +kernel
theorem v108 :
    verdict r108 = ⟨true, true, 1, 1156, 11191, 3037, true, true, true⟩ ∧
    (verdict { r108 with T := 838 }).exact = true ∧
    (verdict { r108 with T := 837 }).exact = false ∧
    (verdict { r108 with T := 1156 }).bridge = true ∧
    (verdict { r108 with T := 1155 }).bridge = false := by decide +kernel
theorem v109 :
    verdict r109 = ⟨true, true, 1, 1336, 8616, 2336, true, true, true⟩ ∧
    (verdict { r109 with T := 1192 }).exact = true ∧
    (verdict { r109 with T := 1191 }).exact = false ∧
    (verdict { r109 with T := 1336 }).bridge = true ∧
    (verdict { r109 with T := 1335 }).bridge = false := by decide +kernel
theorem v110 :
    verdict r110 = ⟨true, true, 1, 920, 6841, 1722, true, true, true⟩ ∧
    (verdict { r110 with T := 783 }).exact = true ∧
    (verdict { r110 with T := 782 }).exact = false ∧
    (verdict { r110 with T := 920 }).bridge = true ∧
    (verdict { r110 with T := 919 }).bridge = false := by decide +kernel
theorem v111 :
    verdict r111 = ⟨true, true, 1, 1778, 14636, 3711, true, true, true⟩ ∧
    (verdict { r111 with T := 1504 }).exact = true ∧
    (verdict { r111 with T := 1503 }).exact = false ∧
    (verdict { r111 with T := 1778 }).bridge = true ∧
    (verdict { r111 with T := 1777 }).bridge = false := by decide +kernel
theorem v112 :
    verdict r112 = ⟨true, true, 1, 1062, 5266, 1324, true, true, true⟩ ∧
    (verdict { r112 with T := 913 }).exact = true ∧
    (verdict { r112 with T := 912 }).exact = false ∧
    (verdict { r112 with T := 1063 }).bridge = true ∧
    (verdict { r112 with T := 1062 }).bridge = false := by decide +kernel
theorem v113 :
    verdict r113 = ⟨true, true, 1, 2054, 11294, 2863, true, true, true⟩ ∧
    (verdict { r113 with T := 1803 }).exact = true ∧
    (verdict { r113 with T := 1802 }).exact = false ∧
    (verdict { r113 with T := 2054 }).bridge = true ∧
    (verdict { r113 with T := 2053 }).bridge = false := by decide +kernel
theorem v114 :
    verdict r114 = ⟨true, true, 1, 717, 11949, 2951, true, true, true⟩ ∧
    (verdict { r114 with T := 593 }).exact = true ∧
    (verdict { r114 with T := 592 }).exact = false ∧
    (verdict { r114 with T := 717 }).bridge = true ∧
    (verdict { r114 with T := 716 }).bridge = false := by decide +kernel
theorem v115 :
    verdict r115 = ⟨true, true, 1, 829, 9203, 2270, true, true, true⟩ ∧
    (verdict { r115 with T := 923 }).exact = true ∧
    (verdict { r115 with T := 922 }).exact = false ∧
    (verdict { r115 with T := 923 }).bridge = true ∧
    (verdict { r115 with T := 922 }).bridge = false := by decide +kernel
theorem v116 :
    verdict r116 = ⟨true, true, 1, 536, 6991, 1802, true, true, true⟩ ∧
    (verdict { r116 with T := 663 }).exact = true ∧
    (verdict { r116 with T := 662 }).exact = false ∧
    (verdict { r116 with T := 718 }).bridge = true ∧
    (verdict { r116 with T := 717 }).bridge = false := by decide +kernel
theorem v117 :
    verdict r117 = ⟨true, true, 1, 922, 14717, 3933, true, true, true⟩ ∧
    (verdict { r117 with T := 1406 }).exact = true ∧
    (verdict { r117 with T := 1405 }).exact = false ∧
    (verdict { r117 with T := 1406 }).bridge = true ∧
    (verdict { r117 with T := 1405 }).bridge = false := by decide +kernel
theorem v118 :
    verdict r118 = ⟨true, true, 1, 619, 5384, 1386, true, true, true⟩ ∧
    (verdict { r118 with T := 907 }).exact = true ∧
    (verdict { r118 with T := 906 }).exact = false ∧
    (verdict { r118 with T := 907 }).bridge = true ∧
    (verdict { r118 with T := 906 }).bridge = false := by decide +kernel
theorem v119 :
    verdict r119 = ⟨true, true, 1, 1065, 11356, 3034, true, true, true⟩ ∧
    (verdict { r119 with T := 1984 }).exact = true ∧
    (verdict { r119 with T := 1983 }).exact = false ∧
    (verdict { r119 with T := 1984 }).bridge = true ∧
    (verdict { r119 with T := 1983 }).bridge = false := by decide +kernel
theorem v120 :
    verdict r120 = ⟨true, true, 1, 887, 12723, 2840, true, true, true⟩ ∧
    (verdict { r120 with T := 835 }).exact = true ∧
    (verdict { r120 with T := 834 }).exact = false ∧
    (verdict { r120 with T := 958 }).bridge = true ∧
    (verdict { r120 with T := 957 }).bridge = false := by decide +kernel
theorem v121 :
    verdict r121 = ⟨true, true, 1, 1026, 9788, 2184, true, true, true⟩ ∧
    (verdict { r121 with T := 1019 }).exact = true ∧
    (verdict { r121 with T := 1018 }).exact = false ∧
    (verdict { r121 with T := 1108 }).bridge = true ∧
    (verdict { r121 with T := 1107 }).bridge = false := by decide +kernel
theorem v122 :
    verdict r122 = ⟨true, true, 1, 677, 6833, 1620, true, true, true⟩ ∧
    (verdict { r122 with T := 665 }).exact = true ∧
    (verdict { r122 with T := 664 }).exact = false ∧
    (verdict { r122 with T := 713 }).bridge = true ∧
    (verdict { r122 with T := 712 }).bridge = false := by decide +kernel
theorem v123 :
    verdict r123 = ⟨true, true, 1, 1279, 15237, 3542, true, true, true⟩ ∧
    (verdict { r123 with T := 1280 }).exact = true ∧
    (verdict { r123 with T := 1279 }).exact = false ∧
    (verdict { r123 with T := 1403 }).bridge = true ∧
    (verdict { r123 with T := 1402 }).bridge = false := by decide +kernel
theorem v124 :
    verdict r124 = ⟨true, true, 1, 782, 5252, 1246, true, true, true⟩ ∧
    (verdict { r124 with T := 768 }).exact = true ∧
    (verdict { r124 with T := 767 }).exact = false ∧
    (verdict { r124 with T := 824 }).bridge = true ∧
    (verdict { r124 with T := 823 }).bridge = false := by decide +kernel
theorem v125 :
    verdict r125 = ⟨true, true, 1, 1477, 11754, 2732, true, true, true⟩ ∧
    (verdict { r125 with T := 1717 }).exact = true ∧
    (verdict { r125 with T := 1716 }).exact = false ∧
    (verdict { r125 with T := 1717 }).bridge = true ∧
    (verdict { r125 with T := 1716 }).bridge = false := by decide +kernel
theorem v126 :
    verdict r126 = ⟨true, true, 1, 2057, 16106, 4151, true, true, true⟩ ∧
    (verdict { r126 with T := 1933 }).exact = true ∧
    (verdict { r126 with T := 1932 }).exact = false ∧
    (verdict { r126 with T := 2057 }).bridge = true ∧
    (verdict { r126 with T := 2056 }).bridge = false := by decide +kernel
theorem v127 :
    verdict r127 = ⟨true, true, 1, 2377, 12401, 3196, true, true, true⟩ ∧
    (verdict { r127 with T := 2233 }).exact = true ∧
    (verdict { r127 with T := 2232 }).exact = false ∧
    (verdict { r127 with T := 2377 }).bridge = true ∧
    (verdict { r127 with T := 2376 }).bridge = false := by decide +kernel
theorem v128 :
    verdict r128 = ⟨true, true, 1, 1258, 8637, 2247, true, true, true⟩ ∧
    (verdict { r128 with T := 1236 }).exact = true ∧
    (verdict { r128 with T := 1235 }).exact = false ∧
    (verdict { r128 with T := 1285 }).bridge = true ∧
    (verdict { r128 with T := 1284 }).bridge = false := by decide +kernel
theorem v129 :
    verdict r129 = ⟨true, true, 1, 2602, 19225, 4891, true, true, true⟩ ∧
    (verdict { r129 with T := 2513 }).exact = true ∧
    (verdict { r129 with T := 2512 }).exact = false ∧
    (verdict { r129 with T := 2626 }).bridge = true ∧
    (verdict { r129 with T := 2625 }).bridge = false := by decide +kernel
theorem v130 :
    verdict r130 = ⟨true, true, 1, 1453, 6645, 1729, true, true, true⟩ ∧
    (verdict { r130 with T := 1428 }).exact = true ∧
    (verdict { r130 with T := 1427 }).exact = false ∧
    (verdict { r130 with T := 1485 }).bridge = true ∧
    (verdict { r130 with T := 1484 }).bridge = false := by decide +kernel
theorem v131 :
    verdict r131 = ⟨true, true, 1, 3005, 14832, 3773, true, true, true⟩ ∧
    (verdict { r131 with T := 2903 }).exact = true ∧
    (verdict { r131 with T := 2902 }).exact = false ∧
    (verdict { r131 with T := 3034 }).bridge = true ∧
    (verdict { r131 with T := 3033 }).bridge = false := by decide +kernel
theorem v132 :
    verdict r132 = ⟨true, true, 1, 1702, 12825, 3868, true, true, true⟩ ∧
    (verdict { r132 with T := 1437 }).exact = true ∧
    (verdict { r132 with T := 1436 }).exact = false ∧
    (verdict { r132 with T := 1702 }).bridge = true ∧
    (verdict { r132 with T := 1701 }).bridge = false := by decide +kernel
theorem v133 :
    verdict r133 = ⟨true, true, 1, 1967, 9885, 2978, true, true, true⟩ ∧
    (verdict { r133 with T := 1660 }).exact = true ∧
    (verdict { r133 with T := 1659 }).exact = false ∧
    (verdict { r133 with T := 1967 }).bridge = true ∧
    (verdict { r133 with T := 1966 }).bridge = false := by decide +kernel
theorem v134 :
    verdict r134 = ⟨true, true, 1, 1158, 7655, 2307, true, true, true⟩ ∧
    (verdict { r134 with T := 1155 }).exact = true ∧
    (verdict { r134 with T := 1154 }).exact = false ∧
    (verdict { r134 with T := 1203 }).bridge = true ∧
    (verdict { r134 with T := 1202 }).bridge = false := by decide +kernel
theorem v135 :
    verdict r135 = ⟨true, true, 1, 2166, 15158, 4890, true, true, true⟩ ∧
    (verdict { r135 with T := 2150 }).exact = true ∧
    (verdict { r135 with T := 2149 }).exact = false ∧
    (verdict { r135 with T := 2263 }).bridge = true ∧
    (verdict { r135 with T := 2262 }).bridge = false := by decide +kernel
theorem v136 :
    verdict r136 = ⟨true, true, 1, 1338, 5898, 1775, true, true, true⟩ ∧
    (verdict { r136 with T := 1334 }).exact = true ∧
    (verdict { r136 with T := 1333 }).exact = false ∧
    (verdict { r136 with T := 1390 }).bridge = true ∧
    (verdict { r136 with T := 1389 }).bridge = false := by decide +kernel
theorem v137 :
    verdict r137 = ⟨true, true, 1, 2502, 11697, 3772, true, true, true⟩ ∧
    (verdict { r137 with T := 2487 }).exact = true ∧
    (verdict { r137 with T := 2486 }).exact = false ∧
    (verdict { r137 with T := 2615 }).bridge = true ∧
    (verdict { r137 with T := 2614 }).bridge = false := by decide +kernel
theorem v138 :
    verdict r138 = ⟨true, true, 1, 1516, 13249, 3428, true, true, true⟩ ∧
    (verdict { r138 with T := 1210 }).exact = true ∧
    (verdict { r138 with T := 1209 }).exact = false ∧
    (verdict { r138 with T := 1516 }).bridge = true ∧
    (verdict { r138 with T := 1515 }).bridge = false := by decide +kernel
theorem v139 :
    verdict r139 = ⟨true, true, 1, 1752, 10212, 2638, true, true, true⟩ ∧
    (verdict { r139 with T := 1398 }).exact = true ∧
    (verdict { r139 with T := 1397 }).exact = false ∧
    (verdict { r139 with T := 1752 }).bridge = true ∧
    (verdict { r139 with T := 1751 }).bridge = false := by decide +kernel
theorem v140 :
    verdict r140 = ⟨true, true, 1, 1257, 8127, 1932, true, true, true⟩ ∧
    (verdict { r140 with T := 985 }).exact = true ∧
    (verdict { r140 with T := 984 }).exact = false ∧
    (verdict { r140 with T := 1263 }).bridge = true ∧
    (verdict { r140 with T := 1262 }).bridge = false := by decide +kernel
theorem v141 :
    verdict r141 = ⟨true, true, 1, 2416, 15899, 4109, true, true, true⟩ ∧
    (verdict { r141 with T := 2307 }).exact = true ∧
    (verdict { r141 with T := 2306 }).exact = false ∧
    (verdict { r141 with T := 2431 }).bridge = true ∧
    (verdict { r141 with T := 2430 }).bridge = false := by decide +kernel
theorem v142 :
    verdict r142 = ⟨true, true, 1, 1452, 6264, 1486, true, true, true⟩ ∧
    (verdict { r142 with T := 1392 }).exact = true ∧
    (verdict { r142 with T := 1391 }).exact = false ∧
    (verdict { r142 with T := 1459 }).bridge = true ∧
    (verdict { r142 with T := 1458 }).bridge = false := by decide +kernel
theorem v143 :
    verdict r143 = ⟨true, true, 1, 2792, 12269, 3170, true, true, true⟩ ∧
    (verdict { r143 with T := 2666 }).exact = true ∧
    (verdict { r143 with T := 2665 }).exact = false ∧
    (verdict { r143 with T := 2809 }).bridge = true ∧
    (verdict { r143 with T := 2808 }).bridge = false := by decide +kernel
theorem v144 :
    verdict r144 = ⟨true, true, 1, 1846, 13249, 4153, true, true, true⟩ ∧
    (verdict { r144 with T := 1722 }).exact = true ∧
    (verdict { r144 with T := 1721 }).exact = false ∧
    (verdict { r144 with T := 1859 }).bridge = true ∧
    (verdict { r144 with T := 1858 }).bridge = false := by decide +kernel
theorem v145 :
    verdict r145 = ⟨true, true, 1, 2133, 10213, 3198, true, true, true⟩ ∧
    (verdict { r145 with T := 2005 }).exact = true ∧
    (verdict { r145 with T := 2004 }).exact = false ∧
    (verdict { r145 with T := 2148 }).bridge = true ∧
    (verdict { r145 with T := 2147 }).bridge = false := by decide +kernel
theorem v146 :
    verdict r146 = ⟨true, true, 1, 1489, 8390, 2573, true, true, true⟩ ∧
    (verdict { r146 with T := 1437 }).exact = true ∧
    (verdict { r146 with T := 1436 }).exact = false ∧
    (verdict { r146 with T := 1490 }).bridge = true ∧
    (verdict { r146 with T := 1489 }).bridge = false := by decide +kernel
theorem v147 :
    verdict r147 = ⟨true, true, 1, 2725, 16340, 5302, true, true, true⟩ ∧
    (verdict { r147 with T := 2607 }).exact = true ∧
    (verdict { r147 with T := 2606 }).exact = false ∧
    (verdict { r147 with T := 2725 }).bridge = true ∧
    (verdict { r147 with T := 2724 }).bridge = false := by decide +kernel
theorem v148 :
    verdict r148 = ⟨true, true, 1, 1720, 6465, 1980, true, true, true⟩ ∧
    (verdict { r148 with T := 1659 }).exact = true ∧
    (verdict { r148 with T := 1658 }).exact = false ∧
    (verdict { r148 with T := 1721 }).bridge = true ∧
    (verdict { r148 with T := 1720 }).bridge = false := by decide +kernel
theorem v149 :
    verdict r149 = ⟨true, true, 1, 3148, 12609, 4090, true, true, true⟩ ∧
    (verdict { r149 with T := 3011 }).exact = true ∧
    (verdict { r149 with T := 3010 }).exact = false ∧
    (verdict { r149 with T := 3148 }).bridge = true ∧
    (verdict { r149 with T := 3147 }).bridge = false := by decide +kernel

end Formal.Timing.ChainSettleExe.GcdD
