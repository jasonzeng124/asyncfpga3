import Formal.Timing.ChainSettleExeGcdDData7

/-! C-10o2 GENERATED: kernel-decided verdicts of chunk 7 (see ChainSettleExe.verdict).
Per row: `verdict` at chainck's late side `T`; exact PASS at `T*` and FAIL at `T* - 1`
(margin_exact = T - T*); bridge PASS at `Tb*` and FAIL at `Tb* - 1`. -/

namespace Formal.Timing.ChainSettleExe.GcdD
open Formal.Timing Formal.Timing.ChainSettleExe

theorem v1050 :
    verdict r1050 = ⟨true, true, 1, 896, 7583, 2850, true, true, true⟩ ∧
    (verdict { r1050 with T := 632 }).exact = true ∧
    (verdict { r1050 with T := 631 }).exact = false ∧
    (verdict { r1050 with T := 896 }).bridge = true ∧
    (verdict { r1050 with T := 895 }).bridge = false := by decide +kernel
theorem v1051 :
    verdict r1051 = ⟨true, true, 1, 1036, 5839, 2192, true, true, true⟩ ∧
    (verdict { r1051 with T := 776 }).exact = true ∧
    (verdict { r1051 with T := 775 }).exact = false ∧
    (verdict { r1051 with T := 1036 }).bridge = true ∧
    (verdict { r1051 with T := 1035 }).bridge = false := by decide +kernel
theorem v1052 :
    verdict r1052 = ⟨true, true, 1, 727, 4733, 1640, true, true, true⟩ ∧
    (verdict { r1052 with T := 557 }).exact = true ∧
    (verdict { r1052 with T := 556 }).exact = false ∧
    (verdict { r1052 with T := 773 }).bridge = true ∧
    (verdict { r1052 with T := 772 }).bridge = false := by decide +kernel
theorem v1053 :
    verdict r1053 = ⟨true, true, 1, 1329, 9643, 3488, true, true, true⟩ ∧
    (verdict { r1053 with T := 1344 }).exact = true ∧
    (verdict { r1053 with T := 1343 }).exact = false ∧
    (verdict { r1053 with T := 1429 }).bridge = true ∧
    (verdict { r1053 with T := 1428 }).bridge = false := by decide +kernel
theorem v1054 :
    verdict r1054 = ⟨true, true, 1, 839, 3644, 1261, true, true, true⟩ ∧
    (verdict { r1054 with T := 904 }).exact = true ∧
    (verdict { r1054 with T := 903 }).exact = false ∧
    (verdict { r1054 with T := 904 }).bridge = true ∧
    (verdict { r1054 with T := 903 }).bridge = false := by decide +kernel
theorem v1055 :
    verdict r1055 = ⟨true, true, 1, 1535, 7439, 2690, true, true, true⟩ ∧
    (verdict { r1055 with T := 1968 }).exact = true ∧
    (verdict { r1055 with T := 1967 }).exact = false ∧
    (verdict { r1055 with T := 1968 }).bridge = true ∧
    (verdict { r1055 with T := 1967 }).bridge = false := by decide +kernel
theorem v1056 :
    verdict r1056 = ⟨true, true, 1, 1633, 13164, 3587, true, true, true⟩ ∧
    (verdict { r1056 with T := 1369 }).exact = true ∧
    (verdict { r1056 with T := 1368 }).exact = false ∧
    (verdict { r1056 with T := 1633 }).bridge = true ∧
    (verdict { r1056 with T := 1632 }).bridge = false := by decide +kernel
theorem v1057 :
    verdict r1057 = ⟨true, true, 1, 1887, 10144, 2761, true, true, true⟩ ∧
    (verdict { r1057 with T := 1582 }).exact = true ∧
    (verdict { r1057 with T := 1581 }).exact = false ∧
    (verdict { r1057 with T := 1887 }).bridge = true ∧
    (verdict { r1057 with T := 1886 }).bridge = false := by decide +kernel
theorem v1058 :
    verdict r1058 = ⟨true, true, 1, 1450, 7637, 2062, true, true, true⟩ ∧
    (verdict { r1058 with T := 1128 }).exact = true ∧
    (verdict { r1058 with T := 1127 }).exact = false ∧
    (verdict { r1058 with T := 1450 }).bridge = true ∧
    (verdict { r1058 with T := 1449 }).bridge = false := by decide +kernel
theorem v1059 :
    verdict r1059 = ⟨true, true, 1, 2578, 15436, 4129, true, true, true⟩ ∧
    (verdict { r1059 with T := 1886 }).exact = true ∧
    (verdict { r1059 with T := 1885 }).exact = false ∧
    (verdict { r1059 with T := 2578 }).bridge = true ∧
    (verdict { r1059 with T := 2577 }).bridge = false := by decide +kernel
theorem v1060 :
    verdict r1060 = ⟨true, true, 1, 1675, 5884, 1587, true, true, true⟩ ∧
    (verdict { r1060 with T := 1335 }).exact = true ∧
    (verdict { r1060 with T := 1334 }).exact = false ∧
    (verdict { r1060 with T := 1675 }).bridge = true ∧
    (verdict { r1060 with T := 1674 }).bridge = false := by decide +kernel
theorem v1061 :
    verdict r1061 = ⟨true, true, 1, 2978, 11911, 3186, true, true, true⟩ ∧
    (verdict { r1061 with T := 2661 }).exact = true ∧
    (verdict { r1061 with T := 2660 }).exact = false ∧
    (verdict { r1061 with T := 2978 }).bridge = true ∧
    (verdict { r1061 with T := 2977 }).bridge = false := by decide +kernel
theorem v1062 :
    verdict r1062 = ⟨true, true, 1, 751, 6795, 2845, true, true, true⟩ ∧
    (verdict { r1062 with T := 627 }).exact = true ∧
    (verdict { r1062 with T := 626 }).exact = false ∧
    (verdict { r1062 with T := 751 }).bridge = true ∧
    (verdict { r1062 with T := 750 }).bridge = false := by decide +kernel
theorem v1063 :
    verdict r1063 = ⟨true, true, 1, 869, 5230, 2188, true, true, true⟩ ∧
    (verdict { r1063 with T := 775 }).exact = true ∧
    (verdict { r1063 with T := 774 }).exact = false ∧
    (verdict { r1063 with T := 869 }).bridge = true ∧
    (verdict { r1063 with T := 868 }).bridge = false := by decide +kernel
theorem v1064 :
    verdict r1064 = ⟨true, true, 1, 701, 4350, 1657, true, true, true⟩ ∧
    (verdict { r1064 with T := 725 }).exact = true ∧
    (verdict { r1064 with T := 724 }).exact = false ∧
    (verdict { r1064 with T := 783 }).bridge = true ∧
    (verdict { r1064 with T := 782 }).bridge = false := by decide +kernel
theorem v1065 :
    verdict r1065 = ⟨true, true, 1, 1250, 8867, 3508, true, true, true⟩ ∧
    (verdict { r1065 with T := 1344 }).exact = true ∧
    (verdict { r1065 with T := 1343 }).exact = false ∧
    (verdict { r1065 with T := 1422 }).bridge = true ∧
    (verdict { r1065 with T := 1421 }).bridge = false := by decide +kernel
theorem v1066 :
    verdict r1066 = ⟨true, true, 1, 810, 3347, 1274, true, true, true⟩ ∧
    (verdict { r1066 with T := 910 }).exact = true ∧
    (verdict { r1066 with T := 909 }).exact = false ∧
    (verdict { r1066 with T := 910 }).bridge = true ∧
    (verdict { r1066 with T := 909 }).bridge = false := by decide +kernel
theorem v1067 :
    verdict r1067 = ⟨true, true, 1, 1445, 6843, 2707, true, true, true⟩ ∧
    (verdict { r1067 with T := 1966 }).exact = true ∧
    (verdict { r1067 with T := 1965 }).exact = false ∧
    (verdict { r1067 with T := 1966 }).bridge = true ∧
    (verdict { r1067 with T := 1965 }).bridge = false := by decide +kernel
theorem v1068 :
    verdict r1068 = ⟨true, true, 1, 1683, 14397, 3918, true, true, true⟩ ∧
    (verdict { r1068 with T := 1559 }).exact = true ∧
    (verdict { r1068 with T := 1558 }).exact = false ∧
    (verdict { r1068 with T := 1683 }).bridge = true ∧
    (verdict { r1068 with T := 1682 }).bridge = false := by decide +kernel
theorem v1069 :
    verdict r1069 = ⟨true, true, 1, 1945, 11097, 3016, true, true, true⟩ ∧
    (verdict { r1069 with T := 1801 }).exact = true ∧
    (verdict { r1069 with T := 1800 }).exact = false ∧
    (verdict { r1069 with T := 1945 }).bridge = true ∧
    (verdict { r1069 with T := 1944 }).bridge = false := by decide +kernel
theorem v1070 :
    verdict r1070 = ⟨true, true, 1, 1390, 8263, 2395, true, true, true⟩ ∧
    (verdict { r1070 with T := 1296 }).exact = true ∧
    (verdict { r1070 with T := 1295 }).exact = false ∧
    (verdict { r1070 with T := 1395 }).bridge = true ∧
    (verdict { r1070 with T := 1394 }).bridge = false := by decide +kernel
theorem v1071 :
    verdict r1071 = ⟨true, true, 1, 2535, 16908, 4956, true, true, true⟩ ∧
    (verdict { r1071 with T := 2418 }).exact = true ∧
    (verdict { r1071 with T := 2417 }).exact = false ∧
    (verdict { r1071 with T := 2545 }).bridge = true ∧
    (verdict { r1071 with T := 2544 }).bridge = false := by decide +kernel
theorem v1072 :
    verdict r1072 = ⟨true, true, 1, 1605, 6365, 1843, true, true, true⟩ ∧
    (verdict { r1072 with T := 1541 }).exact = true ∧
    (verdict { r1072 with T := 1540 }).exact = false ∧
    (verdict { r1072 with T := 1611 }).bridge = true ∧
    (verdict { r1072 with T := 1610 }).bridge = false := by decide +kernel
theorem v1073 :
    verdict r1073 = ⟨true, true, 1, 2928, 13048, 3824, true, true, true⟩ ∧
    (verdict { r1073 with T := 2797 }).exact = true ∧
    (verdict { r1073 with T := 2796 }).exact = false ∧
    (verdict { r1073 with T := 2940 }).bridge = true ∧
    (verdict { r1073 with T := 2939 }).bridge = false := by decide +kernel
theorem v1074 :
    verdict r1074 = ⟨true, true, 1, 707, 6735, 2874, true, true, true⟩ ∧
    (verdict { r1074 with T := 632 }).exact = true ∧
    (verdict { r1074 with T := 631 }).exact = false ∧
    (verdict { r1074 with T := 707 }).bridge = true ∧
    (verdict { r1074 with T := 706 }).bridge = false := by decide +kernel
theorem v1075 :
    verdict r1075 = ⟨true, true, 1, 818, 5184, 2211, true, true, true⟩ ∧
    (verdict { r1075 with T := 950 }).exact = true ∧
    (verdict { r1075 with T := 949 }).exact = false ∧
    (verdict { r1075 with T := 950 }).bridge = true ∧
    (verdict { r1075 with T := 949 }).bridge = false := by decide +kernel
theorem v1076 :
    verdict r1076 = ⟨true, true, 1, 606, 3893, 1767, true, true, true⟩ ∧
    (verdict { r1076 with T := 530 }).exact = true ∧
    (verdict { r1076 with T := 529 }).exact = false ∧
    (verdict { r1076 with T := 606 }).bridge = true ∧
    (verdict { r1076 with T := 605 }).bridge = false := by decide +kernel
theorem v1077 :
    verdict r1077 = ⟨true, true, 1, 1243, 8765, 4015, true, true, true⟩ ∧
    (verdict { r1077 with T := 1309 }).exact = true ∧
    (verdict { r1077 with T := 1308 }).exact = false ∧
    (verdict { r1077 with T := 1309 }).bridge = true ∧
    (verdict { r1077 with T := 1308 }).bridge = false := by decide +kernel
theorem v1078 :
    verdict r1078 = ⟨true, true, 1, 700, 2996, 1358, true, true, true⟩ ∧
    (verdict { r1078 with T := 785 }).exact = true ∧
    (verdict { r1078 with T := 784 }).exact = false ∧
    (verdict { r1078 with T := 785 }).bridge = true ∧
    (verdict { r1078 with T := 784 }).bridge = false := by decide +kernel
theorem v1079 :
    verdict r1079 = ⟨true, true, 1, 1437, 6763, 3097, true, true, true⟩ ∧
    (verdict { r1079 with T := 1771 }).exact = true ∧
    (verdict { r1079 with T := 1770 }).exact = false ∧
    (verdict { r1079 with T := 1771 }).bridge = true ∧
    (verdict { r1079 with T := 1770 }).bridge = false := by decide +kernel
theorem v1080 :
    verdict r1080 = ⟨true, true, 1, 898, 10287, 2992, true, true, true⟩ ∧
    (verdict { r1080 with T := 824 }).exact = true ∧
    (verdict { r1080 with T := 823 }).exact = false ∧
    (verdict { r1080 with T := 1110 }).bridge = true ∧
    (verdict { r1080 with T := 1109 }).bridge = false := by decide +kernel
theorem v1081 :
    verdict r1081 = ⟨true, true, 1, 1038, 7922, 2301, true, true, true⟩ ∧
    (verdict { r1081 with T := 1140 }).exact = true ∧
    (verdict { r1081 with T := 1139 }).exact = false ∧
    (verdict { r1081 with T := 1283 }).bridge = true ∧
    (verdict { r1081 with T := 1282 }).bridge = false := by decide +kernel
theorem v1082 :
    verdict r1082 = ⟨true, true, 1, 700, 6127, 1594, true, true, true⟩ ∧
    (verdict { r1082 with T := 706 }).exact = true ∧
    (verdict { r1082 with T := 705 }).exact = false ∧
    (verdict { r1082 with T := 776 }).bridge = true ∧
    (verdict { r1082 with T := 775 }).bridge = false := by decide +kernel
theorem v1083 :
    verdict r1083 = ⟨true, true, 1, 1414, 12982, 3564, true, true, true⟩ ∧
    (verdict { r1083 with T := 1494 }).exact = true ∧
    (verdict { r1083 with T := 1493 }).exact = false ∧
    (verdict { r1083 with T := 1617 }).bridge = true ∧
    (verdict { r1083 with T := 1616 }).bridge = false := by decide +kernel
theorem v1084 :
    verdict r1084 = ⟨true, true, 1, 808, 4717, 1225, true, true, true⟩ ∧
    (verdict { r1084 with T := 832 }).exact = true ∧
    (verdict { r1084 with T := 831 }).exact = false ∧
    (verdict { r1084 with T := 896 }).bridge = true ∧
    (verdict { r1084 with T := 895 }).bridge = false := by decide +kernel
theorem v1085 :
    verdict r1085 = ⟨true, true, 1, 1633, 10017, 2749, true, true, true⟩ ∧
    (verdict { r1085 with T := 1864 }).exact = true ∧
    (verdict { r1085 with T := 1863 }).exact = false ∧
    (verdict { r1085 with T := 1868 }).bridge = true ∧
    (verdict { r1085 with T := 1867 }).bridge = false := by decide +kernel
theorem v1086 :
    verdict r1086 = ⟨true, true, 1, 567, 6498, 2787, true, true, true⟩ ∧
    (verdict { r1086 with T := 559 }).exact = true ∧
    (verdict { r1086 with T := 558 }).exact = false ∧
    (verdict { r1086 with T := 567 }).bridge = true ∧
    (verdict { r1086 with T := 566 }).bridge = false := by decide +kernel
theorem v1087 :
    verdict r1087 = ⟨true, true, 1, 656, 5001, 2143, true, true, true⟩ ∧
    (verdict { r1087 with T := 866 }).exact = true ∧
    (verdict { r1087 with T := 865 }).exact = false ∧
    (verdict { r1087 with T := 866 }).bridge = true ∧
    (verdict { r1087 with T := 865 }).bridge = false := by decide +kernel
theorem v1088 :
    verdict r1088 = ⟨true, true, 1, 321, 3552, 1743, true, true, true⟩ ∧
    (verdict { r1088 with T := 606 }).exact = true ∧
    (verdict { r1088 with T := 605 }).exact = false ∧
    (verdict { r1088 with T := 606 }).bridge = true ∧
    (verdict { r1088 with T := 605 }).bridge = false := by decide +kernel
theorem v1089 :
    verdict r1089 = ⟨true, true, 1, 649, 7975, 3978, true, true, true⟩ ∧
    (verdict { r1089 with T := 1434 }).exact = true ∧
    (verdict { r1089 with T := 1433 }).exact = false ∧
    (verdict { r1089 with T := 1434 }).bridge = true ∧
    (verdict { r1089 with T := 1433 }).bridge = false := by decide +kernel
theorem v1090 :
    verdict r1090 = ⟨true, true, 1, 371, 2730, 1339, true, true, true⟩ ∧
    (verdict { r1090 with T := 827 }).exact = true ∧
    (verdict { r1090 with T := 826 }).exact = false ∧
    (verdict { r1090 with T := 827 }).bridge = true ∧
    (verdict { r1090 with T := 826 }).bridge = false := by decide +kernel
theorem v1091 :
    verdict r1091 = ⟨true, true, 1, 751, 6152, 3068, true, true, true⟩ ∧
    (verdict { r1091 with T := 1906 }).exact = true ∧
    (verdict { r1091 with T := 1905 }).exact = false ∧
    (verdict { r1091 with T := 1906 }).bridge = true ∧
    (verdict { r1091 with T := 1905 }).bridge = false := by decide +kernel
theorem v1092 :
    verdict r1092 = ⟨true, true, 1, 1104, 11996, 3338, true, true, true⟩ ∧
    (verdict { r1092 with T := 980 }).exact = true ∧
    (verdict { r1092 with T := 979 }).exact = false ∧
    (verdict { r1092 with T := 1104 }).bridge = true ∧
    (verdict { r1092 with T := 1103 }).bridge = false := by decide +kernel
theorem v1093 :
    verdict r1093 = ⟨true, true, 1, 1276, 9239, 2568, true, true, true⟩ ∧
    (verdict { r1093 with T := 1132 }).exact = true ∧
    (verdict { r1093 with T := 1131 }).exact = false ∧
    (verdict { r1093 with T := 1276 }).bridge = true ∧
    (verdict { r1093 with T := 1275 }).bridge = false := by decide +kernel
theorem v1094 :
    verdict r1094 = ⟨true, true, 1, 665, 6956, 1843, true, true, true⟩ ∧
    (verdict { r1094 with T := 792 }).exact = true ∧
    (verdict { r1094 with T := 791 }).exact = false ∧
    (verdict { r1094 with T := 847 }).bridge = true ∧
    (verdict { r1094 with T := 846 }).bridge = false := by decide +kernel
theorem v1095 :
    verdict r1095 = ⟨true, true, 1, 1248, 14324, 4084, true, true, true⟩ ∧
    (verdict { r1095 with T := 1548 }).exact = true ∧
    (verdict { r1095 with T := 1547 }).exact = false ∧
    (verdict { r1095 with T := 1671 }).bridge = true ∧
    (verdict { r1095 with T := 1670 }).bridge = false := by decide +kernel
theorem v1096 :
    verdict r1096 = ⟨true, true, 1, 768, 5353, 1418, true, true, true⟩ ∧
    (verdict { r1096 with T := 979 }).exact = true ∧
    (verdict { r1096 with T := 978 }).exact = false ∧
    (verdict { r1096 with T := 979 }).bridge = true ∧
    (verdict { r1096 with T := 978 }).bridge = false := by decide +kernel
theorem v1097 :
    verdict r1097 = ⟨true, true, 1, 1442, 11051, 3151, true, true, true⟩ ∧
    (verdict { r1097 with T := 2157 }).exact = true ∧
    (verdict { r1097 with T := 2156 }).exact = false ∧
    (verdict { r1097 with T := 2157 }).bridge = true ∧
    (verdict { r1097 with T := 2156 }).bridge = false := by decide +kernel
theorem v1098 :
    verdict r1098 = ⟨true, true, 1, 702, 6164, 2656, true, true, true⟩ ∧
    (verdict { r1098 with T := 438 }).exact = true ∧
    (verdict { r1098 with T := 437 }).exact = false ∧
    (verdict { r1098 with T := 702 }).bridge = true ∧
    (verdict { r1098 with T := 701 }).bridge = false := by decide +kernel
theorem v1099 :
    verdict r1099 = ⟨true, true, 1, 812, 4742, 2042, true, true, true⟩ ∧
    (verdict { r1099 with T := 756 }).exact = true ∧
    (verdict { r1099 with T := 755 }).exact = false ∧
    (verdict { r1099 with T := 812 }).bridge = true ∧
    (verdict { r1099 with T := 811 }).bridge = false := by decide +kernel
theorem v1100 :
    verdict r1100 = ⟨true, true, 1, 619, 3551, 1541, true, true, true⟩ ∧
    (verdict { r1100 with T := 466 }).exact = true ∧
    (verdict { r1100 with T := 465 }).exact = false ∧
    (verdict { r1100 with T := 624 }).bridge = true ∧
    (verdict { r1100 with T := 623 }).bridge = false := by decide +kernel
theorem v1101 :
    verdict r1101 = ⟨true, true, 1, 1232, 7855, 3453, true, true, true⟩ ∧
    (verdict { r1101 with T := 954 }).exact = true ∧
    (verdict { r1101 with T := 953 }).exact = false ∧
    (verdict { r1101 with T := 1233 }).bridge = true ∧
    (verdict { r1101 with T := 1232 }).bridge = false := by decide +kernel
theorem v1102 :
    verdict r1102 = ⟨true, true, 1, 716, 2731, 1184, true, true, true⟩ ∧
    (verdict { r1102 with T := 799 }).exact = true ∧
    (verdict { r1102 with T := 798 }).exact = false ∧
    (verdict { r1102 with T := 799 }).bridge = true ∧
    (verdict { r1102 with T := 798 }).bridge = false := by decide +kernel
theorem v1103 :
    verdict r1103 = ⟨true, true, 1, 1424, 6060, 2663, true, true, true⟩ ∧
    (verdict { r1103 with T := 1780 }).exact = true ∧
    (verdict { r1103 with T := 1779 }).exact = false ∧
    (verdict { r1103 with T := 1780 }).bridge = true ∧
    (verdict { r1103 with T := 1779 }).bridge = false := by decide +kernel
theorem v1104 :
    verdict r1104 = ⟨true, true, 1, 1315, 20898, 7936, true, true, true⟩ ∧
    (verdict { r1104 with T := 2152 }).exact = true ∧
    (verdict { r1104 with T := 2151 }).exact = false ∧
    (verdict { r1104 with T := 2152 }).bridge = true ∧
    (verdict { r1104 with T := 2151 }).bridge = false := by decide +kernel
theorem v1105 :
    verdict r1105 = ⟨true, true, 1, 1520, 16084, 6108, true, true, true⟩ ∧
    (verdict { r1105 with T := 2994 }).exact = true ∧
    (verdict { r1105 with T := 2993 }).exact = false ∧
    (verdict { r1105 with T := 2994 }).bridge = true ∧
    (verdict { r1105 with T := 2993 }).bridge = false := by decide +kernel
theorem v1106 :
    verdict r1106 = ⟨true, true, 1, 1011, 11799, 4300, true, true, true⟩ ∧
    (verdict { r1106 with T := 1581 }).exact = true ∧
    (verdict { r1106 with T := 1580 }).exact = false ∧
    (verdict { r1106 with T := 1581 }).bridge = true ∧
    (verdict { r1106 with T := 1580 }).bridge = false := by decide +kernel
theorem v1107 :
    verdict r1107 = ⟨true, true, 1, 1947, 25629, 9399, true, true, true⟩ ∧
    (verdict { r1107 with T := 3417 }).exact = true ∧
    (verdict { r1107 with T := 3416 }).exact = false ∧
    (verdict { r1107 with T := 3417 }).bridge = true ∧
    (verdict { r1107 with T := 3416 }).bridge = false := by decide +kernel
theorem v1108 :
    verdict r1108 = ⟨true, true, 1, 1168, 9079, 3308, true, true, true⟩ ∧
    (verdict { r1108 with T := 2154 }).exact = true ∧
    (verdict { r1108 with T := 2153 }).exact = false ∧
    (verdict { r1108 with T := 2154 }).bridge = true ∧
    (verdict { r1108 with T := 2153 }).bridge = false := by decide +kernel
theorem v1109 :
    verdict r1109 = ⟨true, true, 1, 2250, 19771, 7251, true, true, true⟩ ∧
    (verdict { r1109 with T := 4537 }).exact = true ∧
    (verdict { r1109 with T := 4536 }).exact = false ∧
    (verdict { r1109 with T := 4537 }).bridge = true ∧
    (verdict { r1109 with T := 4536 }).bridge = false := by decide +kernel
theorem v1110 :
    verdict r1110 = ⟨true, true, 1, 751, 11431, 7832, true, true, true⟩ ∧
    (verdict { r1110 with T := 937 }).exact = true ∧
    (verdict { r1110 with T := 936 }).exact = false ∧
    (verdict { r1110 with T := 937 }).bridge = true ∧
    (verdict { r1110 with T := 936 }).bridge = false := by decide +kernel
theorem v1111 :
    verdict r1111 = ⟨true, true, 1, 869, 8795, 6022, true, true, true⟩ ∧
    (verdict { r1111 with T := 1375 }).exact = true ∧
    (verdict { r1111 with T := 1374 }).exact = false ∧
    (verdict { r1111 with T := 1375 }).bridge = true ∧
    (verdict { r1111 with T := 1374 }).bridge = false := by decide +kernel
theorem v1112 :
    verdict r1112 = ⟨true, true, 1, 672, 5991, 4046, true, true, true⟩ ∧
    (verdict { r1112 with T := 753 }).exact = true ∧
    (verdict { r1112 with T := 752 }).exact = false ∧
    (verdict { r1112 with T := 808 }).bridge = true ∧
    (verdict { r1112 with T := 807 }).bridge = false := by decide +kernel
theorem v1113 :
    verdict r1113 = ⟨true, true, 1, 1460, 13806, 9600, true, true, true⟩ ∧
    (verdict { r1113 with T := 1578 }).exact = true ∧
    (verdict { r1113 with T := 1577 }).exact = false ∧
    (verdict { r1113 with T := 1685 }).bridge = true ∧
    (verdict { r1113 with T := 1684 }).bridge = false := by decide +kernel
theorem v1114 :
    verdict r1114 = ⟨true, true, 1, 776, 4608, 3110, true, true, true⟩ ∧
    (verdict { r1114 with T := 951 }).exact = true ∧
    (verdict { r1114 with T := 950 }).exact = false ∧
    (verdict { r1114 with T := 951 }).bridge = true ∧
    (verdict { r1114 with T := 950 }).bridge = false := by decide +kernel
theorem v1115 :
    verdict r1115 = ⟨true, true, 1, 1687, 10651, 7405, true, true, true⟩ ∧
    (verdict { r1115 with T := 2280 }).exact = true ∧
    (verdict { r1115 with T := 2279 }).exact = false ∧
    (verdict { r1115 with T := 2280 }).bridge = true ∧
    (verdict { r1115 with T := 2279 }).bridge = false := by decide +kernel
theorem v1116 :
    verdict r1116 = ⟨true, true, 1, 1096, 12252, 8037, true, true, true⟩ ∧
    (verdict { r1116 with T := 972 }).exact = true ∧
    (verdict { r1116 with T := 971 }).exact = false ∧
    (verdict { r1116 with T := 1096 }).bridge = true ∧
    (verdict { r1116 with T := 1095 }).bridge = false := by decide +kernel
theorem v1117 :
    verdict r1117 = ⟨true, true, 1, 1267, 9428, 6180, true, true, true⟩ ∧
    (verdict { r1117 with T := 1345 }).exact = true ∧
    (verdict { r1117 with T := 1344 }).exact = false ∧
    (verdict { r1117 with T := 1345 }).bridge = true ∧
    (verdict { r1117 with T := 1344 }).bridge = false := by decide +kernel
theorem v1118 :
    verdict r1118 = ⟨true, true, 1, 848, 6945, 4588, true, true, true⟩ ∧
    (verdict { r1118 with T := 873 }).exact = true ∧
    (verdict { r1118 with T := 872 }).exact = false ∧
    (verdict { r1118 with T := 873 }).bridge = true ∧
    (verdict { r1118 with T := 872 }).bridge = false := by decide +kernel
theorem v1119 :
    verdict r1119 = ⟨true, true, 1, 1783, 15736, 10695, true, true, true⟩ ∧
    (verdict { r1119 with T := 1932 }).exact = true ∧
    (verdict { r1119 with T := 1931 }).exact = false ∧
    (verdict { r1119 with T := 1932 }).bridge = true ∧
    (verdict { r1119 with T := 1931 }).bridge = false := by decide +kernel
theorem v1120 :
    verdict r1120 = ⟨true, true, 1, 979, 5342, 3526, true, true, true⟩ ∧
    (verdict { r1120 with T := 1188 }).exact = true ∧
    (verdict { r1120 with T := 1187 }).exact = false ∧
    (verdict { r1120 with T := 1188 }).bridge = true ∧
    (verdict { r1120 with T := 1187 }).bridge = false := by decide +kernel
theorem v1121 :
    verdict r1121 = ⟨true, true, 1, 2060, 12139, 8248, true, true, true⟩ ∧
    (verdict { r1121 with T := 2615 }).exact = true ∧
    (verdict { r1121 with T := 2614 }).exact = false ∧
    (verdict { r1121 with T := 2615 }).bridge = true ∧
    (verdict { r1121 with T := 2614 }).bridge = false := by decide +kernel
theorem v1122 :
    verdict r1122 = ⟨true, true, 1, 1368, 49626, 43238, true, true, true⟩ ∧
    (verdict { r1122 with T := 1401 }).exact = true ∧
    (verdict { r1122 with T := 1400 }).exact = false ∧
    (verdict { r1122 with T := 1582 }).bridge = true ∧
    (verdict { r1122 with T := 1581 }).bridge = false := by decide +kernel
theorem v1123 :
    verdict r1123 = ⟨true, true, 1, 1581, 38184, 33262, true, true, true⟩ ∧
    (verdict { r1123 with T := 1980 }).exact = true ∧
    (verdict { r1123 with T := 1979 }).exact = false ∧
    (verdict { r1123 with T := 1980 }).bridge = true ∧
    (verdict { r1123 with T := 1979 }).bridge = false := by decide +kernel
theorem v1124 :
    verdict r1124 = ⟨true, true, 1, 1149, 25964, 22239, true, true, true⟩ ∧
    (verdict { r1124 with T := 1105 }).exact = true ∧
    (verdict { r1124 with T := 1104 }).exact = false ∧
    (verdict { r1124 with T := 1155 }).bridge = true ∧
    (verdict { r1124 with T := 1154 }).bridge = false := by decide +kernel
theorem v1125 :
    verdict r1125 = ⟨true, true, 1, 2112, 59887, 52142, true, true, true⟩ ∧
    (verdict { r1125 with T := 2610 }).exact = true ∧
    (verdict { r1125 with T := 2609 }).exact = false ∧
    (verdict { r1125 with T := 2748 }).bridge = true ∧
    (verdict { r1125 with T := 2747 }).bridge = false := by decide +kernel
theorem v1126 :
    verdict r1126 = ⟨true, true, 1, 1327, 19963, 17094, true, true, true⟩ ∧
    (verdict { r1126 with T := 1591 }).exact = true ∧
    (verdict { r1126 with T := 1590 }).exact = false ∧
    (verdict { r1126 with T := 1591 }).bridge = true ∧
    (verdict { r1126 with T := 1590 }).bridge = false := by decide +kernel
theorem v1127 :
    verdict r1127 = ⟨true, true, 1, 2439, 46201, 40224, true, true, true⟩ ∧
    (verdict { r1127 with T := 3645 }).exact = true ∧
    (verdict { r1127 with T := 3644 }).exact = false ∧
    (verdict { r1127 with T := 3645 }).bridge = true ∧
    (verdict { r1127 with T := 3644 }).bridge = false := by decide +kernel
theorem v1128 :
    verdict r1128 = ⟨true, true, 1, 1451, 50047, 43838, true, true, true⟩ ∧
    (verdict { r1128 with T := 1952 }).exact = true ∧
    (verdict { r1128 with T := 1951 }).exact = false ∧
    (verdict { r1128 with T := 2215 }).bridge = true ∧
    (verdict { r1128 with T := 2214 }).bridge = false := by decide +kernel
theorem v1129 :
    verdict r1129 = ⟨true, true, 1, 1677, 38509, 33725, true, true, true⟩ ∧
    (verdict { r1129 with T := 2639 }).exact = true ∧
    (verdict { r1129 with T := 2638 }).exact = false ∧
    (verdict { r1129 with T := 2639 }).bridge = true ∧
    (verdict { r1129 with T := 2638 }).bridge = false := by decide +kernel
theorem v1130 :
    verdict r1130 = ⟨true, true, 1, 1028, 27142, 23680, true, true, true⟩ ∧
    (verdict { r1130 with T := 1425 }).exact = true ∧
    (verdict { r1130 with T := 1424 }).exact = false ∧
    (verdict { r1130 with T := 1546 }).bridge = true ∧
    (verdict { r1130 with T := 1545 }).bridge = false := by decide +kernel
theorem v1131 :
    verdict r1131 = ⟨true, true, 1, 1985, 62373, 55140, true, true, true⟩ ∧
    (verdict { r1131 with T := 2985 }).exact = true ∧
    (verdict { r1131 with T := 2984 }).exact = false ∧
    (verdict { r1131 with T := 2989 }).bridge = true ∧
    (verdict { r1131 with T := 2988 }).bridge = false := by decide +kernel
theorem v1132 :
    verdict r1132 = ⟨true, true, 1, 1187, 20867, 18201, true, true, true⟩ ∧
    (verdict { r1132 with T := 1869 }).exact = true ∧
    (verdict { r1132 with T := 1868 }).exact = false ∧
    (verdict { r1132 with T := 1869 }).bridge = true ∧
    (verdict { r1132 with T := 1868 }).bridge = false := by decide +kernel
theorem v1133 :
    verdict r1133 = ⟨true, true, 1, 2293, 48111, 42530, true, true, true⟩ ∧
    (verdict { r1133 with T := 4247 }).exact = true ∧
    (verdict { r1133 with T := 4246 }).exact = false ∧
    (verdict { r1133 with T := 4247 }).bridge = true ∧
    (verdict { r1133 with T := 4246 }).bridge = false := by decide +kernel
theorem v1134 :
    verdict r1134 = ⟨true, true, 1, 2503, 52223, 44064, true, true, true⟩ ∧
    (verdict { r1134 with T := 2379 }).exact = true ∧
    (verdict { r1134 with T := 2378 }).exact = false ∧
    (verdict { r1134 with T := 2514 }).bridge = true ∧
    (verdict { r1134 with T := 2513 }).bridge = false := by decide +kernel
theorem v1135 :
    verdict r1135 = ⟨true, true, 1, 2892, 40185, 33898, true, true, true⟩ ∧
    (verdict { r1135 with T := 2762 }).exact = true ∧
    (verdict { r1135 with T := 2761 }).exact = false ∧
    (verdict { r1135 with T := 2905 }).bridge = true ∧
    (verdict { r1135 with T := 2904 }).bridge = false := by decide +kernel
theorem v1136 :
    verdict r1136 = ⟨true, true, 1, 1804, 29041, 23903, true, true, true⟩ ∧
    (verdict { r1136 with T := 1744 }).exact = true ∧
    (verdict { r1136 with T := 1743 }).exact = false ∧
    (verdict { r1136 with T := 1837 }).bridge = true ∧
    (verdict { r1136 with T := 1836 }).bridge = false := by decide +kernel
theorem v1137 :
    verdict r1137 = ⟨true, true, 1, 3406, 65852, 55437, true, true, true⟩ ∧
    (verdict { r1137 with T := 3281 }).exact = true ∧
    (verdict { r1137 with T := 3280 }).exact = false ∧
    (verdict { r1137 with T := 3448 }).bridge = true ∧
    (verdict { r1137 with T := 3447 }).bridge = false := by decide +kernel
theorem v1138 :
    verdict r1138 = ⟨true, true, 1, 2083, 22337, 18378, true, true, true⟩ ∧
    (verdict { r1138 with T := 2058 }).exact = true ∧
    (verdict { r1138 with T := 2057 }).exact = false ∧
    (verdict { r1138 with T := 2122 }).bridge = true ∧
    (verdict { r1138 with T := 2121 }).bridge = false := by decide +kernel
theorem v1139 :
    verdict r1139 = ⟨true, true, 1, 3934, 50802, 42763, true, true, true⟩ ∧
    (verdict { r1139 with T := 4426 }).exact = true ∧
    (verdict { r1139 with T := 4425 }).exact = false ∧
    (verdict { r1139 with T := 4426 }).bridge = true ∧
    (verdict { r1139 with T := 4425 }).bridge = false := by decide +kernel
theorem v1140 :
    verdict r1140 = ⟨true, true, 1, 1055, 30488, 23193, true, true, true⟩ ∧
    (verdict { r1140 with T := 1663 }).exact = true ∧
    (verdict { r1140 with T := 1662 }).exact = false ∧
    (verdict { r1140 with T := 1663 }).bridge = true ∧
    (verdict { r1140 with T := 1662 }).bridge = false := by decide +kernel
theorem v1141 :
    verdict r1141 = ⟨true, true, 1, 1220, 23460, 17839, true, true, true⟩ ∧
    (verdict { r1141 with T := 2327 }).exact = true ∧
    (verdict { r1141 with T := 2326 }).exact = false ∧
    (verdict { r1141 with T := 2327 }).bridge = true ∧
    (verdict { r1141 with T := 2326 }).bridge = false := by decide +kernel
theorem v1142 :
    verdict r1142 = ⟨true, true, 1, 758, 16176, 11643, true, true, true⟩ ∧
    (verdict { r1142 with T := 1057 }).exact = true ∧
    (verdict { r1142 with T := 1056 }).exact = false ∧
    (verdict { r1142 with T := 1133 }).bridge = true ∧
    (verdict { r1142 with T := 1132 }).bridge = false := by decide +kernel
theorem v1143 :
    verdict r1143 = ⟨true, true, 1, 1557, 36846, 27428, true, true, true⟩ ∧
    (verdict { r1143 with T := 2586 }).exact = true ∧
    (verdict { r1143 with T := 2585 }).exact = false ∧
    (verdict { r1143 with T := 2586 }).bridge = true ∧
    (verdict { r1143 with T := 2585 }).bridge = false := by decide +kernel
theorem v1144 :
    verdict r1144 = ⟨true, true, 1, 876, 12439, 8947, true, true, true⟩ ∧
    (verdict { r1144 with T := 1477 }).exact = true ∧
    (verdict { r1144 with T := 1476 }).exact = false ∧
    (verdict { r1144 with T := 1477 }).bridge = true ∧
    (verdict { r1144 with T := 1476 }).bridge = false := by decide +kernel
theorem v1145 :
    verdict r1145 = ⟨true, true, 1, 1799, 28424, 21156, true, true, true⟩ ∧
    (verdict { r1145 with T := 3453 }).exact = true ∧
    (verdict { r1145 with T := 3452 }).exact = false ∧
    (verdict { r1145 with T := 3453 }).bridge = true ∧
    (verdict { r1145 with T := 3452 }).bridge = false := by decide +kernel
theorem v1146 :
    verdict r1146 = ⟨true, true, 1, 2618, 56970, 48791, true, true, true⟩ ∧
    (verdict { r1146 with T := 2376 }).exact = true ∧
    (verdict { r1146 with T := 2375 }).exact = false ∧
    (verdict { r1146 with T := 2769 }).bridge = true ∧
    (verdict { r1146 with T := 2768 }).bridge = false := by decide +kernel
theorem v1147 :
    verdict r1147 = ⟨true, true, 1, 3025, 43841, 37533, true, true, true⟩ ∧
    (verdict { r1147 with T := 3169 }).exact = true ∧
    (verdict { r1147 with T := 3168 }).exact = false ∧
    (verdict { r1147 with T := 3199 }).bridge = true ∧
    (verdict { r1147 with T := 3198 }).bridge = false := by decide +kernel
theorem v1148 :
    verdict r1148 = ⟨true, true, 1, 2025, 31958, 26661, true, true, true⟩ ∧
    (verdict { r1148 with T := 1862 }).exact = true ∧
    (verdict { r1148 with T := 1861 }).exact = false ∧
    (verdict { r1148 with T := 2254 }).bridge = true ∧
    (verdict { r1148 with T := 2253 }).bridge = false := by decide +kernel
theorem v1149 :
    verdict r1149 = ⟨true, true, 1, 3684, 72148, 62254, true, true, true⟩ ∧
    (verdict { r1149 with T := 3790 }).exact = true ∧
    (verdict { r1149 with T := 3789 }).exact = false ∧
    (verdict { r1149 with T := 4104 }).bridge = true ∧
    (verdict { r1149 with T := 4103 }).bridge = false := by decide +kernel
theorem v1150 :
    verdict r1150 = ⟨true, true, 1, 2339, 24583, 20498, true, true, true⟩ ∧
    (verdict { r1150 with T := 2437 }).exact = true ∧
    (verdict { r1150 with T := 2436 }).exact = false ∧
    (verdict { r1150 with T := 2604 }).bridge = true ∧
    (verdict { r1150 with T := 2603 }).bridge = false := by decide +kernel
theorem v1151 :
    verdict r1151 = ⟨true, true, 1, 4256, 55658, 48022, true, true, true⟩ ∧
    (verdict { r1151 with T := 4380 }).exact = true ∧
    (verdict { r1151 with T := 4379 }).exact = false ∧
    (verdict { r1151 with T := 4741 }).bridge = true ∧
    (verdict { r1151 with T := 4740 }).bridge = false := by decide +kernel
theorem v1152 :
    verdict r1152 = ⟨true, true, 1, 1266, 21060, 16144, true, true, true⟩ ∧
    (verdict { r1152 with T := 1253 }).exact = true ∧
    (verdict { r1152 with T := 1252 }).exact = false ∧
    (verdict { r1152 with T := 1266 }).bridge = true ∧
    (verdict { r1152 with T := 1265 }).bridge = false := by decide +kernel
theorem v1153 :
    verdict r1153 = ⟨true, true, 1, 1463, 16205, 12416, true, true, true⟩ ∧
    (verdict { r1153 with T := 1827 }).exact = true ∧
    (verdict { r1153 with T := 1826 }).exact = false ∧
    (verdict { r1153 with T := 1827 }).bridge = true ∧
    (verdict { r1153 with T := 1826 }).bridge = false := by decide +kernel
theorem v1154 :
    verdict r1154 = ⟨true, true, 1, 838, 11547, 8767, true, true, true⟩ ∧
    (verdict { r1154 with T := 873 }).exact = true ∧
    (verdict { r1154 with T := 872 }).exact = false ∧
    (verdict { r1154 with T := 923 }).bridge = true ∧
    (verdict { r1154 with T := 922 }).bridge = false := by decide +kernel
theorem v1155 :
    verdict r1155 = ⟨true, true, 1, 1636, 26184, 20525, true, true, true⟩ ∧
    (verdict { r1155 with T := 2072 }).exact = true ∧
    (verdict { r1155 with T := 2071 }).exact = false ∧
    (verdict { r1155 with T := 2072 }).bridge = true ∧
    (verdict { r1155 with T := 2071 }).bridge = false := by decide +kernel
theorem v1156 :
    verdict r1156 = ⟨true, true, 1, 968, 8878, 6736, true, true, true⟩ ∧
    (verdict { r1156 with T := 1250 }).exact = true ∧
    (verdict { r1156 with T := 1249 }).exact = false ∧
    (verdict { r1156 with T := 1250 }).bridge = true ∧
    (verdict { r1156 with T := 1249 }).bridge = false := by decide +kernel
theorem v1157 :
    verdict r1157 = ⟨true, true, 1, 1890, 20198, 15831, true, true, true⟩ ∧
    (verdict { r1157 with T := 2880 }).exact = true ∧
    (verdict { r1157 with T := 2879 }).exact = false ∧
    (verdict { r1157 with T := 2880 }).bridge = true ∧
    (verdict { r1157 with T := 2879 }).bridge = false := by decide +kernel
theorem v1158 :
    verdict r1158 = ⟨true, true, 1, 845, 21571, 15948, true, true, true⟩ ∧
    (verdict { r1158 with T := 1543 }).exact = true ∧
    (verdict { r1158 with T := 1542 }).exact = false ∧
    (verdict { r1158 with T := 1543 }).bridge = true ∧
    (verdict { r1158 with T := 1542 }).bridge = false := by decide +kernel
theorem v1159 :
    verdict r1159 = ⟨true, true, 1, 977, 16598, 12265, true, true, true⟩ ∧
    (verdict { r1159 with T := 2057 }).exact = true ∧
    (verdict { r1159 with T := 2056 }).exact = false ∧
    (verdict { r1159 with T := 2057 }).bridge = true ∧
    (verdict { r1159 with T := 2056 }).bridge = false := by decide +kernel
theorem v1160 :
    verdict r1160 = ⟨true, true, 1, 561, 12110, 8589, true, true, true⟩ ∧
    (verdict { r1160 with T := 1350 }).exact = true ∧
    (verdict { r1160 with T := 1349 }).exact = false ∧
    (verdict { r1160 with T := 1350 }).bridge = true ∧
    (verdict { r1160 with T := 1349 }).bridge = false := by decide +kernel
theorem v1161 :
    verdict r1161 = ⟨true, true, 1, 1021, 26740, 19920, true, true, true⟩ ∧
    (verdict { r1161 with T := 3009 }).exact = true ∧
    (verdict { r1161 with T := 3008 }).exact = false ∧
    (verdict { r1161 with T := 3009 }).bridge = true ∧
    (verdict { r1161 with T := 3008 }).bridge = false := by decide +kernel
theorem v1162 :
    verdict r1162 = ⟨true, true, 1, 648, 9313, 6599, true, true, true⟩ ∧
    (verdict { r1162 with T := 1738 }).exact = true ∧
    (verdict { r1162 with T := 1737 }).exact = false ∧
    (verdict { r1162 with T := 1738 }).bridge = true ∧
    (verdict { r1162 with T := 1737 }).bridge = false := by decide +kernel
theorem v1163 :
    verdict r1163 = ⟨true, true, 1, 1180, 20628, 15365, true, true, true⟩ ∧
    (verdict { r1163 with T := 3799 }).exact = true ∧
    (verdict { r1163 with T := 3798 }).exact = false ∧
    (verdict { r1163 with T := 3799 }).bridge = true ∧
    (verdict { r1163 with T := 3798 }).bridge = false := by decide +kernel
theorem v1164 :
    verdict r1164 = ⟨true, true, 1, 833, 21607, 15813, true, true, true⟩ ∧
    (verdict { r1164 with T := 990 }).exact = true ∧
    (verdict { r1164 with T := 989 }).exact = false ∧
    (verdict { r1164 with T := 990 }).bridge = true ∧
    (verdict { r1164 with T := 989 }).bridge = false := by decide +kernel
theorem v1165 :
    verdict r1165 = ⟨true, true, 1, 963, 16626, 12161, true, true, true⟩ ∧
    (verdict { r1165 with T := 1414 }).exact = true ∧
    (verdict { r1165 with T := 1413 }).exact = false ∧
    (verdict { r1165 with T := 1414 }).bridge = true ∧
    (verdict { r1165 with T := 1413 }).bridge = false := by decide +kernel
theorem v1166 :
    verdict r1166 = ⟨true, true, 1, 728, 12181, 8579, true, true, true⟩ ∧
    (verdict { r1166 with T := 665 }).exact = true ∧
    (verdict { r1166 with T := 664 }).exact = false ∧
    (verdict { r1166 with T := 728 }).bridge = true ∧
    (verdict { r1166 with T := 727 }).bridge = false := by decide +kernel
theorem v1167 :
    verdict r1167 = ⟨true, true, 1, 1422, 27539, 20275, true, true, true⟩ ∧
    (verdict { r1167 with T := 1666 }).exact = true ∧
    (verdict { r1167 with T := 1665 }).exact = false ∧
    (verdict { r1167 with T := 1666 }).bridge = true ∧
    (verdict { r1167 with T := 1665 }).bridge = false := by decide +kernel
theorem v1168 :
    verdict r1168 = ⟨true, true, 1, 841, 9367, 6591, true, true, true⟩ ∧
    (verdict { r1168 with T := 913 }).exact = true ∧
    (verdict { r1168 with T := 912 }).exact = false ∧
    (verdict { r1168 with T := 913 }).bridge = true ∧
    (verdict { r1168 with T := 912 }).bridge = false := by decide +kernel
theorem v1169 :
    verdict r1169 = ⟨true, true, 1, 1643, 21242, 15636, true, true, true⟩ ∧
    (verdict { r1169 with T := 2234 }).exact = true ∧
    (verdict { r1169 with T := 2233 }).exact = false ∧
    (verdict { r1169 with T := 2234 }).bridge = true ∧
    (verdict { r1169 with T := 2233 }).bridge = false := by decide +kernel
theorem v1170 :
    verdict r1170 = ⟨true, true, 1, 841, 21224, 15513, true, true, true⟩ ∧
    (verdict { r1170 with T := 838 }).exact = true ∧
    (verdict { r1170 with T := 837 }).exact = false ∧
    (verdict { r1170 with T := 977 }).bridge = true ∧
    (verdict { r1170 with T := 976 }).bridge = false := by decide +kernel
theorem v1171 :
    verdict r1171 = ⟨true, true, 1, 972, 16331, 11929, true, true, true⟩ ∧
    (verdict { r1171 with T := 1290 }).exact = true ∧
    (verdict { r1171 with T := 1289 }).exact = false ∧
    (verdict { r1171 with T := 1290 }).bridge = true ∧
    (verdict { r1171 with T := 1289 }).bridge = false := by decide +kernel
theorem v1172 :
    verdict r1172 = ⟨true, true, 1, 629, 11442, 8037, true, true, true⟩ ∧
    (verdict { r1172 with T := 760 }).exact = true ∧
    (verdict { r1172 with T := 759 }).exact = false ∧
    (verdict { r1172 with T := 760 }).bridge = true ∧
    (verdict { r1172 with T := 759 }).bridge = false := by decide +kernel
theorem v1173 :
    verdict r1173 = ⟨true, true, 1, 1248, 25610, 18990, true, true, true⟩ ∧
    (verdict { r1173 with T := 1815 }).exact = true ∧
    (verdict { r1173 with T := 1814 }).exact = false ∧
    (verdict { r1173 with T := 1815 }).bridge = true ∧
    (verdict { r1173 with T := 1814 }).bridge = false := by decide +kernel
theorem v1174 :
    verdict r1174 = ⟨true, true, 1, 726, 8796, 6173, true, true, true⟩ ∧
    (verdict { r1174 with T := 1047 }).exact = true ∧
    (verdict { r1174 with T := 1046 }).exact = false ∧
    (verdict { r1174 with T := 1047 }).bridge = true ∧
    (verdict { r1174 with T := 1046 }).bridge = false := by decide +kernel
theorem v1175 :
    verdict r1175 = ⟨true, true, 1, 1442, 19755, 14646, true, true, true⟩ ∧
    (verdict { r1175 with T := 2511 }).exact = true ∧
    (verdict { r1175 with T := 2510 }).exact = false ∧
    (verdict { r1175 with T := 2511 }).bridge = true ∧
    (verdict { r1175 with T := 2510 }).bridge = false := by decide +kernel
theorem v1176 :
    verdict r1176 = ⟨true, true, 1, 713, 19424, 15577, true, true, true⟩ ∧
    (verdict { r1176 with T := 1091 }).exact = true ∧
    (verdict { r1176 with T := 1090 }).exact = false ∧
    (verdict { r1176 with T := 1091 }).bridge = true ∧
    (verdict { r1176 with T := 1090 }).bridge = false := by decide +kernel
theorem v1177 :
    verdict r1177 = ⟨true, true, 1, 825, 14940, 11979, true, true, true⟩ ∧
    (verdict { r1177 with T := 1484 }).exact = true ∧
    (verdict { r1177 with T := 1483 }).exact = false ∧
    (verdict { r1177 with T := 1484 }).bridge = true ∧
    (verdict { r1177 with T := 1483 }).bridge = false := by decide +kernel
theorem v1178 :
    verdict r1178 = ⟨true, true, 1, 413, 11131, 8944, true, true, true⟩ ∧
    (verdict { r1178 with T := 855 }).exact = true ∧
    (verdict { r1178 with T := 854 }).exact = false ∧
    (verdict { r1178 with T := 855 }).bridge = true ∧
    (verdict { r1178 with T := 854 }).bridge = false := by decide +kernel
theorem v1179 :
    verdict r1179 = ⟨true, true, 1, 801, 25779, 21019, true, true, true⟩ ∧
    (verdict { r1179 with T := 2123 }).exact = true ∧
    (verdict { r1179 with T := 2122 }).exact = false ∧
    (verdict { r1179 with T := 2123 }).bridge = true ∧
    (verdict { r1179 with T := 2122 }).bridge = false := by decide +kernel
theorem v1180 :
    verdict r1180 = ⟨true, true, 1, 477, 8558, 6874, true, true, true⟩ ∧
    (verdict { r1180 with T := 1107 }).exact = true ∧
    (verdict { r1180 with T := 1106 }).exact = false ∧
    (verdict { r1180 with T := 1107 }).bridge = true ∧
    (verdict { r1180 with T := 1106 }).bridge = false := by decide +kernel
theorem v1181 :
    verdict r1181 = ⟨true, true, 1, 926, 19885, 16212, true, true, true⟩ ∧
    (verdict { r1181 with T := 2654 }).exact = true ∧
    (verdict { r1181 with T := 2653 }).exact = false ∧
    (verdict { r1181 with T := 2654 }).bridge = true ∧
    (verdict { r1181 with T := 2653 }).bridge = false := by decide +kernel
theorem v1182 :
    verdict r1182 = ⟨true, true, 1, 856, 20759, 15683, true, true, true⟩ ∧
    (verdict { r1182 with T := 1146 }).exact = true ∧
    (verdict { r1182 with T := 1145 }).exact = false ∧
    (verdict { r1182 with T := 1146 }).bridge = true ∧
    (verdict { r1182 with T := 1145 }).bridge = false := by decide +kernel
theorem v1183 :
    verdict r1183 = ⟨true, true, 1, 990, 15973, 12061, true, true, true⟩ ∧
    (verdict { r1183 with T := 1649 }).exact = true ∧
    (verdict { r1183 with T := 1648 }).exact = false ∧
    (verdict { r1183 with T := 1649 }).bridge = true ∧
    (verdict { r1183 with T := 1648 }).bridge = false := by decide +kernel
theorem v1184 :
    verdict r1184 = ⟨true, true, 1, 597, 11482, 8780, true, true, true⟩ ∧
    (verdict { r1184 with T := 918 }).exact = true ∧
    (verdict { r1184 with T := 917 }).exact = false ∧
    (verdict { r1184 with T := 918 }).bridge = true ∧
    (verdict { r1184 with T := 917 }).bridge = false := by decide +kernel
theorem v1185 :
    verdict r1185 = ⟨true, true, 1, 1309, 26613, 20686, true, true, true⟩ ∧
    (verdict { r1185 with T := 2233 }).exact = true ∧
    (verdict { r1185 with T := 2232 }).exact = false ∧
    (verdict { r1185 with T := 2233 }).bridge = true ∧
    (verdict { r1185 with T := 2232 }).bridge = false := by decide +kernel
theorem v1186 :
    verdict r1186 = ⟨true, true, 1, 690, 8828, 6747, true, true, true⟩ ∧
    (verdict { r1186 with T := 1226 }).exact = true ∧
    (verdict { r1186 with T := 1225 }).exact = false ∧
    (verdict { r1186 with T := 1226 }).bridge = true ∧
    (verdict { r1186 with T := 1225 }).bridge = false := by decide +kernel
theorem v1187 :
    verdict r1187 = ⟨true, true, 1, 1513, 20530, 15956, true, true, true⟩ ∧
    (verdict { r1187 with T := 3028 }).exact = true ∧
    (verdict { r1187 with T := 3027 }).exact = false ∧
    (verdict { r1187 with T := 3028 }).bridge = true ∧
    (verdict { r1187 with T := 3027 }).bridge = false := by decide +kernel

end Formal.Timing.ChainSettleExe.GcdD
