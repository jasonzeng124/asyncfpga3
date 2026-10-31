import Formal.Timing.ChainSettleExeGcdDData4

/-! C-10o2 GENERATED: kernel-decided verdicts of chunk 4 (see ChainSettleExe.verdict).
Per row: `verdict` at chainck's late side `T`; exact PASS at `T*` and FAIL at `T* - 1`
(margin_exact = T - T*); bridge PASS at `Tb*` and FAIL at `Tb* - 1`. -/

namespace Formal.Timing.ChainSettleExe.GcdD
open Formal.Timing Formal.Timing.ChainSettleExe

theorem v600 :
    verdict r600 = ⟨true, true, 1, 1859, 13892, 3812, true, true, true⟩ ∧
    (verdict { r600 with T := 1594 }).exact = true ∧
    (verdict { r600 with T := 1593 }).exact = false ∧
    (verdict { r600 with T := 1859 }).bridge = true ∧
    (verdict { r600 with T := 1858 }).bridge = false := by decide +kernel
theorem v601 :
    verdict r601 = ⟨true, true, 1, 2148, 10703, 2934, true, true, true⟩ ∧
    (verdict { r601 with T := 1841 }).exact = true ∧
    (verdict { r601 with T := 1840 }).exact = false ∧
    (verdict { r601 with T := 2148 }).bridge = true ∧
    (verdict { r601 with T := 2147 }).bridge = false := by decide +kernel
theorem v602 :
    verdict r602 = ⟨true, true, 1, 1235, 7615, 2298, true, true, true⟩ ∧
    (verdict { r602 with T := 1222 }).exact = true ∧
    (verdict { r602 with T := 1221 }).exact = false ∧
    (verdict { r602 with T := 1266 }).bridge = true ∧
    (verdict { r602 with T := 1265 }).bridge = false := by decide +kernel
theorem v603 :
    verdict r603 = ⟨true, true, 1, 2344, 16265, 4858, true, true, true⟩ ∧
    (verdict { r603 with T := 2314 }).exact = true ∧
    (verdict { r603 with T := 2313 }).exact = false ∧
    (verdict { r603 with T := 2429 }).bridge = true ∧
    (verdict { r603 with T := 2428 }).bridge = false := by decide +kernel
theorem v604 :
    verdict r604 = ⟨true, true, 1, 1427, 5866, 1768, true, true, true⟩ ∧
    (verdict { r604 with T := 1411 }).exact = true ∧
    (verdict { r604 with T := 1410 }).exact = false ∧
    (verdict { r604 with T := 1463 }).bridge = true ∧
    (verdict { r604 with T := 1462 }).bridge = false := by decide +kernel
theorem v605 :
    verdict r605 = ⟨true, true, 1, 2708, 12553, 3749, true, true, true⟩ ∧
    (verdict { r605 with T := 2672 }).exact = true ∧
    (verdict { r605 with T := 2671 }).exact = false ∧
    (verdict { r605 with T := 2807 }).bridge = true ∧
    (verdict { r605 with T := 2806 }).bridge = false := by decide +kernel
theorem v606 :
    verdict r606 = ⟨true, true, 1, 958, 6865, 2839, true, true, true⟩ ∧
    (verdict { r606 with T := 621 }).exact = true ∧
    (verdict { r606 with T := 620 }).exact = false ∧
    (verdict { r606 with T := 958 }).bridge = true ∧
    (verdict { r606 with T := 957 }).bridge = false := by decide +kernel
theorem v607 :
    verdict r607 = ⟨true, true, 1, 1108, 5283, 2183, true, true, true⟩ ∧
    (verdict { r607 with T := 797 }).exact = true ∧
    (verdict { r607 with T := 796 }).exact = false ∧
    (verdict { r607 with T := 1108 }).bridge = true ∧
    (verdict { r607 with T := 1107 }).bridge = false := by decide +kernel
theorem v608 :
    verdict r608 = ⟨true, true, 1, 714, 3689, 1430, true, true, true⟩ ∧
    (verdict { r608 with T := 453 }).exact = true ∧
    (verdict { r608 with T := 452 }).exact = false ∧
    (verdict { r608 with T := 714 }).bridge = true ∧
    (verdict { r608 with T := 713 }).bridge = false := by decide +kernel
theorem v609 :
    verdict r609 = ⟨true, true, 1, 1476, 8279, 3246, true, true, true⟩ ∧
    (verdict { r609 with T := 1002 }).exact = true ∧
    (verdict { r609 with T := 1001 }).exact = false ∧
    (verdict { r609 with T := 1476 }).bridge = true ∧
    (verdict { r609 with T := 1475 }).bridge = false := by decide +kernel
theorem v610 :
    verdict r610 = ⟨true, true, 1, 825, 2837, 1099, true, true, true⟩ ∧
    (verdict { r610 with T := 665 }).exact = true ∧
    (verdict { r610 with T := 664 }).exact = false ∧
    (verdict { r610 with T := 825 }).bridge = true ∧
    (verdict { r610 with T := 824 }).bridge = false := by decide +kernel
theorem v611 :
    verdict r611 = ⟨true, true, 1, 1705, 6387, 2504, true, true, true⟩ ∧
    (verdict { r611 with T := 1398 }).exact = true ∧
    (verdict { r611 with T := 1397 }).exact = false ∧
    (verdict { r611 with T := 1736 }).bridge = true ∧
    (verdict { r611 with T := 1735 }).bridge = false := by decide +kernel
theorem v612 :
    verdict r612 = ⟨true, true, 1, 890, 10150, 2984, true, true, true⟩ ∧
    (verdict { r612 with T := 979 }).exact = true ∧
    (verdict { r612 with T := 978 }).exact = false ∧
    (verdict { r612 with T := 1102 }).bridge = true ∧
    (verdict { r612 with T := 1101 }).bridge = false := by decide +kernel
theorem v613 :
    verdict r613 = ⟨true, true, 1, 1029, 7817, 2295, true, true, true⟩ ∧
    (verdict { r613 with T := 1131 }).exact = true ∧
    (verdict { r613 with T := 1130 }).exact = false ∧
    (verdict { r613 with T := 1274 }).bridge = true ∧
    (verdict { r613 with T := 1273 }).bridge = false := by decide +kernel
theorem v614 :
    verdict r614 = ⟨true, true, 1, 750, 6241, 1652, true, true, true⟩ ∧
    (verdict { r614 with T := 797 }).exact = true ∧
    (verdict { r614 with T := 796 }).exact = false ∧
    (verdict { r614 with T := 853 }).bridge = true ∧
    (verdict { r614 with T := 852 }).bridge = false := by decide +kernel
theorem v615 :
    verdict r615 = ⟨true, true, 1, 1488, 12969, 3665, true, true, true⟩ ∧
    (verdict { r615 with T := 1587 }).exact = true ∧
    (verdict { r615 with T := 1586 }).exact = false ∧
    (verdict { r615 with T := 1712 }).bridge = true ∧
    (verdict { r615 with T := 1711 }).bridge = false := by decide +kernel
theorem v616 :
    verdict r616 = ⟨true, true, 1, 866, 4805, 1271, true, true, true⟩ ∧
    (verdict { r616 with T := 921 }).exact = true ∧
    (verdict { r616 with T := 920 }).exact = false ∧
    (verdict { r616 with T := 985 }).bridge = true ∧
    (verdict { r616 with T := 984 }).bridge = false := by decide +kernel
theorem v617 :
    verdict r617 = ⟨true, true, 1, 1719, 10007, 2827, true, true, true⟩ ∧
    (verdict { r617 with T := 1846 }).exact = true ∧
    (verdict { r617 with T := 1845 }).exact = false ∧
    (verdict { r617 with T := 1978 }).bridge = true ∧
    (verdict { r617 with T := 1977 }).bridge = false := by decide +kernel
theorem v618 :
    verdict r618 = ⟨true, true, 1, 1375, 12297, 3469, true, true, true⟩ ∧
    (verdict { r618 with T := 1251 }).exact = true ∧
    (verdict { r618 with T := 1250 }).exact = false ∧
    (verdict { r618 with T := 1375 }).bridge = true ∧
    (verdict { r618 with T := 1374 }).bridge = false := by decide +kernel
theorem v619 :
    verdict r619 = ⟨true, true, 1, 1589, 9472, 2670, true, true, true⟩ ∧
    (verdict { r619 with T := 1445 }).exact = true ∧
    (verdict { r619 with T := 1444 }).exact = false ∧
    (verdict { r619 with T := 1589 }).bridge = true ∧
    (verdict { r619 with T := 1588 }).bridge = false := by decide +kernel
theorem v620 :
    verdict r620 = ⟨true, true, 1, 1151, 7712, 2027, true, true, true⟩ ∧
    (verdict { r620 with T := 1100 }).exact = true ∧
    (verdict { r620 with T := 1099 }).exact = false ∧
    (verdict { r620 with T := 1240 }).bridge = true ∧
    (verdict { r620 with T := 1239 }).bridge = false := by decide +kernel
theorem v621 :
    verdict r621 = ⟨true, true, 1, 2042, 15544, 4157, true, true, true⟩ ∧
    (verdict { r621 with T := 2090 }).exact = true ∧
    (verdict { r621 with T := 2089 }).exact = false ∧
    (verdict { r621 with T := 2232 }).bridge = true ∧
    (verdict { r621 with T := 2231 }).bridge = false := by decide +kernel
theorem v622 :
    verdict r622 = ⟨true, true, 1, 1329, 5938, 1560, true, true, true⟩ ∧
    (verdict { r622 with T := 1368 }).exact = true ∧
    (verdict { r622 with T := 1367 }).exact = false ∧
    (verdict { r622 with T := 1432 }).bridge = true ∧
    (verdict { r622 with T := 1431 }).bridge = false := by decide +kernel
theorem v623 :
    verdict r623 = ⟨true, true, 1, 2359, 11993, 3207, true, true, true⟩ ∧
    (verdict { r623 with T := 2435 }).exact = true ∧
    (verdict { r623 with T := 2434 }).exact = false ∧
    (verdict { r623 with T := 2578 }).bridge = true ∧
    (verdict { r623 with T := 2577 }).bridge = false := by decide +kernel
theorem v624 :
    verdict r624 = ⟨true, true, 1, 762, 10816, 3069, true, true, true⟩ ∧
    (verdict { r624 with T := 638 }).exact = true ∧
    (verdict { r624 with T := 637 }).exact = false ∧
    (verdict { r624 with T := 762 }).bridge = true ∧
    (verdict { r624 with T := 761 }).bridge = false := by decide +kernel
theorem v625 :
    verdict r625 = ⟨true, true, 1, 881, 8328, 2361, true, true, true⟩ ∧
    (verdict { r625 with T := 1025 }).exact = true ∧
    (verdict { r625 with T := 1024 }).exact = false ∧
    (verdict { r625 with T := 1025 }).bridge = true ∧
    (verdict { r625 with T := 1024 }).bridge = false := by decide +kernel
theorem v626 :
    verdict r626 = ⟨true, true, 1, 499, 6471, 1608, true, true, true⟩ ∧
    (verdict { r626 with T := 587 }).exact = true ∧
    (verdict { r626 with T := 586 }).exact = false ∧
    (verdict { r626 with T := 588 }).bridge = true ∧
    (verdict { r626 with T := 587 }).bridge = false := by decide +kernel
theorem v627 :
    verdict r627 = ⟨true, true, 1, 1066, 13969, 3706, true, true, true⟩ ∧
    (verdict { r627 with T := 1364 }).exact = true ∧
    (verdict { r627 with T := 1363 }).exact = false ∧
    (verdict { r627 with T := 1364 }).bridge = true ∧
    (verdict { r627 with T := 1363 }).bridge = false := by decide +kernel
theorem v628 :
    verdict r628 = ⟨true, true, 1, 576, 4979, 1236, true, true, true⟩ ∧
    (verdict { r628 with T := 842 }).exact = true ∧
    (verdict { r628 with T := 841 }).exact = false ∧
    (verdict { r628 with T := 842 }).bridge = true ∧
    (verdict { r628 with T := 841 }).bridge = false := by decide +kernel
theorem v629 :
    verdict r629 = ⟨true, true, 1, 1231, 10778, 2859, true, true, true⟩ ∧
    (verdict { r629 with T := 1918 }).exact = true ∧
    (verdict { r629 with T := 1917 }).exact = false ∧
    (verdict { r629 with T := 1918 }).bridge = true ∧
    (verdict { r629 with T := 1917 }).bridge = false := by decide +kernel
theorem v630 :
    verdict r630 = ⟨true, true, 1, 904, 8402, 2998, true, true, true⟩ ∧
    (verdict { r630 with T := 780 }).exact = true ∧
    (verdict { r630 with T := 779 }).exact = false ∧
    (verdict { r630 with T := 904 }).bridge = true ∧
    (verdict { r630 with T := 903 }).bridge = false := by decide +kernel
theorem v631 :
    verdict r631 = ⟨true, true, 1, 1045, 6469, 2306, true, true, true⟩ ∧
    (verdict { r631 with T := 901 }).exact = true ∧
    (verdict { r631 with T := 900 }).exact = false ∧
    (verdict { r631 with T := 1045 }).bridge = true ∧
    (verdict { r631 with T := 1044 }).bridge = false := by decide +kernel
theorem v632 :
    verdict r632 = ⟨true, true, 1, 701, 4975, 1536, true, true, true⟩ ∧
    (verdict { r632 with T := 735 }).exact = true ∧
    (verdict { r632 with T := 734 }).exact = false ∧
    (verdict { r632 with T := 790 }).bridge = true ∧
    (verdict { r632 with T := 789 }).bridge = false := by decide +kernel
theorem v633 :
    verdict r633 = ⟨true, true, 1, 1344, 10748, 3339, true, true, true⟩ ∧
    (verdict { r633 with T := 1411 }).exact = true ∧
    (verdict { r633 with T := 1410 }).exact = false ∧
    (verdict { r633 with T := 1534 }).bridge = true ∧
    (verdict { r633 with T := 1533 }).bridge = false := by decide +kernel
theorem v634 :
    verdict r634 = ⟨true, true, 1, 810, 3831, 1181, true, true, true⟩ ∧
    (verdict { r634 with T := 928 }).exact = true ∧
    (verdict { r634 with T := 927 }).exact = false ∧
    (verdict { r634 with T := 928 }).bridge = true ∧
    (verdict { r634 with T := 927 }).bridge = false := by decide +kernel
theorem v635 :
    verdict r635 = ⟨true, true, 1, 1553, 8295, 2576, true, true, true⟩ ∧
    (verdict { r635 with T := 2041 }).exact = true ∧
    (verdict { r635 with T := 2040 }).exact = false ∧
    (verdict { r635 with T := 2041 }).bridge = true ∧
    (verdict { r635 with T := 2040 }).bridge = false := by decide +kernel
theorem v636 :
    verdict r636 = ⟨true, true, 1, 1083, 7846, 3249, true, true, true⟩ ∧
    (verdict { r636 with T := 818 }).exact = true ∧
    (verdict { r636 with T := 817 }).exact = false ∧
    (verdict { r636 with T := 1083 }).bridge = true ∧
    (verdict { r636 with T := 1082 }).bridge = false := by decide +kernel
theorem v637 :
    verdict r637 = ⟨true, true, 1, 1252, 6041, 2500, true, true, true⟩ ∧
    (verdict { r637 with T := 1094 }).exact = true ∧
    (verdict { r637 with T := 1093 }).exact = false ∧
    (verdict { r637 with T := 1252 }).bridge = true ∧
    (verdict { r637 with T := 1251 }).bridge = false := by decide +kernel
theorem v638 :
    verdict r638 = ⟨true, true, 1, 957, 5051, 2066, true, true, true⟩ ∧
    (verdict { r638 with T := 822 }).exact = true ∧
    (verdict { r638 with T := 821 }).exact = false ∧
    (verdict { r638 with T := 957 }).bridge = true ∧
    (verdict { r638 with T := 956 }).bridge = false := by decide +kernel
theorem v639 :
    verdict r639 = ⟨true, true, 1, 1893, 10817, 4562, true, true, true⟩ ∧
    (verdict { r639 with T := 1615 }).exact = true ∧
    (verdict { r639 with T := 1614 }).exact = false ∧
    (verdict { r639 with T := 1893 }).bridge = true ∧
    (verdict { r639 with T := 1892 }).bridge = false := by decide +kernel
theorem v640 :
    verdict r640 = ⟨true, true, 1, 1106, 3890, 1589, true, true, true⟩ ∧
    (verdict { r640 with T := 997 }).exact = true ∧
    (verdict { r640 with T := 996 }).exact = false ∧
    (verdict { r640 with T := 1106 }).bridge = true ∧
    (verdict { r640 with T := 1105 }).bridge = false := by decide +kernel
theorem v641 :
    verdict r641 = ⟨true, true, 1, 2187, 8347, 3518, true, true, true⟩ ∧
    (verdict { r641 with T := 2245 }).exact = true ∧
    (verdict { r641 with T := 2244 }).exact = false ∧
    (verdict { r641 with T := 2245 }).bridge = true ∧
    (verdict { r641 with T := 2244 }).bridge = false := by decide +kernel
theorem v642 :
    verdict r642 = ⟨true, true, 1, 827, 6866, 2921, true, true, true⟩ ∧
    (verdict { r642 with T := 703 }).exact = true ∧
    (verdict { r642 with T := 702 }).exact = false ∧
    (verdict { r642 with T := 827 }).bridge = true ∧
    (verdict { r642 with T := 826 }).bridge = false := by decide +kernel
theorem v643 :
    verdict r643 = ⟨true, true, 1, 956, 5282, 2246, true, true, true⟩ ∧
    (verdict { r643 with T := 812 }).exact = true ∧
    (verdict { r643 with T := 811 }).exact = false ∧
    (verdict { r643 with T := 956 }).bridge = true ∧
    (verdict { r643 with T := 955 }).bridge = false := by decide +kernel
theorem v644 :
    verdict r644 = ⟨true, true, 1, 612, 3573, 1518, true, true, true⟩ ∧
    (verdict { r644 with T := 568 }).exact = true ∧
    (verdict { r644 with T := 567 }).exact = false ∧
    (verdict { r644 with T := 617 }).bridge = true ∧
    (verdict { r644 with T := 616 }).bridge = false := by decide +kernel
theorem v645 :
    verdict r645 = ⟨true, true, 1, 1310, 8109, 3475, true, true, true⟩ ∧
    (verdict { r645 with T := 1216 }).exact = true ∧
    (verdict { r645 with T := 1215 }).exact = false ∧
    (verdict { r645 with T := 1312 }).bridge = true ∧
    (verdict { r645 with T := 1311 }).bridge = false := by decide +kernel
theorem v646 :
    verdict r646 = ⟨true, true, 1, 707, 2747, 1167, true, true, true⟩ ∧
    (verdict { r646 with T := 801 }).exact = true ∧
    (verdict { r646 with T := 800 }).exact = false ∧
    (verdict { r646 with T := 801 }).bridge = true ∧
    (verdict { r646 with T := 800 }).bridge = false := by decide +kernel
theorem v647 :
    verdict r647 = ⟨true, true, 1, 1514, 6256, 2681, true, true, true⟩ ∧
    (verdict { r647 with T := 1824 }).exact = true ∧
    (verdict { r647 with T := 1823 }).exact = false ∧
    (verdict { r647 with T := 1824 }).bridge = true ∧
    (verdict { r647 with T := 1823 }).bridge = false := by decide +kernel
theorem v648 :
    verdict r648 = ⟨true, true, 1, 1087, 7722, 3041, true, true, true⟩ ∧
    (verdict { r648 with T := 823 }).exact = true ∧
    (verdict { r648 with T := 822 }).exact = false ∧
    (verdict { r648 with T := 1087 }).bridge = true ∧
    (verdict { r648 with T := 1086 }).bridge = false := by decide +kernel
theorem v649 :
    verdict r649 = ⟨true, true, 1, 1257, 5944, 2339, true, true, true⟩ ∧
    (verdict { r649 with T := 1113 }).exact = true ∧
    (verdict { r649 with T := 1112 }).exact = false ∧
    (verdict { r649 with T := 1257 }).bridge = true ∧
    (verdict { r649 with T := 1256 }).bridge = false := by decide +kernel
theorem v650 :
    verdict r650 = ⟨true, true, 1, 854, 4212, 1487, true, true, true⟩ ∧
    (verdict { r650 with T := 604 }).exact = true ∧
    (verdict { r650 with T := 603 }).exact = false ∧
    (verdict { r650 with T := 854 }).bridge = true ∧
    (verdict { r650 with T := 853 }).bridge = false := by decide +kernel
theorem v651 :
    verdict r651 = ⟨true, true, 1, 1814, 9318, 3385, true, true, true⟩ ∧
    (verdict { r651 with T := 1487 }).exact = true ∧
    (verdict { r651 with T := 1486 }).exact = false ∧
    (verdict { r651 with T := 1814 }).bridge = true ∧
    (verdict { r651 with T := 1813 }).bridge = false := by decide +kernel
theorem v652 :
    verdict r652 = ⟨true, true, 1, 987, 3243, 1143, true, true, true⟩ ∧
    (verdict { r652 with T := 838 }).exact = true ∧
    (verdict { r652 with T := 837 }).exact = false ∧
    (verdict { r652 with T := 987 }).bridge = true ∧
    (verdict { r652 with T := 986 }).bridge = false := by decide +kernel
theorem v653 :
    verdict r653 = ⟨true, true, 1, 2096, 7190, 2611, true, true, true⟩ ∧
    (verdict { r653 with T := 1789 }).exact = true ∧
    (verdict { r653 with T := 1788 }).exact = false ∧
    (verdict { r653 with T := 2096 }).bridge = true ∧
    (verdict { r653 with T := 2095 }).bridge = false := by decide +kernel
theorem v654 :
    verdict r654 = ⟨true, true, 1, 1253, 7373, 3134, true, true, true⟩ ∧
    (verdict { r654 with T := 916 }).exact = true ∧
    (verdict { r654 with T := 915 }).exact = false ∧
    (verdict { r654 with T := 1253 }).bridge = true ∧
    (verdict { r654 with T := 1252 }).bridge = false := by decide +kernel
theorem v655 :
    verdict r655 = ⟨true, true, 1, 1448, 5675, 2411, true, true, true⟩ ∧
    (verdict { r655 with T := 1304 }).exact = true ∧
    (verdict { r655 with T := 1303 }).exact = false ∧
    (verdict { r655 with T := 1448 }).bridge = true ∧
    (verdict { r655 with T := 1447 }).bridge = false := by decide +kernel
theorem v656 :
    verdict r656 = ⟨true, true, 1, 792, 3972, 1735, true, true, true⟩ ∧
    (verdict { r656 with T := 702 }).exact = true ∧
    (verdict { r656 with T := 701 }).exact = false ∧
    (verdict { r656 with T := 792 }).bridge = true ∧
    (verdict { r656 with T := 791 }).bridge = false := by decide +kernel
theorem v657 :
    verdict r657 = ⟨true, true, 1, 1712, 8928, 3929, true, true, true⟩ ∧
    (verdict { r657 with T := 1686 }).exact = true ∧
    (verdict { r657 with T := 1685 }).exact = false ∧
    (verdict { r657 with T := 1712 }).bridge = true ∧
    (verdict { r657 with T := 1711 }).bridge = false := by decide +kernel
theorem v658 :
    verdict r658 = ⟨true, true, 1, 915, 3055, 1334, true, true, true⟩ ∧
    (verdict { r658 with T := 986 }).exact = true ∧
    (verdict { r658 with T := 985 }).exact = false ∧
    (verdict { r658 with T := 986 }).bridge = true ∧
    (verdict { r658 with T := 985 }).bridge = false := by decide +kernel
theorem v659 :
    verdict r659 = ⟨true, true, 1, 1978, 6889, 3030, true, true, true⟩ ∧
    (verdict { r659 with T := 2295 }).exact = true ∧
    (verdict { r659 with T := 2294 }).exact = false ∧
    (verdict { r659 with T := 2295 }).bridge = true ∧
    (verdict { r659 with T := 2294 }).bridge = false := by decide +kernel
theorem v660 :
    verdict r660 = ⟨true, true, 1, 874, 7251, 2968, true, true, true⟩ ∧
    (verdict { r660 with T := 852 }).exact = true ∧
    (verdict { r660 with T := 851 }).exact = false ∧
    (verdict { r660 with T := 1086 }).bridge = true ∧
    (verdict { r660 with T := 1085 }).bridge = false := by decide +kernel
theorem v661 :
    verdict r661 = ⟨true, true, 1, 1011, 5581, 2283, true, true, true⟩ ∧
    (verdict { r661 with T := 1113 }).exact = true ∧
    (verdict { r661 with T := 1112 }).exact = false ∧
    (verdict { r661 with T := 1256 }).bridge = true ∧
    (verdict { r661 with T := 1255 }).bridge = false := by decide +kernel
theorem v662 :
    verdict r662 = ⟨true, true, 1, 732, 4082, 1690, true, true, true⟩ ∧
    (verdict { r662 with T := 675 }).exact = true ∧
    (verdict { r662 with T := 674 }).exact = false ∧
    (verdict { r662 with T := 811 }).bridge = true ∧
    (verdict { r662 with T := 810 }).bridge = false := by decide +kernel
theorem v663 :
    verdict r663 = ⟨true, true, 1, 1442, 8900, 3730, true, true, true⟩ ∧
    (verdict { r663 with T := 1305 }).exact = true ∧
    (verdict { r663 with T := 1304 }).exact = false ∧
    (verdict { r663 with T := 1640 }).bridge = true ∧
    (verdict { r663 with T := 1639 }).bridge = false := by decide +kernel
theorem v664 :
    verdict r664 = ⟨true, true, 1, 845, 3140, 1300, true, true, true⟩ ∧
    (verdict { r664 with T := 793 }).exact = true ∧
    (verdict { r664 with T := 792 }).exact = false ∧
    (verdict { r664 with T := 938 }).bridge = true ∧
    (verdict { r664 with T := 937 }).bridge = false := by decide +kernel
theorem v665 :
    verdict r665 = ⟨true, true, 1, 1666, 6867, 2877, true, true, true⟩ ∧
    (verdict { r665 with T := 1752 }).exact = true ∧
    (verdict { r665 with T := 1751 }).exact = false ∧
    (verdict { r665 with T := 1895 }).bridge = true ∧
    (verdict { r665 with T := 1894 }).bridge = false := by decide +kernel
theorem v666 :
    verdict r666 = ⟨true, true, 1, 1549, 9244, 3783, true, true, true⟩ ∧
    (verdict { r666 with T := 1425 }).exact = true ∧
    (verdict { r666 with T := 1424 }).exact = false ∧
    (verdict { r666 with T := 1549 }).bridge = true ∧
    (verdict { r666 with T := 1548 }).bridge = false := by decide +kernel
theorem v667 :
    verdict r667 = ⟨true, true, 1, 1790, 7120, 2912, true, true, true⟩ ∧
    (verdict { r667 with T := 1646 }).exact = true ∧
    (verdict { r667 with T := 1645 }).exact = false ∧
    (verdict { r667 with T := 1790 }).bridge = true ∧
    (verdict { r667 with T := 1789 }).bridge = false := by decide +kernel
theorem v668 :
    verdict r668 = ⟨true, true, 1, 1251, 5671, 2457, true, true, true⟩ ∧
    (verdict { r668 with T := 1368 }).exact = true ∧
    (verdict { r668 with T := 1367 }).exact = false ∧
    (verdict { r668 with T := 1433 }).bridge = true ∧
    (verdict { r668 with T := 1432 }).bridge = false := by decide +kernel
theorem v669 :
    verdict r669 = ⟨true, true, 1, 2098, 11287, 4972, true, true, true⟩ ∧
    (verdict { r669 with T := 2379 }).exact = true ∧
    (verdict { r669 with T := 2378 }).exact = false ∧
    (verdict { r669 with T := 2521 }).bridge = true ∧
    (verdict { r669 with T := 2520 }).bridge = false := by decide +kernel
theorem v670 :
    verdict r670 = ⟨true, true, 1, 1445, 4367, 1891, true, true, true⟩ ∧
    (verdict { r670 with T := 1583 }).exact = true ∧
    (verdict { r670 with T := 1582 }).exact = false ∧
    (verdict { r670 with T := 1655 }).bridge = true ∧
    (verdict { r670 with T := 1654 }).bridge = false := by decide +kernel
theorem v671 :
    verdict r671 = ⟨true, true, 1, 2423, 8708, 3836, true, true, true⟩ ∧
    (verdict { r671 with T := 2769 }).exact = true ∧
    (verdict { r671 with T := 2768 }).exact = false ∧
    (verdict { r671 with T := 2912 }).bridge = true ∧
    (verdict { r671 with T := 2911 }).bridge = false := by decide +kernel
theorem v672 :
    verdict r672 = ⟨true, true, 1, 1033, 6309, 2987, true, true, true⟩ ∧
    (verdict { r672 with T := 909 }).exact = true ∧
    (verdict { r672 with T := 908 }).exact = false ∧
    (verdict { r672 with T := 1033 }).bridge = true ∧
    (verdict { r672 with T := 1032 }).bridge = false := by decide +kernel
theorem v673 :
    verdict r673 = ⟨true, true, 1, 1194, 4854, 2297, true, true, true⟩ ∧
    (verdict { r673 with T := 1050 }).exact = true ∧
    (verdict { r673 with T := 1049 }).exact = false ∧
    (verdict { r673 with T := 1194 }).bridge = true ∧
    (verdict { r673 with T := 1193 }).bridge = false := by decide +kernel
theorem v674 :
    verdict r674 = ⟨true, true, 1, 655, 3744, 1903, true, true, true⟩ ∧
    (verdict { r674 with T := 709 }).exact = true ∧
    (verdict { r674 with T := 708 }).exact = false ∧
    (verdict { r674 with T := 764 }).bridge = true ∧
    (verdict { r674 with T := 763 }).bridge = false := by decide +kernel
theorem v675 :
    verdict r675 = ⟨true, true, 1, 1314, 8380, 4285, true, true, true⟩ ∧
    (verdict { r675 with T := 1426 }).exact = true ∧
    (verdict { r675 with T := 1425 }).exact = false ∧
    (verdict { r675 with T := 1549 }).bridge = true ∧
    (verdict { r675 with T := 1548 }).bridge = false := by decide +kernel
theorem v676 :
    verdict r676 = ⟨true, true, 1, 756, 2879, 1463, true, true, true⟩ ∧
    (verdict { r676 with T := 870 }).exact = true ∧
    (verdict { r676 with T := 869 }).exact = false ∧
    (verdict { r676 with T := 882 }).bridge = true ∧
    (verdict { r676 with T := 881 }).bridge = false := by decide +kernel
theorem v677 :
    verdict r677 = ⟨true, true, 1, 1518, 6465, 3305, true, true, true⟩ ∧
    (verdict { r677 with T := 1942 }).exact = true ∧
    (verdict { r677 with T := 1941 }).exact = false ∧
    (verdict { r677 with T := 1942 }).bridge = true ∧
    (verdict { r677 with T := 1941 }).bridge = false := by decide +kernel
theorem v678 :
    verdict r678 = ⟨true, true, 1, 1082, 6981, 3176, true, true, true⟩ ∧
    (verdict { r678 with T := 958 }).exact = true ∧
    (verdict { r678 with T := 957 }).exact = false ∧
    (verdict { r678 with T := 1082 }).bridge = true ∧
    (verdict { r678 with T := 1081 }).bridge = false := by decide +kernel
theorem v679 :
    verdict r679 = ⟨true, true, 1, 1251, 5374, 2443, true, true, true⟩ ∧
    (verdict { r679 with T := 1107 }).exact = true ∧
    (verdict { r679 with T := 1106 }).exact = false ∧
    (verdict { r679 with T := 1251 }).bridge = true ∧
    (verdict { r679 with T := 1250 }).bridge = false := by decide +kernel
theorem v680 :
    verdict r680 = ⟨true, true, 1, 770, 3917, 1802, true, true, true⟩ ∧
    (verdict { r680 with T := 726 }).exact = true ∧
    (verdict { r680 with T := 725 }).exact = false ∧
    (verdict { r680 with T := 774 }).bridge = true ∧
    (verdict { r680 with T := 773 }).bridge = false := by decide +kernel
theorem v681 :
    verdict r681 = ⟨true, true, 1, 1587, 8697, 4010, true, true, true⟩ ∧
    (verdict { r681 with T := 1476 }).exact = true ∧
    (verdict { r681 with T := 1475 }).exact = false ∧
    (verdict { r681 with T := 1589 }).bridge = true ∧
    (verdict { r681 with T := 1588 }).bridge = false := by decide +kernel
theorem v682 :
    verdict r682 = ⟨true, true, 1, 890, 3015, 1386, true, true, true⟩ ∧
    (verdict { r682 with T := 864 }).exact = true ∧
    (verdict { r682 with T := 863 }).exact = false ∧
    (verdict { r682 with T := 894 }).bridge = true ∧
    (verdict { r682 with T := 893 }).bridge = false := by decide +kernel
theorem v683 :
    verdict r683 = ⟨true, true, 1, 1834, 6710, 3093, true, true, true⟩ ∧
    (verdict { r683 with T := 1982 }).exact = true ∧
    (verdict { r683 with T := 1981 }).exact = false ∧
    (verdict { r683 with T := 1982 }).bridge = true ∧
    (verdict { r683 with T := 1981 }).bridge = false := by decide +kernel
theorem v684 :
    verdict r684 = ⟨true, true, 1, 1654, 11400, 3748, true, true, true⟩ ∧
    (verdict { r684 with T := 1530 }).exact = true ∧
    (verdict { r684 with T := 1529 }).exact = false ∧
    (verdict { r684 with T := 1654 }).bridge = true ∧
    (verdict { r684 with T := 1653 }).bridge = false := by decide +kernel
theorem v685 :
    verdict r685 = ⟨true, true, 1, 1911, 8782, 2885, true, true, true⟩ ∧
    (verdict { r685 with T := 1767 }).exact = true ∧
    (verdict { r685 with T := 1766 }).exact = false ∧
    (verdict { r685 with T := 1911 }).bridge = true ∧
    (verdict { r685 with T := 1910 }).bridge = false := by decide +kernel
theorem v686 :
    verdict r686 = ⟨true, true, 1, 1244, 6542, 2107, true, true, true⟩ ∧
    (verdict { r686 with T := 1109 }).exact = true ∧
    (verdict { r686 with T := 1108 }).exact = false ∧
    (verdict { r686 with T := 1246 }).bridge = true ∧
    (verdict { r686 with T := 1245 }).bridge = false := by decide +kernel
theorem v687 :
    verdict r687 = ⟨true, true, 1, 2349, 13709, 4440, true, true, true⟩ ∧
    (verdict { r687 with T := 2228 }).exact = true ∧
    (verdict { r687 with T := 2227 }).exact = false ∧
    (verdict { r687 with T := 2353 }).bridge = true ∧
    (verdict { r687 with T := 2352 }).bridge = false := by decide +kernel
theorem v688 :
    verdict r688 = ⟨true, true, 1, 1437, 5038, 1621, true, true, true⟩ ∧
    (verdict { r688 with T := 1373 }).exact = true ∧
    (verdict { r688 with T := 1372 }).exact = false ∧
    (verdict { r688 with T := 1440 }).bridge = true ∧
    (verdict { r688 with T := 1439 }).bridge = false := by decide +kernel
theorem v689 :
    verdict r689 = ⟨true, true, 1, 2713, 10578, 3425, true, true, true⟩ ∧
    (verdict { r689 with T := 2575 }).exact = true ∧
    (verdict { r689 with T := 2574 }).exact = false ∧
    (verdict { r689 with T := 2718 }).bridge = true ∧
    (verdict { r689 with T := 2717 }).bridge = false := by decide +kernel
theorem v690 :
    verdict r690 = ⟨true, true, 1, 707, 6372, 2661, true, true, true⟩ ∧
    (verdict { r690 with T := 443 }).exact = true ∧
    (verdict { r690 with T := 442 }).exact = false ∧
    (verdict { r690 with T := 707 }).bridge = true ∧
    (verdict { r690 with T := 706 }).bridge = false := by decide +kernel
theorem v691 :
    verdict r691 = ⟨true, true, 1, 818, 4904, 2046, true, true, true⟩ ∧
    (verdict { r691 with T := 758 }).exact = true ∧
    (verdict { r691 with T := 757 }).exact = false ∧
    (verdict { r691 with T := 818 }).bridge = true ∧
    (verdict { r691 with T := 817 }).bridge = false := by decide +kernel
theorem v692 :
    verdict r692 = ⟨true, true, 1, 504, 3839, 1768, true, true, true⟩ ∧
    (verdict { r692 with T := 558 }).exact = true ∧
    (verdict { r692 with T := 557 }).exact = false ∧
    (verdict { r692 with T := 613 }).bridge = true ∧
    (verdict { r692 with T := 612 }).bridge = false := by decide +kernel
theorem v693 :
    verdict r693 = ⟨true, true, 1, 1011, 8533, 4026, true, true, true⟩ ∧
    (verdict { r693 with T := 1198 }).exact = true ∧
    (verdict { r693 with T := 1197 }).exact = false ∧
    (verdict { r693 with T := 1246 }).bridge = true ∧
    (verdict { r693 with T := 1245 }).bridge = false := by decide +kernel
theorem v694 :
    verdict r694 = ⟨true, true, 1, 582, 2953, 1360, true, true, true⟩ ∧
    (verdict { r694 with T := 793 }).exact = true ∧
    (verdict { r694 with T := 792 }).exact = false ∧
    (verdict { r694 with T := 793 }).bridge = true ∧
    (verdict { r694 with T := 792 }).bridge = false := by decide +kernel
theorem v695 :
    verdict r695 = ⟨true, true, 1, 1168, 6583, 3105, true, true, true⟩ ∧
    (verdict { r695 with T := 1786 }).exact = true ∧
    (verdict { r695 with T := 1785 }).exact = false ∧
    (verdict { r695 with T := 1786 }).bridge = true ∧
    (verdict { r695 with T := 1785 }).bridge = false := by decide +kernel
theorem v696 :
    verdict r696 = ⟨true, true, 1, 1652, 11401, 3887, true, true, true⟩ ∧
    (verdict { r696 with T := 1528 }).exact = true ∧
    (verdict { r696 with T := 1527 }).exact = false ∧
    (verdict { r696 with T := 1652 }).bridge = true ∧
    (verdict { r696 with T := 1651 }).bridge = false := by decide +kernel
theorem v697 :
    verdict r697 = ⟨true, true, 1, 1909, 8781, 2992, true, true, true⟩ ∧
    (verdict { r697 with T := 1765 }).exact = true ∧
    (verdict { r697 with T := 1764 }).exact = false ∧
    (verdict { r697 with T := 1909 }).bridge = true ∧
    (verdict { r697 with T := 1908 }).bridge = false := by decide +kernel
theorem v698 :
    verdict r698 = ⟨true, true, 1, 1453, 6496, 2191, true, true, true⟩ ∧
    (verdict { r698 with T := 1298 }).exact = true ∧
    (verdict { r698 with T := 1297 }).exact = false ∧
    (verdict { r698 with T := 1453 }).bridge = true ∧
    (verdict { r698 with T := 1452 }).bridge = false := by decide +kernel
theorem v699 :
    verdict r699 = ⟨true, true, 1, 2574, 13217, 4351, true, true, true⟩ ∧
    (verdict { r699 with T := 2247 }).exact = true ∧
    (verdict { r699 with T := 2246 }).exact = false ∧
    (verdict { r699 with T := 2574 }).bridge = true ∧
    (verdict { r699 with T := 2573 }).bridge = false := by decide +kernel
theorem v700 :
    verdict r700 = ⟨true, true, 1, 1678, 5002, 1686, true, true, true⟩ ∧
    (verdict { r700 with T := 1499 }).exact = true ∧
    (verdict { r700 with T := 1498 }).exact = false ∧
    (verdict { r700 with T := 1678 }).bridge = true ∧
    (verdict { r700 with T := 1677 }).bridge = false := by decide +kernel
theorem v701 :
    verdict r701 = ⟨true, true, 1, 2974, 10197, 3356, true, true, true⟩ ∧
    (verdict { r701 with T := 2595 }).exact = true ∧
    (verdict { r701 with T := 2594 }).exact = false ∧
    (verdict { r701 with T := 2974 }).bridge = true ∧
    (verdict { r701 with T := 2973 }).bridge = false := by decide +kernel
theorem v702 :
    verdict r702 = ⟨true, true, 1, 693, 6201, 2860, true, true, true⟩ ∧
    (verdict { r702 with T := 632 }).exact = true ∧
    (verdict { r702 with T := 631 }).exact = false ∧
    (verdict { r702 with T := 693 }).bridge = true ∧
    (verdict { r702 with T := 692 }).bridge = false := by decide +kernel
theorem v703 :
    verdict r703 = ⟨true, true, 1, 802, 4772, 2200, true, true, true⟩ ∧
    (verdict { r703 with T := 945 }).exact = true ∧
    (verdict { r703 with T := 944 }).exact = false ∧
    (verdict { r703 with T := 945 }).bridge = true ∧
    (verdict { r703 with T := 944 }).bridge = false := by decide +kernel
theorem v704 :
    verdict r704 = ⟨true, true, 1, 526, 3613, 1685, true, true, true⟩ ∧
    (verdict { r704 with T := 606 }).exact = true ∧
    (verdict { r704 with T := 605 }).exact = false ∧
    (verdict { r704 with T := 606 }).bridge = true ∧
    (verdict { r704 with T := 605 }).bridge = false := by decide +kernel
theorem v705 :
    verdict r705 = ⟨true, true, 1, 1057, 8132, 3841, true, true, true⟩ ∧
    (verdict { r705 with T := 1453 }).exact = true ∧
    (verdict { r705 with T := 1452 }).exact = false ∧
    (verdict { r705 with T := 1453 }).bridge = true ∧
    (verdict { r705 with T := 1452 }).bridge = false := by decide +kernel
theorem v706 :
    verdict r706 = ⟨true, true, 1, 607, 2776, 1295, true, true, true⟩ ∧
    (verdict { r706 with T := 816 }).exact = true ∧
    (verdict { r706 with T := 815 }).exact = false ∧
    (verdict { r706 with T := 816 }).bridge = true ∧
    (verdict { r706 with T := 815 }).bridge = false := by decide +kernel
theorem v707 :
    verdict r707 = ⟨true, true, 1, 1221, 6272, 2962, true, true, true⟩ ∧
    (verdict { r707 with T := 1896 }).exact = true ∧
    (verdict { r707 with T := 1895 }).exact = false ∧
    (verdict { r707 with T := 1896 }).bridge = true ∧
    (verdict { r707 with T := 1895 }).bridge = false := by decide +kernel
theorem v708 :
    verdict r708 = ⟨true, true, 1, 880, 8603, 2974, true, true, true⟩ ∧
    (verdict { r708 with T := 756 }).exact = true ∧
    (verdict { r708 with T := 755 }).exact = false ∧
    (verdict { r708 with T := 880 }).bridge = true ∧
    (verdict { r708 with T := 879 }).bridge = false := by decide +kernel
theorem v709 :
    verdict r709 = ⟨true, true, 1, 1018, 6621, 2287, true, true, true⟩ ∧
    (verdict { r709 with T := 874 }).exact = true ∧
    (verdict { r709 with T := 873 }).exact = false ∧
    (verdict { r709 with T := 1018 }).bridge = true ∧
    (verdict { r709 with T := 1017 }).bridge = false := by decide +kernel
theorem v710 :
    verdict r710 = ⟨true, true, 1, 664, 4937, 1610, true, true, true⟩ ∧
    (verdict { r710 with T := 688 }).exact = true ∧
    (verdict { r710 with T := 687 }).exact = false ∧
    (verdict { r710 with T := 745 }).bridge = true ∧
    (verdict { r710 with T := 744 }).bridge = false := by decide +kernel
theorem v711 :
    verdict r711 = ⟨true, true, 1, 1282, 10774, 3518, true, true, true⟩ ∧
    (verdict { r711 with T := 1365 }).exact = true ∧
    (verdict { r711 with T := 1364 }).exact = false ∧
    (verdict { r711 with T := 1454 }).bridge = true ∧
    (verdict { r711 with T := 1453 }).bridge = false := by decide +kernel
theorem v712 :
    verdict r712 = ⟨true, true, 1, 767, 3799, 1238, true, true, true⟩ ∧
    (verdict { r712 with T := 902 }).exact = true ∧
    (verdict { r712 with T := 901 }).exact = false ∧
    (verdict { r712 with T := 902 }).bridge = true ∧
    (verdict { r712 with T := 901 }).bridge = false := by decide +kernel
theorem v713 :
    verdict r713 = ⟨true, true, 1, 1481, 8314, 2715, true, true, true⟩ ∧
    (verdict { r713 with T := 1994 }).exact = true ∧
    (verdict { r713 with T := 1993 }).exact = false ∧
    (verdict { r713 with T := 1994 }).bridge = true ∧
    (verdict { r713 with T := 1993 }).bridge = false := by decide +kernel
theorem v714 :
    verdict r714 = ⟨true, true, 1, 761, 6622, 2855, true, true, true⟩ ∧
    (verdict { r714 with T := 637 }).exact = true ∧
    (verdict { r714 with T := 636 }).exact = false ∧
    (verdict { r714 with T := 761 }).bridge = true ∧
    (verdict { r714 with T := 760 }).bridge = false := by decide +kernel
theorem v715 :
    verdict r715 = ⟨true, true, 1, 880, 5094, 2195, true, true, true⟩ ∧
    (verdict { r715 with T := 779 }).exact = true ∧
    (verdict { r715 with T := 778 }).exact = false ∧
    (verdict { r715 with T := 880 }).bridge = true ∧
    (verdict { r715 with T := 879 }).bridge = false := by decide +kernel
theorem v716 :
    verdict r716 = ⟨true, true, 1, 642, 3729, 1560, true, true, true⟩ ∧
    (verdict { r716 with T := 676 }).exact = true ∧
    (verdict { r716 with T := 675 }).exact = false ∧
    (verdict { r716 with T := 731 }).bridge = true ∧
    (verdict { r716 with T := 730 }).bridge = false := by decide +kernel
theorem v717 :
    verdict r717 = ⟨true, true, 1, 1192, 7997, 3408, true, true, true⟩ ∧
    (verdict { r717 with T := 1364 }).exact = true ∧
    (verdict { r717 with T := 1363 }).exact = false ∧
    (verdict { r717 with T := 1382 }).bridge = true ∧
    (verdict { r717 with T := 1381 }).bridge = false := by decide +kernel
theorem v718 :
    verdict r718 = ⟨true, true, 1, 742, 2870, 1200, true, true, true⟩ ∧
    (verdict { r718 with T := 900 }).exact = true ∧
    (verdict { r718 with T := 899 }).exact = false ∧
    (verdict { r718 with T := 900 }).bridge = true ∧
    (verdict { r718 with T := 899 }).bridge = false := by decide +kernel
theorem v719 :
    verdict r719 = ⟨true, true, 1, 1377, 6170, 2629, true, true, true⟩ ∧
    (verdict { r719 with T := 1966 }).exact = true ∧
    (verdict { r719 with T := 1965 }).exact = false ∧
    (verdict { r719 with T := 1966 }).bridge = true ∧
    (verdict { r719 with T := 1965 }).bridge = false := by decide +kernel
theorem v720 :
    verdict r720 = ⟨true, true, 1, 872, 8979, 2966, true, true, true⟩ ∧
    (verdict { r720 with T := 748 }).exact = true ∧
    (verdict { r720 with T := 747 }).exact = false ∧
    (verdict { r720 with T := 872 }).bridge = true ∧
    (verdict { r720 with T := 871 }).bridge = false := by decide +kernel
theorem v721 :
    verdict r721 = ⟨true, true, 1, 1008, 6911, 2281, true, true, true⟩ ∧
    (verdict { r721 with T := 864 }).exact = true ∧
    (verdict { r721 with T := 863 }).exact = false ∧
    (verdict { r721 with T := 1008 }).bridge = true ∧
    (verdict { r721 with T := 1007 }).bridge = false := by decide +kernel
theorem v722 :
    verdict r722 = ⟨true, true, 1, 812, 5384, 1745, true, true, true⟩ ∧
    (verdict { r722 with T := 766 }).exact = true ∧
    (verdict { r722 with T := 765 }).exact = false ∧
    (verdict { r722 with T := 812 }).bridge = true ∧
    (verdict { r722 with T := 811 }).bridge = false := by decide +kernel
theorem v723 :
    verdict r723 = ⟨true, true, 1, 1525, 11568, 3729, true, true, true⟩ ∧
    (verdict { r723 with T := 1408 }).exact = true ∧
    (verdict { r723 with T := 1407 }).exact = false ∧
    (verdict { r723 with T := 1525 }).bridge = true ∧
    (verdict { r723 with T := 1524 }).bridge = false := by decide +kernel
theorem v724 :
    verdict r724 = ⟨true, true, 1, 937, 4143, 1341, true, true, true⟩ ∧
    (verdict { r724 with T := 884 }).exact = true ∧
    (verdict { r724 with T := 883 }).exact = false ∧
    (verdict { r724 with T := 938 }).bridge = true ∧
    (verdict { r724 with T := 937 }).bridge = false := by decide +kernel
theorem v725 :
    verdict r725 = ⟨true, true, 1, 1761, 8926, 2877, true, true, true⟩ ∧
    (verdict { r725 with T := 1711 }).exact = true ∧
    (verdict { r725 with T := 1710 }).exact = false ∧
    (verdict { r725 with T := 1761 }).bridge = true ∧
    (verdict { r725 with T := 1760 }).bridge = false := by decide +kernel
theorem v726 :
    verdict r726 = ⟨true, true, 1, 1112, 7655, 3206, true, true, true⟩ ∧
    (verdict { r726 with T := 988 }).exact = true ∧
    (verdict { r726 with T := 987 }).exact = false ∧
    (verdict { r726 with T := 1112 }).bridge = true ∧
    (verdict { r726 with T := 1111 }).bridge = false := by decide +kernel
theorem v727 :
    verdict r727 = ⟨true, true, 1, 1285, 5893, 2466, true, true, true⟩ ∧
    (verdict { r727 with T := 1141 }).exact = true ∧
    (verdict { r727 with T := 1140 }).exact = false ∧
    (verdict { r727 with T := 1285 }).bridge = true ∧
    (verdict { r727 with T := 1284 }).bridge = false := by decide +kernel
theorem v728 :
    verdict r728 = ⟨true, true, 1, 793, 4072, 1602, true, true, true⟩ ∧
    (verdict { r728 with T := 574 }).exact = true ∧
    (verdict { r728 with T := 573 }).exact = false ∧
    (verdict { r728 with T := 803 }).bridge = true ∧
    (verdict { r728 with T := 802 }).bridge = false := by decide +kernel
theorem v729 :
    verdict r729 = ⟨true, true, 1, 1613, 8891, 3567, true, true, true⟩ ∧
    (verdict { r729 with T := 1512 }).exact = true ∧
    (verdict { r729 with T := 1511 }).exact = false ∧
    (verdict { r729 with T := 1635 }).bridge = true ∧
    (verdict { r729 with T := 1634 }).bridge = false := by decide +kernel
theorem v730 :
    verdict r730 = ⟨true, true, 1, 916, 3133, 1232, true, true, true⟩ ∧
    (verdict { r730 with T := 946 }).exact = true ∧
    (verdict { r730 with T := 945 }).exact = false ∧
    (verdict { r730 with T := 946 }).bridge = true ∧
    (verdict { r730 with T := 945 }).bridge = false := by decide +kernel
theorem v731 :
    verdict r731 = ⟨true, true, 1, 1863, 6858, 2751, true, true, true⟩ ∧
    (verdict { r731 with T := 2107 }).exact = true ∧
    (verdict { r731 with T := 2106 }).exact = false ∧
    (verdict { r731 with T := 2107 }).bridge = true ∧
    (verdict { r731 with T := 2106 }).bridge = false := by decide +kernel
theorem v732 :
    verdict r732 = ⟨true, true, 1, 753, 9086, 2847, true, true, true⟩ ∧
    (verdict { r732 with T := 629 }).exact = true ∧
    (verdict { r732 with T := 628 }).exact = false ∧
    (verdict { r732 with T := 753 }).bridge = true ∧
    (verdict { r732 with T := 752 }).bridge = false := by decide +kernel
theorem v733 :
    verdict r733 = ⟨true, true, 1, 871, 6997, 2189, true, true, true⟩ ∧
    (verdict { r733 with T := 776 }).exact = true ∧
    (verdict { r733 with T := 775 }).exact = false ∧
    (verdict { r733 with T := 871 }).bridge = true ∧
    (verdict { r733 with T := 870 }).bridge = false := by decide +kernel
theorem v734 :
    verdict r734 = ⟨true, true, 1, 627, 5123, 1511, true, true, true⟩ ∧
    (verdict { r734 with T := 544 }).exact = true ∧
    (verdict { r734 with T := 543 }).exact = false ∧
    (verdict { r734 with T := 709 }).bridge = true ∧
    (verdict { r734 with T := 708 }).bridge = false := by decide +kernel
theorem v735 :
    verdict r735 = ⟨true, true, 1, 1175, 11024, 3248, true, true, true⟩ ∧
    (verdict { r735 with T := 1344 }).exact = true ∧
    (verdict { r735 with T := 1343 }).exact = false ∧
    (verdict { r735 with T := 1347 }).bridge = true ∧
    (verdict { r735 with T := 1346 }).bridge = false := by decide +kernel
theorem v736 :
    verdict r736 = ⟨true, true, 1, 724, 3941, 1161, true, true, true⟩ ∧
    (verdict { r736 with T := 882 }).exact = true ∧
    (verdict { r736 with T := 881 }).exact = false ∧
    (verdict { r736 with T := 882 }).bridge = true ∧
    (verdict { r736 with T := 881 }).bridge = false := by decide +kernel
theorem v737 :
    verdict r737 = ⟨true, true, 1, 1358, 8508, 2506, true, true, true⟩ ∧
    (verdict { r737 with T := 1937 }).exact = true ∧
    (verdict { r737 with T := 1936 }).exact = false ∧
    (verdict { r737 with T := 1937 }).bridge = true ∧
    (verdict { r737 with T := 1936 }).bridge = false := by decide +kernel
theorem v738 :
    verdict r738 = ⟨true, true, 1, 570, 6025, 2664, true, true, true⟩ ∧
    (verdict { r738 with T := 446 }).exact = true ∧
    (verdict { r738 with T := 445 }).exact = false ∧
    (verdict { r738 with T := 570 }).bridge = true ∧
    (verdict { r738 with T := 569 }).bridge = false := by decide +kernel
theorem v739 :
    verdict r739 = ⟨true, true, 1, 659, 4635, 2048, true, true, true⟩ ∧
    (verdict { r739 with T := 707 }).exact = true ∧
    (verdict { r739 with T := 706 }).exact = false ∧
    (verdict { r739 with T := 707 }).bridge = true ∧
    (verdict { r739 with T := 706 }).bridge = false := by decide +kernel
theorem v740 :
    verdict r740 = ⟨true, true, 1, 542, 3538, 1600, true, true, true⟩ ∧
    (verdict { r740 with T := 584 }).exact = true ∧
    (verdict { r740 with T := 583 }).exact = false ∧
    (verdict { r740 with T := 641 }).bridge = true ∧
    (verdict { r740 with T := 640 }).bridge = false := by decide +kernel
theorem v741 :
    verdict r741 = ⟨true, true, 1, 1240, 8046, 3596, true, true, true⟩ ∧
    (verdict { r741 with T := 1407 }).exact = true ∧
    (verdict { r741 with T := 1406 }).exact = false ∧
    (verdict { r741 with T := 1407 }).bridge = true ∧
    (verdict { r741 with T := 1406 }).bridge = false := by decide +kernel
theorem v742 :
    verdict r742 = ⟨true, true, 1, 626, 2720, 1230, true, true, true⟩ ∧
    (verdict { r742 with T := 868 }).exact = true ∧
    (verdict { r742 with T := 867 }).exact = false ∧
    (verdict { r742 with T := 868 }).bridge = true ∧
    (verdict { r742 with T := 867 }).bridge = false := by decide +kernel
theorem v743 :
    verdict r743 = ⟨true, true, 1, 1434, 6206, 2773, true, true, true⟩ ∧
    (verdict { r743 with T := 1898 }).exact = true ∧
    (verdict { r743 with T := 1897 }).exact = false ∧
    (verdict { r743 with T := 1898 }).bridge = true ∧
    (verdict { r743 with T := 1897 }).bridge = false := by decide +kernel
theorem v744 :
    verdict r744 = ⟨true, true, 1, 1721, 10942, 3675, true, true, true⟩ ∧
    (verdict { r744 with T := 1457 }).exact = true ∧
    (verdict { r744 with T := 1456 }).exact = false ∧
    (verdict { r744 with T := 1721 }).bridge = true ∧
    (verdict { r744 with T := 1720 }).bridge = false := by decide +kernel
theorem v745 :
    verdict r745 = ⟨true, true, 1, 1989, 8431, 2829, true, true, true⟩ ∧
    (verdict { r745 with T := 1683 }).exact = true ∧
    (verdict { r745 with T := 1682 }).exact = false ∧
    (verdict { r745 with T := 1989 }).bridge = true ∧
    (verdict { r745 with T := 1988 }).bridge = false := by decide +kernel
theorem v746 :
    verdict r746 = ⟨true, true, 1, 1134, 5996, 2029, true, true, true⟩ ∧
    (verdict { r746 with T := 930 }).exact = true ∧
    (verdict { r746 with T := 929 }).exact = false ∧
    (verdict { r746 with T := 1134 }).bridge = true ∧
    (verdict { r746 with T := 1133 }).bridge = false := by decide +kernel
theorem v747 :
    verdict r747 = ⟨true, true, 1, 2271, 12810, 4429, true, true, true⟩ ∧
    (verdict { r747 with T := 1828 }).exact = true ∧
    (verdict { r747 with T := 1827 }).exact = false ∧
    (verdict { r747 with T := 2271 }).bridge = true ∧
    (verdict { r747 with T := 2270 }).bridge = false := by decide +kernel
theorem v748 :
    verdict r748 = ⟨true, true, 1, 1310, 4617, 1561, true, true, true⟩ ∧
    (verdict { r748 with T := 1157 }).exact = true ∧
    (verdict { r748 with T := 1156 }).exact = false ∧
    (verdict { r748 with T := 1310 }).bridge = true ∧
    (verdict { r748 with T := 1309 }).bridge = false := by decide +kernel
theorem v749 :
    verdict r749 = ⟨true, true, 1, 2624, 9886, 3418, true, true, true⟩ ∧
    (verdict { r749 with T := 2300 }).exact = true ∧
    (verdict { r749 with T := 2299 }).exact = false ∧
    (verdict { r749 with T := 2624 }).bridge = true ∧
    (verdict { r749 with T := 2623 }).bridge = false := by decide +kernel

end Formal.Timing.ChainSettleExe.GcdD
