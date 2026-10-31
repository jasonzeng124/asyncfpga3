import Formal.Timing.ChainSettleExeGcdDData5

/-! C-10o2 GENERATED: kernel-decided verdicts of chunk 5 (see ChainSettleExe.verdict).
Per row: `verdict` at chainck's late side `T`; exact PASS at `T*` and FAIL at `T* - 1`
(margin_exact = T - T*); bridge PASS at `Tb*` and FAIL at `Tb* - 1`. -/

namespace Formal.Timing.ChainSettleExe.GcdD
open Formal.Timing Formal.Timing.ChainSettleExe

theorem v750 :
    verdict r750 = ⟨true, true, 1, 552, 6937, 2646, true, true, true⟩ ∧
    (verdict { r750 with T := 428 }).exact = true ∧
    (verdict { r750 with T := 427 }).exact = false ∧
    (verdict { r750 with T := 552 }).bridge = true ∧
    (verdict { r750 with T := 551 }).bridge = false := by decide +kernel
theorem v751 :
    verdict r751 = ⟨true, true, 1, 639, 5339, 2034, true, true, true⟩ ∧
    (verdict { r751 with T := 699 }).exact = true ∧
    (verdict { r751 with T := 698 }).exact = false ∧
    (verdict { r751 with T := 699 }).bridge = true ∧
    (verdict { r751 with T := 698 }).bridge = false := by decide +kernel
theorem v752 :
    verdict r752 = ⟨true, true, 1, 418, 3574, 1572, true, true, true⟩ ∧
    (verdict { r752 with T := 501 }).exact = true ∧
    (verdict { r752 with T := 500 }).exact = false ∧
    (verdict { r752 with T := 527 }).bridge = true ∧
    (verdict { r752 with T := 526 }).bridge = false := by decide +kernel
theorem v753 :
    verdict r753 = ⟨true, true, 1, 832, 7825, 3604, true, true, true⟩ ∧
    (verdict { r753 with T := 1230 }).exact = true ∧
    (verdict { r753 with T := 1229 }).exact = false ∧
    (verdict { r753 with T := 1230 }).bridge = true ∧
    (verdict { r753 with T := 1229 }).bridge = false := by decide +kernel
theorem v754 :
    verdict r754 = ⟨true, true, 1, 483, 2750, 1209, true, true, true⟩ ∧
    (verdict { r754 with T := 752 }).exact = true ∧
    (verdict { r754 with T := 751 }).exact = false ∧
    (verdict { r754 with T := 752 }).bridge = true ∧
    (verdict { r754 with T := 751 }).bridge = false := by decide +kernel
theorem v755 :
    verdict r755 = ⟨true, true, 1, 962, 6038, 2780, true, true, true⟩ ∧
    (verdict { r755 with T := 1697 }).exact = true ∧
    (verdict { r755 with T := 1696 }).exact = false ∧
    (verdict { r755 with T := 1697 }).bridge = true ∧
    (verdict { r755 with T := 1696 }).bridge = false := by decide +kernel
theorem v756 :
    verdict r756 = ⟨true, true, 1, 765, 7129, 2859, true, true, true⟩ ∧
    (verdict { r756 with T := 641 }).exact = true ∧
    (verdict { r756 with T := 640 }).exact = false ∧
    (verdict { r756 with T := 765 }).bridge = true ∧
    (verdict { r756 with T := 764 }).bridge = false := by decide +kernel
theorem v757 :
    verdict r757 = ⟨true, true, 1, 885, 5489, 2199, true, true, true⟩ ∧
    (verdict { r757 with T := 780 }).exact = true ∧
    (verdict { r757 with T := 779 }).exact = false ∧
    (verdict { r757 with T := 885 }).bridge = true ∧
    (verdict { r757 with T := 884 }).bridge = false := by decide +kernel
theorem v758 :
    verdict r758 = ⟨true, true, 1, 552, 3784, 1507, true, true, true⟩ ∧
    (verdict { r758 with T := 580 }).exact = true ∧
    (verdict { r758 with T := 579 }).exact = false ∧
    (verdict { r758 with T := 633 }).bridge = true ∧
    (verdict { r758 with T := 632 }).bridge = false := by decide +kernel
theorem v759 :
    verdict r759 = ⟨true, true, 1, 1104, 8316, 3360, true, true, true⟩ ∧
    (verdict { r759 with T := 1346 }).exact = true ∧
    (verdict { r759 with T := 1345 }).exact = false ∧
    (verdict { r759 with T := 1346 }).bridge = true ∧
    (verdict { r759 with T := 1345 }).bridge = false := by decide +kernel
theorem v760 :
    verdict r760 = ⟨true, true, 1, 637, 2909, 1157, true, true, true⟩ ∧
    (verdict { r760 with T := 854 }).exact = true ∧
    (verdict { r760 with T := 853 }).exact = false ∧
    (verdict { r760 with T := 854 }).bridge = true ∧
    (verdict { r760 with T := 853 }).bridge = false := by decide +kernel
theorem v761 :
    verdict r761 = ⟨true, true, 1, 1275, 6416, 2592, true, true, true⟩ ∧
    (verdict { r761 with T := 1911 }).exact = true ∧
    (verdict { r761 with T := 1910 }).exact = false ∧
    (verdict { r761 with T := 1911 }).bridge = true ∧
    (verdict { r761 with T := 1910 }).bridge = false := by decide +kernel
theorem v762 :
    verdict r762 = ⟨true, true, 1, 1868, 11269, 3962, true, true, true⟩ ∧
    (verdict { r762 with T := 1744 }).exact = true ∧
    (verdict { r762 with T := 1743 }).exact = false ∧
    (verdict { r762 with T := 1868 }).bridge = true ∧
    (verdict { r762 with T := 1867 }).bridge = false := by decide +kernel
theorem v763 :
    verdict r763 = ⟨true, true, 1, 2159, 8682, 3050, true, true, true⟩ ∧
    (verdict { r763 with T := 2015 }).exact = true ∧
    (verdict { r763 with T := 2014 }).exact = false ∧
    (verdict { r763 with T := 2159 }).bridge = true ∧
    (verdict { r763 with T := 2158 }).bridge = false := by decide +kernel
theorem v764 :
    verdict r764 = ⟨true, true, 1, 1190, 6279, 2002, true, true, true⟩ ∧
    (verdict { r764 with T := 1134 }).exact = true ∧
    (verdict { r764 with T := 1133 }).exact = false ∧
    (verdict { r764 with T := 1190 }).bridge = true ∧
    (verdict { r764 with T := 1189 }).bridge = false := by decide +kernel
theorem v765 :
    verdict r765 = ⟨true, true, 1, 2413, 13499, 4427, true, true, true⟩ ∧
    (verdict { r765 with T := 2296 }).exact = true ∧
    (verdict { r765 with T := 2295 }).exact = false ∧
    (verdict { r765 with T := 2421 }).bridge = true ∧
    (verdict { r765 with T := 2420 }).bridge = false := by decide +kernel
theorem v766 :
    verdict r766 = ⟨true, true, 1, 1375, 4836, 1539, true, true, true⟩ ∧
    (verdict { r766 with T := 1310 }).exact = true ∧
    (verdict { r766 with T := 1309 }).exact = false ∧
    (verdict { r766 with T := 1375 }).bridge = true ∧
    (verdict { r766 with T := 1374 }).bridge = false := by decide +kernel
theorem v767 :
    verdict r767 = ⟨true, true, 1, 2788, 10416, 3414, true, true, true⟩ ∧
    (verdict { r767 with T := 2652 }).exact = true ∧
    (verdict { r767 with T := 2651 }).exact = false ∧
    (verdict { r767 with T := 2797 }).bridge = true ∧
    (verdict { r767 with T := 2796 }).bridge = false := by decide +kernel
theorem v768 :
    verdict r768 = ⟨true, true, 1, 707, 6421, 2927, true, true, true⟩ ∧
    (verdict { r768 with T := 569 }).exact = true ∧
    (verdict { r768 with T := 568 }).exact = false ∧
    (verdict { r768 with T := 707 }).bridge = true ∧
    (verdict { r768 with T := 706 }).bridge = false := by decide +kernel
theorem v769 :
    verdict r769 = ⟨true, true, 1, 818, 4941, 2251, true, true, true⟩ ∧
    (verdict { r769 with T := 920 }).exact = true ∧
    (verdict { r769 with T := 919 }).exact = false ∧
    (verdict { r769 with T := 920 }).bridge = true ∧
    (verdict { r769 with T := 919 }).bridge = false := by decide +kernel
theorem v770 :
    verdict r770 = ⟨true, true, 1, 621, 3805, 1750, true, true, true⟩ ∧
    (verdict { r770 with T := 604 }).exact = true ∧
    (verdict { r770 with T := 603 }).exact = false ∧
    (verdict { r770 with T := 631 }).bridge = true ∧
    (verdict { r770 with T := 630 }).bridge = false := by decide +kernel
theorem v771 :
    verdict r771 = ⟨true, true, 1, 1255, 8522, 3978, true, true, true⟩ ∧
    (verdict { r771 with T := 1405 }).exact = true ∧
    (verdict { r771 with T := 1404 }).exact = false ∧
    (verdict { r771 with T := 1405 }).bridge = true ∧
    (verdict { r771 with T := 1404 }).bridge = false := by decide +kernel
theorem v772 :
    verdict r772 = ⟨true, true, 1, 717, 2927, 1346, true, true, true⟩ ∧
    (verdict { r772 with T := 872 }).exact = true ∧
    (verdict { r772 with T := 871 }).exact = false ∧
    (verdict { r772 with T := 872 }).bridge = true ∧
    (verdict { r772 with T := 871 }).bridge = false := by decide +kernel
theorem v773 :
    verdict r773 = ⟨true, true, 1, 1450, 6574, 3069, true, true, true⟩ ∧
    (verdict { r773 with T := 1957 }).exact = true ∧
    (verdict { r773 with T := 1956 }).exact = false ∧
    (verdict { r773 with T := 1957 }).bridge = true ∧
    (verdict { r773 with T := 1956 }).bridge = false := by decide +kernel
theorem v774 :
    verdict r774 = ⟨true, true, 1, 559, 6308, 2653, true, true, true⟩ ∧
    (verdict { r774 with T := 436 }).exact = true ∧
    (verdict { r774 with T := 435 }).exact = false ∧
    (verdict { r774 with T := 559 }).bridge = true ∧
    (verdict { r774 with T := 558 }).bridge = false := by decide +kernel
theorem v775 :
    verdict r775 = ⟨true, true, 1, 647, 4854, 2040, true, true, true⟩ ∧
    (verdict { r775 with T := 702 }).exact = true ∧
    (verdict { r775 with T := 701 }).exact = false ∧
    (verdict { r775 with T := 702 }).bridge = true ∧
    (verdict { r775 with T := 701 }).bridge = false := by decide +kernel
theorem v776 :
    verdict r776 = ⟨true, true, 1, 553, 3566, 1478, true, true, true⟩ ∧
    (verdict { r776 with T := 576 }).exact = true ∧
    (verdict { r776 with T := 575 }).exact = false ∧
    (verdict { r776 with T := 576 }).bridge = true ∧
    (verdict { r776 with T := 575 }).bridge = false := by decide +kernel
theorem v777 :
    verdict r777 = ⟨true, true, 1, 1243, 8078, 3438, true, true, true⟩ ∧
    (verdict { r777 with T := 1396 }).exact = true ∧
    (verdict { r777 with T := 1395 }).exact = false ∧
    (verdict { r777 with T := 1396 }).bridge = true ∧
    (verdict { r777 with T := 1395 }).bridge = false := by decide +kernel
theorem v778 :
    verdict r778 = ⟨true, true, 1, 639, 2744, 1136, true, true, true⟩ ∧
    (verdict { r778 with T := 810 }).exact = true ∧
    (verdict { r778 with T := 809 }).exact = false ∧
    (verdict { r778 with T := 810 }).bridge = true ∧
    (verdict { r778 with T := 809 }).bridge = false := by decide +kernel
theorem v779 :
    verdict r779 = ⟨true, true, 1, 1436, 6235, 2652, true, true, true⟩ ∧
    (verdict { r779 with T := 1924 }).exact = true ∧
    (verdict { r779 with T := 1923 }).exact = false ∧
    (verdict { r779 with T := 1924 }).bridge = true ∧
    (verdict { r779 with T := 1923 }).bridge = false := by decide +kernel
theorem v780 :
    verdict r780 = ⟨true, true, 1, 969, 10529, 3063, true, true, true⟩ ∧
    (verdict { r780 with T := 984 }).exact = true ∧
    (verdict { r780 with T := 983 }).exact = false ∧
    (verdict { r780 with T := 1181 }).bridge = true ∧
    (verdict { r780 with T := 1180 }).bridge = false := by decide +kernel
theorem v781 :
    verdict r781 = ⟨true, true, 1, 1120, 8105, 2356, true, true, true⟩ ∧
    (verdict { r781 with T := 1222 }).exact = true ∧
    (verdict { r781 with T := 1221 }).exact = false ∧
    (verdict { r781 with T := 1365 }).bridge = true ∧
    (verdict { r781 with T := 1364 }).bridge = false := by decide +kernel
theorem v782 :
    verdict r782 = ⟨true, true, 1, 621, 5825, 1590, true, true, true⟩ ∧
    (verdict { r782 with T := 674 }).exact = true ∧
    (verdict { r782 with T := 673 }).exact = false ∧
    (verdict { r782 with T := 802 }).bridge = true ∧
    (verdict { r782 with T := 801 }).bridge = false := by decide +kernel
theorem v783 :
    verdict r783 = ⟨true, true, 1, 1239, 12538, 3529, true, true, true⟩ ∧
    (verdict { r783 with T := 1543 }).exact = true ∧
    (verdict { r783 with T := 1542 }).exact = false ∧
    (verdict { r783 with T := 1666 }).bridge = true ∧
    (verdict { r783 with T := 1665 }).bridge = false := by decide +kernel
theorem v784 :
    verdict r784 = ⟨true, true, 1, 718, 4484, 1222, true, true, true⟩ ∧
    (verdict { r784 with T := 863 }).exact = true ∧
    (verdict { r784 with T := 862 }).exact = false ∧
    (verdict { r784 with T := 927 }).bridge = true ∧
    (verdict { r784 with T := 926 }).bridge = false := by decide +kernel
theorem v785 :
    verdict r785 = ⟨true, true, 1, 1432, 9674, 2723, true, true, true⟩ ∧
    (verdict { r785 with T := 1782 }).exact = true ∧
    (verdict { r785 with T := 1781 }).exact = false ∧
    (verdict { r785 with T := 1925 }).bridge = true ∧
    (verdict { r785 with T := 1924 }).bridge = false := by decide +kernel
theorem v786 :
    verdict r786 = ⟨true, true, 1, 1225, 8121, 3319, true, true, true⟩ ∧
    (verdict { r786 with T := 1257 }).exact = true ∧
    (verdict { r786 with T := 1256 }).exact = false ∧
    (verdict { r786 with T := 1437 }).bridge = true ∧
    (verdict { r786 with T := 1436 }).bridge = false := by decide +kernel
theorem v787 :
    verdict r787 = ⟨true, true, 1, 1416, 6253, 2554, true, true, true⟩ ∧
    (verdict { r787 with T := 1518 }).exact = true ∧
    (verdict { r787 with T := 1517 }).exact = false ∧
    (verdict { r787 with T := 1661 }).bridge = true ∧
    (verdict { r787 with T := 1660 }).bridge = false := by decide +kernel
theorem v788 :
    verdict r788 = ⟨true, true, 1, 1022, 4642, 1893, true, true, true⟩ ∧
    (verdict { r788 with T := 1050 }).exact = true ∧
    (verdict { r788 with T := 1049 }).exact = false ∧
    (verdict { r788 with T := 1110 }).bridge = true ∧
    (verdict { r788 with T := 1109 }).bridge = false := by decide +kernel
theorem v789 :
    verdict r789 = ⟨true, true, 1, 1922, 9797, 4017, true, true, true⟩ ∧
    (verdict { r789 with T := 2013 }).exact = true ∧
    (verdict { r789 with T := 2012 }).exact = false ∧
    (verdict { r789 with T := 2136 }).bridge = true ∧
    (verdict { r789 with T := 2135 }).bridge = false := by decide +kernel
theorem v790 :
    verdict r790 = ⟨true, true, 1, 1181, 3574, 1457, true, true, true⟩ ∧
    (verdict { r790 with T := 1218 }).exact = true ∧
    (verdict { r790 with T := 1217 }).exact = false ∧
    (verdict { r790 with T := 1282 }).bridge = true ∧
    (verdict { r790 with T := 1281 }).bridge = false := by decide +kernel
theorem v791 :
    verdict r791 = ⟨true, true, 1, 2221, 7560, 3099, true, true, true⟩ ∧
    (verdict { r791 with T := 2492 }).exact = true ∧
    (verdict { r791 with T := 2491 }).exact = false ∧
    (verdict { r791 with T := 2492 }).bridge = true ∧
    (verdict { r791 with T := 2491 }).bridge = false := by decide +kernel
theorem v792 :
    verdict r792 = ⟨true, true, 1, 1429, 12541, 3383, true, true, true⟩ ∧
    (verdict { r792 with T := 1165 }).exact = true ∧
    (verdict { r792 with T := 1164 }).exact = false ∧
    (verdict { r792 with T := 1429 }).bridge = true ∧
    (verdict { r792 with T := 1428 }).bridge = false := by decide +kernel
theorem v793 :
    verdict r793 = ⟨true, true, 1, 1652, 9662, 2603, true, true, true⟩ ∧
    (verdict { r793 with T := 1346 }).exact = true ∧
    (verdict { r793 with T := 1345 }).exact = false ∧
    (verdict { r793 with T := 1652 }).bridge = true ∧
    (verdict { r793 with T := 1651 }).bridge = false := by decide +kernel
theorem v794 :
    verdict r794 = ⟨true, true, 1, 982, 6608, 1851, true, true, true⟩ ∧
    (verdict { r794 with T := 773 }).exact = true ∧
    (verdict { r794 with T := 772 }).exact = false ∧
    (verdict { r794 with T := 987 }).bridge = true ∧
    (verdict { r794 with T := 986 }).bridge = false := by decide +kernel
theorem v795 :
    verdict r795 = ⟨true, true, 1, 1964, 14119, 4068, true, true, true⟩ ∧
    (verdict { r795 with T := 1536 }).exact = true ∧
    (verdict { r795 with T := 1535 }).exact = false ∧
    (verdict { r795 with T := 1965 }).bridge = true ∧
    (verdict { r795 with T := 1964 }).bridge = false := by decide +kernel
theorem v796 :
    verdict r796 = ⟨true, true, 1, 1134, 5088, 1424, true, true, true⟩ ∧
    (verdict { r796 with T := 983 }).exact = true ∧
    (verdict { r796 with T := 982 }).exact = false ∧
    (verdict { r796 with T := 1140 }).bridge = true ∧
    (verdict { r796 with T := 1139 }).bridge = false := by decide +kernel
theorem v797 :
    verdict r797 = ⟨true, true, 1, 2269, 10895, 3138, true, true, true⟩ ∧
    (verdict { r797 with T := 2019 }).exact = true ∧
    (verdict { r797 with T := 2018 }).exact = false ∧
    (verdict { r797 with T := 2270 }).bridge = true ∧
    (verdict { r797 with T := 2269 }).bridge = false := by decide +kernel
theorem v798 :
    verdict r798 = ⟨true, true, 1, 564, 6076, 2658, true, true, true⟩ ∧
    (verdict { r798 with T := 440 }).exact = true ∧
    (verdict { r798 with T := 439 }).exact = false ∧
    (verdict { r798 with T := 564 }).bridge = true ∧
    (verdict { r798 with T := 563 }).bridge = false := by decide +kernel
theorem v799 :
    verdict r799 = ⟨true, true, 1, 653, 4673, 2043, true, true, true⟩ ∧
    (verdict { r799 with T := 704 }).exact = true ∧
    (verdict { r799 with T := 703 }).exact = false ∧
    (verdict { r799 with T := 704 }).bridge = true ∧
    (verdict { r799 with T := 703 }).bridge = false := by decide +kernel
theorem v800 :
    verdict r800 = ⟨true, true, 1, 469, 3336, 1404, true, true, true⟩ ∧
    (verdict { r800 with T := 573 }).exact = true ∧
    (verdict { r800 with T := 572 }).exact = false ∧
    (verdict { r800 with T := 573 }).bridge = true ∧
    (verdict { r800 with T := 572 }).bridge = false := by decide +kernel
theorem v801 :
    verdict r801 = ⟨true, true, 1, 934, 7435, 3182, true, true, true⟩ ∧
    (verdict { r801 with T := 1332 }).exact = true ∧
    (verdict { r801 with T := 1331 }).exact = false ∧
    (verdict { r801 with T := 1332 }).bridge = true ∧
    (verdict { r801 with T := 1331 }).bridge = false := by decide +kernel
theorem v802 :
    verdict r802 = ⟨true, true, 1, 541, 2565, 1079, true, true, true⟩ ∧
    (verdict { r802 with T := 820 }).exact = true ∧
    (verdict { r802 with T := 819 }).exact = false ∧
    (verdict { r802 with T := 820 }).bridge = true ∧
    (verdict { r802 with T := 819 }).bridge = false := by decide +kernel
theorem v803 :
    verdict r803 = ⟨true, true, 1, 1079, 5736, 2454, true, true, true⟩ ∧
    (verdict { r803 with T := 1842 }).exact = true ∧
    (verdict { r803 with T := 1841 }).exact = false ∧
    (verdict { r803 with T := 1842 }).bridge = true ∧
    (verdict { r803 with T := 1841 }).bridge = false := by decide +kernel
theorem v804 :
    verdict r804 = ⟨true, true, 1, 564, 6960, 2807, true, true, true⟩ ∧
    (verdict { r804 with T := 568 }).exact = true ∧
    (verdict { r804 with T := 567 }).exact = false ∧
    (verdict { r804 with T := 568 }).bridge = true ∧
    (verdict { r804 with T := 567 }).bridge = false := by decide +kernel
theorem v805 :
    verdict r805 = ⟨true, true, 1, 653, 5356, 2158, true, true, true⟩ ∧
    (verdict { r805 with T := 876 }).exact = true ∧
    (verdict { r805 with T := 875 }).exact = false ∧
    (verdict { r805 with T := 876 }).bridge = true ∧
    (verdict { r805 with T := 875 }).bridge = false := by decide +kernel
theorem v806 :
    verdict r806 = ⟨true, true, 1, 361, 3816, 1631, true, true, true⟩ ∧
    (verdict { r806 with T := 586 }).exact = true ∧
    (verdict { r806 with T := 585 }).exact = false ∧
    (verdict { r806 with T := 586 }).bridge = true ∧
    (verdict { r806 with T := 585 }).bridge = false := by decide +kernel
theorem v807 :
    verdict r807 = ⟨true, true, 1, 667, 8394, 3675, true, true, true⟩ ∧
    (verdict { r807 with T := 1362 }).exact = true ∧
    (verdict { r807 with T := 1361 }).exact = false ∧
    (verdict { r807 with T := 1362 }).bridge = true ∧
    (verdict { r807 with T := 1361 }).bridge = false := by decide +kernel
theorem v808 :
    verdict r808 = ⟨true, true, 1, 417, 2935, 1254, true, true, true⟩ ∧
    (verdict { r808 with T := 820 }).exact = true ∧
    (verdict { r808 with T := 819 }).exact = false ∧
    (verdict { r808 with T := 820 }).bridge = true ∧
    (verdict { r808 with T := 819 }).bridge = false := by decide +kernel
theorem v809 :
    verdict r809 = ⟨true, true, 1, 771, 6477, 2836, true, true, true⟩ ∧
    (verdict { r809 with T := 1845 }).exact = true ∧
    (verdict { r809 with T := 1844 }).exact = false ∧
    (verdict { r809 with T := 1845 }).bridge = true ∧
    (verdict { r809 with T := 1844 }).bridge = false := by decide +kernel
theorem v810 :
    verdict r810 = ⟨true, true, 1, 1234, 11096, 3188, true, true, true⟩ ∧
    (verdict { r810 with T := 970 }).exact = true ∧
    (verdict { r810 with T := 969 }).exact = false ∧
    (verdict { r810 with T := 1234 }).bridge = true ∧
    (verdict { r810 with T := 1233 }).bridge = false := by decide +kernel
theorem v811 :
    verdict r811 = ⟨true, true, 1, 1426, 8548, 2453, true, true, true⟩ ∧
    (verdict { r811 with T := 1121 }).exact = true ∧
    (verdict { r811 with T := 1120 }).exact = false ∧
    (verdict { r811 with T := 1426 }).bridge = true ∧
    (verdict { r811 with T := 1425 }).bridge = false := by decide +kernel
theorem v812 :
    verdict r812 = ⟨true, true, 1, 877, 6500, 1763, true, true, true⟩ ∧
    (verdict { r812 with T := 668 }).exact = true ∧
    (verdict { r812 with T := 667 }).exact = false ∧
    (verdict { r812 with T := 882 }).bridge = true ∧
    (verdict { r812 with T := 881 }).bridge = false := by decide +kernel
theorem v813 :
    verdict r813 = ⟨true, true, 1, 1785, 13630, 3919, true, true, true⟩ ∧
    (verdict { r813 with T := 1357 }).exact = true ∧
    (verdict { r813 with T := 1356 }).exact = false ∧
    (verdict { r813 with T := 1786 }).bridge = true ∧
    (verdict { r813 with T := 1785 }).bridge = false := by decide +kernel
theorem v814 :
    verdict r814 = ⟨true, true, 1, 1013, 5007, 1356, true, true, true⟩ ∧
    (verdict { r814 with T := 864 }).exact = true ∧
    (verdict { r814 with T := 863 }).exact = false ∧
    (verdict { r814 with T := 1019 }).bridge = true ∧
    (verdict { r814 with T := 1018 }).bridge = false := by decide +kernel
theorem v815 :
    verdict r815 = ⟨true, true, 1, 2062, 10518, 3023, true, true, true⟩ ∧
    (verdict { r815 with T := 2058 }).exact = true ∧
    (verdict { r815 with T := 2057 }).exact = false ∧
    (verdict { r815 with T := 2064 }).bridge = true ∧
    (verdict { r815 with T := 2063 }).bridge = false := by decide +kernel
theorem v816 :
    verdict r816 = ⟨true, true, 1, 909, 7788, 3003, true, true, true⟩ ∧
    (verdict { r816 with T := 785 }).exact = true ∧
    (verdict { r816 with T := 784 }).exact = false ∧
    (verdict { r816 with T := 909 }).bridge = true ∧
    (verdict { r816 with T := 908 }).bridge = false := by decide +kernel
theorem v817 :
    verdict r817 = ⟨true, true, 1, 1051, 5997, 2310, true, true, true⟩ ∧
    (verdict { r817 with T := 907 }).exact = true ∧
    (verdict { r817 with T := 906 }).exact = false ∧
    (verdict { r817 with T := 1051 }).bridge = true ∧
    (verdict { r817 with T := 1050 }).bridge = false := by decide +kernel
theorem v818 :
    verdict r818 = ⟨true, true, 1, 769, 4898, 1603, true, true, true⟩ ∧
    (verdict { r818 with T := 803 }).exact = true ∧
    (verdict { r818 with T := 802 }).exact = false ∧
    (verdict { r818 with T := 858 }).bridge = true ∧
    (verdict { r818 with T := 857 }).bridge = false := by decide +kernel
theorem v819 :
    verdict r819 = ⟨true, true, 1, 1416, 10023, 3410, true, true, true⟩ ∧
    (verdict { r819 with T := 1483 }).exact = true ∧
    (verdict { r819 with T := 1482 }).exact = false ∧
    (verdict { r819 with T := 1606 }).bridge = true ∧
    (verdict { r819 with T := 1605 }).bridge = false := by decide +kernel
theorem v820 :
    verdict r820 = ⟨true, true, 1, 889, 3771, 1233, true, true, true⟩ ∧
    (verdict { r820 with T := 955 }).exact = true ∧
    (verdict { r820 with T := 954 }).exact = false ∧
    (verdict { r820 with T := 992 }).bridge = true ∧
    (verdict { r820 with T := 991 }).bridge = false := by decide +kernel
theorem v821 :
    verdict r821 = ⟨true, true, 1, 1636, 7736, 2631, true, true, true⟩ ∧
    (verdict { r821 with T := 2070 }).exact = true ∧
    (verdict { r821 with T := 2069 }).exact = false ∧
    (verdict { r821 with T := 2070 }).bridge = true ∧
    (verdict { r821 with T := 2069 }).bridge = false := by decide +kernel
theorem v822 :
    verdict r822 = ⟨true, true, 1, 885, 7039, 2839, true, true, true⟩ ∧
    (verdict { r822 with T := 834 }).exact = true ∧
    (verdict { r822 with T := 833 }).exact = false ∧
    (verdict { r822 with T := 957 }).bridge = true ∧
    (verdict { r822 with T := 956 }).bridge = false := by decide +kernel
theorem v823 :
    verdict r823 = ⟨true, true, 1, 1023, 5417, 2183, true, true, true⟩ ∧
    (verdict { r823 with T := 964 }).exact = true ∧
    (verdict { r823 with T := 963 }).exact = false ∧
    (verdict { r823 with T := 1107 }).bridge = true ∧
    (verdict { r823 with T := 1106 }).bridge = false := by decide +kernel
theorem v824 :
    verdict r824 = ⟨true, true, 1, 668, 3955, 1501, true, true, true⟩ ∧
    (verdict { r824 with T := 619 }).exact = true ∧
    (verdict { r824 with T := 618 }).exact = false ∧
    (verdict { r824 with T := 674 }).bridge = true ∧
    (verdict { r824 with T := 673 }).bridge = false := by decide +kernel
theorem v825 :
    verdict r825 = ⟨true, true, 1, 1391, 8383, 3384, true, true, true⟩ ∧
    (verdict { r825 with T := 1424 }).exact = true ∧
    (verdict { r825 with T := 1423 }).exact = false ∧
    (verdict { r825 with T := 1436 }).bridge = true ∧
    (verdict { r825 with T := 1435 }).bridge = false := by decide +kernel
theorem v826 :
    verdict r826 = ⟨true, true, 1, 771, 3045, 1153, true, true, true⟩ ∧
    (verdict { r826 with T := 866 }).exact = true ∧
    (verdict { r826 with T := 865 }).exact = false ∧
    (verdict { r826 with T := 866 }).bridge = true ∧
    (verdict { r826 with T := 865 }).bridge = false := by decide +kernel
theorem v827 :
    verdict r827 = ⟨true, true, 1, 1607, 6469, 2610, true, true, true⟩ ∧
    (verdict { r827 with T := 2045 }).exact = true ∧
    (verdict { r827 with T := 2044 }).exact = false ∧
    (verdict { r827 with T := 2045 }).bridge = true ∧
    (verdict { r827 with T := 2044 }).bridge = false := by decide +kernel
theorem v828 :
    verdict r828 = ⟨true, true, 1, 752, 7903, 2846, true, true, true⟩ ∧
    (verdict { r828 with T := 628 }).exact = true ∧
    (verdict { r828 with T := 627 }).exact = false ∧
    (verdict { r828 with T := 752 }).bridge = true ∧
    (verdict { r828 with T := 751 }).bridge = false := by decide +kernel
theorem v829 :
    verdict r829 = ⟨true, true, 1, 870, 6082, 2189, true, true, true⟩ ∧
    (verdict { r829 with T := 775 }).exact = true ∧
    (verdict { r829 with T := 774 }).exact = false ∧
    (verdict { r829 with T := 870 }).bridge = true ∧
    (verdict { r829 with T := 869 }).bridge = false := by decide +kernel
theorem v830 :
    verdict r830 = ⟨true, true, 1, 728, 4762, 1635, true, true, true⟩ ∧
    (verdict { r830 with T := 683 }).exact = true ∧
    (verdict { r830 with T := 682 }).exact = false ∧
    (verdict { r830 with T := 738 }).bridge = true ∧
    (verdict { r830 with T := 737 }).bridge = false := by decide +kernel
theorem v831 :
    verdict r831 = ⟨true, true, 1, 1365, 10135, 3564, true, true, true⟩ ∧
    (verdict { r831 with T := 1363 }).exact = true ∧
    (verdict { r831 with T := 1362 }).exact = false ∧
    (verdict { r831 with T := 1387 }).bridge = true ∧
    (verdict { r831 with T := 1386 }).bridge = false := by decide +kernel
theorem v832 :
    verdict r832 = ⟨true, true, 1, 841, 3664, 1257, true, true, true⟩ ∧
    (verdict { r832 with T := 901 }).exact = true ∧
    (verdict { r832 with T := 900 }).exact = false ∧
    (verdict { r832 with T := 901 }).bridge = true ∧
    (verdict { r832 with T := 900 }).bridge = false := by decide +kernel
theorem v833 :
    verdict r833 = ⟨true, true, 1, 1577, 7818, 2749, true, true, true⟩ ∧
    (verdict { r833 with T := 1967 }).exact = true ∧
    (verdict { r833 with T := 1966 }).exact = false ∧
    (verdict { r833 with T := 1967 }).bridge = true ∧
    (verdict { r833 with T := 1966 }).bridge = false := by decide +kernel
theorem v834 :
    verdict r834 = ⟨true, true, 1, 719, 6519, 2813, true, true, true⟩ ∧
    (verdict { r834 with T := 808 }).exact = true ∧
    (verdict { r834 with T := 807 }).exact = false ∧
    (verdict { r834 with T := 931 }).bridge = true ∧
    (verdict { r834 with T := 930 }).bridge = false := by decide +kernel
theorem v835 :
    verdict r835 = ⟨true, true, 1, 832, 5016, 2163, true, true, true⟩ ∧
    (verdict { r835 with T := 1009 }).exact = true ∧
    (verdict { r835 with T := 1008 }).exact = false ∧
    (verdict { r835 with T := 1077 }).bridge = true ∧
    (verdict { r835 with T := 1076 }).bridge = false := by decide +kernel
theorem v836 :
    verdict r836 = ⟨true, true, 1, 628, 3955, 1476, true, true, true⟩ ∧
    (verdict { r836 with T := 662 }).exact = true ∧
    (verdict { r836 with T := 661 }).exact = false ∧
    (verdict { r836 with T := 717 }).bridge = true ∧
    (verdict { r836 with T := 716 }).bridge = false := by decide +kernel
theorem v837 :
    verdict r837 = ⟨true, true, 1, 1175, 8399, 3200, true, true, true⟩ ∧
    (verdict { r837 with T := 1357 }).exact = true ∧
    (verdict { r837 with T := 1356 }).exact = false ∧
    (verdict { r837 with T := 1365 }).bridge = true ∧
    (verdict { r837 with T := 1364 }).bridge = false := by decide +kernel
theorem v838 :
    verdict r838 = ⟨true, true, 1, 725, 3044, 1134, true, true, true⟩ ∧
    (verdict { r838 with T := 889 }).exact = true ∧
    (verdict { r838 with T := 888 }).exact = false ∧
    (verdict { r838 with T := 889 }).bridge = true ∧
    (verdict { r838 with T := 888 }).bridge = false := by decide +kernel
theorem v839 :
    verdict r839 = ⟨true, true, 1, 1357, 6479, 2468, true, true, true⟩ ∧
    (verdict { r839 with T := 1954 }).exact = true ∧
    (verdict { r839 with T := 1953 }).exact = false ∧
    (verdict { r839 with T := 1954 }).bridge = true ∧
    (verdict { r839 with T := 1953 }).bridge = false := by decide +kernel
theorem v840 :
    verdict r840 = ⟨true, true, 1, 947, 12339, 3041, true, true, true⟩ ∧
    (verdict { r840 with T := 823 }).exact = true ∧
    (verdict { r840 with T := 822 }).exact = false ∧
    (verdict { r840 with T := 947 }).bridge = true ∧
    (verdict { r840 with T := 946 }).bridge = false := by decide +kernel
theorem v841 :
    verdict r841 = ⟨true, true, 1, 1095, 9506, 2339, true, true, true⟩ ∧
    (verdict { r841 with T := 951 }).exact = true ∧
    (verdict { r841 with T := 950 }).exact = false ∧
    (verdict { r841 with T := 1095 }).bridge = true ∧
    (verdict { r841 with T := 1094 }).bridge = false := by decide +kernel
theorem v842 :
    verdict r842 = ⟨true, true, 1, 658, 6394, 1488, true, true, true⟩ ∧
    (verdict { r842 with T := 692 }).exact = true ∧
    (verdict { r842 with T := 691 }).exact = false ∧
    (verdict { r842 with T := 747 }).bridge = true ∧
    (verdict { r842 with T := 746 }).bridge = false := by decide +kernel
theorem v843 :
    verdict r843 = ⟨true, true, 1, 1301, 13655, 3289, true, true, true⟩ ∧
    (verdict { r843 with T := 1394 }).exact = true ∧
    (verdict { r843 with T := 1393 }).exact = false ∧
    (verdict { r843 with T := 1491 }).bridge = true ∧
    (verdict { r843 with T := 1490 }).bridge = false := by decide +kernel
theorem v844 :
    verdict r844 = ⟨true, true, 1, 760, 4922, 1144, true, true, true⟩ ∧
    (verdict { r844 with T := 915 }).exact = true ∧
    (verdict { r844 with T := 914 }).exact = false ∧
    (verdict { r844 with T := 915 }).bridge = true ∧
    (verdict { r844 with T := 914 }).bridge = false := by decide +kernel
theorem v845 :
    verdict r845 = ⟨true, true, 1, 1503, 10535, 2537, true, true, true⟩ ∧
    (verdict { r845 with T := 2030 }).exact = true ∧
    (verdict { r845 with T := 2029 }).exact = false ∧
    (verdict { r845 with T := 2030 }).bridge = true ∧
    (verdict { r845 with T := 2029 }).bridge = false := by decide +kernel
theorem v846 :
    verdict r846 = ⟨true, true, 1, 1049, 7521, 3143, true, true, true⟩ ∧
    (verdict { r846 with T := 925 }).exact = true ∧
    (verdict { r846 with T := 924 }).exact = false ∧
    (verdict { r846 with T := 1049 }).bridge = true ∧
    (verdict { r846 with T := 1048 }).bridge = false := by decide +kernel
theorem v847 :
    verdict r847 = ⟨true, true, 1, 1213, 5790, 2418, true, true, true⟩ ∧
    (verdict { r847 with T := 1069 }).exact = true ∧
    (verdict { r847 with T := 1068 }).exact = false ∧
    (verdict { r847 with T := 1213 }).bridge = true ∧
    (verdict { r847 with T := 1212 }).bridge = false := by decide +kernel
theorem v848 :
    verdict r848 = ⟨true, true, 1, 817, 4396, 1631, true, true, true⟩ ∧
    (verdict { r848 with T := 772 }).exact = true ∧
    (verdict { r848 with T := 771 }).exact = false ∧
    (verdict { r848 with T := 827 }).bridge = true ∧
    (verdict { r848 with T := 826 }).bridge = false := by decide +kernel
theorem v849 :
    verdict r849 = ⟨true, true, 1, 1609, 9478, 3573, true, true, true⟩ ∧
    (verdict { r849 with T := 1508 }).exact = true ∧
    (verdict { r849 with T := 1507 }).exact = false ∧
    (verdict { r849 with T := 1631 }).bridge = true ∧
    (verdict { r849 with T := 1630 }).bridge = false := by decide +kernel
theorem v850 :
    verdict r850 = ⟨true, true, 1, 944, 3384, 1255, true, true, true⟩ ∧
    (verdict { r850 with T := 952 }).exact = true ∧
    (verdict { r850 with T := 951 }).exact = false ∧
    (verdict { r850 with T := 956 }).bridge = true ∧
    (verdict { r850 with T := 955 }).bridge = false := by decide +kernel
theorem v851 :
    verdict r851 = ⟨true, true, 1, 1859, 7312, 2756, true, true, true⟩ ∧
    (verdict { r851 with T := 2098 }).exact = true ∧
    (verdict { r851 with T := 2097 }).exact = false ∧
    (verdict { r851 with T := 2098 }).bridge = true ∧
    (verdict { r851 with T := 2097 }).bridge = false := by decide +kernel
theorem v852 :
    verdict r852 = ⟨true, true, 1, 1769, 14326, 4004, true, true, true⟩ ∧
    (verdict { r852 with T := 1645 }).exact = true ∧
    (verdict { r852 with T := 1644 }).exact = false ∧
    (verdict { r852 with T := 1769 }).bridge = true ∧
    (verdict { r852 with T := 1768 }).bridge = false := by decide +kernel
theorem v853 :
    verdict r853 = ⟨true, true, 1, 2044, 11044, 3083, true, true, true⟩ ∧
    (verdict { r853 with T := 1900 }).exact = true ∧
    (verdict { r853 with T := 1899 }).exact = false ∧
    (verdict { r853 with T := 2044 }).bridge = true ∧
    (verdict { r853 with T := 2043 }).bridge = false := by decide +kernel
theorem v854 :
    verdict r854 = ⟨true, true, 1, 1169, 7452, 1955, true, true, true⟩ ∧
    (verdict { r854 with T := 1014 }).exact = true ∧
    (verdict { r854 with T := 1013 }).exact = false ∧
    (verdict { r854 with T := 1169 }).bridge = true ∧
    (verdict { r854 with T := 1168 }).bridge = false := by decide +kernel
theorem v855 :
    verdict r855 = ⟨true, true, 1, 2327, 15736, 4230, true, true, true⟩ ∧
    (verdict { r855 with T := 2000 }).exact = true ∧
    (verdict { r855 with T := 1999 }).exact = false ∧
    (verdict { r855 with T := 2327 }).bridge = true ∧
    (verdict { r855 with T := 2326 }).bridge = false := by decide +kernel
theorem v856 :
    verdict r856 = ⟨true, true, 1, 1350, 5740, 1504, true, true, true⟩ ∧
    (verdict { r856 with T := 1171 }).exact = true ∧
    (verdict { r856 with T := 1170 }).exact = false ∧
    (verdict { r856 with T := 1350 }).bridge = true ∧
    (verdict { r856 with T := 1349 }).bridge = false := by decide +kernel
theorem v857 :
    verdict r857 = ⟨true, true, 1, 2688, 12143, 3264, true, true, true⟩ ∧
    (verdict { r857 with T := 2310 }).exact = true ∧
    (verdict { r857 with T := 2309 }).exact = false ∧
    (verdict { r857 with T := 2689 }).bridge = true ∧
    (verdict { r857 with T := 2688 }).bridge = false := by decide +kernel
theorem v858 :
    verdict r858 = ⟨true, true, 1, 561, 6821, 2655, true, true, true⟩ ∧
    (verdict { r858 with T := 437 }).exact = true ∧
    (verdict { r858 with T := 436 }).exact = false ∧
    (verdict { r858 with T := 561 }).bridge = true ∧
    (verdict { r858 with T := 560 }).bridge = false := by decide +kernel
theorem v859 :
    verdict r859 = ⟨true, true, 1, 649, 5249, 2041, true, true, true⟩ ∧
    (verdict { r859 with T := 702 }).exact = true ∧
    (verdict { r859 with T := 701 }).exact = false ∧
    (verdict { r859 with T := 702 }).bridge = true ∧
    (verdict { r859 with T := 701 }).bridge = false := by decide +kernel
theorem v860 :
    verdict r860 = ⟨true, true, 1, 524, 3808, 1466, true, true, true⟩ ∧
    (verdict { r860 with T := 565 }).exact = true ∧
    (verdict { r860 with T := 564 }).exact = false ∧
    (verdict { r860 with T := 565 }).bridge = true ∧
    (verdict { r860 with T := 564 }).bridge = false := by decide +kernel
theorem v861 :
    verdict r861 = ⟨true, true, 1, 1061, 8322, 3329, true, true, true⟩ ∧
    (verdict { r861 with T := 1313 }).exact = true ∧
    (verdict { r861 with T := 1312 }).exact = false ∧
    (verdict { r861 with T := 1313 }).bridge = true ∧
    (verdict { r861 with T := 1312 }).bridge = false := by decide +kernel
theorem v862 :
    verdict r862 = ⟨true, true, 1, 606, 2930, 1126, true, true, true⟩ ∧
    (verdict { r862 with T := 801 }).exact = true ∧
    (verdict { r862 with T := 800 }).exact = false ∧
    (verdict { r862 with T := 801 }).bridge = true ∧
    (verdict { r862 with T := 800 }).bridge = false := by decide +kernel
theorem v863 :
    verdict r863 = ⟨true, true, 1, 1226, 6423, 2568, true, true, true⟩ ∧
    (verdict { r863 with T := 1805 }).exact = true ∧
    (verdict { r863 with T := 1804 }).exact = false ∧
    (verdict { r863 with T := 1805 }).bridge = true ∧
    (verdict { r863 with T := 1804 }).bridge = false := by decide +kernel
theorem v864 :
    verdict r864 = ⟨true, true, 1, 891, 11832, 2985, true, true, true⟩ ∧
    (verdict { r864 with T := 767 }).exact = true ∧
    (verdict { r864 with T := 766 }).exact = false ∧
    (verdict { r864 with T := 891 }).bridge = true ∧
    (verdict { r864 with T := 890 }).bridge = false := by decide +kernel
theorem v865 :
    verdict r865 = ⟨true, true, 1, 1030, 9115, 2296, true, true, true⟩ ∧
    (verdict { r865 with T := 886 }).exact = true ∧
    (verdict { r865 with T := 885 }).exact = false ∧
    (verdict { r865 with T := 1030 }).bridge = true ∧
    (verdict { r865 with T := 1029 }).bridge = false := by decide +kernel
theorem v866 :
    verdict r866 = ⟨true, true, 1, 646, 6519, 1480, true, true, true⟩ ∧
    (verdict { r866 with T := 680 }).exact = true ∧
    (verdict { r866 with T := 679 }).exact = false ∧
    (verdict { r866 with T := 735 }).bridge = true ∧
    (verdict { r866 with T := 734 }).bridge = false := by decide +kernel
theorem v867 :
    verdict r867 = ⟨true, true, 1, 1271, 13842, 3267, true, true, true⟩ ∧
    (verdict { r867 with T := 1386 }).exact = true ∧
    (verdict { r867 with T := 1385 }).exact = false ∧
    (verdict { r867 with T := 1461 }).bridge = true ∧
    (verdict { r867 with T := 1460 }).bridge = false := by decide +kernel
theorem v868 :
    verdict r868 = ⟨true, true, 1, 746, 5021, 1138, true, true, true⟩ ∧
    (verdict { r868 with T := 907 }).exact = true ∧
    (verdict { r868 with T := 906 }).exact = false ∧
    (verdict { r868 with T := 907 }).bridge = true ∧
    (verdict { r868 with T := 906 }).bridge = false := by decide +kernel
theorem v869 :
    verdict r869 = ⟨true, true, 1, 1469, 10682, 2520, true, true, true⟩ ∧
    (verdict { r869 with T := 2013 }).exact = true ∧
    (verdict { r869 with T := 2012 }).exact = false ∧
    (verdict { r869 with T := 2013 }).bridge = true ∧
    (verdict { r869 with T := 2012 }).bridge = false := by decide +kernel
theorem v870 :
    verdict r870 = ⟨true, true, 1, 966, 8061, 3060, true, true, true⟩ ∧
    (verdict { r870 with T := 842 }).exact = true ∧
    (verdict { r870 with T := 841 }).exact = false ∧
    (verdict { r870 with T := 966 }).bridge = true ∧
    (verdict { r870 with T := 965 }).bridge = false := by decide +kernel
theorem v871 :
    verdict r871 = ⟨true, true, 1, 1117, 6208, 2354, true, true, true⟩ ∧
    (verdict { r871 with T := 973 }).exact = true ∧
    (verdict { r871 with T := 972 }).exact = false ∧
    (verdict { r871 with T := 1117 }).bridge = true ∧
    (verdict { r871 with T := 1116 }).bridge = false := by decide +kernel
theorem v872 :
    verdict r872 = ⟨true, true, 1, 710, 4430, 1663, true, true, true⟩ ∧
    (verdict { r872 with T := 687 }).exact = true ∧
    (verdict { r872 with T := 686 }).exact = false ∧
    (verdict { r872 with T := 739 }).bridge = true ∧
    (verdict { r872 with T := 738 }).bridge = false := by decide +kernel
theorem v873 :
    verdict r873 = ⟨true, true, 1, 1469, 9428, 3684, true, true, true⟩ ∧
    (verdict { r873 with T := 1375 }).exact = true ∧
    (verdict { r873 with T := 1374 }).exact = false ∧
    (verdict { r873 with T := 1490 }).bridge = true ∧
    (verdict { r873 with T := 1489 }).bridge = false := by decide +kernel
theorem v874 :
    verdict r874 = ⟨true, true, 1, 820, 3407, 1278, true, true, true⟩ ∧
    (verdict { r874 with T := 864 }).exact = true ∧
    (verdict { r874 with T := 863 }).exact = false ∧
    (verdict { r874 with T := 864 }).bridge = true ∧
    (verdict { r874 with T := 863 }).bridge = false := by decide +kernel
theorem v875 :
    verdict r875 = ⟨true, true, 1, 1697, 7273, 2842, true, true, true⟩ ∧
    (verdict { r875 with T := 1914 }).exact = true ∧
    (verdict { r875 with T := 1913 }).exact = false ∧
    (verdict { r875 with T := 1914 }).bridge = true ∧
    (verdict { r875 with T := 1913 }).bridge = false := by decide +kernel
theorem v876 :
    verdict r876 = ⟨true, true, 1, 1374, 11075, 3468, true, true, true⟩ ∧
    (verdict { r876 with T := 1250 }).exact = true ∧
    (verdict { r876 with T := 1249 }).exact = false ∧
    (verdict { r876 with T := 1374 }).bridge = true ∧
    (verdict { r876 with T := 1373 }).bridge = false := by decide +kernel
theorem v877 :
    verdict r877 = ⟨true, true, 1, 1588, 8532, 2669, true, true, true⟩ ∧
    (verdict { r877 with T := 1444 }).exact = true ∧
    (verdict { r877 with T := 1443 }).exact = false ∧
    (verdict { r877 with T := 1588 }).bridge = true ∧
    (verdict { r877 with T := 1587 }).bridge = false := by decide +kernel
theorem v878 :
    verdict r878 = ⟨true, true, 1, 914, 6418, 1805, true, true, true⟩ ∧
    (verdict { r878 with T := 893 }).exact = true ∧
    (verdict { r878 with T := 892 }).exact = false ∧
    (verdict { r878 with T := 942 }).bridge = true ∧
    (verdict { r878 with T := 941 }).bridge = false := by decide +kernel
theorem v879 :
    verdict r879 = ⟨true, true, 1, 1881, 13568, 3983, true, true, true⟩ ∧
    (verdict { r879 with T := 1793 }).exact = true ∧
    (verdict { r879 with T := 1792 }).exact = false ∧
    (verdict { r879 with T := 1906 }).bridge = true ∧
    (verdict { r879 with T := 1905 }).bridge = false := by decide +kernel
theorem v880 :
    verdict r880 = ⟨true, true, 1, 1056, 4943, 1388, true, true, true⟩ ∧
    (verdict { r880 with T := 1031 }).exact = true ∧
    (verdict { r880 with T := 1030 }).exact = false ∧
    (verdict { r880 with T := 1088 }).bridge = true ∧
    (verdict { r880 with T := 1087 }).bridge = false := by decide +kernel
theorem v881 :
    verdict r881 = ⟨true, true, 1, 2173, 10470, 3073, true, true, true⟩ ∧
    (verdict { r881 with T := 2136 }).exact = true ∧
    (verdict { r881 with T := 2135 }).exact = false ∧
    (verdict { r881 with T := 2202 }).bridge = true ∧
    (verdict { r881 with T := 2201 }).bridge = false := by decide +kernel
theorem v882 :
    verdict r882 = ⟨true, true, 1, 908, 11575, 3002, true, true, true⟩ ∧
    (verdict { r882 with T := 784 }).exact = true ∧
    (verdict { r882 with T := 783 }).exact = false ∧
    (verdict { r882 with T := 908 }).bridge = true ∧
    (verdict { r882 with T := 907 }).bridge = false := by decide +kernel
theorem v883 :
    verdict r883 = ⟨true, true, 1, 1050, 8915, 2309, true, true, true⟩ ∧
    (verdict { r883 with T := 906 }).exact = true ∧
    (verdict { r883 with T := 905 }).exact = false ∧
    (verdict { r883 with T := 1050 }).bridge = true ∧
    (verdict { r883 with T := 1049 }).bridge = false := by decide +kernel
theorem v884 :
    verdict r884 = ⟨true, true, 1, 614, 6554, 1487, true, true, true⟩ ∧
    (verdict { r884 with T := 638 }).exact = true ∧
    (verdict { r884 with T := 637 }).exact = false ∧
    (verdict { r884 with T := 696 }).bridge = true ∧
    (verdict { r884 with T := 695 }).bridge = false := by decide +kernel
theorem v885 :
    verdict r885 = ⟨true, true, 1, 1241, 13586, 3289, true, true, true⟩ ∧
    (verdict { r885 with T := 1369 }).exact = true ∧
    (verdict { r885 with T := 1368 }).exact = false ∧
    (verdict { r885 with T := 1413 }).bridge = true ∧
    (verdict { r885 with T := 1412 }).bridge = false := by decide +kernel
theorem v886 :
    verdict r886 = ⟨true, true, 1, 710, 5043, 1142, true, true, true⟩ ∧
    (verdict { r886 with T := 885 }).exact = true ∧
    (verdict { r886 with T := 884 }).exact = false ∧
    (verdict { r886 with T := 885 }).bridge = true ∧
    (verdict { r886 with T := 884 }).bridge = false := by decide +kernel
theorem v887 :
    verdict r887 = ⟨true, true, 1, 1434, 10481, 2538, true, true, true⟩ ∧
    (verdict { r887 with T := 1981 }).exact = true ∧
    (verdict { r887 with T := 1980 }).exact = false ∧
    (verdict { r887 with T := 1981 }).bridge = true ∧
    (verdict { r887 with T := 1980 }).bridge = false := by decide +kernel
theorem v888 :
    verdict r888 = ⟨true, true, 1, 1117, 10041, 2998, true, true, true⟩ ∧
    (verdict { r888 with T := 780 }).exact = true ∧
    (verdict { r888 with T := 779 }).exact = false ∧
    (verdict { r888 with T := 1117 }).bridge = true ∧
    (verdict { r888 with T := 1116 }).bridge = false := by decide +kernel
theorem v889 :
    verdict r889 = ⟨true, true, 1, 1291, 7734, 2306, true, true, true⟩ ∧
    (verdict { r889 with T := 1147 }).exact = true ∧
    (verdict { r889 with T := 1146 }).exact = false ∧
    (verdict { r889 with T := 1291 }).bridge = true ∧
    (verdict { r889 with T := 1290 }).bridge = false := by decide +kernel
theorem v890 :
    verdict r890 = ⟨true, true, 1, 705, 5616, 1425, true, true, true⟩ ∧
    (verdict { r890 with T := 578 }).exact = true ∧
    (verdict { r890 with T := 577 }).exact = false ∧
    (verdict { r890 with T := 794 }).bridge = true ∧
    (verdict { r890 with T := 793 }).bridge = false := by decide +kernel
theorem v891 :
    verdict r891 = ⟨true, true, 1, 1478, 12168, 3238, true, true, true⟩ ∧
    (verdict { r891 with T := 1545 }).exact = true ∧
    (verdict { r891 with T := 1544 }).exact = false ∧
    (verdict { r891 with T := 1668 }).bridge = true ∧
    (verdict { r891 with T := 1667 }).bridge = false := by decide +kernel
theorem v892 :
    verdict r892 = ⟨true, true, 1, 814, 4319, 1095, true, true, true⟩ ∧
    (verdict { r892 with T := 936 }).exact = true ∧
    (verdict { r892 with T := 935 }).exact = false ∧
    (verdict { r892 with T := 936 }).bridge = true ∧
    (verdict { r892 with T := 935 }).bridge = false := by decide +kernel
theorem v893 :
    verdict r893 = ⟨true, true, 1, 1707, 9387, 2498, true, true, true⟩ ∧
    (verdict { r893 with T := 2117 }).exact = true ∧
    (verdict { r893 with T := 2116 }).exact = false ∧
    (verdict { r893 with T := 2117 }).bridge = true ∧
    (verdict { r893 with T := 2116 }).bridge = false := by decide +kernel
theorem v894 :
    verdict r894 = ⟨true, true, 1, 1446, 11691, 3612, true, true, true⟩ ∧
    (verdict { r894 with T := 1181 }).exact = true ∧
    (verdict { r894 with T := 1180 }).exact = false ∧
    (verdict { r894 with T := 1446 }).bridge = true ∧
    (verdict { r894 with T := 1445 }).bridge = false := by decide +kernel
theorem v895 :
    verdict r895 = ⟨true, true, 1, 1671, 9007, 2780, true, true, true⟩ ∧
    (verdict { r895 with T := 1364 }).exact = true ∧
    (verdict { r895 with T := 1363 }).exact = false ∧
    (verdict { r895 with T := 1671 }).bridge = true ∧
    (verdict { r895 with T := 1670 }).bridge = false := by decide +kernel
theorem v896 :
    verdict r896 = ⟨true, true, 1, 919, 6519, 2208, true, true, true⟩ ∧
    (verdict { r896 with T := 914 }).exact = true ∧
    (verdict { r896 with T := 913 }).exact = false ∧
    (verdict { r896 with T := 959 }).bridge = true ∧
    (verdict { r896 with T := 958 }).bridge = false := by decide +kernel
theorem v897 :
    verdict r897 = ⟨true, true, 1, 1800, 13851, 4856, true, true, true⟩ ∧
    (verdict { r897 with T := 1794 }).exact = true ∧
    (verdict { r897 with T := 1793 }).exact = false ∧
    (verdict { r897 with T := 1894 }).bridge = true ∧
    (verdict { r897 with T := 1893 }).bridge = false := by decide +kernel
theorem v898 :
    verdict r898 = ⟨true, true, 1, 1062, 5021, 1699, true, true, true⟩ ∧
    (verdict { r898 with T := 1141 }).exact = true ∧
    (verdict { r898 with T := 1140 }).exact = false ∧
    (verdict { r898 with T := 1141 }).bridge = true ∧
    (verdict { r898 with T := 1140 }).bridge = false := by decide +kernel
theorem v899 :
    verdict r899 = ⟨true, true, 1, 2080, 10688, 3747, true, true, true⟩ ∧
    (verdict { r899 with T := 2569 }).exact = true ∧
    (verdict { r899 with T := 2568 }).exact = false ∧
    (verdict { r899 with T := 2569 }).bridge = true ∧
    (verdict { r899 with T := 2568 }).bridge = false := by decide +kernel

end Formal.Timing.ChainSettleExe.GcdD
