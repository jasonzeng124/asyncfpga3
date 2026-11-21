import Formal.Timing.ChainSettleExeGcdDData1

/-! C-10o2 GENERATED: kernel-decided verdicts of chunk 1 (see ChainSettleExe.verdict).
Per row: `verdict` at chainck's late side `T`; exact PASS at `T*` and FAIL at `T* - 1`
(margin_exact = T - T*); bridge PASS at `Tb*` and FAIL at `Tb* - 1`. -/

namespace Formal.Timing.ChainSettleExe.GcdD
open Formal.Timing Formal.Timing.ChainSettleExe

theorem v150 :
    verdict r150 = ⟨true, true, 1, 964, 6701, 2947, true, true, true⟩ ∧
    (verdict { r150 with T := 729 }).exact = true ∧
    (verdict { r150 with T := 728 }).exact = false ∧
    (verdict { r150 with T := 964 }).bridge = true ∧
    (verdict { r150 with T := 963 }).bridge = false := by decide +kernel
theorem v151 :
    verdict r151 = ⟨true, true, 1, 1115, 5157, 2267, true, true, true⟩ ∧
    (verdict { r151 with T := 842 }).exact = true ∧
    (verdict { r151 with T := 841 }).exact = false ∧
    (verdict { r151 with T := 1115 }).bridge = true ∧
    (verdict { r151 with T := 1114 }).bridge = false := by decide +kernel
theorem v152 :
    verdict r152 = ⟨true, true, 1, 653, 3538, 1627, true, true, true⟩ ∧
    (verdict { r152 with T := 603 }).exact = true ∧
    (verdict { r152 with T := 602 }).exact = false ∧
    (verdict { r152 with T := 658 }).bridge = true ∧
    (verdict { r152 with T := 657 }).bridge = false := by decide +kernel
theorem v153 :
    verdict r153 = ⟨true, true, 1, 1454, 8135, 3747, true, true, true⟩ ∧
    (verdict { r153 with T := 1180 }).exact = true ∧
    (verdict { r153 with T := 1179 }).exact = false ∧
    (verdict { r153 with T := 1455 }).bridge = true ∧
    (verdict { r153 with T := 1454 }).bridge = false := by decide +kernel
theorem v154 :
    verdict r154 = ⟨true, true, 1, 755, 2721, 1251, true, true, true⟩ ∧
    (verdict { r154 with T := 821 }).exact = true ∧
    (verdict { r154 with T := 820 }).exact = false ∧
    (verdict { r154 with T := 821 }).bridge = true ∧
    (verdict { r154 with T := 820 }).bridge = false := by decide +kernel
theorem v155 :
    verdict r155 = ⟨true, true, 1, 1680, 6276, 2890, true, true, true⟩ ∧
    (verdict { r155 with T := 1896 }).exact = true ∧
    (verdict { r155 with T := 1895 }).exact = false ∧
    (verdict { r155 with T := 1896 }).bridge = true ∧
    (verdict { r155 with T := 1895 }).bridge = false := by decide +kernel
theorem v156 :
    verdict r156 = ⟨true, true, 1, 1425, 11714, 3535, true, true, true⟩ ∧
    (verdict { r156 with T := 1317 }).exact = true ∧
    (verdict { r156 with T := 1316 }).exact = false ∧
    (verdict { r156 with T := 1440 }).bridge = true ∧
    (verdict { r156 with T := 1439 }).bridge = false := by decide +kernel
theorem v157 :
    verdict r157 = ⟨true, true, 1, 1647, 9028, 2720, true, true, true⟩ ∧
    (verdict { r157 with T := 1521 }).exact = true ∧
    (verdict { r157 with T := 1520 }).exact = false ∧
    (verdict { r157 with T := 1664 }).bridge = true ∧
    (verdict { r157 with T := 1663 }).bridge = false := by decide +kernel
theorem v158 :
    verdict r158 = ⟨true, true, 1, 1219, 7455, 2158, true, true, true⟩ ∧
    (verdict { r158 with T := 1089 }).exact = true ∧
    (verdict { r158 with T := 1088 }).exact = false ∧
    (verdict { r158 with T := 1224 }).bridge = true ∧
    (verdict { r158 with T := 1223 }).bridge = false := by decide +kernel
theorem v159 :
    verdict r159 = ⟨true, true, 1, 2228, 14371, 4477, true, true, true⟩ ∧
    (verdict { r159 with T := 1973 }).exact = true ∧
    (verdict { r159 with T := 1972 }).exact = false ∧
    (verdict { r159 with T := 2245 }).bridge = true ∧
    (verdict { r159 with T := 2244 }).bridge = false := by decide +kernel
theorem v160 :
    verdict r160 = ⟨true, true, 1, 1408, 5746, 1661, true, true, true⟩ ∧
    (verdict { r160 with T := 1259 }).exact = true ∧
    (verdict { r160 with T := 1258 }).exact = false ∧
    (verdict { r160 with T := 1413 }).bridge = true ∧
    (verdict { r160 with T := 1412 }).bridge = false := by decide +kernel
theorem v161 :
    verdict r161 = ⟨true, true, 1, 2573, 11090, 3454, true, true, true⟩ ∧
    (verdict { r161 with T := 2451 }).exact = true ∧
    (verdict { r161 with T := 2450 }).exact = false ∧
    (verdict { r161 with T := 2594 }).bridge = true ∧
    (verdict { r161 with T := 2593 }).bridge = false := by decide +kernel
theorem v162 :
    verdict r162 = ⟨true, true, 1, 1644, 13066, 3738, true, true, true⟩ ∧
    (verdict { r162 with T := 1520 }).exact = true ∧
    (verdict { r162 with T := 1519 }).exact = false ∧
    (verdict { r162 with T := 1644 }).bridge = true ∧
    (verdict { r162 with T := 1643 }).bridge = false := by decide +kernel
theorem v163 :
    verdict r163 = ⟨true, true, 1, 1900, 10065, 2877, true, true, true⟩ ∧
    (verdict { r163 with T := 1756 }).exact = true ∧
    (verdict { r163 with T := 1755 }).exact = false ∧
    (verdict { r163 with T := 1900 }).bridge = true ∧
    (verdict { r163 with T := 1899 }).bridge = false := by decide +kernel
theorem v164 :
    verdict r164 = ⟨true, true, 1, 1231, 7254, 2075, true, true, true⟩ ∧
    (verdict { r164 with T := 1187 }).exact = true ∧
    (verdict { r164 with T := 1186 }).exact = false ∧
    (verdict { r164 with T := 1235 }).bridge = true ∧
    (verdict { r164 with T := 1234 }).bridge = false := by decide +kernel
theorem v165 :
    verdict r165 = ⟨true, true, 1, 2346, 15132, 4376, true, true, true⟩ ∧
    (verdict { r165 with T := 2235 }).exact = true ∧
    (verdict { r165 with T := 2234 }).exact = false ∧
    (verdict { r165 with T := 2348 }).bridge = true ∧
    (verdict { r165 with T := 2347 }).bridge = false := by decide +kernel
theorem v166 :
    verdict r166 = ⟨true, true, 1, 1422, 5587, 1597, true, true, true⟩ ∧
    (verdict { r166 with T := 1371 }).exact = true ∧
    (verdict { r166 with T := 1370 }).exact = false ∧
    (verdict { r166 with T := 1427 }).bridge = true ∧
    (verdict { r166 with T := 1426 }).bridge = false := by decide +kernel
theorem v167 :
    verdict r167 = ⟨true, true, 1, 2711, 11677, 3377, true, true, true⟩ ∧
    (verdict { r167 with T := 2582 }).exact = true ∧
    (verdict { r167 with T := 2581 }).exact = false ∧
    (verdict { r167 with T := 2713 }).bridge = true ∧
    (verdict { r167 with T := 2712 }).bridge = false := by decide +kernel
theorem v168 :
    verdict r168 = ⟨true, true, 1, 969, 8321, 2850, true, true, true⟩ ∧
    (verdict { r168 with T := 632 }).exact = true ∧
    (verdict { r168 with T := 631 }).exact = false ∧
    (verdict { r168 with T := 969 }).bridge = true ∧
    (verdict { r168 with T := 968 }).bridge = false := by decide +kernel
theorem v169 :
    verdict r169 = ⟨true, true, 1, 1120, 6407, 2192, true, true, true⟩ ∧
    (verdict { r169 with T := 800 }).exact = true ∧
    (verdict { r169 with T := 799 }).exact = false ∧
    (verdict { r169 with T := 1120 }).bridge = true ∧
    (verdict { r169 with T := 1119 }).bridge = false := by decide +kernel
theorem v170 :
    verdict r170 = ⟨true, true, 1, 635, 4388, 1449, true, true, true⟩ ∧
    (verdict { r170 with T := 552 }).exact = true ∧
    (verdict { r170 with T := 551 }).exact = false ∧
    (verdict { r170 with T := 724 }).bridge = true ∧
    (verdict { r170 with T := 723 }).bridge = false := by decide +kernel
theorem v171 :
    verdict r171 = ⟨true, true, 1, 1301, 9395, 3294, true, true, true⟩ ∧
    (verdict { r171 with T := 1394 }).exact = true ∧
    (verdict { r171 with T := 1393 }).exact = false ∧
    (verdict { r171 with T := 1491 }).bridge = true ∧
    (verdict { r171 with T := 1490 }).bridge = false := by decide +kernel
theorem v172 :
    verdict r172 = ⟨true, true, 1, 733, 3378, 1114, true, true, true⟩ ∧
    (verdict { r172 with T := 904 }).exact = true ∧
    (verdict { r172 with T := 903 }).exact = false ∧
    (verdict { r172 with T := 904 }).bridge = true ∧
    (verdict { r172 with T := 903 }).bridge = false := by decide +kernel
theorem v173 :
    verdict r173 = ⟨true, true, 1, 1503, 7249, 2541, true, true, true⟩ ∧
    (verdict { r173 with T := 2030 }).exact = true ∧
    (verdict { r173 with T := 2029 }).exact = false ∧
    (verdict { r173 with T := 2030 }).bridge = true ∧
    (verdict { r173 with T := 2029 }).bridge = false := by decide +kernel
theorem v174 :
    verdict r174 = ⟨true, true, 1, 720, 12468, 2814, true, true, true⟩ ∧
    (verdict { r174 with T := 735 }).exact = true ∧
    (verdict { r174 with T := 734 }).exact = false ∧
    (verdict { r174 with T := 932 }).bridge = true ∧
    (verdict { r174 with T := 931 }).bridge = false := by decide +kernel
theorem v175 :
    verdict r175 = ⟨true, true, 1, 833, 9591, 2164, true, true, true⟩ ∧
    (verdict { r175 with T := 935 }).exact = true ∧
    (verdict { r175 with T := 934 }).exact = false ∧
    (verdict { r175 with T := 1078 }).bridge = true ∧
    (verdict { r175 with T := 1077 }).bridge = false := by decide +kernel
theorem v176 :
    verdict r176 = ⟨true, true, 1, 597, 6935, 1745, true, true, true⟩ ∧
    (verdict { r176 with T := 620 }).exact = true ∧
    (verdict { r176 with T := 619 }).exact = false ∧
    (verdict { r176 with T := 705 }).bridge = true ∧
    (verdict { r176 with T := 704 }).bridge = false := by decide +kernel
theorem v177 :
    verdict r177 = ⟨true, true, 1, 1107, 15443, 3798, true, true, true⟩ ∧
    (verdict { r177 with T := 1394 }).exact = true ∧
    (verdict { r177 with T := 1393 }).exact = false ∧
    (verdict { r177 with T := 1394 }).bridge = true ∧
    (verdict { r177 with T := 1393 }).bridge = false := by decide +kernel
theorem v178 :
    verdict r178 = ⟨true, true, 1, 690, 5330, 1341, true, true, true⟩ ∧
    (verdict { r178 with T := 846 }).exact = true ∧
    (verdict { r178 with T := 845 }).exact = false ∧
    (verdict { r178 with T := 846 }).bridge = true ∧
    (verdict { r178 with T := 845 }).bridge = false := by decide +kernel
theorem v179 :
    verdict r179 = ⟨true, true, 1, 1279, 11914, 2931, true, true, true⟩ ∧
    (verdict { r179 with T := 1973 }).exact = true ∧
    (verdict { r179 with T := 1972 }).exact = false ∧
    (verdict { r179 with T := 1973 }).bridge = true ∧
    (verdict { r179 with T := 1972 }).bridge = false := by decide +kernel
theorem v180 :
    verdict r180 = ⟨true, true, 1, 1646, 14276, 3600, true, true, true⟩ ∧
    (verdict { r180 with T := 1382 }).exact = true ∧
    (verdict { r180 with T := 1381 }).exact = false ∧
    (verdict { r180 with T := 1718 }).bridge = true ∧
    (verdict { r180 with T := 1717 }).bridge = false := by decide +kernel
theorem v181 :
    verdict r181 = ⟨true, true, 1, 1902, 10999, 2771, true, true, true⟩ ∧
    (verdict { r181 with T := 1597 }).exact = true ∧
    (verdict { r181 with T := 1596 }).exact = false ∧
    (verdict { r181 with T := 1986 }).bridge = true ∧
    (verdict { r181 with T := 1985 }).bridge = false := by decide +kernel
theorem v182 :
    verdict r182 = ⟨true, true, 1, 1115, 7919, 1737, true, true, true⟩ ∧
    (verdict { r182 with T := 804 }).exact = true ∧
    (verdict { r182 with T := 803 }).exact = false ∧
    (verdict { r182 with T := 1120 }).bridge = true ∧
    (verdict { r182 with T := 1119 }).bridge = false := by decide +kernel
theorem v183 :
    verdict r183 = ⟨true, true, 1, 2228, 16681, 3790, true, true, true⟩ ∧
    (verdict { r183 with T := 1545 }).exact = true ∧
    (verdict { r183 with T := 1544 }).exact = false ∧
    (verdict { r183 with T := 2229 }).bridge = true ∧
    (verdict { r183 with T := 2228 }).bridge = false := by decide +kernel
theorem v184 :
    verdict r184 = ⟨true, true, 1, 1287, 6092, 1336, true, true, true⟩ ∧
    (verdict { r184 with T := 1229 }).exact = true ∧
    (verdict { r184 with T := 1228 }).exact = false ∧
    (verdict { r184 with T := 1293 }).bridge = true ∧
    (verdict { r184 with T := 1292 }).bridge = false := by decide +kernel
theorem v185 :
    verdict r185 = ⟨true, true, 1, 2573, 12873, 2924, true, true, true⟩ ∧
    (verdict { r185 with T := 2432 }).exact = true ∧
    (verdict { r185 with T := 2431 }).exact = false ∧
    (verdict { r185 with T := 2575 }).bridge = true ∧
    (verdict { r185 with T := 2574 }).bridge = false := by decide +kernel
theorem v186 :
    verdict r186 = ⟨true, true, 1, 1357, 12018, 3451, true, true, true⟩ ∧
    (verdict { r186 with T := 1253 }).exact = true ∧
    (verdict { r186 with T := 1252 }).exact = false ∧
    (verdict { r186 with T := 1376 }).bridge = true ∧
    (verdict { r186 with T := 1375 }).bridge = false := by decide +kernel
theorem v187 :
    verdict r187 = ⟨true, true, 1, 1568, 9258, 2656, true, true, true⟩ ∧
    (verdict { r187 with T := 1448 }).exact = true ∧
    (verdict { r187 with T := 1447 }).exact = false ∧
    (verdict { r187 with T := 1591 }).bridge = true ∧
    (verdict { r187 with T := 1590 }).bridge = false := by decide +kernel
theorem v188 :
    verdict r188 = ⟨true, true, 1, 897, 6481, 1674, true, true, true⟩ ∧
    (verdict { r188 with T := 742 }).exact = true ∧
    (verdict { r188 with T := 741 }).exact = false ∧
    (verdict { r188 with T := 937 }).bridge = true ∧
    (verdict { r188 with T := 936 }).bridge = false := by decide +kernel
theorem v189 :
    verdict r189 = ⟨true, true, 1, 1841, 13828, 3748, true, true, true⟩ ∧
    (verdict { r189 with T := 1514 }).exact = true ∧
    (verdict { r189 with T := 1513 }).exact = false ∧
    (verdict { r189 with T := 1901 }).bridge = true ∧
    (verdict { r189 with T := 1900 }).bridge = false := by decide +kernel
theorem v190 :
    verdict r190 = ⟨true, true, 1, 1036, 4991, 1288, true, true, true⟩ ∧
    (verdict { r190 with T := 1018 }).exact = true ∧
    (verdict { r190 with T := 1017 }).exact = false ∧
    (verdict { r190 with T := 1082 }).bridge = true ∧
    (verdict { r190 with T := 1081 }).bridge = false := by decide +kernel
theorem v191 :
    verdict r191 = ⟨true, true, 1, 2127, 10671, 2892, true, true, true⟩ ∧
    (verdict { r191 with T := 2242 }).exact = true ∧
    (verdict { r191 with T := 2241 }).exact = false ∧
    (verdict { r191 with T := 2242 }).bridge = true ∧
    (verdict { r191 with T := 2241 }).bridge = false := by decide +kernel
theorem v192 :
    verdict r192 = ⟨true, true, 1, 1392, 13927, 3370, true, true, true⟩ ∧
    (verdict { r192 with T := 1152 }).exact = true ∧
    (verdict { r192 with T := 1151 }).exact = false ∧
    (verdict { r192 with T := 1392 }).bridge = true ∧
    (verdict { r192 with T := 1391 }).bridge = false := by decide +kernel
theorem v193 :
    verdict r193 = ⟨true, true, 1, 1609, 10717, 2593, true, true, true⟩ ∧
    (verdict { r193 with T := 1331 }).exact = true ∧
    (verdict { r193 with T := 1330 }).exact = false ∧
    (verdict { r193 with T := 1609 }).bridge = true ∧
    (verdict { r193 with T := 1608 }).bridge = false := by decide +kernel
theorem v194 :
    verdict r194 = ⟨true, true, 1, 1118, 7942, 1898, true, true, true⟩ ∧
    (verdict { r194 with T := 979 }).exact = true ∧
    (verdict { r194 with T := 978 }).exact = false ∧
    (verdict { r194 with T := 1123 }).bridge = true ∧
    (verdict { r194 with T := 1122 }).bridge = false := by decide +kernel
theorem v195 :
    verdict r195 = ⟨true, true, 1, 2116, 17417, 4041, true, true, true⟩ ∧
    (verdict { r195 with T := 1836 }).exact = true ∧
    (verdict { r195 with T := 1835 }).exact = false ∧
    (verdict { r195 with T := 2117 }).bridge = true ∧
    (verdict { r195 with T := 2116 }).bridge = false := by decide +kernel
theorem v196 :
    verdict r196 = ⟨true, true, 1, 1291, 6108, 1460, true, true, true⟩ ∧
    (verdict { r196 with T := 1130 }).exact = true ∧
    (verdict { r196 with T := 1129 }).exact = false ∧
    (verdict { r196 with T := 1297 }).bridge = true ∧
    (verdict { r196 with T := 1296 }).bridge = false := by decide +kernel
theorem v197 :
    verdict r197 = ⟨true, true, 1, 2444, 13435, 3117, true, true, true⟩ ∧
    (verdict { r197 with T := 2127 }).exact = true ∧
    (verdict { r197 with T := 2126 }).exact = false ∧
    (verdict { r197 with T := 2446 }).bridge = true ∧
    (verdict { r197 with T := 2445 }).bridge = false := by decide +kernel
theorem v198 :
    verdict r198 = ⟨true, true, 1, 895, 12803, 2989, true, true, true⟩ ∧
    (verdict { r198 with T := 771 }).exact = true ∧
    (verdict { r198 with T := 770 }).exact = false ∧
    (verdict { r198 with T := 895 }).bridge = true ∧
    (verdict { r198 with T := 894 }).bridge = false := by decide +kernel
theorem v199 :
    verdict r199 = ⟨true, true, 1, 1035, 9849, 2299, true, true, true⟩ ∧
    (verdict { r199 with T := 891 }).exact = true ∧
    (verdict { r199 with T := 890 }).exact = false ∧
    (verdict { r199 with T := 1035 }).bridge = true ∧
    (verdict { r199 with T := 1034 }).bridge = false := by decide +kernel
theorem v200 :
    verdict r200 = ⟨true, true, 1, 559, 7183, 1776, true, true, true⟩ ∧
    (verdict { r200 with T := 579 }).exact = true ∧
    (verdict { r200 with T := 578 }).exact = false ∧
    (verdict { r200 with T := 632 }).bridge = true ∧
    (verdict { r200 with T := 631 }).bridge = false := by decide +kernel
theorem v201 :
    verdict r201 = ⟨true, true, 1, 1190, 16419, 4067, true, true, true⟩ ∧
    (verdict { r201 with T := 1235 }).exact = true ∧
    (verdict { r201 with T := 1234 }).exact = false ∧
    (verdict { r201 with T := 1353 }).bridge = true ∧
    (verdict { r201 with T := 1352 }).bridge = false := by decide +kernel
theorem v202 :
    verdict r202 = ⟨true, true, 1, 645, 5522, 1365, true, true, true⟩ ∧
    (verdict { r202 with T := 766 }).exact = true ∧
    (verdict { r202 with T := 765 }).exact = false ∧
    (verdict { r202 with T := 766 }).bridge = true ∧
    (verdict { r202 with T := 765 }).bridge = false := by decide +kernel
theorem v203 :
    verdict r203 = ⟨true, true, 1, 1375, 12666, 3137, true, true, true⟩ ∧
    (verdict { r203 with T := 1807 }).exact = true ∧
    (verdict { r203 with T := 1806 }).exact = false ∧
    (verdict { r203 with T := 1807 }).bridge = true ∧
    (verdict { r203 with T := 1806 }).bridge = false := by decide +kernel
theorem v204 :
    verdict r204 = ⟨true, true, 1, 561, 10751, 2655, true, true, true⟩ ∧
    (verdict { r204 with T := 437 }).exact = true ∧
    (verdict { r204 with T := 436 }).exact = false ∧
    (verdict { r204 with T := 561 }).bridge = true ∧
    (verdict { r204 with T := 560 }).bridge = false := by decide +kernel
theorem v205 :
    verdict r205 = ⟨true, true, 1, 649, 8276, 2041, true, true, true⟩ ∧
    (verdict { r205 with T := 702 }).exact = true ∧
    (verdict { r205 with T := 701 }).exact = false ∧
    (verdict { r205 with T := 702 }).bridge = true ∧
    (verdict { r205 with T := 701 }).bridge = false := by decide +kernel
theorem v206 :
    verdict r206 = ⟨true, true, 1, 516, 6223, 1458, true, true, true⟩ ∧
    (verdict { r206 with T := 565 }).exact = true ∧
    (verdict { r206 with T := 564 }).exact = false ∧
    (verdict { r206 with T := 565 }).bridge = true ∧
    (verdict { r206 with T := 564 }).bridge = false := by decide +kernel
theorem v207 :
    verdict r207 = ⟨true, true, 1, 1053, 13602, 3321, true, true, true⟩ ∧
    (verdict { r207 with T := 1313 }).exact = true ∧
    (verdict { r207 with T := 1312 }).exact = false ∧
    (verdict { r207 with T := 1313 }).bridge = true ∧
    (verdict { r207 with T := 1312 }).bridge = false := by decide +kernel
theorem v208 :
    verdict r208 = ⟨true, true, 1, 596, 4790, 1120, true, true, true⟩ ∧
    (verdict { r208 with T := 798 }).exact = true ∧
    (verdict { r208 with T := 797 }).exact = false ∧
    (verdict { r208 with T := 798 }).bridge = true ∧
    (verdict { r208 with T := 797 }).bridge = false := by decide +kernel
theorem v209 :
    verdict r209 = ⟨true, true, 1, 1217, 10495, 2561, true, true, true⟩ ∧
    (verdict { r209 with T := 1801 }).exact = true ∧
    (verdict { r209 with T := 1800 }).exact = false ∧
    (verdict { r209 with T := 1801 }).bridge = true ∧
    (verdict { r209 with T := 1800 }).bridge = false := by decide +kernel
theorem v210 :
    verdict r210 = ⟨true, true, 1, 772, 6343, 2866, true, true, true⟩ ∧
    (verdict { r210 with T := 648 }).exact = true ∧
    (verdict { r210 with T := 647 }).exact = false ∧
    (verdict { r210 with T := 772 }).bridge = true ∧
    (verdict { r210 with T := 771 }).bridge = false := by decide +kernel
theorem v211 :
    verdict r211 = ⟨true, true, 1, 893, 4881, 2204, true, true, true⟩ ∧
    (verdict { r211 with T := 783 }).exact = true ∧
    (verdict { r211 with T := 782 }).exact = false ∧
    (verdict { r211 with T := 893 }).bridge = true ∧
    (verdict { r211 with T := 892 }).bridge = false := by decide +kernel
theorem v212 :
    verdict r212 = ⟨true, true, 1, 544, 3684, 1464, true, true, true⟩ ∧
    (verdict { r212 with T := 588 }).exact = true ∧
    (verdict { r212 with T := 587 }).exact = false ∧
    (verdict { r212 with T := 633 }).bridge = true ∧
    (verdict { r212 with T := 632 }).bridge = false := by decide +kernel
theorem v213 :
    verdict r213 = ⟨true, true, 1, 1117, 8280, 3331, true, true, true⟩ ∧
    (verdict { r213 with T := 1366 }).exact = true ∧
    (verdict { r213 with T := 1365 }).exact = false ∧
    (verdict { r213 with T := 1366 }).bridge = true ∧
    (verdict { r213 with T := 1365 }).bridge = false := by decide +kernel
theorem v214 :
    verdict r214 = ⟨true, true, 1, 628, 2834, 1125, true, true, true⟩ ∧
    (verdict { r214 with T := 860 }).exact = true ∧
    (verdict { r214 with T := 859 }).exact = false ∧
    (verdict { r214 with T := 860 }).bridge = true ∧
    (verdict { r214 with T := 859 }).bridge = false := by decide +kernel
theorem v215 :
    verdict r215 = ⟨true, true, 1, 1291, 6389, 2570, true, true, true⟩ ∧
    (verdict { r215 with T := 1938 }).exact = true ∧
    (verdict { r215 with T := 1937 }).exact = false ∧
    (verdict { r215 with T := 1938 }).bridge = true ∧
    (verdict { r215 with T := 1937 }).bridge = false := by decide +kernel
theorem v216 :
    verdict r216 = ⟨true, true, 1, 1369, 10335, 3463, true, true, true⟩ ∧
    (verdict { r216 with T := 1458 }).exact = true ∧
    (verdict { r216 with T := 1457 }).exact = false ∧
    (verdict { r216 with T := 1581 }).bridge = true ∧
    (verdict { r216 with T := 1580 }).bridge = false := by decide +kernel
theorem v217 :
    verdict r217 = ⟨true, true, 1, 1582, 7961, 2665, true, true, true⟩ ∧
    (verdict { r217 with T := 1684 }).exact = true ∧
    (verdict { r217 with T := 1683 }).exact = false ∧
    (verdict { r217 with T := 1827 }).bridge = true ∧
    (verdict { r217 with T := 1826 }).bridge = false := by decide +kernel
theorem v218 :
    verdict r218 = ⟨true, true, 1, 852, 5421, 1774, true, true, true⟩ ∧
    (verdict { r218 with T := 799 }).exact = true ∧
    (verdict { r218 with T := 798 }).exact = false ∧
    (verdict { r218 with T := 940 }).bridge = true ∧
    (verdict { r218 with T := 939 }).bridge = false := by decide +kernel
theorem v219 :
    verdict r219 = ⟨true, true, 1, 1801, 11801, 4005, true, true, true⟩ ∧
    (verdict { r219 with T := 1786 }).exact = true ∧
    (verdict { r219 with T := 1785 }).exact = false ∧
    (verdict { r219 with T := 2016 }).bridge = true ∧
    (verdict { r219 with T := 2015 }).bridge = false := by decide +kernel
theorem v220 :
    verdict r220 = ⟨true, true, 1, 984, 4176, 1364, true, true, true⟩ ∧
    (verdict { r220 with T := 1052 }).exact = true ∧
    (verdict { r220 with T := 1051 }).exact = false ∧
    (verdict { r220 with T := 1086 }).bridge = true ∧
    (verdict { r220 with T := 1085 }).bridge = false := by decide +kernel
theorem v221 :
    verdict r221 = ⟨true, true, 1, 2081, 9108, 3089, true, true, true⟩ ∧
    (verdict { r221 with T := 2391 }).exact = true ∧
    (verdict { r221 with T := 2390 }).exact = false ∧
    (verdict { r221 with T := 2391 }).bridge = true ∧
    (verdict { r221 with T := 2390 }).bridge = false := by decide +kernel
theorem v222 :
    verdict r222 = ⟨true, true, 1, 1694, 10674, 3788, true, true, true⟩ ∧
    (verdict { r222 with T := 1570 }).exact = true ∧
    (verdict { r222 with T := 1569 }).exact = false ∧
    (verdict { r222 with T := 1694 }).bridge = true ∧
    (verdict { r222 with T := 1693 }).bridge = false := by decide +kernel
theorem v223 :
    verdict r223 = ⟨true, true, 1, 1958, 8223, 2916, true, true, true⟩ ∧
    (verdict { r223 with T := 1814 }).exact = true ∧
    (verdict { r223 with T := 1813 }).exact = false ∧
    (verdict { r223 with T := 1958 }).bridge = true ∧
    (verdict { r223 with T := 1957 }).bridge = false := by decide +kernel
theorem v224 :
    verdict r224 = ⟨true, true, 1, 1474, 6436, 2325, true, true, true⟩ ∧
    (verdict { r224 with T := 1423 }).exact = true ∧
    (verdict { r224 with T := 1422 }).exact = false ∧
    (verdict { r224 with T := 1563 }).bridge = true ∧
    (verdict { r224 with T := 1562 }).bridge = false := by decide +kernel
theorem v225 :
    verdict r225 = ⟨true, true, 1, 2534, 12620, 4595, true, true, true⟩ ∧
    (verdict { r225 with T := 2562 }).exact = true ∧
    (verdict { r225 with T := 2561 }).exact = false ∧
    (verdict { r225 with T := 2724 }).bridge = true ∧
    (verdict { r225 with T := 2723 }).bridge = false := by decide +kernel
theorem v226 :
    verdict r226 = ⟨true, true, 1, 1703, 4960, 1790, true, true, true⟩ ∧
    (verdict { r226 with T := 1734 }).exact = true ∧
    (verdict { r226 with T := 1733 }).exact = false ∧
    (verdict { r226 with T := 1806 }).bridge = true ∧
    (verdict { r226 with T := 1805 }).bridge = false := by decide +kernel
theorem v227 :
    verdict r227 = ⟨true, true, 1, 2928, 9741, 3546, true, true, true⟩ ∧
    (verdict { r227 with T := 3004 }).exact = true ∧
    (verdict { r227 with T := 3003 }).exact = false ∧
    (verdict { r227 with T := 3147 }).bridge = true ∧
    (verdict { r227 with T := 3146 }).bridge = false := by decide +kernel
theorem v228 :
    verdict r228 = ⟨true, true, 1, 1182, 8373, 3276, true, true, true⟩ ∧
    (verdict { r228 with T := 1058 }).exact = true ∧
    (verdict { r228 with T := 1057 }).exact = false ∧
    (verdict { r228 with T := 1182 }).bridge = true ∧
    (verdict { r228 with T := 1181 }).bridge = false := by decide +kernel
theorem v229 :
    verdict r229 = ⟨true, true, 1, 1366, 6447, 2521, true, true, true⟩ ∧
    (verdict { r229 with T := 1222 }).exact = true ∧
    (verdict { r229 with T := 1221 }).exact = false ∧
    (verdict { r229 with T := 1366 }).bridge = true ∧
    (verdict { r229 with T := 1365 }).bridge = false := by decide +kernel
theorem v230 :
    verdict r230 = ⟨true, true, 1, 750, 4474, 1800, true, true, true⟩ ∧
    (verdict { r230 with T := 728 }).exact = true ∧
    (verdict { r230 with T := 727 }).exact = false ∧
    (verdict { r230 with T := 777 }).bridge = true ∧
    (verdict { r230 with T := 776 }).bridge = false := by decide +kernel
theorem v231 :
    verdict r231 = ⟨true, true, 1, 1617, 9815, 4048, true, true, true⟩ ∧
    (verdict { r231 with T := 1528 }).exact = true ∧
    (verdict { r231 with T := 1527 }).exact = false ∧
    (verdict { r231 with T := 1641 }).bridge = true ∧
    (verdict { r231 with T := 1640 }).bridge = false := by decide +kernel
theorem v232 :
    verdict r232 = ⟨true, true, 1, 866, 3445, 1384, true, true, true⟩ ∧
    (verdict { r232 with T := 913 }).exact = true ∧
    (verdict { r232 with T := 912 }).exact = false ∧
    (verdict { r232 with T := 913 }).bridge = true ∧
    (verdict { r232 with T := 912 }).bridge = false := by decide +kernel
theorem v233 :
    verdict r233 = ⟨true, true, 1, 1868, 7572, 3122, true, true, true⟩ ∧
    (verdict { r233 with T := 2108 }).exact = true ∧
    (verdict { r233 with T := 2107 }).exact = false ∧
    (verdict { r233 with T := 2108 }).bridge = true ∧
    (verdict { r233 with T := 2107 }).bridge = false := by decide +kernel
theorem v234 :
    verdict r234 = ⟨true, true, 1, 777, 6999, 2658, true, true, true⟩ ∧
    (verdict { r234 with T := 440 }).exact = true ∧
    (verdict { r234 with T := 439 }).exact = false ∧
    (verdict { r234 with T := 777 }).bridge = true ∧
    (verdict { r234 with T := 776 }).bridge = false := by decide +kernel
theorem v235 :
    verdict r235 = ⟨true, true, 1, 899, 5385, 2043, true, true, true⟩ ∧
    (verdict { r235 with T := 704 }).exact = true ∧
    (verdict { r235 with T := 703 }).exact = false ∧
    (verdict { r235 with T := 899 }).bridge = true ∧
    (verdict { r235 with T := 898 }).bridge = false := by decide +kernel
theorem v236 :
    verdict r236 = ⟨true, true, 1, 531, 3829, 1336, true, true, true⟩ ∧
    (verdict { r236 with T := 596 }).exact = true ∧
    (verdict { r236 with T := 595 }).exact = false ∧
    (verdict { r236 with T := 596 }).bridge = true ∧
    (verdict { r236 with T := 595 }).bridge = false := by decide +kernel
theorem v237 :
    verdict r237 = ⟨true, true, 1, 1173, 8626, 3097, true, true, true⟩ ∧
    (verdict { r237 with T := 1381 }).exact = true ∧
    (verdict { r237 with T := 1380 }).exact = false ∧
    (verdict { r237 with T := 1381 }).bridge = true ∧
    (verdict { r237 with T := 1380 }).bridge = false := by decide +kernel
theorem v238 :
    verdict r238 = ⟨true, true, 1, 613, 2946, 1026, true, true, true⟩ ∧
    (verdict { r238 with T := 812 }).exact = true ∧
    (verdict { r238 with T := 811 }).exact = false ∧
    (verdict { r238 with T := 812 }).bridge = true ∧
    (verdict { r238 with T := 811 }).bridge = false := by decide +kernel
theorem v239 :
    verdict r239 = ⟨true, true, 1, 1356, 6656, 2389, true, true, true⟩ ∧
    (verdict { r239 with T := 1847 }).exact = true ∧
    (verdict { r239 with T := 1846 }).exact = false ∧
    (verdict { r239 with T := 1847 }).bridge = true ∧
    (verdict { r239 with T := 1846 }).bridge = false := by decide +kernel
theorem v240 :
    verdict r240 = ⟨true, true, 1, 1384, 7878, 3478, true, true, true⟩ ∧
    (verdict { r240 with T := 1260 }).exact = true ∧
    (verdict { r240 with T := 1259 }).exact = false ∧
    (verdict { r240 with T := 1384 }).bridge = true ∧
    (verdict { r240 with T := 1383 }).bridge = false := by decide +kernel
theorem v241 :
    verdict r241 = ⟨true, true, 1, 1600, 6067, 2676, true, true, true⟩ ∧
    (verdict { r241 with T := 1456 }).exact = true ∧
    (verdict { r241 with T := 1455 }).exact = false ∧
    (verdict { r241 with T := 1600 }).bridge = true ∧
    (verdict { r241 with T := 1599 }).bridge = false := by decide +kernel
theorem v242 :
    verdict r242 = ⟨true, true, 1, 959, 4136, 1783, true, true, true⟩ ∧
    (verdict { r242 with T := 904 }).exact = true ∧
    (verdict { r242 with T := 903 }).exact = false ∧
    (verdict { r242 with T := 962 }).bridge = true ∧
    (verdict { r242 with T := 961 }).bridge = false := by decide +kernel
theorem v243 :
    verdict r243 = ⟨true, true, 1, 1933, 8975, 3895, true, true, true⟩ ∧
    (verdict { r243 with T := 1423 }).exact = true ∧
    (verdict { r243 with T := 1422 }).exact = false ∧
    (verdict { r243 with T := 1937 }).bridge = true ∧
    (verdict { r243 with T := 1936 }).bridge = false := by decide +kernel
theorem v244 :
    verdict r244 = ⟨true, true, 1, 1108, 3183, 1371, true, true, true⟩ ∧
    (verdict { r244 with T := 1044 }).exact = true ∧
    (verdict { r244 with T := 1043 }).exact = false ∧
    (verdict { r244 with T := 1111 }).bridge = true ∧
    (verdict { r244 with T := 1110 }).bridge = false := by decide +kernel
theorem v245 :
    verdict r245 = ⟨true, true, 1, 2233, 6924, 3004, true, true, true⟩ ∧
    (verdict { r245 with T := 2242 }).exact = true ∧
    (verdict { r245 with T := 2241 }).exact = false ∧
    (verdict { r245 with T := 2242 }).bridge = true ∧
    (verdict { r245 with T := 2241 }).bridge = false := by decide +kernel
theorem v246 :
    verdict r246 = ⟨true, true, 1, 1172, 7139, 3266, true, true, true⟩ ∧
    (verdict { r246 with T := 1048 }).exact = true ∧
    (verdict { r246 with T := 1047 }).exact = false ∧
    (verdict { r246 with T := 1172 }).bridge = true ∧
    (verdict { r246 with T := 1171 }).bridge = false := by decide +kernel
theorem v247 :
    verdict r247 = ⟨true, true, 1, 1355, 5497, 2513, true, true, true⟩ ∧
    (verdict { r247 with T := 1211 }).exact = true ∧
    (verdict { r247 with T := 1210 }).exact = false ∧
    (verdict { r247 with T := 1355 }).bridge = true ∧
    (verdict { r247 with T := 1354 }).bridge = false := by decide +kernel
theorem v248 :
    verdict r248 = ⟨true, true, 1, 783, 3701, 1671, true, true, true⟩ ∧
    (verdict { r248 with T := 817 }).exact = true ∧
    (verdict { r248 with T := 816 }).exact = false ∧
    (verdict { r248 with T := 872 }).bridge = true ∧
    (verdict { r248 with T := 871 }).bridge = false := by decide +kernel
theorem v249 :
    verdict r249 = ⟨true, true, 1, 1544, 8091, 3693, true, true, true⟩ ∧
    (verdict { r249 with T := 1611 }).exact = true ∧
    (verdict { r249 with T := 1610 }).exact = false ∧
    (verdict { r249 with T := 1734 }).bridge = true ∧
    (verdict { r249 with T := 1733 }).bridge = false := by decide +kernel
theorem v250 :
    verdict r250 = ⟨true, true, 1, 904, 2847, 1285, true, true, true⟩ ∧
    (verdict { r250 with T := 976 }).exact = true ∧
    (verdict { r250 with T := 975 }).exact = false ∧
    (verdict { r250 with T := 1007 }).bridge = true ∧
    (verdict { r250 with T := 1006 }).bridge = false := by decide +kernel
theorem v251 :
    verdict r251 = ⟨true, true, 1, 1783, 6241, 2849, true, true, true⟩ ∧
    (verdict { r251 with T := 2152 }).exact = true ∧
    (verdict { r251 with T := 2151 }).exact = false ∧
    (verdict { r251 with T := 2152 }).bridge = true ∧
    (verdict { r251 with T := 2151 }).bridge = false := by decide +kernel
theorem v252 :
    verdict r252 = ⟨true, true, 1, 1139, 12940, 3020, true, true, true⟩ ∧
    (verdict { r252 with T := 802 }).exact = true ∧
    (verdict { r252 with T := 801 }).exact = false ∧
    (verdict { r252 with T := 1139 }).bridge = true ∧
    (verdict { r252 with T := 1138 }).bridge = false := by decide +kernel
theorem v253 :
    verdict r253 = ⟨true, true, 1, 1317, 9956, 2323, true, true, true⟩ ∧
    (verdict { r253 with T := 927 }).exact = true ∧
    (verdict { r253 with T := 926 }).exact = false ∧
    (verdict { r253 with T := 1317 }).bridge = true ∧
    (verdict { r253 with T := 1316 }).bridge = false := by decide +kernel
theorem v254 :
    verdict r254 = ⟨true, true, 1, 710, 7345, 1768, true, true, true⟩ ∧
    (verdict { r254 with T := 737 }).exact = true ∧
    (verdict { r254 with T := 736 }).exact = false ∧
    (verdict { r254 with T := 792 }).bridge = true ∧
    (verdict { r254 with T := 791 }).bridge = false := by decide +kernel
theorem v255 :
    verdict r255 = ⟨true, true, 1, 1463, 16276, 3960, true, true, true⟩ ∧
    (verdict { r255 with T := 1682 }).exact = true ∧
    (verdict { r255 with T := 1681 }).exact = false ∧
    (verdict { r255 with T := 1682 }).bridge = true ∧
    (verdict { r255 with T := 1681 }).bridge = false := by decide +kernel
theorem v256 :
    verdict r256 = ⟨true, true, 1, 820, 5649, 1359, true, true, true⟩ ∧
    (verdict { r256 with T := 1002 }).exact = true ∧
    (verdict { r256 with T := 1001 }).exact = false ∧
    (verdict { r256 with T := 1002 }).bridge = true ∧
    (verdict { r256 with T := 1001 }).bridge = false := by decide +kernel
theorem v257 :
    verdict r257 = ⟨true, true, 1, 1690, 12558, 3056, true, true, true⟩ ∧
    (verdict { r257 with T := 2323 }).exact = true ∧
    (verdict { r257 with T := 2322 }).exact = false ∧
    (verdict { r257 with T := 2323 }).bridge = true ∧
    (verdict { r257 with T := 2322 }).bridge = false := by decide +kernel
theorem v258 :
    verdict r258 = ⟨true, true, 1, 552, 5868, 2646, true, true, true⟩ ∧
    (verdict { r258 with T := 428 }).exact = true ∧
    (verdict { r258 with T := 427 }).exact = false ∧
    (verdict { r258 with T := 552 }).bridge = true ∧
    (verdict { r258 with T := 551 }).bridge = false := by decide +kernel
theorem v259 :
    verdict r259 = ⟨true, true, 1, 639, 4513, 2034, true, true, true⟩ ∧
    (verdict { r259 with T := 699 }).exact = true ∧
    (verdict { r259 with T := 698 }).exact = false ∧
    (verdict { r259 with T := 699 }).bridge = true ∧
    (verdict { r259 with T := 698 }).bridge = false := by decide +kernel
theorem v260 :
    verdict r260 = ⟨true, true, 1, 530, 3392, 1644, true, true, true⟩ ∧
    (verdict { r260 with T := 501 }).exact = true ∧
    (verdict { r260 with T := 500 }).exact = false ∧
    (verdict { r260 with T := 536 }).bridge = true ∧
    (verdict { r260 with T := 535 }).bridge = false := by decide +kernel
theorem v261 :
    verdict r261 = ⟨true, true, 1, 1074, 7461, 3691, true, true, true⟩ ∧
    (verdict { r261 with T := 1212 }).exact = true ∧
    (verdict { r261 with T := 1211 }).exact = false ∧
    (verdict { r261 with T := 1212 }).bridge = true ∧
    (verdict { r261 with T := 1211 }).bridge = false := by decide +kernel
theorem v262 :
    verdict r262 = ⟨true, true, 1, 612, 2608, 1264, true, true, true⟩ ∧
    (verdict { r262 with T := 755 }).exact = true ∧
    (verdict { r262 with T := 754 }).exact = false ∧
    (verdict { r262 with T := 755 }).bridge = true ∧
    (verdict { r262 with T := 754 }).bridge = false := by decide +kernel
theorem v263 :
    verdict r263 = ⟨true, true, 1, 1241, 5757, 2848, true, true, true⟩ ∧
    (verdict { r263 with T := 1744 }).exact = true ∧
    (verdict { r263 with T := 1743 }).exact = false ∧
    (verdict { r263 with T := 1744 }).bridge = true ∧
    (verdict { r263 with T := 1743 }).bridge = false := by decide +kernel
theorem v264 :
    verdict r264 = ⟨true, true, 1, 1499, 14610, 3806, true, true, true⟩ ∧
    (verdict { r264 with T := 1375 }).exact = true ∧
    (verdict { r264 with T := 1374 }).exact = false ∧
    (verdict { r264 with T := 1499 }).bridge = true ∧
    (verdict { r264 with T := 1498 }).bridge = false := by decide +kernel
theorem v265 :
    verdict r265 = ⟨true, true, 1, 1732, 11245, 2930, true, true, true⟩ ∧
    (verdict { r265 with T := 1588 }).exact = true ∧
    (verdict { r265 with T := 1587 }).exact = false ∧
    (verdict { r265 with T := 1732 }).bridge = true ∧
    (verdict { r265 with T := 1731 }).bridge = false := by decide +kernel
theorem v266 :
    verdict r266 = ⟨true, true, 1, 1160, 7973, 2044, true, true, true⟩ ∧
    (verdict { r266 with T := 1010 }).exact = true ∧
    (verdict { r266 with T := 1009 }).exact = false ∧
    (verdict { r266 with T := 1160 }).bridge = true ∧
    (verdict { r266 with T := 1159 }).bridge = false := by decide +kernel
theorem v267 :
    verdict r267 = ⟨true, true, 1, 2188, 17538, 4316, true, true, true⟩ ∧
    (verdict { r267 with T := 1853 }).exact = true ∧
    (verdict { r267 with T := 1852 }).exact = false ∧
    (verdict { r267 with T := 2188 }).bridge = true ∧
    (verdict { r267 with T := 2187 }).bridge = false := by decide +kernel
theorem v268 :
    verdict r268 = ⟨true, true, 1, 1340, 6135, 1572, true, true, true⟩ ∧
    (verdict { r268 with T := 1167 }).exact = true ∧
    (verdict { r268 with T := 1166 }).exact = false ∧
    (verdict { r268 with T := 1340 }).bridge = true ∧
    (verdict { r268 with T := 1339 }).bridge = false := by decide +kernel
theorem v269 :
    verdict r269 = ⟨true, true, 1, 2528, 13531, 3331, true, true, true⟩ ∧
    (verdict { r269 with T := 2175 }).exact = true ∧
    (verdict { r269 with T := 2174 }).exact = false ∧
    (verdict { r269 with T := 2528 }).bridge = true ∧
    (verdict { r269 with T := 2527 }).bridge = false := by decide +kernel
theorem v270 :
    verdict r270 = ⟨true, true, 1, 561, 6502, 2655, true, true, true⟩ ∧
    (verdict { r270 with T := 437 }).exact = true ∧
    (verdict { r270 with T := 436 }).exact = false ∧
    (verdict { r270 with T := 561 }).bridge = true ∧
    (verdict { r270 with T := 560 }).bridge = false := by decide +kernel
theorem v271 :
    verdict r271 = ⟨true, true, 1, 649, 5003, 2041, true, true, true⟩ ∧
    (verdict { r271 with T := 702 }).exact = true ∧
    (verdict { r271 with T := 701 }).exact = false ∧
    (verdict { r271 with T := 702 }).bridge = true ∧
    (verdict { r271 with T := 701 }).bridge = false := by decide +kernel
theorem v272 :
    verdict r272 = ⟨true, true, 1, 517, 3472, 1399, true, true, true⟩ ∧
    (verdict { r272 with T := 565 }).exact = true ∧
    (verdict { r272 with T := 564 }).exact = false ∧
    (verdict { r272 with T := 565 }).bridge = true ∧
    (verdict { r272 with T := 564 }).bridge = false := by decide +kernel
theorem v273 :
    verdict r273 = ⟨true, true, 1, 1054, 7534, 3149, true, true, true⟩ ∧
    (verdict { r273 with T := 1313 }).exact = true ∧
    (verdict { r273 with T := 1312 }).exact = false ∧
    (verdict { r273 with T := 1313 }).bridge = true ∧
    (verdict { r273 with T := 1312 }).bridge = false := by decide +kernel
theorem v274 :
    verdict r274 = ⟨true, true, 1, 597, 2670, 1074, true, true, true⟩ ∧
    (verdict { r274 with T := 799 }).exact = true ∧
    (verdict { r274 with T := 798 }).exact = false ∧
    (verdict { r274 with T := 799 }).bridge = true ∧
    (verdict { r274 with T := 798 }).bridge = false := by decide +kernel
theorem v275 :
    verdict r275 = ⟨true, true, 1, 1218, 5813, 2428, true, true, true⟩ ∧
    (verdict { r275 with T := 1802 }).exact = true ∧
    (verdict { r275 with T := 1801 }).exact = false ∧
    (verdict { r275 with T := 1802 }).bridge = true ∧
    (verdict { r275 with T := 1801 }).bridge = false := by decide +kernel
theorem v276 :
    verdict r276 = ⟨true, true, 1, 702, 7742, 2796, true, true, true⟩ ∧
    (verdict { r276 with T := 579 }).exact = true ∧
    (verdict { r276 with T := 578 }).exact = false ∧
    (verdict { r276 with T := 702 }).bridge = true ∧
    (verdict { r276 with T := 701 }).bridge = false := by decide +kernel
theorem v277 :
    verdict r277 = ⟨true, true, 1, 812, 5960, 2150, true, true, true⟩ ∧
    (verdict { r277 with T := 757 }).exact = true ∧
    (verdict { r277 with T := 756 }).exact = false ∧
    (verdict { r277 with T := 812 }).bridge = true ∧
    (verdict { r277 with T := 811 }).bridge = false := by decide +kernel
theorem v278 :
    verdict r278 = ⟨true, true, 1, 403, 4081, 1416, true, true, true⟩ ∧
    (verdict { r278 with T := 583 }).exact = true ∧
    (verdict { r278 with T := 582 }).exact = false ∧
    (verdict { r278 with T := 583 }).bridge = true ∧
    (verdict { r278 with T := 582 }).bridge = false := by decide +kernel
theorem v279 :
    verdict r279 = ⟨true, true, 1, 887, 9042, 3292, true, true, true⟩ ∧
    (verdict { r279 with T := 1367 }).exact = true ∧
    (verdict { r279 with T := 1366 }).exact = false ∧
    (verdict { r279 with T := 1367 }).bridge = true ∧
    (verdict { r279 with T := 1366 }).bridge = false := by decide +kernel
theorem v280 :
    verdict r280 = ⟨true, true, 1, 466, 3140, 1088, true, true, true⟩ ∧
    (verdict { r280 with T := 806 }).exact = true ∧
    (verdict { r280 with T := 805 }).exact = false ∧
    (verdict { r280 with T := 806 }).bridge = true ∧
    (verdict { r280 with T := 805 }).bridge = false := by decide +kernel
theorem v281 :
    verdict r281 = ⟨true, true, 1, 1025, 6977, 2539, true, true, true⟩ ∧
    (verdict { r281 with T := 1863 }).exact = true ∧
    (verdict { r281 with T := 1862 }).exact = false ∧
    (verdict { r281 with T := 1863 }).bridge = true ∧
    (verdict { r281 with T := 1862 }).bridge = false := by decide +kernel
theorem v282 :
    verdict r282 = ⟨true, true, 1, 2196, 11736, 4431, true, true, true⟩ ∧
    (verdict { r282 with T := 2072 }).exact = true ∧
    (verdict { r282 with T := 2071 }).exact = false ∧
    (verdict { r282 with T := 2196 }).bridge = true ∧
    (verdict { r282 with T := 2195 }).bridge = false := by decide +kernel
theorem v283 :
    verdict r283 = ⟨true, true, 1, 2538, 9043, 3412, true, true, true⟩ ∧
    (verdict { r283 with T := 2394 }).exact = true ∧
    (verdict { r283 with T := 2393 }).exact = false ∧
    (verdict { r283 with T := 2538 }).bridge = true ∧
    (verdict { r283 with T := 2537 }).bridge = false := by decide +kernel
theorem v284 :
    verdict r284 = ⟨true, true, 1, 2073, 7365, 2771, true, true, true⟩ ∧
    (verdict { r284 with T := 1918 }).exact = true ∧
    (verdict { r284 with T := 1917 }).exact = false ∧
    (verdict { r284 with T := 2073 }).bridge = true ∧
    (verdict { r284 with T := 2072 }).bridge = false := by decide +kernel
theorem v285 :
    verdict r285 = ⟨true, true, 1, 3480, 13937, 5168, true, true, true⟩ ∧
    (verdict { r285 with T := 3153 }).exact = true ∧
    (verdict { r285 with T := 3152 }).exact = false ∧
    (verdict { r285 with T := 3480 }).bridge = true ∧
    (verdict { r285 with T := 3479 }).bridge = false := by decide +kernel
theorem v286 :
    verdict r286 = ⟨true, true, 1, 2395, 5675, 2134, true, true, true⟩ ∧
    (verdict { r286 with T := 2215 }).exact = true ∧
    (verdict { r286 with T := 2214 }).exact = false ∧
    (verdict { r286 with T := 2395 }).bridge = true ∧
    (verdict { r286 with T := 2394 }).bridge = false := by decide +kernel
theorem v287 :
    verdict r287 = ⟨true, true, 1, 4020, 10756, 3987, true, true, true⟩ ∧
    (verdict { r287 with T := 3642 }).exact = true ∧
    (verdict { r287 with T := 3641 }).exact = false ∧
    (verdict { r287 with T := 4020 }).bridge = true ∧
    (verdict { r287 with T := 4019 }).bridge = false := by decide +kernel
theorem v288 :
    verdict r288 = ⟨true, true, 1, 562, 7463, 2656, true, true, true⟩ ∧
    (verdict { r288 with T := 438 }).exact = true ∧
    (verdict { r288 with T := 437 }).exact = false ∧
    (verdict { r288 with T := 562 }).bridge = true ∧
    (verdict { r288 with T := 561 }).bridge = false := by decide +kernel
theorem v289 :
    verdict r289 = ⟨true, true, 1, 650, 5744, 2042, true, true, true⟩ ∧
    (verdict { r289 with T := 702 }).exact = true ∧
    (verdict { r289 with T := 701 }).exact = false ∧
    (verdict { r289 with T := 702 }).bridge = true ∧
    (verdict { r289 with T := 701 }).bridge = false := by decide +kernel
theorem v290 :
    verdict r290 = ⟨true, true, 1, 403, 4075, 1260, true, true, true⟩ ∧
    (verdict { r290 with T := 575 }).exact = true ∧
    (verdict { r290 with T := 574 }).exact = false ∧
    (verdict { r290 with T := 575 }).bridge = true ∧
    (verdict { r290 with T := 574 }).bridge = false := by decide +kernel
theorem v291 :
    verdict r291 = ⟨true, true, 1, 847, 8940, 2897, true, true, true⟩ ∧
    (verdict { r291 with T := 1332 }).exact = true ∧
    (verdict { r291 with T := 1331 }).exact = false ∧
    (verdict { r291 with T := 1332 }).bridge = true ∧
    (verdict { r291 with T := 1331 }).bridge = false := by decide +kernel
theorem v292 :
    verdict r292 = ⟨true, true, 1, 465, 3136, 968, true, true, true⟩ ∧
    (verdict { r292 with T := 796 }).exact = true ∧
    (verdict { r292 with T := 795 }).exact = false ∧
    (verdict { r292 with T := 796 }).bridge = true ∧
    (verdict { r292 with T := 795 }).bridge = false := by decide +kernel
theorem v293 :
    verdict r293 = ⟨true, true, 1, 979, 6897, 2234, true, true, true⟩ ∧
    (verdict { r293 with T := 1809 }).exact = true ∧
    (verdict { r293 with T := 1808 }).exact = false ∧
    (verdict { r293 with T := 1809 }).bridge = true ∧
    (verdict { r293 with T := 1808 }).bridge = false := by decide +kernel
theorem v294 :
    verdict r294 = ⟨true, true, 1, 706, 6319, 2800, true, true, true⟩ ∧
    (verdict { r294 with T := 582 }).exact = true ∧
    (verdict { r294 with T := 581 }).exact = false ∧
    (verdict { r294 with T := 706 }).bridge = true ∧
    (verdict { r294 with T := 705 }).bridge = false := by decide +kernel
theorem v295 :
    verdict r295 = ⟨true, true, 1, 817, 4862, 2153, true, true, true⟩ ∧
    (verdict { r295 with T := 758 }).exact = true ∧
    (verdict { r295 with T := 757 }).exact = false ∧
    (verdict { r295 with T := 817 }).bridge = true ∧
    (verdict { r295 with T := 816 }).bridge = false := by decide +kernel
theorem v296 :
    verdict r296 = ⟨true, true, 1, 456, 3467, 1381, true, true, true⟩ ∧
    (verdict { r296 with T := 583 }).exact = true ∧
    (verdict { r296 with T := 582 }).exact = false ∧
    (verdict { r296 with T := 583 }).bridge = true ∧
    (verdict { r296 with T := 582 }).bridge = false := by decide +kernel
theorem v297 :
    verdict r297 = ⟨true, true, 1, 993, 8005, 3218, true, true, true⟩ ∧
    (verdict { r297 with T := 1355 }).exact = true ∧
    (verdict { r297 with T := 1354 }).exact = false ∧
    (verdict { r297 with T := 1355 }).bridge = true ∧
    (verdict { r297 with T := 1354 }).bridge = false := by decide +kernel
theorem v298 :
    verdict r298 = ⟨true, true, 1, 527, 2667, 1061, true, true, true⟩ ∧
    (verdict { r298 with T := 823 }).exact = true ∧
    (verdict { r298 with T := 822 }).exact = false ∧
    (verdict { r298 with T := 823 }).bridge = true ∧
    (verdict { r298 with T := 822 }).bridge = false := by decide +kernel
theorem v299 :
    verdict r299 = ⟨true, true, 1, 1147, 6177, 2482, true, true, true⟩ ∧
    (verdict { r299 with T := 1883 }).exact = true ∧
    (verdict { r299 with T := 1882 }).exact = false ∧
    (verdict { r299 with T := 1883 }).bridge = true ∧
    (verdict { r299 with T := 1882 }).bridge = false := by decide +kernel

end Formal.Timing.ChainSettleExe.GcdD
