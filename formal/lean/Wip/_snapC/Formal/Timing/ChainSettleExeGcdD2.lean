import Formal.Timing.ChainSettleExeGcdDData2

/-! C-10o2 GENERATED: kernel-decided verdicts of chunk 2 (see ChainSettleExe.verdict).
Per row: `verdict` at chainck's late side `T`; exact PASS at `T*` and FAIL at `T* - 1`
(margin_exact = T - T*); bridge PASS at `Tb*` and FAIL at `Tb* - 1`. -/

namespace Formal.Timing.ChainSettleExe.GcdD
open Formal.Timing Formal.Timing.ChainSettleExe

theorem v300 :
    verdict r300 = ⟨true, true, 1, 905, 7915, 2999, true, true, true⟩ ∧
    (verdict { r300 with T := 781 }).exact = true ∧
    (verdict { r300 with T := 780 }).exact = false ∧
    (verdict { r300 with T := 905 }).bridge = true ∧
    (verdict { r300 with T := 904 }).bridge = false := by decide +kernel
theorem v301 :
    verdict r301 = ⟨true, true, 1, 1046, 6096, 2307, true, true, true⟩ ∧
    (verdict { r301 with T := 902 }).exact = true ∧
    (verdict { r301 with T := 901 }).exact = false ∧
    (verdict { r301 with T := 1046 }).bridge = true ∧
    (verdict { r301 with T := 1045 }).bridge = false := by decide +kernel
theorem v302 :
    verdict r302 = ⟨true, true, 1, 632, 4320, 1540, true, true, true⟩ ∧
    (verdict { r302 with T := 666 }).exact = true ∧
    (verdict { r302 with T := 665 }).exact = false ∧
    (verdict { r302 with T := 721 }).bridge = true ∧
    (verdict { r302 with T := 720 }).bridge = false := by decide +kernel
theorem v303 :
    verdict r303 = ⟨true, true, 1, 1255, 9107, 3448, true, true, true⟩ ∧
    (verdict { r303 with T := 1387 }).exact = true ∧
    (verdict { r303 with T := 1386 }).exact = false ∧
    (verdict { r303 with T := 1445 }).bridge = true ∧
    (verdict { r303 with T := 1444 }).bridge = false := by decide +kernel
theorem v304 :
    verdict r304 = ⟨true, true, 1, 730, 3326, 1184, true, true, true⟩ ∧
    (verdict { r304 with T := 903 }).exact = true ∧
    (verdict { r304 with T := 902 }).exact = false ∧
    (verdict { r304 with T := 903 }).bridge = true ∧
    (verdict { r304 with T := 902 }).bridge = false := by decide +kernel
theorem v305 :
    verdict r305 = ⟨true, true, 1, 1450, 7027, 2660, true, true, true⟩ ∧
    (verdict { r305 with T := 2008 }).exact = true ∧
    (verdict { r305 with T := 2007 }).exact = false ∧
    (verdict { r305 with T := 2008 }).bridge = true ∧
    (verdict { r305 with T := 2007 }).bridge = false := by decide +kernel
theorem v306 :
    verdict r306 = ⟨true, true, 1, 2132, 10303, 4226, true, true, true⟩ ∧
    (verdict { r306 with T := 2008 }).exact = true ∧
    (verdict { r306 with T := 2007 }).exact = false ∧
    (verdict { r306 with T := 2132 }).bridge = true ∧
    (verdict { r306 with T := 2131 }).bridge = false := by decide +kernel
theorem v307 :
    verdict r307 = ⟨true, true, 1, 2464, 7938, 3254, true, true, true⟩ ∧
    (verdict { r307 with T := 2320 }).exact = true ∧
    (verdict { r307 with T := 2319 }).exact = false ∧
    (verdict { r307 with T := 2464 }).bridge = true ∧
    (verdict { r307 with T := 2463 }).bridge = false := by decide +kernel
theorem v308 :
    verdict r308 = ⟨true, true, 1, 1266, 5538, 2008, true, true, true⟩ ∧
    (verdict { r308 with T := 1122 }).exact = true ∧
    (verdict { r308 with T := 1121 }).exact = false ∧
    (verdict { r308 with T := 1355 }).bridge = true ∧
    (verdict { r308 with T := 1354 }).bridge = false := by decide +kernel
theorem v309 :
    verdict r309 = ⟨true, true, 1, 2517, 11317, 4313, true, true, true⟩ ∧
    (verdict { r309 with T := 2170 }).exact = true ∧
    (verdict { r309 with T := 2169 }).exact = false ∧
    (verdict { r309 with T := 2707 }).bridge = true ∧
    (verdict { r309 with T := 2706 }).bridge = false := by decide +kernel
theorem v310 :
    verdict r310 = ⟨true, true, 1, 1462, 4265, 1545, true, true, true⟩ ∧
    (verdict { r310 with T := 1493 }).exact = true ∧
    (verdict { r310 with T := 1492 }).exact = false ∧
    (verdict { r310 with T := 1565 }).bridge = true ∧
    (verdict { r310 with T := 1564 }).bridge = false := by decide +kernel
theorem v311 :
    verdict r311 = ⟨true, true, 1, 2908, 8736, 3328, true, true, true⟩ ∧
    (verdict { r311 with T := 2984 }).exact = true ∧
    (verdict { r311 with T := 2983 }).exact = false ∧
    (verdict { r311 with T := 3127 }).bridge = true ∧
    (verdict { r311 with T := 3126 }).bridge = false := by decide +kernel
theorem v312 :
    verdict r312 = ⟨true, true, 1, 552, 10916, 2646, true, true, true⟩ ∧
    (verdict { r312 with T := 428 }).exact = true ∧
    (verdict { r312 with T := 427 }).exact = false ∧
    (verdict { r312 with T := 552 }).bridge = true ∧
    (verdict { r312 with T := 551 }).bridge = false := by decide +kernel
theorem v313 :
    verdict r313 = ⟨true, true, 1, 639, 8407, 2034, true, true, true⟩ ∧
    (verdict { r313 with T := 699 }).exact = true ∧
    (verdict { r313 with T := 698 }).exact = false ∧
    (verdict { r313 with T := 699 }).bridge = true ∧
    (verdict { r313 with T := 698 }).bridge = false := by decide +kernel
theorem v314 :
    verdict r314 = ⟨true, true, 1, 521, 6428, 1591, true, true, true⟩ ∧
    (verdict { r314 with T := 539 }).exact = true ∧
    (verdict { r314 with T := 538 }).exact = false ∧
    (verdict { r314 with T := 539 }).bridge = true ∧
    (verdict { r314 with T := 538 }).bridge = false := by decide +kernel
theorem v315 :
    verdict r315 = ⟨true, true, 1, 1065, 13776, 3573, true, true, true⟩ ∧
    (verdict { r315 with T := 1312 }).exact = true ∧
    (verdict { r315 with T := 1311 }).exact = false ∧
    (verdict { r315 with T := 1312 }).bridge = true ∧
    (verdict { r315 with T := 1311 }).bridge = false := by decide +kernel
theorem v316 :
    verdict r316 = ⟨true, true, 1, 602, 4947, 1223, true, true, true⟩ ∧
    (verdict { r316 with T := 784 }).exact = true ∧
    (verdict { r316 with T := 783 }).exact = false ∧
    (verdict { r316 with T := 784 }).bridge = true ∧
    (verdict { r316 with T := 783 }).bridge = false := by decide +kernel
theorem v317 :
    verdict r317 = ⟨true, true, 1, 1231, 10629, 2756, true, true, true⟩ ∧
    (verdict { r317 with T := 1811 }).exact = true ∧
    (verdict { r317 with T := 1810 }).exact = false ∧
    (verdict { r317 with T := 1811 }).bridge = true ∧
    (verdict { r317 with T := 1810 }).bridge = false := by decide +kernel
theorem v318 :
    verdict r318 = ⟨true, true, 1, 696, 6742, 2790, true, true, true⟩ ∧
    (verdict { r318 with T := 572 }).exact = true ∧
    (verdict { r318 with T := 571 }).exact = false ∧
    (verdict { r318 with T := 696 }).bridge = true ∧
    (verdict { r318 with T := 695 }).bridge = false := by decide +kernel
theorem v319 :
    verdict r319 = ⟨true, true, 1, 805, 5188, 2145, true, true, true⟩ ∧
    (verdict { r319 with T := 754 }).exact = true ∧
    (verdict { r319 with T := 753 }).exact = false ∧
    (verdict { r319 with T := 805 }).bridge = true ∧
    (verdict { r319 with T := 804 }).bridge = false := by decide +kernel
theorem v320 :
    verdict r320 = ⟨true, true, 1, 677, 3869, 1737, true, true, true⟩ ∧
    (verdict { r320 with T := 633 }).exact = true ∧
    (verdict { r320 with T := 632 }).exact = false ∧
    (verdict { r320 with T := 681 }).bridge = true ∧
    (verdict { r320 with T := 680 }).bridge = false := by decide +kernel
theorem v321 :
    verdict r321 = ⟨true, true, 1, 1295, 8377, 3780, true, true, true⟩ ∧
    (verdict { r321 with T := 1281 }).exact = true ∧
    (verdict { r321 with T := 1280 }).exact = false ∧
    (verdict { r321 with T := 1297 }).bridge = true ∧
    (verdict { r321 with T := 1296 }).bridge = false := by decide +kernel
theorem v322 :
    verdict r322 = ⟨true, true, 1, 782, 2975, 1335, true, true, true⟩ ∧
    (verdict { r322 with T := 808 }).exact = true ∧
    (verdict { r322 with T := 807 }).exact = false ∧
    (verdict { r322 with T := 808 }).bridge = true ∧
    (verdict { r322 with T := 807 }).bridge = false := by decide +kernel
theorem v323 :
    verdict r323 = ⟨true, true, 1, 1496, 6462, 2915, true, true, true⟩ ∧
    (verdict { r323 with T := 1823 }).exact = true ∧
    (verdict { r323 with T := 1822 }).exact = false ∧
    (verdict { r323 with T := 1823 }).bridge = true ∧
    (verdict { r323 with T := 1822 }).bridge = false := by decide +kernel
theorem v324 :
    verdict r324 = ⟨true, true, 1, 562, 5464, 2656, true, true, true⟩ ∧
    (verdict { r324 with T := 438 }).exact = true ∧
    (verdict { r324 with T := 437 }).exact = false ∧
    (verdict { r324 with T := 562 }).bridge = true ∧
    (verdict { r324 with T := 561 }).bridge = false := by decide +kernel
theorem v325 :
    verdict r325 = ⟨true, true, 1, 650, 4204, 2042, true, true, true⟩ ∧
    (verdict { r325 with T := 702 }).exact = true ∧
    (verdict { r325 with T := 701 }).exact = false ∧
    (verdict { r325 with T := 702 }).bridge = true ∧
    (verdict { r325 with T := 701 }).bridge = false := by decide +kernel
theorem v326 :
    verdict r326 = ⟨true, true, 1, 550, 3456, 1483, true, true, true⟩ ∧
    (verdict { r326 with T := 584 }).exact = true ∧
    (verdict { r326 with T := 583 }).exact = false ∧
    (verdict { r326 with T := 639 }).bridge = true ∧
    (verdict { r326 with T := 638 }).bridge = false := by decide +kernel
theorem v327 :
    verdict r327 = ⟨true, true, 1, 994, 7429, 3242, true, true, true⟩ ∧
    (verdict { r327 with T := 1332 }).exact = true ∧
    (verdict { r327 with T := 1331 }).exact = false ∧
    (verdict { r327 with T := 1332 }).bridge = true ∧
    (verdict { r327 with T := 1331 }).bridge = false := by decide +kernel
theorem v328 :
    verdict r328 = ⟨true, true, 1, 635, 2659, 1140, true, true, true⟩ ∧
    (verdict { r328 with T := 853 }).exact = true ∧
    (verdict { r328 with T := 852 }).exact = false ∧
    (verdict { r328 with T := 853 }).bridge = true ∧
    (verdict { r328 with T := 852 }).bridge = false := by decide +kernel
theorem v329 :
    verdict r329 = ⟨true, true, 1, 1148, 5731, 2501, true, true, true⟩ ∧
    (verdict { r329 with T := 1865 }).exact = true ∧
    (verdict { r329 with T := 1864 }).exact = false ∧
    (verdict { r329 with T := 1865 }).bridge = true ∧
    (verdict { r329 with T := 1864 }).bridge = false := by decide +kernel
theorem v330 :
    verdict r330 = ⟨true, true, 1, 705, 6398, 2799, true, true, true⟩ ∧
    (verdict { r330 with T := 581 }).exact = true ∧
    (verdict { r330 with T := 580 }).exact = false ∧
    (verdict { r330 with T := 705 }).bridge = true ∧
    (verdict { r330 with T := 704 }).bridge = false := by decide +kernel
theorem v331 :
    verdict r331 = ⟨true, true, 1, 815, 4925, 2152, true, true, true⟩ ∧
    (verdict { r331 with T := 757 }).exact = true ∧
    (verdict { r331 with T := 756 }).exact = false ∧
    (verdict { r331 with T := 815 }).bridge = true ∧
    (verdict { r331 with T := 814 }).bridge = false := by decide +kernel
theorem v332 :
    verdict r332 = ⟨true, true, 1, 472, 3307, 1362, true, true, true⟩ ∧
    (verdict { r332 with T := 573 }).exact = true ∧
    (verdict { r332 with T := 572 }).exact = false ∧
    (verdict { r332 with T := 573 }).bridge = true ∧
    (verdict { r332 with T := 572 }).bridge = false := by decide +kernel
theorem v333 :
    verdict r333 = ⟨true, true, 1, 1013, 7300, 3094, true, true, true⟩ ∧
    (verdict { r333 with T := 1336 }).exact = true ∧
    (verdict { r333 with T := 1335 }).exact = false ∧
    (verdict { r333 with T := 1336 }).bridge = true ∧
    (verdict { r333 with T := 1335 }).bridge = false := by decide +kernel
theorem v334 :
    verdict r334 = ⟨true, true, 1, 545, 2544, 1046, true, true, true⟩ ∧
    (verdict { r334 with T := 818 }).exact = true ∧
    (verdict { r334 with T := 817 }).exact = false ∧
    (verdict { r334 with T := 818 }).bridge = true ∧
    (verdict { r334 with T := 817 }).bridge = false := by decide +kernel
theorem v335 :
    verdict r335 = ⟨true, true, 1, 1171, 5633, 2387, true, true, true⟩ ∧
    (verdict { r335 with T := 1869 }).exact = true ∧
    (verdict { r335 with T := 1868 }).exact = false ∧
    (verdict { r335 with T := 1869 }).bridge = true ∧
    (verdict { r335 with T := 1868 }).bridge = false := by decide +kernel
theorem v336 :
    verdict r336 = ⟨true, true, 1, 552, 5707, 2646, true, true, true⟩ ∧
    (verdict { r336 with T := 428 }).exact = true ∧
    (verdict { r336 with T := 427 }).exact = false ∧
    (verdict { r336 with T := 552 }).bridge = true ∧
    (verdict { r336 with T := 551 }).bridge = false := by decide +kernel
theorem v337 :
    verdict r337 = ⟨true, true, 1, 639, 4389, 2034, true, true, true⟩ ∧
    (verdict { r337 with T := 699 }).exact = true ∧
    (verdict { r337 with T := 698 }).exact = false ∧
    (verdict { r337 with T := 699 }).bridge = true ∧
    (verdict { r337 with T := 698 }).bridge = false := by decide +kernel
theorem v338 :
    verdict r338 = ⟨true, true, 1, 482, 3342, 1552, true, true, true⟩ ∧
    (verdict { r338 with T := 539 }).exact = true ∧
    (verdict { r338 with T := 538 }).exact = false ∧
    (verdict { r338 with T := 539 }).bridge = true ∧
    (verdict { r338 with T := 538 }).bridge = false := by decide +kernel
theorem v339 :
    verdict r339 = ⟨true, true, 1, 1026, 7547, 3534, true, true, true⟩ ∧
    (verdict { r339 with T := 1312 }).exact = true ∧
    (verdict { r339 with T := 1311 }).exact = false ∧
    (verdict { r339 with T := 1312 }).bridge = true ∧
    (verdict { r339 with T := 1311 }).bridge = false := by decide +kernel
theorem v340 :
    verdict r340 = ⟨true, true, 1, 557, 2570, 1193, true, true, true⟩ ∧
    (verdict { r340 with T := 769 }).exact = true ∧
    (verdict { r340 with T := 768 }).exact = false ∧
    (verdict { r340 with T := 769 }).bridge = true ∧
    (verdict { r340 with T := 768 }).bridge = false := by decide +kernel
theorem v341 :
    verdict r341 = ⟨true, true, 1, 1186, 5822, 2725, true, true, true⟩ ∧
    (verdict { r341 with T := 1797 }).exact = true ∧
    (verdict { r341 with T := 1796 }).exact = false ∧
    (verdict { r341 with T := 1797 }).bridge = true ∧
    (verdict { r341 with T := 1796 }).bridge = false := by decide +kernel
theorem v342 :
    verdict r342 = ⟨true, true, 1, 1836, 12872, 3930, true, true, true⟩ ∧
    (verdict { r342 with T := 1712 }).exact = true ∧
    (verdict { r342 with T := 1711 }).exact = false ∧
    (verdict { r342 with T := 1836 }).bridge = true ∧
    (verdict { r342 with T := 1835 }).bridge = false := by decide +kernel
theorem v343 :
    verdict r343 = ⟨true, true, 1, 2122, 9917, 3025, true, true, true⟩ ∧
    (verdict { r343 with T := 1978 }).exact = true ∧
    (verdict { r343 with T := 1977 }).exact = false ∧
    (verdict { r343 with T := 2122 }).bridge = true ∧
    (verdict { r343 with T := 2121 }).bridge = false := by decide +kernel
theorem v344 :
    verdict r344 = ⟨true, true, 1, 1677, 7916, 2698, true, true, true⟩ ∧
    (verdict { r344 with T := 1631 }).exact = true ∧
    (verdict { r344 with T := 1630 }).exact = false ∧
    (verdict { r344 with T := 1683 }).bridge = true ∧
    (verdict { r344 with T := 1682 }).bridge = false := by decide +kernel
theorem v345 :
    verdict r345 = ⟨true, true, 1, 2903, 15879, 5311, true, true, true⟩ ∧
    (verdict { r345 with T := 2786 }).exact = true ∧
    (verdict { r345 with T := 2785 }).exact = false ∧
    (verdict { r345 with T := 2903 }).bridge = true ∧
    (verdict { r345 with T := 2902 }).bridge = false := by decide +kernel
theorem v346 :
    verdict r346 = ⟨true, true, 1, 1937, 6098, 2077, true, true, true⟩ ∧
    (verdict { r346 with T := 1884 }).exact = true ∧
    (verdict { r346 with T := 1883 }).exact = false ∧
    (verdict { r346 with T := 1945 }).bridge = true ∧
    (verdict { r346 with T := 1944 }).bridge = false := by decide +kernel
theorem v347 :
    verdict r347 = ⟨true, true, 1, 3354, 12254, 4099, true, true, true⟩ ∧
    (verdict { r347 with T := 3218 }).exact = true ∧
    (verdict { r347 with T := 3217 }).exact = false ∧
    (verdict { r347 with T := 3354 }).bridge = true ∧
    (verdict { r347 with T := 3353 }).bridge = false := by decide +kernel
theorem v348 :
    verdict r348 = ⟨true, true, 1, 745, 6818, 2839, true, true, true⟩ ∧
    (verdict { r348 with T := 772 }).exact = true ∧
    (verdict { r348 with T := 771 }).exact = false ∧
    (verdict { r348 with T := 895 }).bridge = true ∧
    (verdict { r348 with T := 894 }).bridge = false := by decide +kernel
theorem v349 :
    verdict r349 = ⟨true, true, 1, 862, 5247, 2183, true, true, true⟩ ∧
    (verdict { r349 with T := 947 }).exact = true ∧
    (verdict { r349 with T := 946 }).exact = false ∧
    (verdict { r349 with T := 1035 }).bridge = true ∧
    (verdict { r349 with T := 1034 }).bridge = false := by decide +kernel
theorem v350 :
    verdict r350 = ⟨true, true, 1, 671, 3664, 1493, true, true, true⟩ ∧
    (verdict { r350 with T := 516 }).exact = true ∧
    (verdict { r350 with T := 515 }).exact = false ∧
    (verdict { r350 with T := 833 }).bridge = true ∧
    (verdict { r350 with T := 832 }).bridge = false := by decide +kernel
theorem v351 :
    verdict r351 = ⟨true, true, 1, 1304, 7949, 3310, true, true, true⟩ ∧
    (verdict { r351 with T := 1453 }).exact = true ∧
    (verdict { r351 with T := 1452 }).exact = false ∧
    (verdict { r351 with T := 1587 }).bridge = true ∧
    (verdict { r351 with T := 1586 }).bridge = false := by decide +kernel
theorem v352 :
    verdict r352 = ⟨true, true, 1, 776, 2819, 1148, true, true, true⟩ ∧
    (verdict { r352 with T := 828 }).exact = true ∧
    (verdict { r352 with T := 827 }).exact = false ∧
    (verdict { r352 with T := 963 }).bridge = true ∧
    (verdict { r352 with T := 962 }).bridge = false := by decide +kernel
theorem v353 :
    verdict r353 = ⟨true, true, 1, 1507, 6133, 2554, true, true, true⟩ ∧
    (verdict { r353 with T := 1855 }).exact = true ∧
    (verdict { r353 with T := 1854 }).exact = false ∧
    (verdict { r353 with T := 1855 }).bridge = true ∧
    (verdict { r353 with T := 1854 }).bridge = false := by decide +kernel
theorem v354 :
    verdict r354 = ⟨true, true, 1, 1898, 13099, 3808, true, true, true⟩ ∧
    (verdict { r354 with T := 1590 }).exact = true ∧
    (verdict { r354 with T := 1589 }).exact = false ∧
    (verdict { r354 with T := 1898 }).bridge = true ∧
    (verdict { r354 with T := 1897 }).bridge = false := by decide +kernel
theorem v355 :
    verdict r355 = ⟨true, true, 1, 2193, 10091, 2931, true, true, true⟩ ∧
    (verdict { r355 with T := 1837 }).exact = true ∧
    (verdict { r355 with T := 1836 }).exact = false ∧
    (verdict { r355 with T := 2193 }).bridge = true ∧
    (verdict { r355 with T := 2192 }).bridge = false := by decide +kernel
theorem v356 :
    verdict r356 = ⟨true, true, 1, 1553, 7386, 2284, true, true, true⟩ ∧
    (verdict { r356 with T := 1220 }).exact = true ∧
    (verdict { r356 with T := 1219 }).exact = false ∧
    (verdict { r356 with T := 1558 }).bridge = true ∧
    (verdict { r356 with T := 1557 }).bridge = false := by decide +kernel
theorem v357 :
    verdict r357 = ⟨true, true, 1, 2801, 15170, 4583, true, true, true⟩ ∧
    (verdict { r357 with T := 2076 }).exact = true ∧
    (verdict { r357 with T := 2075 }).exact = false ∧
    (verdict { r357 with T := 2802 }).bridge = true ∧
    (verdict { r357 with T := 2801 }).bridge = false := by decide +kernel
theorem v358 :
    verdict r358 = ⟨true, true, 1, 1794, 5688, 1757, true, true, true⟩ ∧
    (verdict { r358 with T := 1486 }).exact = true ∧
    (verdict { r358 with T := 1485 }).exact = false ∧
    (verdict { r358 with T := 1800 }).bridge = true ∧
    (verdict { r358 with T := 1799 }).bridge = false := by decide +kernel
theorem v359 :
    verdict r359 = ⟨true, true, 1, 3236, 11705, 3535, true, true, true⟩ ∧
    (verdict { r359 with T := 2853 }).exact = true ∧
    (verdict { r359 with T := 2852 }).exact = false ∧
    (verdict { r359 with T := 3237 }).bridge = true ∧
    (verdict { r359 with T := 3236 }).bridge = false := by decide +kernel
theorem v360 :
    verdict r360 = ⟨true, true, 1, 744, 6233, 2838, true, true, true⟩ ∧
    (verdict { r360 with T := 824 }).exact = true ∧
    (verdict { r360 with T := 823 }).exact = false ∧
    (verdict { r360 with T := 956 }).bridge = true ∧
    (verdict { r360 with T := 955 }).bridge = false := by decide +kernel
theorem v361 :
    verdict r361 = ⟨true, true, 1, 860, 4794, 2182, true, true, true⟩ ∧
    (verdict { r361 with T := 1007 }).exact = true ∧
    (verdict { r361 with T := 1006 }).exact = false ∧
    (verdict { r361 with T := 1105 }).bridge = true ∧
    (verdict { r361 with T := 1104 }).bridge = false := by decide +kernel
theorem v362 :
    verdict r362 = ⟨true, true, 1, 678, 3870, 1791, true, true, true⟩ ∧
    (verdict { r362 with T := 776 }).exact = true ∧
    (verdict { r362 with T := 775 }).exact = false ∧
    (verdict { r362 with T := 776 }).bridge = true ∧
    (verdict { r362 with T := 775 }).bridge = false := by decide +kernel
theorem v363 :
    verdict r363 = ⟨true, true, 1, 1320, 8341, 3928, true, true, true⟩ ∧
    (verdict { r363 with T := 1784 }).exact = true ∧
    (verdict { r363 with T := 1783 }).exact = false ∧
    (verdict { r363 with T := 1784 }).bridge = true ∧
    (verdict { r363 with T := 1783 }).bridge = false := by decide +kernel
theorem v364 :
    verdict r364 = ⟨true, true, 1, 783, 2977, 1377, true, true, true⟩ ∧
    (verdict { r364 with T := 1054 }).exact = true ∧
    (verdict { r364 with T := 1053 }).exact = false ∧
    (verdict { r364 with T := 1054 }).bridge = true ∧
    (verdict { r364 with T := 1053 }).bridge = false := by decide +kernel
theorem v365 :
    verdict r365 = ⟨true, true, 1, 1525, 6433, 3029, true, true, true⟩ ∧
    (verdict { r365 with T := 2346 }).exact = true ∧
    (verdict { r365 with T := 2345 }).exact = false ∧
    (verdict { r365 with T := 2346 }).bridge = true ∧
    (verdict { r365 with T := 2345 }).bridge = false := by decide +kernel
theorem v366 :
    verdict r366 = ⟨true, true, 1, 1077, 12124, 3031, true, true, true⟩ ∧
    (verdict { r366 with T := 813 }).exact = true ∧
    (verdict { r366 with T := 812 }).exact = false ∧
    (verdict { r366 with T := 1149 }).bridge = true ∧
    (verdict { r366 with T := 1148 }).bridge = false := by decide +kernel
theorem v367 :
    verdict r367 = ⟨true, true, 1, 1245, 9339, 2331, true, true, true⟩ ∧
    (verdict { r367 with T := 1185 }).exact = true ∧
    (verdict { r367 with T := 1184 }).exact = false ∧
    (verdict { r367 with T := 1328 }).bridge = true ∧
    (verdict { r367 with T := 1327 }).bridge = false := by decide +kernel
theorem v368 :
    verdict r368 = ⟨true, true, 1, 916, 6818, 1580, true, true, true⟩ ∧
    (verdict { r368 with T := 605 }).exact = true ∧
    (verdict { r368 with T := 604 }).exact = false ∧
    (verdict { r368 with T := 921 }).bridge = true ∧
    (verdict { r368 with T := 920 }).bridge = false := by decide +kernel
theorem v369 :
    verdict r369 = ⟨true, true, 1, 1739, 13839, 3393, true, true, true⟩ ∧
    (verdict { r369 with T := 1412 }).exact = true ∧
    (verdict { r369 with T := 1411 }).exact = false ∧
    (verdict { r369 with T := 1740 }).bridge = true ∧
    (verdict { r369 with T := 1739 }).bridge = false := by decide +kernel
theorem v370 :
    verdict r370 = ⟨true, true, 1, 1058, 5244, 1215, true, true, true⟩ ∧
    (verdict { r370 with T := 1000 }).exact = true ∧
    (verdict { r370 with T := 999 }).exact = false ∧
    (verdict { r370 with T := 1064 }).bridge = true ∧
    (verdict { r370 with T := 1063 }).bridge = false := by decide +kernel
theorem v371 :
    verdict r371 = ⟨true, true, 1, 2009, 10680, 2618, true, true, true⟩ ∧
    (verdict { r371 with T := 2020 }).exact = true ∧
    (verdict { r371 with T := 2019 }).exact = false ∧
    (verdict { r371 with T := 2020 }).bridge = true ∧
    (verdict { r371 with T := 2019 }).bridge = false := by decide +kernel
theorem v372 :
    verdict r372 = ⟨true, true, 1, 893, 9929, 2987, true, true, true⟩ ∧
    (verdict { r372 with T := 769 }).exact = true ∧
    (verdict { r372 with T := 768 }).exact = false ∧
    (verdict { r372 with T := 893 }).bridge = true ∧
    (verdict { r372 with T := 892 }).bridge = false := by decide +kernel
theorem v373 :
    verdict r373 = ⟨true, true, 1, 1033, 7645, 2297, true, true, true⟩ ∧
    (verdict { r373 with T := 889 }).exact = true ∧
    (verdict { r373 with T := 888 }).exact = false ∧
    (verdict { r373 with T := 1033 }).bridge = true ∧
    (verdict { r373 with T := 1032 }).bridge = false := by decide +kernel
theorem v374 :
    verdict r374 = ⟨true, true, 1, 786, 6242, 1831, true, true, true⟩ ∧
    (verdict { r374 with T := 742 }).exact = true ∧
    (verdict { r374 with T := 741 }).exact = false ∧
    (verdict { r374 with T := 791 }).bridge = true ∧
    (verdict { r374 with T := 790 }).bridge = false := by decide +kernel
theorem v375 :
    verdict r375 = ⟨true, true, 1, 1508, 13246, 3961, true, true, true⟩ ∧
    (verdict { r375 with T := 1397 }).exact = true ∧
    (verdict { r375 with T := 1396 }).exact = false ∧
    (verdict { r375 with T := 1510 }).bridge = true ∧
    (verdict { r375 with T := 1509 }).bridge = false := by decide +kernel
theorem v376 :
    verdict r376 = ⟨true, true, 1, 908, 4805, 1408, true, true, true⟩ ∧
    (verdict { r376 with T := 905 }).exact = true ∧
    (verdict { r376 with T := 904 }).exact = false ∧
    (verdict { r376 with T := 914 }).bridge = true ∧
    (verdict { r376 with T := 913 }).bridge = false := by decide +kernel
theorem v377 :
    verdict r377 = ⟨true, true, 1, 1743, 10221, 3055, true, true, true⟩ ∧
    (verdict { r377 with T := 2024 }).exact = true ∧
    (verdict { r377 with T := 2023 }).exact = false ∧
    (verdict { r377 with T := 2024 }).bridge = true ∧
    (verdict { r377 with T := 2023 }).bridge = false := by decide +kernel
theorem v378 :
    verdict r378 = ⟨true, true, 1, 737, 8684, 2831, true, true, true⟩ ∧
    (verdict { r378 with T := 613 }).exact = true ∧
    (verdict { r378 with T := 612 }).exact = false ∧
    (verdict { r378 with T := 737 }).bridge = true ∧
    (verdict { r378 with T := 736 }).bridge = false := by decide +kernel
theorem v379 :
    verdict r379 = ⟨true, true, 1, 852, 6686, 2177, true, true, true⟩ ∧
    (verdict { r379 with T := 769 }).exact = true ∧
    (verdict { r379 with T := 768 }).exact = false ∧
    (verdict { r379 with T := 852 }).bridge = true ∧
    (verdict { r379 with T := 851 }).bridge = false := by decide +kernel
theorem v380 :
    verdict r380 = ⟨true, true, 1, 629, 5468, 1549, true, true, true⟩ ∧
    (verdict { r380 with T := 663 }).exact = true ∧
    (verdict { r380 with T := 662 }).exact = false ∧
    (verdict { r380 with T := 718 }).bridge = true ∧
    (verdict { r380 with T := 717 }).bridge = false := by decide +kernel
theorem v381 :
    verdict r381 = ⟨true, true, 1, 1172, 11653, 3391, true, true, true⟩ ∧
    (verdict { r381 with T := 1361 }).exact = true ∧
    (verdict { r381 with T := 1360 }).exact = false ∧
    (verdict { r381 with T := 1362 }).bridge = true ∧
    (verdict { r381 with T := 1361 }).bridge = false := by decide +kernel
theorem v382 :
    verdict r382 = ⟨true, true, 1, 727, 4209, 1191, true, true, true⟩ ∧
    (verdict { r382 with T := 893 }).exact = true ∧
    (verdict { r382 with T := 892 }).exact = false ∧
    (verdict { r382 with T := 893 }).bridge = true ∧
    (verdict { r382 with T := 892 }).bridge = false := by decide +kernel
theorem v383 :
    verdict r383 = ⟨true, true, 1, 1354, 8991, 2616, true, true, true⟩ ∧
    (verdict { r383 with T := 1956 }).exact = true ∧
    (verdict { r383 with T := 1955 }).exact = false ∧
    (verdict { r383 with T := 1956 }).bridge = true ∧
    (verdict { r383 with T := 1955 }).bridge = false := by decide +kernel
theorem v384 :
    verdict r384 = ⟨true, true, 1, 707, 8887, 2874, true, true, true⟩ ∧
    (verdict { r384 with T := 632 }).exact = true ∧
    (verdict { r384 with T := 631 }).exact = false ∧
    (verdict { r384 with T := 707 }).bridge = true ∧
    (verdict { r384 with T := 706 }).bridge = false := by decide +kernel
theorem v385 :
    verdict r385 = ⟨true, true, 1, 818, 6844, 2211, true, true, true⟩ ∧
    (verdict { r385 with T := 950 }).exact = true ∧
    (verdict { r385 with T := 949 }).exact = false ∧
    (verdict { r385 with T := 950 }).bridge = true ∧
    (verdict { r385 with T := 949 }).bridge = false := by decide +kernel
theorem v386 :
    verdict r386 = ⟨true, true, 1, 540, 5077, 1577, true, true, true⟩ ∧
    (verdict { r386 with T := 434 }).exact = true ∧
    (verdict { r386 with T := 433 }).exact = false ∧
    (verdict { r386 with T := 545 }).bridge = true ∧
    (verdict { r386 with T := 544 }).bridge = false := by decide +kernel
theorem v387 :
    verdict r387 = ⟨true, true, 1, 1177, 11273, 3651, true, true, true⟩ ∧
    (verdict { r387 with T := 1198 }).exact = true ∧
    (verdict { r387 with T := 1197 }).exact = false ∧
    (verdict { r387 with T := 1198 }).bridge = true ∧
    (verdict { r387 with T := 1197 }).bridge = false := by decide +kernel
theorem v388 :
    verdict r388 = ⟨true, true, 1, 624, 3909, 1212, true, true, true⟩ ∧
    (verdict { r388 with T := 767 }).exact = true ∧
    (verdict { r388 with T := 766 }).exact = false ∧
    (verdict { r388 with T := 767 }).bridge = true ∧
    (verdict { r388 with T := 766 }).bridge = false := by decide +kernel
theorem v389 :
    verdict r389 = ⟨true, true, 1, 1360, 8698, 2816, true, true, true⟩ ∧
    (verdict { r389 with T := 1759 }).exact = true ∧
    (verdict { r389 with T := 1758 }).exact = false ∧
    (verdict { r389 with T := 1759 }).bridge = true ∧
    (verdict { r389 with T := 1758 }).bridge = false := by decide +kernel
theorem v390 :
    verdict r390 = ⟨true, true, 1, 704, 8977, 2938, true, true, true⟩ ∧
    (verdict { r390 with T := 580 }).exact = true ∧
    (verdict { r390 with T := 579 }).exact = false ∧
    (verdict { r390 with T := 704 }).bridge = true ∧
    (verdict { r390 with T := 703 }).bridge = false := by decide +kernel
theorem v391 :
    verdict r391 = ⟨true, true, 1, 814, 6912, 2259, true, true, true⟩ ∧
    (verdict { r391 with T := 919 }).exact = true ∧
    (verdict { r391 with T := 918 }).exact = false ∧
    (verdict { r391 with T := 919 }).bridge = true ∧
    (verdict { r391 with T := 918 }).bridge = false := by decide +kernel
theorem v392 :
    verdict r392 = ⟨true, true, 1, 370, 4857, 1577, true, true, true⟩ ∧
    (verdict { r392 with T := 606 }).exact = true ∧
    (verdict { r392 with T := 605 }).exact = false ∧
    (verdict { r392 with T := 606 }).bridge = true ∧
    (verdict { r392 with T := 605 }).bridge = false := by decide +kernel
theorem v393 :
    verdict r393 = ⟨true, true, 1, 753, 10811, 3653, true, true, true⟩ ∧
    (verdict { r393 with T := 1404 }).exact = true ∧
    (verdict { r393 with T := 1403 }).exact = false ∧
    (verdict { r393 with T := 1404 }).bridge = true ∧
    (verdict { r393 with T := 1403 }).bridge = false := by decide +kernel
theorem v394 :
    verdict r394 = ⟨true, true, 1, 428, 3737, 1212, true, true, true⟩ ∧
    (verdict { r394 with T := 843 }).exact = true ∧
    (verdict { r394 with T := 842 }).exact = false ∧
    (verdict { r394 with T := 843 }).bridge = true ∧
    (verdict { r394 with T := 842 }).bridge = false := by decide +kernel
theorem v395 :
    verdict r395 = ⟨true, true, 1, 870, 8340, 2818, true, true, true⟩ ∧
    (verdict { r395 with T := 1918 }).exact = true ∧
    (verdict { r395 with T := 1917 }).exact = false ∧
    (verdict { r395 with T := 1918 }).bridge = true ∧
    (verdict { r395 with T := 1917 }).bridge = false := by decide +kernel
theorem v396 :
    verdict r396 = ⟨true, true, 1, 561, 10020, 2655, true, true, true⟩ ∧
    (verdict { r396 with T := 437 }).exact = true ∧
    (verdict { r396 with T := 436 }).exact = false ∧
    (verdict { r396 with T := 561 }).bridge = true ∧
    (verdict { r396 with T := 560 }).bridge = false := by decide +kernel
theorem v397 :
    verdict r397 = ⟨true, true, 1, 649, 7718, 2041, true, true, true⟩ ∧
    (verdict { r397 with T := 702 }).exact = true ∧
    (verdict { r397 with T := 701 }).exact = false ∧
    (verdict { r397 with T := 702 }).bridge = true ∧
    (verdict { r397 with T := 701 }).bridge = false := by decide +kernel
theorem v398 :
    verdict r398 = ⟨true, true, 1, 393, 5197, 1291, true, true, true⟩ ∧
    (verdict { r398 with T := 565 }).exact = true ∧
    (verdict { r398 with T := 564 }).exact = false ∧
    (verdict { r398 with T := 565 }).bridge = true ∧
    (verdict { r398 with T := 564 }).bridge = false := by decide +kernel
theorem v399 :
    verdict r399 = ⟨true, true, 1, 841, 11284, 2945, true, true, true⟩ ∧
    (verdict { r399 with T := 1313 }).exact = true ∧
    (verdict { r399 with T := 1312 }).exact = false ∧
    (verdict { r399 with T := 1313 }).bridge = true ∧
    (verdict { r399 with T := 1312 }).bridge = false := by decide +kernel
theorem v400 :
    verdict r400 = ⟨true, true, 1, 454, 4001, 991, true, true, true⟩ ∧
    (verdict { r400 with T := 781 }).exact = true ∧
    (verdict { r400 with T := 780 }).exact = false ∧
    (verdict { r400 with T := 781 }).bridge = true ∧
    (verdict { r400 with T := 780 }).bridge = false := by decide +kernel
theorem v401 :
    verdict r401 = ⟨true, true, 1, 972, 8706, 2272, true, true, true⟩ ∧
    (verdict { r401 with T := 1785 }).exact = true ∧
    (verdict { r401 with T := 1784 }).exact = false ∧
    (verdict { r401 with T := 1785 }).bridge = true ∧
    (verdict { r401 with T := 1784 }).bridge = false := by decide +kernel
theorem v402 :
    verdict r402 = ⟨true, true, 1, 553, 6278, 2860, true, true, true⟩ ∧
    (verdict { r402 with T := 621 }).exact = true ∧
    (verdict { r402 with T := 620 }).exact = false ∧
    (verdict { r402 with T := 703 }).bridge = true ∧
    (verdict { r402 with T := 702 }).bridge = false := by decide +kernel
theorem v403 :
    verdict r403 = ⟨true, true, 1, 640, 4832, 2200, true, true, true⟩ ∧
    (verdict { r403 with T := 937 }).exact = true ∧
    (verdict { r403 with T := 936 }).exact = false ∧
    (verdict { r403 with T := 937 }).bridge = true ∧
    (verdict { r403 with T := 936 }).bridge = false := by decide +kernel
theorem v404 :
    verdict r404 = ⟨true, true, 1, 465, 3601, 1527, true, true, true⟩ ∧
    (verdict { r404 with T := 594 }).exact = true ∧
    (verdict { r404 with T := 593 }).exact = false ∧
    (verdict { r404 with T := 594 }).bridge = true ∧
    (verdict { r404 with T := 593 }).bridge = false := by decide +kernel
theorem v405 :
    verdict r405 = ⟨true, true, 1, 998, 8192, 3547, true, true, true⟩ ∧
    (verdict { r405 with T := 1429 }).exact = true ∧
    (verdict { r405 with T := 1428 }).exact = false ∧
    (verdict { r405 with T := 1429 }).bridge = true ∧
    (verdict { r405 with T := 1428 }).bridge = false := by decide +kernel
theorem v406 :
    verdict r406 = ⟨true, true, 1, 537, 2767, 1173, true, true, true⟩ ∧
    (verdict { r406 with T := 790 }).exact = true ∧
    (verdict { r406 with T := 789 }).exact = false ∧
    (verdict { r406 with T := 790 }).bridge = true ∧
    (verdict { r406 with T := 789 }).bridge = false := by decide +kernel
theorem v407 :
    verdict r407 = ⟨true, true, 1, 1153, 6322, 2736, true, true, true⟩ ∧
    (verdict { r407 with T := 1857 }).exact = true ∧
    (verdict { r407 with T := 1856 }).exact = false ∧
    (verdict { r407 with T := 1857 }).bridge = true ∧
    (verdict { r407 with T := 1856 }).bridge = false := by decide +kernel
theorem v408 :
    verdict r408 = ⟨true, true, 1, 892, 6154, 2846, true, true, true⟩ ∧
    (verdict { r408 with T := 628 }).exact = true ∧
    (verdict { r408 with T := 627 }).exact = false ∧
    (verdict { r408 with T := 892 }).bridge = true ∧
    (verdict { r408 with T := 891 }).bridge = false := by decide +kernel
theorem v409 :
    verdict r409 = ⟨true, true, 1, 1031, 4738, 2189, true, true, true⟩ ∧
    (verdict { r409 with T := 775 }).exact = true ∧
    (verdict { r409 with T := 774 }).exact = false ∧
    (verdict { r409 with T := 1031 }).bridge = true ∧
    (verdict { r409 with T := 1030 }).bridge = false := by decide +kernel
theorem v410 :
    verdict r410 = ⟨true, true, 1, 679, 3497, 1563, true, true, true⟩ ∧
    (verdict { r410 with T := 493 }).exact = true ∧
    (verdict { r410 with T := 492 }).exact = false ∧
    (verdict { r410 with T := 679 }).bridge = true ∧
    (verdict { r410 with T := 678 }).bridge = false := by decide +kernel
theorem v411 :
    verdict r411 = ⟨true, true, 1, 1396, 7848, 3503, true, true, true⟩ ∧
    (verdict { r411 with T := 1117 }).exact = true ∧
    (verdict { r411 with T := 1116 }).exact = false ∧
    (verdict { r411 with T := 1396 }).bridge = true ∧
    (verdict { r411 with T := 1395 }).bridge = false := by decide +kernel
theorem v412 :
    verdict r412 = ⟨true, true, 1, 785, 2691, 1201, true, true, true⟩ ∧
    (verdict { r412 with T := 826 }).exact = true ∧
    (verdict { r412 with T := 825 }).exact = false ∧
    (verdict { r412 with T := 826 }).bridge = true ∧
    (verdict { r412 with T := 825 }).bridge = false := by decide +kernel
theorem v413 :
    verdict r413 = ⟨true, true, 1, 1613, 6057, 2703, true, true, true⟩ ∧
    (verdict { r413 with T := 1853 }).exact = true ∧
    (verdict { r413 with T := 1852 }).exact = false ∧
    (verdict { r413 with T := 1853 }).bridge = true ∧
    (verdict { r413 with T := 1852 }).bridge = false := by decide +kernel
theorem v414 :
    verdict r414 = ⟨true, true, 1, 951, 6587, 3031, true, true, true⟩ ∧
    (verdict { r414 with T := 838 }).exact = true ∧
    (verdict { r414 with T := 837 }).exact = false ∧
    (verdict { r414 with T := 1077 }).bridge = true ∧
    (verdict { r414 with T := 1076 }).bridge = false := by decide +kernel
theorem v415 :
    verdict r415 = ⟨true, true, 1, 1100, 5070, 2331, true, true, true⟩ ∧
    (verdict { r415 with T := 1102 }).exact = true ∧
    (verdict { r415 with T := 1101 }).exact = false ∧
    (verdict { r415 with T := 1245 }).bridge = true ∧
    (verdict { r415 with T := 1244 }).bridge = false := by decide +kernel
theorem v416 :
    verdict r416 = ⟨true, true, 1, 824, 4082, 1926, true, true, true⟩ ∧
    (verdict { r416 with T := 772 }).exact = true ∧
    (verdict { r416 with T := 771 }).exact = false ∧
    (verdict { r416 with T := 827 }).bridge = true ∧
    (verdict { r416 with T := 826 }).bridge = false := by decide +kernel
theorem v417 :
    verdict r417 = ⟨true, true, 1, 1581, 8723, 4158, true, true, true⟩ ∧
    (verdict { r417 with T := 1487 }).exact = true ∧
    (verdict { r417 with T := 1486 }).exact = false ∧
    (verdict { r417 with T := 1584 }).bridge = true ∧
    (verdict { r417 with T := 1583 }).bridge = false := by decide +kernel
theorem v418 :
    verdict r418 = ⟨true, true, 1, 952, 3142, 1482, true, true, true⟩ ∧
    (verdict { r418 with T := 968 }).exact = true ∧
    (verdict { r418 with T := 967 }).exact = false ∧
    (verdict { r418 with T := 968 }).bridge = true ∧
    (verdict { r418 with T := 967 }).bridge = false := by decide +kernel
theorem v419 :
    verdict r419 = ⟨true, true, 1, 1827, 6730, 3207, true, true, true⟩ ∧
    (verdict { r419 with T := 2150 }).exact = true ∧
    (verdict { r419 with T := 2149 }).exact = false ∧
    (verdict { r419 with T := 2150 }).bridge = true ∧
    (verdict { r419 with T := 2149 }).bridge = false := by decide +kernel
theorem v420 :
    verdict r420 = ⟨true, true, 1, 1960, 9900, 4054, true, true, true⟩ ∧
    (verdict { r420 with T := 1836 }).exact = true ∧
    (verdict { r420 with T := 1835 }).exact = false ∧
    (verdict { r420 with T := 1960 }).bridge = true ∧
    (verdict { r420 with T := 1959 }).bridge = false := by decide +kernel
theorem v421 :
    verdict r421 = ⟨true, true, 1, 2265, 7628, 3121, true, true, true⟩ ∧
    (verdict { r421 with T := 2121 }).exact = true ∧
    (verdict { r421 with T := 2120 }).exact = false ∧
    (verdict { r421 with T := 2265 }).bridge = true ∧
    (verdict { r421 with T := 2264 }).bridge = false := by decide +kernel
theorem v422 :
    verdict r422 = ⟨true, true, 1, 1254, 5390, 2084, true, true, true⟩ ∧
    (verdict { r422 with T := 1203 }).exact = true ∧
    (verdict { r422 with T := 1202 }).exact = false ∧
    (verdict { r422 with T := 1343 }).bridge = true ∧
    (verdict { r422 with T := 1342 }).bridge = false := by decide +kernel
theorem v423 :
    verdict r423 = ⟨true, true, 1, 2422, 11328, 4443, true, true, true⟩ ∧
    (verdict { r423 with T := 2470 }).exact = true ∧
    (verdict { r423 with T := 2469 }).exact = false ∧
    (verdict { r423 with T := 2612 }).bridge = true ∧
    (verdict { r423 with T := 2611 }).bridge = false := by decide +kernel
theorem v424 :
    verdict r424 = ⟨true, true, 1, 1449, 4153, 1604, true, true, true⟩ ∧
    (verdict { r424 with T := 1480 }).exact = true ∧
    (verdict { r424 with T := 1479 }).exact = false ∧
    (verdict { r424 with T := 1552 }).bridge = true ∧
    (verdict { r424 with T := 1551 }).bridge = false := by decide +kernel
theorem v425 :
    verdict r425 = ⟨true, true, 1, 2798, 8742, 3428, true, true, true⟩ ∧
    (verdict { r425 with T := 2875 }).exact = true ∧
    (verdict { r425 with T := 2874 }).exact = false ∧
    (verdict { r425 with T := 3018 }).bridge = true ∧
    (verdict { r425 with T := 3017 }).bridge = false := by decide +kernel
theorem v426 :
    verdict r426 = ⟨true, true, 1, 1044, 8761, 3138, true, true, true⟩ ∧
    (verdict { r426 with T := 920 }).exact = true ∧
    (verdict { r426 with T := 919 }).exact = false ∧
    (verdict { r426 with T := 1044 }).bridge = true ∧
    (verdict { r426 with T := 1043 }).bridge = false := by decide +kernel
theorem v427 :
    verdict r427 = ⟨true, true, 1, 1207, 6747, 2414, true, true, true⟩ ∧
    (verdict { r427 with T := 1063 }).exact = true ∧
    (verdict { r427 with T := 1062 }).exact = false ∧
    (verdict { r427 with T := 1207 }).bridge = true ∧
    (verdict { r427 with T := 1206 }).bridge = false := by decide +kernel
theorem v428 :
    verdict r428 = ⟨true, true, 1, 797, 5181, 1660, true, true, true⟩ ∧
    (verdict { r428 with T := 821 }).exact = true ∧
    (verdict { r428 with T := 820 }).exact = false ∧
    (verdict { r428 with T := 879 }).bridge = true ∧
    (verdict { r428 with T := 878 }).bridge = false := by decide +kernel
theorem v429 :
    verdict r429 = ⟨true, true, 1, 1491, 10337, 3517, true, true, true⟩ ∧
    (verdict { r429 with T := 1540 }).exact = true ∧
    (verdict { r429 with T := 1539 }).exact = false ∧
    (verdict { r429 with T := 1663 }).bridge = true ∧
    (verdict { r429 with T := 1662 }).bridge = false := by decide +kernel
theorem v430 :
    verdict r430 = ⟨true, true, 1, 921, 3990, 1276, true, true, true⟩ ∧
    (verdict { r430 with T := 962 }).exact = true ∧
    (verdict { r430 with T := 961 }).exact = false ∧
    (verdict { r430 with T := 1016 }).bridge = true ∧
    (verdict { r430 with T := 1015 }).bridge = false := by decide +kernel
theorem v431 :
    verdict r431 = ⟨true, true, 1, 1723, 7977, 2714, true, true, true⟩ ∧
    (verdict { r431 with T := 2094 }).exact = true ∧
    (verdict { r431 with T := 2093 }).exact = false ∧
    (verdict { r431 with T := 2094 }).bridge = true ∧
    (verdict { r431 with T := 2093 }).bridge = false := by decide +kernel
theorem v432 :
    verdict r432 = ⟨true, true, 1, 757, 9071, 3277, true, true, true⟩ ∧
    (verdict { r432 with T := 846 }).exact = true ∧
    (verdict { r432 with T := 845 }).exact = false ∧
    (verdict { r432 with T := 969 }).bridge = true ∧
    (verdict { r432 with T := 968 }).bridge = false := by decide +kernel
theorem v433 :
    verdict r433 = ⟨true, true, 1, 875, 6987, 2522, true, true, true⟩ ∧
    (verdict { r433 with T := 1269 }).exact = true ∧
    (verdict { r433 with T := 1268 }).exact = false ∧
    (verdict { r433 with T := 1269 }).bridge = true ∧
    (verdict { r433 with T := 1268 }).bridge = false := by decide +kernel
theorem v434 :
    verdict r434 = ⟨true, true, 1, 602, 5140, 1538, true, true, true⟩ ∧
    (verdict { r434 with T := 447 }).exact = true ∧
    (verdict { r434 with T := 446 }).exact = false ∧
    (verdict { r434 with T := 701 }).bridge = true ∧
    (verdict { r434 with T := 700 }).bridge = false := by decide +kernel
theorem v435 :
    verdict r435 = ⟨true, true, 1, 1239, 10806, 3542, true, true, true⟩ ∧
    (verdict { r435 with T := 1341 }).exact = true ∧
    (verdict { r435 with T := 1340 }).exact = false ∧
    (verdict { r435 with T := 1464 }).bridge = true ∧
    (verdict { r435 with T := 1463 }).bridge = false := by decide +kernel
theorem v436 :
    verdict r436 = ⟨true, true, 1, 696, 3959, 1183, true, true, true⟩ ∧
    (verdict { r436 with T := 793 }).exact = true ∧
    (verdict { r436 with T := 792 }).exact = false ∧
    (verdict { r436 with T := 810 }).bridge = true ∧
    (verdict { r436 with T := 809 }).bridge = false := by decide +kernel
theorem v437 :
    verdict r437 = ⟨true, true, 1, 1432, 8339, 2733, true, true, true⟩ ∧
    (verdict { r437 with T := 1855 }).exact = true ∧
    (verdict { r437 with T := 1854 }).exact = false ∧
    (verdict { r437 with T := 1855 }).bridge = true ∧
    (verdict { r437 with T := 1854 }).bridge = false := by decide +kernel
theorem v438 :
    verdict r438 = ⟨true, true, 1, 685, 6994, 2779, true, true, true⟩ ∧
    (verdict { r438 with T := 561 }).exact = true ∧
    (verdict { r438 with T := 560 }).exact = false ∧
    (verdict { r438 with T := 685 }).bridge = true ∧
    (verdict { r438 with T := 684 }).bridge = false := by decide +kernel
theorem v439 :
    verdict r439 = ⟨true, true, 1, 792, 5385, 2137, true, true, true⟩ ∧
    (verdict { r439 with T := 749 }).exact = true ∧
    (verdict { r439 with T := 748 }).exact = false ∧
    (verdict { r439 with T := 792 }).bridge = true ∧
    (verdict { r439 with T := 791 }).bridge = false := by decide +kernel
theorem v440 :
    verdict r440 = ⟨true, true, 1, 453, 3702, 1345, true, true, true⟩ ∧
    (verdict { r440 with T := 571 }).exact = true ∧
    (verdict { r440 with T := 570 }).exact = false ∧
    (verdict { r440 with T := 571 }).bridge = true ∧
    (verdict { r440 with T := 570 }).bridge = false := by decide +kernel
theorem v441 :
    verdict r441 = ⟨true, true, 1, 986, 8112, 3071, true, true, true⟩ ∧
    (verdict { r441 with T := 1332 }).exact = true ∧
    (verdict { r441 with T := 1331 }).exact = false ∧
    (verdict { r441 with T := 1332 }).bridge = true ∧
    (verdict { r441 with T := 1331 }).bridge = false := by decide +kernel
theorem v442 :
    verdict r442 = ⟨true, true, 1, 523, 2848, 1032, true, true, true⟩ ∧
    (verdict { r442 with T := 809 }).exact = true ∧
    (verdict { r442 with T := 808 }).exact = false ∧
    (verdict { r442 with T := 809 }).bridge = true ∧
    (verdict { r442 with T := 808 }).bridge = false := by decide +kernel
theorem v443 :
    verdict r443 = ⟨true, true, 1, 1139, 6260, 2369, true, true, true⟩ ∧
    (verdict { r443 with T := 1855 }).exact = true ∧
    (verdict { r443 with T := 1854 }).exact = false ∧
    (verdict { r443 with T := 1855 }).bridge = true ∧
    (verdict { r443 with T := 1854 }).bridge = false := by decide +kernel
theorem v444 :
    verdict r444 = ⟨true, true, 1, 564, 8080, 2658, true, true, true⟩ ∧
    (verdict { r444 with T := 440 }).exact = true ∧
    (verdict { r444 with T := 439 }).exact = false ∧
    (verdict { r444 with T := 564 }).bridge = true ∧
    (verdict { r444 with T := 563 }).bridge = false := by decide +kernel
theorem v445 :
    verdict r445 = ⟨true, true, 1, 653, 6220, 2043, true, true, true⟩ ∧
    (verdict { r445 with T := 704 }).exact = true ∧
    (verdict { r445 with T := 703 }).exact = false ∧
    (verdict { r445 with T := 704 }).bridge = true ∧
    (verdict { r445 with T := 703 }).bridge = false := by decide +kernel
theorem v446 :
    verdict r446 = ⟨true, true, 1, 379, 4065, 1314, true, true, true⟩ ∧
    (verdict { r446 with T := 573 }).exact = true ∧
    (verdict { r446 with T := 572 }).exact = false ∧
    (verdict { r446 with T := 573 }).bridge = true ∧
    (verdict { r446 with T := 572 }).bridge = false := by decide +kernel
theorem v447 :
    verdict r447 = ⟨true, true, 1, 844, 9131, 3092, true, true, true⟩ ∧
    (verdict { r447 with T := 1332 }).exact = true ∧
    (verdict { r447 with T := 1331 }).exact = false ∧
    (verdict { r447 with T := 1332 }).bridge = true ∧
    (verdict { r447 with T := 1331 }).bridge = false := by decide +kernel
theorem v448 :
    verdict r448 = ⟨true, true, 1, 438, 3128, 1010, true, true, true⟩ ∧
    (verdict { r448 with T := 786 }).exact = true ∧
    (verdict { r448 with T := 785 }).exact = false ∧
    (verdict { r448 with T := 786 }).bridge = true ∧
    (verdict { r448 with T := 785 }).bridge = false := by decide +kernel
theorem v449 :
    verdict r449 = ⟨true, true, 1, 976, 7046, 2385, true, true, true⟩ ∧
    (verdict { r449 with T := 1808 }).exact = true ∧
    (verdict { r449 with T := 1807 }).exact = false ∧
    (verdict { r449 with T := 1808 }).bridge = true ∧
    (verdict { r449 with T := 1807 }).bridge = false := by decide +kernel

end Formal.Timing.ChainSettleExe.GcdD
