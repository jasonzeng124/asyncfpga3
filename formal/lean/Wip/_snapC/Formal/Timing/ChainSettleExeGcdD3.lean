import Formal.Timing.ChainSettleExeGcdDData3

/-! C-10o2 GENERATED: kernel-decided verdicts of chunk 3 (see ChainSettleExe.verdict).
Per row: `verdict` at chainck's late side `T`; exact PASS at `T*` and FAIL at `T* - 1`
(margin_exact = T - T*); bridge PASS at `Tb*` and FAIL at `Tb* - 1`. -/

namespace Formal.Timing.ChainSettleExe.GcdD
open Formal.Timing Formal.Timing.ChainSettleExe

theorem v450 :
    verdict r450 = ⟨true, true, 1, 561, 5729, 2655, true, true, true⟩ ∧
    (verdict { r450 with T := 437 }).exact = true ∧
    (verdict { r450 with T := 436 }).exact = false ∧
    (verdict { r450 with T := 561 }).bridge = true ∧
    (verdict { r450 with T := 560 }).bridge = false := by decide +kernel
theorem v451 :
    verdict r451 = ⟨true, true, 1, 649, 4406, 2041, true, true, true⟩ ∧
    (verdict { r451 with T := 702 }).exact = true ∧
    (verdict { r451 with T := 701 }).exact = false ∧
    (verdict { r451 with T := 702 }).bridge = true ∧
    (verdict { r451 with T := 701 }).bridge = false := by decide +kernel
theorem v452 :
    verdict r452 = ⟨true, true, 1, 398, 2907, 1255, true, true, true⟩ ∧
    (verdict { r452 with T := 575 }).exact = true ∧
    (verdict { r452 with T := 574 }).exact = false ∧
    (verdict { r452 with T := 575 }).bridge = true ∧
    (verdict { r452 with T := 574 }).bridge = false := by decide +kernel
theorem v453 :
    verdict r453 = ⟨true, true, 1, 846, 6702, 2896, true, true, true⟩ ∧
    (verdict { r453 with T := 1332 }).exact = true ∧
    (verdict { r453 with T := 1331 }).exact = false ∧
    (verdict { r453 with T := 1332 }).bridge = true ∧
    (verdict { r453 with T := 1331 }).bridge = false := by decide +kernel
theorem v454 :
    verdict r454 = ⟨true, true, 1, 459, 2234, 964, true, true, true⟩ ∧
    (verdict { r454 with T := 794 }).exact = true ∧
    (verdict { r454 with T := 793 }).exact = false ∧
    (verdict { r454 with T := 794 }).bridge = true ∧
    (verdict { r454 with T := 793 }).bridge = false := by decide +kernel
theorem v455 :
    verdict r455 = ⟨true, true, 1, 977, 5170, 2233, true, true, true⟩ ∧
    (verdict { r455 with T := 1809 }).exact = true ∧
    (verdict { r455 with T := 1808 }).exact = false ∧
    (verdict { r455 with T := 1809 }).bridge = true ∧
    (verdict { r455 with T := 1808 }).bridge = false := by decide +kernel
theorem v456 :
    verdict r456 = ⟨true, true, 1, 701, 8489, 2795, true, true, true⟩ ∧
    (verdict { r456 with T := 577 }).exact = true ∧
    (verdict { r456 with T := 576 }).exact = false ∧
    (verdict { r456 with T := 701 }).bridge = true ∧
    (verdict { r456 with T := 700 }).bridge = false := by decide +kernel
theorem v457 :
    verdict r457 = ⟨true, true, 1, 811, 6536, 2149, true, true, true⟩ ∧
    (verdict { r457 with T := 756 }).exact = true ∧
    (verdict { r457 with T := 755 }).exact = false ∧
    (verdict { r457 with T := 811 }).bridge = true ∧
    (verdict { r457 with T := 810 }).bridge = false := by decide +kernel
theorem v458 :
    verdict r458 = ⟨true, true, 1, 527, 4472, 1440, true, true, true⟩ ∧
    (verdict { r458 with T := 512 }).exact = true ∧
    (verdict { r458 with T := 511 }).exact = false ∧
    (verdict { r458 with T := 532 }).bridge = true ∧
    (verdict { r458 with T := 531 }).bridge = false := by decide +kernel
theorem v459 :
    verdict r459 = ⟨true, true, 1, 1149, 9963, 3334, true, true, true⟩ ∧
    (verdict { r459 with T := 1196 }).exact = true ∧
    (verdict { r459 with T := 1195 }).exact = false ∧
    (verdict { r459 with T := 1196 }).bridge = true ∧
    (verdict { r459 with T := 1195 }).bridge = false := by decide +kernel
theorem v460 :
    verdict r460 = ⟨true, true, 1, 609, 3443, 1107, true, true, true⟩ ∧
    (verdict { r460 with T := 763 }).exact = true ∧
    (verdict { r460 with T := 762 }).exact = false ∧
    (verdict { r460 with T := 763 }).bridge = true ∧
    (verdict { r460 with T := 762 }).bridge = false := by decide +kernel
theorem v461 :
    verdict r461 = ⟨true, true, 1, 1328, 7689, 2572, true, true, true⟩ ∧
    (verdict { r461 with T := 1747 }).exact = true ∧
    (verdict { r461 with T := 1746 }).exact = false ∧
    (verdict { r461 with T := 1747 }).bridge = true ∧
    (verdict { r461 with T := 1746 }).bridge = false := by decide +kernel
theorem v462 :
    verdict r462 = ⟨true, true, 1, 1117, 7034, 3211, true, true, true⟩ ∧
    (verdict { r462 with T := 993 }).exact = true ∧
    (verdict { r462 with T := 992 }).exact = false ∧
    (verdict { r462 with T := 1117 }).bridge = true ∧
    (verdict { r462 with T := 1116 }).bridge = false := by decide +kernel
theorem v463 :
    verdict r463 = ⟨true, true, 1, 1291, 5413, 2470, true, true, true⟩ ∧
    (verdict { r463 with T := 1147 }).exact = true ∧
    (verdict { r463 with T := 1146 }).exact = false ∧
    (verdict { r463 with T := 1291 }).bridge = true ∧
    (verdict { r463 with T := 1290 }).bridge = false := by decide +kernel
theorem v464 :
    verdict r464 = ⟨true, true, 1, 743, 3567, 1607, true, true, true⟩ ∧
    (verdict { r464 with T := 767 }).exact = true ∧
    (verdict { r464 with T := 766 }).exact = false ∧
    (verdict { r464 with T := 825 }).bridge = true ∧
    (verdict { r464 with T := 824 }).bridge = false := by decide +kernel
theorem v465 :
    verdict r465 = ⟨true, true, 1, 1522, 7758, 3537, true, true, true⟩ ∧
    (verdict { r465 with T := 1571 }).exact = true ∧
    (verdict { r465 with T := 1570 }).exact = false ∧
    (verdict { r465 with T := 1694 }).bridge = true ∧
    (verdict { r465 with T := 1693 }).bridge = false := by decide +kernel
theorem v466 :
    verdict r466 = ⟨true, true, 1, 858, 2743, 1235, true, true, true⟩ ∧
    (verdict { r466 with T := 942 }).exact = true ∧
    (verdict { r466 with T := 941 }).exact = false ∧
    (verdict { r466 with T := 953 }).bridge = true ∧
    (verdict { r466 with T := 952 }).bridge = false := by decide +kernel
theorem v467 :
    verdict r467 = ⟨true, true, 1, 1759, 5987, 2729, true, true, true⟩ ∧
    (verdict { r467 with T := 2114 }).exact = true ∧
    (verdict { r467 with T := 2113 }).exact = false ∧
    (verdict { r467 with T := 2114 }).bridge = true ∧
    (verdict { r467 with T := 2113 }).bridge = false := by decide +kernel
theorem v468 :
    verdict r468 = ⟨true, true, 1, 569, 8217, 2663, true, true, true⟩ ∧
    (verdict { r468 with T := 658 }).exact = true ∧
    (verdict { r468 with T := 657 }).exact = false ∧
    (verdict { r468 with T := 781 }).bridge = true ∧
    (verdict { r468 with T := 780 }).bridge = false := by decide +kernel
theorem v469 :
    verdict r469 = ⟨true, true, 1, 658, 6326, 2047, true, true, true⟩ ∧
    (verdict { r469 with T := 951 }).exact = true ∧
    (verdict { r469 with T := 950 }).exact = false ∧
    (verdict { r469 with T := 951 }).bridge = true ∧
    (verdict { r469 with T := 950 }).bridge = false := by decide +kernel
theorem v470 :
    verdict r470 = ⟨true, true, 1, 503, 4328, 1485, true, true, true⟩ ∧
    (verdict { r470 with T := 575 }).exact = true ∧
    (verdict { r470 with T := 574 }).exact = false ∧
    (verdict { r470 with T := 585 }).bridge = true ∧
    (verdict { r470 with T := 584 }).bridge = false := by decide +kernel
theorem v471 :
    verdict r471 = ⟨true, true, 1, 1103, 9566, 3378, true, true, true⟩ ∧
    (verdict { r471 with T := 1372 }).exact = true ∧
    (verdict { r471 with T := 1371 }).exact = false ∧
    (verdict { r471 with T := 1372 }).bridge = true ∧
    (verdict { r471 with T := 1371 }).bridge = false := by decide +kernel
theorem v472 :
    verdict r472 = ⟨true, true, 1, 581, 3331, 1141, true, true, true⟩ ∧
    (verdict { r472 with T := 837 }).exact = true ∧
    (verdict { r472 with T := 836 }).exact = false ∧
    (verdict { r472 with T := 837 }).bridge = true ∧
    (verdict { r472 with T := 836 }).bridge = false := by decide +kernel
theorem v473 :
    verdict r473 = ⟨true, true, 1, 1274, 7381, 2605, true, true, true⟩ ∧
    (verdict { r473 with T := 1935 }).exact = true ∧
    (verdict { r473 with T := 1934 }).exact = false ∧
    (verdict { r473 with T := 1935 }).bridge = true ∧
    (verdict { r473 with T := 1934 }).bridge = false := by decide +kernel
theorem v474 :
    verdict r474 = ⟨true, true, 1, 704, 6161, 2938, true, true, true⟩ ∧
    (verdict { r474 with T := 580 }).exact = true ∧
    (verdict { r474 with T := 579 }).exact = false ∧
    (verdict { r474 with T := 704 }).bridge = true ∧
    (verdict { r474 with T := 703 }).bridge = false := by decide +kernel
theorem v475 :
    verdict r475 = ⟨true, true, 1, 814, 4738, 2259, true, true, true⟩ ∧
    (verdict { r475 with T := 919 }).exact = true ∧
    (verdict { r475 with T := 918 }).exact = false ∧
    (verdict { r475 with T := 919 }).bridge = true ∧
    (verdict { r475 with T := 918 }).bridge = false := by decide +kernel
theorem v476 :
    verdict r476 = ⟨true, true, 1, 370, 3229, 1577, true, true, true⟩ ∧
    (verdict { r476 with T := 606 }).exact = true ∧
    (verdict { r476 with T := 605 }).exact = false ∧
    (verdict { r476 with T := 606 }).bridge = true ∧
    (verdict { r476 with T := 605 }).bridge = false := by decide +kernel
theorem v477 :
    verdict r477 = ⟨true, true, 1, 753, 7399, 3653, true, true, true⟩ ∧
    (verdict { r477 with T := 1404 }).exact = true ∧
    (verdict { r477 with T := 1403 }).exact = false ∧
    (verdict { r477 with T := 1404 }).bridge = true ∧
    (verdict { r477 with T := 1403 }).bridge = false := by decide +kernel
theorem v478 :
    verdict r478 = ⟨true, true, 1, 427, 2482, 1212, true, true, true⟩ ∧
    (verdict { r478 with T := 844 }).exact = true ∧
    (verdict { r478 with T := 843 }).exact = false ∧
    (verdict { r478 with T := 844 }).bridge = true ∧
    (verdict { r478 with T := 843 }).bridge = false := by decide +kernel
theorem v479 :
    verdict r479 = ⟨true, true, 1, 870, 5709, 2818, true, true, true⟩ ∧
    (verdict { r479 with T := 1918 }).exact = true ∧
    (verdict { r479 with T := 1917 }).exact = false ∧
    (verdict { r479 with T := 1918 }).bridge = true ∧
    (verdict { r479 with T := 1917 }).bridge = false := by decide +kernel
theorem v480 :
    verdict r480 = ⟨true, true, 1, 752, 12210, 2846, true, true, true⟩ ∧
    (verdict { r480 with T := 628 }).exact = true ∧
    (verdict { r480 with T := 627 }).exact = false ∧
    (verdict { r480 with T := 752 }).bridge = true ∧
    (verdict { r480 with T := 751 }).bridge = false := by decide +kernel
theorem v481 :
    verdict r481 = ⟨true, true, 1, 870, 9394, 2189, true, true, true⟩ ∧
    (verdict { r481 with T := 775 }).exact = true ∧
    (verdict { r481 with T := 774 }).exact = false ∧
    (verdict { r481 with T := 870 }).bridge = true ∧
    (verdict { r481 with T := 869 }).bridge = false := by decide +kernel
theorem v482 :
    verdict r482 = ⟨true, true, 1, 623, 6537, 1458, true, true, true⟩ ∧
    (verdict { r482 with T := 589 }).exact = true ∧
    (verdict { r482 with T := 588 }).exact = false ∧
    (verdict { r482 with T := 633 }).bridge = true ∧
    (verdict { r482 with T := 632 }).bridge = false := by decide +kernel
theorem v483 :
    verdict r483 = ⟨true, true, 1, 1261, 14722, 3273, true, true, true⟩ ∧
    (verdict { r483 with T := 1363 }).exact = true ∧
    (verdict { r483 with T := 1362 }).exact = false ∧
    (verdict { r483 with T := 1363 }).bridge = true ∧
    (verdict { r483 with T := 1362 }).bridge = false := by decide +kernel
theorem v484 :
    verdict r484 = ⟨true, true, 1, 720, 5025, 1121, true, true, true⟩ ∧
    (verdict { r484 with T := 861 }).exact = true ∧
    (verdict { r484 with T := 860 }).exact = false ∧
    (verdict { r484 with T := 861 }).bridge = true ∧
    (verdict { r484 with T := 860 }).bridge = false := by decide +kernel
theorem v485 :
    verdict r485 = ⟨true, true, 1, 1457, 11357, 2524, true, true, true⟩ ∧
    (verdict { r485 with T := 1928 }).exact = true ∧
    (verdict { r485 with T := 1927 }).exact = false ∧
    (verdict { r485 with T := 1928 }).bridge = true ∧
    (verdict { r485 with T := 1927 }).bridge = false := by decide +kernel
theorem v486 :
    verdict r486 = ⟨true, true, 1, 552, 5849, 2646, true, true, true⟩ ∧
    (verdict { r486 with T := 428 }).exact = true ∧
    (verdict { r486 with T := 427 }).exact = false ∧
    (verdict { r486 with T := 552 }).bridge = true ∧
    (verdict { r486 with T := 551 }).bridge = false := by decide +kernel
theorem v487 :
    verdict r487 = ⟨true, true, 1, 639, 4499, 2034, true, true, true⟩ ∧
    (verdict { r487 with T := 699 }).exact = true ∧
    (verdict { r487 with T := 698 }).exact = false ∧
    (verdict { r487 with T := 699 }).bridge = true ∧
    (verdict { r487 with T := 698 }).bridge = false := by decide +kernel
theorem v488 :
    verdict r488 = ⟨true, true, 1, 535, 3494, 1459, true, true, true⟩ ∧
    (verdict { r488 with T := 501 }).exact = true ∧
    (verdict { r488 with T := 500 }).exact = false ∧
    (verdict { r488 with T := 540 }).bridge = true ∧
    (verdict { r488 with T := 539 }).bridge = false := by decide +kernel
theorem v489 :
    verdict r489 = ⟨true, true, 1, 1079, 7790, 3288, true, true, true⟩ ∧
    (verdict { r489 with T := 1172 }).exact = true ∧
    (verdict { r489 with T := 1171 }).exact = false ∧
    (verdict { r489 with T := 1172 }).bridge = true ∧
    (verdict { r489 with T := 1171 }).bridge = false := by decide +kernel
theorem v490 :
    verdict r490 = ⟨true, true, 1, 618, 2687, 1121, true, true, true⟩ ∧
    (verdict { r490 with T := 758 }).exact = true ∧
    (verdict { r490 with T := 757 }).exact = false ∧
    (verdict { r490 with T := 758 }).bridge = true ∧
    (verdict { r490 with T := 757 }).bridge = false := by decide +kernel
theorem v491 :
    verdict r491 = ⟨true, true, 1, 1246, 6010, 2536, true, true, true⟩ ∧
    (verdict { r491 with T := 1702 }).exact = true ∧
    (verdict { r491 with T := 1701 }).exact = false ∧
    (verdict { r491 with T := 1702 }).bridge = true ∧
    (verdict { r491 with T := 1701 }).bridge = false := by decide +kernel
theorem v492 :
    verdict r492 = ⟨true, true, 1, 729, 12306, 3177, true, true, true⟩ ∧
    (verdict { r492 with T := 621 }).exact = true ∧
    (verdict { r492 with T := 620 }).exact = false ∧
    (verdict { r492 with T := 739 }).bridge = true ∧
    (verdict { r492 with T := 738 }).bridge = false := by decide +kernel
theorem v493 :
    verdict r493 = ⟨true, true, 1, 843, 9467, 2445, true, true, true⟩ ∧
    (verdict { r493 with T := 1004 }).exact = true ∧
    (verdict { r493 with T := 1003 }).exact = false ∧
    (verdict { r493 with T := 1004 }).bridge = true ∧
    (verdict { r493 with T := 1003 }).bridge = false := by decide +kernel
theorem v494 :
    verdict r494 = ⟨true, true, 1, 744, 7280, 1813, true, true, true⟩ ∧
    (verdict { r494 with T := 584 }).exact = true ∧
    (verdict { r494 with T := 583 }).exact = false ∧
    (verdict { r494 with T := 744 }).bridge = true ∧
    (verdict { r494 with T := 743 }).bridge = false := by decide +kernel
theorem v495 :
    verdict r495 = ⟨true, true, 1, 1372, 16227, 3986, true, true, true⟩ ∧
    (verdict { r495 with T := 1270 }).exact = true ∧
    (verdict { r495 with T := 1269 }).exact = false ∧
    (verdict { r495 with T := 1372 }).bridge = true ∧
    (verdict { r495 with T := 1371 }).bridge = false := by decide +kernel
theorem v496 :
    verdict r496 = ⟨true, true, 1, 860, 5597, 1394, true, true, true⟩ ∧
    (verdict { r496 with T := 815 }).exact = true ∧
    (verdict { r496 with T := 814 }).exact = false ∧
    (verdict { r496 with T := 860 }).bridge = true ∧
    (verdict { r496 with T := 859 }).bridge = false := by decide +kernel
theorem v497 :
    verdict r497 = ⟨true, true, 1, 1585, 12518, 3075, true, true, true⟩ ∧
    (verdict { r497 with T := 1796 }).exact = true ∧
    (verdict { r497 with T := 1795 }).exact = false ∧
    (verdict { r497 with T := 1796 }).bridge = true ∧
    (verdict { r497 with T := 1795 }).bridge = false := by decide +kernel
theorem v498 :
    verdict r498 = ⟨true, true, 1, 711, 6502, 3144, true, true, true⟩ ∧
    (verdict { r498 with T := 632 }).exact = true ∧
    (verdict { r498 with T := 631 }).exact = false ∧
    (verdict { r498 with T := 711 }).bridge = true ∧
    (verdict { r498 with T := 710 }).bridge = false := by decide +kernel
theorem v499 :
    verdict r499 = ⟨true, true, 1, 822, 5004, 2419, true, true, true⟩ ∧
    (verdict { r499 with T := 1000 }).exact = true ∧
    (verdict { r499 with T := 999 }).exact = false ∧
    (verdict { r499 with T := 1000 }).bridge = true ∧
    (verdict { r499 with T := 999 }).bridge = false := by decide +kernel
theorem v500 :
    verdict r500 = ⟨true, true, 1, 382, 3592, 1923, true, true, true⟩ ∧
    (verdict { r500 with T := 616 }).exact = true ∧
    (verdict { r500 with T := 615 }).exact = false ∧
    (verdict { r500 with T := 616 }).bridge = true ∧
    (verdict { r500 with T := 615 }).bridge = false := by decide +kernel
theorem v501 :
    verdict r501 = ⟨true, true, 1, 784, 8171, 4391, true, true, true⟩ ∧
    (verdict { r501 with T := 1476 }).exact = true ∧
    (verdict { r501 with T := 1475 }).exact = false ∧
    (verdict { r501 with T := 1476 }).bridge = true ∧
    (verdict { r501 with T := 1475 }).bridge = false := by decide +kernel
theorem v502 :
    verdict r502 = ⟨true, true, 1, 442, 2761, 1478, true, true, true⟩ ∧
    (verdict { r502 with T := 845 }).exact = true ∧
    (verdict { r502 with T := 844 }).exact = false ∧
    (verdict { r502 with T := 845 }).bridge = true ∧
    (verdict { r502 with T := 844 }).bridge = false := by decide +kernel
theorem v503 :
    verdict r503 = ⟨true, true, 1, 906, 6304, 3386, true, true, true⟩ ∧
    (verdict { r503 with T := 1964 }).exact = true ∧
    (verdict { r503 with T := 1963 }).exact = false ∧
    (verdict { r503 with T := 1964 }).bridge = true ∧
    (verdict { r503 with T := 1963 }).bridge = false := by decide +kernel
theorem v504 :
    verdict r504 = ⟨true, true, 1, 744, 13339, 2838, true, true, true⟩ ∧
    (verdict { r504 with T := 620 }).exact = true ∧
    (verdict { r504 with T := 619 }).exact = false ∧
    (verdict { r504 with T := 744 }).bridge = true ∧
    (verdict { r504 with T := 743 }).bridge = false := by decide +kernel
theorem v505 :
    verdict r505 = ⟨true, true, 1, 860, 10264, 2182, true, true, true⟩ ∧
    (verdict { r505 with T := 772 }).exact = true ∧
    (verdict { r505 with T := 771 }).exact = false ∧
    (verdict { r505 with T := 860 }).bridge = true ∧
    (verdict { r505 with T := 859 }).bridge = false := by decide +kernel
theorem v506 :
    verdict r506 = ⟨true, true, 1, 717, 7507, 1773, true, true, true⟩ ∧
    (verdict { r506 with T := 673 }).exact = true ∧
    (verdict { r506 with T := 672 }).exact = false ∧
    (verdict { r506 with T := 722 }).bridge = true ∧
    (verdict { r506 with T := 721 }).bridge = false := by decide +kernel
theorem v507 :
    verdict r507 = ⟨true, true, 1, 1361, 16620, 3838, true, true, true⟩ ∧
    (verdict { r507 with T := 1343 }).exact = true ∧
    (verdict { r507 with T := 1342 }).exact = false ∧
    (verdict { r507 with T := 1363 }).bridge = true ∧
    (verdict { r507 with T := 1362 }).bridge = false := by decide +kernel
theorem v508 :
    verdict r508 = ⟨true, true, 1, 829, 5776, 1364, true, true, true⟩ ∧
    (verdict { r508 with T := 871 }).exact = true ∧
    (verdict { r508 with T := 870 }).exact = false ∧
    (verdict { r508 with T := 871 }).bridge = true ∧
    (verdict { r508 with T := 870 }).bridge = false := by decide +kernel
theorem v509 :
    verdict r509 = ⟨true, true, 1, 1573, 12822, 2960, true, true, true⟩ ∧
    (verdict { r509 with T := 1949 }).exact = true ∧
    (verdict { r509 with T := 1948 }).exact = false ∧
    (verdict { r509 with T := 1949 }).bridge = true ∧
    (verdict { r509 with T := 1948 }).bridge = false := by decide +kernel
theorem v510 :
    verdict r510 = ⟨true, true, 1, 922, 6657, 2943, true, true, true⟩ ∧
    (verdict { r510 with T := 725 }).exact = true ∧
    (verdict { r510 with T := 724 }).exact = false ∧
    (verdict { r510 with T := 922 }).bridge = true ∧
    (verdict { r510 with T := 921 }).bridge = false := by decide +kernel
theorem v511 :
    verdict r511 = ⟨true, true, 1, 1066, 5123, 2263, true, true, true⟩ ∧
    (verdict { r511 with T := 838 }).exact = true ∧
    (verdict { r511 with T := 837 }).exact = false ∧
    (verdict { r511 with T := 1066 }).bridge = true ∧
    (verdict { r511 with T := 1065 }).bridge = false := by decide +kernel
theorem v512 :
    verdict r512 = ⟨true, true, 1, 669, 3578, 1534, true, true, true⟩ ∧
    (verdict { r512 with T := 583 }).exact = true ∧
    (verdict { r512 with T := 582 }).exact = false ∧
    (verdict { r512 with T := 669 }).bridge = true ∧
    (verdict { r512 with T := 668 }).bridge = false := by decide +kernel
theorem v513 :
    verdict r513 = ⟨true, true, 1, 1425, 7909, 3495, true, true, true⟩ ∧
    (verdict { r513 with T := 1220 }).exact = true ∧
    (verdict { r513 with T := 1219 }).exact = false ∧
    (verdict { r513 with T := 1425 }).bridge = true ∧
    (verdict { r513 with T := 1424 }).bridge = false := by decide +kernel
theorem v514 :
    verdict r514 = ⟨true, true, 1, 772, 2751, 1179, true, true, true⟩ ∧
    (verdict { r514 with T := 673 }).exact = true ∧
    (verdict { r514 with T := 672 }).exact = false ∧
    (verdict { r514 with T := 772 }).bridge = true ∧
    (verdict { r514 with T := 771 }).bridge = false := by decide +kernel
theorem v515 :
    verdict r515 = ⟨true, true, 1, 1646, 6102, 2696, true, true, true⟩ ∧
    (verdict { r515 with T := 1713 }).exact = true ∧
    (verdict { r515 with T := 1712 }).exact = false ∧
    (verdict { r515 with T := 1713 }).bridge = true ∧
    (verdict { r515 with T := 1712 }).bridge = false := by decide +kernel
theorem v516 :
    verdict r516 = ⟨true, true, 1, 1878, 14320, 3972, true, true, true⟩ ∧
    (verdict { r516 with T := 1754 }).exact = true ∧
    (verdict { r516 with T := 1753 }).exact = false ∧
    (verdict { r516 with T := 1878 }).bridge = true ∧
    (verdict { r516 with T := 1877 }).bridge = false := by decide +kernel
theorem v517 :
    verdict r517 = ⟨true, true, 1, 2170, 11036, 3058, true, true, true⟩ ∧
    (verdict { r517 with T := 2026 }).exact = true ∧
    (verdict { r517 with T := 2025 }).exact = false ∧
    (verdict { r517 with T := 2170 }).bridge = true ∧
    (verdict { r517 with T := 2169 }).bridge = false := by decide +kernel
theorem v518 :
    verdict r518 = ⟨true, true, 1, 1106, 7691, 2109, true, true, true⟩ ∧
    (verdict { r518 with T := 1085 }).exact = true ∧
    (verdict { r518 with T := 1084 }).exact = false ∧
    (verdict { r518 with T := 1134 }).bridge = true ∧
    (verdict { r518 with T := 1133 }).bridge = false := by decide +kernel
theorem v519 :
    verdict r519 = ⟨true, true, 1, 2355, 16428, 4674, true, true, true⟩ ∧
    (verdict { r519 with T := 2267 }).exact = true ∧
    (verdict { r519 with T := 2266 }).exact = false ∧
    (verdict { r519 with T := 2380 }).bridge = true ∧
    (verdict { r519 with T := 2379 }).bridge = false := by decide +kernel
theorem v520 :
    verdict r520 = ⟨true, true, 1, 1278, 5925, 1623, true, true, true⟩ ∧
    (verdict { r520 with T := 1253 }).exact = true ∧
    (verdict { r520 with T := 1252 }).exact = false ∧
    (verdict { r520 with T := 1310 }).bridge = true ∧
    (verdict { r520 with T := 1309 }).bridge = false := by decide +kernel
theorem v521 :
    verdict r521 = ⟨true, true, 1, 2721, 12676, 3605, true, true, true⟩ ∧
    (verdict { r521 with T := 2618 }).exact = true ∧
    (verdict { r521 with T := 2617 }).exact = false ∧
    (verdict { r521 with T := 2750 }).bridge = true ∧
    (verdict { r521 with T := 2749 }).bridge = false := by decide +kernel
theorem v522 :
    verdict r522 = ⟨true, true, 1, 905, 12924, 2862, true, true, true⟩ ∧
    (verdict { r522 with T := 644 }).exact = true ∧
    (verdict { r522 with T := 643 }).exact = false ∧
    (verdict { r522 with T := 905 }).bridge = true ∧
    (verdict { r522 with T := 904 }).bridge = false := by decide +kernel
theorem v523 :
    verdict r523 = ⟨true, true, 1, 1046, 9950, 2201, true, true, true⟩ ∧
    (verdict { r523 with T := 781 }).exact = true ∧
    (verdict { r523 with T := 780 }).exact = false ∧
    (verdict { r523 with T := 1046 }).bridge = true ∧
    (verdict { r523 with T := 1045 }).bridge = false := by decide +kernel
theorem v524 :
    verdict r524 = ⟨true, true, 1, 655, 7148, 1552, true, true, true⟩ ∧
    (verdict { r524 with T := 601 }).exact = true ∧
    (verdict { r524 with T := 600 }).exact = false ∧
    (verdict { r524 with T := 655 }).bridge = true ∧
    (verdict { r524 with T := 654 }).bridge = false := by decide +kernel
theorem v525 :
    verdict r525 = ⟨true, true, 1, 1365, 15272, 3471, true, true, true⟩ ∧
    (verdict { r525 with T := 1395 }).exact = true ∧
    (verdict { r525 with T := 1394 }).exact = false ∧
    (verdict { r525 with T := 1395 }).bridge = true ∧
    (verdict { r525 with T := 1394 }).bridge = false := by decide +kernel
theorem v526 :
    verdict r526 = ⟨true, true, 1, 756, 5504, 1192, true, true, true⟩ ∧
    (verdict { r526 with T := 868 }).exact = true ∧
    (verdict { r526 with T := 867 }).exact = false ∧
    (verdict { r526 with T := 868 }).bridge = true ∧
    (verdict { r526 with T := 867 }).bridge = false := by decide +kernel
theorem v527 :
    verdict r527 = ⟨true, true, 1, 1577, 11785, 2678, true, true, true⟩ ∧
    (verdict { r527 with T := 1946 }).exact = true ∧
    (verdict { r527 with T := 1945 }).exact = false ∧
    (verdict { r527 with T := 1946 }).bridge = true ∧
    (verdict { r527 with T := 1945 }).bridge = false := by decide +kernel
theorem v528 :
    verdict r528 = ⟨true, true, 1, 704, 12170, 2658, true, true, true⟩ ∧
    (verdict { r528 with T := 440 }).exact = true ∧
    (verdict { r528 with T := 439 }).exact = false ∧
    (verdict { r528 with T := 704 }).bridge = true ∧
    (verdict { r528 with T := 703 }).bridge = false := by decide +kernel
theorem v529 :
    verdict r529 = ⟨true, true, 1, 814, 9372, 2043, true, true, true⟩ ∧
    (verdict { r529 with T := 757 }).exact = true ∧
    (verdict { r529 with T := 756 }).exact = false ∧
    (verdict { r529 with T := 814 }).bridge = true ∧
    (verdict { r529 with T := 813 }).bridge = false := by decide +kernel
theorem v530 :
    verdict r530 = ⟨true, true, 1, 520, 6805, 1443, true, true, true⟩ ∧
    (verdict { r530 with T := 511 }).exact = true ∧
    (verdict { r530 with T := 510 }).exact = false ∧
    (verdict { r530 with T := 525 }).bridge = true ∧
    (verdict { r530 with T := 524 }).bridge = false := by decide +kernel
theorem v531 :
    verdict r531 = ⟨true, true, 1, 1154, 14744, 3374, true, true, true⟩ ∧
    (verdict { r531 with T := 1197 }).exact = true ∧
    (verdict { r531 with T := 1196 }).exact = false ∧
    (verdict { r531 with T := 1197 }).bridge = true ∧
    (verdict { r531 with T := 1196 }).bridge = false := by decide +kernel
theorem v532 :
    verdict r532 = ⟨true, true, 1, 600, 5239, 1108, true, true, true⟩ ∧
    (verdict { r532 with T := 759 }).exact = true ∧
    (verdict { r532 with T := 758 }).exact = false ∧
    (verdict { r532 with T := 759 }).bridge = true ∧
    (verdict { r532 with T := 758 }).bridge = false := by decide +kernel
theorem v533 :
    verdict r533 = ⟨true, true, 1, 1333, 11377, 2602, true, true, true⟩ ∧
    (verdict { r533 with T := 1749 }).exact = true ∧
    (verdict { r533 with T := 1748 }).exact = false ∧
    (verdict { r533 with T := 1749 }).bridge = true ∧
    (verdict { r533 with T := 1748 }).bridge = false := by decide +kernel
theorem v534 :
    verdict r534 = ⟨true, true, 1, 912, 8858, 2865, true, true, true⟩ ∧
    (verdict { r534 with T := 838 }).exact = true ∧
    (verdict { r534 with T := 837 }).exact = false ∧
    (verdict { r534 with T := 983 }).bridge = true ∧
    (verdict { r534 with T := 982 }).bridge = false := by decide +kernel
theorem v535 :
    verdict r535 = ⟨true, true, 1, 1054, 6822, 2203, true, true, true⟩ ∧
    (verdict { r535 with T := 1029 }).exact = true ∧
    (verdict { r535 with T := 1028 }).exact = false ∧
    (verdict { r535 with T := 1137 }).bridge = true ∧
    (verdict { r535 with T := 1136 }).bridge = false := by decide +kernel
theorem v536 :
    verdict r536 = ⟨true, true, 1, 653, 5502, 1766, true, true, true⟩ ∧
    (verdict { r536 with T := 639 }).exact = true ∧
    (verdict { r536 with T := 638 }).exact = false ∧
    (verdict { r536 with T := 684 }).bridge = true ∧
    (verdict { r536 with T := 683 }).bridge = false := by decide +kernel
theorem v537 :
    verdict r537 = ⟨true, true, 1, 1380, 11775, 4006, true, true, true⟩ ∧
    (verdict { r537 with T := 1384 }).exact = true ∧
    (verdict { r537 with T := 1383 }).exact = false ∧
    (verdict { r537 with T := 1465 }).bridge = true ∧
    (verdict { r537 with T := 1464 }).bridge = false := by decide +kernel
theorem v538 :
    verdict r538 = ⟨true, true, 1, 754, 4234, 1358, true, true, true⟩ ∧
    (verdict { r538 with T := 848 }).exact = true ∧
    (verdict { r538 with T := 847 }).exact = false ∧
    (verdict { r538 with T := 848 }).bridge = true ∧
    (verdict { r538 with T := 847 }).bridge = false := by decide +kernel
theorem v539 :
    verdict r539 = ⟨true, true, 1, 1595, 9086, 3092, true, true, true⟩ ∧
    (verdict { r539 with T := 2013 }).exact = true ∧
    (verdict { r539 with T := 2012 }).exact = false ∧
    (verdict { r539 with T := 2013 }).bridge = true ∧
    (verdict { r539 with T := 2012 }).bridge = false := by decide +kernel
theorem v540 :
    verdict r540 = ⟨true, true, 1, 702, 7780, 2656, true, true, true⟩ ∧
    (verdict { r540 with T := 438 }).exact = true ∧
    (verdict { r540 with T := 437 }).exact = false ∧
    (verdict { r540 with T := 702 }).bridge = true ∧
    (verdict { r540 with T := 701 }).bridge = false := by decide +kernel
theorem v541 :
    verdict r541 = ⟨true, true, 1, 812, 5990, 2042, true, true, true⟩ ∧
    (verdict { r541 with T := 756 }).exact = true ∧
    (verdict { r541 with T := 755 }).exact = false ∧
    (verdict { r541 with T := 812 }).bridge = true ∧
    (verdict { r541 with T := 811 }).bridge = false := by decide +kernel
theorem v542 :
    verdict r542 = ⟨true, true, 1, 632, 4622, 1457, true, true, true⟩ ∧
    (verdict { r542 with T := 501 }).exact = true ∧
    (verdict { r542 with T := 500 }).exact = false ∧
    (verdict { r542 with T := 637 }).bridge = true ∧
    (verdict { r542 with T := 636 }).bridge = false := by decide +kernel
theorem v543 :
    verdict r543 = ⟨true, true, 1, 1395, 10245, 3344, true, true, true⟩ ∧
    (verdict { r543 with T := 1116 }).exact = true ∧
    (verdict { r543 with T := 1115 }).exact = false ∧
    (verdict { r543 with T := 1396 }).bridge = true ∧
    (verdict { r543 with T := 1395 }).bridge = false := by decide +kernel
theorem v544 :
    verdict r544 = ⟨true, true, 1, 730, 3554, 1119, true, true, true⟩ ∧
    (verdict { r544 with T := 819 }).exact = true ∧
    (verdict { r544 with T := 818 }).exact = false ∧
    (verdict { r544 with T := 819 }).bridge = true ∧
    (verdict { r544 with T := 818 }).bridge = false := by decide +kernel
theorem v545 :
    verdict r545 = ⟨true, true, 1, 1611, 7903, 2579, true, true, true⟩ ∧
    (verdict { r545 with T := 1899 }).exact = true ∧
    (verdict { r545 with T := 1898 }).exact = false ∧
    (verdict { r545 with T := 1899 }).bridge = true ∧
    (verdict { r545 with T := 1898 }).bridge = false := by decide +kernel
theorem v546 :
    verdict r546 = ⟨true, true, 1, 553, 6722, 3001, true, true, true⟩ ∧
    (verdict { r546 with T := 621 }).exact = true ∧
    (verdict { r546 with T := 620 }).exact = false ∧
    (verdict { r546 with T := 621 }).bridge = true ∧
    (verdict { r546 with T := 620 }).bridge = false := by decide +kernel
theorem v547 :
    verdict r547 = ⟨true, true, 1, 640, 5174, 2309, true, true, true⟩ ∧
    (verdict { r547 with T := 937 }).exact = true ∧
    (verdict { r547 with T := 936 }).exact = false ∧
    (verdict { r547 with T := 937 }).bridge = true ∧
    (verdict { r547 with T := 936 }).bridge = false := by decide +kernel
theorem v548 :
    verdict r548 = ⟨true, true, 1, 439, 3738, 1424, true, true, true⟩ ∧
    (verdict { r548 with T := 511 }).exact = true ∧
    (verdict { r548 with T := 510 }).exact = false ∧
    (verdict { r548 with T := 511 }).bridge = true ∧
    (verdict { r548 with T := 510 }).bridge = false := by decide +kernel
theorem v549 :
    verdict r549 = ⟨true, true, 1, 972, 8357, 3354, true, true, true⟩ ∧
    (verdict { r549 with T := 1232 }).exact = true ∧
    (verdict { r549 with T := 1231 }).exact = false ∧
    (verdict { r549 with T := 1232 }).bridge = true ∧
    (verdict { r549 with T := 1231 }).bridge = false := by decide +kernel
theorem v550 :
    verdict r550 = ⟨true, true, 1, 507, 2876, 1094, true, true, true⟩ ∧
    (verdict { r550 with T := 679 }).exact = true ∧
    (verdict { r550 with T := 678 }).exact = false ∧
    (verdict { r550 with T := 679 }).bridge = true ∧
    (verdict { r550 with T := 678 }).bridge = false := by decide +kernel
theorem v551 :
    verdict r551 = ⟨true, true, 1, 1123, 6450, 2587, true, true, true⟩ ∧
    (verdict { r551 with T := 1617 }).exact = true ∧
    (verdict { r551 with T := 1616 }).exact = false ∧
    (verdict { r551 with T := 1617 }).bridge = true ∧
    (verdict { r551 with T := 1616 }).bridge = false := by decide +kernel
theorem v552 :
    verdict r552 = ⟨true, true, 1, 772, 8649, 2866, true, true, true⟩ ∧
    (verdict { r552 with T := 648 }).exact = true ∧
    (verdict { r552 with T := 647 }).exact = false ∧
    (verdict { r552 with T := 772 }).bridge = true ∧
    (verdict { r552 with T := 771 }).bridge = false := by decide +kernel
theorem v553 :
    verdict r553 = ⟨true, true, 1, 893, 6660, 2204, true, true, true⟩ ∧
    (verdict { r553 with T := 783 }).exact = true ∧
    (verdict { r553 with T := 782 }).exact = false ∧
    (verdict { r553 with T := 893 }).bridge = true ∧
    (verdict { r553 with T := 892 }).bridge = false := by decide +kernel
theorem v554 :
    verdict r554 = ⟨true, true, 1, 689, 5593, 1726, true, true, true⟩ ∧
    (verdict { r554 with T := 645 }).exact = true ∧
    (verdict { r554 with T := 644 }).exact = false ∧
    (verdict { r554 with T := 693 }).bridge = true ∧
    (verdict { r554 with T := 692 }).bridge = false := by decide +kernel
theorem v555 :
    verdict r555 = ⟨true, true, 1, 1469, 12009, 3901, true, true, true⟩ ∧
    (verdict { r555 with T := 1358 }).exact = true ∧
    (verdict { r555 with T := 1357 }).exact = false ∧
    (verdict { r555 with T := 1471 }).bridge = true ∧
    (verdict { r555 with T := 1470 }).bridge = false := by decide +kernel
theorem v556 :
    verdict r556 = ⟨true, true, 1, 796, 4305, 1327, true, true, true⟩ ∧
    (verdict { r556 with T := 829 }).exact = true ∧
    (verdict { r556 with T := 828 }).exact = false ∧
    (verdict { r556 with T := 829 }).bridge = true ∧
    (verdict { r556 with T := 828 }).bridge = false := by decide +kernel
theorem v557 :
    verdict r557 = ⟨true, true, 1, 1697, 9265, 3009, true, true, true⟩ ∧
    (verdict { r557 with T := 1930 }).exact = true ∧
    (verdict { r557 with T := 1929 }).exact = false ∧
    (verdict { r557 with T := 1930 }).bridge = true ∧
    (verdict { r557 with T := 1929 }).bridge = false := by decide +kernel
theorem v558 :
    verdict r558 = ⟨true, true, 1, 1938, 9532, 3819, true, true, true⟩ ∧
    (verdict { r558 with T := 1601 }).exact = true ∧
    (verdict { r558 with T := 1600 }).exact = false ∧
    (verdict { r558 with T := 1938 }).bridge = true ∧
    (verdict { r558 with T := 1937 }).bridge = false := by decide +kernel
theorem v559 :
    verdict r559 = ⟨true, true, 1, 2240, 7343, 2940, true, true, true⟩ ∧
    (verdict { r559 with T := 1849 }).exact = true ∧
    (verdict { r559 with T := 1848 }).exact = false ∧
    (verdict { r559 with T := 2240 }).bridge = true ∧
    (verdict { r559 with T := 2239 }).bridge = false := by decide +kernel
theorem v560 :
    verdict r560 = ⟨true, true, 1, 1516, 5984, 2388, true, true, true⟩ ∧
    (verdict { r560 with T := 1358 }).exact = true ∧
    (verdict { r560 with T := 1357 }).exact = false ∧
    (verdict { r560 with T := 1516 }).bridge = true ∧
    (verdict { r560 with T := 1515 }).bridge = false := by decide +kernel
theorem v561 :
    verdict r561 = ⟨true, true, 1, 2790, 11868, 4866, true, true, true⟩ ∧
    (verdict { r561 with T := 2436 }).exact = true ∧
    (verdict { r561 with T := 2435 }).exact = false ∧
    (verdict { r561 with T := 2790 }).bridge = true ∧
    (verdict { r561 with T := 2789 }).bridge = false := by decide +kernel
theorem v562 :
    verdict r562 = ⟨true, true, 1, 1751, 4609, 1838, true, true, true⟩ ∧
    (verdict { r562 with T := 1568 }).exact = true ∧
    (verdict { r562 with T := 1567 }).exact = false ∧
    (verdict { r562 with T := 1751 }).bridge = true ∧
    (verdict { r562 with T := 1750 }).bridge = false := by decide +kernel
theorem v563 :
    verdict r563 = ⟨true, true, 1, 3223, 9158, 3754, true, true, true⟩ ∧
    (verdict { r563 with T := 2827 }).exact = true ∧
    (verdict { r563 with T := 2826 }).exact = false ∧
    (verdict { r563 with T := 3223 }).bridge = true ∧
    (verdict { r563 with T := 3222 }).bridge = false := by decide +kernel
theorem v564 :
    verdict r564 = ⟨true, true, 1, 1266, 7304, 3360, true, true, true⟩ ∧
    (verdict { r564 with T := 1142 }).exact = true ∧
    (verdict { r564 with T := 1141 }).exact = false ∧
    (verdict { r564 with T := 1478 }).bridge = true ∧
    (verdict { r564 with T := 1477 }).bridge = false := by decide +kernel
theorem v565 :
    verdict r565 = ⟨true, true, 1, 1463, 5623, 2585, true, true, true⟩ ∧
    (verdict { r565 with T := 1457 }).exact = true ∧
    (verdict { r565 with T := 1456 }).exact = false ∧
    (verdict { r565 with T := 1708 }).bridge = true ∧
    (verdict { r565 with T := 1707 }).bridge = false := by decide +kernel
theorem v566 :
    verdict r566 = ⟨true, true, 1, 1052, 4259, 1901, true, true, true⟩ ∧
    (verdict { r566 with T := 1076 }).exact = true ∧
    (verdict { r566 with T := 1075 }).exact = false ∧
    (verdict { r566 with T := 1146 }).bridge = true ∧
    (verdict { r566 with T := 1145 }).bridge = false := by decide +kernel
theorem v567 :
    verdict r567 = ⟨true, true, 1, 1888, 8579, 3877, true, true, true⟩ ∧
    (verdict { r567 with T := 1542 }).exact = true ∧
    (verdict { r567 with T := 1541 }).exact = false ∧
    (verdict { r567 with T := 2114 }).bridge = true ∧
    (verdict { r567 with T := 2113 }).bridge = false := by decide +kernel
theorem v568 :
    verdict r568 = ⟨true, true, 1, 1215, 3278, 1462, true, true, true⟩ ∧
    (verdict { r568 with T := 1243 }).exact = true ∧
    (verdict { r568 with T := 1242 }).exact = false ∧
    (verdict { r568 with T := 1324 }).bridge = true ∧
    (verdict { r568 with T := 1323 }).bridge = false := by decide +kernel
theorem v569 :
    verdict r569 = ⟨true, true, 1, 2181, 6620, 2991, true, true, true⟩ ∧
    (verdict { r569 with T := 2275 }).exact = true ∧
    (verdict { r569 with T := 2274 }).exact = false ∧
    (verdict { r569 with T := 2442 }).bridge = true ∧
    (verdict { r569 with T := 2441 }).bridge = false := by decide +kernel
theorem v570 :
    verdict r570 = ⟨true, true, 1, 898, 5896, 2839, true, true, true⟩ ∧
    (verdict { r570 with T := 621 }).exact = true ∧
    (verdict { r570 with T := 620 }).exact = false ∧
    (verdict { r570 with T := 1110 }).bridge = true ∧
    (verdict { r570 with T := 1109 }).bridge = false := by decide +kernel
theorem v571 :
    verdict r571 = ⟨true, true, 1, 1038, 4537, 2183, true, true, true⟩ ∧
    (verdict { r571 with T := 1140 }).exact = true ∧
    (verdict { r571 with T := 1139 }).exact = false ∧
    (verdict { r571 with T := 1283 }).bridge = true ∧
    (verdict { r571 with T := 1282 }).bridge = false := by decide +kernel
theorem v572 :
    verdict r572 = ⟨true, true, 1, 838, 3567, 1588, true, true, true⟩ ∧
    (verdict { r572 with T := 599 }).exact = true ∧
    (verdict { r572 with T := 598 }).exact = false ∧
    (verdict { r572 with T := 930 }).bridge = true ∧
    (verdict { r572 with T := 929 }).bridge = false := by decide +kernel
theorem v573 :
    verdict r573 = ⟨true, true, 1, 1483, 7367, 3318, true, true, true⟩ ∧
    (verdict { r573 with T := 1550 }).exact = true ∧
    (verdict { r573 with T := 1549 }).exact = false ∧
    (verdict { r573 with T := 1703 }).bridge = true ∧
    (verdict { r573 with T := 1702 }).bridge = false := by decide +kernel
theorem v574 :
    verdict r574 = ⟨true, true, 1, 968, 2746, 1221, true, true, true⟩ ∧
    (verdict { r574 with T := 1007 }).exact = true ∧
    (verdict { r574 with T := 1006 }).exact = false ∧
    (verdict { r574 with T := 1074 }).bridge = true ∧
    (verdict { r574 with T := 1073 }).bridge = false := by decide +kernel
theorem v575 :
    verdict r575 = ⟨true, true, 1, 1713, 5685, 2559, true, true, true⟩ ∧
    (verdict { r575 with T := 2095 }).exact = true ∧
    (verdict { r575 with T := 2094 }).exact = false ∧
    (verdict { r575 with T := 2095 }).bridge = true ∧
    (verdict { r575 with T := 2094 }).bridge = false := by decide +kernel
theorem v576 :
    verdict r576 = ⟨true, true, 1, 1496, 14204, 3730, true, true, true⟩ ∧
    (verdict { r576 with T := 1372 }).exact = true ∧
    (verdict { r576 with T := 1371 }).exact = false ∧
    (verdict { r576 with T := 1496 }).bridge = true ∧
    (verdict { r576 with T := 1495 }).bridge = false := by decide +kernel
theorem v577 :
    verdict r577 = ⟨true, true, 1, 1729, 10942, 2871, true, true, true⟩ ∧
    (verdict { r577 with T := 1585 }).exact = true ∧
    (verdict { r577 with T := 1584 }).exact = false ∧
    (verdict { r577 with T := 1729 }).bridge = true ∧
    (verdict { r577 with T := 1728 }).bridge = false := by decide +kernel
theorem v578 :
    verdict r578 = ⟨true, true, 1, 869, 7411, 2105, true, true, true⟩ ∧
    (verdict { r578 with T := 986 }).exact = true ∧
    (verdict { r578 with T := 985 }).exact = false ∧
    (verdict { r578 with T := 1044 }).bridge = true ∧
    (verdict { r578 with T := 1043 }).bridge = false := by decide +kernel
theorem v579 :
    verdict r579 = ⟨true, true, 1, 1656, 16054, 4587, true, true, true⟩ ∧
    (verdict { r579 with T := 1938 }).exact = true ∧
    (verdict { r579 with T := 1937 }).exact = false ∧
    (verdict { r579 with T := 2061 }).bridge = true ∧
    (verdict { r579 with T := 2060 }).bridge = false := by decide +kernel
theorem v580 :
    verdict r580 = ⟨true, true, 1, 1004, 5708, 1619, true, true, true⟩ ∧
    (verdict { r580 with T := 1139 }).exact = true ∧
    (verdict { r580 with T := 1138 }).exact = false ∧
    (verdict { r580 with T := 1206 }).bridge = true ∧
    (verdict { r580 with T := 1205 }).bridge = false := by decide +kernel
theorem v581 :
    verdict r581 = ⟨true, true, 1, 1914, 12391, 3540, true, true, true⟩ ∧
    (verdict { r581 with T := 2448 }).exact = true ∧
    (verdict { r581 with T := 2447 }).exact = false ∧
    (verdict { r581 with T := 2448 }).bridge = true ∧
    (verdict { r581 with T := 2447 }).bridge = false := by decide +kernel
theorem v582 :
    verdict r582 = ⟨true, true, 1, 713, 6642, 2807, true, true, true⟩ ∧
    (verdict { r582 with T := 589 }).exact = true ∧
    (verdict { r582 with T := 588 }).exact = false ∧
    (verdict { r582 with T := 713 }).bridge = true ∧
    (verdict { r582 with T := 712 }).bridge = false := by decide +kernel
theorem v583 :
    verdict r583 = ⟨true, true, 1, 825, 5111, 2158, true, true, true⟩ ∧
    (verdict { r583 with T := 761 }).exact = true ∧
    (verdict { r583 with T := 760 }).exact = false ∧
    (verdict { r583 with T := 825 }).bridge = true ∧
    (verdict { r583 with T := 824 }).bridge = false := by decide +kernel
theorem v584 :
    verdict r584 = ⟨true, true, 1, 535, 3470, 1424, true, true, true⟩ ∧
    (verdict { r584 with T := 574 }).exact = true ∧
    (verdict { r584 with T := 573 }).exact = false ∧
    (verdict { r584 with T := 617 }).bridge = true ∧
    (verdict { r584 with T := 616 }).bridge = false := by decide +kernel
theorem v585 :
    verdict r585 = ⟨true, true, 1, 1078, 7609, 3158, true, true, true⟩ ∧
    (verdict { r585 with T := 1337 }).exact = true ∧
    (verdict { r585 with T := 1336 }).exact = false ∧
    (verdict { r585 with T := 1337 }).bridge = true ∧
    (verdict { r585 with T := 1336 }).bridge = false := by decide +kernel
theorem v586 :
    verdict r586 = ⟨true, true, 1, 619, 2669, 1094, true, true, true⟩ ∧
    (verdict { r586 with T := 842 }).exact = true ∧
    (verdict { r586 with T := 841 }).exact = false ∧
    (verdict { r586 with T := 842 }).bridge = true ∧
    (verdict { r586 with T := 841 }).bridge = false := by decide +kernel
theorem v587 :
    verdict r587 = ⟨true, true, 1, 1246, 5873, 2437, true, true, true⟩ ∧
    (verdict { r587 with T := 1894 }).exact = true ∧
    (verdict { r587 with T := 1893 }).exact = false ∧
    (verdict { r587 with T := 1894 }).bridge = true ∧
    (verdict { r587 with T := 1893 }).bridge = false := by decide +kernel
theorem v588 :
    verdict r588 = ⟨true, true, 1, 1706, 12454, 3800, true, true, true⟩ ∧
    (verdict { r588 with T := 1582 }).exact = true ∧
    (verdict { r588 with T := 1581 }).exact = false ∧
    (verdict { r588 with T := 1706 }).bridge = true ∧
    (verdict { r588 with T := 1705 }).bridge = false := by decide +kernel
theorem v589 :
    verdict r589 = ⟨true, true, 1, 1972, 9590, 2925, true, true, true⟩ ∧
    (verdict { r589 with T := 1828 }).exact = true ∧
    (verdict { r589 with T := 1827 }).exact = false ∧
    (verdict { r589 with T := 1972 }).bridge = true ∧
    (verdict { r589 with T := 1971 }).bridge = false := by decide +kernel
theorem v590 :
    verdict r590 = ⟨true, true, 1, 1382, 7183, 2196, true, true, true⟩ ∧
    (verdict { r590 with T := 1247 }).exact = true ∧
    (verdict { r590 with T := 1246 }).exact = false ∧
    (verdict { r590 with T := 1464 }).bridge = true ∧
    (verdict { r590 with T := 1463 }).bridge = false := by decide +kernel
theorem v591 :
    verdict r591 = ⟨true, true, 1, 2447, 14999, 4362, true, true, true⟩ ∧
    (verdict { r591 with T := 2495 }).exact = true ∧
    (verdict { r591 with T := 2494 }).exact = false ∧
    (verdict { r591 with T := 2619 }).bridge = true ∧
    (verdict { r591 with T := 2618 }).bridge = false := by decide +kernel
theorem v592 :
    verdict r592 = ⟨true, true, 1, 1596, 5532, 1689, true, true, true⟩ ∧
    (verdict { r592 with T := 1440 }).exact = true ∧
    (verdict { r592 with T := 1439 }).exact = false ∧
    (verdict { r592 with T := 1691 }).bridge = true ∧
    (verdict { r592 with T := 1690 }).bridge = false := by decide +kernel
theorem v593 :
    verdict r593 = ⟨true, true, 1, 2827, 11574, 3366, true, true, true⟩ ∧
    (verdict { r593 with T := 2883 }).exact = true ∧
    (verdict { r593 with T := 2882 }).exact = false ∧
    (verdict { r593 with T := 3026 }).bridge = true ∧
    (verdict { r593 with T := 3025 }).bridge = false := by decide +kernel
theorem v594 :
    verdict r594 = ⟨true, true, 1, 1084, 9207, 3178, true, true, true⟩ ∧
    (verdict { r594 with T := 960 }).exact = true ∧
    (verdict { r594 with T := 959 }).exact = false ∧
    (verdict { r594 with T := 1084 }).bridge = true ∧
    (verdict { r594 with T := 1083 }).bridge = false := by decide +kernel
theorem v595 :
    verdict r595 = ⟨true, true, 1, 1253, 7092, 2445, true, true, true⟩ ∧
    (verdict { r595 with T := 1109 }).exact = true ∧
    (verdict { r595 with T := 1108 }).exact = false ∧
    (verdict { r595 with T := 1253 }).bridge = true ∧
    (verdict { r595 with T := 1252 }).bridge = false := by decide +kernel
theorem v596 :
    verdict r596 = ⟨true, true, 1, 724, 4909, 1750, true, true, true⟩ ∧
    (verdict { r596 with T := 750 }).exact = true ∧
    (verdict { r596 with T := 749 }).exact = false ∧
    (verdict { r596 with T := 805 }).bridge = true ∧
    (verdict { r596 with T := 804 }).bridge = false := by decide +kernel
theorem v597 :
    verdict r597 = ⟨true, true, 1, 1472, 10539, 3906, true, true, true⟩ ∧
    (verdict { r597 with T := 1518 }).exact = true ∧
    (verdict { r597 with T := 1517 }).exact = false ∧
    (verdict { r597 with T := 1640 }).bridge = true ∧
    (verdict { r597 with T := 1639 }).bridge = false := by decide +kernel
theorem v598 :
    verdict r598 = ⟨true, true, 1, 836, 3780, 1346, true, true, true⟩ ∧
    (verdict { r598 with T := 887 }).exact = true ∧
    (verdict { r598 with T := 886 }).exact = false ∧
    (verdict { r598 with T := 930 }).bridge = true ∧
    (verdict { r598 with T := 929 }).bridge = false := by decide +kernel
theorem v599 :
    verdict r599 = ⟨true, true, 1, 1700, 8131, 3013, true, true, true⟩ ∧
    (verdict { r599 with T := 1983 }).exact = true ∧
    (verdict { r599 with T := 1982 }).exact = false ∧
    (verdict { r599 with T := 1983 }).bridge = true ∧
    (verdict { r599 with T := 1982 }).bridge = false := by decide +kernel

end Formal.Timing.ChainSettleExe.GcdD
