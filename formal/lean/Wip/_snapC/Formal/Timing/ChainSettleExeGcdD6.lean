import Formal.Timing.ChainSettleExeGcdDData6

/-! C-10o2 GENERATED: kernel-decided verdicts of chunk 6 (see ChainSettleExe.verdict).
Per row: `verdict` at chainck's late side `T`; exact PASS at `T*` and FAIL at `T* - 1`
(margin_exact = T - T*); bridge PASS at `Tb*` and FAIL at `Tb* - 1`. -/

namespace Formal.Timing.ChainSettleExe.GcdD
open Formal.Timing Formal.Timing.ChainSettleExe

theorem v900 :
    verdict r900 = ⟨true, true, 1, 757, 6968, 2851, true, true, true⟩ ∧
    (verdict { r900 with T := 633 }).exact = true ∧
    (verdict { r900 with T := 632 }).exact = false ∧
    (verdict { r900 with T := 757 }).bridge = true ∧
    (verdict { r900 with T := 756 }).bridge = false := by decide +kernel
theorem v901 :
    verdict r901 = ⟨true, true, 1, 875, 5362, 2192, true, true, true⟩ ∧
    (verdict { r901 with T := 777 }).exact = true ∧
    (verdict { r901 with T := 776 }).exact = false ∧
    (verdict { r901 with T := 875 }).bridge = true ∧
    (verdict { r901 with T := 874 }).bridge = false := by decide +kernel
theorem v902 :
    verdict r902 = ⟨true, true, 1, 547, 3590, 1466, true, true, true⟩ ∧
    (verdict { r902 with T := 589 }).exact = true ∧
    (verdict { r902 with T := 588 }).exact = false ∧
    (verdict { r902 with T := 636 }).bridge = true ∧
    (verdict { r902 with T := 635 }).bridge = false := by decide +kernel
theorem v903 :
    verdict r903 = ⟨true, true, 1, 1090, 7959, 3307, true, true, true⟩ ∧
    (verdict { r903 with T := 1363 }).exact = true ∧
    (verdict { r903 with T := 1362 }).exact = false ∧
    (verdict { r903 with T := 1363 }).bridge = true ∧
    (verdict { r903 with T := 1362 }).bridge = false := by decide +kernel
theorem v904 :
    verdict r904 = ⟨true, true, 1, 631, 2762, 1127, true, true, true⟩ ∧
    (verdict { r904 with T := 862 }).exact = true ∧
    (verdict { r904 with T := 861 }).exact = false ∧
    (verdict { r904 with T := 862 }).bridge = true ∧
    (verdict { r904 with T := 861 }).bridge = false := by decide +kernel
theorem v905 :
    verdict r905 = ⟨true, true, 1, 1259, 6140, 2551, true, true, true⟩ ∧
    (verdict { r905 with T := 1926 }).exact = true ∧
    (verdict { r905 with T := 1925 }).exact = false ∧
    (verdict { r905 with T := 1926 }).bridge = true ∧
    (verdict { r905 with T := 1925 }).bridge = false := by decide +kernel
theorem v906 :
    verdict r906 = ⟨true, true, 1, 903, 7191, 3146, true, true, true⟩ ∧
    (verdict { r906 with T := 779 }).exact = true ∧
    (verdict { r906 with T := 778 }).exact = false ∧
    (verdict { r906 with T := 903 }).bridge = true ∧
    (verdict { r906 with T := 902 }).bridge = false := by decide +kernel
theorem v907 :
    verdict r907 = ⟨true, true, 1, 1044, 5534, 2420, true, true, true⟩ ∧
    (verdict { r907 with T := 1005 }).exact = true ∧
    (verdict { r907 with T := 1004 }).exact = false ∧
    (verdict { r907 with T := 1044 }).bridge = true ∧
    (verdict { r907 with T := 1043 }).bridge = false := by decide +kernel
theorem v908 :
    verdict r908 = ⟨true, true, 1, 516, 3784, 1846, true, true, true⟩ ∧
    (verdict { r908 with T := 643 }).exact = true ∧
    (verdict { r908 with T := 642 }).exact = false ∧
    (verdict { r908 with T := 698 }).bridge = true ∧
    (verdict { r908 with T := 697 }).bridge = false := by decide +kernel
theorem v909 :
    verdict r909 = ⟨true, true, 1, 1017, 8353, 4101, true, true, true⟩ ∧
    (verdict { r909 with T := 1436 }).exact = true ∧
    (verdict { r909 with T := 1435 }).exact = false ∧
    (verdict { r909 with T := 1440 }).bridge = true ∧
    (verdict { r909 with T := 1439 }).bridge = false := by decide +kernel
theorem v910 :
    verdict r910 = ⟨true, true, 1, 596, 2913, 1421, true, true, true⟩ ∧
    (verdict { r910 with T := 908 }).exact = true ∧
    (verdict { r910 with T := 907 }).exact = false ∧
    (verdict { r910 with T := 908 }).bridge = true ∧
    (verdict { r910 with T := 907 }).bridge = false := by decide +kernel
theorem v911 :
    verdict r911 = ⟨true, true, 1, 1175, 6445, 3164, true, true, true⟩ ∧
    (verdict { r911 with T := 2044 }).exact = true ∧
    (verdict { r911 with T := 2043 }).exact = false ∧
    (verdict { r911 with T := 2044 }).bridge = true ∧
    (verdict { r911 with T := 2043 }).bridge = false := by decide +kernel
theorem v912 :
    verdict r912 = ⟨true, true, 1, 1269, 9673, 3150, true, true, true⟩ ∧
    (verdict { r912 with T := 932 }).exact = true ∧
    (verdict { r912 with T := 931 }).exact = false ∧
    (verdict { r912 with T := 1269 }).bridge = true ∧
    (verdict { r912 with T := 1268 }).bridge = false := by decide +kernel
theorem v913 :
    verdict r913 = ⟨true, true, 1, 1467, 7450, 2423, true, true, true⟩ ∧
    (verdict { r913 with T := 1077 }).exact = true ∧
    (verdict { r913 with T := 1076 }).exact = false ∧
    (verdict { r913 with T := 1467 }).bridge = true ∧
    (verdict { r913 with T := 1466 }).bridge = false := by decide +kernel
theorem v914 :
    verdict r914 = ⟨true, true, 1, 746, 5515, 1689, true, true, true⟩ ∧
    (verdict { r914 with T := 728 }).exact = true ∧
    (verdict { r914 with T := 727 }).exact = false ∧
    (verdict { r914 with T := 786 }).bridge = true ∧
    (verdict { r914 with T := 785 }).bridge = false := by decide +kernel
theorem v915 :
    verdict r915 = ⟨true, true, 1, 1525, 11943, 3730, true, true, true⟩ ∧
    (verdict { r915 with T := 1451 }).exact = true ∧
    (verdict { r915 with T := 1450 }).exact = false ∧
    (verdict { r915 with T := 1574 }).bridge = true ∧
    (verdict { r915 with T := 1573 }).bridge = false := by decide +kernel
theorem v916 :
    verdict r916 = ⟨true, true, 1, 861, 4244, 1298, true, true, true⟩ ∧
    (verdict { r916 with T := 943 }).exact = true ∧
    (verdict { r916 with T := 942 }).exact = false ∧
    (verdict { r916 with T := 943 }).bridge = true ∧
    (verdict { r916 with T := 942 }).bridge = false := by decide +kernel
theorem v917 :
    verdict r917 = ⟨true, true, 1, 1762, 9216, 2878, true, true, true⟩ ∧
    (verdict { r917 with T := 2099 }).exact = true ∧
    (verdict { r917 with T := 2098 }).exact = false ∧
    (verdict { r917 with T := 2099 }).bridge = true ∧
    (verdict { r917 with T := 2098 }).bridge = false := by decide +kernel
theorem v918 :
    verdict r918 = ⟨true, true, 1, 843, 6447, 2797, true, true, true⟩ ∧
    (verdict { r918 with T := 579 }).exact = true ∧
    (verdict { r918 with T := 578 }).exact = false ∧
    (verdict { r918 with T := 843 }).bridge = true ∧
    (verdict { r918 with T := 842 }).bridge = false := by decide +kernel
theorem v919 :
    verdict r919 = ⟨true, true, 1, 975, 4961, 2151, true, true, true⟩ ∧
    (verdict { r919 with T := 756 }).exact = true ∧
    (verdict { r919 with T := 755 }).exact = false ∧
    (verdict { r919 with T := 975 }).bridge = true ∧
    (verdict { r919 with T := 974 }).bridge = false := by decide +kernel
theorem v920 :
    verdict r920 = ⟨true, true, 1, 675, 3519, 1510, true, true, true⟩ ∧
    (verdict { r920 with T := 544 }).exact = true ∧
    (verdict { r920 with T := 543 }).exact = false ∧
    (verdict { r920 with T := 680 }).bridge = true ∧
    (verdict { r920 with T := 679 }).bridge = false := by decide +kernel
theorem v921 :
    verdict r921 = ⟨true, true, 1, 1364, 7698, 3363, true, true, true⟩ ∧
    (verdict { r921 with T := 1085 }).exact = true ∧
    (verdict { r921 with T := 1084 }).exact = false ∧
    (verdict { r921 with T := 1365 }).bridge = true ∧
    (verdict { r921 with T := 1364 }).bridge = false := by decide +kernel
theorem v922 :
    verdict r922 = ⟨true, true, 1, 780, 2706, 1160, true, true, true⟩ ∧
    (verdict { r922 with T := 829 }).exact = true ∧
    (verdict { r922 with T := 828 }).exact = false ∧
    (verdict { r922 with T := 829 }).bridge = true ∧
    (verdict { r922 with T := 828 }).bridge = false := by decide +kernel
theorem v923 :
    verdict r923 = ⟨true, true, 1, 1576, 5940, 2593, true, true, true⟩ ∧
    (verdict { r923 with T := 1848 }).exact = true ∧
    (verdict { r923 with T := 1847 }).exact = false ∧
    (verdict { r923 with T := 1848 }).bridge = true ∧
    (verdict { r923 with T := 1847 }).bridge = false := by decide +kernel
theorem v924 :
    verdict r924 = ⟨true, true, 1, 553, 6370, 3001, true, true, true⟩ ∧
    (verdict { r924 with T := 618 }).exact = true ∧
    (verdict { r924 with T := 617 }).exact = false ∧
    (verdict { r924 with T := 618 }).bridge = true ∧
    (verdict { r924 with T := 617 }).bridge = false := by decide +kernel
theorem v925 :
    verdict r925 = ⟨true, true, 1, 640, 4902, 2309, true, true, true⟩ ∧
    (verdict { r925 with T := 934 }).exact = true ∧
    (verdict { r925 with T := 933 }).exact = false ∧
    (verdict { r925 with T := 934 }).bridge = true ∧
    (verdict { r925 with T := 933 }).bridge = false := by decide +kernel
theorem v926 :
    verdict r926 = ⟨true, true, 1, 518, 3599, 1648, true, true, true⟩ ∧
    (verdict { r926 with T := 624 }).exact = true ∧
    (verdict { r926 with T := 623 }).exact = false ∧
    (verdict { r926 with T := 624 }).bridge = true ∧
    (verdict { r926 with T := 623 }).bridge = false := by decide +kernel
theorem v927 :
    verdict r927 = ⟨true, true, 1, 1060, 8063, 3745, true, true, true⟩ ∧
    (verdict { r927 with T := 1446 }).exact = true ∧
    (verdict { r927 with T := 1445 }).exact = false ∧
    (verdict { r927 with T := 1446 }).bridge = true ∧
    (verdict { r927 with T := 1445 }).bridge = false := by decide +kernel
theorem v928 :
    verdict r928 = ⟨true, true, 1, 598, 2767, 1267, true, true, true⟩ ∧
    (verdict { r928 with T := 833 }).exact = true ∧
    (verdict { r928 with T := 832 }).exact = false ∧
    (verdict { r928 with T := 833 }).bridge = true ∧
    (verdict { r928 with T := 832 }).bridge = false := by decide +kernel
theorem v929 :
    verdict r929 = ⟨true, true, 1, 1225, 6220, 2889, true, true, true⟩ ∧
    (verdict { r929 with T := 1889 }).exact = true ∧
    (verdict { r929 with T := 1888 }).exact = false ∧
    (verdict { r929 with T := 1889 }).bridge = true ∧
    (verdict { r929 with T := 1888 }).bridge = false := by decide +kernel
theorem v930 :
    verdict r930 = ⟨true, true, 1, 1030, 9860, 3196, true, true, true⟩ ∧
    (verdict { r930 with T := 765 }).exact = true ∧
    (verdict { r930 with T := 764 }).exact = false ∧
    (verdict { r930 with T := 1030 }).bridge = true ∧
    (verdict { r930 with T := 1029 }).bridge = false := by decide +kernel
theorem v931 :
    verdict r931 = ⟨true, true, 1, 1191, 7595, 2459, true, true, true⟩ ∧
    (verdict { r931 with T := 1074 }).exact = true ∧
    (verdict { r931 with T := 1073 }).exact = false ∧
    (verdict { r931 with T := 1191 }).bridge = true ∧
    (verdict { r931 with T := 1190 }).bridge = false := by decide +kernel
theorem v932 :
    verdict r932 = ⟨true, true, 1, 743, 5755, 1942, true, true, true⟩ ∧
    (verdict { r932 with T := 740 }).exact = true ∧
    (verdict { r932 with T := 739 }).exact = false ∧
    (verdict { r932 with T := 788 }).bridge = true ∧
    (verdict { r932 with T := 787 }).bridge = false := by decide +kernel
theorem v933 :
    verdict r933 = ⟨true, true, 1, 1408, 12057, 4241, true, true, true⟩ ∧
    (verdict { r933 with T := 1507 }).exact = true ∧
    (verdict { r933 with T := 1506 }).exact = false ∧
    (verdict { r933 with T := 1507 }).bridge = true ∧
    (verdict { r933 with T := 1506 }).bridge = false := by decide +kernel
theorem v934 :
    verdict r934 = ⟨true, true, 1, 858, 4431, 1493, true, true, true⟩ ∧
    (verdict { r934 with T := 942 }).exact = true ∧
    (verdict { r934 with T := 941 }).exact = false ∧
    (verdict { r934 with T := 942 }).bridge = true ∧
    (verdict { r934 with T := 941 }).bridge = false := by decide +kernel
theorem v935 :
    verdict r935 = ⟨true, true, 1, 1627, 9304, 3271, true, true, true⟩ ∧
    (verdict { r935 with T := 2112 }).exact = true ∧
    (verdict { r935 with T := 2111 }).exact = false ∧
    (verdict { r935 with T := 2112 }).bridge = true ∧
    (verdict { r935 with T := 2111 }).bridge = false := by decide +kernel
theorem v936 :
    verdict r936 = ⟨true, true, 1, 921, 7408, 2802, true, true, true⟩ ∧
    (verdict { r936 with T := 584 }).exact = true ∧
    (verdict { r936 with T := 583 }).exact = false ∧
    (verdict { r936 with T := 921 }).bridge = true ∧
    (verdict { r936 with T := 920 }).bridge = false := by decide +kernel
theorem v937 :
    verdict r937 = ⟨true, true, 1, 1065, 5703, 2155, true, true, true⟩ ∧
    (verdict { r937 with T := 758 }).exact = true ∧
    (verdict { r937 with T := 757 }).exact = false ∧
    (verdict { r937 with T := 1065 }).bridge = true ∧
    (verdict { r937 with T := 1064 }).bridge = false := by decide +kernel
theorem v938 :
    verdict r938 = ⟨true, true, 1, 616, 3735, 1469, true, true, true⟩ ∧
    (verdict { r938 with T := 606 }).exact = true ∧
    (verdict { r938 with T := 605 }).exact = false ∧
    (verdict { r938 with T := 635 }).bridge = true ∧
    (verdict { r938 with T := 634 }).bridge = false := by decide +kernel
theorem v939 :
    verdict r939 = ⟨true, true, 1, 1255, 8167, 3291, true, true, true⟩ ∧
    (verdict { r939 with T := 1404 }).exact = true ∧
    (verdict { r939 with T := 1403 }).exact = false ∧
    (verdict { r939 with T := 1404 }).bridge = true ∧
    (verdict { r939 with T := 1403 }).bridge = false := by decide +kernel
theorem v940 :
    verdict r940 = ⟨true, true, 1, 712, 2875, 1129, true, true, true⟩ ∧
    (verdict { r940 with T := 875 }).exact = true ∧
    (verdict { r940 with T := 874 }).exact = false ∧
    (verdict { r940 with T := 875 }).bridge = true ∧
    (verdict { r940 with T := 874 }).bridge = false := by decide +kernel
theorem v941 :
    verdict r941 = ⟨true, true, 1, 1450, 6301, 2539, true, true, true⟩ ∧
    (verdict { r941 with T := 1948 }).exact = true ∧
    (verdict { r941 with T := 1947 }).exact = false ∧
    (verdict { r941 with T := 1948 }).bridge = true ∧
    (verdict { r941 with T := 1947 }).bridge = false := by decide +kernel
theorem v942 :
    verdict r942 = ⟨true, true, 1, 711, 6990, 2945, true, true, true⟩ ∧
    (verdict { r942 with T := 587 }).exact = true ∧
    (verdict { r942 with T := 586 }).exact = false ∧
    (verdict { r942 with T := 711 }).bridge = true ∧
    (verdict { r942 with T := 710 }).bridge = false := by decide +kernel
theorem v943 :
    verdict r943 = ⟨true, true, 1, 822, 5381, 2265, true, true, true⟩ ∧
    (verdict { r943 with T := 921 }).exact = true ∧
    (verdict { r943 with T := 920 }).exact = false ∧
    (verdict { r943 with T := 921 }).bridge = true ∧
    (verdict { r943 with T := 920 }).bridge = false := by decide +kernel
theorem v944 :
    verdict r944 = ⟨true, true, 1, 438, 3948, 1707, true, true, true⟩ ∧
    (verdict { r944 with T := 604 }).exact = true ∧
    (verdict { r944 with T := 603 }).exact = false ∧
    (verdict { r944 with T := 620 }).bridge = true ∧
    (verdict { r944 with T := 619 }).bridge = false := by decide +kernel
theorem v945 :
    verdict r945 = ⟨true, true, 1, 840, 8675, 3852, true, true, true⟩ ∧
    (verdict { r945 with T := 1405 }).exact = true ∧
    (verdict { r945 with T := 1404 }).exact = false ∧
    (verdict { r945 with T := 1405 }).bridge = true ∧
    (verdict { r945 with T := 1404 }).bridge = false := by decide +kernel
theorem v946 :
    verdict r946 = ⟨true, true, 1, 506, 3038, 1313, true, true, true⟩ ∧
    (verdict { r946 with T := 868 }).exact = true ∧
    (verdict { r946 with T := 867 }).exact = false ∧
    (verdict { r946 with T := 868 }).bridge = true ∧
    (verdict { r946 with T := 867 }).bridge = false := by decide +kernel
theorem v947 :
    verdict r947 = ⟨true, true, 1, 971, 6694, 2972, true, true, true⟩ ∧
    (verdict { r947 with T := 1952 }).exact = true ∧
    (verdict { r947 with T := 1951 }).exact = false ∧
    (verdict { r947 with T := 1952 }).bridge = true ∧
    (verdict { r947 with T := 1951 }).bridge = false := by decide +kernel
theorem v948 :
    verdict r948 = ⟨true, true, 1, 1260, 11107, 3494, true, true, true⟩ ∧
    (verdict { r948 with T := 1136 }).exact = true ∧
    (verdict { r948 with T := 1135 }).exact = false ∧
    (verdict { r948 with T := 1260 }).bridge = true ∧
    (verdict { r948 with T := 1259 }).bridge = false := by decide +kernel
theorem v949 :
    verdict r949 = ⟨true, true, 1, 1456, 8557, 2689, true, true, true⟩ ∧
    (verdict { r949 with T := 1312 }).exact = true ∧
    (verdict { r949 with T := 1311 }).exact = false ∧
    (verdict { r949 with T := 1456 }).bridge = true ∧
    (verdict { r949 with T := 1455 }).bridge = false := by decide +kernel
theorem v950 :
    verdict r950 = ⟨true, true, 1, 740, 6237, 1907, true, true, true⟩ ∧
    (verdict { r950 with T := 867 }).exact = true ∧
    (verdict { r950 with T := 866 }).exact = false ∧
    (verdict { r950 with T := 922 }).bridge = true ∧
    (verdict { r950 with T := 921 }).bridge = false := by decide +kernel
theorem v951 :
    verdict r951 = ⟨true, true, 1, 1402, 13303, 4213, true, true, true⟩ ∧
    (verdict { r951 with T := 1702 }).exact = true ∧
    (verdict { r951 with T := 1701 }).exact = false ∧
    (verdict { r951 with T := 1825 }).bridge = true ∧
    (verdict { r951 with T := 1824 }).bridge = false := by decide +kernel
theorem v952 :
    verdict r952 = ⟨true, true, 1, 855, 4802, 1467, true, true, true⟩ ∧
    (verdict { r952 with T := 1016 }).exact = true ∧
    (verdict { r952 with T := 1015 }).exact = false ∧
    (verdict { r952 with T := 1065 }).bridge = true ∧
    (verdict { r952 with T := 1064 }).bridge = false := by decide +kernel
theorem v953 :
    verdict r953 = ⟨true, true, 1, 1620, 10264, 3250, true, true, true⟩ ∧
    (verdict { r953 with T := 2235 }).exact = true ∧
    (verdict { r953 with T := 2234 }).exact = false ∧
    (verdict { r953 with T := 2235 }).bridge = true ∧
    (verdict { r953 with T := 2234 }).bridge = false := by decide +kernel
theorem v954 :
    verdict r954 = ⟨true, true, 1, 704, 6363, 2798, true, true, true⟩ ∧
    (verdict { r954 with T := 580 }).exact = true ∧
    (verdict { r954 with T := 579 }).exact = false ∧
    (verdict { r954 with T := 704 }).bridge = true ∧
    (verdict { r954 with T := 703 }).bridge = false := by decide +kernel
theorem v955 :
    verdict r955 = ⟨true, true, 1, 814, 4895, 2151, true, true, true⟩ ∧
    (verdict { r955 with T := 757 }).exact = true ∧
    (verdict { r955 with T := 756 }).exact = false ∧
    (verdict { r955 with T := 814 }).bridge = true ∧
    (verdict { r955 with T := 813 }).bridge = false := by decide +kernel
theorem v956 :
    verdict r956 = ⟨true, true, 1, 590, 3583, 1513, true, true, true⟩ ∧
    (verdict { r956 with T := 624 }).exact = true ∧
    (verdict { r956 with T := 623 }).exact = false ∧
    (verdict { r956 with T := 679 }).bridge = true ∧
    (verdict { r956 with T := 678 }).bridge = false := by decide +kernel
theorem v957 :
    verdict r957 = ⟨true, true, 1, 1113, 7643, 3338, true, true, true⟩ ∧
    (verdict { r957 with T := 1355 }).exact = true ∧
    (verdict { r957 with T := 1354 }).exact = false ∧
    (verdict { r957 with T := 1355 }).bridge = true ∧
    (verdict { r957 with T := 1354 }).bridge = false := by decide +kernel
theorem v958 :
    verdict r958 = ⟨true, true, 1, 682, 2758, 1164, true, true, true⟩ ∧
    (verdict { r958 with T := 876 }).exact = true ∧
    (verdict { r958 with T := 875 }).exact = false ∧
    (verdict { r958 with T := 876 }).bridge = true ∧
    (verdict { r958 with T := 875 }).bridge = false := by decide +kernel
theorem v959 :
    verdict r959 = ⟨true, true, 1, 1286, 5898, 2575, true, true, true⟩ ∧
    (verdict { r959 with T := 1929 }).exact = true ∧
    (verdict { r959 with T := 1928 }).exact = false ∧
    (verdict { r959 with T := 1929 }).bridge = true ∧
    (verdict { r959 with T := 1928 }).bridge = false := by decide +kernel
theorem v960 :
    verdict r960 = ⟨true, true, 1, 743, 7053, 2655, true, true, true⟩ ∧
    (verdict { r960 with T := 437 }).exact = true ∧
    (verdict { r960 with T := 436 }).exact = false ∧
    (verdict { r960 with T := 743 }).bridge = true ∧
    (verdict { r960 with T := 742 }).bridge = false := by decide +kernel
theorem v961 :
    verdict r961 = ⟨true, true, 1, 859, 5430, 2041, true, true, true⟩ ∧
    (verdict { r961 with T := 771 }).exact = true ∧
    (verdict { r961 with T := 770 }).exact = false ∧
    (verdict { r961 with T := 859 }).bridge = true ∧
    (verdict { r961 with T := 858 }).bridge = false := by decide +kernel
theorem v962 :
    verdict r962 = ⟨true, true, 1, 556, 3794, 1268, true, true, true⟩ ∧
    (verdict { r962 with T := 588 }).exact = true ∧
    (verdict { r962 with T := 587 }).exact = false ∧
    (verdict { r962 with T := 588 }).bridge = true ∧
    (verdict { r962 with T := 587 }).bridge = false := by decide +kernel
theorem v963 :
    verdict r963 = ⟨true, true, 1, 1183, 8289, 2998, true, true, true⟩ ∧
    (verdict { r963 with T := 1361 }).exact = true ∧
    (verdict { r963 with T := 1360 }).exact = false ∧
    (verdict { r963 with T := 1361 }).bridge = true ∧
    (verdict { r963 with T := 1360 }).bridge = false := by decide +kernel
theorem v964 :
    verdict r964 = ⟨true, true, 1, 643, 2922, 974, true, true, true⟩ ∧
    (verdict { r964 with T := 836 }).exact = true ∧
    (verdict { r964 with T := 835 }).exact = false ∧
    (verdict { r964 with T := 836 }).bridge = true ∧
    (verdict { r964 with T := 835 }).bridge = false := by decide +kernel
theorem v965 :
    verdict r965 = ⟨true, true, 1, 1367, 6396, 2312, true, true, true⟩ ∧
    (verdict { r965 with T := 1900 }).exact = true ∧
    (verdict { r965 with T := 1899 }).exact = false ∧
    (verdict { r965 with T := 1900 }).bridge = true ∧
    (verdict { r965 with T := 1899 }).bridge = false := by decide +kernel
theorem v966 :
    verdict r966 = ⟨true, true, 1, 708, 6213, 2802, true, true, true⟩ ∧
    (verdict { r966 with T := 584 }).exact = true ∧
    (verdict { r966 with T := 583 }).exact = false ∧
    (verdict { r966 with T := 708 }).bridge = true ∧
    (verdict { r966 with T := 707 }).bridge = false := by decide +kernel
theorem v967 :
    verdict r967 = ⟨true, true, 1, 819, 4781, 2155, true, true, true⟩ ∧
    (verdict { r967 with T := 758 }).exact = true ∧
    (verdict { r967 with T := 757 }).exact = false ∧
    (verdict { r967 with T := 819 }).bridge = true ∧
    (verdict { r967 with T := 818 }).bridge = false := by decide +kernel
theorem v968 :
    verdict r968 = ⟨true, true, 1, 554, 3658, 1833, true, true, true⟩ ∧
    (verdict { r968 with T := 511 }).exact = true ∧
    (verdict { r968 with T := 510 }).exact = false ∧
    (verdict { r968 with T := 554 }).bridge = true ∧
    (verdict { r968 with T := 553 }).bridge = false := by decide +kernel
theorem v969 :
    verdict r969 = ⟨true, true, 1, 1177, 8393, 4231, true, true, true⟩ ∧
    (verdict { r969 with T := 1238 }).exact = true ∧
    (verdict { r969 with T := 1237 }).exact = false ∧
    (verdict { r969 with T := 1238 }).bridge = true ∧
    (verdict { r969 with T := 1237 }).bridge = false := by decide +kernel
theorem v970 :
    verdict r970 = ⟨true, true, 1, 639, 2812, 1409, true, true, true⟩ ∧
    (verdict { r970 with T := 772 }).exact = true ∧
    (verdict { r970 with T := 771 }).exact = false ∧
    (verdict { r970 with T := 772 }).bridge = true ∧
    (verdict { r970 with T := 771 }).bridge = false := by decide +kernel
theorem v971 :
    verdict r971 = ⟨true, true, 1, 1360, 6476, 3264, true, true, true⟩ ∧
    (verdict { r971 with T := 1807 }).exact = true ∧
    (verdict { r971 with T := 1806 }).exact = false ∧
    (verdict { r971 with T := 1807 }).bridge = true ∧
    (verdict { r971 with T := 1806 }).bridge = false := by decide +kernel
theorem v972 :
    verdict r972 = ⟨true, true, 1, 838, 7324, 2932, true, true, true⟩ ∧
    (verdict { r972 with T := 714 }).exact = true ∧
    (verdict { r972 with T := 713 }).exact = false ∧
    (verdict { r972 with T := 838 }).bridge = true ∧
    (verdict { r972 with T := 837 }).bridge = false := by decide +kernel
theorem v973 :
    verdict r973 = ⟨true, true, 1, 969, 5638, 2255, true, true, true⟩ ∧
    (verdict { r973 with T := 825 }).exact = true ∧
    (verdict { r973 with T := 824 }).exact = false ∧
    (verdict { r973 with T := 969 }).bridge = true ∧
    (verdict { r973 with T := 968 }).bridge = false := by decide +kernel
theorem v974 :
    verdict r974 = ⟨true, true, 1, 756, 4720, 1852, true, true, true⟩ ∧
    (verdict { r974 with T := 710 }).exact = true ∧
    (verdict { r974 with T := 709 }).exact = false ∧
    (verdict { r974 with T := 763 }).bridge = true ∧
    (verdict { r974 with T := 762 }).bridge = false := by decide +kernel
theorem v975 :
    verdict r975 = ⟨true, true, 1, 1465, 10230, 4036, true, true, true⟩ ∧
    (verdict { r975 with T := 1348 }).exact = true ∧
    (verdict { r975 with T := 1347 }).exact = false ∧
    (verdict { r975 with T := 1465 }).bridge = true ∧
    (verdict { r975 with T := 1464 }).bridge = false := by decide +kernel
theorem v976 :
    verdict r976 = ⟨true, true, 1, 874, 3634, 1424, true, true, true⟩ ∧
    (verdict { r976 with T := 855 }).exact = true ∧
    (verdict { r976 with T := 854 }).exact = false ∧
    (verdict { r976 with T := 881 }).bridge = true ∧
    (verdict { r976 with T := 880 }).bridge = false := by decide +kernel
theorem v977 :
    verdict r977 = ⟨true, true, 1, 1693, 7897, 3115, true, true, true⟩ ∧
    (verdict { r977 with T := 1930 }).exact = true ∧
    (verdict { r977 with T := 1929 }).exact = false ∧
    (verdict { r977 with T := 1930 }).bridge = true ∧
    (verdict { r977 with T := 1929 }).bridge = false := by decide +kernel
theorem v978 :
    verdict r978 = ⟨true, true, 1, 552, 6008, 2646, true, true, true⟩ ∧
    (verdict { r978 with T := 428 }).exact = true ∧
    (verdict { r978 with T := 427 }).exact = false ∧
    (verdict { r978 with T := 552 }).bridge = true ∧
    (verdict { r978 with T := 551 }).bridge = false := by decide +kernel
theorem v979 :
    verdict r979 = ⟨true, true, 1, 639, 4621, 2034, true, true, true⟩ ∧
    (verdict { r979 with T := 699 }).exact = true ∧
    (verdict { r979 with T := 698 }).exact = false ∧
    (verdict { r979 with T := 699 }).bridge = true ∧
    (verdict { r979 with T := 698 }).bridge = false := by decide +kernel
theorem v980 :
    verdict r980 = ⟨true, true, 1, 531, 3150, 1455, true, true, true⟩ ∧
    (verdict { r980 with T := 501 }).exact = true ∧
    (verdict { r980 with T := 500 }).exact = false ∧
    (verdict { r980 with T := 536 }).bridge = true ∧
    (verdict { r980 with T := 535 }).bridge = false := by decide +kernel
theorem v981 :
    verdict r981 = ⟨true, true, 1, 1075, 7025, 3284, true, true, true⟩ ∧
    (verdict { r981 with T := 1172 }).exact = true ∧
    (verdict { r981 with T := 1171 }).exact = false ∧
    (verdict { r981 with T := 1172 }).bridge = true ∧
    (verdict { r981 with T := 1171 }).bridge = false := by decide +kernel
theorem v982 :
    verdict r982 = ⟨true, true, 1, 614, 2422, 1119, true, true, true⟩ ∧
    (verdict { r982 with T := 756 }).exact = true ∧
    (verdict { r982 with T := 755 }).exact = false ∧
    (verdict { r982 with T := 756 }).bridge = true ∧
    (verdict { r982 with T := 755 }).bridge = false := by decide +kernel
theorem v983 :
    verdict r983 = ⟨true, true, 1, 1243, 5420, 2534, true, true, true⟩ ∧
    (verdict { r983 with T := 1701 }).exact = true ∧
    (verdict { r983 with T := 1700 }).exact = false ∧
    (verdict { r983 with T := 1701 }).bridge = true ∧
    (verdict { r983 with T := 1700 }).bridge = false := by decide +kernel
theorem v984 :
    verdict r984 = ⟨true, true, 1, 846, 8445, 2800, true, true, true⟩ ∧
    (verdict { r984 with T := 582 }).exact = true ∧
    (verdict { r984 with T := 581 }).exact = false ∧
    (verdict { r984 with T := 846 }).bridge = true ∧
    (verdict { r984 with T := 845 }).bridge = false := by decide +kernel
theorem v985 :
    verdict r985 = ⟨true, true, 1, 978, 6499, 2153, true, true, true⟩ ∧
    (verdict { r985 with T := 758 }).exact = true ∧
    (verdict { r985 with T := 757 }).exact = false ∧
    (verdict { r985 with T := 978 }).bridge = true ∧
    (verdict { r985 with T := 977 }).bridge = false := by decide +kernel
theorem v986 :
    verdict r986 = ⟨true, true, 1, 685, 4567, 1574, true, true, true⟩ ∧
    (verdict { r986 with T := 488 }).exact = true ∧
    (verdict { r986 with T := 487 }).exact = false ∧
    (verdict { r986 with T := 685 }).bridge = true ∧
    (verdict { r986 with T := 684 }).bridge = false := by decide +kernel
theorem v987 :
    verdict r987 = ⟨true, true, 1, 1391, 10162, 3505, true, true, true⟩ ∧
    (verdict { r987 with T := 1111 }).exact = true ∧
    (verdict { r987 with T := 1110 }).exact = false ∧
    (verdict { r987 with T := 1391 }).bridge = true ∧
    (verdict { r987 with T := 1390 }).bridge = false := by decide +kernel
theorem v988 :
    verdict r988 = ⟨true, true, 1, 791, 3514, 1210, true, true, true⟩ ∧
    (verdict { r988 with T := 824 }).exact = true ∧
    (verdict { r988 with T := 823 }).exact = false ∧
    (verdict { r988 with T := 824 }).bridge = true ∧
    (verdict { r988 with T := 823 }).bridge = false := by decide +kernel
theorem v989 :
    verdict r989 = ⟨true, true, 1, 1607, 7841, 2705, true, true, true⟩ ∧
    (verdict { r989 with T := 1844 }).exact = true ∧
    (verdict { r989 with T := 1843 }).exact = false ∧
    (verdict { r989 with T := 1844 }).bridge = true ∧
    (verdict { r989 with T := 1843 }).bridge = false := by decide +kernel
theorem v990 :
    verdict r990 = ⟨true, true, 1, 564, 6150, 2798, true, true, true⟩ ∧
    (verdict { r990 with T := 559 }).exact = true ∧
    (verdict { r990 with T := 558 }).exact = false ∧
    (verdict { r990 with T := 564 }).bridge = true ∧
    (verdict { r990 with T := 563 }).bridge = false := by decide +kernel
theorem v991 :
    verdict r991 = ⟨true, true, 1, 653, 4730, 2151, true, true, true⟩ ∧
    (verdict { r991 with T := 866 }).exact = true ∧
    (verdict { r991 with T := 865 }).exact = false ∧
    (verdict { r991 with T := 866 }).bridge = true ∧
    (verdict { r991 with T := 865 }).bridge = false := by decide +kernel
theorem v992 :
    verdict r992 = ⟨true, true, 1, 417, 3581, 1721, true, true, true⟩ ∧
    (verdict { r992 with T := 586 }).exact = true ∧
    (verdict { r992 with T := 585 }).exact = false ∧
    (verdict { r992 with T := 591 }).bridge = true ∧
    (verdict { r992 with T := 590 }).bridge = false := by decide +kernel
theorem v993 :
    verdict r993 = ⟨true, true, 1, 723, 7672, 3805, true, true, true⟩ ∧
    (verdict { r993 with T := 1362 }).exact = true ∧
    (verdict { r993 with T := 1361 }).exact = false ∧
    (verdict { r993 with T := 1362 }).bridge = true ∧
    (verdict { r993 with T := 1361 }).bridge = false := by decide +kernel
theorem v994 :
    verdict r994 = ⟨true, true, 1, 481, 2753, 1322, true, true, true⟩ ∧
    (verdict { r994 with T := 842 }).exact = true ∧
    (verdict { r994 with T := 841 }).exact = false ∧
    (verdict { r994 with T := 842 }).bridge = true ∧
    (verdict { r994 with T := 841 }).bridge = false := by decide +kernel
theorem v995 :
    verdict r995 = ⟨true, true, 1, 835, 5921, 2935, true, true, true⟩ ∧
    (verdict { r995 with T := 1866 }).exact = true ∧
    (verdict { r995 with T := 1865 }).exact = false ∧
    (verdict { r995 with T := 1866 }).bridge = true ∧
    (verdict { r995 with T := 1865 }).bridge = false := by decide +kernel
theorem v996 :
    verdict r996 = ⟨true, true, 1, 954, 9480, 3048, true, true, true⟩ ∧
    (verdict { r996 with T := 830 }).exact = true ∧
    (verdict { r996 with T := 829 }).exact = false ∧
    (verdict { r996 with T := 954 }).bridge = true ∧
    (verdict { r996 with T := 953 }).bridge = false := by decide +kernel
theorem v997 :
    verdict r997 = ⟨true, true, 1, 1103, 7297, 2344, true, true, true⟩ ∧
    (verdict { r997 with T := 959 }).exact = true ∧
    (verdict { r997 with T := 958 }).exact = false ∧
    (verdict { r997 with T := 1103 }).bridge = true ∧
    (verdict { r997 with T := 1102 }).bridge = false := by decide +kernel
theorem v998 :
    verdict r998 = ⟨true, true, 1, 688, 5075, 1632, true, true, true⟩ ∧
    (verdict { r998 with T := 712 }).exact = true ∧
    (verdict { r998 with T := 711 }).exact = false ∧
    (verdict { r998 with T := 770 }).bridge = true ∧
    (verdict { r998 with T := 769 }).bridge = false := by decide +kernel
theorem v999 :
    verdict r999 = ⟨true, true, 1, 1351, 11112, 3578, true, true, true⟩ ∧
    (verdict { r999 with T := 1400 }).exact = true ∧
    (verdict { r999 with T := 1399 }).exact = false ∧
    (verdict { r999 with T := 1523 }).bridge = true ∧
    (verdict { r999 with T := 1522 }).bridge = false := by decide +kernel
theorem v1000 :
    verdict r1000 = ⟨true, true, 1, 795, 3904, 1254, true, true, true⟩ ∧
    (verdict { r1000 with T := 914 }).exact = true ∧
    (verdict { r1000 with T := 913 }).exact = false ∧
    (verdict { r1000 with T := 914 }).bridge = true ∧
    (verdict { r1000 with T := 913 }).bridge = false := by decide +kernel
theorem v1001 :
    verdict r1001 = ⟨true, true, 1, 1561, 8573, 2761, true, true, true⟩ ∧
    (verdict { r1001 with T := 2028 }).exact = true ∧
    (verdict { r1001 with T := 2027 }).exact = false ∧
    (verdict { r1001 with T := 2028 }).bridge = true ∧
    (verdict { r1001 with T := 2027 }).bridge = false := by decide +kernel
theorem v1002 :
    verdict r1002 = ⟨true, true, 1, 706, 6138, 2800, true, true, true⟩ ∧
    (verdict { r1002 with T := 722 }).exact = true ∧
    (verdict { r1002 with T := 721 }).exact = false ∧
    (verdict { r1002 with T := 845 }).bridge = true ∧
    (verdict { r1002 with T := 844 }).bridge = false := by decide +kernel
theorem v1003 :
    verdict r1003 = ⟨true, true, 1, 817, 4722, 2153, true, true, true⟩ ∧
    (verdict { r1003 with T := 919 }).exact = true ∧
    (verdict { r1003 with T := 918 }).exact = false ∧
    (verdict { r1003 with T := 977 }).bridge = true ∧
    (verdict { r1003 with T := 976 }).bridge = false := by decide +kernel
theorem v1004 :
    verdict r1004 = ⟨true, true, 1, 523, 3574, 1571, true, true, true⟩ ∧
    (verdict { r1004 with T := 633 }).exact = true ∧
    (verdict { r1004 with T := 632 }).exact = false ∧
    (verdict { r1004 with T := 662 }).bridge = true ∧
    (verdict { r1004 with T := 661 }).bridge = false := by decide +kernel
theorem v1005 :
    verdict r1005 = ⟨true, true, 1, 1060, 7856, 3502, true, true, true⟩ ∧
    (verdict { r1005 with T := 1463 }).exact = true ∧
    (verdict { r1005 with T := 1462 }).exact = false ∧
    (verdict { r1005 with T := 1463 }).bridge = true ∧
    (verdict { r1005 with T := 1462 }).bridge = false := by decide +kernel
theorem v1006 :
    verdict r1006 = ⟨true, true, 1, 604, 2748, 1207, true, true, true⟩ ∧
    (verdict { r1006 with T := 906 }).exact = true ∧
    (verdict { r1006 with T := 905 }).exact = false ∧
    (verdict { r1006 with T := 906 }).bridge = true ∧
    (verdict { r1006 with T := 905 }).bridge = false := by decide +kernel
theorem v1007 :
    verdict r1007 = ⟨true, true, 1, 1225, 6064, 2702, true, true, true⟩ ∧
    (verdict { r1007 with T := 2034 }).exact = true ∧
    (verdict { r1007 with T := 2033 }).exact = false ∧
    (verdict { r1007 with T := 2034 }).bridge = true ∧
    (verdict { r1007 with T := 2033 }).bridge = false := by decide +kernel
theorem v1008 :
    verdict r1008 = ⟨true, true, 1, 1289, 9970, 3243, true, true, true⟩ ∧
    (verdict { r1008 with T := 1025 }).exact = true ∧
    (verdict { r1008 with T := 1024 }).exact = false ∧
    (verdict { r1008 with T := 1289 }).bridge = true ∧
    (verdict { r1008 with T := 1288 }).bridge = false := by decide +kernel
theorem v1009 :
    verdict r1009 = ⟨true, true, 1, 1490, 7677, 2495, true, true, true⟩ ∧
    (verdict { r1009 with T := 1184 }).exact = true ∧
    (verdict { r1009 with T := 1183 }).exact = false ∧
    (verdict { r1009 with T := 1490 }).bridge = true ∧
    (verdict { r1009 with T := 1489 }).bridge = false := by decide +kernel
theorem v1010 :
    verdict r1010 = ⟨true, true, 1, 1025, 6072, 1952, true, true, true⟩ ∧
    (verdict { r1010 with T := 821 }).exact = true ∧
    (verdict { r1010 with T := 820 }).exact = false ∧
    (verdict { r1010 with T := 1025 }).bridge = true ∧
    (verdict { r1010 with T := 1024 }).bridge = false := by decide +kernel
theorem v1011 :
    verdict r1011 = ⟨true, true, 1, 1946, 12740, 4174, true, true, true⟩ ∧
    (verdict { r1011 with T := 1503 }).exact = true ∧
    (verdict { r1011 with T := 1502 }).exact = false ∧
    (verdict { r1011 with T := 1946 }).bridge = true ∧
    (verdict { r1011 with T := 1945 }).bridge = false := by decide +kernel
theorem v1012 :
    verdict r1012 = ⟨true, true, 1, 1184, 4674, 1501, true, true, true⟩ ∧
    (verdict { r1012 with T := 1032 }).exact = true ∧
    (verdict { r1012 with T := 1031 }).exact = false ∧
    (verdict { r1012 with T := 1184 }).bridge = true ∧
    (verdict { r1012 with T := 1183 }).bridge = false := by decide +kernel
theorem v1013 :
    verdict r1013 = ⟨true, true, 1, 2248, 9833, 3221, true, true, true⟩ ∧
    (verdict { r1013 with T := 1925 }).exact = true ∧
    (verdict { r1013 with T := 1924 }).exact = false ∧
    (verdict { r1013 with T := 2248 }).bridge = true ∧
    (verdict { r1013 with T := 2247 }).bridge = false := by decide +kernel
theorem v1014 :
    verdict r1014 = ⟨true, true, 1, 756, 6832, 2990, true, true, true⟩ ∧
    (verdict { r1014 with T := 632 }).exact = true ∧
    (verdict { r1014 with T := 631 }).exact = false ∧
    (verdict { r1014 with T := 756 }).bridge = true ∧
    (verdict { r1014 with T := 755 }).bridge = false := by decide +kernel
theorem v1015 :
    verdict r1015 = ⟨true, true, 1, 874, 5258, 2300, true, true, true⟩ ∧
    (verdict { r1015 with T := 938 }).exact = true ∧
    (verdict { r1015 with T := 937 }).exact = false ∧
    (verdict { r1015 with T := 938 }).bridge = true ∧
    (verdict { r1015 with T := 937 }).bridge = false := by decide +kernel
theorem v1016 :
    verdict r1016 = ⟨true, true, 1, 602, 4300, 1842, true, true, true⟩ ∧
    (verdict { r1016 with T := 719 }).exact = true ∧
    (verdict { r1016 with T := 718 }).exact = false ∧
    (verdict { r1016 with T := 777 }).bridge = true ∧
    (verdict { r1016 with T := 776 }).bridge = false := by decide +kernel
theorem v1017 :
    verdict r1017 = ⟨true, true, 1, 1008, 8630, 3941, true, true, true⟩ ∧
    (verdict { r1017 with T := 1393 }).exact = true ∧
    (verdict { r1017 with T := 1392 }).exact = false ∧
    (verdict { r1017 with T := 1413 }).bridge = true ∧
    (verdict { r1017 with T := 1412 }).bridge = false := by decide +kernel
theorem v1018 :
    verdict r1018 = ⟨true, true, 1, 696, 3310, 1416, true, true, true⟩ ∧
    (verdict { r1018 with T := 924 }).exact = true ∧
    (verdict { r1018 with T := 923 }).exact = false ∧
    (verdict { r1018 with T := 924 }).bridge = true ∧
    (verdict { r1018 with T := 923 }).bridge = false := by decide +kernel
theorem v1019 :
    verdict r1019 = ⟨true, true, 1, 1165, 6661, 3041, true, true, true⟩ ∧
    (verdict { r1019 with T := 2000 }).exact = true ∧
    (verdict { r1019 with T := 1999 }).exact = false ∧
    (verdict { r1019 with T := 2000 }).bridge = true ∧
    (verdict { r1019 with T := 1999 }).bridge = false := by decide +kernel
theorem v1020 :
    verdict r1020 = ⟨true, true, 1, 960, 8423, 3054, true, true, true⟩ ∧
    (verdict { r1020 with T := 838 }).exact = true ∧
    (verdict { r1020 with T := 837 }).exact = false ∧
    (verdict { r1020 with T := 1172 }).bridge = true ∧
    (verdict { r1020 with T := 1171 }).bridge = false := by decide +kernel
theorem v1021 :
    verdict r1021 = ⟨true, true, 1, 1110, 6482, 2349, true, true, true⟩ ∧
    (verdict { r1021 with T := 1212 }).exact = true ∧
    (verdict { r1021 with T := 1211 }).exact = false ∧
    (verdict { r1021 with T := 1355 }).bridge = true ∧
    (verdict { r1021 with T := 1354 }).bridge = false := by decide +kernel
theorem v1022 :
    verdict r1022 = ⟨true, true, 1, 746, 4839, 1724, true, true, true⟩ ∧
    (verdict { r1022 with T := 691 }).exact = true ∧
    (verdict { r1022 with T := 690 }).exact = false ∧
    (verdict { r1022 with T := 794 }).bridge = true ∧
    (verdict { r1022 with T := 793 }).bridge = false := by decide +kernel
theorem v1023 :
    verdict r1023 = ⟨true, true, 1, 1485, 10764, 3820, true, true, true⟩ ∧
    (verdict { r1023 with T := 1426 }).exact = true ∧
    (verdict { r1023 with T := 1425 }).exact = false ∧
    (verdict { r1023 with T := 1640 }).bridge = true ∧
    (verdict { r1023 with T := 1639 }).bridge = false := by decide +kernel
theorem v1024 :
    verdict r1024 = ⟨true, true, 1, 862, 3723, 1325, true, true, true⟩ ∧
    (verdict { r1024 with T := 924 }).exact = true ∧
    (verdict { r1024 with T := 923 }).exact = false ∧
    (verdict { r1024 with T := 924 }).bridge = true ∧
    (verdict { r1024 with T := 923 }).bridge = false := by decide +kernel
theorem v1025 :
    verdict r1025 = ⟨true, true, 1, 1716, 8304, 2946, true, true, true⟩ ∧
    (verdict { r1025 with T := 2055 }).exact = true ∧
    (verdict { r1025 with T := 2054 }).exact = false ∧
    (verdict { r1025 with T := 2055 }).bridge = true ∧
    (verdict { r1025 with T := 2054 }).bridge = false := by decide +kernel
theorem v1026 :
    verdict r1026 = ⟨true, true, 1, 694, 6056, 2860, true, true, true⟩ ∧
    (verdict { r1026 with T := 632 }).exact = true ∧
    (verdict { r1026 with T := 631 }).exact = false ∧
    (verdict { r1026 with T := 694 }).bridge = true ∧
    (verdict { r1026 with T := 693 }).bridge = false := by decide +kernel
theorem v1027 :
    verdict r1027 = ⟨true, true, 1, 803, 4659, 2200, true, true, true⟩ ∧
    (verdict { r1027 with T := 945 }).exact = true ∧
    (verdict { r1027 with T := 944 }).exact = false ∧
    (verdict { r1027 with T := 945 }).bridge = true ∧
    (verdict { r1027 with T := 944 }).bridge = false := by decide +kernel
theorem v1028 :
    verdict r1028 = ⟨true, true, 1, 468, 3233, 1558, true, true, true⟩ ∧
    (verdict { r1028 with T := 606 }).exact = true ∧
    (verdict { r1028 with T := 605 }).exact = false ∧
    (verdict { r1028 with T := 606 }).bridge = true ∧
    (verdict { r1028 with T := 605 }).bridge = false := by decide +kernel
theorem v1029 :
    verdict r1029 = ⟨true, true, 1, 973, 7306, 3561, true, true, true⟩ ∧
    (verdict { r1029 with T := 1453 }).exact = true ∧
    (verdict { r1029 with T := 1452 }).exact = false ∧
    (verdict { r1029 with T := 1453 }).bridge = true ∧
    (verdict { r1029 with T := 1452 }).bridge = false := by decide +kernel
theorem v1030 :
    verdict r1030 = ⟨true, true, 1, 540, 2484, 1198, true, true, true⟩ ∧
    (verdict { r1030 with T := 823 }).exact = true ∧
    (verdict { r1030 with T := 822 }).exact = false ∧
    (verdict { r1030 with T := 823 }).bridge = true ∧
    (verdict { r1030 with T := 822 }).bridge = false := by decide +kernel
theorem v1031 :
    verdict r1031 = ⟨true, true, 1, 1125, 5636, 2747, true, true, true⟩ ∧
    (verdict { r1031 with T := 1904 }).exact = true ∧
    (verdict { r1031 with T := 1903 }).exact = false ∧
    (verdict { r1031 with T := 1904 }).bridge = true ∧
    (verdict { r1031 with T := 1903 }).bridge = false := by decide +kernel
theorem v1032 :
    verdict r1032 = ⟨true, true, 1, 1088, 9035, 3182, true, true, true⟩ ∧
    (verdict { r1032 with T := 964 }).exact = true ∧
    (verdict { r1032 with T := 963 }).exact = false ∧
    (verdict { r1032 with T := 1088 }).bridge = true ∧
    (verdict { r1032 with T := 1087 }).bridge = false := by decide +kernel
theorem v1033 :
    verdict r1033 = ⟨true, true, 1, 1258, 6957, 2448, true, true, true⟩ ∧
    (verdict { r1033 with T := 1114 }).exact = true ∧
    (verdict { r1033 with T := 1113 }).exact = false ∧
    (verdict { r1033 with T := 1258 }).bridge = true ∧
    (verdict { r1033 with T := 1257 }).bridge = false := by decide +kernel
theorem v1034 :
    verdict r1034 = ⟨true, true, 1, 772, 5057, 1676, true, true, true⟩ ∧
    (verdict { r1034 with T := 717 }).exact = true ∧
    (verdict { r1034 with T := 716 }).exact = false ∧
    (verdict { r1034 with T := 775 }).bridge = true ∧
    (verdict { r1034 with T := 774 }).bridge = false := by decide +kernel
theorem v1035 :
    verdict r1035 = ⟨true, true, 1, 1583, 11224, 3766, true, true, true⟩ ∧
    (verdict { r1035 with T := 1464 }).exact = true ∧
    (verdict { r1035 with T := 1463 }).exact = false ∧
    (verdict { r1035 with T := 1587 }).bridge = true ∧
    (verdict { r1035 with T := 1586 }).bridge = false := by decide +kernel
theorem v1036 :
    verdict r1036 = ⟨true, true, 1, 892, 3890, 1288, true, true, true⟩ ∧
    (verdict { r1036 with T := 925 }).exact = true ∧
    (verdict { r1036 with T := 924 }).exact = false ∧
    (verdict { r1036 with T := 925 }).bridge = true ∧
    (verdict { r1036 with T := 924 }).bridge = false := by decide +kernel
theorem v1037 :
    verdict r1037 = ⟨true, true, 1, 1829, 8662, 2905, true, true, true⟩ ∧
    (verdict { r1037 with T := 2071 }).exact = true ∧
    (verdict { r1037 with T := 2070 }).exact = false ∧
    (verdict { r1037 with T := 2071 }).bridge = true ∧
    (verdict { r1037 with T := 2070 }).bridge = false := by decide +kernel
theorem v1038 :
    verdict r1038 = ⟨true, true, 1, 564, 6210, 2658, true, true, true⟩ ∧
    (verdict { r1038 with T := 440 }).exact = true ∧
    (verdict { r1038 with T := 439 }).exact = false ∧
    (verdict { r1038 with T := 564 }).bridge = true ∧
    (verdict { r1038 with T := 563 }).bridge = false := by decide +kernel
theorem v1039 :
    verdict r1039 = ⟨true, true, 1, 653, 4777, 2043, true, true, true⟩ ∧
    (verdict { r1039 with T := 704 }).exact = true ∧
    (verdict { r1039 with T := 703 }).exact = false ∧
    (verdict { r1039 with T := 704 }).bridge = true ∧
    (verdict { r1039 with T := 703 }).bridge = false := by decide +kernel
theorem v1040 :
    verdict r1040 = ⟨true, true, 1, 443, 3134, 1378, true, true, true⟩ ∧
    (verdict { r1040 with T := 573 }).exact = true ∧
    (verdict { r1040 with T := 572 }).exact = false ∧
    (verdict { r1040 with T := 573 }).bridge = true ∧
    (verdict { r1040 with T := 572 }).bridge = false := by decide +kernel
theorem v1041 :
    verdict r1041 = ⟨true, true, 1, 908, 7077, 3156, true, true, true⟩ ∧
    (verdict { r1041 with T := 1332 }).exact = true ∧
    (verdict { r1041 with T := 1331 }).exact = false ∧
    (verdict { r1041 with T := 1332 }).bridge = true ∧
    (verdict { r1041 with T := 1331 }).bridge = false := by decide +kernel
theorem v1042 :
    verdict r1042 = ⟨true, true, 1, 512, 2410, 1059, true, true, true⟩ ∧
    (verdict { r1042 with T := 810 }).exact = true ∧
    (verdict { r1042 with T := 809 }).exact = false ∧
    (verdict { r1042 with T := 810 }).bridge = true ∧
    (verdict { r1042 with T := 809 }).bridge = false := by decide +kernel
theorem v1043 :
    verdict r1043 = ⟨true, true, 1, 1050, 5460, 2435, true, true, true⟩ ∧
    (verdict { r1043 with T := 1832 }).exact = true ∧
    (verdict { r1043 with T := 1831 }).exact = false ∧
    (verdict { r1043 with T := 1832 }).bridge = true ∧
    (verdict { r1043 with T := 1831 }).bridge = false := by decide +kernel
theorem v1044 :
    verdict r1044 = ⟨true, true, 1, 1045, 11099, 3139, true, true, true⟩ ∧
    (verdict { r1044 with T := 921 }).exact = true ∧
    (verdict { r1044 with T := 920 }).exact = false ∧
    (verdict { r1044 with T := 1257 }).bridge = true ∧
    (verdict { r1044 with T := 1256 }).bridge = false := by decide +kernel
theorem v1045 :
    verdict r1045 = ⟨true, true, 1, 1208, 8547, 2415, true, true, true⟩ ∧
    (verdict { r1045 with T := 1310 }).exact = true ∧
    (verdict { r1045 with T := 1309 }).exact = false ∧
    (verdict { r1045 with T := 1453 }).bridge = true ∧
    (verdict { r1045 with T := 1452 }).bridge = false := by decide +kernel
theorem v1046 :
    verdict r1046 = ⟨true, true, 1, 674, 6030, 1720, true, true, true⟩ ∧
    (verdict { r1046 with T := 772 }).exact = true ∧
    (verdict { r1046 with T := 771 }).exact = false ∧
    (verdict { r1046 with T := 827 }).bridge = true ∧
    (verdict { r1046 with T := 826 }).bridge = false := by decide +kernel
theorem v1047 :
    verdict r1047 = ⟨true, true, 1, 1393, 13291, 3862, true, true, true⟩ ∧
    (verdict { r1047 with T := 1630 }).exact = true ∧
    (verdict { r1047 with T := 1629 }).exact = false ∧
    (verdict { r1047 with T := 1753 }).bridge = true ∧
    (verdict { r1047 with T := 1752 }).bridge = false := by decide +kernel
theorem v1048 :
    verdict r1048 = ⟨true, true, 1, 779, 4642, 1323, true, true, true⟩ ∧
    (verdict { r1048 with T := 999 }).exact = true ∧
    (verdict { r1048 with T := 998 }).exact = false ∧
    (verdict { r1048 with T := 999 }).bridge = true ∧
    (verdict { r1048 with T := 998 }).bridge = false := by decide +kernel
theorem v1049 :
    verdict r1049 = ⟨true, true, 1, 1610, 10255, 2979, true, true, true⟩ ∧
    (verdict { r1049 with T := 2274 }).exact = true ∧
    (verdict { r1049 with T := 2273 }).exact = false ∧
    (verdict { r1049 with T := 2274 }).bridge = true ∧
    (verdict { r1049 with T := 2273 }).bridge = false := by decide +kernel

end Formal.Timing.ChainSettleExe.GcdD
