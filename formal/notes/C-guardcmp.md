# C-guardcmp: draws' min RAM setup margin vs hostrace's host-write slack, three guard forms (shard C, 2026-11-20 00:43 UTC)

Farm c_mem24..31 (research HEAD at filing, nextpnr 6e5d224472232d5d; every row's sdf checked against research's route),
memtask HOSTPORT, 16 draws + 16 slow-carry/RAM draws of research's model per route, then hostrace.py (static, band
0.255, cells 0.6). drawMin = smallest RAM setup margin over all RAM edges of all 32 draws (kernel phase included);
plain / x.772/1.155 / -400 = smallest host-write setup slack per route in each form. Untrusted simulation and
static path sums. Produced by formal/tools/margin/bram/guardcmp.py.

```
kernel               seed sdf      check     pass    drawMin    plain x.772/1.155     -400
if_loop_1            1    b2ad5a7b SAME      32/32       25      193    -1107     -207
iir                  1    091c7f6d SAME      32/32      186      337     -899      -63
spmv                 4    f52af15f SAME      32/32       22      258     -891     -142
dot2                 4    9ff7f65b SAME      32/32      278      489     -862       89
if_loop_1            3    dd17e534 SAME      32/32      197      397     -814       -3
gather               2    86c9d605 SAME      32/32      306      323     -772      -77
if_loop_1            4    cdf0560b SAME      32/32      314      708     -719      308
loop_path            1    1f4eee75 SAME      32/32      293      585     -691      185
iir                  1    729969dd SAME      32/32      311      466     -654       66
fill                 3    a98cfa1d SAME      32/32      525      753     -643      353
simple_example_1     3    07f19197 SAME      32/32      601      735     -570      335
loop_path            1    e54c35fd SAME      32/32      562      766     -560      366
nested_loop          3    af476179 SAME      32/32      403      683     -555      283
if_loop_2            1    912166a1 SAME      32/32      844     1007     -522      607
gather               3    4e41e339 SAME      32/32      774      830     -472      430
test_flatten_array   3    4573e3ac SAME      32/32      757      887     -467      487
fill                 2    87090c0b SAME      32/32      536      682     -436      282
test_stdint          1    bca02df4 SAME      32/32      295      398     -405       -2
test_bitint          3    fc7854a3 SAME      32/32      490      689     -400      289
spmv                 2    fe1740d4 SAME      32/32      466      706     -387      306
fir                  4    4060231b SAME      32/32      820      778     -380      378
simple_example_1     1    5b20a707 SAME      32/32      926     1129     -374      729
dot2                 3    36a3907f SAME      32/32      871     1107     -331      707
gather               1    ed13e202 SAME      32/32      670      867     -309      467
if_loop_2            3    073c09d9 SAME      32/32      809     1144     -305      744
if_convert           4    50e31cef SAME      32/32      575      813     -300      413
memsum               1    e996f436 SAME      32/32     1095     1341     -280      941
single_loop          1    3e51a82d SAME      32/32      838     1054     -269      654
fir                  3    42e919b6 SAME      32/32      678      991     -264      591
if_convert           2    c990d905 SAME      32/32      743      907     -261      507
spmv                 1    6caf1111 SAME      32/32     1069     1193     -222      793
spmv                 1    f156f9f9 SAME      32/32      968     1243     -205      843
test_bitint          1    cf69bd3e SAME      32/32      429      643     -177      243
share_test_1         1    440fee8f SAME      32/32     1008     1428     -175     1028
test_memory_2        2    6b132f6f SAME      32/32     1369     1643     -174     1243
sumi3_mem            2    26f31958 SAME      32/32      960     1073     -164      673
mul_example          2    eaafdc60 SAME      32/32      638      860     -155      460
nested_loop          1    84d60192 SAME      32/32      938     1156     -130      756
if_loop_2            2    5ecd6192 SAME      32/32     1282     1566     -119     1166
fir                  2    b95f54ea SAME      32/32      966     1102     -100      702
single_loop          1    e29c9cc7 SAME      32/32      952     1168      -85      768
if_convert           1    d8bc2924 SAME      32/32      867     1076      -73      676
if_loop_1            1    c3113cc4 SAME      32/32     1152     1365      -69      965
nested_loop          1    089fc849 SAME      32/32     1365     1716      -63     1316
if_convert           3    1e8bb52e SAME      32/32      899     1122      -54      722
unused_arg           4    8865ecb5 SAME      32/32     1291     1532      -35     1132
dot2                 2    4d68e57e SAME      32/32     1161     1313      -21      913
mul_example          1    7876f9f4 SAME      32/32      822     1170       -6      770
sumi3_mem            3    77e26098 SAME      32/32      535     1148       -5      748
fill                 1    2db8f6e8 SAME      32/32     1153     1365        1      965
nested_loop          2    4f755025 SAME      32/32     1059     1404       16     1004
loop_path            2    36c11dae SAME      32/32     1133     1338       35      938
stencil_2d           3    d886b5d4 SAME      32/32     1201     1408       45     1008
while_loop_3         2    c9f1d0a0 SAME      32/32      974     1604       95     1204
test_flatten_array   2    96248d2a SAME      32/32     1154     1335      102      935
vector_rescale       1    120bd6ba SAME      32/32     1255     1547      106     1147
memsum               4    d8d78d23 SAME      32/32      925     1311      107      911
test_bitint          2    3696e956 SAME      32/32     1016     1127      110      727
test_bitint          1    e2ae20a1 SAME      32/32      816      981      120      581
sumi3_mem            1    448634ea SAME      32/32     1305     1480      150     1080
if_convert           1    a99380fc SAME      32/32     1192     1423      161     1023
dot2                 3    cee82855 SAME      32/32     1417     1759      206     1359
gather               4    4902271a SAME      32/32     1479     1613      207     1213
while_loop_3         1    2918dcd1 SAME      32/32     1559     1910      261     1510
stencil_2d           1    9bdd8c47 SAME      64/64     1273     1569      262     1169
fill                 1    fcf270f3 SAME      32/32      886     1601      270     1201
test_bitint          4    b0c5f05a SAME      32/32     1284     1456      271     1056
dot2                 3    9ddddf3b SAME      32/32     1297     1805      289     1405
sumi3_mem            1    eba8d3bc SAME      32/32     1435     1686      329     1286
fir                  1    01a9e080 SAME      32/32     1136     1510      336     1110
memsum               1    95dfac83 SAME      32/32     1649     1930      344     1530
if_loop_1            2    25d24290 SAME      32/32     1453     1648      349     1248
test_bool_array      1    724d0364 SAME      32/32     1338     1562      354     1162
binary_search        1    5981c80b SAME      32/32     1655     2023      377     1623
nested_loop          4    0e1d0a58 SAME      32/32     2023     1932      384     1532
while_loop_3         4    207142f2 SAME      32/32      891     1841      399     1441
unused_arg           1    db282072 SAME      32/32     2043     2296      412     1896
dot2                 1    cd975c99 SAME      32/32     1640     1839      438     1439
sumi3_mem            4    9d874530 SAME      32/32     1604     1886      442     1486
single_loop          2    b98bccb9 SAME      32/32     1862     1772      487     1372
test_memory_2        1    36c3a48b SAME      32/32     1169     2102      516     1702
simple_example_1     4    091c9121 SAME      32/32      668     1755      531     1355
iir                  3    de4bfae6 SAME      32/32     1858     2229      555     1829
fir                  1    2ce84953 SAME      32/32      965     1800      578     1400
if_loop_2            1    ae0edcb6 SAME      32/32     2003     2224      578     1824
gather               1    33b77519 SAME      32/32     1520     2015      597     1615
share_test_1         2    420e38e3 SAME      32/32     1774     2008      616     1608
simple_example_1     2    4c992d90 SAME      32/32     1642     1917      620     1517
test_bool_array      3    e3ac07f8 SAME      32/32     1501     1649      636     1249
while_loop_3         3    e3f8c11b SAME      32/32     1838     2122      662     1722
test_flatten_array   4    927c767c SAME      32/32     1870     2104      675     1704
test_memory_1        4    1604154a SAME      32/32     1114     2411      686     2011
test_memory_2        1    c4df7a8a SAME      32/32     1270     2388      726     1988
if_loop_2            4    7cb58e52 SAME      32/32     2140     2410      753     2010
stencil_2d           4    4c252a06 SAME      32/32     1017     2131      853     1731
fill                 4    836133a7 SAME      32/32     2350     2584      869     2184
unused_arg           3    543d6546 SAME      32/32     1996     2375     1002     1975
binary_search        2    d1f73792 SAME      32/32     2368     2684     1042     2284
dot2                 1    43afb62a SAME      32/32     2110     2429     1042     2029
memsum               2    38436143 SAME      32/32     2218     2548     1049     2148
binary_search        3    142dae86 SAME      32/32     2051     2531     1067     2131
image_resize         2    1e790569 SAME      32/32     2427     2680     1089     2280
unused_arg           2    44a0988d SAME      32/32     2351     2693     1117     2293
test_flatten_array   1    692f9c71 SAME      32/32     2211     2671     1119     2271
spmv                 3    04edd759 SAME      32/32     2498     2795     1134     2395
while_loop_3         1    a732a489 SAME      32/32     2411     2881     1199     2481
test_memory_1        1    0c85e348 SAME      32/32     1597     3022     1254     2622
if_loop_2            4    dcc7f48d SAME      32/32     2695     2932     1299     2532
binary_search        1    4b26990e SAME      32/32     2589     2893     1396     2493
unused_arg           1    1e5a1934 SAME      32/32     2854     3165     1436     2765
if_loop_1            3    9395ad8a SAME      64/64     2861     3139     1507     2739
test_stdint          1    14ddd413 SAME      32/32     2321     3022     1536     2622
iir                  2    84ed82ef SAME      32/32     1866     3060     1554     2660
test_flatten_array   1    ce6c6a19 SAME      32/32     2940     3195     1605     2795
test_memory_1        1    0e95d2ca SAME      32/32     2358     3295     1611     2895
memsum               3    b6a797f9 SAME      32/32     2665     3518     1734     3118
test_bool_array      2    e4582eeb SAME      32/32     3195     3146     1760     2746
image_resize         1    1e81bd80 SAME      32/32     3316     3709     1774     3309
binary_search        4    8598e270 SAME      32/32     3409     3602     1786     3202
if_loop_2            4    93d2bf9f SAME      32/32     3328     3562     1911     3162
test_bool_array      1    8759dc8d SAME      32/32     3560     3835     2201     3435
if_loop_1            4    ?        NO-BUILD  -            -        -        -        -
test_loop_free       3    7a06a359 SAME      32/32        -        -        -        -
test_loop_free       4    7a6acf1c SAME      32/32        -        -        -        -
test_loop_free       1    ff65916b SAME      32/32        -        -        -        -
test_loop_free       2    42c0bac6 SAME      32/32        -        -        -        -

121 routes with hostrace + SAME; 0 with a failing draw
plain          negative on   0 routes (0 of them with a failing draw); positive on 121 (0 with a failing draw)
x0.772/x1.155  negative on  49 routes (0 of them with a failing draw); positive on  72 (0 with a failing draw)
-400           negative on   6 routes (0 of them with a failing draw); positive on 115 (0 with a failing draw)
```
