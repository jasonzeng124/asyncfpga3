#!/usr/bin/env bash
# dyn_vecs.sh -- the v2 vector files of Dynamatic's store and load-first tests (research/data/suite/dyn/README.md, "the store
# tests"): research/data/suite/vec/K.hex, written by memvec.py from the domains read off each test's C
# (research/data/suite/dynsrc/K/). Expected values never come from here: oracle_mem.sh computes them from the C.
# Every written array is filled with values the kernel does not write, so a store that did not happen is visible on
# read-back; every vector stays inside the C's defined behaviour (no signed overflow, no access past an array).
# K_rtl.hex (RTL only, research/tools/suite/rtl_bench.sh): for a kernel with large arrays, every call, of which
# K.hex keeps the few the decoded-netlist gate can afford (the `split` lines at the end); for while_loop_3, the edges
# whose trip counts (46340) no gate can afford.
set -euo pipefail
cd "$(dirname "$0")/../../.."
V=research/data/suite/vec; M="python3 research/tools/suite/memvec.py"
# simple_example_1(a[100]): x counts the N = 100 trips, then a[0] = x: a[0] becomes 100, a[1..99] stay
$M simple_example_1 --seed 101 --range=-2147483648,2147483647 -o $V/simple_example_1.hex \
  --call ";a=seq:0,1" --call ";a=rand:-2147483648,2147483647" --call ";a=const:-1" --call ";a=const:99"
# while_loop_3(a[100], bound): i = 0; while (i * i < bound) i++; a[0] = i.  Defined for bound <= 46340^2 =
# 2147395600 (i * i overflows above); bound <= 0: no trip, a[0] = 0.  Exact squares and their successors.
$M while_loop_3 --seed 103 --range=-2147483648,2147483647 -o $V/while_loop_3.hex \
  --call "0x80000000;a=const:-1" --call "0;a=rand:1,2147483647" --call "1;a=const:0" --call "2" \
  --call "100" --call "101" --call "1025"
$M while_loop_3 --seed 104 --range=-2147483648,2147483647 -o $V/while_loop_3_rtl.hex \
  --call "2147395600;a=const:0" --call "2147395599" --call "2147302921" --call "2147302922"
# if_convert(a[200], b[200]): i = 1; do { if (i * a[i] < 10000) i++; i++; b[i] = 1; } while (i < 199).  Reads a[1..198],
# writes b[2..199] (b[0], b[1] never).  Defined only if the trip never stands at i = 198 with the branch taken
# (b[200] is past the array): a[198] >= 51 wherever 198 can be reached; |a[i]| <= 10845877 (198 * a[i] in int).
$M if_convert --seed 105 -o $V/if_convert.hex \
  --call ";a=rand:0,4999@198=5000;b=const:0" --call ";a=const:0;b=rand:2,2147483647" \
  --call ";a=const:10000;b=const:-1" --call ";a=const:51;b=rand:-2147483648,0" \
  --call ";a=rand:-10845877,10845877@198=10845877;b=rand:-2147483648,2147483647"
# loop_path(a, b, c[1000]): t = a[i] + b[i]; c[i] = t; i++; stops when 1000 - t <= 5 * t (t >= 167) or i == 1000.
# |t| <= 429496729 keeps 5 * t in int.
$M loop_path --seed 107 -o $V/loop_path.hex \
  --call ";a=seq:0,1;b=const:1;c=rand:-2147483648,2147483647" \
  --call ";a=const:166;b=const:0;c=const:-1" --call ";a=const:100;b=const:67;c=rand:-2147483648,2147483647" \
  --call ";a=rand:-214748364,214748364;b=rand:-214748364,214748364;c=rand:-2147483648,2147483647"
# single_loop(a, b, c[1000]): s = a[i] * b[i]; c[i] = s; i++; while (s < 1000).  Defined only if some i <= 999 has
# a[i] * b[i] >= 1000 (else a[1000] is read); |a|, |b| <= 46340.
$M single_loop --seed 109 -o $V/single_loop.hex \
  --call ";a=const:2;b=seq:0,1;c=rand:-2147483648,2147483647" --call ";a=const:1000;b=const:1;c=const:-1" \
  --call ";a=const:999@999=1000;b=const:1;c=rand:-2147483648,2147483647" \
  --call ";a=rand:-46340,46340@999=46340;b=rand:-46340,46340@999=46340;c=const:0x5a5a5a5a" \
  --call ";a=const:-46340@10=1;b=const:46340@10=1000;c=rand:-2147483648,2147483647"
# nested_loop(a, b, c[1000]): twice (j = 0, 1): i = 0; do { s = a[i] * b[i]; c[i + 400 j] = s; i++; } while (s < 1000).
# Defined only if the exit comes by i = 599 (c[i + 400] in the array); |a|, |b| <= 46340.
$M nested_loop --seed 111 -o $V/nested_loop.hex \
  --call ";a=const:5;b=seq:0,1;c=rand:-2147483648,2147483647" --call ";a=const:1000;b=const:1;c=const:-1" \
  --call ";a=const:999@599=1000;b=const:1;c=rand:-2147483648,2147483647" \
  --call ";a=rand:-46340,46340@599=46340;b=rand:-46340,46340@599=46340;c=const:0x5a5a5a5a"
# matrix(inA, inB, outC [30][30]): outC = inA x inB, 27000 multiply-adds; |elements| <= 8460 (30 * 8460^2 in int).
$M matrix --seed 113 -o $V/matrix.hex \
  --call ";inA=rand:0,9;inB=rand:0,9;outC=rand:-2147483648,2147483647" \
  --call ";inA=const:8460;inB=const:8460;outC=const:0x5a5a5a5a" \
  --call ";inA=const:8460;inB=const:-8460;outC=const:0x5a5a5a5a" \
  --call ";inA=rand:-8460,8460;inB=rand:-8460,8460;outC=rand:-2147483648,2147483647"
# stencil_2d(orig[900], filter[10], sol[900]) -> temp: sol[c] = sum of filter[3 k1 + k2] * orig[30 k1 + c + k2] for c < 28;
# returns the last sum.  Reads orig[0..89], filter[0..8]; |elements| <= 15446 (9 * 15446^2 in int).
$M stencil_2d --seed 115 -o $V/stencil_2d.hex \
  --call ";orig=rand:0,99;filter=rand:0,99;sol=rand:-2147483648,2147483647" \
  --call ";orig=const:15446;filter=const:15446;sol=const:-1" \
  --call ";orig=const:15446;filter=const:-15446;sol=const:0x5a5a5a5a" \
  --call ";orig=rand:-15446,15446;filter=rand:-15446,15446;sol=rand:-2147483648,2147483647"
# test_flatten_array(input, output [4][8][16]): output[a][b][c] = input[a][7 - b][15 - c] (512 trips, no arithmetic).
$M test_flatten_array --seed 117 -o $V/test_flatten_array.hex \
  --call ";input=seq:0,1;output=const:-1" \
  --call ";input=rand:-2147483648,2147483647;output=rand:-2147483648,2147483647"
# ---- load first on one controller (mc:load1st: an arbitrated port, the load's z forked into the token) ----
# In place (an array read and then written): the bench's second run of a call would transform the transformed array,
# so these are judged with ONE run per call (GATE_NRUNS=1, ORACLE_RUNS=1): test_memory_1, test_memory_2,
# vector_rescale, mul_example, image_resize, video_filter, share_test_2.
# test_memory_1(a[4], n): for (i = 0; i < n; i++) a[i] += 5.  n <= 4; a[i] <= INT_MAX - 5.
$M test_memory_1 --seed 121 -o $V/test_memory_1.hex \
  --call "4;a=rand:-2147483648,2147483642" --call "0;a=const:-1" --call "0x80000000;a=const:7" --call "1;a=const:-5" \
  --call "4;a=const:2147483642" --call "3;a=list:-2147483648,0,-6,9"
# test_memory_2(a[5], n): for (i = 0; i < n - 1; i++) a[i] = a[i + 1] + 5.  n <= 5 and n > INT_MIN (n - 1);
# a[1..4] <= INT_MAX - 5.  Reads the next element, writes this one (the load of i + 1 and the store of i, LS).
$M test_memory_2 --seed 123 -o $V/test_memory_2.hex \
  --call "5;a=seq:10,10" --call "0;a=const:-1" --call "1;a=const:3" --call "2;a=rand:-2147483648,2147483642" \
  --call "5;a=rand:-2147483648,2147483642" --call="-2147483647;a=const:1" --call "5;a=list:7,2147483642,-2147483648,0,-5"
# vector_rescale(a[1000], c): a[i] *= c.  |a[i] * c| <= INT_MAX.
$M vector_rescale --seed 125 -o $V/vector_rescale.hex \
  --call "3;a=rand:-715827882,715827882" --call="-1;a=rand:-2147483647,2147483647" \
  --call "46341;a=rand:-46340,46340@999=46340" --call "0;a=rand:1,2147483647"
# mul_example(a[100]): a[i] = a[i]^3.  |a[i]| <= 1290 (1290^3 = 2146689000).
$M mul_example --seed 127 -o $V/mul_example.hex \
  --call ";a=rand:-1290,1290" --call ";a=list:1290,-1290,0,1,-1,2" --call ";a=seq:-50,1"
# image_resize(a[30][30], c): a = c - a.
$M image_resize --seed 129 -o $V/image_resize.hex \
  --call "0;a=rand:-2147483647,2147483647" --call "2147483647;a=rand:0,2147483647" \
  --call="-2147483648;a=rand:-2147483648,0" --call "12345;a=seq:0,1"
# video_filter(offset, scale, R, G, B [30][30]): p = ((p - offset) * scale) >> 4.  |p - offset| * |scale| <= INT_MAX.
$M video_filter --seed 131 -o $V/video_filter.hex \
  --call "0 16;pixelR=rand:0,255;pixelG=rand:0,255;pixelB=rand:0,255" \
  --call "255 8421504;pixelR=rand:0,255;pixelG=const:0;pixelB=rand:0,255" \
  --call "100 -8421504;pixelR=rand:0,255;pixelG=rand:0,255;pixelB=const:255"
# share_test_2(a[100]): acc += i + 123456; a[i] = acc*i*456784 + 123456*x*i + 444444*x*acc -- signed overflow for
# EVERY input (acc*i*456784 at i = 1 alone is 5.6e10): no defined answer; the oracle's is -fwrapv's (two's complement).
$M share_test_2 --seed 133 -o $V/share_test_2.hex \
  --call ";a=rand:-2147483648,2147483647" --call ";a=const:0" --call ";a=seq:0,1"
# Read twice, written never or elsewhere (two runs per call, as the bench's default):
# binary_search(search, a[101]) -> the first even index holding search, else the first odd one, else -1.
$M binary_search --seed 135 -o $V/binary_search.hex \
  --call "7;a=rand:100,200@40=7@41=7" --call "7;a=rand:100,200@41=7" --call "7;a=rand:100,200" \
  --call="-2147483648;a=rand:0,10@0=-2147483648" --call "2147483647;a=rand:0,10@100=2147483647" \
  --call "5;a=rand:0,4@99=5" --call "0;a=seq:-50,1"
# test_bool_array(a[2] _Bool) -> a[0] || a[1].  Only 0 and 1 are _Bool values.
$M test_bool_array --seed 137 -o $V/test_bool_array.hex \
  --call ";a=list:1,0" --call ";a=list:0,1" --call ";a=list:1,1" --call ";a=list:0,0"
# share_test_1(a, b [1000]) -> sum 5 a[i] b[999-i] + sum a[999-i] b[i]; |a|, |b| <= 598 (6000 * 598^2 < 2^31).
$M share_test_1 --seed 139 -o $V/share_test_1.hex \
  --call ";a=rand:-598,598;b=rand:-598,598" --call ";a=const:598;b=const:598" --call ";a=seq:0,1;b=const:-1"
# iir(y, x [1000], a, b) -> tmp = a*tmp + b*x[i] from tmp = y[0], y[i] = tmp (i >= 1).  Defined only for small a:
# a in {0, 1, -1}, |b x| * 1000 + |y[0]| <= INT_MAX.
$M iir --seed 141 -o $V/iir.hex \
  --call "1 1;y=rand:-1000000,1000000;x=rand:-2000000,2000000" \
  --call "0 -3;y=rand:-2147483648,2147483647;x=rand:-700000000,700000000" \
  --call="-1 2;y=rand:-1000000,1000000;x=rand:-1000000,1000000"
# sobel(in[256], gX[9], gY[9], out[256]) -> sum: for y, x < 15: sumX/sumY over in[x] * g[k], clamped to [0, 255],
# sum += both, out[x + y] = 255 - (unsigned char)sum.  |in|, |g| <= 15446 (9 * 15446^2 < 2^31).
$M sobel --seed 143 -o $V/sobel.hex \
  --call ";in=rand:0,255;gX=list:-1,0,1,-2,0,2,-1,0,1;gY=list:-1,-2,-1,0,0,0,1,2,1;out=rand:-2147483648,2147483647" \
  --call ";in=rand:-15446,15446;gX=rand:-15446,15446;gY=rand:-15446,15446;out=const:-1" \
  --call ";in=const:15446;gX=const:15446;gY=const:-15446;out=const:0x5a5a5a5a"
# spmv(n, row[11], col[10], val[10], vec[10], out[10]) -> row[n - 1] (s): CSR rows [row[i], row[i+1]) for i < n.
# Defined for n <= 10, 0 <= row[i] <= 10, col[c] in [0, 9]; |val * vec| * 10 <= INT_MAX.
$M spmv --seed 145 -o $V/spmv.hex \
  --call "10;row=list:0,1,1,3,4,4,6,8,9,10,10;col=list:3,0,9,5,5,1,7,2,8,4;val=rand:-14654,14654;vec=rand:-14654,14654;out=const:-1" \
  --call "10;row=list:0,0,0,0,0,0,0,0,0,0,10;col=seq:9,-1;val=rand:-1000,1000;vec=rand:-1000,1000;out=rand:-2147483648,2147483647" \
  --call "0;row=const:0;col=const:0;val=const:5;vec=const:5;out=const:7" \
  --call "3;row=list:2,5,5,9,0,0,0,0,0,0,0;col=list:0,1,2,3,4,5,6,7,8,9;val=seq:1,1;vec=seq:-5,1;out=const:0x5a5a5a5a"
# test_stdint(a[100] int8_t, b int8_t): a[i] = a[i]^3 + b, stored back as int8_t (x^3 <= 2^21 in int; the store's
# narrowing is implementation-defined, gcc: modulo 2^8 -- the bench's i8 port does the same).  In place: one run.
$M test_stdint --seed 147 -o $V/test_stdint.hex \
  --call "5;a=rand:-128,127" --call="-128;a=list:-128,127,0,1,-1,2" --call "127;a=seq:-50,1" --call "0;a=const:-128"
# ---- the gate's files: a kernel whose arrays hold thousands of words costs the decoded-netlist gate about 14 min of
# wall per 1000 host accesses (each call fills every array and reads every array back: research/data/suite/dyn/
# README.md), so its K.hex keeps only the calls listed here; every call stays in K_rtl.hex (rtl_bench.sh).
S="python3 research/tools/suite/vecsub.py"
split() { k=$1; shift; mv $V/$k.hex $V/${k}_rtl.hex; $S $V/${k}_rtl.hex $V/$k.hex "$@"; }
split if_convert 0 3 4
split loop_path 0
split single_loop 0
split nested_loop 0
split matrix 0
split stencil_2d 3
split test_flatten_array 0
split vector_rescale 0 2
split image_resize 0 1
split video_filter 0
split share_test_1 0
split iir 0
