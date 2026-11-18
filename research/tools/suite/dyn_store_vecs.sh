#!/usr/bin/env bash
# dyn_store_vecs.sh -- the v2 vector files of Dynamatic's store tests (research/data/suite/dyn/README.md, "the store
# tests"): research/data/suite/vec/K.hex, written by memvec.py from the domains read off each test's C
# (research/data/suite/dynsrc/K/). Expected values never come from here: oracle_mem.sh computes them from the C.
# Every written array is filled with values the kernel does not write, so a store that did not happen is visible on
# read-back; every vector stays inside the C's defined behaviour (no signed overflow, no access past an array).
# K_rtl.hex: the edges that are too long for the decoded-netlist gate (RTL only, research/tools/suite/rtl_bench.sh).
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
