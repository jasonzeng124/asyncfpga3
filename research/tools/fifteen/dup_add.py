#!/usr/bin/env python3
"""dup_add.py IN.mlir OUT.mlir -- xorshift only: give the loop compare its own copy of the loop increment.

    %29 = addi %7, %14 ; %30:2 = fork %29 ; %31 = cmpi slt, %30#1, %11#1 ; cond_br6 reads %30#0
becomes
    %7d:2 = fork %7 ; %29 = addi %7d#0, %14 ; cond_br6 reads %29
    %29d = addi %7d#1, <its own constant 1> ; %31 = cmpi slt, %29d, %11#1
so bdc fuses the copy with the compare (one region computing i+1 < rounds from i) while the original add carries i
round the loop in parallel.  Same function, the same handshake protocol; a pre-pass on the frontend's MLIR, bdc
unchanged.  research/data/fifteen (lever 6).  Refuses if the expected lines are not exactly there.
"""
import re, sys
src = open(sys.argv[1]).read()
need = {
    "add": "    %29 = addi %7, %14 {handshake.bb = 1 : ui32, handshake.name = \"addi0\"} : <i32>\n",
    "fork": "    %30:2 = fork [2] %29 {handshake.bb = 1 : ui32, handshake.name = \"fork8\"} : <i32>\n",
    "cmp": "    %31 = cmpi slt, %30#1, %11#1 {handshake.bb = 1 : ui32, handshake.name = \"cmpi1\"} : <i32>\n",
}
for k, v in need.items():
    if src.count(v) != 1: sys.exit("dup_add: expected line not found once: %s" % k)
if src.count("%30#0") != 1 or src.count("%30#1") != 1: sys.exit("dup_add: %30 is read elsewhere")
src = src.replace(need["add"],
    "    %7d:2 = fork [2] %7 {handshake.bb = 1 : ui32, handshake.name = \"forkdup0\"} : <i32>\n"
    "    %29 = addi %7d#0, %14 {handshake.bb = 1 : ui32, handshake.name = \"addi0\"} : <i32>\n"
    "    %14s = source {handshake.bb = 1 : ui32, handshake.name = \"sourcedup0\"} : <>\n"
    "    %14d = constant %14s {handshake.bb = 1 : ui32, handshake.name = \"constantdup0\", value = 1 : i32} : <>, <i32>\n"
    "    %29d = addi %7d#1, %14d {handshake.bb = 1 : ui32, handshake.name = \"addidup0\"} : <i32>\n")
src = src.replace(need["fork"], "")
src = src.replace(need["cmp"], "    %31 = cmpi slt, %29d, %11#1 {handshake.bb = 1 : ui32, handshake.name = \"cmpi1\"} : <i32>\n")
src = src.replace("%30#0", "%29")
# %7 must now have exactly one reader: the new fork
uses = [l for l in src.splitlines() if re.search(r"%7\b(?![d:])", l) and not l.lstrip().startswith("%7 =")]
if len(uses) != 1 or "forkdup0" not in uses[0]: sys.exit("dup_add: %7 has other readers: %s" % uses)
open(sys.argv[2], "w").write(src)
