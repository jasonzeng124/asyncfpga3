#!/usr/bin/env python3
"""pre_dec.py IN.mlir OUT.mlir -- xorshift only: the loop test reads i, not i + 1.

    %29 = addi %7, %14 ; %30:2 = fork %29 ; %31 = cmpi slt, %30#1, %11#1     (i + 1 < n, n round the rounds ring)
becomes
    bb0: %1d = addi %1#0, -1 (from a source/constant) feeds cond_br4: the rounds ring carries m = n - 1
    %7f:2 = fork %7 ; %29 = addi %7f#0, %14 (read only by cond_br6) ; %31 = cmpi slt, %7f#1, %11#1   (i < m)
so the compare starts with the add instead of after it.  Exact on every reachable state: the loop is entered only when
n > 0 (cmpi0: n sgt 0), so m = n - 1 does not wrap, and i + 1 <= n <= INT_MAX inside the loop, so i + 1 < n <=> i < m.
The ring's value is read only by the compare (%11#1) and the ring itself (%11#0 -> cond_br8), and leaves only to a
sink (%falseResult_3, %falseResult_11), so no other user sees m.  Same handshake protocol; a pre-pass on the
frontend's MLIR (MLIR_OVERRIDE), bdc unchanged.  Refuses unless the expected lines are there exactly once.
"""
import re, sys
src = open(sys.argv[1]).read()
need = {
    "add": '    %29 = addi %7, %14 {handshake.bb = 1 : ui32, handshake.name = "addi0"} : <i32>\n',
    "fork": '    %30:2 = fork [2] %29 {handshake.bb = 1 : ui32, handshake.name = "fork8"} : <i32>\n',
    "cmp": '    %31 = cmpi slt, %30#1, %11#1 {handshake.bb = 1 : ui32, handshake.name = "cmpi1"} : <i32>\n',
    "br4": '    %trueResult_2, %falseResult_3 = cond_br %4#2, %1#0 {handshake.bb = 0 : ui32, handshake.name = "cond_br4"} : <i1>, <i32>\n',
    "sink1": '    sink %falseResult_3 {handshake.name = "sink1"} : <i32>\n',
    "sink3": '    sink %falseResult_11 {handshake.name = "sink3"} : <i32>\n',
    "br8": '    %trueResult_10, %falseResult_11 = cond_br %32#1, %11#0 {handshake.bb = 1 : ui32, handshake.name = "cond_br8"} : <i1>, <i32>\n',
    "mux2": '    %10 = mux %12#2 [%trueResult_2, %trueResult_10] {handshake.bb = 1 : ui32, handshake.name = "mux2"} : <i1>, [<i32>, <i32>] to <i32>\n',
}
for k, v in need.items():
    if src.count(v) != 1: sys.exit("pre_dec: expected line not found once: %s" % k)
for tok, n in (("%30#0", 1), ("%30#1", 1), ("%11#0", 1), ("%11#1", 1), ("%1#0", 1), ("%falseResult_3", 2), ("%falseResult_11", 2)):
    if len(re.findall(re.escape(tok) + r"\b", src)) != n: sys.exit("pre_dec: %s is read elsewhere" % tok)
src = src.replace(need["br4"],
    '    %1s = source {handshake.bb = 0 : ui32, handshake.name = "sourcedec0"} : <>\n'
    '    %1c = constant %1s {handshake.bb = 0 : ui32, handshake.name = "constantdec0", value = -1 : i32} : <>, <i32>\n'
    '    %1d = addi %1#0, %1c {handshake.bb = 0 : ui32, handshake.name = "addidec0"} : <i32>\n'
    + need["br4"].replace("%4#2, %1#0", "%4#2, %1d"))
src = src.replace(need["add"],
    '    %7f:2 = fork [2] %7 {handshake.bb = 1 : ui32, handshake.name = "forkdec0"} : <i32>\n'
    + need["add"].replace("addi %7,", "addi %7f#0,"))
src = src.replace(need["fork"], "")
src = src.replace(need["cmp"], need["cmp"].replace("%30#1", "%7f#1"))
src = src.replace("%30#0", "%29")
uses = [l for l in src.splitlines() if re.search(r"%7\b(?![fd:])", l) and not l.lstrip().startswith("%7 =")]
if len(uses) != 1 or "forkdec0" not in uses[0]: sys.exit("pre_dec: %7 has other readers: %s" % uses)
open(sys.argv[2], "w").write(src)
