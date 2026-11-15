#!/usr/bin/env python3
"""pre_eq2.py IN.mlir OUT.mlir -- collatz / collatz64: the loop test reads n, not the updated n.

The kernel (kernels/collatz*/): n' = (n & 1) == 0 ? n >> 1 : 3 * n + 1, exit when n' == 1.  In w-bit two's
complement (w = 32 or 64, arithmetic shift):
  n even: n >> 1 == 1  <=>  n in {2, 3}  <=>  n == 2 (even);
  n odd : 3n + 1 == 1  <=>  3n == 0 (mod 2^w)  <=>  n == 0 (3 is odd, so invertible mod 2^w) -- not odd: never.
So n' == 1 <=> n == 2, on every input.  The compare then starts with the update instead of after it.
Rewrite: cmpi2 = cmpi eq, <fork7 out>, <const 1>  ->  cmpi eq, <fork3 new out>, <new const 2>; fork7 (n' to the
compare and the loop-back steer) is removed, cond_br7 reads n' directly; the freed const-1 fork output is sunk.
Same handshake protocol; MLIR_OVERRIDE pre-pass, bdc unchanged.  Refuses unless the expected shapes are there.
"""
import re, sys
src = open(sys.argv[1]).read()
def one(pat):
    m = re.findall(pat, src, re.M)
    if len(m) != 1: sys.exit("pre_eq2: expected exactly one match: " + pat)
    return m[0]
ty = one(r'handshake\.name = "cmpi2"\} : <(i\d+)>')
# fork3: the loop value n
f3 = one(r'^    (%\d+):(\d+) = fork \[\d+\] (%\S+) \{handshake\.bb = 1 : ui32, handshake\.name = "fork3"\} : <' + ty + '>$')
f7 = one(r'^    (%\d+):2 = fork \[2\] (%\d+) \{handshake\.bb = 1 : ui32, handshake\.name = "fork7"\} : <' + ty + '>$')
cm = one(r'^    (%\d+) = cmpi eq, (%\d+#\d+), (%\d+#\d+) \{handshake\.bb = 1 : ui32, handshake\.name = "cmpi2"\} : <' + ty + '>$')
v3, n3, x3 = f3; v7, x7 = f7; vc, a, cst = cm
if a != v7 + "#1": sys.exit("pre_eq2: cmpi2 does not read fork7#1")
# the constant really is 1: find the fork feeding cst and its constant
cf = one(r'^    ' + re.escape(cst.split("#")[0]) + r':\d+ = fork \[\d+\] (%\d+) ')
one(r'^    ' + re.escape(cf) + r' = constant %\S+ \{[^}]*value = 1 : ' + ty + r'\}')
if len(re.findall(re.escape(v7) + r"#0\b", src)) != 1 or len(re.findall(re.escape(v7) + r"#1\b", src)) != 1:
    sys.exit("pre_eq2: fork7 read elsewhere")
n3 = int(n3)
old_f3 = '    %s:%d = fork [%d] %s {handshake.bb = 1 : ui32, handshake.name = "fork3"} : <%s>\n' % (v3, n3, n3, x3, ty)
if src.count(old_f3) != 1: sys.exit("pre_eq2: fork3 line")
src = src.replace(old_f3, old_f3.replace("%s:%d = fork [%d]" % (v3, n3, n3), "%s:%d = fork [%d]" % (v3, n3 + 1, n3 + 1))
    + '    %%eq2s = source {handshake.bb = 1 : ui32, handshake.name = "sourceeq2"} : <>\n'
    '    %%eq2c = constant %%eq2s {handshake.bb = 1 : ui32, handshake.name = "constanteq2", value = 2 : %s} : <>, <%s>\n' % (ty, ty))
src = re.sub(r'^    ' + re.escape(v7) + r':2 = fork \[2\] .*"fork7".*\n', '', src, flags=re.M)
src = src.replace('%s = cmpi eq, %s, %s {' % (vc, a, cst), '%s = cmpi eq, %s#%d, %%eq2c {' % (vc, v3, n3))
src = src.replace(v7 + "#0", x7)
# the constant-1 output the compare no longer reads
src = src.replace('    end {', '    sink %s {handshake.name = "sinkeq2"} : <%s>\n    end {' % (cst, ty), 1)
open(sys.argv[2], "w").write(src)
