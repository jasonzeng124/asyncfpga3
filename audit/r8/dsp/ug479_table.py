"""Auditor: research dsp_model.alu vs a literal transcription of UG479 Tables 2-13/2-14
(ALUMODE arithmetic and two-input logic tables), random 48-bit words."""
import sys, random
sys.path.insert(0, sys.argv[1]); import dsp_model
M = (1 << 48) - 1; random.seed(1)
arith = {0: lambda x, y, z, c: (z + x + y + c) & M, 1: lambda x, y, z, c: (-z + (x + y + c) - 1) & M,
         2: lambda x, y, z, c: (-z - x - y - c - 1) & M, 3: lambda x, y, z, c: (z - (x + y + c)) & M}
# logic (Y=0 rows / Y=all ones rows), UG479 Table 2-14
logic = {(4, 0): lambda x, z: x ^ z, (4, 2): lambda x, z: ~(x ^ z) & M, (5, 0): lambda x, z: ~(x ^ z) & M,
         (5, 2): lambda x, z: x ^ z, (6, 0): lambda x, z: ~(x ^ z) & M, (6, 2): lambda x, z: x ^ z,
         (7, 0): lambda x, z: x ^ z, (7, 2): lambda x, z: ~(x ^ z) & M,
         (12, 0): lambda x, z: x & z, (12, 2): lambda x, z: x | z, (13, 0): lambda x, z: x & ~z & M,
         (13, 2): lambda x, z: (x | ~z) & M, (14, 0): lambda x, z: ~(x & z) & M, (14, 2): lambda x, z: ~(x | z) & M,
         (15, 0): lambda x, z: (~x | z) & M, (15, 2): lambda x, z: ~x & z & M}
bad = 0
for _ in range(2000):
    x, y, z, c = random.getrandbits(48), random.getrandbits(48), random.getrandbits(48), random.getrandbits(1)
    for a, f in arith.items():
        bad += dsp_model.alu(x, y, z, a, c) != f(x, y, z, c)
    for (a, ym), f in logic.items():
        bad += dsp_model.alu(x, 0 if ym == 0 else M, z, a, 0) != f(x, z)
print("dsp_model.alu vs UG479 tables: %d mismatches over 2000 x %d checks" % (bad, len(arith) + len(logic)))
