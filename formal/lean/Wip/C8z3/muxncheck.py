"""C-8z3: which gates of the 3-way mux (bd_muxn3) are persistent over its reachable table
(OpsMuxN.TB), under the same step constraints as OpsMuxN.ClosedAt. Untrusted."""
import os, re, itertools
src = open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", "Formal", "Net", "OpsMuxN.lean")).read()
TB = int(re.search(r"def TB : Nat := (0x[0-9a-f]+)", src).group(1), 16)
B = [False, True]
def code(r, a, cr, ca, zr, za, j, s):
    return (sum(int(r[k]) << k for k in range(3)) + sum(int(a[k]) << (3 + k) for k in range(3)) +
            64 * cr + 128 * ca + 256 * zr + 512 * za + sum(int(j[k]) << (10 + k) for k in range(3)) + 8192 * s)
def mem(*x): return (TB >> (8 * code(*x))) % 256 % 2 == 1
bad = {}; n = 0
for r in itertools.product(B, repeat=3):
  for a in itertools.product(B, repeat=3):
    for cr, ca, zr, za in itertools.product(B, repeat=4):
      for j in itertools.product(B, repeat=3):
        for s in range(4):
          if not mem(r, a, cr, ca, zr, za, j, s): continue
          n += 1
          for r2 in itertools.product(B, repeat=3):
            if any(r2[k] != r[k] and r[k] != a[k] for k in range(3)): continue
            for cr2, za2, zr2, ca2 in itertools.product(B, repeat=4):
              if cr2 != cr and cr != ca: continue
              if za2 != za and za == zr: continue
              if zr2 != zr and zr2 != (j[0] or j[1] or j[2]): continue
              if ca2 != ca and ca2 != za: continue
              for j2 in itertools.product(B, repeat=3):
                if any(j2[k] != j[k] and not (r[k] == j2[k] and (cr and s == k) == j2[k]) for k in range(3)): continue
                for a2 in itertools.product(B, repeat=3):
                  if any(a2[k] != a[k] and not (j[k] == a2[k] and za == a2[k]) for k in range(3)): continue
                  for s2 in range(4):
                    if s2 != s and (cr or ca) and (cr2 or ca2): continue
                    for v in B:
                      for k in range(3):
                        if r[k] == v and (cr and s == k) == v and j[k] != v and not ((r2[k] == v and (cr2 and s2 == k) == v) or j2[k] == v):
                          bad.setdefault(("j", k, v), (r, a, cr, ca, zr, za, j, s))
                        if j[k] == v and za == v and a[k] != v and not ((j2[k] == v and za2 == v) or a2[k] == v):
                          bad.setdefault(("ack", k, v, "za2=%s" % za2), (r, a, cr, ca, zr, za, j, s))
                      if (j[0] or j[1] or j[2]) == v and zr != v and not ((j2[0] or j2[1] or j2[2]) == v or zr2 == v):
                        bad.setdefault(("zr", v), 1)
                      if za == v and ca != v and not (za2 == v or ca2 == v):
                        bad.setdefault(("ca", v), 1)
print("reachable states", n)
for k, v in sorted(bad.items()): print(k, v)
