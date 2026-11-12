#!/usr/bin/env python3
"""vcd_norm.py A.vcd B.vcd -- compare two VCDs signal by signal: identifier
codes and the header (date, parameters) are ignored; every wire/reg's full
value-change history is compared by hierarchical name.  Exit 0 = identical."""
import hashlib, sys


def norm(path):
    scope, names, hist, t = [], {}, {}, 0
    with open(path) as f:
        for line in f:
            w = line.split()
            if not w:
                continue
            if w[0] == "$scope":
                scope.append(w[2])
            elif w[0] == "$upscope":
                scope.pop()
            elif w[0] == "$var":
                if w[1] in ("wire", "reg"):
                    names.setdefault(w[3], []).append(".".join(scope + [w[4]]))
            elif w[0][0] == "#":
                t = int(w[0][1:])
            elif w[0][0] in "01xzXZ" and len(w) == 1 and w[0][1:] in names:
                for n in names[w[0][1:]]:
                    hist.setdefault(n, []).append((t, w[0][0]))
            elif w[0][0] in "bB" and len(w) == 2 and w[1] in names:
                for n in names[w[1]]:
                    hist.setdefault(n, []).append((t, w[0]))
    return hist


a, b = norm(sys.argv[1]), norm(sys.argv[2])
common = set(a) & set(b)
diff = [n for n in common if a[n] != b[n]]
ev = sum(len(a[n]) for n in common)
print("signals: %d in A, %d in B, %d common, %d value changes compared, %d differ"
      % (len(a), len(b), len(common), ev, len(diff)))
for n in sorted(set(a) ^ set(b))[:10]:
    print("  only in one:", n)
for n in sorted(diff)[:10]:
    print("  DIFF", n)
sys.exit(1 if diff else 0)
