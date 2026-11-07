"""kappa.py -- probe C-12d: C-10i's H_GRANT_FORK verdicts under A's corner model
(shared corner c in [0,1], local scatter kappa; Formal/Core/Delay/Corner.lean),
read from the committed, kernel-checked data file Formal/Timing/GrantForkInst.lean
(per element FMIN/FMAX/SMIN/SMAX point boxes; no routed inputs needed).

Per element e (the 8 routed quantities of one client), endpoints:
  lit   F = FMIN, S = SLOW_MAX;  d in [(1-k) D(c), (1+k) D(c)],  D(c) = lerp(F, S, c)
  cons  d in [(1-k) lerp(FMIN, SMIN, c), (1+k) lerp(FMAX, SMAX, c)]   (k = 0, c = 0/1:
        exactly C-10i's 'fast' / 'slow' boxes)
The transport window W is a signed sum of the 8 delays, so its maximum over the
box at corner c, Whi(c), is a sum of interval endpoints, each affine in c: Whi is
affine in c and max over [0,1] is at c = 0 or c = 1 (exact, rationals).  The
inertial check okI is evaluated at c in {0, 1/4, 1/2, 3/4, 1} (not affine: max/min).
Output: per instance x client the smallest kappa at which the fork race opens
(transport), for each reading, and counts at kappa = 0, 1/11, 383/1927.
Run: python3 -I kappa.py [path/to/GrantForkInst.lean]
"""
import re
import sys
from fractions import Fraction as Fr
from pathlib import Path

HERE = Path(__file__).resolve().parent
INST = HERE.parent.parent / "lean/Formal/Timing/GrantForkInst.lean"
F = ("dqg", "dqs", "drg", "drs", "agq", "agr", "asq", "asr")
SIGN = dict(dqg=1, agq=1, drs=1, asr=1, dqs=-1, asq=-1, drg=-1, agr=-1)
K11, KE = Fr(1, 11), Fr(383, 1927)


def parse(path):
    txt = Path(path).read_text()
    boxes = {}
    for m in re.finditer(r"def (\w+)_(fast|slow|FMIN|FMAX|SMIN|SMAX|sdf) : Box :=\s*\{(.*?)\}", txt, re.S):
        iv = dict((k, (int(a), int(b))) for k, a, b in re.findall(r"(\w+) := ⟨(-?\d+), (-?\d+)⟩", m.group(3)))
        boxes.setdefault(m.group(1), {})[m.group(2)] = iv
    return boxes


def ends(b, e):
    """(FMIN, FMAX, SMIN, SMAX) of element e, outward (lo of MIN boxes, hi of MAX boxes)."""
    return (b["FMIN"][e][0], b["FMAX"][e][1], b["SMIN"][e][0], b["SMAX"][e][1])


def box(b, c, k, rd):
    out = {}
    for e in F:
        fn, fx, sn, sx = ends(b, e)
        if rd == "lit":
            d = fn + c * (sx - fn)
            out[e] = ((1 - k) * d, (1 + k) * d)
        else:
            out[e] = ((1 - k) * (fn + c * (sn - fn)), (1 + k) * (fx + c * (sx - fx)))
    return out


def whi(bx):
    return sum(bx[e][1] if SIGN[e] > 0 else -bx[e][0] for e in F)


def okT(b, k, rd):
    return max(whi(box(b, Fr(0), k, rd)), whi(box(b, Fr(1), k, rd))) <= 0


def okI(b, k, rd):
    for c in (Fr(0), Fr(1, 4), Fr(1, 2), Fr(3, 4), Fr(1)):
        B = box(b, c, k, rd)
        lhs = B["dqg"][1] - (B["drg"][0] - B["drs"][1]) - max(0, B["dqs"][0] - max(B["asq"][1], B["asr"][1]) + 1)
        if not lhs < min(B["agq"][0], B["agr"][0]):
            return False
    return True


def kstar(b, rd, ok):
    """largest kappa in [0,1) with ok (bisection on rationals, 1e-4); None if fails at 0."""
    if not ok(b, Fr(0), rd):
        return None
    lo, hi = Fr(0), Fr(1)
    if ok(b, Fr(999, 1000), rd):
        return Fr(1)
    while hi - lo > Fr(1, 10000):
        mid = (lo + hi) / 2
        if ok(b, mid, rd):
            lo = mid
        else:
            hi = mid
    return lo


def main():
    boxes = parse(sys.argv[1] if len(sys.argv) > 1 else INST)
    rows = sorted(boxes)
    print(f"{len(rows)} instance-clients from {INST.name}")
    print("instance_client                 | W(c=0,k=0) W(c=1,k=0) | k* transport lit / cons | k* inertial lit / cons")
    tally = {}
    for r in rows:
        b = boxes[r]
        w0 = whi(box(b, Fr(0), Fr(0), "cons"))
        w1 = whi(box(b, Fr(1), Fr(0), "cons"))
        ks = []
        for chk in (okT, okI):
            for rd in ("lit", "cons"):
                ks.append(kstar(b, rd, chk))
                for kn, k in (("0", Fr(0)), ("1/11", K11), ("kE", KE)):
                    key = (chk.__name__, rd, kn)
                    tally[key] = tally.get(key, 0) + (1 if chk(b, k, rd) else 0)
        f = lambda x: "fail@0" if x is None else ("  >=1 " if x == 1 else f"{float(x):6.4f}")  # noqa: E731
        print(f"{r:31} | {float(w0):9.0f} {float(w1):9.0f} | {f(ks[0])} / {f(ks[1])} | {f(ks[2])} / {f(ks[3])}")
    print("\npassing instance-clients (of %d):" % len(rows))
    for chk in ("okT", "okI"):
        for rd in ("lit", "cons"):
            print(f"  {chk} {rd:4}: " + "  ".join(f"k={kn}: {tally[(chk, rd, kn)]}" for kn in ("0", "1/11", "kE")))


if __name__ == "__main__":
    main()
