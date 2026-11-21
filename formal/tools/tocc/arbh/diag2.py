# unbounded relative Up: follow one blocker chain down through anchors until a terminal reason
import sys, os, threading
sys.argv = ["ao.py", sys.argv[1] if len(sys.argv) > 1 else "1", "0"]
src = open("/tmp/claude-0/arbh/ao.py").read(); src = src[:src.index("# ---------------- rounds")]
exec(src)
os.environ["RELD"] = "99"
exec(open("/tmp/claude-0/arbh/relup.py").read())
sys.setrecursionlimit(100000); threading.stack_size(512 * 1024 * 1024)
r = {nm[n]: n for n in EX}
def ev_(s): n, k = s.rsplit("(", 1); return eid[(r[n], int(k[:-1]))]
def s_(e): return "%s(%d)@%d%s" % (nm[el[e][0]], el[e][1], el[e][2], "[ENV]" if el[e][0] in envnode else "")
E = ev_(os.environ.get("EE", "SLICE_X39Y47.D6(1)"))
e0 = ev_(os.environ.get("E0", "SLICE_X27Y80.A6(2)"))
D = 99
def first_block(e0, e):
    """walk e's derivation from e0: return (event x >= e0 in tm with no entry, blocked cause/prev p)"""
    U = _extend(e0, D, int(tm[e]))["U"]
    x = e; seen = set()
    while True:
        seen.add(x)
        v, k, t = el[x]
        if v in envnode or v not in g: return (x, None, "x is env/non-gate")
        cand = []
        if k > 0 and _term(prev[x], e0, D, U, whi(v, v)) is None: cand.append(prev[x])
        ab = [[p for p in alt if _term(p, e0, D, U, whi(v, el[p][0])) is None] for alt in alts[x]]
        if all(ab) and ab: cand += min(ab, key=len)
        nxt = [p for p in cand if tm[p] >= tm[e0] and p not in U and p not in seen]
        if nxt: x = nxt[0]; continue
        return (x, cand[0] if cand else None, "alts" if not cand else "")
def main():
    cur0, cur = e0, E
    for lvl in range(30):
        x, p, why = first_block(cur0, cur)
        print("L%d e0=%s target=%s: blocked at %s by %s %s" % (lvl, s_(cur0), s_(cur), s_(x), s_(p) if p is not None else None, why))
        if p is None: break
        if p is not None and el[p][0] in envnode: print("   ENV cause; Sep23(p->e0)", sep23(p, cur0)); 
        an = _anchors(p, cur0)[:RELTRY]
        info = [(s_(a), sep23(a, cur0)) for a in an]
        good = [a for a in an if sep23(a, cur0) is not None]
        print("   anchors with Sep23 to e0: %d of %d; first: %s" % (len(good), len(an), info[:3]))
        if not good: break
        cur0, cur = good[0], p
th = threading.Thread(target=main); th.start(); th.join()
