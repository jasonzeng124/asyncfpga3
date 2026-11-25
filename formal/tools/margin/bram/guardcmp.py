#!/usr/bin/env python3
"""margin/bram/guardcmp.py [REQ...] [--ref origin/claude/cluster] (shard C): research's C64 question -- which guard form
the draws support -- as one table over the farm results of c_mem24..31 (memtask with the hostrace step): per route the
sdf check, the draws (PASS / FAIL of 16 + 16), the draws' smallest RAM setup margin (any RAM, any phase), and
hostrace's smallest host-write setup slack at mid band, plain, skew.py-guarded (x0.772 clock / x1.155 payload) and
-400 ps (rule B's additive form). A guard form is contradicted by a route it calls negative whose draws never come near
failing, or by a route it calls positive that fails. Caveat: the draws' minimum is over every RAM edge, hostrace's over
the host's writes only."""
import argparse, re, subprocess
ap = argparse.ArgumentParser(); ap.add_argument("reqs", nargs="*", default=["fm_c_mem%d" % i for i in range(24, 32)])
ap.add_argument("--ref", default="origin/claude/cluster"); a = ap.parse_args()
git = lambda *x: subprocess.run(["git"] + list(x), capture_output=True, text=True).stdout
rows = []
for rq in a.reqs:
    for p in git("ls-tree", "--name-only", a.ref, "results/%s/" % rq).split():
        if not re.search(r"/\d+$", p): continue
        s = git("show", "%s:%s/summary.txt" % (a.ref, p))
        if not s: continue
        h = s.splitlines()[0].split()
        m = re.search(r"sdf (\w+) \(research (\w+)\) (SAME|DIFFERENT)", s)
        d = re.findall(r"draws \d+: PASS (\d+) FAIL (\d+) UNDECIDED (\d+)", s)
        hr = re.search(r"min slack (-?\d+) ps, guarded \S+ (-?\d+) ps, -400 (-?\d+) ps; draws' min RAM setup margin (-?\d+|\?)", s)
        rows.append((h[0], h[1], m.group(2) if m else "?", m.group(3) if m else "NO-BUILD",
                     "%d/%d" % (sum(int(x[0]) for x in d), sum(int(x[0]) + int(x[1]) + int(x[2]) for x in d)) if d else "-",
                     sum(int(x[1]) for x in d), hr.groups() if hr else None))
print("%-20s %-4s %-8s %-9s %-7s %6s %8s %8s %8s" % ("kernel", "seed", "sdf", "check", "pass", "drawMin", "plain", "x.772/1.155", "-400"))
for k, s, sdf, chk, ps, nf, hr in sorted(rows, key=lambda r: (int(r[6][1]) if r[6] else 1 << 30)):
    v = (hr[3], hr[0], hr[1], hr[2]) if hr else ("-",) * 4
    print("%-20s %-4s %-8s %-9s %-7s %6s %8s %8s %8s" % ((k, s, sdf, chk, ps) + tuple(v)))
ok = [r for r in rows if r[6] and r[3] == "SAME"]
print("\n%d routes with hostrace + SAME; %d with a failing draw" % (len(ok), sum(1 for r in ok if r[5])))
for lab, i in (("plain", 0), ("x0.772/x1.155", 1), ("-400", 2)):
    neg = [r for r in ok if int(r[6][i]) < 0]
    print("%-14s negative on %3d routes (%d of them with a failing draw); positive on %3d (%d with a failing draw)"
          % (lab, len(neg), sum(1 for r in neg if r[5]), len(ok) - len(neg), sum(1 for r in ok if r[5] and int(r[6][i]) >= 0)))
