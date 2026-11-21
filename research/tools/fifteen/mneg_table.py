#!/usr/bin/env python3
"""mneg_table.py [REQUEST] -- the rule-M negative-control table from farm request mneg (origin/claude/cluster): per
task (route, mux) and injection size, the injected mux's rule-M row (worst / nom; the A rows marked "peers no common
source reaches"), whether rule E had any row below 0, and the gate at FAST_MIN / worst. Then the count of gate failures
with and without an M row below 0 on the injected mux."""
import subprocess, sys
req = sys.argv[1] if len(sys.argv) > 1 else 'mneg'
def show(p):
    r = subprocess.run(['git', 'show', 'origin/claude/cluster:' + p], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None
fam = {'x27': 'xorshift item 27 s2', 'c64_26': 'collatz64 item 26 s25', 'ip19': 'ipow item 19 s1', 'c28': 'collatz item 28 s20'}
print("| route, mux | inj | rule M on that mux, worst / nom | rule E rows < 0 | gate FAST_MIN | gate worst |")
print("|---|---|---|---|---|---|")
fails = flagged = 0; strict = 0
for t in range(1, 15):
    f = show(f'results/{req}/{t}/task.txt')
    if not f: continue
    h = f.splitlines()[0].split(); F, M = h[1], h[7]
    for P in ('4000', '8000'):
        m = {}; e = 0; g = {}
        for l in f.splitlines():
            w = l.split()
            if l.startswith('inj M +' + P) and len(w) >= 6 and w[5] == M:
                m[w[3]] = min(m.get(w[3], int(w[4])), int(w[4]))
            if l.startswith('inj E +' + P): e += 1
            if l.startswith('gate_inj +' + P):
                g[w[2]] = 'no completion' if w[3].startswith('TIMEOUT') else ' '.join(w[3:5])
        if not g: continue
        fail = any(not v.startswith("PASS") for v in g.values()); fl = any(v < 0 for v in m.values())
        fails += fail; flagged += fail and fl; strict += (not fail) and fl
        print(f"| {fam.get(F, F)}, {M} | +{P} | {m.get('worst', '-')} / {m.get('nom', '-')} | {e} | {g.get('min', '--')} | {g.get('worst', '--')} |")
print(f"\nruns with a gate failure: {fails}; rule M below 0 on the injected mux in {flagged} of them; M below 0 but every gate passed: {strict}")
