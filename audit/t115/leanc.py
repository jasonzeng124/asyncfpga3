#!/usr/bin/env python3
"""T115 (audit, own tool): compile a set of formal modules (and their Formal.* import closure) with the auditor's own
Lean, without lake, into OUT (oleans), in dependency order; then run an axiom report on named theorems.
usage: leanc.py PROJECT_DIR OUT_DIR MODULE [MODULE ...] -- THEOREM [THEOREM ...]"""
import os, re, sys, subprocess
proj, out = sys.argv[1], sys.argv[2]
args = sys.argv[3:]; k = args.index('--'); mods, thms = args[:k], args[k+1:]
LEAN = '/root/audit-lean/lean-4.35.0-linux/bin/lean'
def path(m): return os.path.join(proj, m.replace('.', '/') + '.lean')
order, seen = [], set()
def visit(m):
    if m in seen or not os.path.exists(path(m)): return
    seen.add(m)
    for l in open(path(m)):
        mm = re.match(r'import\s+(\S+)', l)
        if mm: visit(mm[1])
    order.append(m)
for m in mods: visit(m)
env = dict(os.environ, LEAN_PATH=out)
for m in order:
    o = os.path.join(out, m.replace('.', '/') + '.olean'); os.makedirs(os.path.dirname(o), exist_ok=True)
    if os.path.exists(o) and os.path.getmtime(o) > os.path.getmtime(path(m)): continue
    r = subprocess.run([LEAN, path(m), '-o', o], env=env, capture_output=True, text=True)
    bad = [l for l in (r.stdout + r.stderr).splitlines() if 'error' in l or 'sorry' in l]
    print(f"{m}: rc={r.returncode}" + (" " + " | ".join(bad[:3]) if bad else ""), flush=True)
    if r.returncode: sys.exit(1)
chk = os.path.join(out, 'Audit_axioms.lean')
open(chk, 'w').write("\n".join(f"import {m}" for m in mods) + "\n" + "\n".join(f"#print axioms {t}" for t in thms) + "\n")
r = subprocess.run([LEAN, chk], env=env, capture_output=True, text=True)
print(r.stdout + r.stderr)
