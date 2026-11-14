#!/usr/bin/env python3
"""farm_table.py REQUEST -- one row per task of a farm eval_task.sh request (origin/claude/cluster), then a summary:
period median / mean / best / worst, gate passes, routes CLEAN in the static check at both corners."""
import subprocess, re, sys, statistics as st
req = sys.argv[1]
def show(p):
    r = subprocess.run(['git', 'show', 'origin/claude/cluster:' + p], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None
rows = ["seed\tsdf\tperiod_ps\todata\tequiv\tstatic_nom\tstatic_worst\tgate_max\tgate_min\tgate_worst"]
P = []; gp = gn = 0; clean = 0; built = 0
for t in range(1, 257):
    e = show(f'results/{req}/{t}/eval.txt')
    if e is None:
        if show(f'results/{req}/{t}/log.txt') is None: continue
        rows.append(f"{t}\t-\tNO-EVAL\t-\t-\t-\t-\t-\t-\t-"); continue
    b = re.search(r'build \S+ (\S+) P=(\S+) (odata=\S+)?\s*VERDICT: ([A-Z ]+?)\s+ffmux', e)
    if not b:
        rows.append(f"{t}\t-\tBUILD-FAILED\t-\t-\t-\t-\t-\t-\t-"); continue
    built += 1
    sn = re.search(r'static nom (.*?) \|', e); sw = re.search(r'static worst (.*?) \|', e)
    g = {}
    for c in ('max', 'min', 'worst'):
        m = re.search(rf'gate {c} (\S+ \S+)', e); g[c] = m.group(1) if m else 'NA'
        if m: gn += 1; gp += m.group(1).startswith('PASS')
    if b.group(2).isdigit(): P.append(int(b.group(2)))
    snv = sn.group(1) if sn else 'NA'; swv = sw.group(1) if sw else 'NA'
    clean += (snv == 'CLEAN' and swv == 'CLEAN')
    rows.append(f"{t}\t{b.group(1)}\t{b.group(2)}\t{b.group(3)}\t{b.group(4)}\t{snv}\t{swv}\t{g['max']}\t{g['min']}\t{g['worst']}")
print("\n".join(rows))
if P:
    print(f"# {req}: {built} routes built; period median {st.median(P)/1e3:.2f} mean {st.mean(P)/1e3:.2f} best {min(P)/1e3:.2f} "
          f"worst {max(P)/1e3:.2f} ns; gate {gp}/{gn} PASS; static CLEAN at both corners on {clean}/{built}")
