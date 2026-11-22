#!/usr/bin/env python3
"""table.py REQUEST [B_CENSUS_LINES]  (shard C, 2026-11-22; untrusted): one markdown row per task of a farm request that ran
drawspec.sh (origin/claude/cluster results/fm_REQUEST/N/line.txt): route, sdf, trimmed fasm, model draws, slow-carry draws,
the SWEEP stress points; with shard B's census_lines.txt, B's weakest steer bound and adversary beside it."""
import re, subprocess, sys
req = sys.argv[1]
def show(p):
    r = subprocess.run(["git", "show", "origin/claude/cluster:results/fm_%s/%s" % (req, p)], capture_output=True, text=True)
    return r.stdout if r.returncode == 0 else None
B = {}
if len(sys.argv) > 2:
    for l in open(sys.argv[2]):
        f = [x.strip() for x in l.split("|")]
        if len(f) > 4:
            kl = re.search(r"min kappa_lo (-?[0-9.]+)", l); ad = re.search(r"adversary first failure:? ([^|]*)", l)
            B[f[0]] = ((kl.group(1) if kl else "?"), (ad.group(1).strip()[:30] if ad else "?"))
print("| route | sdf / trimmed fasm | model draws | slow-carry | sarc x3 | x4 | x5 | B kappa_lo | B adversary |")
print("|---|---|---|---|---|---|---|---|---|")
t = 1
while True:
    task = show("%d/task.txt" % t)
    if task is None: break
    line = show("%d/line.txt" % t) or "(no line: %s)" % (show("%d/log.txt" % t) or "")[-80:].replace("\n", " ")
    name = task.strip().split("/")[-1].replace(".spec", "")
    ids = re.search(r"sdf ([0-9a-f]{8}),? (?:\(research [0-9a-f]+\) [A-Z]+ \| fasm |trimmed fasm )([0-9a-f]{8})", line)
    d = re.findall(r"(?:PASS (\d+) FAIL (\d+) UNDECIDED (\d+))", line)
    dd = ["%s/%s" % (p, int(p) + int(f) + int(u)) + (" (%s und.)" % u if u != "0" else "") for p, f, u in d[:2]]
    sw = re.findall(r"sarc [0-9.]+: fail (\d+) / (\d+) \(hang / undecided (\d+)\)", line)
    sws = ["%s/%s" % (f, n) for f, n, h in sw]
    bk = B.get(name, ("", ""))
    print("| %s | %s | %s | %s | %s | %s | %s | %s | %s |" % (name, "%s / %s" % ids.groups() if ids else line[:60].replace("|", "/"),
          *(dd + ["", ""])[:2], *(sws + ["", "", ""])[:3], bk[0], bk[1]))
    t += 1
