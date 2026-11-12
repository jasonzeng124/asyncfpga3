import os, re, sys, json
ROOT = "/home/user/asyncfpga3/formal/lean"
mods = {}
for d, _, fs in os.walk(os.path.join(ROOT, "Formal")):
    for f in fs:
        if f.endswith(".lean"):
            p = os.path.relpath(os.path.join(d, f), ROOT)
            m = p[:-5].replace("/", ".")
            imps = []
            for line in open(os.path.join(ROOT, p)):
                mm = re.match(r"\s*import\s+(.*)", line)
                if mm:
                    imps += mm.group(1).split()
            mods[m] = imps
dep = {}
def reaches(m):
    if m in dep: return dep[m]
    dep[m] = False
    r = any(i == "Formal.Cells.Prelim" or (i in mods and reaches(i)) for i in mods.get(m, []))
    dep[m] = r
    return r
MC = {}
def mlc(m):
    if m in MC: return MC[m]
    MC[m] = False
    r = any(i.split(".")[0] in ("Mathlib", "Batteries") for i in mods[m]) or any(mlc(i) for i in mods[m] if i in mods)
    MC[m] = r
    return r
cl = sorted(m for m in mods if m != "Formal.Cells.Prelim" and reaches(m))
json.dump({"closure": cl, "imports": {m: mods[m] for m in cl}}, open("/tmp/claude-0/probes/Bpd/closure.json", "w"), indent=1)
for m in cl:
    print(m, "DIRECT" if "Formal.Cells.Prelim" in mods[m] else "-", "ML" if mlc(m) else "core")
