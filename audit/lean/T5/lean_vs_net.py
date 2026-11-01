#!/usr/bin/env python3
"""Audit T5: parse the COMMITTED generated Lean data (Formal/Target/Net/*.lean at formal 6f094d32, extracted with
`git show`) with my own parser and compare every gate and node name with the auditor's own decoder run
(/root/t4work2/net.json, audit T4). Also resolve `arbs` and `boundary` indices to node names.
usage: python3 -I lean_vs_net.py NETDIR net.json [seed]"""
import json, re, sys, os, random
D, NJ = sys.argv[1], sys.argv[2]
seed = int(sys.argv[3]) if len(sys.argv) > 3 else 5
strre = r'"((?:[^"\\]|\\.)*)"'
P = re.compile(r'^\s*P ' + strre + r' (\d+) (\d+) (\d+) (\d+) (\d+) (\d+)[,\]]\s*$')
G = re.compile(r'^\s*⟨' + strre + r', (\d+), (\d+), \[([0-9, ]*)\], \[(.*)\], (\d+)⟩[,\]]\s*$')
A = re.compile(r'⟨(\d+), (\d+), (\d+), (\d+)⟩')
gates = []
for c in range(80):
    txt = open(os.path.join(D, "G%03d.lean" % c)).read().splitlines()
    n0 = len(gates)
    for ln in txt:
        m = P.match(ln)
        if m:
            nm, i, o, a, b, cc, d = m.groups()
            gates.append((nm, 1, 2, [int(i)], [(int(a), int(b), int(cc), int(d))], int(o)))
            continue
        m = G.match(ln)
        if m:
            nm, k, init, ins, arcs, o = m.groups()
            gates.append((nm, int(k), int(init), [int(x) for x in ins.split(",") if x.strip()],
                          [tuple(map(int, t)) for t in A.findall(arcs)], int(o)))
            continue
        if ln.startswith("  ") and ("⟨" in ln or ln.lstrip().startswith("P ")):
            sys.exit("unparsed gate line in G%03d: %s" % (c, ln[:120]))
    mlen = re.search(r"theorem g%03d_len : g%03d.length = (\d+)" % (c, c), "\n".join(txt))
    assert mlen and int(mlen.group(1)) == len(gates) - n0, c
names = []
ntxt = open(os.path.join(D, "Nodes.lean")).read()
parts = re.findall(r'def (n\d\d) : List String := \[(.*?)\]\n', ntxt, re.S)
order = re.search(r'def names : List String := (.*)', ntxt).group(1).split(" ++ ")
pd = {k: v for k, v in parts}
for k in order:
    names += [s.encode().decode("unicode_escape") if "\\" in s else s for s in re.findall(strre, pd[k.strip()])]
N = json.load(open(NJ))
print("Lean: %d gates, %d node names; net.json: %d gates, %d nodes" % (len(gates), len(names), len(N["gates"]), len(N["nodes"])))
alltxt = open(os.path.join(D, "All.lean")).read()
print("All.lean net.n:", re.search(r"def net : Net := ⟨(\d+),", alltxt).group(1), " nGates:", re.search(r"def nGates : Nat := (\d+)", alltxt).group(1))
print("node names: Lean order == net.json order:", names == N["nodes"], "; same multiset:", sorted(names) == sorted(N["nodes"]), "; distinct:", len(set(names)) == len(names))
JN = N["nodes"]
def lt(g): return (g[0], g[1], g[2], [names[i] for i in g[3]], g[4], names[g[5]])
def jt(jg): return (jg["name"], jg["k"], jg["init"], [JN[i] for i in jg["ins"]], [(a["fmin"], a["fmax"], a["smin"], a["smax"]) for a in jg["arcs"]], JN[jg["out"]])
jby = {}
for jg in N["gates"]: jby[JN[jg["out"]]] = jg
diff = 0
for idx, lg in enumerate(gates):
    jg = jby.get(names[lg[5]])
    if jg is None or lt(lg) != jt(jg):
        diff += 1
        if diff < 5: print("DIFF gate", idx, lt(lg), jg and jt(jg))
tilde = [g for g in gates if g[0].startswith("~")]
d2 = sum(1 for g in gates if (lambda jg: (g[0].lstrip("~"),) + lt(g)[1:] != jt(jg))(jby[names[g[5]]]))
tp = sum(1 for g in tilde if (jby[names[g[5]]].get("prov") or {}).get("pseudo") is True)
print("Lean names with '~' prefix: %d (json prov.pseudo=True for %d of them); json pseudo pips total: %d" % (len(tilde), tp, sum(1 for jg in N["gates"] if (jg.get("prov") or {}).get("pseudo") is True)))
print("differences ignoring a leading '~' in the name: %d" % d2)
print("gate-by-gate by output-node name (name,k,init,input names,arcs,output name) differences: %d of %d; json gates matched: %d" % (diff, len(gates), len(jby)))
print("gate i drives node i:", all(g[5] == i for i, g in enumerate(gates)))
random.seed(seed)
print("20 random gates (Lean vs net.json):")
for idx in sorted(random.sample(range(len(gates)), 20)):
    g = gates[idx]; jg = jby[names[g[5]]]
    print("  Lean#%d %s k=%d init=%d ins=%s arcs=%s -> %s | json kind=%s equal=%s" % (
        idx, g[0][:60], g[1], g[2], [names[i] for i in g[3]][:2], g[4][:2], names[g[5]], jg["kind"], lt(g) == jt(jg)))
arbs = [(int(q), [int(x) for x in ins.split(",")]) for q, ins in re.findall(r"⟨(\d+), \[([0-9, ]+)\]⟩", alltxt.split("def arbs")[1].split("theorem net_wf")[0])]
json.dump({"arbs": [{"q": names[q], "qi": q, "ins": [names[i] for i in ins], "insi": ins} for q, ins in arbs]},
          open(os.path.join(os.path.dirname(os.path.abspath(__file__)), "lean_arbs.json"), "w"), indent=1)
print("arbs (%d):" % len(arbs))
for q, ins in arbs: print("  q=%d %s ins=%s" % (q, names[q], [names[i] for i in ins]))
