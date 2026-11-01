#!/usr/bin/env python3
"""lean_cmp.py (audit T4): is the generated Lean netlist (gen_lean.py output) the decoder's net.json?

    python3 -I lean_cmp.py NET.json LEANDIR

Own parser of LEANDIR/{Nodes,G*,All}.lean (no formal/ import). Checks, gate by gate in order: name
(pseudo pips prefixed '~'), k, INIT, input node NAMES, output node NAME, arcs; node and gate counts; and
evaluates Net.WF's per-gate conditions and "gate i drives node i" in Python (what `decide +kernel`
must establish). Also scans the generated files for sorry / native_decide / axiom.
"""
import glob
import json
import os
import re
import sys


def main():
    net = json.load(open(sys.argv[1]))
    d = sys.argv[2]
    names = []
    for m in re.finditer(r'def n\d+ : List String := \[(.*?)\]\n', open(os.path.join(d, "Nodes.lean")).read(), re.S):
        names += json.loads("[" + m.group(1) + "]")
    gates = []
    files = sorted(glob.glob(os.path.join(d, "G*.lean")))
    bad_tok = []
    for f in files + [os.path.join(d, "All.lean"), os.path.join(d, "Nodes.lean")]:
        txt = open(f).read()
        for tok in ("sorry", "native_decide", "axiom", "admit", "implemented_by", "extern", "ofReduceBool"):
            if re.search(r"\b%s\b" % tok, txt):
                bad_tok.append((os.path.basename(f), tok))
    nthm = 0
    for f in files:
        txt = open(f).read()
        nthm += len(re.findall(r":= by decide \+kernel", txt))
        body = re.search(r"def g\d+ : List Gate := \[\n(.*?)\]\n\ntheorem", txt, re.S).group(1)
        for line in body.split("\n"):
            line = line.strip().rstrip(",")
            m = re.match(r'^P ("(?:[^"\\]|\\.)*") (\d+) (\d+) (\d+) (\d+) (\d+) (\d+)$', line)
            if m:
                gates.append((json.loads(m.group(1)), 1, 2, [int(m.group(2))], [tuple(int(m.group(i)) for i in (4, 5, 6, 7))],
                              int(m.group(3))))
                continue
            m = re.match(r'^⟨("(?:[^"\\]|\\.)*"), (\d+), (\d+), \[([\d, ]*)\], \[(.*)\], (\d+)⟩$', line)
            if not m:
                sys.exit("unparsed: " + line[:200])
            arcs = [tuple(map(int, a.split(","))) for a in re.findall(r"⟨([\d, ]+)⟩", m.group(5))]
            gates.append((json.loads(m.group(1)), int(m.group(2)), int(m.group(3)),
                          [int(x) for x in m.group(4).split(",") if x.strip()], arcs, int(m.group(6))))
    allt = open(os.path.join(d, "All.lean")).read()
    mnet = re.search(r"def net : Net := ⟨(\d+), names, gates⟩", allt)
    print("Lean: %d node names, %d gates, net.n = %s, decide+kernel theorems %d (3 per chunk x %d chunks)"
          % (len(names), len(gates), mnet.group(1) if mnet else None, nthm, len(files)))
    print("net.json: %d nodes, %d gates" % (len(net["nodes"]), len(net["gates"])))
    print("forbidden tokens in generated files:", bad_tok or "none")
    # gate-by-gate comparison by NAMES (gen_lean renumbers nodes)
    nn = net["nodes"]
    diff = 0
    for i, (g, l) in enumerate(zip(net["gates"], gates)):
        nm = ("~" + g["name"]) if g["kind"] == "pip" and g["prov"].get("pseudo") else g["name"]
        arcs = [(a["fmin"], a["fmax"], a["smin"], a["smax"]) for a in g["arcs"]]
        same = (l[0] == nm and l[1] == g["k"] and l[2] == g["init"] and [names[x] for x in l[3]] == [nn[x] for x in g["ins"]]
                and names[l[5]] == nn[g["out"]] and l[4] == arcs)
        if not same:
            diff += 1
            if diff <= 5:
                print("DIFF gate %d: lean %s / net %s" % (i, l[:3], (nm, g["k"], g["init"])))
    print("gate-by-gate (name, k, INIT, input names, output name, arcs): %d differences of %d" % (diff, len(gates)))
    print("node name multiset equal:", sorted(names) == sorted(nn), "; distinct:", len(set(names)) == len(names))
    # WF in Python
    n = len(names)
    wf = 0
    for g in gates:
        nm, k, init, ins, arcs, out = g
        ok = (len(ins) == k and len(arcs) == k and out < n and all(x < n for x in ins) and init < 2 ** (2 ** k) and
              all(a[0] <= a[1] and a[2] <= a[3] and a[0] <= a[2] and a[1] <= a[3] for a in arcs))
        wf += not ok
    outs_ok = all(g[5] == i for i, g in enumerate(gates))
    print("Python evaluation of Net.WF: per-gate failures %d; gate i drives node i: %s" % (wf, outs_ok))


if __name__ == "__main__":
    main()
