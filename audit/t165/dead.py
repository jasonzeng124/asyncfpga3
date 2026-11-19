"""Independent deadness: walk forward from each cell; live if it reaches a non-slice cell (IOB/PS7/BUFG/BRAM/DSP...),
a top port bit, an FF (any FF input counts: D/CE/SR/CLK -- an FF is a state element; also report FF-transitive), or a
LUT input pin the LUT's INIT actually depends on (then that LUT's liveness)."""
import json, sys, re, collections
sys.path.insert(0, "/root/agentH/wt/cells/gls/fid")
m = json.load(open(sys.argv[1]))["modules"]["top"]
cells = m["cells"]
nodir = [(cn, p) for cn, c in cells.items() for p in c["connections"] if p not in c.get("port_directions", {})]
print("ports without direction:", len(nodir), nodir[:5])
portbits = {b for p in m.get("ports", {}).values() for b in p["bits"] if isinstance(b, int)}
print("top ports:", {k: (v["direction"], len(v["bits"])) for k, v in m.get("ports", {}).items()})
users = collections.defaultdict(list)
for cn, c in cells.items():
    for p, bl in c["connections"].items():
        if c["port_directions"].get(p) in ("input", "inout"):
            for b in bl:
                users[b].append((cn, p))
def init_dep(c):
    """physical pins A1..A6 the INIT depends on, through X_ORIG_PORT_Ak (logical I0..I5)"""
    init = c["parameters"].get("INIT", "0")
    bits = init if isinstance(init, str) else bin(init)[2:]
    n = len(bits); v = int(bits, 2)
    k = max(1, (n - 1).bit_length())
    ldep = set()
    for i in range(k):
        for a in range(n):
            if not a & (1 << i) and ((v >> a) & 1) != ((v >> (a | (1 << i))) & 1):
                ldep.add(i); break
    at = c.get("attributes", {})
    if not any(x.startswith("X_ORIG_PORT_A") for x in at):
        return {"A%d" % (i + 1) for i in ldep}
    dep = set()
    for x, val in at.items():
        mm = re.match(r"^X_ORIG_PORT_(A\d)$", x)
        if mm and any(int(t) in ldep for t in re.findall(r"I(\d)", val)):
            dep.add(mm.group(1))
    return dep
SLICE = ("SLICE_LUTX", "SELMUX2_1", "CARRY4", "SLICE_FFX")
memo = {}
def outs(cn):
    c = cells[cn]
    return [b for p, bl in c["connections"].items() if c["port_directions"][p] == "output" for b in bl]
deps = {cn: init_dep(c) for cn, c in cells.items() if c["type"] == "SLICE_LUTX" and c.get("attributes", {}).get("X_ORIG_TYPE", "LUT").startswith("LUT") and "INIT" in c["parameters"]}
# fixpoint liveness
def solve(ff_always):
    live = {cn for cn, c in cells.items() if c["type"] not in SLICE}
    live |= {cn for cn in cells if any(b in portbits for b in outs(cn))}
    if ff_always: live |= {cn for cn, c in cells.items() if c["type"] == "SLICE_FFX"}
    grew = True
    while grew:
        grew = False
        for cn in cells:
            if cn in live: continue
            for b in outs(cn):
                if any(u != cn and u in live and not (u in deps and p not in deps[u]) for u, p in users[b]):
                    live.add(cn); grew = True; break
    return live
liveB = solve(False)
deadB = set(cells) - liveB
deadA = set(cells) - solve(True)
print("dead with FF-as-sink:", len(deadA), sorted(deadA)[:6])
live = liveB
dead = set(cells) - live
json.dump(sorted(dead), open(sys.argv[2], "w"))
print("cells", len(cells), "dead(mine, FF loads = live)", len(dead))
# checker's structural deadness
import importlib.util
spec = importlib.util.spec_from_file_location("fe", "/root/agentH/wt/cells/gls/fid/fasm_equiv_new.py"); fe = importlib.util.module_from_spec(spec); spec.loader.exec_module(fe)
jd = fe.dead_cells(cells, fe.json_loads(cells))
print("checker dead", len(jd), "checker-dead but mine-live:", sorted(jd - dead)[:10], "mine-dead not checker:", len(dead - jd))
