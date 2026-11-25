#!/usr/bin/env python3
"""boundary_ps.py (shard A, THE goal): boundary.py for the gcd_ps target (bridge_i.udut, BQ#4); the kernel boundary of the target as node names of the decoded
netlist (untrusted naming, from yosys + nextpnr's routed JSON).

    python3 boundary_ps.py SYNTH.json ROUTED.json NET.json OUT.json

For each kernel port bit (bridge_i.udut.<port>), the logical net in yosys, its aliases, the alias that
nextpnr kept, that net's driver BEL, and the decoded node of that BEL's output. A constant bit is
reported as const. Output: {port: [node name or "const0"/"const1", ...]}, plus the env node list.
"""
import json, sys
syn, rout, netp, outp = sys.argv[1:5]
Y = json.load(open(syn))["modules"]["gcd_ps"]
R = json.load(open(rout))["modules"]["top"]
net = json.load(open(netp))
nodes = {n: i for i, n in enumerate(net["nodes"])}
alias = {}
for n, v in Y["netnames"].items():
    for b in v["bits"]:
        alias.setdefault(b, []).append(n)
rbits = {}
for n, v in R["netnames"].items():
    rbits[n] = v["bits"]
drv = {}
for cn, c in R["cells"].items():
    for p, d in c["port_directions"].items():
        if d == "output":
            for b in c["connections"][p]:
                drv[b] = (cn, c["type"], p, c["attributes"].get("NEXTPNR_BEL"))


def phys(ybit, what):
    if ybit in ("0", "1"):
        return "const" + ybit
    cands = []
    for a in alias[ybit]:
        if a in rbits:
            cands.append(a)
        else:
            # vector element
            import re
            m = re.match(r"(.*)$", a)
    # yosys vectors: name[i]
    for n, v in Y["netnames"].items():
        if len(v["bits"]) > 1:
            for i, b in enumerate(v["bits"]):
                if b == ybit and "%s[%d]" % (n, i) in rbits:
                    cands.append("%s[%d]" % (n, i))
    for c in cands:
        b = rbits[c][0]
        if b in drv:
            cn, ct, p, bel = drv[b]
            site, belname = bel.split("/")
            if ct == "SLICE_LUTX":
                L, w = belname[0], belname[1]   # A6LUT -> A, 6
                nm = "%s.%s%s" % (site, L, w)
            elif ct == "SLICE_FFX":
                nm = "%s.%sQ" % (site, belname[0]) if belname[1:] == "FF" else "%s.%s5Q" % (site, belname[0])
            else:
                sys.exit("%s: driver %s %s %s not handled" % (what, cn, ct, bel))
            if nm not in nodes:
                sys.exit("%s: node %s not in the decoded netlist" % (what, nm))
            return nm
    sys.exit("%s: no routed alias with a driver among %s" % (what, alias[ybit]))


def by_name(rname, what):
    """The decoded node of the BEL driving routed net `rname` (a LUT or a slice FF)."""
    b = rbits[rname][0]
    cn, ct, p, bel = drv[b]
    site, belname = bel.split("/")
    if ct == "SLICE_LUTX":
        nm = "%s.%s%s" % (site, belname[0], belname[1])
    elif ct == "SLICE_FFX":
        nm = "%s.%sQ" % (site, belname[0]) if belname[1:] == "FF" else "%s.%s5Q" % (site, belname[0])
    else:
        sys.exit("%s: driver %s is %s" % (what, cn, ct))
    if nm not in nodes:
        sys.exit("%s: node %s not in the decoded netlist" % (what, nm))
    return nm


ynames = Y["netnames"]
# handshake nets: the names nextpnr kept (checked against the yosys aliases below)
HS = {"rst": "bridge_i.ctrl_rst", "req": "bridge_i.p_end_req", "a_ack": "bridge_i.a_ack", "b_ack": "bridge_i.b_ack",
      "start_ack": "bridge_i.start_ack", "out0_req": "core_o_req", "out0_ack": "bridge_i.udut.n_index_97_ack",
      "pend_ack": "bridge_i.p_end_ack"}
res = {k: by_name(v, k) for k, v in HS.items()}
res["a_data"] = [phys(b, "a_data[%d]" % i) for i, b in enumerate(ynames["bridge_i.a_data_reg"]["bits"])]
res["b_data"] = [phys(b, "b_data[%d]" % i) for i, b in enumerate(ynames["bridge_i.b_data_reg"]["bits"])]
res["out0_data"] = [by_name("bridge_i.o_data_pl[%d]" % i, "out0_data[%d]" % i) for i in range(32)]
# the yosys aliases of each handshake net, for the record (untrusted naming, checkable)
yal = {}
for k, v in HS.items():
    yal[k] = [n for n, w in ynames.items() if len(w["bits"]) == 1 and any(n == v or n.endswith(v.split(".")[-1]) for _ in [0])][:6]
env = sorted({res["rst"], res["req"], res["out0_ack"], res["pend_ack"]} |
             {x for x in res["a_data"] + res["b_data"] if not x.startswith("const")})
json.dump({"boundary": res, "env": env, "routed_names": HS}, open(outp, "w"), indent=1)
for k in ["rst", "req", "a_ack", "b_ack", "start_ack", "out0_req", "out0_ack", "pend_ack"]:
    print(k, res[k])
print("a_data distinct", len(set(res["a_data"])), "b_data distinct", len(set(res["b_data"])),
      "out0_data distinct", len(set(res["out0_data"])), "env nodes", len(env))
