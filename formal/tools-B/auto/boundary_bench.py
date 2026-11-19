#!/usr/bin/env python3
"""Shard B copy (2026-11-18, tools-B/auto) of shard C's formal/tools/margin/boundary_bench.py with ONE addition: a DUT
output bit that is a constant INSIDE the kernel module (isprime's out0_data[31:1] = 0 from extui; the top-level yosys bit
is then a fresh net whose only driver is the udut cell itself, which nextpnr does not keep) is reported as const0/const1,
read from the kernel module's own port bits. Otherwise unchanged. C's doc follows.
Shard C copy (2026-11-15, margin tool) of shard A's tools-A/target/boundary_bench.py, plus Verilog concatenations
{a, b} in the DUT port map (collatz64's n_data = {op1_to_core, op0_to_core}); otherwise unchanged. Original doc:
boundary_bench.py (shard A, 2026-11-15): the kernel boundary of a research bench build as decoded node names.

    python3 boundary_bench.py SYNTH.json ROUTED.json NET.json KERNEL_V BENCH_V OUT.json
    e.g. ... build/hw/collatz_bench_gen/collatz_bench_gen.json  ..._routed.json  net.json \
             build/gen/collatz_kernel_bench.v  build/gen/collatz_bench_gen.v  bnd.json

Generic version of boundary_ps.py (gcd_ps only). The kernel's ports are read from the `module bdc_<k>` header of
KERNEL_V (input/output, width); the bench net wired to each port is read from the `udut (...)` port map in BENCH_V
(inside `bridge_i`; yosys keeps the DUT as its own module, so the bench-side net is the one named in the top). For
each port bit, that yosys net `bridge_i.<net>[i]`, its aliases,
the alias nextpnr kept, that net's driver BEL, and the decoded node of the BEL's output (`SITE.<L>6` / `.<L>5` for a
LUT, `.<L>Q` / `.<L>5Q` for a flop or latch). Constant bits are reported as const0/const1. UNTRUSTED naming (it
relies on yosys and nextpnr names); checkable against the routed JSON. Output: {"ports": {port: {"dir", "nodes"}}}.
"""
import json, re, sys

syn, rout, netp, kv, bv, outp = sys.argv[1:7]
dut = "bridge_i"
mods = json.load(open(syn))["modules"]
Y = next(m for m in mods.values() if any(n.startswith(dut + ".") for n in m["netnames"]))
pm = re.search(r"(?:\)|\bbdc_\w+)\s*udut\s*\((.*?)\);", open(bv).read(), re.S).group(1)   # shard B: also a DUT with no parameters
conn = dict(re.findall(r"\.(\w+)\s*\(\s*([^()]*?)\s*\)", pm))
R = json.load(open(rout))["modules"]["top"]
nodes = set(json.load(open(netp))["nodes"])

src = open(kv).read()
dmod = (re.search(r"\b(bdc_\w+)\s*#\((?:(?!\bbdc_\w+\s*#\().)*?\)\s*udut\s*\(", open(bv).read(), re.S)
        or re.search(r"\b(bdc_\w+)\s+udut\s*\(", open(bv).read())).group(1)
m = re.search(r"module\s+" + dmod + r"\s*(#\(.*?\))?\s*\((.*?)\);", src, re.S)
ports = []
for line in m.group(2).splitlines():
    p = re.match(r"\s*(input|output)\s+wire\s*(\[(\d+):0\])?\s*(\w+)", line)
    if p:
        ports.append((p.group(4), p.group(1), int(p.group(3)) + 1 if p.group(3) else 1))

alias = {}
for n, v in Y["netnames"].items():
    for i, b in enumerate(v["bits"]):
        alias.setdefault(b, []).append(n if len(v["bits"]) == 1 else "%s[%d]" % (n, i))
rbits = {n: v["bits"] for n, v in R["netnames"].items()}
for n, v in R["netnames"].items():
    if len(v["bits"]) > 1:
        for i, b in enumerate(v["bits"]):
            rbits.setdefault("%s[%d]" % (n, i), [b])
drv = {}
for cn, c in R["cells"].items():
    for p, d in c["port_directions"].items():
        if d == "output":
            for b in c["connections"][p]:
                drv[b] = (cn, c["type"], p, c["attributes"].get("NEXTPNR_BEL"))


def node_of(bel, ct, port, what):
    site, belname = bel.split("/")
    if ct == "SLICE_LUTX":
        nm = "%s.%s%s" % (site, belname[0], belname[1])
    elif ct == "SLICE_FFX":
        nm = "%s.%sQ" % (site, belname[0]) if belname[1:] == "FF" else "%s.%s5Q" % (site, belname[0])
    elif ct == "CARRY4" and re.match(r"^(O|CO)[0-3]$", port):   # shard B, 2026-11-19: a kernel output read straight off a carry chain (straight)
        nm = "%s.%s" % (site, "XOR" + port[1] if port[0] == "O" and port[1] != "O" else port)
    else:
        sys.exit("%s: driver BEL %s of type %s not handled" % (what, bel, ct))
    if nm not in nodes:
        sys.exit("%s: node %s not in the decoded netlist" % (what, nm))
    return nm


def phys(ybit, what):
    if ybit in ("0", "1"):
        return "const" + ybit
    for a in alias.get(ybit, []):
        if a in rbits and rbits[a][0] in drv:
            cn, ct, p, bel = drv[rbits[a][0]]
            return node_of(bel, ct, p, what)
    # fallback: nextpnr dropped the net's names, but keeps yosys cell names; find the yosys driver cell of the bit
    for cn, c in Y["cells"].items():
        for p, bs in c["connections"].items():
            if ybit in bs and c["port_directions"].get(p) == "output" and cn in R["cells"]:
                rc = R["cells"][cn]
                outs = [q for q, d in rc["port_directions"].items() if d == "output"]
                if len(outs) == 1:
                    return node_of(rc["attributes"]["NEXTPNR_BEL"], rc["type"], outs[0], what)
    # shard B: driven only by the (hierarchical) DUT cell's output port, whose bit inside the kernel module is a constant
    for cn, c in Y["cells"].items():
        if cn != dut + ".udut": continue
        sub = mods.get(c["type"])
        for p, bs in c["connections"].items():
            if ybit in bs and c["port_directions"].get(p) == "output" and sub is not None:
                ib = sub["ports"][p]["bits"][bs.index(ybit)]
                if ib in ("0", "1"):
                    return "const" + ib
                # shard B, 2026-11-19: an output bit that is an INPUT port bit inside the kernel (a pass-through,
                # e.g. test_divui's start_ack = p_end_ack): follow the input's top-level bit to its driver
                for q, qd in sub["ports"].items():
                    if qd["direction"] == "input" and ib in qd["bits"] and q in c["connections"]:
                        tb = c["connections"][q][qd["bits"].index(ib)]
                        if tb != ybit:
                            return phys(tb, what + " (= %s)" % q)
    sys.exit("%s: no routed alias with a driver among %s" % (what, alias.get(ybit)))


res = {}
for name, d, w in ports:
    e = conn[name]
    elems = [x.strip() for x in e.strip()[1:-1].split(",")] if e.strip().startswith("{") else [e]
    bits = []
    for x in reversed(elems):          # Verilog {msb_part, ..., lsb_part}; yosys bit lists are LSB first
        mm = re.match(r"^(\w+)(\[(\d+)(?::(\d+))?\])?$", x)   # shard B: also a part-select net[hi:lo]
        if not mm:
            sys.exit("port %s: connection %r not a net, net bit or concatenation of them" % (name, e))
        yn = "%s.%s" % (dut, mm.group(1))
        if yn not in Y["netnames"]:
            sys.exit("port %s: no yosys net %s" % (name, yn))
        bb = Y["netnames"][yn]["bits"]
        if mm.group(4) is not None: bits += bb[int(mm.group(4)):int(mm.group(3)) + 1]
        else: bits += [bb[int(mm.group(3))]] if mm.group(3) is not None else list(bb)
    if len(bits) != w:
        sys.exit("port %s: width %d in yosys, %d in the module header" % (name, len(bits), w))
    res[name] = {"dir": d, "bench_net": e, "nodes": [phys(b, "%s[%d]" % (name, i)) for i, b in enumerate(bits)]}
json.dump({"dut": dut, "ports": res}, open(outp, "w"), indent=1)
for name, v in res.items():
    ns = v["nodes"]
    print("%-10s %-6s %s" % (name, v["dir"], ns[0] if len(ns) == 1 else "%d bits, %d distinct, e.g. %s" %
                             (len(ns), len(set(ns)), ns[0])))
