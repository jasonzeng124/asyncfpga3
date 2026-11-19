#!/usr/bin/env python3
"""margin/simx_conv.py (shard C, UNTRUSTED): NET.json + BND.json -> the compact text netlist simx reads.

    python3 simx_conv.py NET.json BND.json OUT.simx

DSP48E1 gates (kind "dsp", margin/dsp/dsp_gates.py) are written with flag 2 and their parameters (simx.cpp dsp48).
Mirrors the --full setup of tools/huff/simadv.py exactly: env nodes' drivers dropped (later gate wins a node),
the gate order is Python's iteration order of set(drv.values()) (simadv evaluates/schedules in that order, which
fixes the heap's FIFO tie-breaks), readers in that order. Also records the kernel-cone counts simadv prints.
"""
import json, sys

netf, bndf, outf = sys.argv[1:4]
N = json.load(open(netf)); BJ = json.load(open(bndf)); B = BJ["boundary"]
names = N["nodes"]; idx = {n: i for i, n in enumerate(names)}; gates = N["gates"]
nb = lambda k: idx[B[k]]
ENV = set(idx[x] for x in BJ["env"])
drv = {}
for gi, g in enumerate(gates):
    if g["out"] not in ENV:
        drv[g["out"]] = gi
outs = [nb("a_ack"), nb("b_ack"), nb("start_ack"), nb("out0_req")] + [idx[x] for x in B["out0_data"]]
cone, todo = set(), list(outs)
seen = set(todo)
while todo:
    n = todo.pop()
    gi = drv.get(n)
    if gi is None:
        continue
    cone.add(gi)
    for i in gates[gi]["ins"]:
        if i not in seen and i not in ENV:
            seen.add(i); todo.append(i)
ncone_kernel, nseen = len(cone), len(seen)
cone = set(drv.values())   # --full
order = list(cone)
with open(outf, "w") as f:
    f.write("SIMX1\n%d %d %d %d %d\n" % (len(names), len(gates), len(order), ncone_kernel, nseen))
    for n in names:
        assert "\n" not in n
        f.write(n + "\n")
    for gi in order:
        g = gates[gi]
        lut = 1 if (g["name"].endswith("LUT.O6") or g["name"].endswith("LUT.O5")) else 0
        assert len(g["ins"]) == g["k"] == len(g["arcs"])
        # a DSP48E1 output bit (margin/dsp/dsp_gates.py): flag 2, its function's parameters after the arcs
        dd = g.get("dsp") if g["kind"] == "dsp" else None
        rr = g.get("ram") if g["kind"] == "ram" else None
        rtail = ""
        if rr:   # a RAMB18E1 DOADO bit (margin/bram/bram_gates.py): flag 3, then R id obit base su/ho (ADDR, WE, DI) roles M n (addr word)..
            rtail = " R %d %d %x %d %d %d %d %d %d %s M %d%s" % (rr["id"], rr["obit"], rr["base"], rr["setup"]["A"], rr["hold"]["A"],
                rr["setup"]["W"], rr["hold"]["W"], rr["setup"]["D"], rr["hold"]["D"], " ".join(map(str, rr["roles"])),
                len(rr["mem"]), "".join(" %s %x" % (a_, w_) for a_, w_ in sorted(rr["mem"].items(), key=lambda x: int(x[0]))))
        f.write("%d %d %d %d %x %s %s%s%s\n" % (gi, g["out"], g["k"], 3 if rr else 2 if dd else lut, g["init"], " ".join(map(str, g["ins"])),
                " ".join("%d %d %d %d" % (e["fmin"], e["fmax"], e["smin"], e["smax"]) for e in g["arcs"]),
                (" D %d %d %d %d %d %d %s %s" % (dd["obit"], dd["opmode"], dd["alumode"], dd["inmode"], dd["carryinsel"], dd["carryin"],
                 " ".join("%x" % b for b in dd["base"]), " ".join(map(str, dd["roles"])))) if dd else "", rtail))
    for k in ("rst", "req", "a_ack", "b_ack", "start_ack", "out0_req", "out0_ack", "pend_ack"):
        f.write("%s %d\n" % (k, -1 if B.get(k) is None else nb(k)))   # pend_ack None: a void kernel (bench logic acks p_end)
    for k in ("a_data", "b_data", "out0_data"):
        # node index, or -1 (const0) / -2 (const1) for tied bits (as simadv: any name starting "const")
        f.write("%s %d %s\n" % (k, len(B[k]), " ".join(
            str(-2 if nm == "const1" else -1) if nm.startswith("const") else str(idx[nm]) for nm in B[k])))
    if B.get("xacks"):   # margin/bram/mk_bnd_mem.py: acknowledges of the other input channels (simx waits for all)
        f.write("xacks %d %s\n" % (len(B["xacks"]), " ".join(str(idx[x]) for x in B["xacks"])))
    for h in B.get("hosts", []):   # margin/bram/mk_bnd_mem.py: a host port per array (simx --hostport)
        cn = lambda x: -2 if x == "const1" else -1 if x.startswith("const") else idx[x]
        f.write("host %s %d %d %d %d %s %d %s\n" % (h["name"], cn(h["req"]), cn(h["we"]), cn(h["ack"]), len(h["addr"]),
                " ".join(str(cn(x)) for x in h["addr"]), len(h["wdata"]), " ".join(str(cn(x)) for x in h["wdata"])))
print("simx_conv: %d nodes, %d gates simulated (--full), kernel cone %d gates (%d nodes) -> %s"
      % (len(names), len(order), ncone_kernel, nseen, outf), file=sys.stderr)
