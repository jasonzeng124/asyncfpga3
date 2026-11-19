#!/usr/bin/env python3
"""margin/bram/bram_gates.py (shard C, UNTRUSTED): the gates of decode_bram.py's RAMB18E1 cells, added to a net.

    python3 bram_gates.py D0.json NET0.json NET.json

build_net.py leaves a ramb18e1 cell opaque (its input routes are in NET0, its read outputs "<site>/DOADO<i>" undriven).
For every read DOADO<i> this adds one gate, kind "ram" (simx flag 3), out = that node, inputs (constants folded):
  role 0      CLKARDCLK, arc = site-pin delay + prjxray IOPATH CLKARDCLK -> DOADO   (the edge's effect on DO)
  role 1      CLKARDCLK again, arc = site-pin delay                                 (the edge at the pin: sampling)
  role 2, 3   WEA0, WEA1 (byte write enables, bits 7:0 / 15:8)
  role 16+i   ADDRARDADDR[4+i], i = 0..9 (the x18 word address)
  role 32+i   DIADI[i], i = 0..15
every non-clock arc = its site-pin delay. simx (flag 3): at each rising edge h of the clock node, the pins are sampled at
h + arc(role 1) - arc(pin); a write (WEA) stores DIADI's bytes, WRITE_FIRST puts the written word on DO, else the stored
word; DO changes at h + arc(role 0). A sampled pin that changes within [-SETUP, +HOLD] of its sampling instant is a
setup / hold violation (simx counts RAMVIOL; a run with one is not a pass). SETUP / HOLD: the largest prjxray value
(BRAM_L.sdf, RAMBFIFO36E1 cell types; corner unknown, so the widest window): ADDR 566 / 360, WE 532 / 197, DI 737 / 667 ps.
Initial state: the output latch from ZINIT_A, memory words from INIT_* (decode_bram.py).
"""
import importlib.util, json, os, re, sys

HERE = os.path.dirname(os.path.abspath(__file__))
_spec = importlib.util.spec_from_file_location("dsp_gates", os.path.join(HERE, "..", "dsp", "dsp_gates.py"))
DG = importlib.util.module_from_spec(_spec)
_spec.loader.exec_module(DG)

CLK2DO = [585, 1098, 1353, 2454]          # prjxray BRAM_[LR].sdf IOPATH CLKARDCLK -> DOADO, DOA_REG 0 (ps)
SETUP = {"A": 566, "W": 532, "D": 737}
HOLD = {"A": 360, "W": 197, "D": 667}


def die(m):
    print("bram_gates: " + m, file=sys.stderr)
    sys.exit(1)


def clk2do(tiletype):
    t = open(os.path.join(DG.BN.DB, "timings", "%s.sdf" % tiletype)).read()
    vals = set()
    # only the cell types with the output register OFF (DOA_REG_[LU]_0): the DOA_REG_1 types carry the register's much
    # faster CLK->DO (204 / 468 ps), which a 2026-11-19 review found mixed in here (the min over all types was taken)
    for cell in re.split(r"\(CELL\b", t):
        ct = re.search(r'CELLTYPE "([^"]*)"', cell)
        if not ct or not re.search(r"DOA_REG_[LU]_0", ct.group(1)):
            continue
        for m in re.finditer(r"\(IOPATH CLKARDCLK[LU] DOADO[LU] \(([\d.]+)::([\d.]+)\)\(([\d.]+)::([\d.]+)\)\)", cell):
            vals.add(tuple(int(round(float(x) * 1000)) for x in m.groups()))
    if not vals:
        die("no IOPATH CLKARDCLK -> DOADO in %s.sdf" % tiletype)
    r = [min(v[0] for v in vals), max(v[1] for v in vals), min(v[2] for v in vals), max(v[3] for v in vals)]
    if r != CLK2DO:
        die("CLK->DO from %s.sdf is %s, not the expected DOA_REG=0 %s" % (tiletype, r, CLK2DO))
    return r


def main():
    d0, net0, out = sys.argv[1:4]
    D = json.load(open(d0)); N = json.load(open(net0))
    rams = [c for c in D["cells"] if c["kind"] == "ramb18e1"]
    names = N["nodes"]; idx = {n: i for i, n in enumerate(names)}
    gates = N["gates"]
    drv = {g["out"]: gi for gi, g in enumerate(gates)}
    added = 0
    for ri, c in enumerate(rams):
        r = c["ram"]; sn = c["name"]
        io = clk2do(r["tiletype"])
        pins = [("CLKARDCLK", 0), ("CLKARDCLK", 1), ("WEA0", 2), ("WEA1", 3)] + \
               [("ADDRARDADDR%d" % (4 + i), 16 + i) for i in range(10)] + [("DIADI%d" % i, 32 + i) for i in range(16)]
        ins, arcs, roles, base = [], [], [], 0
        for pin, role in pins:
            v = c["conn"][pin]
            if "const" in v:
                if role < 2:
                    die("%s: constant clock" % sn)
                base |= int(bool(v["const"])) << role
                continue
            if "float" in v:
                die("%s %s: floating" % (sn, pin))
            rt = v.get("_route")
            if not rt or rt["sink"] not in idx:
                die("%s %s: no routed sink node in the net" % (sn, pin))
            spd = DG.site_pin_delay(*rt["sinkwire"])
            e = [x + y for x, y in zip(io, spd)] if role == 0 else spd
            ins.append(idx[rt["sink"]]); roles.append(role)
            arcs.append({"fmin": e[0], "fmax": e[1], "smin": e[2], "smax": e[3]})
        mem = {int(k): w for k, w in r["mem_nonzero"].items()}
        for o in r["read"]:
            m = re.match(r"^DOADO(\d+)$", o)
            if not m:
                die("%s: %s read (only DOADO modelled)" % (sn, o))
            on = "%s/%s" % (sn, o)
            if on not in idx:
                continue
            if idx[on] in drv:
                die("%s already has a driver" % on)
            bit = int(m.group(1))
            g = {"name": "%s.%s" % (sn, o), "kind": "ram", "k": len(ins), "init": (r["init_do"] >> bit) & 1,
                 "ins": list(ins), "arcs": arcs, "out": idx[on], "prov": {"site": sn, "tile": r["tile"], "pin": o},
                 "ram": {"id": ri, "site": sn, "obit": bit, "roles": list(roles), "base": base,
                         "setup": SETUP, "hold": HOLD, "mem": mem, "json_cell": r.get("json_cell")}}
            gates.append(g); drv[g["out"]] = len(gates) - 1; added += 1
    for nm, i in idx.items():
        if re.match(r"^RAMB18_X\d+Y\d+/", nm) and i not in drv:
            die("%s is read but has no driver" % nm)
    N["fidelity"]["RAMB18E1 port A as gates (ram: DO bit = stored word at the last clock edge, WRITE_FIRST; "
                  "prjxray CLK->DO; setup / hold windows counted, not modelled as X)"] = len(rams)
    N["ram_gates"] = added
    N["rams"] = [{"id": ri, "site": c["name"], "json_cell": c["ram"].get("json_cell")} for ri, c in enumerate(rams)]
    json.dump(N, open(out, "w"))
    print("bram_gates: %d RAMB18 sites -> %d ram gates; %d nodes, %d gates" % (len(rams), added, len(names), len(gates)),
          file=sys.stderr)


if __name__ == "__main__":
    main()
