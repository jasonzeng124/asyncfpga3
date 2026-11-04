# T20: the August ipow LUT research 7edc6af6 calls "live, written as constant 0".  Prints the routed-JSON cell at a BEL
# (type, INIT, physical pin -> original logical ports, drivers) and the function it implements on its physical pins.
# usage: lut_check_own.py ROUTED_JSON BEL
import json, sys, itertools
m = list(json.load(open(sys.argv[1]))["modules"].values())[0]
drv = {b: n for n, c in m["cells"].items() for p, bits in c["connections"].items()
       if c["port_directions"].get(p) == "output" for b in bits}
for n, c in m["cells"].items():
    if c["attributes"].get("NEXTPNR_BEL") != sys.argv[2]: continue
    init = c["parameters"]["INIT"]
    bits = int(init, 2)                                  # MSB-first bit string (yosys/nextpnr JSON)
    pins = {p: c["attributes"].get("X_ORIG_PORT_" + p, "").split() for p in c["connections"] if p.startswith("A")}
    print(n, c["type"], c["attributes"].get("X_ORIG_TYPE"), "INIT", init)
    for p, l in sorted(pins.items()):
        b = c["connections"][p]
        print("  pin", p, "-> logical", l or "-", "net", b, "driver", drv.get(b[0], "none") if b else "unconnected")
    # logical input index -> physical pin
    lp = {int(x[1:]): p for p, l in pins.items() for x in l}
    phys = sorted({lp[i] for i in lp})
    print("  truth table over physical pins", phys)
    vals = set()
    for v in itertools.product((0, 1), repeat=len(phys)):
        a = dict(zip(phys, v)); idx = sum(a[lp[i]] << i for i in lp)
        o = (bits >> idx) & 1; vals.add(o); print("   ", dict(zip(phys, v)), "->", o)
    print("  output takes values", sorted(vals), "-> constant" if len(vals) == 1 else "-> live")
