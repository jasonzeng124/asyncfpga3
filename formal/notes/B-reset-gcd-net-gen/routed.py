#!/usr/bin/env python3
"""Check the control network against the ROUTED design, read back from the bits.

    python3 -I routed.py NET.json FLAT_SYNTH.json ROUTED.json PHYS.json [OUT.json]

NET.json   gen.py net's output (the control network of the synthesized netlist)
FLAT_SYNTH the flattened synthesized netlist (gen.py writes it with --keep-flat;
           or yosys flatten of gcd_hw.json, see README)
ROUTED     nextpnr's gcd_hw_routed.json: used ONLY to find which BEL each logical
           cell sits on (NEXTPNR_BEL), i.e. as a hint for the renaming
PHYS       formal/tools/fasm2lean3/fasm2lean3.py's JSON of the FASM read back from
           the .bit (bitread + bit2fasm): the physical LUTs, their physical INITs,
           and for every physical pin A1..A6 the site output (or tie) it is routed from

For every control node N of NET (a LUT output with logical INIT and pins I0..):
  * its BEL gives the physical LUT P (SITE.xLUT) and output (6LUT -> O6, 5LUT -> O5);
  * every logical source of N (rst, data net, control node, constant) has a
    physical image: the site output of the BEL its driver sits on (xLUT O6 -> SITE.x6,
    O5 -> SITE.x5, xFF -> SITE.xQ, x5FF -> SITE.x5Q);
  * CHECK: each physical pin of P is a tie or the image of one of N's sources, and
    for EVERY assignment of N's (distinct, non-constant) source nets the physical
    output (physical INIT, physical pins) equals the logical one.
This is semantic equality under the placer's pin permutation, constant folding and
pin merging (nextpnr turns a LUT6_2 O6 with I5 tied 1 into a LUT5, puts several
tied pins on one physical pin, etc.). The pin map X_ORIG_PORT_* is NOT used.
"""
import json
import re
import sys
from itertools import product


def main():
    netj, flatp, routedp, physp = sys.argv[1:5]
    outp = sys.argv[5] if len(sys.argv) > 5 else None
    net = json.load(open(netj))["nodes"]
    flat = json.load(open(flatp))["modules"]["gcd_hw"]
    routed = json.load(open(routedp))["modules"]["top"]["cells"]
    phys = {c["name"]: c for c in json.load(open(physp))["cells"]}

    # logical net bit -> driver (cell, port) in the synthesized netlist
    drv = {}
    for k, v in flat["cells"].items():
        for p, bs in v["connections"].items():
            if v.get("port_directions", {}).get(p) == "output" or p in ("O", "O5", "O6", "Q"):
                for b in bs:
                    drv[b] = (k, p)

    def bel_of(cell, port):
        """BEL of a logical cell's output (LUT6_2 halves are split by nextpnr)."""
        # nextpnr names a flattened cell "a.b.$abc..." where yosys's flatten says
        # "$flatten\\a.\\b.$abc..."
        alt = cell.replace("$flatten\\", "").replace("\\", "")
        cands = [cell, alt]
        if port == "O6":
            cands = [cell + "$LUT6", alt + "$LUT6"] + cands
        elif port == "O5":
            cands = [cell + "$LUT5", alt + "$LUT5"] + cands
        for c in cands:
            if c in routed and "NEXTPNR_BEL" in routed[c]["attributes"]:
                return routed[c]["attributes"]["NEXTPNR_BEL"]
        return None

    def image(bit):
        """Physical net name of a logical net (by its driver's BEL)."""
        if bit not in drv:
            return None
        cell, port = drv[bit]
        bel = bel_of(cell, port)
        if bel is None:
            return None
        site, b = bel.split("/")
        m = re.fullmatch(r"([A-D])([56])LUT", b)
        if m:
            return f"{site}.{m.group(1)}{m.group(2)}"
        m = re.fullmatch(r"([A-D])(5?)FF", b)
        if m:
            return f"{site}.{m.group(1)}{m.group(2)}Q"
        return f"{site}/{b}"

    if "--mutate" in sys.argv:
        # negative control: flip one INIT bit of the physical LUT of a given control node
        tgt = sys.argv[sys.argv.index("--mutate") + 1]
        n = next(n for n in net if n["name"] == tgt)
        site, b = bel_of(n["cell"], n["out"]).split("/")
        P = phys[f"{site}.{b[0]}LUT"]
        # flip the bit read when every physical input is 0
        P["init"] ^= 1
        print(f"routed: MUTATED {site}.{b[0]}LUT (INIT bit 0) for {tgt}")
    if "--swap" in sys.argv:
        # negative control: swap the sources of the first two non-tied physical pins
        tgt = sys.argv[sys.argv.index("--swap") + 1]
        n = next(n for n in net if n["name"] == tgt)
        site, b = bel_of(n["cell"], n["out"]).split("/")
        P = phys[f"{site}.{b[0]}LUT"]
        js = [j for j in range(6) if "net" in P["conn"].get(f"I{j}", {})][:2]
        a, c = (P["conn"][f"I{j}"] for j in js)
        P["conn"][f"I{js[0]}"], P["conn"][f"I{js[1]}"] = c, a
        print(f"routed: MUTATED {site}.{b[0]}LUT (pins A{js[0] + 1}/A{js[1] + 1} swapped) for {tgt}")
    res = dict(ok=0, fail=[], unplaced=[])
    # the renaming must be injective: distinct logical nets, distinct physical nets
    seen = {}
    for i, n in enumerate(net):
        bits = [n["net"]] if n["kind"] != "gate" else [n["net"]]
        for b_ in bits:
            im = image(b_)
            if im is not None:
                if im in seen and seen[im] != b_:
                    res["fail"].append((n["name"], "physical net is the image of two logical nets", im))
                seen[im] = b_
    res["images"] = len(seen)
    for i, n in enumerate(net):
        if n["kind"] != "gate":
            continue
        bel = bel_of(n["cell"], n["out"] if n["out"] != "O" else "O")
        if bel is None:
            res["unplaced"].append(n["name"])
            continue
        site, b = bel.split("/")
        m = re.fullmatch(r"([A-D])([56])LUT", b)
        P = phys.get(f"{site}.{m.group(1)}LUT")
        if P is None:
            res["fail"].append((n["name"], "no physical LUT at " + bel))
            continue
        o5 = m.group(2) == "5"
        # logical sources
        srcs = []  # per logical pin: ('k', v) or ('n', physname)
        for b_ in n["pins"]:
            if b_ in ("0", "1"):
                srcs.append(("k", int(b_)))
            else:
                im = image(b_)
                if im is None:
                    srcs.append(("?", b_))
                else:
                    srcs.append(("n", im))
        if any(s[0] == "?" for s in srcs):
            res["fail"].append((n["name"], "a logical source has no physical image"))
            continue
        vars_ = sorted({s[1] for s in srcs if s[0] == "n"})
        ppins = []
        bad = None
        for j in range(6):
            c = P["conn"].get(f"I{j}")
            if c is None:
                ppins.append(("k", 1))  # unconnected physical pin: never read (checked below)
            elif "const" in c:
                ppins.append(("k", int(bool(c["const"]))))
            elif c.get("net") in vars_:
                ppins.append(("n", c["net"]))
            else:
                ppins.append(("x", c.get("net")))
        lin, pin = n["init"], P["init"]
        for asg in product((0, 1), repeat=len(vars_)):
            env = dict(zip(vars_, asg))
            la = sum((s[1] if s[0] == "k" else env[s[1]]) << k for k, s in enumerate(srcs))
            lv = (lin >> la) & 1
            # physical: a pin from an unrelated net must not matter -> try both values
            xs = [j for j, s in enumerate(ppins) if s[0] == "x" and (not o5 or j < 5)]
            pvs = set()
            for xv in product((0, 1), repeat=len(xs)):
                a = 0
                for j, s in enumerate(ppins[:5] if o5 else ppins):
                    v = s[1] if s[0] == "k" else env[s[1]] if s[0] == "n" else xv[xs.index(j)]
                    a |= v << j
                pvs.add(((pin % (1 << 32)) >> a) & 1 if o5 else (pin >> a) & 1)
            if pvs != {lv}:
                bad = (asg, lv, sorted(pvs))
                break
        if bad:
            res["fail"].append((n["name"], "function differs", bad, ppins, srcs))
        else:
            res["ok"] += 1
    print(f"routed: {res['images']} logical nets (rst, data, control) have distinct physical images; "
          f"{res['ok']} control nodes equal as functions of their sources "
          f"(physical INIT, physical pins, read back from the bits); "
          f"{len(res['fail'])} fail, {len(res['unplaced'])} without a BEL")
    for f in res["fail"][:20]:
        print("  FAIL", f)
    for u in res["unplaced"][:20]:
        print("  UNPLACED", u)
    if outp:
        json.dump(res, open(outp, "w"), indent=0)
    sys.exit(1 if res["fail"] or res["unplaced"] else 0)


if __name__ == "__main__":
    main()
