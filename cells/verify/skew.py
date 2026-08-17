#!/usr/bin/env python3
"""Rule E -- does a request still trail its own data AFTER THE WIRE?

    python3 verify/skew.py <routed.sdf> <routed.json> [--emit pads.json]

WHAT THE OTHER GATES CANNOT SEE.  tighten.py's rules A-D all measure inside a
cell: a matched delay against the datapath of the unit that drives it, with
every input assumed to launch together.  That is the right check for a cell.
It is not the whole bundling constraint, because the constraint is about what
arrives AT THE CONSUMER, and between producer and consumer the request net and
the N data nets are routed INDEPENDENTLY.  On this part routing is most of
every hop, so the ordering established at the producer's output pins is not the
ordering seen at the consumer's input pins, and nothing checked the difference.

This measures it, from the SDF's own INTERCONNECT records: for every channel
whose request net and data net land on the SAME consumer cell, the arrival of
each at that cell.  Same driver, same destination, same units -- so the
difference is a real number and not a screen.

WHAT IT FOUND ON gcd.  30 of 42 measurable pairs had the request arriving
FIRST, by up to 1605 ps, and the consumers were the bd_mux select joins:

    skew    req   data  channel -> shared consumer
   -1605    150   1755  n151__0 -> umux15.uj0
   -1170    150   1320  n32__1  -> umux1.uj0
   -1140    585   1725  n90__0  -> umux9.uj1

umux15 is `.ctl_req(n151__0_req) ... .s(n151__0_data[0])` -- the request that
fires the mux's join and the select value it steers on are the SAME channel,
and the request wins by 1.6 ns.  A mux that samples a select which has not
arrived steers the token down the wrong branch.  That accounts for the whole
shape of gcd's failure: a mis-steered token produces NO result rather than a
wrong one (err_sticky is always clean), the mask is deterministic per bitstream
and different on every route because routing skew is a property of the route,
and even gcd(1,1) can die because this is control and not arithmetic.

WHY PADDING BY HAND DID NOT FIX IT.  A global BDC_SELECT_PAD buys margin on the
padded channel and spends it everywhere else -- 24 channels of 32 elements is
768 extra LUT1s, congestion rises, and the channels that were already marginal
get worse faster than the padded ones improve.  The recorded sweep shows
exactly that: pad 4 -> 7/16, pad 32 -> 16/16 on one route and 9/16 on the next,
pad 64 -> 8/16 with gcd(1,1) among the dead.  The number has to come from the
route, per channel, which is what --emit produces and what
bdc/emit.py's BDC_SELECT_PADS has always been shaped to consume.
"""
import argparse
import collections
import json
import re

IC = re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\(([-\d.:]+)\)")

# One bd_delay element, for converting a picosecond skew into a pad length.
# Same number tighten.py uses; see its header for where it comes from.
ELEM_PS = 274

# Cell outputs, by routed-JSON type.  A pin not listed here is an input, which
# is what makes the sink map below correct without a second table.
OUTS = {"SLICE_LUTX": ("O6", "O5"), "SLICE_FFX": ("Q",), "SELMUX2_1": ("OUT",),
        "CARRY4": ("O0", "O1", "O2", "O3", "CO0", "CO1", "CO2", "CO3"),
        "BUFGCTRL": ("O",)}


def load(sdf, jsn):
    arr = collections.defaultdict(list)          # dst pin -> [(src pin, ps)]
    for line in open(sdf):
        m = IC.search(line)
        if m:
            dst = m.group(2).replace("\\", "")
            arr[dst].append(float(m.group(3).split(":")[1]))
    top = json.load(open(jsn))["modules"]["top"]
    sink = collections.defaultdict(list)         # net bit -> [(cell, pin)]
    for cn, c in top["cells"].items():
        outs = OUTS.get(c["type"], ())
        for p, bits in c["connections"].items():
            if p in outs:
                continue
            for b in bits:
                if isinstance(b, int):
                    sink[b].append((cn, f"{cn}/{p}"))
    return arr, sink, top["netnames"]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("sdf")
    ap.add_argument("json")
    ap.add_argument("--emit", help="write per-instance pads for BDC_SELECT_PADS")
    ap.add_argument("--base", type=int, default=4,
                    help="pad already present on select links in the route that "
                         "was measured (BDC_SELECT_PAD, default 4).  The deficit "
                         "below is ON TOP of it: emit.py's per-instance override "
                         "REPLACES the default rather than adding to it, so "
                         "emitting the bare deficit would SHORTEN a channel that "
                         "already had four elements and make things worse.")
    a = ap.parse_args()
    arr, sink, nets = load(a.sdf, a.json)

    def arrivals(bit):
        """consumer cell -> worst arrival at that cell for this net."""
        out = {}
        for cn, pin in sink.get(bit, []):
            for d in arr.get(pin, []):
                if d > out.get(cn, -1.0):
                    out[cn] = d
        return out

    chan = collections.defaultdict(dict)
    for name, v in nets.items():
        m = re.match(r"^(.*)_(req|data)$", name)
        if m:
            chan[m.group(1)][m.group(2)] = v["bits"]

    rows = []
    for base, d in chan.items():
        if "req" not in d or "data" not in d:
            continue
        rq = d["req"][0] if isinstance(d["req"], list) else d["req"]
        if not isinstance(rq, int):
            continue
        ra = arrivals(rq)
        for b in d["data"]:
            if not isinstance(b, int):
                continue
            for cn, da in arrivals(b).items():
                if cn in ra:
                    rows.append((ra[cn] - da, base, cn, ra[cn], da))
    rows.sort()
    bad = [r for r in rows if r[0] < 0]
    print(f"rule E  {len(rows)} (channel, shared consumer) pair(s) measurable; "
          f"request arrives BEFORE its own data on {len(bad)}")
    if bad:
        print(f"\n  {'skew':>7} {'req':>6} {'data':>6}  channel -> shared consumer")
        for s, base, cn, r_, d_ in bad[:30]:
            print(f"  {s:7.0f} {r_:6.0f} {d_:6.0f}  {base} -> {cn}")

    if a.emit:
        # Worst skew per channel -> a pad in bd_delay elements, rounded up, with
        # one element of guardband.  Keyed by the link instance name emit.py
        # gives it, which is what BDC_SELECT_PADS looks up.
        worst = {}
        for s, base, _cn, _r, _d in bad:
            short = base.split(".")[-1]
            if s < worst.get(short, 0.0):
                worst[short] = s
        pads = {f"ulink_{k}": a.base + int(-v // ELEM_PS) + 1
                for k, v in worst.items()}
        with open(a.emit, "w") as f:
            json.dump(pads, f, indent=1, sort_keys=True)
        print(f"\nwrote {a.emit}: {len(pads)} channel(s), "
              f"max pad {max(pads.values()) if pads else 0} element(s)")
    return 1 if bad else 0


if __name__ == "__main__":
    raise SystemExit(main())
