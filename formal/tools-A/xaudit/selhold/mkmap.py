"""mkmap.py -- build the SELECT MAP that xselhold (Events9SelMain.lean) checks (UNTRUSTED).

    python3 -I mkmap.py CERT.json SKEL.json FULLNET.json MAPDATA.lean OUT.json

Probe E8SelC (shard A).  For every REAL filtered pin of the xevents certificate and each of
its select literals, names the channel of C's model whose H_BUNDLE is to hold the select
still, by its C channel name (CapNet.Gcd.chanNames, as listed in B's generated table
Formal/Cells/ResetCapstoneMapData.lean: name, request driver/net, acknowledge driver/net),
and gives the channel's request and acknowledge wires as SKELETON gate names ("<cell>/O") and
its bus bits as skeleton input ports ("sel_<bit>").

Channel choice (the hold argument needs the channel that is mid-transaction through the
pin's whole read window):
  * steer pin (cond_br, st=true): the CONDITION input channel of the cond_br's join, i.e. the
    B-table row whose acknowledge driver is `ucond_brN.uack` (the steer's ack, broadcast to
    both join inputs) and whose request driver belongs to the select's producer instance
    (the comparator `ucmpiK` or the link `ulink_X` that latches the select);
  * mux-join or N-way decode pin (umuxN, st=false or a decode steer gate): the select channel `X` of the link `ulink_X` that
    latches the select (B-table row with request net `X_req`).
Everything here is name matching on the routed netlist and B's table; xselhold re-checks the
structural part (route arc from the bus wire to the select gate's input, bus membership) and
prints the names; the correspondence of the name to C's channel stays TRUSTED.
Unresolved literals are listed in OUT["unresolved"] (their pins keep design_verdict9_sel's
premise).
"""
import json
import re
import sys


def load_rows(p):
    rows = []
    rx = re.compile(r"^\* (\d+) `([^`]+)`: (\d+) \[(.+?)\] <- `([^`]+)` ; (\d+) \[(.+?)\] <- `([^`]+)`")
    for l in open(p):
        m = rx.match(l)
        if m:
            i, nm, _, rd, rn, _, ad, an = m.groups()
            rows.append(dict(idx=int(i), name=nm, rdrv=rd, rnet=rn, adrv=ad, anet=an))
    return rows


def comps(s):
    return [c for c in re.split(r"\.", s) if c]


def subseq(a, b):
    """every component of a occurs in b, in order (b may have extra ones)."""
    it = iter(b)
    return all(any(x == y for y in it) for x in a)


def main(certp, skelp, fullp, mapdp, outp):
    cert = json.load(open(certp))
    skel = json.load(open(skelp))["modules"]["gcd_ctl"]
    full = json.load(open(fullp))["modules"]["gcd_ctl"]
    rows = load_rows(mapdp)
    assert len(rows) > 400, f"only {len(rows)} B-table rows parsed"
    cells = full["cells"]
    drv = {}
    for cn, c in cells.items():
        for b in c["connections"].get("O", []):
            drv[b] = cn
    # RTL instance -> routed cell: the instance's components, in order, inside the cell name
    ccomp = {cn: comps(re.sub(r"\$LUT\d", "", cn)) for cn in cells}

    def cell_of(inst):
        want = ["urig", "udut"] + comps(inst) if not inst.startswith("urig.") else comps(inst)
        hits = [cn for cn, cc in ccomp.items() if subseq(want, cc) and cc[-1] == want[-1]]
        if len(hits) > 1:  # prefer the shortest name (fewest inserted components)
            hits.sort(key=lambda c: len(ccomp[c]))
            hits = [h for h in hits if len(ccomp[h]) == len(ccomp[hits[0]])]
        if len(hits) == 1:
            return hits[0]
        # delay lines are re-sized by the flow (BD_SIZES): B's table names the RTL default
        # length (e.g. udly.g[29]); take the END of the routed chain (the element whose
        # output no other element of the same chain reads)
        m = re.match(r"^(.*)\.g\[\d+\]\.u$", inst)
        if not m:
            return None
        pre = ["urig", "udut"] + comps(m.group(1)) if not inst.startswith("urig.") else comps(m.group(1))
        ch = [cn for cn, cc in ccomp.items() if subseq(pre, cc) and len(cc) >= 2 and re.match(r"g\[\d+\]$", cc[-2])
              and cc[-1] == "u" and cc[:len(cc) - 2] in (pre, pre + ["chain"])]
        outs = {cells[c]["connections"]["O"][0]: c for c in ch}
        read = {b for c in ch for k, v in cells[c]["connections"].items() if k != "O" for b in v}
        ends = [c for o, c in outs.items() if o not in read]
        return ends[0] if len(ends) == 1 else None

    skcells = set(skel["cells"])
    ports = {p["bits"][0]: n for n, p in skel["ports"].items()}
    gates = {}
    for nj in cert["nodes"]:
        pass
    ent, unres = [], []
    for j, nj in enumerate(cert["nodes"]):
        if nj["virt"]:
            continue
        for pi, p in enumerate(nj["pins"]):
            if p["pk"] != "filt":
                continue
            lits = p["ssel"] if p["st"] else p["fold"]
            sgate = p["sg"] if p["st"] else nj["lut"]
            scell = sgate.rsplit("/", 1)[0]
            for (i, _pol) in lits:
                b = skel["cells"][scell]["connections"][f"I{i}"][0]
                if b not in ports:
                    unres.append(dict(node=j, pin=pi, lit=i, why=f"select net {b} is not a cut input"))
                    continue
                sd = drv.get(b, "")
                sinst = sd.replace("urig.udut.", "").split(".")[0]
                cand = []
                cbr = scell.replace("urig.udut.", "").split(".")[0]
                if p["st"] and cbr.startswith("ucond_br"):
                    cand = [r for r in rows if r["adrv"] == f"{cbr}.uack"]
                    pick = [r for r in cand if r["rdrv"].split(".")[0] == sinst]
                else:
                    X = sinst[len("ulink_"):] if sinst.startswith("ulink_") else None
                    pick = [r for r in rows if X and r["rnet"] == f"{X}_req"]
                if len(pick) != 1:
                    unres.append(dict(node=j, pin=pi, lit=i, why=f"select driver {sd}: {len(pick)} candidate channels "
                                      f"({[r['name'] for r in (pick or cand)]})"))
                    continue
                r = pick[0]
                rc, ac = cell_of(r["rdrv"]), cell_of(r["adrv"])
                if not rc or not ac or rc not in skcells or ac not in skcells:
                    unres.append(dict(node=j, pin=pi, lit=i, why=f"channel {r['name']}: req/ack driver cell not found "
                                      f"in the skeleton ({r['rdrv']}->{rc}, {r['adrv']}->{ac})"))
                    continue
                ent.append(dict(node=j, pin=pi, lit=i, name=r["name"], cidx=r["idx"], rnet=r["rnet"], anet=r["anet"],
                                rq=rc + "/O", ak=ac + "/O", ws=[ports[b]], seldrv=sd))
    json.dump(dict(entries=ent, unresolved=unres), open(outp, "w"), indent=0)
    print(f"mkmap: {len(ent)} literals mapped, {len(unres)} unresolved")
    for u in unres:
        print("  UNRESOLVED", u)


if __name__ == "__main__":
    main(*sys.argv[1:6])
