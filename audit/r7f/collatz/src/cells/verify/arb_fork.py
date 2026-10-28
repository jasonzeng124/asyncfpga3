#!/usr/bin/env python3
"""Rule J: inside every bd_arbiter, A0's fall reaches the acknowledge
C-elements before the grant that A0's fall unlocks does.

    python3 verify/arb_fork.py build/hw/gcd_hw/gcd_hw.sdf

bd_arbiter (rtl/bd_arb.v) holds its state node q while A0 is high, so that a
handover cannot acknowledge the next client for a transaction the server never
began.  That fix is only as good as an isochronic-fork assumption the cell does
not state: A0 is one net with two kinds of sink, the hold pin on ustate and the
A0 pin of each ack C-element ua_k = C(g_k, A0).  If A0's fall reaches ustate
first, q flips, g_k rises, and if g_k then reaches ua_k BEFORE A0's fall does,
ua_k sees (g_k=1, A0=1 stale) and acknowledges client k at once.  Client k
withdraws its request, the grant and R0 fall before the server saw them, and
the token is gone.  Found 2026-10-25 by bisecting a routed-GLS deadlock of
gcd_hw under per-arc delay scatter to ucontrol_merge2's ua2 and ustate, then
reproduced with no scatter at all by slowing ua2's arcs x2.5.

For each arbiter and each client k, from A0's driver:

    late  = A0 -> ua_k (interconnect) + ua_k's A0-pin arc
    early = A0 -> ustate (interconnect) + ustate's A0-pin arc to q
          + q -> ugrant_k (interconnect) + ugrant_k's q-pin arc
          + g_k -> ua_k (interconnect) + ua_k's g_k-pin arc

and the guarded margin is GUARD_LO*(early - c) - GUARD_HI*(late - c) (skew.py's
constants), where c is the part of A0's route the two branches share: one
physical wire cannot run fast on one leg and slow on the other, the same
reasoning as skew.py's divergence point.  The routed JSON gives each net's
route tree (ROUTING) but not per-pip delays, so c is an ESTIMATE: for each of
the two sinks, its interconnect delay times the fraction of its pips that lie on
the shared prefix, and the smaller of the two.  It must be > 0.  rst is told from A0 by fanout: both reach ustate
and ua_k, and rst reaches far more cells.

Exit status 1 on any violation, 2 if an arbiter cannot be resolved (a gap,
not a pass), 0 otherwise.
"""
import json, re, sys, pathlib, collections

sys.path.insert(0, str(pathlib.Path(__file__).resolve().parent))
GUARD_LO, GUARD_HI = 0.772, 1.155   # verify/skew.py

RE_INST = re.compile(r"\(INSTANCE\s+(\S*?)\)")
RE_IO = re.compile(r"\(IOPATH\s+(\S+)\s+(\S+)\s+\((\d+):")
RE_IC = re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\((\d+):")


def unesc(s):
    return s.replace("\\", "")


def main(argv):
    sdf = pathlib.Path(argv[0])
    jpath = sdf.with_name(sdf.stem + "_routed.json")
    top = [m for m in json.load(open(jpath))["modules"].values()
           if m.get("attributes", {}).get("top")]
    cells = top[0]["cells"]

    io, ic = {}, {}
    inst = None
    for line in open(sdf):
        m = RE_IC.search(line)
        if m:
            ic[(unesc(m.group(1)), unesc(m.group(2)))] = int(m.group(3))
            continue
        m = RE_INST.search(line)
        if m:
            inst = unesc(m.group(1))
            continue
        m = RE_IO.search(line)
        if m and inst:
            io[(inst, m.group(1), m.group(2))] = int(m.group(3))

    routes = {}
    for nn in top[0]["netnames"].values():
        r = nn.get("attributes", {}).get("ROUTING")
        if r and nn["bits"]:
            routes.setdefault(nn["bits"][0], r)

    def path_to(bit, cn):
        """Wires from the net's source to the input of cell `cn`, source first.
        The route names PHYSICAL LUT pins (after nextpnr's pin permutation),
        the cell's connections logical ones, so the sink is found as the one
        site wire of this net on the cell's own LUT (site + letter)."""
        r = routes.get(bit)
        bel = cells[cn]["attributes"].get("NEXTPNR_BEL", "")
        if r is None or "/" not in bel:
            return None
        site, lut = bel.split("/")
        sink = re.compile(r"^SITEWIRE/%s/%s[1-6]$" % (re.escape(site), lut[0]))
        f = r.split(";")
        parent = {}
        for i in range(0, len(f) - 2, 3):
            w, pip = f[i], f[i + 1]
            parent[w] = pip.split("->")[0] if "->" in pip else None
        hits = [w for w in parent if sink.match(w)]
        if len(hits) != 1:
            return None
        out, w, seen = [], hits[0], set()
        while w is not None and w not in seen:
            seen.add(w)
            out.append(w)
            w = parent.get(w)
        return out[::-1]

    def shared_ps(bit, sink_a, d_a, sink_b, d_b):
        pa, pb = path_to(bit, sink_a[0]), path_to(bit, sink_b[0])
        if not pa or not pb:
            return 0
        n = 0
        for x, y in zip(pa, pb):
            if x != y:
                break
            n += 1
        hops_a, hops_b = max(len(pa) - 1, 1), max(len(pb) - 1, 1)
        shared = max(n - 1, 0)
        return int(min(d_a * shared / hops_a, d_b * shared / hops_b))

    driver, fanout = {}, collections.Counter()
    for cn, c in cells.items():
        for p, d in c.get("port_directions", {}).items():
            for b in c["connections"].get(p, []):
                if d == "output":
                    driver[b] = (cn, p)
                else:
                    fanout[b] += 1

    def pins(cn):
        c = cells[cn]
        return {p: c["connections"][p][0] for p, d in c["port_directions"].items()
                if d == "input" and c["connections"].get(p)}

    def out_bit(cn):
        c = cells[cn]
        for p in ("O6", "O5", "O"):
            if p in c["connections"] and c["port_directions"].get(p) == "output":
                return p, c["connections"][p][0]
        return None, None

    arbs = sorted(cn[:-len(".ustate$LUT6")] for cn in cells if cn.endswith(".ustate$LUT6"))
    print(f"rule J       {sdf}")
    print(f"             {len(arbs)} bd_arbiter(s); guardband {GUARD_LO}*early vs {GUARD_HI}*late "
          f"past the shared part of A0's route")
    bad = gaps = 0
    for a in arbs:
        st = a + ".ustate$LUT6"
        _, q = out_bit(st)
        for k, gcell in ((1, a + ".ugrant$LUT5"), (2, a + ".ugrant$LUT6")):
            ua = a + f".ua{k}.u"
            try:
                gport, g = out_bit(gcell)
                if gcell.endswith("$LUT5") and "O5" in cells[gcell]["connections"]:
                    gport, g = "O5", cells[gcell]["connections"]["O5"][0]
                pu, ps, pg = pins(ua), pins(st), pins(gcell)
                common = set(pu.values()) & set(ps.values())
                common -= {q, g}
                ext = [b for b in common if driver.get(b, ("", ""))[0].startswith(a + ".") is False]
                a0 = min(ext, key=lambda b: fanout[b])
                d_cell, d_port = driver[a0]
                src = f"{d_cell}/{d_port}"
                ua_a0 = next(p for p, b in pu.items() if b == a0)
                ua_g = next(p for p, b in pu.items() if b == g)
                st_a0 = next(p for p, b in ps.items() if b == a0)
                g_q = next(p for p, b in pg.items() if b == q)
                d_ua, d_st = ic[(src, f"{ua}/{ua_a0}")], ic[(src, f"{st}/{st_a0}")]
                c = shared_ps(a0, (ua, ua_a0), d_ua, (st, st_a0), d_st)
                late = d_ua + io[(ua, ua_a0, "O6")]
                early = (d_st + io[(st, st_a0, "O6")]
                         + ic[(f"{st}/O6", f"{gcell}/{g_q}")] + io[(gcell, g_q, gport)]
                         + ic[(f"{gcell}/{gport}", f"{ua}/{ua_g}")] + io[(ua, ua_g, "O6")])
            except (KeyError, StopIteration, ValueError) as e:
                print(f"  {a} client {k}: NOT RESOLVED ({type(e).__name__} {e}) -- a gap, not a pass")
                gaps += 1
                continue
            margin = int(GUARD_LO * (early - c) - GUARD_HI * (late - c))
            ok = margin > 0
            bad += not ok
            print(f"  {'ok      ' if ok else 'VIOLATED'} {a} client {k}: A0 late {late} ps, "
                  f"grant early {early} ps, shared {c} ps, raw {early - late:+d}, guarded {margin:+d}")
    if bad:
        print(f"\n  {bad} arbiter handover(s) can acknowledge a client before the server "
              f"has begun its transaction.")
        return 1
    if gaps:
        return 2
    print("\n  every arbiter's A0 reaches its ack C-elements before the grant it unlocks")
    return 0


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
