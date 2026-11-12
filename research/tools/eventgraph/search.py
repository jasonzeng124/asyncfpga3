#!/usr/bin/env python3
"""search.py GRAPHDIR SIZES_VH [--steps N] -- PROGRAM.md FIRST item step 4: the smallest set of BUILDABLE edits that
brings the predicted period toward the floor, greedy, from one base graph.

Candidates are only edits bdc can already build, each with the parameters the build would get:
  depth:LINK:SD:0        BDC_LINK_DEPTHS=LINK=d+1 (new stage at the input; SD = the pipe's SDELAY from SIZES_VH if the
                         link is already a pipe, else bdc's STAGE_PAD 3)
  stage:Z_REQ:Z_ACK:4:6:fastrise   BDC_MERGE_OUT_LINK=MERGE (a bd_link with SELECT_PAD 4 / ACK_PAD 6) per bdc_amerge
  fastfall:BDC           BDC_LINK_FASTFALL=1 (single-stage links' rdly and 2-input muxes' udly fall in one element)
Each step takes the candidate with the lowest predicted period; it stops when no candidate gains 300 ps (a third of
the ~1 ns seed scatter) or after --steps.  Prints each step's period, cycle and polarity changes, and the floor.
"""
import sys, os, re
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from whatif import G, polarity_floor  # noqa: E402


def candidates(g, sizes):
    sz = open(sizes).read()
    out = []
    for inst, (t, par, ports) in g.verilog().items():
        if t in ("bd_link", "bd_pipe") and inst.startswith("ulink_"):
            sd = 3
            if t == "bd_pipe":
                m = re.search(r"BD_SZ_BRIDGE_I_UDUT_%s_SDELAY\s+(\d+)" % inst.upper(), sz)
                if m: sd = int(m.group(1))
            out.append("depth:%s:%d:0" % (inst, sd))
        if t.startswith("bdc_amerge"):
            out.append("stage:%s:%s:4:6:fastrise" % (ports["z_req"][0], ports["z_ack"][0]))
    out.append("fastfall:BDC")
    return out


def apply(g, ed):
    if ed == "fastfall:BDC":
        # BDC_LINK_FASTFALL=1: RFAST on every single-stage bd_link's rdly (not a bd_pipe's stages, so not a link this
        # edit set deepened, and not the merge-output link) and FASTFALL on every 2-input bd_mux's udly
        deep = getattr(g, "deepened", set())
        insts = {n["inst"] for n in g.nodes if (n["inst"].startswith("ulink_") and ".rdly.chain" in n.get("cell", "")
                 and "many.stage" not in n.get("cell", "") and n["inst"] not in deep)
                 or (n["inst"].startswith("umux") and ".udly.chain" in n.get("cell", ""))}
        for i in insts: g.fastfall(i, strict=False)
        return g
    return g.apply(ed)


def predict(base, eds):
    g = base.copy()
    for e in sorted(eds, key=lambda e: e.startswith("fastfall")):    # the knob acts on the final structure
        apply(g, e)
    return g.period(), g


def main():
    d, sizes = sys.argv[1], sys.argv[2]
    steps = int(sys.argv[sys.argv.index("--steps") + 1]) if "--steps" in sys.argv else 4
    g = G(d)
    (lam0, cyc0), _ = predict(g, [])
    fl = polarity_floor(g)
    print("base %.0f ps; floor (no polarity change) R %.0f F %.0f" % (lam0, fl["R"][0], fl["F"][0]))
    chosen, cur = [], lam0
    cands = candidates(g, sizes)
    for step in range(steps):
        res = []
        for c in cands:
            if c in chosen: continue
            try:
                (lam, cyc), g2 = predict(g, chosen + [c])
            except ValueError as x:
                continue
            res.append((lam, c, g2, cyc))
        if not res: break
        res.sort(key=lambda r: r[0])
        lam, c, g2, cyc = res[0]
        print("step %d: best %-60s %.0f ps (%+.0f); runner-up %s %.0f" % (step + 1, c, lam, lam - cur,
              res[1][1] if len(res) > 1 else "-", res[1][0] if len(res) > 1 else 0))
        if cur - lam < 300:
            print("  stop: < 300 ps gain"); break
        by, flips = g2.describe(cyc)
        print("  cycle: %s; polarity changes %d" % (", ".join(by), len(flips)))
        chosen.append(c); cur = lam
    print("chosen: %s -> %.0f ps (%.3fx)" % (" ".join(chosen) or "-", cur, lam0 / cur))
    print("ENV " + " ".join(to_env(g, chosen)))


def to_env(g, chosen):
    """the bdc knobs that build the chosen edits"""
    depths, mo, ff = [], [], False
    for c in chosen:
        p = c.split(":")
        if p[0] == "depth":
            t, par, ports = g.verilog()[p[1]]
            n = int(re.search(r"\.N\((\d+)\)", par).group(1)) if t == "bd_pipe" else 1
            depths.append("%s=%d" % (p[1], n + 1))
        elif p[0] == "stage":
            mo += [i for i, (t, par, ports) in g.verilog().items() if t.startswith("bdc_amerge") and ports["z_req"][0] == p[1]]
        elif c == "fastfall:BDC":
            ff = True
    out = []
    if depths: out.append("BDC_LINK_DEPTHS=" + ",".join(depths))
    if mo: out.append("BDC_MERGE_OUT_LINK=" + ",".join(mo))
    if ff: out.append("BDC_LINK_FASTFALL=1")
    return out


if __name__ == "__main__":
    main()
