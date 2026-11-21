#!/usr/bin/env python3
"""scale_sdf.py -- put gen.py's exact scatter factors on a route's NEXTPNR-NAMED SDF,
so the post-route rules (cells/verify/tighten.py) can be run on one GLS draw.

    scale_sdf.py --hw HWDIR --fid FIDDIR --out OUT.sdf [--base xray|nextpnr]
                 [--factors FACTORS.tsv]

HWDIR  : cells/build/hw/gcd_hw (gcd_hw.sdf, gcd_hw_routed.json, gcd_hw_xray.sdf)
FIDDIR : fasm2net.py output for that route (fasm_routed.json, fasm.sdf) -- the
         exact files the full-stack GLS gives gen.py (build_fid.sh copies them to
         routed.json / routed.sdf).  REQUIRED for exactness: gen.py's per-arc
         Gaussian draws are consumed in fasm.sdf's line order and its wire
         factors hash the pip names of fasm_routed.json's ROUTING.
Env    : exactly gen.py's knobs (GLS_SCATTER_REGION, GLS_SCATTER, GLS_SCATTER_MODE,
         GLS_SCATTER_SEED, GLS_REGION_SLICES, GLS_SCATTER_LOGN, GLS_DELAY_SCALE,
         GLS_SDF_FIELD, GLS_SDF_BAND).  GLS_SDF_FIELD/BAND only pick the BASE value
         read from the xray SDF (--base xray); factors do not depend on them.

How the factors are obtained (no reimplementation): gen.py is IMPORTED with
GLS_WORK pointing at FIDDIR's files, its tri() is replaced by a constant 10**9,
and its own read_sdf() is run.  Every value it returns is then
round(1e9 * factor) with factor exactly what gen.py would multiply that arc by
(same RNG stream, same draw order, same region and wire models).  The factors
are then moved from fasm2net's bel names back to nextpnr's cell names
(cell -> NEXTPNR_BEL; interconnect keyed by its SINK bel/pin, as fasm2net's
rekey_sdf does, including its sibling-LUT fallback) and applied to the chosen
base SDF.  Output keeps the base SDF's text and names; only the numbers of
IOPATH / INTERCONNECT triples change (all three columns set to the scaled
value).  SETUPHOLDs are untouched, as in gen.py.

Not modelled: gen.py's DSP48E1 "largest arc of the group" step (gcd has no DSP
on this route? counted and printed).
"""
import argparse, json, os, re, sys, collections, tempfile

REPO = os.environ.get("REPO", "/home/user/asyncfpga3")
BIG = 10 ** 9


def load_gen(fid):
    work = tempfile.mkdtemp(prefix="scale_sdf_")
    os.symlink(os.path.abspath(os.path.join(fid, "fasm_routed.json")), os.path.join(work, "routed.json"))
    os.symlink(os.path.abspath(os.path.join(fid, "fasm.sdf")), os.path.join(work, "routed.sdf"))
    os.environ["GLS_WORK"] = work
    sys.path.insert(0, os.path.join(REPO, "cells/gls"))
    import gen  # noqa: E402  reads the env knobs at import, like a fresh gen.py run
    gen.tri = lambda m, first: BIG
    return gen, work


def set_draw(gen, region, wire, seed):
    """Re-point an imported gen at another (region sigma, wire sigma, draw) without
    re-reading the JSON: the same module state a fresh gen.py run starts from
    (fresh RNG, empty region cache, zeroed counters), using gen's own classes."""
    import random
    seed = str(seed)
    os.environ["GLS_SCATTER_SEED"] = seed
    os.environ["GLS_SCATTER"] = str(wire)
    os.environ["GLS_SCATTER_REGION"] = str(region)
    gen.SCATTER, gen.SCATTER_REGION = float(wire), float(region)
    gen._rng = random.Random(int(seed))
    gen.n_wire = gen.n_wire_fallback = gen.n_region = gen.n_region_miss = gen.n_scaled_inst = 0
    if gen.SCATTER_REGION:
        if gen._region is None:
            gen._region = gen.RegionModel(gen.JSON, gen.SCATTER_REGION, seed, gen.REGION_SLICES)
        gen._region.sigma, gen._region.seed, gen._region.cache = gen.SCATTER_REGION, seed, {}
    if gen.SCATTER and gen.SCATTER_MODE == "wire":
        if gen._wire is None:
            gen._wire = gen.WireModel(gen.JSON, gen.SCATTER, seed)
        gen._wire.sigma, gen._wire.seed = gen.SCATTER, seed


def factors(gen):
    iop, ic, _sh, n_io, n_ic, _ = gen.read_sdf(gen.SDF)
    io_f = {}                    # (bel, from, to, occ) -> factor
    for inst, arcs in iop.items():
        occ = collections.Counter()
        for a, z, v in arcs:
            io_f[(inst, a, z, occ[(a, z)])] = v / BIG
            occ[(a, z)] += 1
    ic_f = {dst: v / BIG for src, dst, v in ic}   # sink bel/pin -> factor
    stats = dict(n_io=n_io, n_ic=n_ic, n_wire=gen.n_wire, n_wire_fallback=gen.n_wire_fallback,
                 n_region=gen.n_region, n_region_miss=gen.n_region_miss)
    return io_f, ic_f, stats


RE_INST = re.compile(r"\(INSTANCE\s*(\S*?)\s*\)")
RE_IO = re.compile(r"(\(IOPATH\s+(\S+)\s+(\S+)\s+)(\(.*)$")
RE_IC = re.compile(r"(\(INTERCONNECT\s+(\S+)\s+(\S+)\s+)(\(.*)$")
RE_TRI = re.compile(r"\((\d+):(\d+):(\d+)\)")


def base_value(m, base):
    lo, mid, hi = (int(x) for x in m.groups())
    if base == "nextpnr":
        return lo                           # nextpnr writes the same number thrice
    fld = os.environ.get("GLS_SDF_FIELD", "min")
    if fld == "band":
        b = float(os.environ.get("GLS_SDF_BAND", "0.38"))
        return int(round(lo + b * (hi - lo)))
    return (lo, mid, hi)[{"min": 0, "typ": 1, "max": 2}[fld]]


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--hw", required=True)
    ap.add_argument("--fid", required=True)
    ap.add_argument("--out", required=True)
    ap.add_argument("--base", choices=["xray", "nextpnr"], default="xray")
    ap.add_argument("--factors", help="also write per-arc factors (nextpnr names) here")
    a = ap.parse_args()
    gen, work = load_gen(a.fid)
    io_f, ic_f, st = factors(gen)
    apply(a.hw, a.base, io_f, ic_f, st, a.out, a.factors)
    os.unlink(os.path.join(work, "routed.json")); os.unlink(os.path.join(work, "routed.sdf")); os.rmdir(work)


_cells = {}


def apply(hw, base, io_f, ic_f, st, out_path, factors_path=None):
    class A: pass
    a = A(); a.hw, a.base, a.out, a.factors = hw, base, out_path, factors_path
    if hw not in _cells:
        _cells[hw] = json.load(open(os.path.join(a.hw, "gcd_hw_routed.json")))["modules"]["top"]["cells"]
    cells = _cells[hw]
    bel = {}
    for n, c in cells.items():
        b = c["attributes"].get("NEXTPNR_BEL", "")
        bel[n] = "$VCC" if c["type"] == "PSEUDO_VCC" else "$GND" if c["type"] == "PSEUDO_GND" else b
        if c["type"] == "DSP48E1_DSP48E1":
            st["dsp_cells_not_grouped"] = st.get("dsp_cells_not_grouped", 0) + 1
    unesc = lambda s: s.replace("\\", "")
    src = os.path.join(a.hw, "gcd_hw_xray.sdf" if a.base == "xray" else "gcd_hw.sdf")
    out, fo = [], open(a.factors, "w") if a.factors else None
    cnt = collections.Counter()
    inst, occ = None, collections.Counter()
    for line in open(src):
        m = RE_IC.search(line)
        if m:
            s, d = unesc(m.group(2)), unesc(m.group(3))
            dc, _, dp = d.rpartition("/")
            b = bel.get(dc)
            f = ic_f.get("%s/%s" % (b, dp)) if b else None
            if f is None and b and re.search(r"[A-D][56]LUT$", b):
                sib = b[:-4] + ("5LUT" if b.endswith("6LUT") else "6LUT")
                f = ic_f.get("%s/%s" % (sib, dp))
                if f is not None:
                    cnt["ic_sibling"] += 1
            key = "IC %s -> %s" % (s, d)
        else:
            m = RE_INST.search(line)
            if m:
                inst, occ = unesc(m.group(1)), collections.Counter()
                out.append(line)
                continue
            m = RE_IO.search(line)
            if not m:
                out.append(line)
                continue
            fr, to = m.group(2), m.group(3)
            k = (bel.get(inst), fr, to, occ[(fr, to)])
            occ[(fr, to)] += 1
            f = io_f.get(k)
            key = "IO %s %s %s" % (inst, fr, to)
        kind = key[:2]
        if f is None:
            cnt[kind + "_unmatched"] += 1
            f = 1.0
        else:
            cnt[kind + "_matched"] += 1
        tri = RE_TRI.search(m.group(4))
        v = max(0, int(round(base_value(tri, a.base) * f)))
        rest = RE_TRI.sub("(%d:%d:%d)" % (v, v, v), m.group(4))
        out.append(line[:m.start()] + m.group(1) + rest + "\n")
        if fo:
            fo.write("%s\t%.9f\t%d\n" % (key, f, v))
    open(a.out, "w").write("".join(out))
    st.update(cnt)
    if fo:
        fo.close()
    sys.stderr.write("scale_sdf: base %s, %s\n" % (a.base, " ".join("%s=%s" % kv for kv in sorted(st.items()))))
    return st


if __name__ == "__main__":
    main()
