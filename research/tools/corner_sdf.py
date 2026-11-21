#!/usr/bin/env python3
"""corner_sdf.py XRAY_SDF ROUTED_JSON OUT_SDF [--band B] [--cell CT=b,...] [--inst-rx REGEX:b ...] [--inst-file FILE:b]
-- the prjxray SDF of one route collapsed to ONE delay corner, every triple written v:v:v.

    # the full-stack gate's worst case (PROGRAM item 1): chains 0.21, CARRY4/F7F8/FF SLOW_MAX, the rest 0.288
    python3 research/tools/corner_sdf.py pnr/soak_xray.sdf pnr/soak_routed.json corner/soak.sdf \\
        --band 0.288 --cell CARRY4=1,SELMUX2_1=1,SLICE_FFX=1 --inst-rx '\\.chain\\.g\\[\\d+\\]\\.u$:0.21'
    # FAST_MIN everywhere
    python3 research/tools/corner_sdf.py pnr/soak_xray.sdf pnr/soak_routed.json corner/soak.sdf --band 0

XRAY_SDF is cells/gls/fid/xray_delay.py's output: nextpnr instance names, every triple FAST_MIN:SLOW_MIN:SLOW_MAX.
Each arc gets  v = round(FAST_MIN + b * (SLOW_MAX - FAST_MIN))  with the band b chosen EXACTLY as cells/gls/gen.py
(GLS_SDF_FIELD=band) chooses it -- see gen.py's tri() and read_sdf():

  * IOPATH of an instance listed by --inst-rx / --inst-file: that instance's band (wins over --cell);
  * else IOPATH of a cell type named in --cell: that type's band (gen.py's GLS_SDF_BAND_CELL);
  * INTERCONNECT whose DESTINATION instance is listed: that band (gen.py: "every INTERCONNECT arc INTO them");
  * everything else, INTERCONNECT included (gen.py never applies the cell band to a wire): --band.

gen.py reads only the first triple of a line; both rise and fall triples are collapsed here with the same band, so a
reader of either column sees this corner.  SETUPHOLD keeps its first (FAST_MIN) value, which is what gen.py reads.

The instance band in the full stack is a GLS_SDF_BAND_INST file of BELs (research/tools/band_inst_list.py), because
the full-stack netlist is decoded from the bits and named by BEL.  Each bd_delay chain cell is one BEL (a 6LUT and a
5LUT are separate BELs in fasm2net), so matching the same regex on nextpnr's cell names selects the same arcs.  ROUTED_JSON
checks that: every --inst-rx cell must have a NEXTPNR_BEL and be in the SDF, and --inst-file entries may be BELs (as in
pnr/chains.band), mapped back to cells through NEXTPNR_BEL.  A listed instance missing from the SDF is an error, as in
gen.py.

Self-check printed: arcs moved per class (instance band IOPATH / INTERCONNECT, each cell type, default), and the count
of instances listed vs found -- compare with the GLS_SDF_BAND_INST / GLS_SDF_BAND_CELL lines of a full-stack
generate.log (those count the decoded netlist, whose interconnect is split differently, so INTERCONNECT counts differ;
IOPATH counts per cell type should be close).
"""
import argparse, collections, json, re, sys

RE_CT = re.compile(r'\(CELLTYPE "([^"]*)"\)')
RE_INST = re.compile(r"\(INSTANCE\s+(\S*?)\)")
RE_IO = re.compile(r"\(IOPATH\s+(\S+)\s+(\S+)\s+\(")
RE_IC = re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\(")
RE_SH = re.compile(r"\(SETUPHOLD\s")
RE_TRI = re.compile(r"\((-?\d+):(-?\d+):(-?\d+)\)")


def unesc(s):
    return s.replace("\\", "")


def parse_args(argv):
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("xray_sdf")
    ap.add_argument("routed_json")
    ap.add_argument("out_sdf")
    ap.add_argument("--band", type=float, default=0.288)
    ap.add_argument("--cell", default="", help="CELLTYPE=b[,CELLTYPE=b...] (IOPATH only)")
    ap.add_argument("--inst-rx", action="append", default=[], help="REGEX:b on nextpnr cell names (repeatable)")
    ap.add_argument("--inst-file", action="append", default=[],
                    help="FILE[:b] -- lines 'NAME band' (BEL or cell name); :b overrides the file's band")
    return ap.parse_args(argv)


def inst_bands(a):
    """{nextpnr cell name: band} from --inst-rx / --inst-file, checked against the routed JSON."""
    cells = list(json.load(open(a.routed_json))["modules"].values())[0]["cells"]
    by_bel = {}
    for n, c in cells.items():
        bel = c.get("attributes", {}).get("NEXTPNR_BEL")
        if bel:
            by_bel.setdefault(bel, []).append(n)
    out = {}
    for spec in a.inst_rx:
        rx, _, b = spec.rpartition(":")
        r = re.compile(rx)
        hit = [n for n in cells if r.search(n)]
        if not hit:
            sys.exit("corner_sdf: --inst-rx %r matches no cell" % rx)
        for n in hit:
            if not cells[n].get("attributes", {}).get("NEXTPNR_BEL"):
                sys.exit("corner_sdf: %s has no NEXTPNR_BEL" % n)
            out[n] = float(b)
    for spec in a.inst_file:
        path, b = spec, None
        m = re.match(r"^(.*):([0-9.]+)$", spec)
        if m:
            path, b = m.group(1), float(m.group(2))
        for ln in open(path):
            if not ln.strip() or ln.startswith("#"):
                continue
            name, v = ln.split()
            v = b if b is not None else float(v)
            names = by_bel.get(name) or ([name] if name in cells else None)
            if not names:
                sys.exit("corner_sdf: %s in %s is neither a BEL nor a cell of %s" % (name, path, a.routed_json))
            for n in names:
                out[n] = v
    return out


def collapse(line, band):
    def f(m):
        lo, hi = int(m.group(1)), int(m.group(3))
        v = int(round(lo + band * (hi - lo)))
        return "(%d:%d:%d)" % (v, v, v)
    return RE_TRI.sub(f, line)


def main(argv=None):
    a = parse_args(sys.argv[1:] if argv is None else argv)
    cellband = {k: float(v) for k, v in (kv.split("=") for kv in filter(None, a.cell.split(",")))}
    ib = inst_bands(a)
    n = collections.Counter()
    seen_inst = set()
    ct = inst = None
    out = []
    for line in open(a.xray_sdf):
        m = RE_CT.search(line)
        if m:
            ct = m.group(1)
        m = RE_IC.search(line)
        if m:
            dst = unesc(m.group(2)).rpartition("/")[0]
            if dst in ib:
                band, cls = ib[dst], "INTERCONNECT into listed instance (%g)" % ib[dst]
            else:
                band, cls = a.band, "INTERCONNECT default (%g)" % a.band
            n[cls] += 1
            out.append(collapse(line, band))
            continue
        m = RE_INST.search(line)
        if m:
            inst = unesc(m.group(1))
            if inst in ib:
                seen_inst.add(inst)
            out.append(line)
            continue
        if RE_IO.search(line):
            if inst in ib:
                band, cls = ib[inst], "IOPATH listed instance (%g)" % ib[inst]
            elif ct in cellband:
                band, cls = cellband[ct], "IOPATH %s (%g)" % (ct, cellband[ct])
            else:
                band, cls = a.band, "IOPATH default (%g)" % a.band
            n[cls] += 1
            out.append(collapse(line, band))
            continue
        if RE_SH.search(line):
            n["SETUPHOLD (FAST_MIN, as gen.py)"] += 1
            out.append(RE_TRI.sub(lambda m: "(%s:%s:%s)" % ((m.group(1),) * 3), line))
            continue
        if RE_TRI.search(line):
            sys.exit("corner_sdf: a delay triple on a line this tool does not know: %r" % line[:120])
        out.append(line)
    missing = set(ib) - seen_inst
    if missing:
        sys.exit("corner_sdf: %d listed instance(s) not in the SDF (e.g. %s) -- wrong naming?"
                 % (len(missing), sorted(missing)[:3]))
    with open(a.out_sdf, "w") as f:
        f.writelines(out)
    print("corner_sdf: %s -> %s" % (a.xray_sdf, a.out_sdf))
    print("  band %g, cells %s, %d instance(s) listed (%s), all in the SDF"
          % (a.band, cellband or "none", len(ib), ", ".join(sorted({"%g" % v for v in ib.values()})) or "-"))
    for k in sorted(n):
        print("  %-48s %6d arcs" % (k, n[k]))
    return 0


if __name__ == "__main__":
    sys.exit(main())
