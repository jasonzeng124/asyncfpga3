"""negsel.py ROUTED_JSON SRC_SDF DST_SDF DELTA_PS [MUX] -- the select-race negative control: a copy of a route's prjxray
SDF with every INTERCONNECT into a bdc_muxnN decode LUT's INDEX pins (tighten.py muxn_decode_sites(): every pin of
sel[k] = ctl_req & (s == k) but ctl_req) lengthened by DELTA_PS, all of min:typ:max, rise and fall.  The request pins
and every other arc are untouched, so the index arrives at the decode DELTA_PS later and nothing else moves.
MUX (optional): only the decode LUTs of that mux instance (e.g. bridge_i.udut.umux13).  Prints what it changed."""
import pathlib, re, sys
HERE = pathlib.Path(__file__).resolve()
sys.path.insert(0, str(HERE.parents[4] / "cells" / "verify"))
jpath, src, dst, delta = pathlib.Path(sys.argv[1]), sys.argv[2], sys.argv[3], int(sys.argv[4])
mux = sys.argv[5] if len(sys.argv) > 5 else None
sys.argv = [sys.argv[0], src]
import tighten as T                                                     # noqa: E402
sites, notes = T.muxn_decode_sites(jpath)
pins = {sp for parent, cell, rp, sps in sites if mux in (None, parent) for sp in sps}
assert pins, "no bdc_muxnN decode index pin%s" % (" under " + mux if mux else "")
unesc = lambda s: re.sub(r"\\(.)", r"\1", s)
hit = set()
with open(src) as f, open(dst, "w") as g:
    for ln in f:
        m = re.match(r"^(\s*\(INTERCONNECT )(\S+) (\S+) (.*)$", ln)
        if m and unesc(m.group(3)) in pins:
            ln = m.group(1) + m.group(2) + " " + m.group(3) + " " + re.sub(
                r"\((\d+):(\d+):(\d+)\)", lambda q: "(%d:%d:%d)" % tuple(int(x) + delta for x in q.groups()),
                m.group(4)) + "\n"
            hit.add(unesc(m.group(3)))
            print("+%d ps  %s -> %s" % (delta, unesc(m.group(2)), unesc(m.group(3))))
        g.write(ln)
missing = pins - hit
assert not missing, "index pins with no INTERCONNECT in %s: %s" % (src, sorted(missing))
print("%d interconnect(s) lengthened by %d ps (%d index pins of %d decode LUT(s))" % (
    len(hit), delta, len(pins), len({p.rsplit('/', 1)[0] for p in pins})))
