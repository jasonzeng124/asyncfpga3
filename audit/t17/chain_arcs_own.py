# T17: count SDF arcs a GLS_SDF_BAND_INST of the chain LUTs moves: IOPATH of those cells + INTERCONNECT into them.
# usage: chain_arcs_own.py ROUTED_JSON SDF [bel]   (bel: SDF keyed by NEXTPNR_BEL, as the bits-decoded GLS's routed.sdf)
import json, re, sys
m = list(json.load(open(sys.argv[1]))["modules"].values())[0]
rx = re.compile(r'\.chain\.g\[\d+\]\.u$')
ch = {n for n in m["cells"] if rx.search(n)}
if len(sys.argv) > 3: ch = {m["cells"][n]["attributes"]["NEXTPNR_BEL"] for n in ch}
un = lambda s: re.sub(r'\\(.)', r'\1', s)
io = ic = 0; cur = None; seen = set()
for l in open(sys.argv[2]):
    mm = re.search(r'\(INSTANCE\s*([^)]*)\)', l)
    if mm: cur = un(mm.group(1))
    if '(IOPATH' in l and cur in ch: io += 1; seen.add(cur)
    mm = re.match(r'\s*\(INTERCONNECT\s+(\S+)\s+(\S+)', l)
    if mm:
        d = un(mm.group(2)); c = d.rsplit('/', 1)[0]
        if c in ch: ic += 1
print('chain cells %d, with IOPATH in SDF %d; IOPATH arcs %d, INTERCONNECT into them %d, total %d' % (len(ch), len(seen), io, ic, io + ic))
