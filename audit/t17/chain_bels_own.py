# T17: own selection of matched-delay chain LUTs in a routed JSON by their *source line* (yosys src attribute in
# bd_latch.v bd_delay / bd_delay_gated LUT instantiations), not by research's name regex; compare with the regex.
# usage: chain_bels_own.py ROUTED_JSON BD_LATCH_V
import json, re, sys
m = list(json.load(open(sys.argv[1]))["modules"].values())[0]
src = open(sys.argv[2]).read().split('\n')
# line numbers of LUT instantiations inside module bd_delay / bd_delay_gated
lines, cur = set(), None
for i, l in enumerate(src, 1):
    mm = re.match(r'\s*module\s+(\w+)', l)
    if mm: cur = mm.group(1)
    if cur in ('bd_delay', 'bd_delay_gated') and re.search(r'\bLUT\d\b.*\bu\s*\(', l): lines.add(i)
print('bd_delay LUT source lines', sorted(lines))
rx = re.compile(r'\.chain\.g\[\d+\]\.u$')
own, reg, types = set(), set(), {}
for n, c in m["cells"].items():
    s = c["attributes"].get("src", "")
    hit = any(re.search(r'bd_latch\.v:%d\.' % ln, s) for ln in lines)
    if hit: own.add(n); types[c["type"]] = types.get(c["type"], 0) + 1
    if rx.search(n): reg.add(n)
print('own (by src line) %d cells, types %s' % (len(own), types))
print('regex %d cells; regex-only %d, own-only %d' % (len(reg), len(reg - own), len(own - reg)))
for n in sorted(own - reg)[:8]: print('  own-only', n)
for n in sorted(reg - own)[:8]: print('  regex-only', n, m["cells"][n]["type"], m["cells"][n]["attributes"].get("src", "")[:80])
bels = {m["cells"][n]["attributes"].get("NEXTPNR_BEL") for n in own}
print('own BELs', len(bels), 'missing BEL', sum(1 for n in own if not m["cells"][n]["attributes"].get("NEXTPNR_BEL")))
