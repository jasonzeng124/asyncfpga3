"""Auditor P16 (shard C, 6c95637a): independent spot check of the committed 11g Lean data against the
committed bitstream read-back FASM (fixture gcd_hw_<s>.fromBit.fasm.xz, sha256 checked separately).
For every LUT site the FASM sets an INIT on, compare with the INIT of the physical lut6_2 instance in
Formal/Net/FasmDesign/Gcd<s>/C*.lean. Site -> tile mapping without prjxray-db: within each row Y the CLB
tiles' X coordinates are ranked globally and matched to slice-pair columns (SLICE_X 2k / 2k+1) by rank.
Usage: python3 -I C_initcmp.py <seed> <Lean dir> <fromBit.fasm.xz>"""
import re, sys, lzma, glob
from collections import Counter
seed, ldir, fz = sys.argv[1:4]
fasm = {}
for line in lzma.open(fz, 'rt'):
    m = re.match(r'(CLBL[LM]_[LR])_X(\d+)Y(\d+)\.SLICE[LM]_X([01])\.([A-D])LUT\.INIT\[(\d+)(?::(\d+))?\](?: = \d+\'b([01]+))?', line)
    if m:
        tt, tx, ty, sx, let, hi, lo, bits = m.groups()
        lo = int(lo) if lo is not None else int(hi)
        val = int(bits, 2) if bits is not None else 1   # a single-bit feature with no value = 1
        k = (int(tx), int(ty), int(sx), let)
        fasm[k] = fasm.get(k, 0) | (val << lo)
lean = {}
for f in sorted(glob.glob(ldir + '/C*.lean')):
    for m in re.finditer(r'"SLICE_X(\d+)Y(\d+)\.([A-D])LUT", \.lut6_2, 0x([0-9A-F]+)', open(f).read()):
        x, y, let, init = m.groups()
        lean[(int(x), int(y), let)] = int(init, 16)
tcols = sorted({k[0] for k in fasm}); scols = sorted({k[0] // 2 for k in lean})
print(f'seed {seed}: FASM LUT INITs {len(fasm)}, Lean phys lut6_2 {len(lean)} (nonzero {sum(1 for v in lean.values() if v)}); '
      f'CLB tile columns {len(tcols)}, slice-pair columns {len(scols)}')
# multiset check (mapping-free)
mf = Counter(v for v in fasm.values() if v); ml = Counter(v for v in lean.values() if v)
print('  multiset of nonzero INITs equal:', mf == ml)
if len(tcols) == len(scols):
    cmap = dict(zip(scols, tcols))
    bad = 0; n = 0; missing = 0
    for (x, y, let), v in lean.items():
        key = (cmap[x // 2], y, x % 2, let)
        fv = fasm.get(key, 0); n += 1
        if fv != v: bad += 1
    extra = sum(1 for k, v in fasm.items() if v and (k[0] not in tcols))
    print(f'  rank-mapped site-by-site compare: {n} Lean LUT sites, {bad} INIT mismatches')
else:
    print('  column counts differ; site-by-site compare skipped')
