# Own scan (T44): for every 5FF (A5FF..D5FF) with any feature (ZINI/ZRST/...) in a FASM, is a <X>5FFMUX.* feature present?
# A configured 5FF without a 5FFMUX select leaves its D input unselected (research 94aa1084).  usage: scan_5ff_own.py FASM...
import re, sys
for fn in sys.argv[1:]:
    ff, mux = set(), set()
    for l in open(fn):
        l = l.strip().split('#')[0].strip()
        if not l: continue
        f = l.split()[0]
        m = re.match(r'(\S+)\.(SLICE[LM]_X\d)\.([A-D])5FF\.', f)
        if m: ff.add((m.group(1), m.group(2), m.group(3)))
        m = re.match(r'(\S+)\.(SLICE[LM]_X\d)\.([A-D])5FFMUX\.', f)
        if m: mux.add((m.group(1), m.group(2), m.group(3)))
    miss = sorted(ff - mux)
    print(fn, "5FF configured:", len(ff), "with 5FFMUX:", len(ff & mux), "MISSING 5FFMUX:", len(miss), miss[:4])
