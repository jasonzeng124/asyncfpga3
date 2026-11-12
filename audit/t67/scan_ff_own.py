# T67: own scan, extending T43's 5FF scan to the four main slice flops: every flop with any <X>FF.* (or <X>5FF.*) feature in a
# FASM must also carry an <X>FFMUX.* (<X>5FFMUX.*) feature; every AFFMUX/5FFMUX option sets >= 1 segbit in prjxray-db,
# so a missing mux feature leaves the D select at all-zero bits, i.e. unselected.  usage: scan_ff_own.py FASM...
import re, sys
for fn in sys.argv[1:]:
    ff, mux = set(), set()
    for l in open(fn):
        l = l.split('#')[0].strip()
        if not l: continue
        f = l.split()[0]
        m = re.match(r'(\S+)\.(SLICE[LM]_X\d)\.([A-D]5?)FF\.', f)
        if m: ff.add(m.groups())
        m = re.match(r'(\S+)\.(SLICE[LM]_X\d)\.([A-D]5?)FFMUX\.', f)
        if m: mux.add(m.groups())
    miss = sorted(ff - mux)
    print(f"{fn}: flops configured {len(ff)} (5FF {sum(1 for x in ff if '5' in x[2])}), with mux {len(ff & mux)}, MISSING MUX {len(miss)} {miss[:6]}")
