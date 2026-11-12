# T65: own trace of every mux SELECT path in a bdc-emitted kernel (independent of bdc's emit.select_channels):
# from each bd_mux's ctl_req net, walk drivers backwards through links/pipes, forks and plain assigns, collecting every
# link instance, until a non-trivial producer (merge, compare, ...). Then compare a candidate sizes file with its base on
# every parameter of those links (DELAY, SDELAY, UACK) and every mux DELAY.  usage: seltrace.py KERNEL.v BASE.vh CAND.vh PREFIX
import re, sys
src = open(sys.argv[1]).read()
def rd(f):
    return {m[1]: int(m[2]) for m in re.finditer(r'`define (BD_SZ_\S+)\s+(\d+)', open(f).read())}
b, c, pre = rd(sys.argv[2]), rd(sys.argv[3]), sys.argv[4]
drv = {}   # net -> ('link', inst, in_net) | ('fork', inst, in_net) | ('assign', None, in_net) | ('other', inst, None)
for m in re.finditer(r'(bd_link|bd_pipe)\s*#\(.*?\)\s*(\w+)\s*\((.*?)\);', src, re.S):
    i = re.search(r'\.req_in\((\w+)_req\)', m[3])[1]; o = re.search(r'\.req_out\((\w+)_req\)', m[3])[1]
    drv[o] = ('link', m[2], i)
for m in re.finditer(r'bd_fork\s*#\(.*?\)\s*(\w+)\s*\((.*?)\);', src, re.S):
    i = re.search(r'\.req\((\w+)_req\)', m[2])[1]
    for o in re.findall(r'(\w+)_req', re.search(r'\.req_out\(\{?(.*?)\}?\)', m[2])[1]): drv[o] = ('fork', m[1], i)
for m in re.finditer(r'assign\s+(\w+)_req\s*=\s*(\w+)_req\s*;', src): drv.setdefault(m[1], ('assign', None, m[2]))
muxes = re.findall(r'bd_mux\s*#\(.*?\)\s*(\w+)\s*\(.*?\.ctl_req\((\w+)_req\)', src, re.S)
links = set()
for mux, net in muxes:
    path, n = [], net
    while n in drv and drv[n][0] in ('link', 'fork', 'assign'):
        k, inst, n2 = drv[n]
        path.append(f"{k}:{inst}" if inst else f"assign:{n}")
        if k == 'link': links.add(inst)
        n = n2
    print(f"{mux}: ctl {net} <- " + " <- ".join(path) + f" <- [{n}]")
print("select-path links:", sorted(links))
def key(inst, suf=''): return f"{pre}{inst.upper()}{suf}"
bad, seen = [], 0
for inst in sorted(links):
    for suf in ('', '_SDELAY', '_UACK'):
        k = key(inst, suf)
        if k in b or k in c:
            seen += 1
            bv, cv = b.get(k), c.get(k)
            flag = '' if (bv is None or cv is None or cv >= bv) else '  <-- SHORTER'
            if flag: bad.append(k)
            print(f"  {k}: base {bv} cand {cv}{flag}")
for mux, _ in muxes:
    k = key(mux); bv, cv = b.get(k), c.get(k)
    flag = '' if (bv is None or cv is None or cv >= bv) else '  <-- SHORTER'
    if flag: bad.append(k)
    print(f"  {k}: base {bv} cand {cv}{flag}")
print(f"RESULT {sys.argv[3].split('/')[-1]} vs {sys.argv[2].split('/')[-1]}: {len(bad)} select-path parameters shorter than base: {bad}")
