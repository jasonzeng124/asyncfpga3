# own extraction of the gcd kernel's boundary nets from the (flattened) yosys JSON of the target build
import json, sys, re, collections
m = next(iter(json.load(open(sys.argv[1]))['modules'].values()))
nn = m['netnames']
def bits(name):
    return nn[name]['bits'] if name in nn else None
cands = [n for n in nn if re.search(r'udut\.(a|b|start|out0|end|p_end)_(data|req|ack|valid|ready)$', n) or re.search(r'^urig\.(a_v|b_v)$', n)]
for n in sorted(cands):
    b = nn[n]['bits']
    if len(b) == 1: print(f"{n}: {b}")
    else:
        groups = collections.defaultdict(list)
        for i, x in enumerate(b): groups[str(x)].append(i)
        consts = [i for i, x in enumerate(b) if isinstance(x, str)]
        multi = {k: v for k, v in groups.items() if len(v) > 1 and not k.startswith("'") and k not in ('0','1')}
        print(f"{n}: width {len(b)}, distinct non-const nets {len({str(x) for x in b if not isinstance(x,str)})}, const bits {consts}, shared {list(multi.values())}")
