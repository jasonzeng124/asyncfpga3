"""Drift check for C-9d (a): what bdc's reset puts in a ring.
Usage: python3 resetscan.py EMITTED.v [...]   (bdc/emit.py output)
For every LUT whose rst input sits on a pin, in the emitted file AND in every cells/rtl module
it instantiates (transitively), evaluate the INIT with that pin at 1 over all other pins and
report the reset value (0 = comes up empty). Also lists every *_set cell reachable from the design."""
import re, sys, os, itertools
ROOT = os.path.abspath(os.path.join(os.path.dirname(__file__), *[".."] * 5))
RTL = os.path.join(ROOT, "cells", "rtl")
def modules(text):
    out = {}
    for m in re.finditer(r"\bmodule\s+(\w+)(.*?)\bendmodule\b", text, re.S):
        out[m.group(1)] = m.group(2)
    return out
lib = {}
for f in sorted(os.listdir(RTL)):
    if f.endswith(".v"):
        lib.update(modules(re.sub(r"//[^\n]*", "", open(os.path.join(RTL, f)).read())))
INST = re.compile(r"^\s*(?:\(\*[^*]*\*\)\s*)?(\w+)\s*(?:#\s*\((?:[^()]|\([^()]*\))*\))?\s+(\w+)\s*\(", re.M)
LUT = re.compile(r"(LUT[1-6](?:_2)?)\s*#\s*\(\s*\.INIT\(\s*(\d+)'h([0-9A-Fa-f_]+)\s*\)\s*\)\s*(\w+)\s*\((.*?)\)\s*;", re.S)
def luts(body):
    res = []
    for m in LUT.finditer(body):
        kind, init, name, conns = m.group(1), int(m.group(3).replace("_", ""), 16), m.group(4), m.group(5)
        pins = dict(re.findall(r"\.I(\d)\(\s*([^()]*?)\s*\)", conns))
        res.append((kind, init, name, {int(k): v for k, v in pins.items()}))
    return res
def rst_value(init, pins):
    rp = [k for k, v in pins.items() if v == "rst"]
    if not rp: return None
    r = rp[0]; vals = set()
    others = [k for k in pins if k != r and not re.fullmatch(r"1'b[01]", pins[k])]
    for bits in itertools.product([0, 1], repeat=len(others)):
        idx = 1 << r
        for k, b in zip(others, bits): idx |= b << k
        for k, v in pins.items():
            if v == "1'b1": idx |= 1 << k
        vals.add((init >> idx) & 1)
    return vals
def walk(text):
    seen, todo, used = set(), [], {}
    top = modules(re.sub(r"//[^\n]*", "", text))
    bodies = dict(top)
    for b in top.values():
        for m in INST.finditer(b):
            todo.append(m.group(1))
    while todo:
        mname = todo.pop()
        used[mname] = used.get(mname, 0) + 1
        if mname in seen or mname not in lib: continue
        seen.add(mname); bodies[mname] = lib[mname]
        for m in INST.finditer(lib[mname]): todo.append(m.group(1))
    return bodies, used
for path in sys.argv[1:]:
    bodies, used = walk(open(path).read())
    sets = sorted(m for m in used if m.endswith("_set"))
    print(f"== {os.path.basename(path)}: {len(bodies)} module bodies; *_set cells reachable: {sets or 'none'}")
    seen_init = {}
    for mod, body in sorted(bodies.items()):
        for kind, init, name, pins in luts(body):
            v = rst_value(init, pins)
            if v is None: continue
            seen_init.setdefault((mod, name, hex(init)), v)
    for (mod, name, init), v in sorted(seen_init.items()):
        flag = "" if v == {0} else "   <-- NOT cleared"
        print(f"   {mod:22s} {name:10s} INIT {init:20s} reset value {sorted(v)}{flag}")
    links = used.get("bd_link", 0) + used.get("bd_pipe", 0)
    print(f"   instances: bd_link {used.get('bd_link',0)}, bd_pipe {used.get('bd_pipe',0)}, bd_link_ctl {used.get('bd_link_ctl',0)}, bd_c2n {used.get('bd_c2n',0)}, bd_c2n_set {used.get('bd_c2n_set',0)}, bd_c2_set {used.get('bd_c2_set',0)}")
