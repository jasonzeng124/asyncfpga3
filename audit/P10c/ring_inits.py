#!/usr/bin/env python3
"""P10c item 6: own extraction of the ring-cell INITs from cells/rtl and a reset-clear check.
Run: python3 -I ring_inits.py <cells/rtl dir>"""
import re, sys, os, itertools
rtl = sys.argv[1]
src = ""
for f in sorted(os.listdir(rtl)):
    if f.endswith(".v"):
        s = open(os.path.join(rtl, f)).read()
        s = re.sub(r'//[^\n]*', '', s)
        src += f"\n//FILE {f}\n" + s
# every LUT instance: module, INIT, pins
mods = re.split(r'\bmodule\s+', src)
rows = []
for m in mods[1:]:
    name = re.match(r'(\w+)', m).group(1)
    body = m.split('endmodule')[0]
    for lm in re.finditer(r'LUT(\d)(_2)?\s*#\s*\(\s*\.INIT\(\s*(\d+)\'h([0-9A-Fa-f_]+)\s*\)\s*\)\s*(\w+)\s*\((.*?)\);', body, re.S):
        init = int(lm.group(4).replace('_', ''), 16)
        pins = {}
        for pm in re.finditer(r'\.(I\d|O\d?)\s*\(\s*([^)]*?)\s*\)', lm.group(6)):
            pins[pm.group(1)] = pm.group(2)
        rows.append((name, lm.group(5), int(lm.group(1)), init, pins))
def ev(init, bits):  # bits: list I0..I5
    idx = sum(b << i for i, b in enumerate(bits))
    return (init >> idx) & 1
for (mod, inst, k, init, pins) in rows:
    rstpins = [int(p[1]) for p, n in pins.items() if p.startswith('I') and n.strip() in ('rst', 'arb_rst', 'ring_rst')]
    if not rstpins:
        continue
    r = rstpins[0]
    outs = []
    # constant pins
    const = {int(p[1]): int(n[-1]) for p, n in pins.items() if p.startswith('I') and re.fullmatch(r"1'b[01]", n.strip())}
    free = [i for i in range(6) if i != r and i not in const and f"I{i}" in pins]
    vals = set()
    for combo in itertools.product([0, 1], repeat=len(free)):
        bits = [0]*6
        for i, c in const.items(): bits[i] = c
        for i, b in zip(free, combo): bits[i] = b
        bits[r] = 1
        vals.add(ev(init, bits))
    print(f"{mod:14s} {inst:8s} LUT{k} INIT=0x{init:016X} rst=I{r} out_under_rst={sorted(vals)}")
