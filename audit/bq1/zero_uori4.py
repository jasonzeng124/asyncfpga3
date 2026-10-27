#!/usr/bin/env python3
# Negative control: copy an SDF with uori4's matched delay (bd_delay_gated udly
# chain) collapsed to ~0: every IOPATH of a cell under urig.udut.uori4.udly.
# and every INTERCONNECT along the chain (source uori4.uor or a chain cell,
# destination a chain cell) set to 0.  Gate (join->chain) wires are untouched.
import re, sys
src, dst = sys.argv[1], sys.argv[2]
P = r"urig\.udut\.uori4\."
ric = re.compile(r"\(INTERCONNECT (\S+) (\S+) \(")
rinst = re.compile(r"\(INSTANCE (\S*)\)")
rio = re.compile(r"\(IOPATH ")
inst = None; nio = nic = 0; out = []
Z = lambda l: re.sub(r"\(\d+:\d+:\d+\)", "(0:0:0)", l)
for l in open(src):
    m = ric.search(l)
    if m:
        s, d = m.group(1), m.group(2)
        if re.match(P + r"(udly\.|uor/)", s) and re.match(P + r"udly\.", d):
            l = Z(l); nic += 1
        out.append(l); continue
    m = rinst.search(l)
    if m: inst = m.group(1)
    elif rio.search(l) and inst and re.match(P + r"udly\.", inst):
        l = Z(l); nio += 1
    out.append(l)
open(dst, "w").write("".join(out))
print(f"zeroed {nic} INTERCONNECT and {nio} IOPATH entries")
