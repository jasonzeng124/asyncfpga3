#!/usr/bin/env python3
"""pend.py VCD [T]: final value (at T or end) of every X_req / X_ack pair at the dumped scope; lists pairs with
req != ack (a token offered and not taken: req=1 ack=0; a return to zero not finished: req=0 ack=1), with the time of
each net's last change."""
import sys, re, collections
path = sys.argv[1]; T = int(sys.argv[2]) if len(sys.argv) > 2 else None
ids = {}; last = {}; lastt = {}; t = 0
for ln in open(path):
    if ln.startswith("$var"):
        p = ln.split(); ids[p[3]] = p[4]; continue
    if not ln or ln[0] in "$ \n": continue
    if ln[0] == "#":
        t = int(ln[1:])
        if T is not None and t > T: break
        continue
    if ln[0] in "01xz":
        i = ln[1:].strip()
        if i in ids: last[ids[i]] = ln[0]; lastt[ids[i]] = t
    elif ln[0] == "b":
        v, i = ln[1:].split()
        if i in ids: last[ids[i]] = v; lastt[ids[i]] = t
for n in sorted(last):
    if n.endswith("_req"):
        b = n[:-4]; a = b + "_ack"
        if a in last and last[n] != last[a]:
            print(f"{b:34s} req={last[n]} ack={last[a]}  req@{lastt[n]} ack@{lastt[a]}")
