#!/usr/bin/env python3
"""T125 (audit, own code): copy an own route dir and add DELTA ps to every (a:b:c) triple of the INTERCONNECT arcs whose
source matches SRC_RX and destination matches DST_RX, in every *.sdf of the copy. usage: inject.py SRC_DIR DST_DIR SRC_RX DST_RX DELTA"""
import sys, os, re, shutil
src, dst, srx, drx, delta = sys.argv[1], sys.argv[2], re.compile(sys.argv[3]), re.compile(sys.argv[4]), int(sys.argv[5])
if os.path.exists(dst): shutil.rmtree(dst)
shutil.copytree(src, dst)
add = lambda mm: '(' + ':'.join(str(int(x) + delta) for x in mm[1].split(':')) + ')'
for f in sorted(os.listdir(dst)):
    if not f.endswith('.sdf'): continue
    p = os.path.join(dst, f); out = []; n = 0
    for l in open(p):
        mm = re.match(r'(\s*\(INTERCONNECT )(\S+) (\S+) (.*)$', l)
        if mm and srx.search(mm[2]) and drx.search(mm[3]):
            l = mm[1] + mm[2] + ' ' + mm[3] + ' ' + re.sub(r'\(([\d.]+:[\d.]+:[\d.]+)\)', add, mm[4]) + '\n'; n += 1
            print(f, l.strip())
        out.append(l)
    open(p, 'w').writelines(out); print(f, 'arcs', n)
