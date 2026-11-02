#!/usr/bin/env python3
"""sitet_cmp.py (audit T11): the round trip's site-prefix table (RT/Top.lean `siteT` leaves: SLICE site -> FASM
prefix TILE.SLICEx_Xn) vs the auditor's own prjxray tilegrid lookup (audit/t4/xnode.py slice_prefix).
    python3 -I sitet_cmp.py TOP.lean"""
import re, sys, os
sys.path.insert(0, os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "t4"))
from xnode import XDB
s = open(sys.argv[1]).read(); s = s[s.index("def siteT"):]
s = s[:s.index("\ndef ", 5)] if "\ndef " in s[5:] else s
pairs = re.findall(r'\.leaf "(SLICE_X\d+Y\d+)" "([^"]+)"', s)
X = XDB(); bad = []
for site, pre in pairs:
    t, sx, _ = X.slice_prefix(site)
    if "%s.%s" % (t, sx) != pre:
        bad.append((site, pre, "%s.%s" % (t, sx)))
print("siteT entries", len(pairs), "distinct sites", len({a for a, _ in pairs}), "distinct prefixes", len({b for _, b in pairs}),
      "mismatches vs own prjxray lookup", len(bad), bad[:5])
