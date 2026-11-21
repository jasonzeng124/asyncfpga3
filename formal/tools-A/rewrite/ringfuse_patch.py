#!/usr/bin/env python3
"""ringfuse_patch.py TOOLSCOPY -- the two run-time patches ringfuse_autoproof.sh applies to a COPY of formal/tools."""
import os, sys
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import fuse_check as F  # noqa: E402
T = sys.argv[1]
m = os.path.join(T, 'dfimport', 'mlir2lean.py'); t = open(m).read()
assert t.count(F.MR_OLD) == 1, 'dfimport changed'
t = t.replace(F.MR_OLD, F.MR_NEW)
old = '        return self.em.ch[v][1]\n'
assert t.count(old) == 1
open(m, 'w').write(t.replace(old, '        return self.em.ch[v][1] if v in self.em.ch else False\n'))
a = os.path.join(T, 'autoproof', 'autoproof.py'); s = open(a).read()
old = 'env = {x: y for x, y in os.environ.items() if not x.startswith("BDC_")}'
assert s.count(old) == 2, 'autoproof changed'
open(a, 'w').write(s.replace(old, 'env = dict(os.environ)'))
