#!/usr/bin/env python3
"""cfront_strlit_patch.py TOOLSCOPY -- runtime patch to a COPY of cfront.py, CF_STRLIT=1 (apply after the CF_W64
patch if that is set): the lexer accepts a C string literal ("...", backslash escapes, one line) as ONE operator
token whose text is the literal. No rule of the parser accepts such a token, so a string literal inside the kernel
function is still refused ("expected ..."); outside it (main's assert message: factorial) it is skipped like every
other token before the function."""
import sys, os
c = os.path.join(sys.argv[1], 'autoproof', 'cfront.py'); s = open(c).read()
old = '[-+*/%&|^~!<>=?:;,(){}]))"'
n = s.count(old)
assert n in (1, 2), n
s = s.replace(old, r'[-+*/%&|^~!<>=?:;,(){}]|\x22(?:[^\x22\\\n]|\\.)*\x22))"')
open(c, 'w').write(s)
