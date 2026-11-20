#!/usr/bin/env python3
"""cfront_define_patch.py TOOLSCOPY -- runtime patch to a COPY of cfront.py, CF_DEFINE=1: an object-like
`#define NAME LITERAL` (one decimal/hex integer literal, optional u/U suffix, nothing else on the line) in the
kernel's source replaces each later identifier token NAME by that literal token (what the preprocessor does for
this form). Any other #define is still dropped with the other # lines; an identifier it defined stays an
undeclared variable (refused). (lfsrfind: #define LIMIT 256.)"""
import sys, os
c = os.path.join(sys.argv[1], 'autoproof', 'cfront.py'); s = open(c).read()
def rep(old, new):
    global s
    assert s.count(old) == 1, old
    s = s.replace(old, new)
rep('''def lex(src):
    src = re.sub(r"^[ \\t]*#.*$", "", src, flags=re.M)   # keep the newlines: line numbers
''', '''def lex(src):
    defs = dict(re.findall(r"^[ \\t]*#[ \\t]*define[ \\t]+([A-Za-z_]\\w*)[ \\t]+(0[xX][0-9a-fA-F]+[uU]?|\\d+[uU]?)[ \\t]*$",
                           src, flags=re.M))
    src = re.sub(r"^[ \\t]*#.*$", "", src, flags=re.M)   # keep the newlines: line numbers
''')
rep('''        elif m.group(3):
            out.append(("id", m.group(3), line))
''', '''        elif m.group(3) and m.group(3) in defs:
            out.append(("num", defs[m.group(3)], line))
        elif m.group(3):
            out.append(("id", m.group(3), line))
''')
open(c, 'w').write(s)
