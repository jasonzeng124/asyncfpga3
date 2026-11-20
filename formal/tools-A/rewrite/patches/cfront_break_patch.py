#!/usr/bin/env python3
"""cfront_break_patch.py TOOLSCOPY -- runtime patch to a COPY of cfront.py, CF_BREAK=1: `break;` leaves the
innermost enclosing loop (while / do / for), i.e. control goes to the statement after that loop (C11 6.8.6.3).
An `if` containing a `break` is a test point (has_ctl). `break` outside a loop is refused; `continue` stays
refused. (lfsrfind: `if (x == k) break;` inside a for.)"""
import sys, os
c = os.path.join(sys.argv[1], 'autoproof', 'cfront.py'); s = open(c).read()
def rep(old, new):
    global s
    assert s.count(old) == 1, old
    s = s.replace(old, new)
rep('''        if tk[0] == "id" and tk[1] in ("break", "continue", "goto", "switch"):''',
    '''        if tk[0] == "id" and tk[1] == "break":
            self.eat()
            self.eat(";")
            return ("brk", tk[2])
        if tk[0] == "id" and tk[1] in ("break", "continue", "goto", "switch"):''')
rep('''    if k in ("while", "do", "for", "ret"):''', '''    if k in ("while", "do", "for", "ret", "brk"):''')
rep('''        self.low = low
        self.nodes = []
''', '''        self.low = low
        self.nodes = []
        self.brk = []   # break targets of the enclosing loops (innermost last)
''')
rep('''        if k == "ret":
            return self.new(("ret", s[1], s[2]))
''', '''        if k == "ret":
            return self.new(("ret", s[1], s[2]))
        if k == "brk":
            if not self.brk:
                raise SyntaxError(f"cfront: line {s[1]}: `break` outside a loop")
            return self.brk[-1]
''')
rep('''            tn = self.new(("test", s[1], None, nxt, s[3]))
            body = self.build(s[2], tn)
''', '''            tn = self.new(("test", s[1], None, nxt, s[3]))
            self.brk.append(nxt)
            body = self.build(s[2], tn)
            self.brk.pop()
''')
rep('''            tn = self.new(("test", s[2], None, nxt, s[3]))
            body = self.build(s[1], tn)
''', '''            tn = self.new(("test", s[2], None, nxt, s[3]))
            self.brk.append(nxt)
            body = self.build(s[1], tn)
            self.brk.pop()
''')
rep('''            step = self.build(s[3], tn) if s[3] is not None else tn
            body = self.build(s[4], step)
''', '''            step = self.build(s[3], tn) if s[3] is not None else tn
            self.brk.append(nxt)
            body = self.build(s[4], step)
            self.brk.pop()
''')
open(c, 'w').write(s)
