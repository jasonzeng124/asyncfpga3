#!/usr/bin/env python3
"""multidecl_patch.py TOOLSCOPY -- runtime patch to a COPY of cfront.py: read a multi-declarator
declaration `T a = e1, b = e2;` as the block `T a = e1; T b = e2;` (C: each declarator's
initializer is sequenced before the next; quadrec)."""
import sys, os
c = os.path.join(sys.argv[1], 'autoproof', 'cfront.py'); s = open(c).read()
old = '''            if self.at("="):
                self.eat("=")
                e = self.expr()
            return ("decl", ty, nm, e)
'''
new = '''            if self.at("="):
                self.eat("=")
                e = self.expr()
            ds = [("decl", ty, nm, e)]
            while self.at(","):
                self.eat(",")
                nm = self.eat(kind="id")[1]
                e = None
                if self.at("="):
                    self.eat("=")
                    e = self.expr()
                ds.append(("decl", ty, nm, e))
            return ds[0] if len(ds) == 1 else ("blk", ds)
'''
assert s.count(old) == 1
open(c, 'w').write(s.replace(old, new))
