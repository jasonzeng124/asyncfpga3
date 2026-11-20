#!/usr/bin/env python3
"""cfront_consttest_patch.py TOOLSCOPY -- runtime patch to a COPY of cfront.py, CF_CONSTTEST=1: during the
symbolic straight-line run between test points, a test whose condition (over the symbolic state there) has no
variable is evaluated and its branch followed, instead of stopping there (exact: the outcome is the same on
every input). E.g. lfsrfind's `for (i = 0; i < LIMIT; i++)` at entry: `0 < 256` is always true, so the C
automaton starts at the `x == k` test, as the graph (whose front end rotated the loop) does. A cycle of folded
tests is refused like any straight-line cycle."""
import sys, os
c = os.path.join(sys.argv[1], 'autoproof', 'cfront.py'); s = open(c).read()
old = '''        n = cfg.nodes[node]
        if n[0] == "test":
            return ("test", node, env)
'''
new = '''        n = cfg.nodes[node]
        if n[0] == "test" and os.environ.get("CF_CONSTTEST") == "1":
            cc = subst(env, L.cond(n[1]))
            if not _hasvar(cc):
                if node in seen:
                    raise SyntaxError("cfront: a cycle of constant tests")
                seen.add(node)
                node = n[2] if ev(cc, []) % 2 == 1 else n[3]
                continue
        if n[0] == "test":
            return ("test", node, env)
'''
assert s.count(old) == 1
s = s.replace(old, new)
old = "def sym_straight(cfg, node, env, seen=None):\n"
assert s.count(old) == 1
s = s.replace(old, '''def _hasvar(e):
    if e[0] == "var":
        return True
    return e[0] != "lit" and any(_hasvar(x) for x in e[1:] if isinstance(x, tuple) and x and
                                 x[0] in ("var", "lit", "un", "bin", "sel"))


''' + old)
open(c, 'w').write(s)
