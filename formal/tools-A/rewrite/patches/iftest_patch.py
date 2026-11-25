#!/usr/bin/env python3
"""iftest_patch.py TOOLSCOPY -- runtime patch to a COPY of cfront.py: with CF_IFTEST=1, every C `if`
is a test point (cfront otherwise if-converts an `if` whose arms are only assignments into `sel`
expressions). Both transcriptions are exact; this one cuts the C where the graph branches (brhash:
the graph tests `h & 1` and the loop exit in separate segments)."""
import sys, os
c = os.path.join(sys.argv[1], 'autoproof', 'cfront.py'); s = open(c).read()
old = '    if k == "if":\n        return has_ctl(s[2]) or (s[3] is not None and has_ctl(s[3]))\n'
assert s.count(old) == 1
s = s.replace(old, '    if k == "if":\n        return os.environ.get("CF_IFTEST") == "1" or has_ctl(s[2]) or (s[3] is not None and has_ctl(s[3]))\n')
open(c, 'w').write(s)
