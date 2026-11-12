#!/usr/bin/env python3
"""Stand-in for `/usr/bin/time -v` (not installed here): run a command, print wall
time and the peak RSS of the largest waited-for descendant (ru_maxrss of
RUSAGE_CHILDREN, which covers the lean grandchild of slot.sh/lake)."""
import resource, subprocess, sys, time
t0 = time.time()
rc = subprocess.call(sys.argv[1:])
ru = resource.getrusage(resource.RUSAGE_CHILDREN)
print(f"[memtime] wall {time.time()-t0:.1f} s, user {ru.ru_utime:.1f} s, "
      f"max RSS {ru.ru_maxrss/1024:.0f} MB, rc {rc}", file=sys.stderr)
sys.exit(rc)
