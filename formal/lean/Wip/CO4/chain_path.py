# shortest run (per-gate SI, end-only persistence) to the hazard, bd_delay N=3 FASTFALL
import itertools
from collections import deque
n=3
G=[lambda s:s[0], lambda s:s[1] and s[0], lambda s:s[2] and s[0]]
init=(False,)*4; prev={init:None}; q=deque([init]); bad=None
while q:
    s=q.popleft()
    exc=[k for k in range(1,n+1) if G[k-1](s)!=s[k]]
    x0o=[s[0], not s[0]] if s[n]==s[0] else [s[0]]
    for r in range(len(exc)+1):
        for sub in itertools.combinations(exc,r):
            for x0 in x0o:
                t=list(s); t[0]=x0
                for k in sub: t[k]=not s[k]
                t=tuple(t)
                if t[n]!=s[n] and t[n]!=s[0] and bad is None: bad=(s,t)
                if t not in prev: prev[t]=s; q.append(t)
s,t=bad; path=[t,s]
while prev[path[-1]] is not None: path.append(prev[path[-1]])
path.reverse()
for i,p in enumerate(path): print(i, [int(v) for v in p])
