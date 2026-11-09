import sys, pickle, collections, itertools
sys.path.insert(0,'.')
from classify import load, lut
from bisect import bisect_right
C=load(); g=C['gates']; nm=C['names']; idn={n:i for i,n in enumerate(nm)}; rd=C['rd']
H=pickle.load(open('hist_c0.pkl','rb'))['hist']
def flips(n,a=40000,b=10**9): return [t for t in H.get(n,(0,[]))[1] if a<=t<=b]
def val(n,t):
    if n not in H: return False
    b,ts=H[n]; return b ^ (bisect_right(ts,t)%2==1)
z=idn['SLICE_X11Y31.B6']; src=idn['SLICE_X15Y19.B6']
# backward cone of z (data only)
cone=set(); todo=[z]
while todo:
    u=todo.pop()
    if u in cone: continue
    cone.add(u)
    if u in C['LATCH'] or u not in g: pass
    if u in g and u not in C['EXACT']:
        for p in C['live'][u]:
            if p['src'] not in cone and p['src'] not in C['EXACT'] and p['src'] not in C['const']: todo.append(p['src'])
# forward from src through data nodes, BFS paths, restricted to backward cone of z (through latches too)
full=set(); todo=[z]
while todo:
    u=todo.pop()
    if u in full: continue
    full.add(u)
    if u in g and u not in C['EXACT']:
        for p in C['live'][u]:
            s=p['src']
            if s not in C['EXACT'] and s not in C['const']: todo.append(s)
print('15Y19.B6 in full data cone of z (through latches):', src in full)
prev={src:None}; q=collections.deque([src])
while q:
    u=q.popleft()
    if u==z: break
    for v in rd[u]:
        if v in full and v not in prev and v not in C['EXACT']: prev[v]=u; q.append(v)
path=[]; u=z
while u is not None: path.append(u); u=prev.get(u)
path=path[::-1]
print('path', [nm[x] for x in path])
for x in path:
    G=g[x]; kind='LATCH' if x in C['LATCH'] else 'comb'
    pins=[(nm[p['src']], 'X' if p['src'] in C['EXACT'] else ('c' if p['src'] in C['const'] else 'D')) for p in G['pins'] if p['live']]
    extra=''
    if x in C['LATCH']:
        fb,en=C['LATCH'][x]; extra=' enable %s'%[(nm[G['pins'][p]['src']],v) for p,v in en if G['pins'][p]['src'] in C['EXACT']]
    print(' %-16s %s%s pins %s flips %s'%(nm[x], kind, extra, pins, flips(x)[:8]))
