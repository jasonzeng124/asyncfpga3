#!/usr/bin/env python3
# arb_holdreach.py ROUTED_JSON XRAY_SDF -- research/data/fid/arbtie.md "Hold release" (S12).
# Naive shortest paths (a lower bound on the re-request path, so a positive slack is robust).
# hold-release reachability on a routed design (FAST_MIN): the holder's re-request reaches
# ustate within TLOOP of q's release edge iff
#   d(A0->ua_h pin)+arc + [A_h -> ... -> r_h at ustate pin] (shortest) + arc  <  d(A0->ustate pin)+arc + TLOOP
import sys,json,re,heapq,collections
J,S=sys.argv[1:3]; col=0
cells=json.load(open(J))['modules']['top']['cells']
adj=collections.defaultdict(list); arc={}; wire={}; inst=None
RI=re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)"); RN=re.compile(r"\(INSTANCE\s+(\S*?)\)"); RO=re.compile(r"\(IOPATH\s+(\S+)\s+(\S+)\s+\((\d+):(\d+):(\d+)\)")
u=lambda s:s.replace('\\','')
for l in open(S):
    m=RI.search(l)
    if m:
        s,d=u(m.group(1)),u(m.group(2))
        if s.startswith('$PACKER'): continue
        w=int(m.group(3+col)); adj[s].append((d,w)); wire[(s,d)]=w; continue
    m=RN.search(l)
    if m: inst=u(m.group(1)); continue
    m=RO.search(l)
    if m and inst:
        w=int(m.group(3+col)); arc[(inst,m.group(1),m.group(2))]=w; adj[inst+'/'+m.group(1)].append((inst+'/'+m.group(2),w))
def pin(c,lg):
    for k,v in cells[c]['attributes'].items():
        if k.startswith('X_ORIG_PORT_A') and lg in v.split(): return k[12:]
def dj(src,tgt,avoid):
    dist={src:0};pq=[(0,src)]
    while pq:
        d,x=heapq.heappop(pq)
        if x==tgt: return d
        if d>dist[x]: continue
        for y,w in adj.get(x,()):
            if y.startswith(avoid) and y != tgt: continue
            if d+w<dist.get(y,1e18): dist[y]=d+w; heapq.heappush(pq,(d+w,y))
for st6 in sorted(c for c in cells if c.endswith('.ustate$LUT6')):
    p=st6[:-12]; a0p=pin(st6,'I4'); a0net=cells[st6]['connections'][a0p][0]
    src=[s for (s,d) in wire if d==st6+'/'+a0p][0]
    fb=[d for (s,d) in wire if s==st6+'/O6' and d.startswith(st6+'/')][0].split('/')[-1]
    TL=wire[(st6+'/O6',st6+'/'+fb)]+arc.get((st6,fb,'O6'),124)
    rel=wire[(src,st6+'/'+a0p)]+arc.get((st6,a0p,'O6'),0)
    out=[]
    for k,lg in ((1,'I0'),(2,'I1')):
        ua=p+'.ua%d.u'%k
        ap=[q for q,b in cells[ua]['connections'].items() if b==[a0net] and q.startswith('A')][0]
        rp=pin(st6,lg)
        t=wire[(src,ua+'/'+ap)]+arc.get((ua,ap,'O6'),0)
        back=dj(ua+'/O6',st6+'/'+rp,p+'.ustate')
        rr=t+back+arc.get((st6,rp,'O6'),0)
        out.append('h%d: re-request at q %5.0f vs window end %5.0f (slack %5.0f)'%(k,rr,rel+TL,rr-(rel+TL)))
    print('%-28s TLOOP %4d  '%(p.replace('urig.udut.',''),TL)+'  '.join(out))
