# uori3 chain vs datapath placement from the routed JSON (NEXTPNR_BEL), own extraction
import json,re,sys,collections
j=json.load(open(sys.argv[1])); m=next(iter(j['modules'].values()))
ch=[];dp=[]
for n,c in m['cells'].items():
    if not n.startswith('urig.udut.uori3.'): continue
    b=c['attributes'].get('NEXTPNR_BEL','')
    s=re.match(r'SLICE_X(\d+)Y(\d+)',b)
    if not s: continue
    xy=(int(s[1]),int(s[2]))
    (ch if '.udly.' in n else dp).append((xy,n,c['type']))
def rng(L): xs=[p[0][0] for p in L]; ys=[p[0][1] for p in L]; return "X%d-%d Y%d-%d n=%d"%(min(xs),max(xs),min(ys),max(ys),len(L))
print("chain",rng(ch)); print("datapath",rng(dp))
print("datapath regions",collections.Counter((p[0][0]//10,p[0][1]//10) for p in dp))
print("chain regions",collections.Counter((p[0][0]//10,p[0][1]//10) for p in ch))
cx=lambda L:(sum(p[0][0] for p in L)/len(L),sum(p[0][1] for p in L)/len(L))
a,b=cx(ch),cx(dp); print("centroids",a,b,"dist %.1f"%(((a[0]-b[0])**2+(a[1]-b[1])**2)**.5))
