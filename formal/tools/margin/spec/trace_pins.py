#!/usr/bin/env python3
# trace_pins.py DIR/m/ LUTNODE x  (shard C, 2026-11-22; untrusted): for each input pin of a decoded LUT gate, walk back through
# single-input routing gates (pips, wires, site hops) to the driving LUT / FF / constant; prints its instance name (nextpnr BEL
# map) and the routing delay summed over the walk (prjxray fast-max / slow-max ps).
import json,re,sys
B,lut,tile=sys.argv[1],sys.argv[2],sys.argv[3]   # e.g. SLICE_X24Y43.A6  CLBLM_R_X17Y43/CLBLM_M_A
N=json.load(open(B+'net.json')); R=json.load(open(B+'routed.json'))
BEL={c["attributes"].get("NEXTPNR_BEL"):n for n,c in R["modules"]["top"]["cells"].items() if c.get("attributes",{}).get("NEXTPNR_BEL")}
nodes=N['nodes']; drv={g['out']:g for g in N['gates']}; idx={n:i for i,n in enumerate(nodes)}
def name(n):
    m=re.match(r"^(SLICE_X\d+Y\d+)\.([A-D])([56])$",n)
    return BEL.get("%s/%s%sLUT"%m.groups(), n) if m else n
g=drv[idx[lut]]
for pin,n in enumerate(g['ins']):
    hops=0; d=[0,0]
    while n in drv and drv[n]['kind'] not in ('lut6','lut5','lut','ff','carry4','muxf7','muxf8','latch') and len(drv[n]['ins'])==1:
        a=drv[n].get('arcs',[{}])[0]; d[0]+=a.get('fmax',0); d[1]+=a.get('smax',0); n=drv[n]['ins'][0]; hops+=1
    print("pin",pin,"<-",nodes[n],name(nodes[n]),drv[n]['kind'] if n in drv else 'const/none',"hops",hops,"routing fast/slow max",d)
