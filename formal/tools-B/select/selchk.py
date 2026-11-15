import json,lzma,re,collections,sys
S=sys.argv[1]
N=json.load(open(S+'/net.json'));g=N['gates'];NG=len(g)
J=json.load(lzma.open('/home/user/asyncfpga3/formal/target/gcd_ps_e6bb4aec.routed.json.xz'))
bel={c['attributes'].get('NEXTPNR_BEL'):cn for cn,c in J['modules']['top']['cells'].items()};del J
def src(n):
    while n<NG and g[n]['k']==1 and g[n]['init']==2: n=g[n]['ins'][0]
    return n
def cell(i):
    m=re.match(r"(SLICE_X\d+Y\d+)\.([A-D])LUT\.O([56])",g[i]['name'])
    return bel.get("%s/%s%sLUT"%m.groups(),'?') if m else '?'
cn={i:cell(i) for i in range(NG) if g[i]['k']>=2}
O=json.load(open(S+'/uncovered_mux.json'))
res=collections.Counter()
for o in O:
    mc=o['mux_cell']; m=re.match(r'(bridge_i\.udut\.umux\d+)\.',mc)
    if not m: continue
    inst=m.group(1); sel=o['select']['src']
    js=[i for i,c in cn.items() if c.startswith(inst+'.uj')]
    res[(len(js), all(sel in {src(n) for n in g[i]['ins']} for i in js))]+=1
print(res)
