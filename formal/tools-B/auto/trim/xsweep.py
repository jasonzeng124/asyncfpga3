import json, subprocess, sys
d=sys.argv[1]; K=sys.argv[2]; M=d+'/w/m'
N=json.load(open(M+'/net.json')); G=N['gates']; names=N['nodes']; drv={g['out']:gi for gi,g in enumerate(G)}
C=json.load(open(sys.argv[3]))
pairs=open(d+'/pairs.txt').read().split()
W=','.join(str(int(l.split()[0],16)) for l in open(d+'/exp.txt') if l.strip() and not l.startswith('//'))
GCL={}
for l in open(M+'/gclass.txt'): gi,c=l.split(); GCL[int(gi)]=c
def arcs(cls):
    out=[]
    for e in C[cls]:
        nm,pins=(e[0],[e[1]]) if isinstance(e,list) else (e,None)
        u=names.index(nm); gi=drv[u]; g=G[gi]
        for p in (pins if pins is not None else range(len(g['ins']))): out.append((nm,p,gi,g['arcs'][p]))
    return out
S,F=arcs('S'),arcs('F')
def run(bc,br,x):
    I=[]
    for sign,lst in ((1,S),(-1,F)):
        for nm,p,gi,a in lst:
            c=GCL.get(gi,'r'); b=bc if c in ('c','q') else br
            base=a['fmin']+b*(a['smax']-a['fmin']); I.append([nm,p,int(round(sign*x*base))])
    json.dump({"S":[],"F":[],"I":I},open(d+'/inj.json','w'))
    r=subprocess.run([M+'/simx',M+'/net.simx','--periodic','--maxev','300000000','--kernel',K,'--want',W,'--pairs',*pairs,
        '--corner','0','--data0','--full','--R','400000','--su','1000','--datachange','broad','--nextreq','seq','--tmax','400000000',
        '--hostdelay','12000','--draw','1','--gclass',M+'/gclass.txt','--bands','%g,%g,1.0'%(bc,br),'--sreg','0','--sarc','0','--w','20',
        '--classes',d+'/inj.json'],capture_output=True,text=True)
    o=r.stdout+r.stderr
    res=next((l.split(':')[0] for l in o.splitlines() if l.startswith('RESULT')),'MAXEV' if 'MAXEV' in o else 'NONE')
    pul=next((l.split(':')[1].split(';')[0].strip() for l in o.splitlines() if l.startswith('NEARMISS')),'?')
    return res,pul
for bc,br in ((0.20,0.20),(0.20,0.31),(0.31,0.31)):
    for x in (0.0,0.04,0.06,0.08,0.10,0.12,0.15,0.20,0.25):
        res,pul=run(bc,br,x); print('bands chains %.2f rest %.2f  x=%.2f: %s pulses %s'%(bc,br,x,res,pul),flush=True)
        if 'OK' not in res: break
