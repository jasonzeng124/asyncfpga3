"""run_mono.py -- P_mono (hazard-freedom) for bd_c2 at W = W_min and W_min+3, every channel kind -> results/celem_mono.txt"""
import os, sys; sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import celem,tsmc,time
D=[((1,1),(1,1)),((1,2),(1,2)),((2,3),(1,3)),((1,3),(2,2)),((2,2),(3,3))]
out=open(os.path.join(os.path.dirname(os.path.abspath(__file__)), 'results', 'celem_mono.txt'),'w')
for kind in ('win','fifo','inert'):
  for dl,dw in D:
    Dmax=dl[1]+dw[1]
    W = Dmax if kind!='inert' else Dmax-dl[0]+1
    for w in (W, Dmax+3):
      ts,P=celem.build(kind,dl,dw,W=w); t=time.time()
      r=tsmc.prove(ts,P['mono'],kmax=25,spacer_tmo=30)
      s='%-5s dl=%s dw=%s W=%d mono: %s [%.1fs]'%(kind,dl,dw,w,tsmc.verdict(r),time.time()-t)
      print(s,flush=True); out.write(s+'\n'); out.flush()
