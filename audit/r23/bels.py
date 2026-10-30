# GLS_SCALE_INST value (site/BEL names, as the fid SDF uses) for a cell's matched-delay chain
import json,sys
j=json.load(open(sys.argv[1])); m=next(iter(j['modules'].values())); pre=sys.argv[2]; f=sys.argv[3]
b=sorted(c['attributes']['NEXTPNR_BEL'] for n,c in m['cells'].items() if n.startswith(pre))
sys.stderr.write("%d cells\n"%len(b)); print(",".join("%s:%s"%(x,f) for x in b))
