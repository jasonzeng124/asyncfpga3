import os,re,sys
sys.argv=[sys.argv[0],'0']
exec(open('Wip/C8r/walkcheck.py').read().split('if __name__')[0])
sp=sorted(spine)
for g in sp:
    cons=[(i,r) for i,r in enumerate(rules) if g in mlir2lean.Graph.rule_ins(r)]
    prods=[(i,r) for i,r in enumerate(rules) if r[0]!='mux' and ((r[0]=='comp' and r[2]==g) or (r[0]=='fork' and g in r[2]) or (r[0]=='branch' and g in r[3:5]) or (r[0]=='cm' and g in r[2:4]))]
    print(g, 'cons', cons, 'prods', [i for i,_ in prods])
