import sys, os, re
sys.argv=[sys.argv[0]]
HERE='/home/user/asyncfpga3/formal/lean/Wip/C8x2'
exec(open(os.path.join(HERE,'classify.py')).read().split("# rank:")[0].replace("HERE = os.path.dirname(os.path.abspath(__file__))","HERE='%s'"%HERE))
am=[c for c in range(NC) if P[prod[c]][0]=='amerge']
print('amerge outputs', am, [P[prod[c]][1] for c in am])
ST2 = STRUCT|{'amerge'}
# find cycles: dfs
def ranks(struct_chans):
    rank={}; state={}
    def rk(c):
        if c in rank: return rank[c]
        if state.get(c)==1: raise RuntimeError(c)
        state[c]=1
        k,ins,_=P[prod[c]]
        r = 1+max([rk(i) for i in ins],default=-1) if c in struct_chans else 0
        rank[c]=r; state[c]=2; return r
    for c in range(NC): rk(c)
    return rank
base=set(c for c in range(NC) if P[prod[c]][0] in STRUCT)
good=[]
for c in am:
    try: ranks(base|{c}); good.append(c); print(c,'ok alone')
    except RuntimeError as e: print(c,'cycle',e)
try:
    r=ranks(base|set(good)); print('all good together, max rank', max(r.values()))
except RuntimeError as e: print('together cycle', e)
st3 = base|set(good)
r = ranks(st3)
roots3=[c for c in range(NC) if c not in st3]
print('ROOTS3', len(roots3), roots3)
print('RANK3', [r[c] for c in range(NC)])
from collections import Counter
print(Counter(P[prod[c]][0] for c in roots3))
obl = {}
for l in open(os.path.join(ROOT, 'tools/oblgen/out/obligations.tsv')):
    f = l.rstrip('\n').split('\t')
    if f[1].startswith('H_BUNDLE('):
        c = int(re.match(r'chan (\d+)', f[2])[1]); obl[c] = (f[3], f[4])
with open(os.path.join('/home/user/asyncfpga3/formal/lean/Wip/C8x3','roots3.tsv'),'w') as w:
    w.write('chan\tproducer\tinstance\t8w_expect\trank3\n')
    for c in roots3: w.write(f'{c}\t{P[prod[c]][0]}\t{obl[c][0]}\t{obl[c][1]}\t0\n')
    for c in good: w.write(f'{c}\tamerge(now structural)\t{obl[c][0]}\t{obl[c][1]}\t{r[c]}\n')
print('roots3 expectations', Counter(obl[c][1] for c in roots3))
