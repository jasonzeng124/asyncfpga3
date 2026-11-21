import re,math
R='/root/agentL/rs/research/data/suite/dynamatic/'
est={l.split('\t')[0]:float(l.split('\t')[1]) for l in open(R+'dynamatic_est.tsv') if not l.startswith('#') and l.split('\t')[1].replace('.','').isdigit()}
rs=[];mism=[]
for l in open(R+'routed/README.md'):
    c=[x.strip() for x in l.strip().strip('|').split('|')]
    if len(c)!=7 or not re.match(r'^[0-9.]+$',c[5]): continue
    try: r=float(c[4]); e=float(c[5])
    except: continue
    if abs(est.get(c[0],-1)-e)>0.01: mism.append((c[0],e,est.get(c[0])))
    # recompute ns/iter = mean period * cycles
    p=float(c[2].split()[0]); cy=float(c[3]); 
    if abs(p*cy-r)>0.05*max(1,r)/5: mism.append(('nsiter',c[0],p,cy,p*cy,r))
    rs.append((c[0],r/e,float(c[6])))
g=math.exp(sum(math.log(x[1]) for x in rs)/len(rs))
print(len(rs),'gm',g,'min',min(rs,key=lambda x:x[1]),'max',max(rs,key=lambda x:x[1]))
print('>1.1',sum(x[1]>1.1 for x in rs),'<0.9',sum(x[1]<0.9 for x in rs))
print('mismatch',mism)
# 28 headline subset
H='binary_search branchloop brhash collatz collatz64 countloop dot2 fill fold64 gather horner if_convert if_loop_1 if_loop_2 ipow iterative_sqrt lfsrfind memsum mul_example nested_loop share_test_2 sqrtsub sumi3_mem twoloops varshift vector_rescale while_loop_3 xorshift'.split()
s=[x for x in rs if x[0] in H]; print('headline subset n',len(s),math.exp(sum(math.log(x[1]) for x in s)/len(s)))
