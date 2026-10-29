import sys, os
sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import explore as X
sys.path.insert(0, os.path.join(X.ROOT, "formal", "lean", "Wip", "C8z2"))
import persim as P
names, ops, out0 = X.sim.load_net()
abstract = "--abstract" in sys.argv
nums=[int(x) for x in sys.argv[1:] if x.isdigit()]
a,b=(nums+[0,0])[:2]
M = X.build(names, ops, out0, abstract, a, b)
r = X.explore(M, ops, out0, int(nums[2]) if len(nums)>2 else 3000, names)
NC=M['NC']
for s in r['dead'][:1]:
    path=[]; cur=s
    while r['seenmap'][cur] is not None:
        p,gi=r['seenmap'][cur]; path.append(gi); cur=p
    path.reverse()
    print("path len", len(path))
    # independent excitation check with persim gates2
    class S: pass
    st=S(); st.req=[bool(s[c]) for c in range(NC)]; st.ack=[bool(s[NC+c]) for c in range(NC)]
    st.it={n:[bool(s[v]) for v in M['itv'][n]] for n in range(len(ops))}
    d=M['dats'](s); st.D=[d(c) for c in range(NC)]
    for n,o in enumerate(ops):
        for j,(key,eT,eF) in enumerate(P.gates2(n,o)):
            cur = st.req[key[1]] if key[0]=='r' else (st.ack[key[1]] if key[0]=='a' else st.it[key[1]][key[2]])
            if (eT(st) and not cur) or (eF(st) and cur):
                print("EXCITED (persim):", n, o['k'], key, names[key[1]] if key[0]!='i' else '')
    print("last 15 fired:", [(gi, M['G'][gi]['out']) for gi in path[-15:]])
    print("start req/ack", st.req[2], st.ack[2], "started", s[M['STARTED']])
    print("out0 req/ack", st.req[out0], st.ack[out0])
    for c in range(NC):
        if st.req[c]!=st.ack[c]:
            pk=ops[M['prod'][c]]['k']
            cons=[ (n,o['k']) for n,o in enumerate(ops) if c in X.sim.ins_of(o)]
            print("unbalanced", names[c], "req",st.req[c],"ack",st.ack[c],"prod",M['prod'][c],pk,"cons",cons)
    for n,o in enumerate(ops):
        if o['k'] in ('mux','muxn','amerge','link') and any(st.it[n]) : pass
    for n in (136,138,139,140,180):
        o=ops[n]; print(n,o['k'],{k:(names[v],st.req[v],st.ack[v],st.D[v]) for k,v in o.items() if k in('c','x','y','z')}, "it",st.it[n])
        z=o['z']; cons=[(m,ops[m]['k']) for m,oo in enumerate(ops) if z in X.sim.ins_of(oo)]; print("   z cons",cons)
    def show(c, depth=0, seen=set()):
        if c in seen or depth>40: print(" "*depth+"(seen) "+names[c]); return
        seen.add(c)
        n=M['prod'][c]; o=ops[n]
        print(" "*depth+f"{names[c]} r{int(st.req[c])}a{int(st.ack[c])} prod {n} {o['k']} it {st.it[n]} ins {[ (names[i],int(st.req[i]),int(st.ack[i])) for i in X.sim.ins_of(o)]}")
        for i in X.sim.ins_of(o):
            if st.req[i] and st.ack[i]: show(i, depth+1, seen)
    print("--- chain from select g212.1")
    show(names.index('g212.1'))
    import pickle
    NCv=NC; inv={}
    for n in range(len(ops)):
        for m,v in enumerate(M['itv'][n]): inv[v]=('i',n,m)
    def key(v): return ('r',v) if v<NCv else (('a',v-NCv) if v<2*NCv else inv[v])
    keys=[key(M['G'][gi]['out']) for gi in path]
    pickle.dump(keys, open(f"path_{a}_{b}.pkl","wb")); print("saved path", len(keys))
