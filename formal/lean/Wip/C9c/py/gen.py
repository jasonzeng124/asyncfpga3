from proj import pairsets
def enc(p,v,n):
    if p==0: return 16+v
    if p==n+1: return 32+v
    return v
for m in ['iso','rt']:
    n=5
    R,P=pairsets(m,n)
    adj={}
    for p in P:
        for (u,v) in P[p]:
            adj.setdefault(enc(p,u,n),set()).add(enc(p+1,v,n))
    adj.setdefault(48,set()).update({16,17}) if False else None
    adj[48]={16,17}
    adj.setdefault(32,set()).add(48); adj.setdefault(33,set()).add(48)
    print(f"def adj{m.capitalize()} : Nat → List Nat")
    for v in sorted(adj):
        print(f"  | {v} => {sorted(adj[v])}")
    print("  | _ => []")
    print(sum(len(x) for x in adj.values()))
