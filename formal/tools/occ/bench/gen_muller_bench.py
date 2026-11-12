import sys, random
S=int(sys.argv[1]); TOK=int(sys.argv[2]); n=S+2
def val_next(st, v):
    if v==0: return (not st[0]) if (st[0]==st[1]) else None
    if v==S+1: return st[S] if st[S]!=st[S+1] else None
    a=st[v-1]; b=not st[v+1]
    if a==b and st[v]!=a: return a
    return None
st=[False]*n; cnt=[0]*n; events=[]; random.seed(1)
while True:
    en=[v for v in range(n) if val_next(st,v) is not None and not (v==0 and cnt[0]>=2*TOK)]
    if not en: break
    v=random.choice(en)
    sup=[0,1] if v==0 else ([S] if v==S+1 else [v-1,v+1])
    events.append((v,cnt[v],[(u,cnt[u]-1) for u in sup if cnt[u]>0])); st[v]=not st[v]; cnt[v]+=1
cz={(v,k):c for (v,k,c) in events}; tm={(v,k):i for i,(v,k,c) in enumerate(events)}
anc={}
for (v,k,c) in events:
    s=[0]*n; s[v]=k+1
    if k>0: s=[max(a,b) for a,b in zip(s,anc[(v,k-1)])]
    for e in c: s=[max(a,b) for a,b in zip(s,anc[e])]
    anc[(v,k)]=s
out=["import Formal.Net.OccNetDec\nset_option maxRecDepth 100000\nset_option maxHeartbeats 0\nnamespace Bench2\nopen Formal.Net.OccNet\n"]
out.append(f"""def en (v : Nat) (s : Nat → Bool) : Bool :=
  if v = 0 then (s 0 == s 1) else if v = {S+1} then s {S} != s {S+1}
  else (s (v-1) == !s (v+1)) && (s v != s (v-1))
""")
for v in range(1,S+1):
    D=[v,v-1,v+1]
    lens=" else ".join(f"if u = {u} then {cnt[u]}" for u in D)+" else 0"
    causes="[" + ",".join("[" + ",".join(f"({u},{j})" for (u,j) in cz[(v,k)]) + "]" for k in range(cnt[v])) + "]"
    # L as list per (a in D) of list per k of list per b in D
    Lrows=[]
    for a in D:
        Lrows.append("[" + ",".join("[" + ",".join(str(anc[(a,k)][b]) for b in D) + "]" for k in range(cnt[a])) + "]")
    out.append(f"""namespace N{v}
def D : List Nat := [{",".join(map(str,D))}]
def cs : List (List (Nat × Nat)) := {causes}
def C : Cert Nat := ⟨fun u => {lens}, fun u k => if u = {v} then cs.getD k [] else [], fun _ _ => 0⟩
def LT : List (List (List Nat)) := [{",".join(Lrows)}]
def idx (u : Nat) : Nat := D.idxOf u
def L : Nat → Nat → Nat → Nat := fun a k b => if a ∈ D ∧ b ∈ D then ((LT.getD (idx a) []).getD k []).getD (idx b) 0 else 0
theorem chk : enumAll C L (chkAt en (fun _ => false) C {v}) D [] (fun _ => 0) = true := by decide +kernel
end N{v}
""")
out.append("end Bench2\n")
open("Bench2.lean","w").write("".join(out))
print(len(events))
