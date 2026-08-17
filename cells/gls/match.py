import json,re,collections
SDF="gcd_hw.sdf"; JS="gcd_hw_routed.json"
txt=open(SDF).read()
RE_CELL=re.compile(r'\(CELLTYPE "([^"]*)"\)\s*\(INSTANCE\s+(\S*)\s*\)')
def unesc(s): return s.replace("\\","")
sdf_inst={}
for ct,inst in RE_CELL.findall(txt):
    sdf_inst[unesc(inst)]=ct
d=json.load(open(JS))
mods=list(d["modules"].keys())
top=d["modules"]["top"]
cells=top["cells"]
jnames=set(cells)
print("modules:",mods)
print("json cells:",len(cells))
print("sdf CELL blocks:",len(sdf_inst))
sdfn=set(sdf_inst)-{""}
print("sdf instances (non-top):",len(sdfn))
inter=sdfn&jnames
print("matched:",len(inter))
print("sdf-only:",len(sdfn-jnames))
print("json-only:",len(jnames-sdfn))
for n in list(sdfn-jnames)[:10]: print("  SDFONLY",repr(n),sdf_inst[n])
jo=jnames-sdfn
tc=collections.Counter(cells[n]["type"] for n in jo)
print("  json-only by type:",tc.most_common())
# celltype agreement
dis=[(n,sdf_inst[n],cells[n]["type"]) for n in inter if sdf_inst[n]!=cells[n]["type"]]
print("celltype disagreements:",len(dis), dis[:5])
print("json type counts:",collections.Counter(c["type"] for c in cells.values()).most_common())
# now endpoint instance names in INTERCONNECT
RE_IC=re.compile(r"\(INTERCONNECT\s+(\S+)\s+(\S+)\s+\(")
eps=set()
for a,b in RE_IC.findall(txt):
    for p in (a,b):
        eps.add(unesc(p).rsplit("/",1)[0])
print("distinct IC endpoint instances:",len(eps),"unmatched:",len(eps-jnames))
for n in list(eps-jnames)[:10]: print("  EPONLY",repr(n))
