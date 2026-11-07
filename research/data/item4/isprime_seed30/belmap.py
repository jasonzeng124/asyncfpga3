import json,sys
j=json.load(open(sys.argv[1]))["modules"]["top"]
nn={}
for name,n in j["netnames"].items():
    for b in n["bits"]:
        if isinstance(b,int): nn.setdefault(b,name)
out=open(sys.argv[2],'w')
for cn,c in j["cells"].items():
    bel=c["attributes"].get("NEXTPNR_BEL","?")
    conns=" ".join("%s=%s"%(p,nn.get(bl[0],bl[0]) if bl else "-") for p,bl in c["connections"].items())
    out.write("%s\t%s\t%s\t%s\n"%(bel,cn,c["type"],conns))
