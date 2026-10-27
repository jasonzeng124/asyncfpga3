import json,sys
top=json.load(open(sys.argv[1]))["modules"]["top"]
nets={}
for nn,n in top["netnames"].items():
    for b in n["bits"]: nets.setdefault(b,nn)
for cn,c in top["cells"].items():
    b=c["attributes"].get("NEXTPNR_BEL","")
    for pos in sys.argv[2:]:
        if b.startswith(pos):
            print(b,c["type"],{k:v for k,v in c["parameters"].items() if k=="INIT"})
            for p,bl in c["connections"].items():
                print("   ",p,bl,[nets.get(x,x) for x in bl][:1])
            print("   attrs", {k:v for k,v in c["attributes"].items() if 'ORIG' in k or 'PORT' in k})
