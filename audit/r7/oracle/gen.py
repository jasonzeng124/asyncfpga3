import re,sys
t=open(sys.argv[1]).read()
rows=re.findall(r"4'd(\d+):\s*vector = \{32'h([0-9A-Fa-f]+), 32'h([0-9A-Fa-f]+), 32'h([0-9A-Fa-f]+)\}",t)
assert len(rows)==16
with open("tab.h","w") as f:
    f.write("unsigned T[16][3]={\n")
    for i,g,b,a in rows: f.write("{0x%s,0x%s,0x%s},\n"%(a,b,g))
    f.write("};\n")
