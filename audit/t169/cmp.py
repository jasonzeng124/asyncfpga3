import re,sys
rd={}
for l in open(sys.argv[1]):
    if l.startswith("| ") and not l.startswith("| kernel") and l.count("|")==14:
        c=[x.strip() for x in l.strip().strip("|").split("|")]; rd[c[0]]=c
mine={}
for l in open(sys.argv[2]):
    m=re.match(r"(\S+)\s+(PASS|WRONG|NO RESULT|NOT-A-BOARD-ROUTE)(.*)",l)
    if m: mine[m.group(1)]=l
nums=lambda s: re.findall(r"\d+\.\d+|\d+",s)
bad=0
for k,c in rd.items():
    l=mine.get(k,"")
    want=nums(" ".join([c[2],c[3],c[4],c[5],c[8],c[10],c[12]]))
    # drop Dynamatic figs from mine
    have=nums(re.sub(r"(?<![\d.])0/0","-",re.sub(r"dyn=\S+","",l.split(" ",1)[1] if l else "")))
    if [w for w in want] != [h for h in have if True][:len(want)] and sorted(want)!=sorted(have):
        bad+=1; print("DIFF",k,"\n  readme",want,"\n  mine  ",have)
print("rows",len(rd),"diffs",bad)
