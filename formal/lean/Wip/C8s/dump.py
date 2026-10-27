import os,re,sys
sys.argv=[sys.argv[0],'0']
exec(open('Wip/C8r/walkcheck.py').read().split('if __name__')[0])
spLt = re.search(r"def spL : List Bool := \[(.*?)\]", open('Formal/Net/CapstoneCutSpine.lean').read()).group(1)
spL2=[x.strip()=='true' for x in spLt.split(',')]
prodT = [int(x) for x in re.search(r"def prodT : List \(Fin NO\) := \[(.*?)\]", net).group(1).split(",")]
for c in range(NC):
    if spL2[c]:
        print(c, names[c], 'desc', descL[c], '| prod', prodT[c], opsL[prodT[c]].strip()[:60], '| cons', consT[c], opsL[consT[c]].strip()[:70])
