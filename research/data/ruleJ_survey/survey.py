import glob,os,re,subprocess,json,sys
S='/tmp/claude-0/-home-user-asyncfpga3/1493a6da-414d-591f-aed7-9ee9f21c4602/scratchpad'
AF=S+'/wt_gls2/cells/verify/arb_fork.py'
items=[]
for f in sorted(glob.glob(S+'/gcdhw/s*/gcd_hw.sdf')): items.append(('gcd_hw[mine v4+pads]',f))
for f in sorted(glob.glob(S+'/res_R*_s*/gcd_hw.sdf')): items.append(('gcd_hw[coord '+f.split('/')[-2].rsplit('_',1)[0]+']',f))
for f in sorted(glob.glob(S+'/wt_gls2/build/gls2/*/seed*/pnr/soak.sdf')): items.append((f.split('/')[-4],f))
for d in ('coll8','xs8','ip8'):
    for f in sorted(glob.glob(S+f'/wt_coll/build/{d}/*/seed*/pnr/soak.sdf')): items.append((d,f))
RE=re.compile(r'^\s+(ok|VIOLATED)\s+(\S+) client (\d): A0 late (\d+) ps, grant early (\d+) ps, shared (\d+) ps, raw ([-+]\d+), guarded ([-+]\d+)')
rows=[]
for design,f in items:
    r=subprocess.run(['python3',AF,f],capture_output=True,text=True)
    n=0; gaps=r.stdout.count('NOT RESOLVED')
    for l in r.stdout.splitlines():
        m=RE.match(l)
        if m:
            v,arb,k,late,early,sh,raw,g=m.groups(); n+=1
            rows.append(dict(design=design,route=f,arb=arb,client=int(k),late=int(late),early=int(early),shared=int(sh),raw=int(raw),g=int(g),viol=v=='VIOLATED'))
    if n==0 or gaps: print('NOTE',design,f,'parsed',n,'gaps',gaps,'exit',r.returncode, file=sys.stderr)
json.dump(rows,open(S+'/ruleJ/rows.json','w'))
print(len(items),'routes',len(rows),'rows')
