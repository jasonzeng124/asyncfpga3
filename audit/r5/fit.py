import json,sys
v=json.load(open(sys.argv[1])); r=json.load(open(sys.argv[2]))['routes'][sys.argv[3]]
x=[e.get('in',e).get('rounds') for e in v]
for k in ('routed_fast','routed_stalled'):
    y=r[k]; n=len(x); mx=sum(x)/n; my=sum(y)/n
    print(k, round(sum((a-mx)*(b-my) for a,b in zip(x,y))/sum((a-mx)**2 for a in x)/1000,2),'ns/round over',n,'vectors')
