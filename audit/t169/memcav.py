import math
r={'branchloop':0.40,'collatz':1.60,'collatz64':1.73,'countloop':2.56,'digitdiv':0.49,'dot2':0.52,'fill':3.00,'fir':0.53,'fold64':2.02,'horner':0.67,'if_convert':0.76,'if_loop_2':1.79,'ipow':0.40,'lfsrfind':1.30,'loop_path':1.40,'memsum':0.50,'sqrtsub':2.86,'sumi3_mem':0.29,'while_loop_3':0.76,'xorshift':1.74}
cyc={'branchloop':3.44,'digitdiv':39.5,'dot2':5.98,'fill':1,'fir':5.99,'horner':5,'if_convert':6,'if_loop_2':1.99,'ipow':5,'lfsrfind':2,'loop_path':2,'memsum':5.98,'sumi3_mem':9.99,'while_loop_3':5}
mem={'dot2','fir','fill','if_convert','loop_path','memsum','sumi3_mem','while_loop_3'}
g=lambda v: math.exp(sum(map(math.log,v))/len(v))
print("all n=20 %.3f"%g(list(r.values())))
nm=[v for k,v in r.items() if k not in mem]; print("non-memory n=%d %.3f"%(len(nm),g(nm)))
print("memory kernels at 1 cycle (solver bound) n=20 %.3f"%g([v*cyc.get(k,1) if k in mem else v for k,v in r.items()]))
print("every kernel at 1 cycle n=20 %.3f"%g([v*cyc.get(k,1) for k,v in r.items()]))
print("favourable (<1):",sorted((k,v,cyc.get(k,1)) for k,v in r.items() if v<1))
