import sys,re,os
sys.path.insert(0,'/home/user/asyncfpga3/formal/tools/capwit')
import sim
names, ops, out0 = sim.load_net()
txt=open('/home/user/asyncfpga3/formal/lean/Formal/Net/CapstoneCutSpine.lean').read()
spl=re.search(r'def spL : List Bool := \[(.*?)\]',txt).group(1).split(', ')
sp=[s=='true' for s in spl]
prod={};cons={}
for n,o in enumerate(ops):
  for c in sim.outs_of(o): prod[c]=n
  for c in sim.ins_of(o): cons[c]=n
def show(n):
  o=ops[n]; return "%d %s in %s out %s"%(n,o['k'],sim.ins_of(o),sim.outs_of(o))
