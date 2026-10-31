import sys
sys.argv=[sys.argv[0], sys.argv[1], sys.argv[2]]
exec(open('/tmp/claude-0/-home-user-asyncfpga3/1493a6da-414d-591f-aed7-9ee9f21c4602/scratchpad/rtz/backtrace.py').read())
inv={v:k for k,v in netname.items()}
for nm in ['urig.out0_req','urig.in_ack','urig.udut.n138_req','urig.udut.n163_req','urig.udut.n121_req']:
    n=inv.get(nm); print(nm, n, [(t,v) for t,v in ev.get(n,[])][:12], len(ev.get(n,[])))
