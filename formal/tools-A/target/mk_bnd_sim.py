#!/usr/bin/env python3
"""mk_bnd_sim.py BENCH_BND.json OUT.json -- shard A: map boundary_bench.py's ports onto sim.py's gcd-shaped keys.
One-operand kernels (collatz: n) use the operand in both slots; two-operand kernels (xorshift: seed, rounds) map the
first data input to a and the second to b. All input requests must be one node (the bench's req_core)."""
import json, sys
b = json.load(open(sys.argv[1]))["ports"]
one = lambda k: b[k]["nodes"][0]
ins = [k[:-5] for k in b if k.endswith("_data") and b[k]["dir"] == "input"]
reqs = {one(k + "_req") for k in ins} | {one("start_req"), one("p_end_req")}
assert len(reqs) == 1, reqs
a, bb = ins[0], ins[-1]
B = {"rst": one("rst"), "req": one(a + "_req"), "a_ack": one(a + "_ack"), "b_ack": one(bb + "_ack"),
     "start_ack": one("start_ack"), "out0_req": one("out0_req"), "out0_ack": one("out0_ack"), "pend_ack": one("p_end_ack"),
     "a_data": b[a + "_data"]["nodes"], "b_data": b[bb + "_data"]["nodes"], "out0_data": b["out0_data"]["nodes"]}
env = sorted({B["rst"], B["req"], B["out0_ack"], B["pend_ack"]} |
             {x for x in B["a_data"] + B["b_data"] if not x.startswith("const")})
json.dump({"boundary": B, "env": env, "operands": [a, bb]}, open(sys.argv[2], "w"))
print("operands", a, bb, "env nodes", len(env))
