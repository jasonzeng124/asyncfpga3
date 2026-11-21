#!/usr/bin/env python3
"""margin/bram/mk_bnd_mem.py BENCH_BND.json OUT.json (shard C): shard A's tools-A/target/mk_bnd_sim.py, generalised for
memory kernels: (1) a kernel with NO operand word (only arrays) gets empty a_data / b_data and the start channel's
acknowledge in the a / b slots; (2) every other input channel's acknowledge (a memref's <array>_start_ack, a third
operand's ack) is listed in "xacks": simx_conv.py writes them and simx waits for all of them (with a_ack, b_ack,
start_ack) before it drops the request, and for all of them low before the next offer. All input requests must still be
one node (the bench's req_core). Otherwise as mk_bnd_sim.py."""
import json, sys
b = json.load(open(sys.argv[1]))["ports"]
one = lambda k: b[k]["nodes"][0]
ins = [k[:-5] for k in b if k.endswith("_data") and b[k]["dir"] == "input" and not k.endswith("_host_wdata")]
chans = [k[:-4] for k in b if k.endswith("_req") and b[k]["dir"] == "input" and not k.endswith("_host_req")]
reqs = {one(c + "_req") for c in chans}
assert len(reqs) == 1, reqs
if ins:
    a, bb = ins[0], ins[-1]
    aack, back = one(a + "_ack"), one(bb + "_ack")
    ad, bd = b[a + "_data"]["nodes"], b[bb + "_data"]["nodes"]
else:
    a = bb = "start"
    aack = back = one("start_ack"); ad = bd = []
xacks = sorted({one(c + "_ack") for c in chans} - {aack, back, one("start_ack")})
xdata = [{"name": c, "ack": one(c + "_ack"), "nodes": b[c + "_data"]["nodes"]} for c in ins[1:-1]]   # > 2 operand words
void = "void" in b   # a void kernel: the bench's completion join takes p_end (its own logic drives p_end_ack)
B = {"rst": one("rst"), "req": reqs.pop(), "a_ack": aack, "b_ack": back,
     "start_ack": one("start_ack"), "out0_req": one("out0_req"), "out0_ack": one("out0_ack"),
     "pend_ack": None if void else one("p_end_ack"),
     "a_data": ad, "b_data": bd, "out0_data": b["out0_data"]["nodes"], "xacks": xacks}
# the host's port of each array (<array>_host_req / _we / _addr / _wdata in, _ack out): simx --hostport drives the fills
# through it as the bench's sequencer does (gen_bench.py: payload one aclk before the request, 2-flop synchronised ack)
hosts = []
for k in sorted(b):
    if k.endswith("_host_req") and b[k]["dir"] == "input":
        h = k[:-len("_host_req")]
        hosts.append({"name": h, "req": one(h + "_host_req"), "we": one(h + "_host_we"), "ack": one(h + "_host_ack"),
                      "addr": b[h + "_host_addr"]["nodes"], "wdata": b[h + "_host_wdata"]["nodes"]})
B["hosts"] = hosts
B["xdata"] = xdata
hostin = {x for h in hosts for x in [h["req"], h["we"]] + h["addr"] + h["wdata"] if not x.startswith("const")}
env = sorted(hostin | {x for c in xdata for x in c["nodes"] if not x.startswith("const")} | {B["rst"], B["req"], B["out0_ack"]} | ({B["pend_ack"]} if B["pend_ack"] else set()) |
             {x for x in ad + bd if not x.startswith("const")})
json.dump({"boundary": B, "env": env, "operands": [a, bb], "channels": chans}, open(sys.argv[2], "w"))
print("void" if void else "", "operands", a, bb, "channels", chans, "extra acks", len(xacks), "env nodes", len(env))
