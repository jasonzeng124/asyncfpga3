#!/usr/bin/env python3
"""Emit absguard.vh: an EVENT-ALIGNED self-check on gcd's abs.

Why not just snapshot the buses periodically.  A periodic dump samples every
stage of the pipeline at one instant, and the stages are not on the same
transaction -- so an operand from iteration k+1 gets compared against a result
from iteration k and the check reports a fault that never happened.  That trap
already cost this project once on silicon (see the cmpb detector in
cells/hw/gcd_hw.v, which fired on seven vectors that were delivering correct
answers) and it is the same trap here.

So this samples on the only edge where the bundling contract says every one of
these wires is simultaneously valid: the rise of the select's own outgoing
request, z_req.  At that edge the cell's matched delay has expired, which is
precisely the claim `DELAY` exists to make -- if the values are wrong THERE,
either the delay is too short or an operand arrived late, and both are real
faults rather than artefacts of when the observer happened to look.

It checks the one invariant gcd's abs has to satisfy, against ground truth
computed in the testbench from the operand itself:

    x  = %135, the subtractor's output      (the value being absolute-valued)
    s  = %136, cmpi sgt(x, -1)              (the comparator's answer)
    z  = %139, the select's output          (the abs)

    s must equal (x > -1),  and  z must equal |x|.

Both are reported separately on purpose: a wrong `s` with a correct `z`
localises to the comparator, a correct `s` with a wrong `z` to the select or
its delay, and both wrong is a late operand feeding both.
"""
import json, os, re, sys

HERE = os.environ.get("GLS_WORK") or os.path.dirname(os.path.abspath(__file__))
top = json.load(open(os.path.join(HERE, "routed.json")))["modules"]["top"]
nets = top["netnames"]

# z_req is sampled at the OUTPUT of the select's own matched delay chain,
# `udly.chain.s[N]` (bd_latch.v: s[0] is the input, s[N] the output, so the
# last index present is the one to take).  The channel net `n139_req` is not
# in the routed netlist under that name -- it is absorbed into the link that
# consumes it -- and the chain output is the same wire and the more honest
# probe point anyway: it is exactly where the cell claims its data is ready.
# The operands are taken at the SELECT'S OWN INPUT PINS, not at some other
# fork leg of the same value.  %135 forks three ways -- #0 to this cell's
# a_data, #1 to the negate, #2 to the comparator -- and each leg has its own
# bd_link, so the three are not necessarily carrying the same transaction at
# the same instant.  Comparing z against the negate's copy of x reported the
# select as "one transaction behind" when what it was really showing is that
# two fork legs had drifted apart.  a_data is the wire the cell actually
# muxes, so it is the only honest reference for what the cell did.
# Z is the select's OWN output, not the channel downstream of it.  n139 is
# the far side of a bd_link, and a link's latch has not opened yet at the
# instant its request rises -- so reading z there reports the previous
# transaction's value every single time and looks exactly like a mux that
# never settles.  The pre-link value is already brought out as a probe port
# (bdc/emit.py --probe n138), which lands in the routed netlist as
# `rig_abs_data`; likewise the comparator's own operand as `rig_cmp_in`.
#
# C is that comparator operand.  %135 forks to a_data (#0) and to the
# comparator (#2) through SEPARATE links, so "is s right" and "is s right
# for the operand this cell is muxing" are different questions, and only
# comparing all three tells them apart.
WANT = {"A": "urig.udut.n135__0", "B": "urig.udut.n137",
        "S": "urig.udut.n136",    "Z": "rig_abs_data",
        "C": "rig_cmp_in",
        "ZREQ": "urig.udut.uselect1.udly.chain.s"}


def bits(base):
    """The net numbers for `base`, widest-first, as a concatenation."""
    if base in nets and len(nets[base]["bits"]) == 1 \
            and isinstance(nets[base]["bits"][0], int):
        return "dut.n%d" % nets[base]["bits"][0], 1
    if base in nets and len(nets[base]["bits"]) >= 1 and \
            all(isinstance(b, int) for b in nets[base]["bits"]):
        bl = nets[base]["bits"]
        return "{" + ", ".join("dut.n%d" % b for b in reversed(bl)) + "}", len(bl)
    idx = {}
    for name, nn in nets.items():
        m = re.fullmatch(re.escape(base) + r"\[(\d+)\]", name)
        if m and len(nn["bits"]) == 1 and isinstance(nn["bits"][0], int):
            idx[int(m.group(1))] = nn["bits"][0]
    if not idx:
        sys.exit(f"gen_absguard: no net named {base} in this route")
    w = max(idx) + 1
    missing = [k for k in range(w) if k not in idx]
    if missing:
        sys.exit(f"gen_absguard: {base} is missing bit(s) {missing}")
    return "{" + ", ".join("dut.n%d" % idx[k] for k in range(w - 1, -1, -1)) + "}", w


a_s, aw = bits(WANT["A"] + "_data")
b_s, _  = bits(WANT["B"] + "_data")
ss,  _  = bits(WANT["S"] + "_data")
zs,  zw = bits(WANT["Z"])
c_s, _  = bits(WANT["C"])
import re as _re
_ix = sorted(int(m.group(1)) for m in
             (_re.fullmatch(_re.escape(WANT["ZREQ"]) + r"\[(\d+)\]", n)
              for n in nets) if m)
if not _ix:
    sys.exit(f"gen_absguard: no delay chain at {WANT['ZREQ']}")
qs, _ = bits(f"{WANT['ZREQ']}[{_ix[-1]}]")

L = [f"// AUTO-GENERATED by gen_absguard.py -- operands {aw}b, result {zw}b",
     f"wire signed [{aw-1}:0] ag_a = {a_s};",
     f"wire signed [{aw-1}:0] ag_b = {b_s};",
     f"wire                   ag_s = {ss};",
     f"wire signed [{zw-1}:0] ag_z = {zs};",
     f"wire signed [{aw-1}:0] ag_c = {c_s};",
     f"wire                   ag_q = {qs};",
     "integer ag_n, ag_mux, ag_pair, ag_cmpi, ag_fork;",
     "initial begin ag_n=0; ag_mux=0; ag_pair=0; ag_cmpi=0; ag_fork=0; end",
     "always @(posedge ag_q) begin",
     "    ag_n = ag_n + 1;",
     # A PER-TRANSACTION TRACE, not another counter.  The counters above say
     # how often bb10 was wrong; they cannot say what the loop was doing at
     # the moment it stopped, and that is the only question left once the
     # board has told you the failure is exactly "the a<b branch was taken".
     # Bounded, because a passing vector produces thousands of these.
     "    if (ag_n <= 40) $display(\"BB10 #%0d t=%0t diff=%0d neg=%0d "
     "sgt=%0b abs=%0d\", ag_n, $time, ag_a, ag_b, ag_s, ag_z);",
     "    // 1. did the cell's own mux settle before it raised its request?",
     "    if (ag_z !== (ag_s ? ag_a : ag_b)) begin",
     "        ag_mux = ag_mux + 1;",
     "        if (ag_mux <= 6) $display(\"ABS #%0d t=%0t MUX UNSETTLED: "
     "s=%0b a=%0d b=%0d -> z should be %0d, is %0d\", ag_n, $time, ag_s, "
     "ag_a, ag_b, (ag_s?ag_a:ag_b), ag_z);",
     "    end",
     "    // 2. are the two operands even from the same transaction?  b is",
     "    //    0-a by construction (subi1), so b != -a means one fork leg",
     "    //    has run ahead of the other.",
     "    if (ag_b !== -ag_a) begin",
     "        ag_pair = ag_pair + 1;",
     "        if (ag_pair <= 6) $display(\"ABS #%0d t=%0t OPERANDS SKEWED: "
     "a=%0d but b=%0d (should be %0d)\", ag_n, $time, ag_a, ag_b, -ag_a);",
     "    end",
     "    // 3. is the comparator's answer right for the operand present?",
     "    if (ag_a !== ag_c) begin",
"        ag_fork = ag_fork + 1;",
"        if (ag_fork <= 6) $display(\"ABS #%0d t=%0t FORK SKEWED: select sees a=%0d, comparator sees %0d\", ag_n, $time, ag_a, ag_c);",
"    end",
"    if (ag_s !== (ag_c > -1)) begin",
     "        ag_cmpi = ag_cmpi + 1;",
     "        if (ag_cmpi <= 6) $display(\"ABS #%0d t=%0t CMPI WRONG: a=%0d "
     "sgt(a,-1) should be %0b, is %0b\", ag_n, $time, ag_a, (ag_a > -1), ag_s);",
     "    end",
     "end",
     "task absguard_report; begin",
     "    $display(\"ABSGUARD %0d samples: %0d mux-unsettled, %0d "
     "operand-skewed, %0d cmpi-wrong\", ag_n, ag_mux, ag_pair, ag_cmpi);",
     "end endtask"]

open(os.path.join(HERE, "absguard.vh"), "w").write("\n".join(L) + "\n")
print(f"absguard.vh: operands {aw}b, result {zw}b, sampled on the select's own delay-chain output")
