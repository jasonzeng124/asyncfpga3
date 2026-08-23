#!/usr/bin/env python3
"""Emit cycle.vh: a continuous, timestamped transition log of gcd's loop ring.

NOT A TESTBENCH, AND NOT SELF-CHECKING.  This and tb_cycle.v are measurement
instrumentation: they dump cycle_trace.txt and a SUMMARY line, and contain no
assertion, no expected value, and no pass/fail of any kind.  A human (or a
downstream analysis not yet in this tree) has to read the trace to learn
anything.  That is a deliberate exception to this project's rule that a
hardware or simulation run must judge itself -- stated here so nobody mistakes
a clean run of this for evidence that anything works.  If you want a verdict,
use the rigs that produce one; this only produces numbers.

gen_chan.py answers "is this channel toggling" (a count).  gen_trace.py
answers "what value did this channel carry, on the edge that made it valid"
(one snapshot per event, on stdout).  Neither gives what Q1/Q2/Q3 of the
per-iteration cost breakdown need: the WALL-CLOCK TIME of every request and
acknowledge transition on the loop's own critical cycle, plus the input and
output of every matched-delay chain that sits on it -- so a period can be
measured, a phase order can be reconstructed from real timestamps instead of
assumed from source order, and a rising transition's delay-chain traversal
time can be compared against a falling one.

WHERE THE CHANNEL LIST COMES FROM.  bdc/slack.py already builds the
handshake-dialect dataflow graph for gcd and finds its cycles (10 SCCs, all
storage-free -- see its own docstring for what that means and does not mean).
Its --report output was captured once (see /tmp/slack_gcd.txt in the session
that wrote this file) and every `--[%value]-->` edge across all 10 SCCs was
extracted: 145 distinct SSA values, 106 distinct node names.  That list is
pasted below as CYCLE_VALUES / CYCLE_NODES rather than re-derived at build
time, for the same reason gen_trace.py's TRACE table is pasted rather than
inferred: it is read once, checked against the MLIR by a human, and then
trusted -- re-parsing the MLIR here would add a second, unaudited path to the
same names bdc/emit.py already turned into wires.

A handful of those values do not survive to a distinctly-named net (yosys folds
an `assign a = b` into one physical net with one surviving name; the SSA value
that named the other side of the assign is real but not independently
addressable).  Missing ones are reported and skipped, not guessed at -- see
NOT-FOUND handling below and gen_trace.py's own note on the same phenomenon
("a >>> 1 makes z[31] literally a[31]").

DELAY CHAINS.  Every DELAY_BEARING op (bdc/emit.py's own list: addi, subi,
muli, cmpi, andi, ori, xori, shli, shrsi, shrui, select, mux, merge,
control_merge) instantiates exactly one bd_delay chain, `<inst>.udly.chain`,
whose input is `s[0]` ("either", the join's OR'd request) and whose output is
`s[N]` (== its own z_req, aliased).  This scans routed.json's own net names
for `.udly.chain.s[k]` and records (din_bit, dout_bit, N) per instance found
-- 65 in this route, not just the ones on gcd's cycles, because it costs
nothing extra to log all of them and Q4 wants some off-cycle ones for
cross-checking tighten.py's chain-length-vs-delay relationship anyway.

Usage:  GLS_WORK=<dir> python3 gen_cycle.py
Output: cycle.vh (compiled in), cycle_manifest.json (read by the Python
        analysis that turns cycle_trace.txt into the Q1-Q4 numbers).
"""
import json, os, re, sys, collections

HERE = os.environ.get("GLS_WORK") or os.path.dirname(os.path.abspath(__file__))
D = "urig.udut."

# ---------------------------------------------------------------------------
# The 145 SSA values and 106 node names across all 10 SCCs bdc/slack.py found
# in build/frontend/gcd/comp/handshake_transformed.mlir, extracted verbatim
# from `python3 bdc/slack.py --report ...` (repo root).  See module docstring.
CYCLE_VALUES = [
"113","falseResult_73","128","140","148","trueResult_84","falseResult_85",
"88","falseResult_51","62","falseResult_37","31","42","trueResult_26",
"111","112#0","112#1","114","115#0","115#1","116","117#0","117#1",
"result_68","120","121","122","123#0","123#1","123#3","falseResult_71",
"falseResult_75","falseResult_77","124","125#0","125#1","126","127#0",
"127#1","result_78","index_79","129#0","129#1","134","135#0","135#1",
"135#2","136","137","138","139","141","142","143","144","145#0","145#1",
"145#2","145#3","146","149","150","result_80","index_81","151#0","151#2",
"151#3","157","158","160","161","162#0","162#1","162#2","162#3","162#5",
"163","trueResult_82","trueResult_86","falseResult_87","trueResult_88",
"falseResult_89","trueResult_90","falseResult_91","falseResult_93",
"89","falseResult_53",
"63","falseResult_39",
"result_20","index_21","32#0","32#1","38","39#0","39#1","40","41#0",
"41#1","43","44","46","48","49#0","49#1","49#3","trueResult_22",
"trueResult_24","trueResult_28",
"29","30",
"90","result_58","index_59","92#0","92#1","98","99#0","99#1","100",
"101","102","103","104","105#0","105#1","trueResult_60","trueResult_62",
"result_40","index_41","71#0","71#1","77","78#0","78#1","79","80","81",
"82","83#0","83#1","trueResult_42","trueResult_44",
"64",
"result_30","index_31","54#0","54#1","65#0","65#1","66","67","69","70",
"72","73#0","73#1","75#0","75#1","76","trueResult_32","falseResult_41",
"falseResult_43",
]
CYCLE_NODES = [
"cond_br38","merge11","cond_br42","mux16","br13","mux14",
"cond_br29","mux10",
"cond_br24","mux7",
"cond_br21","addi0","mux2",
"cmpi11","cmpi12","shrsi4","fork31","cmpi10","cond_br40","fork28",
"merge10","cond_br41","cond_br46","fork37","control_merge10","br16",
"fork34","control_merge9","cond_br39","control_merge8","cond_br45",
"fork40","ori4","cmpi13","andi4","trunci4","fork36","mux15","br12",
"select1","subi1","fork35","subi0","fork30","merge13","cond_br44",
"mux18","br15","fork33","mux13","cond_br37","select0","cmpi9","fork29",
"merge12","cond_br43","mux17","br14","fork32","mux12",
"cond_br30","mux11",
"shrsi3","cmpi7","andi3","trunci3","cond_br32","fork22",
"control_merge6","cond_br31","fork25","ori3","cmpi6","fork21","mux9",
"mux8","cond_br25",
"cmpi4","shrsi2","cond_br27","fork17","control_merge4","cond_br26",
"fork20","ori2","cmpi5","andi2","trunci2","fork16","mux6",
"cond_br22","fork13","shrsi1","mux1","cond_br20","fork14","cmpi3",
"andi1","trunci1","ori1","cond_br19","fork12","shrsi0","mux0","fork9",
"control_merge2",
]

DELAY_BEARING = {"addi", "subi", "muli", "cmpi", "andi", "ori", "xori",
                  "shli", "shrsi", "shrui", "select", "mux", "merge",
                  "control_merge"}


def vname(ssa):
    s = ssa.lstrip("%").replace("#", "__")
    s = re.sub(r"[^A-Za-z0-9_]", "_", s)
    return ("n" if s[:1].isdigit() else "n_") + s


top = json.load(open(os.path.join(HERE, "routed.json")))["modules"]["top"]
nets = top["netnames"]

scalar = {}          # net name -> bit id, for every single-bit net
for name, nn in sorted(nets.items()):
    b = nn["bits"]
    if len(b) == 1 and isinstance(b[0], int):
        scalar[name] = b[0]

# -- 1. req/ack channels for every cycle value -------------------------------
# A value whose consumer is a DELAY_BEARING cell gets a measurability-site
# bd_link in front of it (bdc/emit.py's measurability_sites, rule A in this
# module's docstring's cross-reference to verify/tighten.py): the compute
# unit's own raw port is named `<v>_u_req`/`_u_ack` (pre-link, what the cell
# itself drives) and the link's own output keeps the plain `<v>_req`/`_ack`
# (post-link, what the rest of the design sees).  Try plain first, then the
# `_u` raw form -- gen_trace.py's TRACE table already relies on exactly this
# for cmpi11 (`n136_u_req`), so it is not a guess.
probes = []           # (label, bit, kind, cat)   kind in req/ack
found_vals, missing_vals = [], []
for v in CYCLE_VALUES:
    base = D + vname("%" + v)
    ok = False
    for suf, kind in ((("_req"), "req"), (("_ack"), "ack")):
        n = base + suf
        if n in scalar:
            probes.append((n, scalar[n], kind, "chan"))
            ok = True
        else:
            nu = base + "_u" + suf
            if nu in scalar:
                probes.append((nu, scalar[nu], kind, "chan"))
                ok = True
    (found_vals if ok else missing_vals).append(v)

# -- 2. delay chains: every instance with a .udly.chain.s[k] net -------------
chain_re = re.compile(re.escape(D) + r"(u[A-Za-z0-9_]+)\.udly\.chain\.s\[(\d+)\]$")
chains = collections.defaultdict(dict)     # inst -> {idx: bit}
for name, bit in scalar.items():
    m = chain_re.match(name)
    if m:
        chains[m.group(1)][int(m.group(2))] = bit

delay_info = {}        # inst -> (din_bit, dout_bit, N)
for inst, idx in chains.items():
    nmax = max(idx)
    if nmax not in idx:
        continue
    # s[0] is `assign s[0] = a;` in bd_delay -- a wire alias, not a driven
    # output, so yosys keeps only the UPSTREAM name for that bit (the same
    # aliasing gen_trace.py documents for `a >>> 1` -> z[31]).  The upstream
    # name is always `<inst>.either`: every DELAY_BEARING cell wires its join
    # exactly `wire either; ... bd_delay #(.N(DELAY)) udly (.a(either), ...)`
    # (bd_ctl.v, bd_mux.v, bd_merge.v, bdc/compute.py's emit_unit all agree).
    ein = D + inst + ".either"
    if ein not in scalar:
        continue
    din, dout = scalar[ein], idx[nmax]
    delay_info[inst] = (din, dout, nmax)
    probes.append((D + inst + ".udly.DIN", din, "din", "delay"))
    probes.append((D + inst + ".udly.DOUT", dout, "dout", "delay"))

# dedup by (bit, kind) -- a value's _req can equal another value's _req when
# yosys folded two SSA names onto one net; log the net once, keep every label
# that pointed at it so the manifest can still explain the duplication.
seen = {}
uniq = []
for label, bit, kind, cat in probes:
    key = (bit, kind)
    if key in seen:
        seen[key]["aliases"].append(label)
        continue
    seen[key] = {"label": label, "bit": bit, "kind": kind, "cat": cat,
                 "aliases": [label]}
    uniq.append(seen[key])

L = ["// AUTO-GENERATED by gen_cycle.py -- %d probed nets (%d chan, %d delay-tap)"
     % (len(uniq), sum(1 for u in uniq if u["cat"] == "chan"),
        sum(1 for u in uniq if u["cat"] == "delay")),
     "integer ycf;",
     "reg [63:0] y_t0, y_t1;",
     'initial ycf = $fopen("cycle_trace.txt", "w");',
     "task y_close; begin $fclose(ycf); end endtask"]
for i, u in enumerate(uniq):
    L.append('always @(dut.n%d) if ($time >= y_t0 && $time <= y_t1) '
             '$fdisplay(ycf, "%%0t %s %%b", $time, dut.n%d);'
             % (u["bit"], u["label"], u["bit"]))

open(os.path.join(HERE, "cycle.vh"), "w").write("\n".join(L) + "\n")

manifest = {
    "nprobes": len(uniq),
    "found_values": found_vals,
    "missing_values": missing_vals,
    "delay_info": delay_info,     # inst -> [din_bit, dout_bit, N]
    "probes": [{"label": u["label"], "bit": u["bit"], "kind": u["kind"],
                "cat": u["cat"], "aliases": u["aliases"]} for u in uniq],
}
json.dump(manifest, open(os.path.join(HERE, "cycle_manifest.json"), "w"), indent=1)

print("cycle values: %d found, %d missing" % (len(found_vals), len(missing_vals)))
if missing_vals:
    print("  missing:", ", ".join(missing_vals))
print("delay chains found:", len(delay_info))
print("total probed nets:", len(uniq))
print("-> cycle.vh, cycle_manifest.json")
