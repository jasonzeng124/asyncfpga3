"""Split one critical cycle (trace.py hops) into PROGRAM.md's FIRST-item categories.

Every hop is an output edge at t caused by an input edge at t_src, dt = t - t_src = wire (routed delay to the pin,
ICBUF D) + arc (the cell's pin->output arc).  slack == 0 on every hop (checked), so the hops tile the period.

Each hop's CELL (not net) is named from the routed JSON (BEL -> nextpnr cell name):
  delay      a matched-delay element: *.udly.chain.*, *.rdly.chain.*, *.uack.chain.*, *.us.chain.*, and the
             pass-through/OR LUT `uor` that feeds a udly (bdc's emit counts it as one link of the chain)
  handshake  every other kernel control cell: C-elements (ctl, ujoin, uj0/uj1, forks, steers' joins, the
             arbiter), steer/merge/fork LUTs and the LUT latches (lat.*) when the path runs through one
  logic      datapath cells: anything else inside bridge_i.udut (yosys' $gt/$abc/$alu/uz_* LUTs, CARRY4, F7)
  harness    outside bridge_i.udut (bench FSM, PS model) -- never expected on a steady-state kernel cycle
Categories (they partition the period):
  rtz        every hop whose output edge is a FALL of a control net (4-phase return-to-zero: phases 3-4),
             wire and arc, whatever cell it is; reported also by cell role
  routing    wire part of a rising control hop out of a handshake cell or into one: the request/ack wires
             between cells (the wire INTO a delay element, and the wires between chain elements, are delay)
  handshake  arc part of a rising hop through a handshake cell
  delay      rising hops through delay elements (wire + arc); split by the bundled data's measured settle:
             logic   = clamp(settle - t_a, 0, d)   where t_a is the event entering the delay instance on the
                       cycle, d the instance's time on the cycle, settle the last arrival (edge time + wire)
                       of the data that instance bundles at any of its loads
             excess  = d - logic
  logic      rising hops through datapath cells (data on the cycle itself), wire + arc
"""
import json, re, collections

CHAIN = re.compile(r"\.(udly|rdly|uack|us)\.chain\.")


def bel_names(routed_json):
    j = json.load(open(routed_json)); m = j["modules"]
    top = [k for k in m if m[k].get("attributes", {}).get("top")] or list(m)
    out = {}
    for k, v in m[top[0]]["cells"].items():
        b = v.get("attributes", {}).get("NEXTPNR_BEL")
        if b: out[b] = k
    return out


def load_names(work):
    d = {}
    for l in open(work + "/names.map"):
        p = l.split()
        if len(p) >= 2 and p[0].startswith("c_"): d[p[0]] = p[1]
    return d


def logical(cell, port, cnames, bels):
    bel = cnames.get(cell, "")
    if port == "O5": bel = bel.replace("6LUT", "5LUT")
    return bels.get(bel, bel)


def role(lname):
    if not lname.startswith("bridge_i.udut."): return "harness"
    n = lname[len("bridge_i.udut."):]
    if CHAIN.search(n) or n.endswith(".uor"): return "delay"
    inst = n.split(".")[0]
    if inst.startswith(("ulink_", "ufork", "ucond_br", "ucontrol_merge", "usink", "uarb")): return "handshake"
    rest = n[len(inst) + 1:]
    # datapath = cells yosys generated ($abc/$gt/$alu/$techmap..., CARRY4) or bdc's result LUTs (uz_*), and the
    # data mux (udat.*); every other named cell inside an instance is bdc control (ujoin, uj0/uj1, uxa/uya acks,
    # uarb*, ctl, lat, ...)
    if rest.startswith(("$", "uz_", "udat")) or "$abc$" in rest or "$auto$" in rest: return "logic"
    return "handshake"


def delay_inst(lname):
    """bridge_i.udut.ucmpi1.udly.chain.g[3].u -> ('ucmpi1', 'udly'); ulink_x.many.stage[1].u.rdly -> (.., 'rdly')"""
    n = lname[len("bridge_i.udut."):]
    if n.endswith(".uor"): return n[:-4], "udly"
    m = CHAIN.search(n)
    return n[:m.start()], m.group(1)
