#!/usr/bin/env python3
"""Follow-up to explore.py: the cells explore.py did not cover.

  (1) the arbitrated merge as bdc/emit.py builds it (bdc_amerge2 = bd_arbiter +
      uor + udly, index = g2 | in1_ack) as a loop-header control_merge
      (amerge -> bd_fork(result, index)), with the index as the select of the
      loop's data bd_mux, and the loop's two cond_brs; plus bd_merge (the
      unarbitrated cell) in the same place;
  (2) bdc_muxn with N = 3, and bd_ctree with N = 5, 6, in a fork-join loop;
  (3) bd_delay FASTFALL request lines (RFAST = 1) on links.

The arbiter is NOT abstracted: its LUT6_2 (state node q on O6, R0 on O5), its
grant LUT6_2 and its two acknowledge C-elements are modelled with their INITs.
q is SR-like (set r1.~r2, reset ~r1.r2, hold on a tie, frozen while A0 = 1).
The nondeterministic grant is the speed-independent interleaving: when both
requests are up, which one q favours is decided by which one q saw alone
first; when r1 rises (q excited to rise) and r2 rises before q fires, q's
transition is disabled -- that is the metastability point, and it is counted
separately as an arbitration race, not as a hazard (on silicon the node
resolves either way; both resolutions are explored, because q firing before
r2 rises is the other interleaving).

Every run also checks the four-phase protocol on every channel (req rises
only while ack = 0, falls only while ack = 1; ack rises only while req = 1,
falls only while req = 0) and bundled-data stability of every select /
condition / index (it must not change while its channel's req or ack is 1).
A lost or duplicated token shows up as a protocol violation.
"""
import os
import sys
from collections import deque

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
from explore import (INIT, Net, analyse, chain, eval_gate, excited, fmt_state,  # noqa: E402
                     gate_trace, lut_table, make_completion)

ARB_STATE = 0xFFF0_FFB2_ACAC_ACAC   # I0 r1, I1 r2, I2 q, I3 rst, I4 A0, I5 = 1
ARB_GRANT = 0x0C0C_0C0C_A0A0_A0A0   # I0 r1, I1 r2, I2 q, I5 = 1: O5 g1, O6 g2


class Net2(Net):
    def __init__(self, fastfall=0):
        super().__init__()
        self.fastfall = fastfall
        self.channels = []       # (name, req, ack)
        self.bundled = []        # (name, data signal, req, ack)
        self.arb_q = []          # gate indices of arbiter state nodes

    def chan(self, name, req, ack):
        self.channels.append((name, req, ack))

    def link(self, name, req_in, ack_in, req_out, ack_out, delays=False):
        self.chan(f"{name}.in", req_in, ack_in)
        if not self.fastfall:
            return super().link(name, req_in, ack_in, req_out, ack_out, delays)
        # bd_link RFAST = 1: rdly = bd_delay #(.N(n), .FASTFALL(1)):
        # s1 = LUT1(a), s_{i+1} = LUT2 INIT 8 (s_i & a), z = s_n
        c = f"{name}.c"
        g = self.gate(name, c, [req_in, ack_out, c], INIT["bd_c2n"], [0, 1, 2], 3,
                      kind="link")
        self.links.append(g)
        self.req_pin[g] = self.sig(req_in)
        self.ack_pin[g] = self.sig(ack_out)
        prev = c
        for i in range(self.fastfall):
            z = req_out if i == self.fastfall - 1 else f"{name}.rdly{i + 1}"
            if i == 0:
                self.gate(f"{name}.rdly{i + 1}", z, [prev], INIT["lut1_buf"], [0])
            else:
                self.gate(f"{name}.rdly{i + 1}", z, [prev, c], 0x8, [0, 1])
            prev = z
        self.assign(ack_in, c)
        return g

    def arbiter(self, name, r1, A1, r2, A2, R0, A0):
        q, g1, g2 = f"{name}.q", f"{name}.g1", f"{name}.g2"
        gi = self.gate(f"{name}.ustate.O6", q, [r1, r2, q, A0], ARB_STATE, [0, 1, 2, 4], 3,
                       consts={5: 1}, kind="hold")
        self.arb_q.append(gi)
        self.gate(f"{name}.ustate.O5", R0, [r1, r2, q, A0], ARB_STATE & 0xFFFFFFFF,
                  [0, 1, 2, 4], 3)
        self.gate(f"{name}.ugrant.O5", g1, [r1, r2, q], ARB_GRANT & 0xFFFFFFFF, [0, 1, 2])
        self.gate(f"{name}.ugrant.O6", g2, [r1, r2, q], ARB_GRANT, [0, 1, 2], consts={5: 1})
        self.c2(f"{name}.ua1", g1, A0, A1)
        self.c2(f"{name}.ua2", g2, A0, A2)
        return g1, g2

    def amerge2(self, name, in0_r, in0_a, in1_r, in1_a, z_r, z_a, index, delays=False):
        """bdc_amerge2_W: one bd_arbiter; won[1] = g2 | in1_ack; index = won[1];
        uor = LUT1 buffer on r0; udly = bd_delay(DELAY) (wire, or one buffer)."""
        r0 = f"{name}.r0"
        g1, g2 = self.arbiter(f"{name}.uarb1", in0_r, in0_a, in1_r, in1_a, r0, z_a)
        self.gate(f"{name}.won1", index, [g2, in1_a], INIT["lut2_or"], [0, 1])
        either = f"{name}.either"
        self.gate(f"{name}.uor", either, [r0], INIT["lut1_buf"], [0])
        self.delay(f"{name}.udly", either, z_r, 1 if delays else 0)
        for c in ((f"{name}.in0", in0_r, in0_a), (f"{name}.in1", in1_r, in1_a),
                  (f"{name}.z", z_r, z_a)):
            self.chan(*c)

    def merge(self, name, x_r, x_a, y_r, y_a, z_r, z_a, delays=False):
        """bd_merge: z_req = delay(x_req | y_req); x_ack = C(x_req, z_ack);
        y_ack = C(y_req, z_ack); sel = x_req | x_ack (data only).  Index for a
        control_merge built on it: sel (1 = x)."""
        either = f"{name}.either"
        self.gate(f"{name}.uor", either, [x_r, y_r], INIT["lut2_or"], [0, 1])
        self.delay(f"{name}.udly", either, z_r, 1 if delays else 0)
        self.c2(f"{name}.uxa", x_r, z_a, x_a)
        self.c2(f"{name}.uya", y_r, z_a, y_a)
        self.gate(f"{name}.usel", f"{name}.sel", [x_r, x_a], INIT["lut2_or"], [0, 1])
        for c in ((f"{name}.x", x_r, x_a), (f"{name}.y", y_r, y_a), (f"{name}.z", z_r, z_a)):
            self.chan(*c)

    def muxn(self, name, ins, ctl_r, ctl_a, s_bits, z_r, z_a, delays=False):
        """bdc_muxn N: sel_k = ctl_req & (s == k) (one LUT per k, as yosys may
        map it), j_k = bd_c2(in_k_req, sel_k), uor = LUT1 over |j (an OR gate
        then the LUT1 buffer), ua_k = bd_c2(j_k, z_ack), ctl_ack = z_ack."""
        n = len(ins)
        nb = len(s_bits)
        js = []
        for k, (r, a) in enumerate(ins):
            sel = f"{name}.sel{k}"
            sig = [ctl_r] + list(s_bits)
            t = 0
            for v in range(1 << (nb + 1)):
                if (v & 1) and (v >> 1) == k:
                    t |= 1 << v
            gi = self.gate(f"{name}.usel{k}", sel, sig, 0, [])
            self.gates[gi]["tab"] = self.gates[gi]["rtab"] = t
            j = f"{name}.j{k}"
            self.c2(f"{name}.uj{k}", r, sel, j)
            js.append(j)
            self.c2(f"{name}.ua{k}", j, z_a, a)
            self.chan(f"{name}.in{k}", r, a)
        orj = f"{name}.orj"
        t = 0
        for v in range(1 << n):
            if v:
                t |= 1 << v
        gi = self.gate(f"{name}.or", orj, js, 0, [])
        self.gates[gi]["tab"] = self.gates[gi]["rtab"] = t
        either = f"{name}.either"
        self.gate(f"{name}.uor", either, [orj], INIT["lut1_buf"], [0])
        self.delay(f"{name}.udly", either, z_r, 1 if delays else 0)
        self.assign(ctl_a, z_a)
        self.chan(f"{name}.ctl", ctl_r, ctl_a)
        self.chan(f"{name}.z", z_r, z_a)

    def ctree(self, name, ins, q):
        if len(ins) <= 4:
            return super().ctree(name, ins, q)
        nch = (len(ins) + 3) // 4
        parts = []
        for i in range(nch):
            chunk = ins[4 * i: 4 * i + 4]
            p = f"{name}.part{i}"
            super().ctree(f"{name}.chunk{i}", chunk, p)
            parts.append(p)
        self.ctree(f"{name}.top", parts, q)


# ------------------------------------------------------------- monitors -----

def resolve(net, name):
    return net.find(net.sig(name)) if name in net.names else None


def sigval(net, st, s):
    if s in net.const:
        return net.const[s]
    return (st >> net.bit[s]) & 1


def monitors(net, adj):
    """Protocol and bundled-data checks over every edge of the gate graph.
    Returns (violations list[(kind, name, state, gate)])."""
    chans = []
    for nm, r, a in net.channels:
        r, a = net.find(net.sig(r)), net.find(net.sig(a))
        if r in net.const and a in net.const:
            continue
        chans.append((nm, r, a))
    bund = [(nm, net.find(net.sig(d)), net.find(net.sig(r)), net.find(net.sig(a)))
            for nm, d, r, a in net.bundled]
    bad = []
    for st, succ in adj.items():
        for ns in succ:
            gi = (st ^ ns).bit_length() - 1
            for nm, r, a in chans:
                rv, av = sigval(net, st, r), sigval(net, st, a)
                rv2, av2 = sigval(net, ns, r), sigval(net, ns, a)
                if rv2 != rv and rv != av:
                    bad.append(("req moved while ack differs", nm, st, gi))
                if av2 != av and av == rv:
                    bad.append(("ack moved while req equal", nm, st, gi))
            for nm, d, r, a in bund:
                if sigval(net, st, d) != sigval(net, ns, d) and \
                        (sigval(net, st, r) or sigval(net, st, a)):
                    bad.append(("data moved mid-handshake", nm, st, gi))
    return bad


def hazards(net, adj, exclude=()):
    """(state, fired, disabled) semi-modularity violations; disabling of a gate
    in `exclude` (arbiter state nodes, environment bits) is listed apart."""
    hz, arb = [], []
    exc = {st: set(excited(net, st)) for st in adj}
    for st in adj:
        for gi in exc[st]:
            e2 = exc[st ^ (1 << gi)]
            for gj in exc[st]:
                if gj != gi and gj not in e2:
                    (arb if gj in exclude else hz).append((st, gi, gj))
    return hz, arb, exc


def explore_from(net, starts, limit=3_000_000):
    adj = {}
    dq = deque()
    for s in starts:
        if s not in adj:
            adj[s] = None
            dq.append(s)
    while dq:
        st = dq.popleft()
        succ = [st ^ (1 << gi) for gi in excited(net, st)]
        adj[st] = succ
        for ns in succ:
            if ns not in adj:
                adj[ns] = None
                dq.append(ns)
                if len(adj) > limit:
                    raise RuntimeError("state limit")
    return adj


def trace_to(net, start, target):
    return gate_trace(net, start, lambda s: s == target)


# --------------------------------------------------------- loop header -------

def matched_delay(net, name, either, z, data_out, data_ins, fn):
    """The request delay of a cell whose data (index / select) is computed from
    the same state as its request: abstracted as 'long enough' -- z rises only
    once `data_out` equals fn(data_ins) (the data has settled), falls when
    `either` falls.  The data inputs are not traced by the stage-graph
    derivation (they are a timing side condition, not a handshake arc)."""
    ins = [either, data_out] + list(data_ins) + [z]
    n = len(ins)
    t = 0
    for v in range(1 << n):
        b = [(v >> j) & 1 for j in range(n)]
        e, d, xs, q = b[0], b[1], b[2:-1], b[-1]
        if not e:
            o = 0
        elif d == fn(*xs):
            o = 1
        else:
            o = q
        if o:
            t |= 1 << v
    gi = net.gate(name, z, ins, 0, [], kind="hold")
    net.gates[gi]["tab"] = net.gates[gi]["rtab"] = t & ~0 if False else t
    # reset: rst forces nothing here (bd_delay has no rst); start from 0
    net.gates[gi]["rtab"] = 0
    net.gates[gi]["notrace"] = tuple(range(1, n - 1))
    return gi


def build_loop(k=1, merge="amerge", mode="fixed", LC=0, LB=1, LD=1, LK=1, LB2=1):
    """A loop as Dynamatic / bdc emit it, abstracted to its handshakes:

      reservoir (2k links holding k tokens: the function's entry)
        -> fork F0 -> entry control (CM in0) and entry data (M x)
      CM = control_merge (bdc_amerge2 + bd_fork(result, index)), or the same
           with bd_merge (x = back edge) in place of the arbitrated merge
      index -> M.ctl directly (unlinked), s = the index (won[1] = g2 | in1_ack)
      M = bd_mux(x = entry data, y = data back edge) -> LD links -> fork FD
      FD -> LK links (the condition's producer, e.g. the cmpi) -> fork FC
      FD -> data of cond_br CBd;  FC -> condition of CBc and CBd
      CM result -> LC links -> data of cond_br CBc (the control token)
      CBc true -> LB links -> CM in1;  CBd true -> LB2 links -> M y
      both false branches -> bd_snk (loop exit)
    mode 'fixed': the condition is 1 (never exits); 'free': an environment bit
    that may change only while the condition's producer channel is idle."""
    n = Net2()
    idx = [0]
    segs = {}
    segs["E"] = chain(n, "E", 2 * k, "1'b0", "e_head_a", "e_r", "e_a", False, idx)
    n.fork("F0", "e_r", "e_a", ["enc_r", "end_r"], ["enc_a", "end_a"])
    n.chan("entry", "e_r", "e_a")
    if merge == "amerge":
        # amerge2 with the matched request delay
        r0 = "CM.r0"
        g1, g2 = n.arbiter("CM.uarb1", "enc_r", "enc_a", "bc_r", "bc_a", r0, "cm_a")
        n.gate("CM.won1", "index", [g2, "bc_a"], INIT["lut2_or"], [0, 1])
        n.gate("CM.uor", "CM.either", [r0], INIT["lut1_buf"], [0])
        matched_delay(n, "CM.udly", "CM.either", "cm_r", "index", [g2, "bc_a"],
                      lambda a, b: a | b)
        for c in (("CM.in0", "enc_r", "enc_a"), ("CM.in1", "bc_r", "bc_a"),
                  ("CM.z", "cm_r", "cm_a")):
            n.chan(*c)
    else:
        n.gate("CM.uor", "CM.either", ["bc_r", "enc_r"], INIT["lut2_or"], [0, 1])
        n.c2("CM.uxa", "bc_r", "cm_a", "bc_a")
        n.c2("CM.uya", "enc_r", "cm_a", "enc_a")
        n.gate("CM.usel", "index", ["bc_r", "bc_a"], INIT["lut2_or"], [0, 1])
        matched_delay(n, "CM.udly", "CM.either", "cm_r", "index", ["bc_r", "bc_a"],
                      lambda a, b: a | b)
        for c in (("CM.x", "bc_r", "bc_a"), ("CM.y", "enc_r", "enc_a"),
                  ("CM.z", "cm_r", "cm_a")):
            n.chan(*c)
    n.fork("CF", "cm_r", "cm_a", ["res_r", "idx_r"], ["res_a", "idx_a"])
    segs["C"] = chain(n, "C", LC, "res_r", "res_a", "cbcd_r", "cbcd_a", False, idx)
    n.mux("M", "end_r", "end_a", "bd_r", "bd_a", "idx_r", "idx_a", "index", "m_r", "m_a")
    for c in (("M.x", "end_r", "end_a"), ("M.y", "bd_r", "bd_a"), ("M.ctl", "idx_r", "idx_a"),
              ("M.z", "m_r", "m_a")):
        n.chan(*c)
    n.bundled.append(("index@M", "index", "idx_r", "idx_a"))
    segs["D"] = chain(n, "D", LD, "m_r", "m_a", "d_r", "d_a", False, idx)
    n.fork("FD", "d_r", "d_a", ["kin_r", "cbdd_r"], ["kin_a", "cbdd_a"])
    segs["K"] = chain(n, "K", LK, "kin_r", "kin_a", "k_r", "k_a", False, idx)
    n.fork("FC", "k_r", "k_a", ["cbcc_r", "cbdc_r"], ["cbcc_a", "cbdc_a"])
    if mode == "fixed":
        cond = "1'b1"
    else:
        n.env_bit("cond", "cond", ["k_r", "k_a"])
        cond = "cond"
    for nm, c, d, t, ex in (("CBc", "cbcc", "cbcd", "tc", "xc"), ("CBd", "cbdc", "cbdd", "td", "xd")):
        n.join(f"{nm}J", [f"{c}_r", f"{d}_r"], [f"{c}_a", f"{d}_a"], f"{nm}j_r", f"{nm}j_a")
        n.steer(nm, f"{nm}j_r", cond, f"{nm}j_a", f"{ex}_r", f"{ex}_a", f"{t}_r", f"{t}_a")
        n.snk(f"{ex}_r", f"{ex}_a")
        for cc in ((f"{nm}.cond", f"{c}_r", f"{c}_a"), (f"{nm}.data", f"{d}_r", f"{d}_a"),
                   (f"{nm}.true", f"{t}_r", f"{t}_a"), (f"{nm}.false", f"{ex}_r", f"{ex}_a")):
            n.chan(*cc)
        if mode != "fixed":
            n.bundled.append((f"cond@{nm}", "cond", f"{nm}j_r", f"{nm}j_a"))
    segs["B"] = chain(n, "B", LB, "tc_r", "tc_a", "bc_r", "bc_a", False, idx)
    segs["B2"] = chain(n, "B2", LB2, "td_r", "td_a", "bd_r", "bd_a", False, idx)
    net = n.finalize()
    return net, segs


def reset_state(net, x):
    from explore import make_reset
    return make_reset(net)(x)


def terminal_dead(net, adj):
    """Terminal SCCs with no non-environment move: {state: True} for their
    states.  Returns the set of such states."""
    from explore import scc_dp
    envset = set(net.env)
    nenv = {}
    for st, succ in adj.items():
        nenv[st] = sum(1 for ns in succ if ((st ^ ns).bit_length() - 1) not in envset)
    # reuse scc_dp with identity projection over a compact index
    ids = {st: i for i, st in enumerate(adj)}
    cadj = {ids[st]: [ids[w] for w in succ] for st, succ in adj.items()}
    cn = {ids[st]: nenv[st] for st in adj}
    res = scc_dp(cadj, lambda v: 0, cn)
    # scc_dp's dead bitset is over projections; recompute membership directly
    dead = set()
    for st in adj:
        if nenv[st] == 0:
            # terminal-with-env-only check: every successor is an env move and
            # stays within env-only states
            ok = all(nenv.get(ns, 0) == 0 for ns in adj[st])
            if ok:
                dead.add(st)
    return dead, res, ids
