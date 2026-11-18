#!/usr/bin/env python3
"""Gate-level speed-independent explorer vs the stage-level (marked-graph) model.

Shard C of the formal study of research/data/suite/ringfloor.md's collapse claim:
"the gate network (bd_fork / bd_join / bd_mux select-join / bd_steer) adds arcs,
not tokens", i.e. the netlist of real LUT cells behaves like the stage model in
which stage t is excited iff every stage feeding it differs from it and every
stage it feeds equals it.

Gate model
  * every LUT whose output is a state bit is a gate: link controllers (bd_c2n),
    fork / join C-elements (bd_c2, bd_c3 = bd_ctree N<=4), bd_mux's uj0 / uj1 /
    uor / uxa / uya, bd_steer's LUT6_2 halves and its LUT2 OR, optionally the
    bd_delay buffers (--delays).  Functions are computed from the verbatim LUT
    INITs of cells/rtl (rst pin = 0 after reset).
  * a gate is excited iff f(inputs, own output) != output; one excited gate
    fires per step, any order (unbounded gate delays, zero wire delays: the
    speed-independent model).  BFS over all reachable states.
  * semi-modularity (hazard) is checked on every edge: a gate excited before a
    firing of ANOTHER gate and not excited after it, without having fired.
Data path abstracted: only req / ack / select / condition wires.  The mux select
s and the steer condition s are fixed to 1 (the loop iterates: the mux takes its
back-edge input y, the steer takes branch 1 = trueResult back into the loop);
the mux's x input is tied to 0 (req) and the steer's branch 0 goes to a bd_snk
(ack0 = req0).  This is "fixed mode"; see --help for the per-topology params.

Stage model: derived from the same netlist -- feeders(t) = link outputs reached
by tracing t's req_in backwards through non-link gates; fed(p) = the stages
whose feeders contain p (and checked against tracing p's c_next backwards).

Initial markings: EVERY stage vector x in {0,1}^S.  Two gate initial states per x:
  comp  : the "consistent completion": link controllers = x; every internal
          gate whose function is decided by its inputs takes that value; an
          internal hold gate (C-element with disagreeing inputs) takes the
          value of the side that has not moved yet: a request-side gate the
          value of the stage it drives, an acknowledge-side gate NOT the value
          of the stage whose c_next it drives.  Checked a posteriori: across all
          reachable gate states every stable internal gate equals the
          completion of the state's projection (column "inv").
  reset : the physical power-up with bd_c2n_set on every link with x=1 and every
          other cell as bdc/emit.py emits it (bd_c2 / bd_c3 / bd_mux joins come
          up 0), combinational gates settled with rst=1, then rst falls.
"""
import argparse
import itertools
import sys
from collections import defaultdict

# ---------------------------------------------------------------- LUT cells --


def lut_table(init, pins, rst_pin=None, rst=0, nbits=6, consts=None):
    """Truth table of a LUT over the listed signal pins.

    init: INIT integer; pins: list of pin indices (I0..I5) that carry signals,
    in the order the gate's input list will be given; rst_pin: pin index of
    rst (set to `rst`); consts: {pin: value} for tied pins.  Unlisted pins = 0.
    Returns an int whose bit k is the output for input vector k (bit j of k =
    value of pins[j])."""
    consts = dict(consts or {})
    if rst_pin is not None:
        consts[rst_pin] = rst
    t = 0
    for k in range(1 << len(pins)):
        addr = 0
        for j, p in enumerate(pins):
            if (k >> j) & 1:
                addr |= 1 << p
        for p, v in consts.items():
            if v:
                addr |= 1 << p
        if (init >> addr) & 1:
            t |= 1 << k
    return t


INIT = {
    "bd_c2":  0x00E8_00E8_00E8_00E8,   # I0 a, I1 b, I2 q, I3 rst
    "bd_c2n": 0x00B2_00B2_00B2_00B2,   # I0 a, I1 b, I2 q, I3 rst
    "bd_c2n_set": 0xFFB2_FFB2_FFB2_FFB2,
    "bd_c3":  0x0000_FE80_0000_FE80,   # I0 a, I1 b, I2 c, I3 q, I4 rst
    "bd_c4":  0x0000_0000_FFFE_8000,   # I0..I3, I4 q, I5 rst
    "mux_uj0": 0x0000_AE08_0000_AE08,  # I0 x_req, I1 ctl_req, I2 s, I3 j0, I4 rst
    "mux_uj1": 0x0000_EA80_0000_EA80,  # I0 y_req, I1 ctl_req, I2 s, I3 j1, I4 rst
    "steer":  0x8888_8888_2222_2222,   # LUT6_2: I0 req, I1 s, I5 = 1
    "lut2_or": 0xE,
    "lut1_buf": 0x2,
    "lut1_inv": 0x1,
}


class Net:
    """A netlist of single-output gates over named signals, with wires as
    aliases (resolved by union-find in finalize())."""

    def __init__(self):
        self.names = {}
        self.parent = []
        self.gates = []          # dicts: name, out, ins, tab, rtab, kind, self_fb
        self.const = {}
        self.links = []          # (gate index) of link controllers, stage order
        self.env = []            # gate indices of environment choice bits
        self.req_pin = {}        # link gate idx -> signal of its req_in
        self.ack_pin = {}        # link gate idx -> signal of its c_next
        self.zero = self.sig("1'b0")
        self.one = self.sig("1'b1")
        self.const = {self.zero: 0, self.one: 1}

    def sig(self, name):
        if name not in self.names:
            self.names[name] = len(self.parent)
            self.parent.append(len(self.parent))
        return self.names[name]

    def find(self, s):
        while self.parent[s] != s:
            self.parent[s] = self.parent[self.parent[s]]
            s = self.parent[s]
        return s

    def assign(self, dst, src):
        a, b = self.find(self.sig(dst)), self.find(self.sig(src))
        if a != b:
            self.parent[a] = b

    def gate(self, name, out, ins, init, pins, rst_pin=None, consts=None,
             kind="comb", reset_init=None):
        ins = [self.sig(i) for i in ins]
        g = dict(name=name, out=self.sig(out), ins=ins, kind=kind,
                 tab=lut_table(init, pins, rst_pin, 0, consts=consts),
                 rtab=lut_table(reset_init if reset_init is not None else init,
                                pins, rst_pin, 1, consts=consts))
        self.gates.append(g)
        return len(self.gates) - 1

    # -- cells, as cells/rtl writes them ------------------------------------
    def c2(self, name, a, b, q):
        return self.gate(name, q, [a, b, q], INIT["bd_c2"], [0, 1, 2], 3, kind="hold")

    def c3(self, name, a, b, c, q):
        return self.gate(name, q, [a, b, c, q], INIT["bd_c3"], [0, 1, 2, 3], 4, kind="hold")

    def c4(self, name, a, b, c, d, q):
        return self.gate(name, q, [a, b, c, d, q], INIT["bd_c4"], [0, 1, 2, 3, 4], 5, kind="hold")

    def ctree(self, name, ins, q):
        if len(ins) == 1:
            self.assign(q, ins[0])
        elif len(ins) == 2:
            self.c2(name, ins[0], ins[1], q)
        elif len(ins) == 3:
            self.c3(name, ins[0], ins[1], ins[2], q)
        elif len(ins) == 4:
            self.c4(name, *ins, q)
        else:
            raise ValueError("ctree > 4 not modelled")

    def delay(self, name, a, z, n):
        """bd_delay #(.N(n)): wire at n=0; with --delays one LUT1 buffer
        (a chain of n buffers collapsed to one; FASTRISE / FASTFALL side LUTs
        are not modelled)."""
        if n == 0:
            self.assign(z, a)
        else:
            self.gate(name, z, [a], INIT["lut1_buf"], [0])

    def link(self, name, req_in, ack_in, req_out, ack_out, delays=False):
        """bd_link (BD_LINK_DC undefined): ctl = bd_c2n(req_in, ack_out);
        req_out = bd_delay(DELAY)(c); ack_in = bd_delay(DACK, FASTRISE)(c)."""
        c = f"{name}.c"
        g = self.gate(name, c, [req_in, ack_out, c], INIT["bd_c2n"], [0, 1, 2], 3,
                      kind="link", reset_init=INIT["bd_c2n"])
        self.links.append(g)
        self.req_pin[g] = self.sig(req_in)
        self.ack_pin[g] = self.sig(ack_out)
        self.delay(f"{name}.rdly", c, req_out, 1 if delays else 0)
        self.delay(f"{name}.uack", c, ack_in, 1 if delays else 0)
        return g

    def fork(self, name, req, ack, req_out, ack_in):
        for r in req_out:
            self.assign(r, req)
        self.ctree(name, ack_in, ack)

    def join(self, name, req_in, ack_out, req, ack):
        self.ctree(name, req_in, req)
        for a in ack_out:
            self.assign(a, ack)

    def steer(self, name, req, s, ack, req0, ack0, req1, ack1):
        # LUT6_2: O5 = INIT[31:0](I4..I0), O6 = INIT[63:0] with I5 = 1.
        self.gate(f"{name}.O5", req0, [req, s], INIT["steer"] & 0xFFFFFFFF, [0, 1])
        self.gate(f"{name}.O6", req1, [req, s], INIT["steer"], [0, 1], consts={5: 1})
        self.gate(f"{name}.uack", ack, [ack0, ack1], INIT["lut2_or"], [0, 1])

    def mux(self, name, x_req, x_ack, y_req, y_ack, ctl_req, ctl_ack, s,
            z_req, z_ack, delays=False):
        j0, j1, either = f"{name}.j0", f"{name}.j1", f"{name}.either"
        self.gate(f"{name}.uj0", j0, [x_req, ctl_req, s, j0], INIT["mux_uj0"],
                  [0, 1, 2, 3], 4, kind="hold")
        self.gate(f"{name}.uj1", j1, [y_req, ctl_req, s, j1], INIT["mux_uj1"],
                  [0, 1, 2, 3], 4, kind="hold")
        self.gate(f"{name}.uor", either, [j0, j1], INIT["lut2_or"], [0, 1])
        self.delay(f"{name}.udly", either, z_req, 1 if delays else 0)
        self.c2(f"{name}.uxa", j0, z_ack, x_ack)
        self.c2(f"{name}.uya", j1, z_ack, y_ack)
        self.assign(ctl_ack, z_ack)

    def snk(self, req, ack):
        """bd_snk: ack = req (a wire)."""
        self.assign(ack, req)

    def src_stage(self, name, req, ack):
        """bd_src (LUT1 INIT 2'h1: req = ~ack), made a stage of the stage model:
        it is C(1, ~ack) exactly."""
        g = self.gate(name, req, [ack], INIT["lut1_inv"], [0], kind="link")
        self.links.append(g)
        self.req_pin[g] = self.sig("1'b1")
        self.ack_pin[g] = self.sig(ack)
        return g

    def snk_stage(self, name, req, ack):
        """bd_snk made a stage: ack = req through one LUT1 buffer (a wire delay
        on a single-fanout wire), so it is C(req, ~0)."""
        g = self.gate(name, ack, [req], INIT["lut1_buf"], [0], kind="link")
        self.links.append(g)
        self.req_pin[g] = self.sig(req)
        self.ack_pin[g] = self.sig("1'b0")
        return g

    def env_bit(self, name, s, guard):
        """An environment choice bit (a mux select / steer condition, which is
        DATA bundled with a channel): toggles freely while every guard signal
        is 0, i.e. between handshakes of the channel it is bundled with."""
        ins = list(guard) + [s]
        n = len(ins)
        t = 0
        for k in range(1 << n):
            q = (k >> (n - 1)) & 1
            free = all(((k >> j) & 1) == 0 for j in range(n - 1))
            if (1 - q if free else q):
                t |= 1 << k
        g = self.gate(name, s, ins, 0, [], kind="env")
        self.gates[g]["tab"] = t
        self.gates[g]["rtab"] = t
        self.env.append(g)
        return g

    # -- finalize ------------------------------------------------------------
    def finalize(self):
        drv = {}
        for gi, g in enumerate(self.gates):
            g["out"] = self.find(g["out"])
            g["ins"] = [self.find(i) for i in g["ins"]]
            if g["out"] in drv or g["out"] in (self.find(self.zero), self.find(self.one)):
                raise ValueError(f"double driver on {g['name']}")
            drv[g["out"]] = gi
        self.const = {self.find(self.zero): 0, self.find(self.one): 1}
        for gi, g in enumerate(self.gates):
            for i in g["ins"]:
                if i not in drv and i not in self.const:
                    nm = [k for k, v in self.names.items() if self.find(v) == i]
                    raise ValueError(f"undriven input {nm} of {g['name']}")
            g["self_fb"] = g["out"] in g["ins"]
        self.req_pin = {g: self.find(s) for g, s in self.req_pin.items()}
        self.ack_pin = {g: self.find(s) for g, s in self.ack_pin.items()}
        self.drv = drv
        # gate i's output is state bit i
        self.bit = {g["out"]: gi for gi, g in enumerate(self.gates)}
        # precompiled input fetchers: list of (bit index or None, const)
        self.fetch = []
        for g in self.gates:
            f = []
            for i in g["ins"]:
                if i in self.const:
                    f.append((None, self.const[i]))
                else:
                    f.append((self.bit[i], 0))
            self.fetch.append(f)
        self.S = len(self.links)
        self.link_bit = list(self.links)
        return self


# ---------------------------------------------------------------- gate model --

def eval_gate(net, gi, st, reset=False):
    tab = net.gates[gi]["rtab" if reset else "tab"]
    k = 0
    for j, (b, c) in enumerate(net.fetch[gi]):
        v = c if b is None else (st >> b) & 1
        if v:
            k |= 1 << j
    return (tab >> k) & 1


def excited(net, st):
    out = []
    for gi in range(len(net.gates)):
        if eval_gate(net, gi, st) != (st >> gi) & 1:
            out.append(gi)
    return out


def project(net, st):
    """Stage vector of a gate state: link controller outputs in bits 0..S-1,
    environment choice bits (mux select / steer condition) in bits S..S+E-1."""
    x = 0
    for i, gi in enumerate(net.link_bit):
        if (st >> gi) & 1:
            x |= 1 << i
    for e, gi in enumerate(net.env):
        if (st >> gi) & 1:
            x |= 1 << (net.S + e)
    return x


def sigma_assume(net, x):
    """{signal: value} for the environment bits of extended stage vector x."""
    return {net.gates[gi]["out"]: (x >> (net.S + e)) & 1 for e, gi in enumerate(net.env)}


def sensitive(net, gi, j, assume=None):
    """Does gate gi's output depend on its input j, with tied-off (constant)
    inputs held at their constants and `assume`d signals at their values?"""
    g = net.gates[gi]
    n = len(g["ins"])
    fixed = {k: c for k, (b, c) in enumerate(net.fetch[gi]) if b is None}
    if assume:
        for k, i in enumerate(g["ins"]):
            if i in assume:
                fixed[k] = assume[i]
    if j in fixed:
        return False
    # a gate holding its own state (C-element) is traced through the inputs
    # that can make it RISE from 0: a hold gate that cannot rise in this mode
    # (bd_mux's j0 with s = 1) is dormant and feeds nothing
    own = g["ins"].index(g["out"]) if g["out"] in g["ins"] else None
    if own is not None and own != j:
        fixed[own] = 0
    for k in range(1 << n):
        if any(((k >> q) & 1) != v for q, v in fixed.items()):
            continue
        if ((g["tab"] >> k) & 1) != ((g["tab"] >> (k ^ (1 << j))) & 1):
            return True
    return False


# ---------------------------------------------------- stage graph from netlist --

def trace_back_to_links(net, sig, skip=(), assume=None):
    """Link outputs reached from `sig` going backwards through non-link gates
    (through the inputs each gate is sensitive to; not through gates in skip)."""
    seen, out, stack = set(), set(), [sig]
    linkset = set(net.links)
    while stack:
        s = stack.pop()
        if s in seen or s in net.const or (assume and s in assume):
            continue
        seen.add(s)
        gi = net.drv[s]
        if gi in linkset:
            out.add(net.links.index(gi))
            continue
        if gi in skip:
            continue
        nt = net.gates[gi].get("notrace", ())
        for j, i in enumerate(net.gates[gi]["ins"]):
            if i != s and j not in nt and sensitive(net, gi, j, assume):
                stack.append(i)
    return out


def stage_graph(net, assume=None):
    S = net.S
    feeders = [trace_back_to_links(net, net.req_pin[g], (), assume) for g in net.links]
    fed = [set() for _ in range(S)]
    for t in range(S):
        for p in feeders[t]:
            fed[p].add(t)
    # acknowledge side: backwards from c_next, not through request-side hold
    # gates (bd_mux's y_ack = C(j1, z_ack) reads its own join j1)
    _, roles_of = make_completion(net)
    roles = roles_of(assume)
    reqside = {gi for gi, (k, _) in roles.items() if k == "req"}
    ackfed = [trace_back_to_links(net, net.ack_pin[g], reqside, assume) for g in net.links]
    mismatch = [(p, sorted(fed[p]), sorted(ackfed[p])) for p in range(S) if fed[p] != ackfed[p]]
    return feeders, fed, mismatch


# ------------------------------------------------------------- initial states --

def trace_forward_pins(net, gi, assume=None, through_hold=False):
    """From internal gate gi's output, forward through combinational (non-hold,
    non-link) gates and wires: the set of ('req', stage) / ('ack', stage) pins
    reached."""
    fan = defaultdict(list)
    for gj, g in enumerate(net.gates):
        for i in g["ins"]:
            fan[i].append(gj)
    res, seen, stack = set(), set(), [net.gates[gi]["out"]]
    while stack:
        s = stack.pop()
        if s in seen:
            continue
        seen.add(s)
        for t, lg in enumerate(net.links):
            if net.req_pin[lg] == s:
                res.add(("req", t))
            if net.ack_pin[lg] == s:
                res.add(("ack", t))
        for gj in fan[s]:
            g = net.gates[gj]
            if (g["kind"] == "comb" or (through_hold and g["kind"] == "hold")) \
                    and gj != gi and any(
                    i == s and sensitive(net, gj, j, assume) for j, i in enumerate(g["ins"])):
                stack.append(g["out"])
    return res


def make_completion(net):
    """comp(x): see the module docstring.  x is an extended stage vector (the
    environment bits, if any, above bit S).  Returns (comp, roles_of)."""
    cache = {}

    def roles_of(assume):
        key = tuple(sorted((assume or {}).items()))
        if key in cache:
            return cache[key]
        roles = {}
        for gi, g in enumerate(net.gates):
            if g["kind"] == "hold":
                pins = trace_forward_pins(net, gi, assume)
                if not pins:
                    # feeds only another hold gate (bd_mux's y_ack into the
                    # fork's C-element when the path has no link): take the
                    # role of the pins reached through it
                    pins = trace_forward_pins(net, gi, assume, through_hold=True)
                kinds = {k for k, _ in pins}
                if not pins:         # dangling (bd_mux's x_ack with x tied off)
                    roles[gi] = ("none", [])
                    continue
                if len(kinds) != 1:
                    roles[gi] = ("ambiguous", sorted(t for _, t in pins))
                    continue
                roles[gi] = (kinds.pop(), sorted(t for _, t in pins))
        cache[key] = roles
        return roles

    settle = [gi for gi, g in enumerate(net.gates) if g["kind"] not in ("link", "env")]

    def comp(x):
        st = 0
        for i, gi in enumerate(net.link_bit):
            if (x >> i) & 1:
                st |= 1 << gi
        for e, gi in enumerate(net.env):
            if (x >> (net.S + e)) & 1:
                st |= 1 << gi
        roles = roles_of(sigma_assume(net, x))
        guess = {}
        for gi, (k, ts) in roles.items():
            if k == "none":
                guess[gi] = 0
                continue
            if k == "ambiguous":
                return None
            vals = {(x >> t) & 1 for t in ts}
            if len(vals) != 1:
                return None          # the side that has not moved is ambiguous
            v = vals.pop()
            guess[gi] = v if k == "req" else 1 - v
            if guess[gi]:
                st |= 1 << gi
        for _ in range(len(net.gates) + 2):
            changed = False
            for gi in settle:
                cur = (st >> gi) & 1
                if net.gates[gi]["self_fb"]:
                    a = eval_gate(net, gi, st & ~(1 << gi))
                    b = eval_gate(net, gi, st | (1 << gi))
                    v = a if a == b else guess[gi]
                else:
                    v = eval_gate(net, gi, st)
                if v != cur:
                    st ^= 1 << gi
                    changed = True
            if not changed:
                return st
        raise RuntimeError("completion did not settle")

    return comp, roles_of


def make_reset(net):
    """Power-up: rst = 1 with bd_c2n_set on the links set in x.  Hold gates and
    links take their rst value; combinational gates settle; then rst falls.
    Environment bits are taken from x."""
    def reset(x):
        st = 0
        for i, gi in enumerate(net.link_bit):
            if (x >> i) & 1:
                st |= 1 << gi
        for e, gi in enumerate(net.env):
            if (x >> (net.S + e)) & 1:
                st |= 1 << gi
        for _ in range(len(net.gates) + 2):
            changed = False
            for gi, g in enumerate(net.gates):
                if g["kind"] in ("link", "env"):
                    continue
                v = eval_gate(net, gi, st, reset=True)
                if v != (st >> gi) & 1:
                    st ^= 1 << gi
                    changed = True
            if not changed:
                return st
        return None                  # combinational loop does not settle
    return reset


# ------------------------------------------------------------ exploration ----

def explore_gate(net, starts):
    """BFS over everything reachable from the start states.
    Returns ({state: [succ]}, {state: number of non-environment successors})."""
    adj, nenv = {}, {}
    envset = set(net.env)
    frontier = []
    for s in starts:
        if s is not None and s not in adj:
            adj[s] = None
            frontier.append(s)
    while frontier:
        nxt = []
        for st in frontier:
            ex = excited(net, st)
            succ = [st ^ (1 << gi) for gi in ex]
            nenv[st] = sum(1 for gi in ex if gi not in envset)
            for ns in succ:
                if ns not in adj:
                    adj[ns] = None
                    nxt.append(ns)
            adj[st] = succ
        frontier = nxt
    return adj, nenv


def stage_modes(net):
    """Per environment assignment sigma (an int over E bits): (feeders, fed),
    plus the union over sigma of each (for the mode-switching rules), plus the
    links each environment bit's guard reads."""
    E = len(net.env)
    modes = {}
    for sg in range(1 << E):
        assume = sigma_assume(net, sg << net.S)
        f, d, _ = stage_graph(net, assume)
        modes[sg] = (f, d)
    S = net.S
    everfeed = [set().union(*(modes[sg][0][t] for sg in modes)) for t in range(S)]
    everfed = [set().union(*(modes[sg][1][t] for sg in modes)) for t in range(S)]
    guards = []
    for gi in net.env:
        g = net.gates[gi]
        ls = set()
        for i in g["ins"]:
            if i != g["out"]:
                ls |= trace_back_to_links(net, i)
        guards.append(ls)
    return modes, everfeed, everfed, guards


def explore_stage(net):
    """The stage model.  Fixed mode (no environment bits): stage t is excited
    iff every stage feeding it differs from it and every stage it feeds equals
    it.  With environment bits sigma, the feeders / fed sets are those of mode
    sigma, and a stage that has none in this mode but has some in another
    (an unselected mux input, a dead steer branch) is handled as the cells do:
      - fed_sigma(t) empty: t cannot fall (no acknowledge will rise for it);
        it may rise when its feeders differ and every stage it ever feeds is 0
        (the previous handshake's acknowledge has returned to zero);
      - feeders_sigma(t) empty: its request is held at 0; it may fall when its
        fed stages equal it, never rise.
    Environment bit e toggles iff every link its guard reads is 0 (the bundled
    select / condition may change only between handshakes)."""
    S, E = net.S, len(net.env)
    modes, everfeed, everfed, guards = stage_modes(net)
    adj, nenv = {}, {}
    for x in range(1 << (S + E)):
        sg = x >> S
        feeders, fed = modes[sg]
        succ = []
        for t in range(S):
            v = (x >> t) & 1
            F, D = feeders[t], fed[t]
            if not F and everfeed[t]:
                ok = v == 1 and all(((x >> u) & 1) == v for u in (D or everfed[t]))
            elif not D and everfed[t]:
                ok = v == 0 and all(((x >> p) & 1) != v for p in F) and \
                    all(((x >> u) & 1) == 0 for u in everfed[t])
            else:
                ok = all(((x >> p) & 1) != v for p in F) and \
                    all(((x >> u) & 1) == v for u in D)
            if ok:
                succ.append(x ^ (1 << t))
        nenv[x] = len(succ)
        for e in range(E):
            if all(((x >> l) & 1) == 0 for l in guards[e]):
                succ.append(x ^ (1 << (S + e)))
        adj[x] = succ
    return adj, nenv


def scc_dp(adj, proj, nenv):
    """Per node: bitset of reachable projections, bitset of projections of the
    states of reachable DEAD terminal components.  A terminal strongly
    connected component is dead when no state in it has a non-environment
    move (with no environment bits: a state with no excited gate / stage).
    Iterative Tarjan."""
    index, low, onstack, comp_of = {}, {}, set(), {}
    stack, comps = [], []
    counter = 0
    for root in adj:
        if root in index:
            continue
        work = [(root, 0)]
        while work:
            v, i = work.pop()
            if i == 0:
                index[v] = low[v] = counter
                counter += 1
                stack.append(v)
                onstack.add(v)
            succ = adj[v]
            recurse = False
            while i < len(succ):
                w = succ[i]
                i += 1
                if w not in index:
                    work.append((v, i))
                    work.append((w, 0))
                    recurse = True
                    break
                elif w in onstack:
                    low[v] = min(low[v], index[w])
            if recurse:
                continue
            if low[v] == index[v]:
                c = []
                while True:
                    w = stack.pop()
                    onstack.discard(w)
                    comp_of[w] = len(comps)
                    c.append(w)
                    if w == v:
                        break
                comps.append(c)
            if work:
                u = work[-1][0]
                low[u] = min(low[u], low[v])
    reach = [0] * len(comps)
    dead = [0] * len(comps)
    for ci, c in enumerate(comps):        # sinks first
        r = d = 0
        terminal = True
        for v in c:
            r |= 1 << proj(v)
            for w in adj[v]:
                cw = comp_of[w]
                if cw != ci:
                    terminal = False
                    r |= reach[cw]
                    d |= dead[cw]
        if terminal and all(nenv[v] == 0 for v in c):
            for v in c:
                d |= 1 << proj(v)
        reach[ci], dead[ci] = r, d
    return {v: (reach[comp_of[v]], dead[comp_of[v]]) for v in adj}


# ----------------------------------------------------------- predictions -----

def mg_tokenfree_cycle(S, feeders, x):
    """Z(x): p->t if x_p == x_t, t->p otherwise, over stage edges p->t.
    Returns True if Z(x) has a cycle."""
    succ = defaultdict(set)
    for t in range(S):
        for p in feeders[t]:
            if ((x >> p) & 1) == ((x >> t) & 1):
                succ[p].add(t)
            else:
                succ[t].add(p)
    color = {}
    for r in range(S):
        if r in color:
            continue
        stack = [(r, iter(succ[r]))]
        color[r] = 1
        while stack:
            v, it = stack[-1]
            for w in it:
                if color.get(w) == 1:
                    return True
                if w not in color:
                    color[w] = 1
                    stack.append((w, iter(succ[w])))
                    break
            else:
                color[v] = 2
                stack.pop()
    return False


def mg_full_tokenfree(S, feeders, x):
    """The marked graph on 2S transitions (t+, t-): per stage edge p->t arcs
    p+->t+, p-->t-, t+->p-, t-->p+, marked per ringfloor.md's table; plus the
    stage's own t+->t- and t-->t+ alternation (marked t+->t- iff x_t = 1).
    True iff some cycle carries no token."""
    def node(t, up):
        return 2 * t + (0 if up else 1)
    succ = defaultdict(set)
    for t in range(S):
        xt = (x >> t) & 1
        # own alternation: a token on t+->t- when x_t = 1 (t- next)
        if not xt:
            succ[node(t, True)].add(node(t, False))
        else:
            succ[node(t, False)].add(node(t, True))
        for p in feeders[t]:
            xp = (x >> p) & 1
            m = {(1, 0): "pp", (0, 1): "mm", (1, 1): "tp", (0, 0): "tm"}[(xp, xt)]
            arcs = {"pp": (node(p, True), node(t, True)),
                    "mm": (node(p, False), node(t, False)),
                    "tp": (node(t, True), node(p, False)),
                    "tm": (node(t, False), node(p, True))}
            for k, (a, b) in arcs.items():
                if k != m:
                    succ[a].add(b)
    color = {}
    for r in range(2 * S):
        if r in color:
            continue
        stack = [(r, iter(succ[r]))]
        color[r] = 1
        while stack:
            v, it = stack[-1]
            for w in it:
                if color.get(w) == 1:
                    return True
                if w not in color:
                    color[w] = 1
                    stack.append((w, iter(succ[w])))
                    break
            else:
                color[v] = 2
                stack.pop()
    return False


# ------------------------------------------------------------- topologies ----

def build_ring(N, delays=False):
    n = Net()
    for i in range(N):
        n.link(f"L{i}", f"r{i}", f"a{i}", f"r{(i + 1) % N}", f"a{(i + 1) % N}", delays)
    return n.finalize(), {"segments": {"ring": list(range(N))}}


def chain(n, name, L, req_in, ack_in, req_out, ack_out, delays, idx):
    """L links from (req_in, ack_in) to (req_out, ack_out); returns stage ids."""
    if L == 0:
        n.assign(req_out, req_in)
        n.assign(ack_in, ack_out)
        return []
    ids = []
    prev_r, prev_a = req_in, ack_in
    for i in range(L):
        r = req_out if i == L - 1 else f"{name}{i}_r"
        a = ack_out if i == L - 1 else f"{name}{i}_a"
        n.link(f"{name}{i}", prev_r, prev_a, r, a, delays)
        ids.append(idx[0])
        idx[0] += 1
        prev_r, prev_a = r, a
    return ids


def build_forkjoin(kind, Ls, LR, delays=False, mode="fixed"):
    """Fork F -> paths (Ls[i] links each) -> J -> LR links -> F.
    kind: 'join' (bd_join N), 'mux' (bd_mux: path 0 = select ctl, path 1 =
    data y), 'steer' (cond_br as emitted: bd_join(cond = path 0, data = path 1)
    then bd_steer, branch 1 = trueResult back into the loop).
    mode 'fixed': s = 1 (loop iterates); mux x tied to 0; steer branch 0 into
    a bd_snk.  mode 'free': s is an environment bit (toggles only while the
    select / condition channel's req and ack are both 0); the mux's x input is
    a bd_src and the steer's branch 0 a bd_snk, both made stages."""
    n = Net()
    idx = [0]
    segs = {}
    k = len(Ls)
    segs["R"] = chain(n, "R", LR, "jz_r", "jz_a", "f_r", "f_a", delays, idx)
    pr, pa = [], []
    for i, L in enumerate(Ls):
        nm = "PQXYZ"[i] if i < 5 else f"S{i}"
        segs[nm] = chain(n, nm, L, f"fo{i}_r", f"fo{i}_a", f"ji{i}_r", f"ji{i}_a", delays, idx)
        pr.append(f"fo{i}_r")
        pa.append(f"fo{i}_a")
    n.fork("F", "f_r", "f_a", pr, pa)
    if kind == "join":
        assert mode == "fixed"
        n.join("J", [f"ji{i}_r" for i in range(k)], [f"ji{i}_a" for i in range(k)], "jz_r", "jz_a")
    elif kind == "mux":
        assert k == 2
        if mode == "fixed":
            n.mux("M", "1'b0", "mx_ack_unused", "ji1_r", "ji1_a", "ji0_r", "ji0_a", "1'b1",
                  "jz_r", "jz_a", delays)
        else:
            n.src_stage("SRC", "mx_r", "mx_a")
            segs["src"] = [idx[0]]
            idx[0] += 1
            n.env_bit("s_mux", "msel", ["ji0_r", "ji0_a"])
            n.mux("M", "mx_r", "mx_a", "ji1_r", "ji1_a", "ji0_r", "ji0_a", "msel",
                  "jz_r", "jz_a", delays)
    elif kind == "steer":
        assert k == 2
        n.join("CJ", ["ji0_r", "ji1_r"], ["ji0_a", "ji1_a"], "cb_req", "cb_ack")
        if mode == "fixed":
            n.steer("CB", "cb_req", "1'b1", "cb_ack", "cb_r0", "cb_a0", "jz_r", "jz_a")
            n.snk("cb_r0", "cb_a0")
        else:
            n.env_bit("s_cond", "csel", ["ji0_r", "ji0_a"])
            n.steer("CB", "cb_req", "csel", "cb_ack", "cb_r0", "cb_a0", "jz_r", "jz_a")
            n.snk_stage("SNK", "cb_r0", "cb_a0")
            segs["snk"] = [idx[0]]
            idx[0] += 1
    else:
        raise ValueError(kind)
    net = n.finalize()
    return net, {"segments": segs}


# ------------------------------------------------------------ conditions -----

def rest_marking(S, feeders, fed, x):
    for t in range(S):
        if (x >> t) & 1:
            if any((x >> p) & 1 for p in feeders[t]) or any((x >> u) & 1 for u in fed[t]):
                return False
    return True


def research_condition(meta, x, kind):
    """ringfloor.md's arithmetic, for a rest marking (every high stage has all
    neighbours low; a high stage = one token).  Cycles: S >= 2T + 1 (and T >= 1:
    a cycle with no token is dead, which ringfloor.md takes for granted);
    fork-join: L_Q >= 2K for each ordered pair of paths, K = T_Q - T_P.
    Returns True when the condition says LIVE."""
    segs = meta["segments"]
    T = {k: sum((x >> s) & 1 for s in v) for k, v in segs.items()}
    L = {k: len(v) for k, v in segs.items()}
    if "ring" in segs:
        return T["ring"] >= 1 and L["ring"] >= 2 * T["ring"] + 1
    paths = [k for k in segs if k != "R"]
    ok = True
    for p in paths:
        s = L[p] + L["R"]
        t = T[p] + T["R"]
        ok &= t >= 1 and s >= 2 * t + 1
    for q in paths:
        for p in paths:
            if p != q:
                K = T[q] - T[p]
                if K > 0:
                    ok &= L[q] >= 2 * K
    return ok


# ------------------------------------------------------------------ driver ---

def analyse(label, params, net, meta, kind, starts_kind=("comp", "reset"), check_inv=True):
    S, E = net.S, len(net.env)
    feeders, fed, mism = stage_graph(net, sigma_assume(net, ((1 << E) - 1) << S))
    sadj, snenv = explore_stage(net)
    sres = scc_dp(sadj, lambda v: v, snenv)
    comp, roles_of = make_completion(net)
    reset = make_reset(net)
    envset = set(net.env)
    linkset = {gi: i for i, gi in enumerate(net.link_bit)}
    envpos = {gi: S + e for e, gi in enumerate(net.env)}
    # with environment bits, start only where every choice point is idle (all
    # links its guard reads are 0), so that sigma is consistent with the
    # handshakes in flight; fixed mode: every stage vector
    guards = stage_modes(net)[3] if E else []
    rows, detail = [], []
    for sk in starts_kind:
        f = comp if sk == "comp" else reset
        starts = {x: f(x) for x in range(1 << (S + E))
                  if all(((x >> l) & 1) == 0 for gl in guards for l in gl)}
        gadj, gnenv = explore_gate(net, [s for s in starts.values() if s is not None])
        gres = scc_dp(gadj, lambda v: project(net, v), gnenv)
        exc = {st: excited(net, st) for st in gadj}
        # semi-modularity: an excited non-environment gate disabled by another
        # gate's firing (environment choices are not hazards)
        nH, hz = 0, None
        for st in gadj:
            ex = exc[st]
            for gi in ex:
                ex2 = set(exc[st ^ (1 << gi)])
                for gj in ex:
                    if gj != gi and gj not in envset and gj not in ex2:
                        nH += 1
                        hz = hz or (st, gi, gj)
        # step simulation: every link / environment firing of the gate model
        # is a step of the stage model at the projected state
        sim_bad, sim_ex = 0, None
        for st in gadj:
            x = project(net, st)
            for gi in exc[st]:
                pos = linkset.get(gi, envpos.get(gi))
                if pos is not None and (x ^ (1 << pos)) not in sadj[x]:
                    sim_bad += 1
                    sim_ex = sim_ex or (st, gi)
        # completion invariant: every stable internal hold gate equals the
        # completion of the state's projection (meaningful without --delays)
        inv_bad, inv_ex = None, None
        if sk == "comp" and check_inv:
            inv_bad = 0
            for st in gadj:
                x = project(net, st)
                c = comp(x)
                if c is None:
                    continue
                for gi in roles_of(sigma_assume(net, x)):
                    if gi not in exc[st] and ((st >> gi) & 1) != ((c >> gi) & 1):
                        inv_bad += 1
                        inv_ex = inv_ex or (st, gi)
        n_start = agree_dead = agree_reach = subset = dead_starts = 0
        rest_n = rest_ok = 0
        z_bad = mg_bad = 0
        same_as_comp = 0
        mism_rows = []
        for x, g0 in starts.items():
            if g0 is None:
                continue
            n_start += 1
            if sk == "reset" and g0 == comp(x):
                same_as_comp += 1
            gr, gd = gres[g0]
            sr, sd = sres[x]
            gdead, sdead = gd != 0, sd != 0
            dead_starts += gdead
            if gd == sd:
                agree_dead += 1
            if gr == sr:
                agree_reach += 1
            elif gr & ~sr == 0:
                subset += 1
            if gr != sr or gd != sd:
                mism_rows.append((x, g0, gr, sr, gd, sd))
            if E == 0:
                z_bad += mg_tokenfree_cycle(S, feeders, x) != gdead
                mg_bad += mg_full_tokenfree(S, feeders, x) != gdead
                if rest_marking(S, feeders, fed, x):
                    rest_n += 1
                    live = research_condition(meta, x, kind)
                    if live == (not gdead):
                        rest_ok += 1
                    else:
                        detail.append(f"{label} {params} start={sk} x={x:0{S}b}: ringfloor "
                                      f"condition says {'live' if live else 'dead'}, gate model "
                                      f"{'deadlocks' if gdead else 'live'}")
        rows.append(dict(
            topo=label, params=params, start=sk, S=S, E=E, gates=len(net.gates),
            gstates=len(gadj), starts=n_start, sstates=1 << (S + E),
            dead=dead_starts, agree_dead=agree_dead, agree_reach=agree_reach,
            subset=subset, hazards=nH, inv=inv_bad,
            z_bad=z_bad if E == 0 else None, mg_bad=mg_bad if E == 0 else None,
            rest=rest_n, rest_ok=rest_ok, sim_bad=sim_bad, sim_ex=sim_ex,
            graph_mism=len(mism), same_as_comp=same_as_comp if sk == "reset" else None,
            mism=mism_rows, hz=hz, inv_ex=inv_ex))
    return rows, detail, (feeders, fed, mism)


def fmt_state(net, st):
    on = [g["name"] for gi, g in enumerate(net.gates) if (st >> gi) & 1]
    return "{" + ", ".join(on) + "}"


def gate_trace(net, start, target_pred):
    """Shortest firing sequence from start to a state satisfying target_pred."""
    from collections import deque
    prev = {start: None}
    dq = deque([start])
    while dq:
        st = dq.popleft()
        if target_pred(st):
            path = []
            while prev[st] is not None:
                ps, gi = prev[st]
                path.append(net.gates[gi]["name"] + ("+" if (st >> gi) & 1 else "-"))
                st = ps
            return list(reversed(path))
        for gi in excited(net, st):
            ns = st ^ (1 << gi)
            if ns not in prev:
                prev[ns] = (st, gi)
                dq.append(ns)
    return None
