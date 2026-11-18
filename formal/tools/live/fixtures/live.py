#!/usr/bin/env python3
"""live.py MLIR [--inv N] [--max-states K] [--json-dir D --tag T] -- an independent liveness check of the circuit bdc emits.

Builds the emitted circuit at the level of its handshake GATES (every state-holding element of the cells: each Muller
stage c = C(req_in, ~ack_out), the C-elements of forks / joins / compute joins / cond_br joins / mux j and ack
C-elements, the arbiter state q and its two ack C-elements, memory station joined/done/hold, the RAM ack), with the
combinational gates (steer ANDs / OR, mux OR, arbiter R0/g) as zero-delay functions, reading the design (which channels
are linked, with how many stages; olink / rlink / fork-out links; fusion; memory accessors) off bdc's own Emitter.
Nothing of emit.token_graph / short_walk / token_floor or ring_tokens.py is used.

Data is abstracted: only values that can steer (cond_br conditions, mux selects, control_merge indices) are tracked;
every i1 produced by a compute cell whose value is not determined by its inputs (cmpi, or anything fed by non-tracked
data) is a NONDETERMINISTIC bit chosen when the cell's output request rises, and copied by forks / stages from there.

Search: explicit-state, from reset, environment = one 4-phase source per argument (N tokens, invocation k+1 offered
only after every result of invocation k came back) and one 4-phase sink per result.  Partial-order reduction (stubborn
sets): a gate transition that is not an arbiter's and does not drive an arbiter input is persistent (checked on every
firing: any transition it disables is reported as a hazard) and is fired alone; nondeterministic values branch; when only
arbiter-related transitions remain, every enabled transition is expanded.  Deadlocks (no enabled transition, invocation
unfinished) are preserved exactly by this reduction.  No bound on trip counts is needed: the state space is finite.

Also: the stage-level projection (Muller stages + boundary sources/sinks; an edge p -> t when p feeds t through
rendezvous cells under the routing of the current state) and its zero graph Z(x); for a deadlock the Z-cycle (trap).
"""
import argparse
import hashlib
import json
import os
import sys
import time
from collections import deque

BDC = os.environ.get("LIVE_BDC_DIR", "/home/user/rs/bdc")
sys.path.insert(0, BDC)
sys.dont_write_bytecode = True
import emit  # noqa: E402
from hs import parse  # noqa: E402


class ModelError(Exception):
    pass


# ----------------------------------------------------------------------------------------------------------- netlist
class Ch:
    """A wire-level handshake channel: one producer port, one consumer port."""
    __slots__ = ("name", "prod", "pport", "cons", "cport", "ctl")

    def __init__(self, name, ctl=False):
        self.name, self.prod, self.pport, self.cons, self.cport, self.ctl = name, None, None, None, None, ctl


class Net:
    def __init__(self):
        self.cells = []
        self.nvar = 0
        self.init = []
        self.varname = []
        self.varcell = []
        self.chs = []

    def var(self, cell, name, init=0):
        i = self.nvar
        self.nvar += 1
        self.init.append(init)
        self.varname.append(name)
        self.varcell.append(cell)
        return i

    def ch(self, name, ctl=False):
        c = Ch(name, ctl)
        self.chs.append(c)
        return c

    def add(self, cell):
        self.cells.append(cell)
        for k, c in enumerate(cell.ins):
            if c.cons is not None:
                raise ModelError(f"channel {c.name} consumed twice ({c.cons.name}, {cell.name})")
            c.cons, c.cport = cell, k
        for k, c in enumerate(cell.outs):
            if c.prod is not None:
                raise ModelError(f"channel {c.name} produced twice ({c.prod.name}, {cell.name})")
            c.prod, c.pport = cell, k
        cell.net = self
        cell.mkvars()
        return cell


# signal evaluation: S = state list (bits / ints), V = value list (per var)
def req(c, S, V):
    return c.prod.oreq(c.pport, S, V)


def ack(c, S, V):
    return c.cons.iack(c.cport, S, V)


def data(c, S, V):
    return c.prod.odata(c.pport, S, V)


def rdeps(c):
    return c.prod.oreq_deps(c.pport)


def adeps(c):
    return c.cons.iack_deps(c.cport)


def ddeps(c):
    return c.prod.odata_deps(c.pport)


def C(inputs, cur):
    if all(inputs):
        return 1
    if not any(inputs):
        return 0
    return cur


class Cell:
    kind = "?"
    stage = False      # a Muller stage (or boundary source / sink) for the stage-level projection

    def __init__(self, name, ins, outs):
        self.name, self.ins, self.outs = name, list(ins), list(outs)
        self.gates = []    # var indices this cell owns that are gates (fire by excitation)

    def mkvars(self):
        pass

    # next value of gate g (None -> not this cell's), and the deps of the gate's next-state function
    def nxt(self, g, S, V):
        raise NotImplementedError

    def deps(self, g):
        raise NotImplementedError

    def on_fire(self, g, S, V, newbit, choice):
        pass

    def choices(self, g, S, V):
        return None   # None -> deterministic; else list of values to branch on

    def odata_deps(self, k):
        return set()


class Stage(Cell):
    kind = "stage"
    stage = True

    def mkvars(self):
        self.c = self.net.var(self, self.name)
        self.gates = [self.c]

    def oreq(self, k, S, V):
        return S[self.c]

    def iack(self, k, S, V):
        return S[self.c]

    def odata(self, k, S, V):
        return V[self.c]

    def oreq_deps(self, k):
        return {self.c}

    def iack_deps(self, k):
        return {self.c}

    def odata_deps(self, k):
        return {self.c}

    def nxt(self, g, S, V):
        r, a = req(self.ins[0], S, V), ack(self.outs[0], S, V)
        if r and not a:
            return 1
        if a and not r:
            return 0
        return S[g]

    def deps(self, g):
        return rdeps(self.ins[0]) | adeps(self.outs[0])

    def on_fire(self, g, S, V, newbit, choice):
        if newbit:
            V[g] = data(self.ins[0], S, V)


class Wire(Cell):
    """constant, br, extui, trunci, ...: a rename of the handshake, data through fn."""
    kind = "wire"

    def __init__(self, name, i, o, fn, fndeps=True):
        super().__init__(name, [i], [o])
        self.fn, self.fndeps = fn, fndeps

    def oreq(self, k, S, V):
        return req(self.ins[0], S, V)

    def iack(self, k, S, V):
        return ack(self.outs[0], S, V)

    def odata(self, k, S, V):
        return self.fn(lambda: data(self.ins[0], S, V))

    def oreq_deps(self, k):
        return rdeps(self.ins[0])

    def iack_deps(self, k):
        return adeps(self.outs[0])

    def odata_deps(self, k):
        return ddeps(self.ins[0]) if self.fndeps else set()


class Fork(Cell):
    kind = "fork"

    def mkvars(self):
        self.a = self.net.var(self, self.name + ".ack")
        self.gates = [self.a]

    def oreq(self, k, S, V):
        return req(self.ins[0], S, V)

    def iack(self, k, S, V):
        return S[self.a]

    def odata(self, k, S, V):
        return data(self.ins[0], S, V)

    def oreq_deps(self, k):
        return rdeps(self.ins[0])

    def iack_deps(self, k):
        return {self.a}

    def odata_deps(self, k):
        return ddeps(self.ins[0])

    def nxt(self, g, S, V):
        return C([ack(o, S, V) for o in self.outs], S[g])

    def deps(self, g):
        d = set()
        for o in self.outs:
            d |= adeps(o)
        return d


class Join(Cell):
    """join, a compute unit, a fused region: a C-element over the requests, the ack broadcast back.
    fn(vals) -> output value (or None); choice=True: an i1 output whose value is None is a nondeterministic bit."""
    kind = "join"

    def __init__(self, name, ins, out, fn=None, choice=False):
        super().__init__(name, ins, [out])
        self.fn, self.choice = fn, choice

    def mkvars(self):
        self.j = self.net.var(self, self.name)
        self.gates = [self.j]

    def oreq(self, k, S, V):
        return S[self.j]

    def iack(self, k, S, V):
        return ack(self.outs[0], S, V)

    def odata(self, k, S, V):
        return V[self.j]

    def oreq_deps(self, k):
        return {self.j}

    def iack_deps(self, k):
        return adeps(self.outs[0])

    def odata_deps(self, k):
        return {self.j}

    def nxt(self, g, S, V):
        return C([req(i, S, V) for i in self.ins], S[g])

    def deps(self, g):
        d = set()
        for i in self.ins:
            d |= rdeps(i)
        return d

    def _val(self, S, V):
        if self.fn is None:
            return None
        return self.fn([data(i, S, V) for i in self.ins])

    def choices(self, g, S, V):
        if S[g] == 0 and self.choice and self._val(S, V) is None:
            pat = getattr(self, "pattern", None)
            if pat is not None:
                return [pat[S[self.pctr]]]
            return [0, 1]
        return None

    def on_fire(self, g, S, V, newbit, choice):
        if newbit:
            V[g] = choice if choice is not None else self._val(S, V)
            if getattr(self, "pattern", None) is not None and choice is not None:
                S[self.pctr] = (S[self.pctr] + 1) % len(self.pattern)


def bit(v, who):
    if v is None:
        raise ModelError(f"{who}: steering on an untracked value")
    if isinstance(v, tuple):
        v = v[0]
    return int(v) & 1


class Steer(Cell):
    """cond_br: bd_join(cond, data) then bd_steer: req0 = j.~s (false), req1 = j.s (true); ack = ack0 + ack1."""
    kind = "steer"

    def __init__(self, name, cond, dat, t, f):
        super().__init__(name, [cond, dat], [f, t])   # out 0 = false, out 1 = true (as req0 / req1)

    def mkvars(self):
        self.j = self.net.var(self, self.name)
        self.gates = [self.j]

    def sel(self, S, V):
        return bit(data(self.ins[0], S, V), self.name)

    def oreq(self, k, S, V):
        if not S[self.j]:
            return 0
        return int(self.sel(S, V) == k)

    def iack(self, k, S, V):
        return ack(self.outs[0], S, V) | ack(self.outs[1], S, V)

    def odata(self, k, S, V):
        return data(self.ins[1], S, V)

    def oreq_deps(self, k):
        return {self.j} | ddeps(self.ins[0])

    def iack_deps(self, k):
        return adeps(self.outs[0]) | adeps(self.outs[1])

    def odata_deps(self, k):
        return ddeps(self.ins[1])

    def nxt(self, g, S, V):
        return C([req(self.ins[0], S, V), req(self.ins[1], S, V)], S[g])

    def deps(self, g):
        return rdeps(self.ins[0]) | rdeps(self.ins[1])

    def route(self, S, V):
        v = data(self.ins[0], S, V)
        return None if v is None else bit(v, self.name)


class Mux(Cell):
    """bd_mux / bdc_muxn: j_k = C(in_k.req, ctl.req . (s == k)); z.req = OR j_k; in_k.ack = C(j_k, z.ack);
    ctl.ack = z.ack; z.data = in_s.data."""
    kind = "mux"

    def __init__(self, name, sel, ins, out):
        super().__init__(name, [sel] + list(ins), [out])
        self.n = len(ins)

    def mkvars(self):
        self.jv = [self.net.var(self, f"{self.name}.j{k}") for k in range(self.n)]
        self.av = [self.net.var(self, f"{self.name}.a{k}") for k in range(self.n)]
        self.gates = self.jv + self.av

    def selv(self, S, V):
        v = data(self.ins[0], S, V)
        if v is None:
            raise ModelError(f"{self.name}: select is an untracked value")
        return v[1] if isinstance(v, tuple) else v

    def oreq(self, k, S, V):
        return int(any(S[j] for j in self.jv))

    def iack(self, k, S, V):
        if k == 0:
            return ack(self.outs[0], S, V)
        return S[self.av[k - 1]]

    def odata(self, k, S, V):
        s = data(self.ins[0], S, V)
        if s is None:
            return None
        s = s[1] if isinstance(s, tuple) else s
        if not 0 <= s < self.n:
            return None
        return data(self.ins[1 + s], S, V)

    def oreq_deps(self, k):
        return set(self.jv)

    def iack_deps(self, k):
        return adeps(self.outs[0]) if k == 0 else {self.av[k - 1]}

    def odata_deps(self, k):
        d = set(ddeps(self.ins[0]))
        for i in self.ins[1:]:
            d |= ddeps(i)
        return d

    def nxt(self, g, S, V):
        if g in self.jv:
            k = self.jv.index(g)
            ctl = req(self.ins[0], S, V)
            sk = int(bool(ctl) and self.selv(S, V) == k)
            return C([req(self.ins[1 + k], S, V), sk], S[g])
        k = self.av.index(g)
        return C([S[self.jv[k]], ack(self.outs[0], S, V)], S[g])

    def deps(self, g):
        if g in self.jv:
            k = self.jv.index(g)
            return rdeps(self.ins[0]) | ddeps(self.ins[0]) | rdeps(self.ins[1 + k])
        k = self.av.index(g)
        return {self.jv[k]} | adeps(self.outs[0])

    def route(self, S, V):
        v = data(self.ins[0], S, V)
        if v is None:
            return None
        return v[1] if isinstance(v, tuple) else v


class AMerge(Cell):
    """bdc_amerge<n>: a cascade of bd_arbiters (cells/rtl/bd_arb.v, decoded from its LUT INITs):
    q' = A0 ? q : (q == 0 && r1 && !r2 ? 1 : q == 1 && r2 && !r1 ? 0 : q)   (reset 1)
    R0 = q ? r1 : r2 ; g1 = q.r1 ; g2 = ~q.r2 ; A1 = C(g1, A0) ; A2 = C(g2, A0).
    Stage k's r1 is stage k-1's R0 (stage 1: in0), r2 = in_k; the last stage's A0 is z.ack, stage k's A0 is stage k+1's A1.
    index = the largest k with won[k] = g2[k] | in_k.ack, else 0.  Output data = (in_index.data, index)."""
    kind = "amerge"

    def __init__(self, name, ins, out, cmerge=False):
        super().__init__(name, ins, [out])
        self.n = len(ins)
        self.cmerge = cmerge

    def mkvars(self):
        self.q = [None] + [self.net.var(self, f"{self.name}.q{k}", init=1) for k in range(1, self.n)]
        self.a1 = [None] + [self.net.var(self, f"{self.name}.A1_{k}") for k in range(1, self.n)]
        self.a2 = [None] + [self.net.var(self, f"{self.name}.A2_{k}") for k in range(1, self.n)]
        self.gates = self.q[1:] + self.a1[1:] + self.a2[1:]

    def r1(self, k, S, V):
        return req(self.ins[0], S, V) if k == 1 else self.R0(k - 1, S, V)

    def r2(self, k, S, V):
        return req(self.ins[k], S, V)

    def R0(self, k, S, V):
        return self.r1(k, S, V) if S[self.q[k]] else self.r2(k, S, V)

    def A0(self, k, S, V):
        return ack(self.outs[0], S, V) if k == self.n - 1 else S[self.a1[k + 1]]

    def r1deps(self, k):
        return rdeps(self.ins[0]) if k == 1 else self.R0deps(k - 1)

    def R0deps(self, k):
        return {self.q[k]} | self.r1deps(k) | rdeps(self.ins[k])

    def A0deps(self, k):
        return adeps(self.outs[0]) if k == self.n - 1 else {self.a1[k + 1]}

    def oreq(self, k, S, V):
        # z_req is R0 through the cell's matched delay (bundled data): it rises only once the index it announces is
        # settled, i.e. no acknowledge of a previous winner (won[k] = g2[k] | A2[k]) is still high for a non-winner.
        if not self.R0(self.n - 1, S, V):
            return 0
        w = self.route(S, V)
        for kk in range(1, self.n):
            if kk != w and S[self.a2[kk]]:
                return 0
        return 1

    def oreq_deps(self, k):
        return self.R0deps(self.n - 1) | set(self.a2[1:])

    def iack(self, k, S, V):
        return S[self.a1[1]] if k == 0 else S[self.a2[k]]

    def iack_deps(self, k):
        return {self.a1[1]} if k == 0 else {self.a2[k]}

    def index(self, S, V):
        for k in range(self.n - 1, 0, -1):
            g2 = (not S[self.q[k]]) and self.r2(k, S, V)
            if g2 or S[self.a2[k]]:
                return k
        return 0

    def odata(self, k, S, V):
        i = self.index(S, V)
        return (data(self.ins[i], S, V), i)

    def odata_deps(self, k):
        d = set(self.q[1:]) | set(self.a2[1:])
        for i in self.ins:
            d |= ddeps(i) | rdeps(i)
        return d

    def nxt(self, g, S, V):
        for k in range(1, self.n):
            if g == self.q[k]:
                if self.A0(k, S, V):
                    return S[g]
                r1, r2 = self.r1(k, S, V), self.r2(k, S, V)
                if S[g] == 0 and r1 and not r2:
                    return 1
                if S[g] == 1 and r2 and not r1:
                    return 0
                return S[g]
            if g == self.a1[k]:
                g1 = S[self.q[k]] and self.r1(k, S, V)
                return C([g1, self.A0(k, S, V)], S[g])
            if g == self.a2[k]:
                g2 = (not S[self.q[k]]) and self.r2(k, S, V)
                return C([g2, self.A0(k, S, V)], S[g])
        raise KeyError(g)

    def deps(self, g):
        for k in range(1, self.n):
            if g in (self.q[k], self.a1[k], self.a2[k]):
                return {self.q[k]} | self.r1deps(k) | rdeps(self.ins[k]) | self.A0deps(k)
        raise KeyError(g)

    def arb_input_deps(self):
        d = set()
        for k in range(1, self.n):
            d |= self.r1deps(k) | rdeps(self.ins[k]) | self.A0deps(k)
        return d

    def route(self, S, V):
        # the input the arbiter currently / last granted, read off the q's
        k = self.n - 1
        while k >= 1:
            if not S[self.q[k]]:
                return k
            k -= 1
        return 0


class Split(Cell):
    """control_merge's fork after the arbiter (or olink): out0 = result, out1 = index (data projections)."""
    kind = "fork"

    def mkvars(self):
        self.a = self.net.var(self, self.name + ".ack")
        self.gates = [self.a]

    oreq = Fork.oreq
    iack = Fork.iack
    oreq_deps = Fork.oreq_deps
    iack_deps = Fork.iack_deps
    nxt = Fork.nxt
    deps = Fork.deps

    def odata(self, k, S, V):
        v = data(self.ins[0], S, V)
        if v is None:
            return None
        return v[0] if k == 0 else v[1]

    def odata_deps(self, k):
        return ddeps(self.ins[0])


class Src(Cell):
    """bd_src: req = ~ack (a LUT1 gate), data constant 0.  Also an argument's environment source (budget)."""
    kind = "src"
    stage = True

    def __init__(self, name, out, env=False):
        super().__init__(name, [], [out])
        self.env = env

    def mkvars(self):
        self.g = self.net.var(self, self.name)
        self.gates = [self.g]
        if self.env:
            self.cnt = self.net.var(self, self.name + ".sent")

    def oreq(self, k, S, V):
        return S[self.g]

    def oreq_deps(self, k):
        return {self.g}

    def odata(self, k, S, V):
        return None if self.env else 0

    def nxt(self, g, S, V):
        a = ack(self.outs[0], S, V)
        if not self.env:
            return 1 - a
        if S[g] == 0 and not a and S[self.cnt] < self.net.allowed(S):
            return 1
        if S[g] == 1 and a:
            return 0
        return S[g]

    def deps(self, g):
        d = adeps(self.outs[0])
        if self.env:
            d = d | {self.cnt} | set(self.net.recv_vars)
        return d

    def on_fire(self, g, S, V, newbit, choice):
        if self.env and newbit:
            S[self.cnt] += 1


class Snk(Cell):
    """bd_snk: ack = req."""
    kind = "snk"

    def __init__(self, name, i):
        super().__init__(name, [i], [])

    def iack(self, k, S, V):
        return req(self.ins[0], S, V)

    def iack_deps(self, k):
        return rdeps(self.ins[0])


class EnvSnk(Cell):
    """A result port's environment: ack follows req (a gate); counts tokens."""
    kind = "envsnk"
    stage = True

    def __init__(self, name, i):
        super().__init__(name, [i], [])

    def mkvars(self):
        self.g = self.net.var(self, self.name)
        self.cnt = self.net.var(self, self.name + ".recv")
        self.gates = [self.g]
        self.net.recv_vars.append(self.cnt)

    def iack(self, k, S, V):
        return S[self.g]

    def iack_deps(self, k):
        return {self.g}

    def nxt(self, g, S, V):
        return req(self.ins[0], S, V)

    def deps(self, g):
        return rdeps(self.ins[0])

    def on_fire(self, g, S, V, newbit, choice):
        if newbit:
            S[self.cnt] = min(S[self.cnt] + 1, self.net.ninv + 1)


class MemStation(Cell):
    """bdc_load / bdc_store (bdc/mem.py): joined = C(c?, a, d?); done' = joined.(p_ack + done); hold' = z_ack + hold.p_ack
    (0x00EA); p_req = joined.~done; z_req = done; operand acks = hold.  A store's z with no consumer is tied (ack = req)."""
    kind = "mem"

    def __init__(self, name, ins, out):
        super().__init__(name, ins, [out] if out is not None else [])
        self.port = None
        self.slot = 0

    def mkvars(self):
        self.jn = self.net.var(self, self.name + ".joined")
        self.dn = self.net.var(self, self.name + ".done")
        self.hd = self.net.var(self, self.name + ".hold")
        self.gates = [self.jn, self.dn, self.hd]

    def zack(self, S, V):
        return ack(self.outs[0], S, V) if self.outs else S[self.dn]

    def zackdeps(self):
        return adeps(self.outs[0]) if self.outs else {self.dn}

    def preq(self, S):
        return S[self.jn] and not S[self.dn]

    def oreq(self, k, S, V):
        return S[self.dn]

    def oreq_deps(self, k):
        return {self.dn}

    def iack(self, k, S, V):
        return S[self.hd]

    def iack_deps(self, k):
        return {self.hd}

    def odata(self, k, S, V):
        return None

    def nxt(self, g, S, V):
        if g == self.jn:
            return C([req(i, S, V) for i in self.ins], S[g])
        pa = self.port.pack(self.slot, S)
        if g == self.dn:
            return int(bool(S[self.jn] and (pa or S[self.dn])))
        return int(bool(self.zack(S, V) or (S[self.hd] and pa)))

    def deps(self, g):
        if g == self.jn:
            d = set()
            for i in self.ins:
                d |= rdeps(i)
            return d
        pd = self.port.packdeps(self.slot)
        if g == self.dn:
            return {self.jn, self.dn} | pd
        return {self.hd} | pd | self.zackdeps()


class MemPort(Cell):
    """bdc_memport: unarbitrated, ram' = OR of the slots' p_req and every slot reads p_ack = ram; arbitrated (2 slots):
    a bd_arbiter (r1, r2 = the slots' p_req, A0 = ram) in front, ram' = R0, slot acks A1 / A2."""
    kind = "memport"

    def __init__(self, name, stations, arb):
        super().__init__(name, [], [])
        self.st, self.arb = stations, arb
        for k, s in enumerate(stations):
            s.port, s.slot = self, k

    def mkvars(self):
        self.ram = self.net.var(self, self.name + ".ram")
        self.gates = [self.ram]
        if self.arb:
            self.q = self.net.var(self, self.name + ".q", init=1)
            self.a1 = self.net.var(self, self.name + ".A1")
            self.a2 = self.net.var(self, self.name + ".A2")
            self.gates += [self.q, self.a1, self.a2]

    def pack(self, k, S):
        if not self.arb:
            return S[self.ram]
        return S[self.a1] if k == 0 else S[self.a2]

    def packdeps(self, k):
        if not self.arb:
            return {self.ram}
        return {self.a1} if k == 0 else {self.a2}

    def R0(self, S):
        r1, r2 = self.st[0].preq(S), self.st[1].preq(S)
        return r1 if S[self.q] else r2

    def nxt(self, g, S, V):
        if not self.arb:
            return int(any(s.preq(S) for s in self.st))
        r1, r2 = self.st[0].preq(S), self.st[1].preq(S)
        A0 = S[self.ram]
        if g == self.ram:
            return int(bool(self.R0(S)))
        if g == self.q:
            if A0:
                return S[g]
            if S[g] == 0 and r1 and not r2:
                return 1
            if S[g] == 1 and r2 and not r1:
                return 0
            return S[g]
        if g == self.a1:
            return C([S[self.q] and r1, A0], S[g])
        return C([(not S[self.q]) and r2, A0], S[g])

    def deps(self, g):
        d = set()
        for s in self.st:
            d |= {s.jn, s.dn}
        d.add(self.ram)
        if self.arb:
            d.add(self.q)
        return d

    def arb_input_deps(self):
        return self.deps(self.ram) if self.arb else set()


# ------------------------------------------------------------------------------------------------- design -> netlist
MASKOPS = {"andi": lambda a, b: a & b, "ori": lambda a, b: a | b, "xori": lambda a, b: a ^ b}
PASS_OPS = ("br", "extui", "extsi", "trunci", "buffer")
COMPUTE = ("cmpi", "addi", "subi", "muli", "andi", "ori", "xori", "shli", "shrsi", "shrui", "select", "divsi",
           "divui", "remsi", "remui", "cmpf", "addf", "subf", "mulf", "maxsi", "minsi", "maxui", "minui", "extf")


def const_val(node):
    v = node.attrs.get("value")
    raw = getattr(v, "value", v)
    if isinstance(raw, bool):
        return int(raw)
    if isinstance(raw, str):
        if raw == "true":
            return 1
        if raw == "false":
            return 0
    if isinstance(raw, int):
        return raw
    return None


def op_fn(op, width):
    mask = (1 << max(width, 1)) - 1
    if op in MASKOPS:
        f = MASKOPS[op]
        return lambda xs: None if xs[0] is None or xs[1] is None else f(xs[0], xs[1]) & mask
    if op == "select":
        return lambda xs: None if xs[0] is None else (xs[1] if (xs[0] & 1) else xs[2])
    return lambda xs: None


def build(path, ninv):
    func = [f for f in parse.parse_module(open(path).read(), filename=path) if not f.is_declaration][0]
    e = emit.Emitter(func)
    nodes = func.nodes
    net = Net()
    net.ninv = ninv
    net.recv_vars = []
    net.func, net.e = func, e
    fus = e.fusion
    dead = set(fus.dead_values) if fus else set()
    prod_ch, cons_ch = {}, {}

    def ctl(ssa):
        return e.is_control(ssa) if ssa in e.ch else True

    def chan(ssa):
        if ssa in prod_ch:
            return
        if ssa in dead or ssa in e.mem_absorbed:
            raise ModelError(f"reference to a dead channel {ssa}")
        p = net.ch(ssa + ".u" if ssa in e.linked else ssa, ctl(ssa))
        prod_ch[ssa] = p
        cur = p
        if ssa in e.linked:
            n = e.depth.get(ssa, 1)
            for k in range(n):
                nxt_ = net.ch(f"{ssa}.s{k + 1}" if k < n - 1 else ssa, ctl(ssa))
                net.add(Stage(f"ulink_{emit.vname(ssa)}[{k}]", [cur], [nxt_]))
                cur = nxt_
        cons_ch[ssa] = cur

    def P(ssa):
        chan(ssa)
        return prod_ch[ssa]

    def Q(ssa):
        chan(ssa)
        return cons_ch[ssa]

    def width(ssa):
        return e.width(ssa) if ssa in e.ch else 0

    # arguments
    for arg in func.args:
        if arg.ssa_name in e.memrefs or not arg.ssa_name:
            continue
        net.add(Src(f"env_{arg.name}", P(arg.ssa_name), env=True))
    net.src_cells = [c for c in net.cells if isinstance(c, Src) and c.env]

    mem_cells = {}
    for i, node in enumerate(nodes):
        if fus is not None and i in fus.skip:
            continue
        inst = emit.instname(node, i)
        op = node.op
        if fus is not None and i in fus.anchor_region:
            reg = fus.anchor_region[i]
            z = nodes[reg.anchor].results[0]
            ext = list(reg.ext_inputs)

            def fused_fn(xs, reg=reg):
                vals = {}
                for m in reg.node_ids:
                    n = nodes[m]
                    chans = emit._FUSABLE_CHANS[n.op]
                    args = {}
                    for port in chans:
                        kind, v = reg.ref[(m, port)]
                        args[port] = v if kind == "const" else (xs[v] if kind == "ext" else vals.get(v))
                    order = ["s", "a", "b"] if n.op == "select" else ["a", "b"]
                    w = width(n.results[0]) or 1
                    vals[m] = op_fn(n.op, w)([args[p] for p in order])
                return vals[reg.anchor]
            net.add(Join(inst, [Q(x) for x in ext], P(z), fn=fused_fn, choice=width(z) == 1))
            continue
        ops, res = node.operands, node.results
        if op in ("fork", "lazy_fork"):
            outs = []
            for r in res:
                if emit.vname(r) in emit.FORK_OUT_LINK:
                    f = net.ch(r + ".f", ctl(r))
                    net.add(Stage(f"ulink_{emit.vname(r)}_folink", [f], [P(r)]))
                    outs.append(f)
                else:
                    outs.append(P(r))
            net.add(Fork(inst, [Q(ops[0])], outs))
        elif op == "join":
            net.add(Join(inst, [Q(o) for o in ops], P(res[0])))
        elif op == "cond_br":
            net.add(Steer(inst, Q(ops[0]), Q(ops[1]), P(res[0]), P(res[1])))
        elif op == "mux":
            net.add(Mux(inst, Q(ops[0]), [Q(o) for o in ops[1:]], P(res[0])))
        elif op == "merge":
            if len(ops) == 1:
                net.add(Wire(inst, Q(ops[0]), P(res[0]), lambda d: d()))
            else:
                m = net.ch(inst + ".z")
                net.add(AMerge(inst, [Q(o) for o in ops], m))
                net.add(Wire(inst + ".dat", m, P(res[0]), lambda d: (lambda v: None if v is None else v[0])(d())))
        elif op == "control_merge":
            r, ix = res
            if len(ops) == 1:
                a = net.ch(inst + ".a")
                net.add(Wire(inst + ".tag", Q(ops[0]), a, lambda d: (d(), 0)))
                net.add(Split(inst, [a], [P(r), P(ix)]))
            else:
                m = net.ch(inst + ".z")
                net.add(AMerge(inst, [Q(o) for o in ops], m, cmerge=True))
                if inst in emit.MERGE_OUT_LINK:
                    m2 = net.ch(inst + ".ol")
                    net.add(Stage(inst + "_olink", [m], [m2]))
                    m = m2
                if inst in emit.MERGE_RES_LINK:
                    rr = net.ch(inst + ".rr")
                    net.add(Split(inst + "_f", [m], [rr, P(ix)]))
                    cur = rr
                    for k in range(emit.MERGE_RES_DEPTH):
                        nx = net.ch(f"{inst}.rl{k}") if k < emit.MERGE_RES_DEPTH - 1 else P(r)
                        net.add(Stage(f"{inst}_rlink[{k}]", [cur], [nx]))
                        cur = nx
                else:
                    net.add(Split(inst + "_f", [m], [P(r), P(ix)]))
        elif op == "constant":
            v = const_val(node)
            if v is None:
                raise ModelError(f"constant {inst}: value {node.attrs.get('value')!r}")
            w = width(res[0])
            v &= (1 << max(w, 1)) - 1
            net.add(Wire(inst, Q(ops[0]), P(res[0]), (lambda v: lambda d: v)(v), fndeps=False))
        elif op == "source":
            net.add(Src(inst, P(res[0])))
        elif op == "sink":
            net.add(Snk(inst, Q(ops[0])))
        elif op in PASS_OPS:
            w = width(res[0])
            if op == "trunci":
                f = (lambda m: lambda d: (lambda v: None if v is None else
                                          (v & m if isinstance(v, int) else None))(d()))((1 << max(w, 1)) - 1)
            else:
                f = (lambda d: (lambda v: v if isinstance(v, int) or v is None else None)(d()))
            net.add(Wire(inst, Q(ops[0]), P(res[0]), f))
        elif op in COMPUTE:
            w = width(res[0])
            net.add(Join(inst, [Q(o) for o in ops], P(res[0]), fn=op_fn(op, w), choice=(w == 1)))
        elif op == "load":
            mem_cells[res[0]] = net.add(MemStation(inst, [Q(ops[0])], P(res[1])))
        elif op == "store":
            info = e.accessor_info[res[0]]
            done = res[2] if len(res) == 3 else None
            mem_cells[res[0]] = (inst, [Q(ops[0]), Q(ops[1])], done, info)
        elif op == "mem_controller":
            pass   # after the loop (stations first)
        elif op == "end":
            pass
        else:
            raise ModelError(f"op {op!r} ({inst}) not modelled")
    # stores (their z may chain to the second accessor's c token) and controllers
    for memend, info in e.mc_info.items():
        stations = []
        tok = None
        for k, (kind, addr_res) in enumerate(info["accessors"]):
            ai = e.accessor_info[addr_res]
            if kind == "store":
                inst, ins, done, _ = mem_cells[addr_res]
                if "z_req_net" in ai:
                    tok = net.ch(info["inst"] + ".tok")
                    out = tok
                elif done is not None:
                    out = P(done)
                else:
                    out = None
                st = net.add(MemStation(inst, ins, out))
                mem_cells[addr_res] = st
            else:
                st = mem_cells[addr_res]
            if ai["seq"]:
                if tok is None:
                    raise ModelError("seq accessor without a token")
                st.ins.insert(0, tok)
                tok.cons, tok.cport = st, 0
                for kk, c in enumerate(st.ins):
                    c.cport = kk
            stations.append(st)
        net.add(MemPort(info["inst"] + "_uport", stations, info["arb"]))
        for k, c in enumerate(info.get("counts", ())):
            net.add(Snk(f"{info['inst']}_ucount{k}", Q(c)))
        h = net.ch(info["inst"] + "_started", True)
        net.add(Stage(info["inst"] + "_uhold", [Q(info["memstart"])], [h]))
        net.add(Join(info["inst"] + "_uend", [Q(info["ctrlend"]), h], P(memend)))
    # end
    endn = [n for n in nodes if n.op == "end"][0]
    plan = emit.call_join_plan(func, endn) if emit.CALL_JOIN else None
    base = [r.name for r in func.results]
    port = {}
    tied, joined = plan if plan is not None else ([], [])
    for t in tied:
        cp = [net.ch(f"end_{base[t]}_c{j}", True) for j in range(len(joined))]
        po = net.ch(f"port_{base[t]}", True)
        net.add(Fork(f"end_ufork_{base[t]}", [Q(endn.operands[t])], [po] + cp))
        port[t] = po
        for j in range(len(joined)):
            pass
    for j, i in enumerate(joined):
        cps = []
        for t in tied:
            f = [c for c in net.chs if c.name == f"end_{base[t]}_c{j}"][0]
            cps.append(f)
        po = net.ch(f"port_{base[i]}")
        net.add(Join(f"end_ujoin_{base[i]}", cps + [Q(endn.operands[i])], po,
                     fn=(lambda xs: xs[-1])))
        port[i] = po
    skip = set(joined) | set(tied)
    if e.store_plan:
        stends = {m for m, inf in e.mc_info.items() if any(k == "store" for k, _ in inf["accessors"])}
        sel = [i for i, s_ in enumerate(endn.operands) if not e.is_control(s_) or s_ in stends]
        if len(sel) >= 2:
            a = net.ch("end_all")
            net.add(Join("end_ujoin", [Q(endn.operands[i]) for i in sel], a))
            outs = [net.ch(f"port_{base[i]}") for i in sel]
            net.add(Fork("end_ufork", [a], outs))
            for i, o in zip(sel, outs):
                port[i] = o
            skip.update(sel)
    for i, s_ in enumerate(endn.operands):
        if i not in skip:
            port[i] = Q(s_)
    for i in range(len(func.results)):
        net.add(EnvSnk(f"env_{base[i]}", port[i]))
    # every channel must be connected at both ends
    for c in net.chs:
        if c.prod is None or c.cons is None:
            raise ModelError(f"channel {c.name}: producer {c.prod and c.prod.name}, consumer {c.cons and c.cons.name}")
    net.finish()
    return net


def _allowed(net, S):
    if not net.recv_vars:
        return net.ninv
    return min(net.ninv, min(S[v] for v in net.recv_vars) + 1)


def _finish(net):
    net.allowed = lambda S: _allowed(net, S)
    net.gate_cell = {}
    for c in net.cells:
        for g in c.gates:
            net.gate_cell[g] = c
    net.gdeps = {}
    fan = {}
    for g, c in net.gate_cell.items():
        d = c.deps(g) | {g}
        net.gdeps[g] = d
        for v in d:
            fan.setdefault(v, set()).add(g)
    net.fan = {v: sorted(gs) for v, gs in fan.items()}
    # arbiter-related gates: arbiter state and anything that drives an arbiter input
    dang = set()
    for c in net.cells:
        if isinstance(c, AMerge):
            dang |= set(c.gates) | c.arb_input_deps()
        if isinstance(c, MemPort) and c.arb:
            dang |= set(c.gates) | c.arb_input_deps()
    net.dang = dang
    net.gates = sorted(net.gate_cell)
    net.tokgates = sorted(g for g, c in net.gate_cell.items() if isinstance(c, (Stage, Fork, Join, Steer, Mux, Split)))
    net.vhold = sorted({g for g, c in net.gate_cell.items() if isinstance(c, (Stage, Join))})


Net.finish = _finish


# ---------------------------------------------------------------------------------------------------------- search
class Search:
    def __init__(self, net, max_states, max_chain=2_000_000):
        self.net = net
        self.max_states = max_states
        self.max_chain = max_chain
        self.hazards = {}
        self.residue = 0
        self.overflow = 0
        self.residue_example = None
        self.samples = {}      # mode text -> (S, V), first branch state seen in that routing mode
        self.max_samples = 4

    def excited(self, S, V, g):
        c = self.net.gate_cell[g]
        return c.nxt(g, S, V) != S[g]

    def fire(self, S, V, g, choice, exc):
        net = self.net
        c = net.gate_cell[g]
        nb = 1 - S[g]
        before = [h for h in net.fan.get(g, ()) if h != g and h in exc]
        c.on_fire(g, S, V, nb, choice)
        S[g] = nb
        changed = [g]
        if isinstance(c, (Src, EnvSnk)) and hasattr(c, "cnt"):
            changed.append(c.cnt)
        for v in changed:
            for h in net.fan.get(v, ()):
                if self.excited(S, V, h):
                    exc.add(h)
                else:
                    if h in exc and h != g and h in before and h not in net.dang:
                        self.hazards[(net.varname[g], net.varname[h])] = self.hazards.get(
                            (net.varname[g], net.varname[h]), 0) + 1
                    exc.discard(h)
        exc.discard(g)
        if self.excited(S, V, g):
            exc.add(g)

    def pack(self, S, V, k):
        return (bytes(S), tuple(V[i] for i in self.net.vhold), k)

    def unpack(self, t):
        S = list(t[0])
        V = [None] * self.net.nvar
        for i, v in zip(self.net.vhold, t[1]):
            V[i] = v
        exc = {g for g in self.net.gates if self.excited(S, V, g)}
        return S, V, exc, t[2]

    def key(self, S, V):
        h = hashlib.blake2b(bytes(S) if max(S) < 256 else repr(S).encode(), digest_size=16)
        h.update(repr(tuple(V[i] for i in self.net.vhold)).encode())
        return h.digest()

    def run(self):
        net = self.net
        S0 = list(net.init)
        V0 = [None] * net.nvar
        exc0 = {g for g in net.gates if self.excited(S0, V0, g)}
        seen = {}
        parent = {}
        q = deque()
        k0 = self.key(S0, V0)
        seen[k0] = None
        q.append(self.pack(S0, V0, k0))
        deadlocks = []
        nfired = 0
        finished = 0
        while q:
            S, V, exc, k = self.unpack(q.popleft())
            # deterministic closure: fire persistent, non-arbiter, choice-free gates in index order
            chain = 0
            trail = []
            while True:
                det = None
                ch = None
                for g in sorted(exc):
                    if g in net.dang:
                        continue
                    cs = net.gate_cell[g].choices(g, S, V)
                    if cs is None:
                        det = g
                        break
                    if ch is None:
                        ch = (g, cs)
                if det is None:
                    break
                self.fire(S, V, det, None, exc)
                nfired += 1
                chain += 1
                if chain > self.max_chain:
                    return {"verdict": "LIVELOCK-DET", "states": len(seen), "fired": nfired}
            if ch is not None:
                succ = [(ch[0], v) for v in ch[1]]
                if len(self.samples) < self.max_samples:
                    try:
                        mt = mode_text(net, S, V)
                    except ModelError:
                        mt = None
                    if mt is not None and mt not in self.samples:
                        self.samples[mt] = (list(S), list(V), net.varname[ch[0]])
            else:
                succ = []
                for g in sorted(exc):
                    cs = net.gate_cell[g].choices(g, S, V)
                    for v in (cs if cs is not None else [None]):
                        succ.append((g, v))
            if not succ:
                done = all(S[v] >= net.ninv for v in net.recv_vars) if net.recv_vars else True
                over = any(S[v] > net.ninv for v in net.recv_vars)
                if over:
                    self.overflow += 1
                if done:
                    finished += 1
                    if any(S[g] != net.init[g] for g in net.tokgates):
                        self.residue += 1
                        if self.residue_example is None:
                            self.residue_example = [net.varname[g] for g in net.tokgates if S[g] != net.init[g]][:6]
                else:
                    deadlocks.append((S, V, k))
                    if len(deadlocks) >= 1:
                        break
                continue
            for (g, v) in succ:
                S2, V2, e2 = list(S), list(V), set(exc)
                self.fire(S2, V2, g, v, e2)
                k2 = self.key(S2, V2)
                if k2 in seen:
                    continue
                seen[k2] = (k, net.varname[g], v)
                if len(seen) > self.max_states:
                    return {"verdict": "BLOWUP", "states": len(seen), "fired": nfired}
                q.append(self.pack(S2, V2, k2))
        res = {"states": len(seen), "fired": nfired, "finished": finished}
        if deadlocks:
            S, V, k = deadlocks[0]
            res["verdict"] = "DEADLOCK"
            res["S"], res["V"] = S, V
            res["trace"] = self.trace(seen, k)
        else:
            res["verdict"] = "LIVE"
        return res

    def trace(self, seen, k):
        steps = []
        while seen.get(k) is not None:
            pk, g, v = seen[k]
            steps.append((g, v))
            k = pk
        steps.reverse()
        return steps


# ------------------------------------------------------------------------------------------- stage-level projection
def stage_graph(net, S, V):
    """Stages (Muller stages, sources, result sinks) and edges p -> t: p's output reaches t's input through rendezvous
    cells under the routing read off the state (steer: its condition's current value; mux: its select's; arbiter: its q)."""
    stages = [c for c in net.cells if c.stage]
    idx = {id(c): k for k, c in enumerate(stages)}
    edges = set()
    undet = []

    def back(ch, t, seen):
        c, port = ch.prod, ch.pport
        if c.stage:
            edges.add((idx[id(c)], t))
            return
        key = (id(c), port)
        if key in seen:
            return
        seen.add(key)
        if isinstance(c, (Wire, Fork, Split)):
            back(c.ins[0], t, seen)
        elif isinstance(c, Join) or isinstance(c, MemStation):
            for i in c.ins:
                back(i, t, seen)
        elif isinstance(c, Steer):
            r = c.route(S, V)
            if r is None:
                undet.append(c.name)
                return
            if r == port:
                back(c.ins[0], t, seen)
                back(c.ins[1], t, seen)
        elif isinstance(c, Mux):
            r = c.route(S, V)
            if r is None or not 0 <= r < c.n:
                undet.append(c.name)
                return
            back(c.ins[0], t, seen)
            back(c.ins[1 + r], t, seen)
        elif isinstance(c, AMerge):
            back(c.ins[c.route(S, V)], t, seen)
        else:
            raise ModelError(f"stage graph: {c.kind}")

    for t, c in enumerate(stages):
        for i in c.ins:
            back(i, t, set())
    x = [S[c.gates[0]] for c in stages]
    return stages, sorted(edges), x, sorted(set(undet))


def z_cycle(n, edges, x):
    """Z(x) = {p->t : x_p == x_t} u {t->p : x_p != x_t}; return a cycle (list of stages) or None."""
    adj = [[] for _ in range(n)]
    for p, t in edges:
        if x[p] == x[t]:
            adj[p].append(t)
        else:
            adj[t].append(p)
    color = [0] * n
    stack_pos = {}
    for s0 in range(n):
        if color[s0]:
            continue
        path = [s0]
        it = [iter(adj[s0])]
        color[s0] = 1
        stack_pos[s0] = 0
        while path:
            try:
                w = next(it[-1])
            except StopIteration:
                v = path.pop()
                it.pop()
                color[v] = 2
                stack_pos.pop(v, None)
                continue
            if color[w] == 1:
                return path[stack_pos[w]:]
            if color[w] == 0:
                color[w] = 1
                stack_pos[w] = len(path)
                path.append(w)
                it.append(iter(adj[w]))
    return None


def mode_text(net, S, V):
    parts = []
    for c in net.cells:
        if isinstance(c, Steer):
            r = c.route(S, V)
            parts.append(f"{c.name}={'?' if r is None else 'TF'[1 - r]}")
        elif isinstance(c, Mux):
            r = c.route(S, V)
            parts.append(f"{c.name}={'?' if r is None else r}")
        elif isinstance(c, AMerge):
            parts.append(f"{c.name}={c.route(S, V)}")
    return " ".join(parts)


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("mlir")
    ap.add_argument("--inv", type=int, default=1)
    ap.add_argument("--max-states", type=int, default=400000)
    ap.add_argument("--json-dir")
    ap.add_argument("--tag", default="")
    ap.add_argument("--pattern", action="append", default=[],
                    help="CELL=BITS: that compute cell's nondeterministic bit follows BITS cyclically (e.g. a fixed trip "
                         "count), instead of branching")
    ap.add_argument("--out", help="write the result as one JSON line here")
    a = ap.parse_args()
    import resource
    lim = int(float(os.environ.get("LIVE_MEM_GB", "2.5")) * 2**30)
    resource.setrlimit(resource.RLIMIT_AS, (lim, lim))
    t0 = time.time()
    out = {"mlir": a.mlir, "inv": a.inv}
    try:
        net = build(a.mlir, a.inv)
    except emit.EmitError as ex:
        out.update(verdict="REFUSED", error=str(ex).splitlines()[0][:300])
        return finish(a, out)
    except ModelError as ex:
        out.update(verdict="MODEL-ERROR", error=str(ex)[:300])
        return finish(a, out)
    stages = [c for c in net.cells if c.stage and isinstance(c, Stage)]
    for pa in a.pattern:
        nm, _, bits = pa.partition("=")
        c = [c for c in net.cells if c.name == nm][0]
        c.pattern = [int(b) for b in bits]
        c.pctr = net.var(c, nm + ".pattern")
    out["stages"] = len(stages)
    out["gates"] = len(net.gates)
    out["token_floor"] = [(f"ulink_{emit.vname(v)}", n) for v, n in net.e.token_floor]
    srch = Search(net, a.max_states)
    try:
        res = srch.run()
    except MemoryError:
        res = {"verdict": "BLOWUP-MEM", "states": -1, "fired": -1}
    except ModelError as ex:
        out.update(verdict="MODEL-ERROR", error=str(ex)[:300])
        return finish(a, out)
    out["verdict"] = res["verdict"]
    out["states"] = res["states"]
    out["fired"] = res["fired"]
    out["hazards"] = len(srch.hazards)
    out["hazard_examples"] = [f"{k[0]} disables {k[1]}" for k in list(srch.hazards)[:3]]
    out["residue"] = srch.residue
    out["residue_example"] = srch.residue_example
    zs = []
    for k, (mt, (S, V, at)) in enumerate(srch.samples.items()):
        sts, edges, x, undet = stage_graph(net, S, V)
        cyc = z_cycle(len(sts), edges, x)
        zs.append(None if cyc is None else len(cyc))
        if a.json_dir:
            dump(a, net, sts, edges, x, cyc, f"s{k}", f"branch state before {at}; " + mt)
    out["samples_z"] = zs
    out["overflow"] = srch.overflow
    out["secs"] = round(time.time() - t0, 1)
    if res["verdict"] == "DEADLOCK":
        S, V = res["S"], res["V"]
        tr = res["trace"]
        choices = [f"{g}={v}" for g, v in tr if v is not None]
        arbs = [g for g, v in tr if v is None]
        out["trace_choices"] = choices
        out["trace_len"] = len(tr)
        out["trace_arb"] = len(arbs)
        sts, edges, x, undet = stage_graph(net, S, V)
        cyc = z_cycle(len(sts), edges, x)
        out["trap"] = None if cyc is None else [sts[k].name for k in cyc]
        out["undetermined_routes"] = undet
        out["high_stages"] = [sts[k].name for k in range(len(sts)) if x[k] and isinstance(sts[k], Stage)]
        out["sent"] = {c.name: S[c.cnt] for c in net.src_cells}
        out["recv"] = {net.varname[v]: S[v] for v in net.recv_vars}
        if a.json_dir:
            dump(a, net, sts, edges, x, cyc, "deadlock", mode_text(net, S, V))
    return finish(a, out)


def dump(a, net, sts, edges, x, cyc, which, mode):
    os.makedirs(a.json_dir, exist_ok=True)
    fn = os.path.join(a.json_dir, f"{a.tag}.{which}.json")
    parts = a.tag.split(".")
    json.dump({"fixture": net.func.name, "tag": a.tag, "flow": parts[1] if len(parts) > 1 else "",
               "floor": parts[2] if len(parts) > 2 else "", "mode": f"{which}: {mode}", "n": len(sts),
               "names": [s.name for s in sts], "edges": [list(e) for e in edges], "x": x,
               "trap": cyc}, open(fn, "w"))


def finish(a, out):
    s = json.dumps(out)
    if a.out:
        with open(a.out, "a") as f:
            f.write(s + "\n")
    print(s)
    return 0


if __name__ == "__main__":
    sys.exit(main())
