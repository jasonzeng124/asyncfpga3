#!/usr/bin/env python3
"""dynamatic_est.py KERNEL [VECTORS.hex] -- Dynamatic's cycles for a kernel, and an ESTIMATED ns per iteration.

Dynamatic's RTL exporter (export-rtl) is not in the owner's build, so Dynamatic's own figure cannot be routed here.
This makes the next best thing from Dynamatic's own tools and models (PROGRAM "A benchmark suite for the compiler"):

  1. Buffers: Dynamatic's own pass, `dynamatic-opt --handshake-set-buffering-properties=version=fpga20
     --handshake-place-buffers=algorithm=on-merges timing-models=components.json` then `--handshake-canonicalize
     --handshake-hoist-ext-instances` (compile.sh's on-merges branch and its export step; no MILP, no Gurobi) on the
     kernel's fixture build/frontend/<k>/comp/handshake_transformed.mlir.
  2. Cycles (MEASURED, by simulation): a cycle-level model of the buffered circuit, unit by unit transcribed from
     Dynamatic's Verilog library (dynamatic/data/verilog: eager fork, lazy fork, join, merge, mux, control_merge with
     its internal TEHB + fork, cond_br, the antitoken select, oehb / tehb buffers, muli's 4-stage and div/rem's
     35-stage pipelines, load's two TEHBs, mem_controller's read / write arbiters and mc_control).  Every cycle the
     valid / ready / data nets are settled to their fixed point and then the registers clock.  The environment drives
     every argument and start token from cycle 0 and takes every result at once (ready = 1).  Cycles per call = the
     cycle in which the last `end` operand is taken, counted from 1.  The results are checked against the kernel's C,
     compiled with gcc and run on the same arguments: a cycle count from a wrong answer is not reported as a number.
  3. Period (ESTIMATE): the longest combinational path between registers of the buffered circuit in Dynamatic's own
     timing model (components.json: per-unit data / valid / ready delays and the mixed valid->ready, condition->valid,
     condition->ready, valid->data arcs that its buffer placement uses), scaled by ONE factor fitted on the three
     kernels whose Dynamatic period was routed in 2026-08 (xorshift 12.73, collatz 14.05, collatz64 17.84 ns,
     research/data/dynamatic_ref/README.md).  The fit and its leave-one-out error are printed by --calibrate.

    research/tools/suite/dynamatic_est.py xorshift research/data/eventgraph/gate/xor19.hex
    research/tools/suite/dynamatic_est.py gcd                     # no vectors: the call in the C's own main()
    research/tools/suite/dynamatic_est.py --calibrate             # the period fit on the three routed kernels
    research/tools/suite/dynamatic_est.py --table K1 K2 ...       # the markdown table (README)

Vectors: one call per line, hex words (research/data/eventgraph/gate/ipow17.hex): the kernel's scalar arguments in
order, one word per 32 bits (a 64-bit argument takes two, low word first); missing words are 0, extra words ignored.
The bench's domain masks (cells/hw/gen_bench.py DOMAIN_RESTRICTIONS) are applied to the words as the bench applies
them, so both sides compute the same calls.  Without a vector file the call is the one in the C's own main()
(CALL_KERNEL), which is also how arrays get their contents (memory kernels).

What this does NOT capture is printed at the end of every run and written in research/data/suite/dynamatic/README.md.
"""
import argparse
import ast
import collections
import glob
import json
import math
import os
import re
import shutil
import statistics
import subprocess
import sys
import tempfile

REPO = os.path.abspath(os.path.join(os.path.dirname(os.path.abspath(__file__)), "..", "..", ".."))
sys.path.insert(0, os.path.join(REPO, "bdc"))
from hs import parse as hsparse  # noqa: E402

DYN = os.environ.get("DYNAMATIC_DIR") or next(
    (d for d in (os.path.join(REPO, "dynamatic"), os.path.expanduser("~/dynamatic"), "/home/afpga/dynamatic")
     if os.path.isfile(os.path.join(d, "build", "bin", "dynamatic-opt"))), os.path.join(REPO, "dynamatic"))
DOPT = os.path.join(DYN, "build", "bin", "dynamatic-opt")
COMPONENTS = os.path.join(DYN, "data", "components.json")

# The three Dynamatic periods that were routed (one route each, nextpnr default seed, 2026-08;
# research/data/dynamatic_ref/README.md).  They calibrate the period.  Kernels are named in this tool here and in
# GATE_VECTORS (where the six original kernels' vectors live, as in suite_one.sh), nowhere else.
MEASURED = {"xorshift": 12.73, "collatz": 14.05, "collatz64": 17.84}

METHOD = ("Dynamatic on-merges buffers (its own dynamatic-opt pass) -> cycle-level simulation of its Verilog units, "
          "answers checked against the C -> cycles; period = longest path in Dynamatic's timing model (components.json) "
          "x a factor fitted on 3 routed kernels (ESTIMATE)")

NOT_CAPTURED = [
    "the period is an ESTIMATE: Dynamatic's pre-synthesis unit delays scaled by one factor fitted on 3 single-seed "
    "routes; nothing of this circuit was synthesised, placed or routed (no LUT packing, no wires, no seed scatter)",
    "on-merges is the only placement here: Dynamatic's MILP placements (fpga20 / fpl22 at a target period) need "
    "Gurobi or CBC and this build has neither ('LLVM ERROR: CBC not installed!'); they give other buffers, fewer "
    "cycles where on-merges serialises a loop on a multi-cycle unit (memory, muli), and other periods",
    "the cycle model is transcribed from the Verilog library in dynamatic/data/verilog of the owner's build; it is "
    "not Dynamatic's own simulation (export-rtl and hls-verifier are not built), so a transcription error would not "
    "show in the answers unless it changed a value",
    "one call per simulation from reset, the environment always ready: no back-to-back calls, no host I/O",
    "LSQ kernels and floating point are not simulated (reported as such)",
    "memory: an ideal 1-cycle BRAM behind Dynamatic's mem_controller; no BRAM mapping or timing",
]


# ----------------------------------------------------------------------------------------------------------------
# Helpers

def mask(w):
    return (1 << w) - 1 if w > 0 else 0


def sext(x, w):
    x &= mask(w)
    return x - (1 << w) if w and x >> (w - 1) else x


class Unsupported(Exception):
    pass


def type_atoms(sig):
    return re.findall(r"<([^<>]*)>", sig)


def width_of(atom):
    """'i32' -> 32, '' -> 0 (control); floats are refused."""
    atom = atom.strip()
    if atom == "":
        return 0
    m = re.fullmatch(r"i(\d+)", atom)
    if m:
        return int(m.group(1))
    raise Unsupported("type <%s>" % atom)


def attr_int(v):
    if isinstance(v, hsparse.TypedLiteral):
        return v.value
    return v


# ----------------------------------------------------------------------------------------------------------------
# Units.  Every unit reads and writes the shared net arrays V (valid), R (ready), D (data), indexed by channel.
# comb() recomputes the nets the unit drives from its inputs and state and returns True if any changed; tick()
# clocks its registers from the settled nets.  Each is a transcription of the named Verilog module.

class Unit:
    kind = "?"
    seq = False  # has registers

    def __init__(self, sim, name, bb, ins, outs):
        self.sim, self.name, self.bb, self.ins, self.outs = sim, name, bb, list(ins), list(outs)
        self.V, self.R, self.D = sim.V, sim.R, sim.D

    def reset(self):
        pass

    def comb(self):
        return False

    def tick(self):
        pass


def _set(arr, i, v):
    if arr[i] != v:
        arr[i] = v
        return True
    return False


class Fork(Unit):
    """handshake/dataless/fork.v + support/eager_fork_register_block.v (eager fork)."""
    kind = "fork"
    seq = True

    def reset(self):
        self.t = [True] * len(self.outs)

    def comb(self):
        V, R, D = self.V, self.R, self.D
        i = self.ins[0]
        iv, d = V[i], D[i]
        ch = False
        stop = False
        for k, o in enumerate(self.outs):
            t = self.t[k]
            nv = t and iv
            if V[o] != nv:
                V[o] = nv
                ch = True
            if D[o] != d:
                D[o] = d
                ch = True
            if t and not R[o]:
                stop = True
        if R[i] == stop:
            R[i] = not stop
            ch = True
        return ch

    def tick(self):
        V, R = self.V, self.R
        keep = [(not R[o]) and t for o, t in zip(self.outs, self.t)]
        bp = V[self.ins[0]] and any(keep)
        self.t = [kp or not bp for kp in keep]


class LazyFork(Unit):
    """handshake/dataless/lazy_fork.v."""
    kind = "lazy_fork"

    def comb(self):
        V, R, D = self.V, self.R, self.D
        i = self.ins[0]
        iv, d = V[i], D[i]
        rs = [R[o] for o in self.outs]
        ch = False
        for k, o in enumerate(self.outs):
            nv = iv and all(r for j, r in enumerate(rs) if j != k)
            ch |= _set(V, o, nv)
            ch |= _set(D, o, d)
        ch |= _set(R, i, all(rs))
        return ch


class Join(Unit):
    """handshake/join.v (join_type): dataless join of N channels."""
    kind = "join"

    def comb(self):
        V, R = self.V, self.R
        o = self.outs[0]
        vs = [V[c] for c in self.ins]
        ch = _set(V, o, all(vs))
        ro = R[o]
        for k, c in enumerate(self.ins):
            ch |= _set(R, c, ro and all(v for j, v in enumerate(vs) if j != k))
        return ch


class Merge(Unit):
    """handshake/merge.v / dataless/merge.v: the lowest-index valid input wins, no internal buffer."""
    kind = "merge"

    def comb(self):
        V, R, D = self.V, self.R, self.D
        o = self.outs[0]
        first = -1
        for k, c in enumerate(self.ins):
            if V[c]:
                first = k
                break
        ch = _set(V, o, first >= 0)
        ch |= _set(D, o, D[self.ins[first if first >= 0 else 0]])
        ro = R[o]
        for k, c in enumerate(self.ins):
            ch |= _set(R, c, k == first and ro)
        return ch


class Mux(Unit):
    """handshake/mux.v.  ins[0] is the index channel."""
    kind = "mux"

    def comb(self):
        V, R, D = self.V, self.R, self.D
        sel, data = self.ins[0], self.ins[1:]
        o = self.outs[0]
        sv_ = V[sel]
        idx = D[sel]
        sv = sv_ and idx < len(data) and V[data[idx]]
        ch = _set(V, o, sv)
        ch |= _set(D, o, D[data[idx]] if sv else D[data[0]])
        ro = R[o]
        for k, c in enumerate(data):
            vc = V[c]
            ch |= _set(R, c, (k == idx and sv_ and ro and vc) or not vc)
        ch |= _set(R, sel, (not sv_) or (sv and ro))
        return ch


class ControlMerge(Unit):
    """handshake/dataless/control_merge.v: merge_dataless -> tehb(index) -> fork_dataless(2) {outs, index}.
    (The data-carrying variant is $fatal in this library; a data cmerge forwards the winner's data the same way.)"""
    kind = "control_merge"
    seq = True

    def reset(self):
        self.full, self.reg, self.t = False, 0, [True, True]

    def comb(self):
        V, R, D = self.V, self.R, self.D
        first = -1
        for k, c in enumerate(self.ins):
            if V[c]:
                first = k
                break
        avail = first >= 0
        tready = not self.full
        ch = False
        for k, c in enumerate(self.ins):
            ch |= _set(R, c, k == first and tready)
        tv = avail or self.full
        tidx = self.reg if self.full else (first if avail else 0)
        o, oi = self.outs
        ch |= _set(V, o, self.t[0] and tv)
        ch |= _set(D, o, D[self.ins[tidx]] if tidx < len(self.ins) else 0)
        ch |= _set(V, oi, self.t[1] and tv)
        ch |= _set(D, oi, tidx)
        self._first, self._tv = first, tv
        return ch

    def tick(self):
        V, R = self.V, self.R
        first = -1
        for k, c in enumerate(self.ins):
            if V[c]:
                first = k
                break
        avail = first >= 0
        tv = avail or self.full
        o, oi = self.outs
        keep = [(not R[o]) and self.t[0], (not R[oi]) and self.t[1]]
        ready_to_fork = not (keep[0] or keep[1])
        if (not self.full) and avail and not ready_to_fork:
            self.reg = first
        self.full = (avail or self.full) and not ready_to_fork
        bp = tv and (keep[0] or keep[1])
        self.t = [kp or not bp for kp in keep]


class CondBr(Unit):
    """handshake/cond_br.v.  ins = [condition, data]; outs = [true, false]."""
    kind = "cond_br"

    def comb(self):
        V, R, D = self.V, self.R, self.D
        c, d = self.ins
        t, f = self.outs
        bv = V[c] and V[d]
        cond = D[c] & 1
        ch = _set(V, t, bool(cond) and bv)
        ch |= _set(V, f, (not cond) and bv)
        dd = D[d]
        ch |= _set(D, t, dd)
        ch |= _set(D, f, dd)
        br = (R[f] and not cond) or (R[t] and bool(cond))
        ch |= _set(R, d, br and V[c])
        ch |= _set(R, c, br and V[d])
        return ch


class Sink(Unit):
    kind = "sink"

    def comb(self):
        return _set(self.R, self.ins[0], True)


class Source(Unit):
    kind = "source"

    def comb(self):
        return _set(self.V, self.outs[0], True)


class Constant(Unit):
    kind = "constant"

    def __init__(self, sim, name, bb, ins, outs, value):
        super().__init__(sim, name, bb, ins, outs)
        self.value = value

    def comb(self):
        V, R, D = self.V, self.R, self.D
        i, o = self.ins[0], self.outs[0]
        ch = _set(V, o, V[i])
        ch |= _set(D, o, self.value)
        ch |= _set(R, i, R[o])
        return ch


class Pass(Unit):
    """br, extsi, extui, trunci, not: one input, one output, combinational."""
    kind = "pass"

    def __init__(self, sim, name, bb, ins, outs, fn, trunc_ready=False):
        super().__init__(sim, name, bb, ins, outs)
        self.fn, self.trunc_ready = fn, trunc_ready

    def comb(self):
        V, R, D = self.V, self.R, self.D
        i, o = self.ins[0], self.outs[0]
        iv = V[i]
        ch = _set(V, o, iv)
        ch |= _set(D, o, self.fn(D[i]))
        # trunci.v: ins_ready = ~ins_valid | outs_ready; the others: ins_ready = outs_ready
        ch |= _set(R, i, ((not iv) or R[o]) if self.trunc_ready else R[o])
        return ch


class Binary(Unit):
    """arith/<op>.v: join_type(2) + a combinational function (addi, subi, andi, ori, xori, shli, shrsi, shrui,
    cmpi)."""
    kind = "binary"

    def __init__(self, sim, name, bb, ins, outs, fn):
        super().__init__(sim, name, bb, ins, outs)
        self.fn = fn

    def comb(self):
        V, R, D = self.V, self.R, self.D
        a, b = self.ins
        o = self.outs[0]
        va, vb = V[a], V[b]
        ch = _set(V, o, va and vb)
        ch |= _set(D, o, self.fn(D[a], D[b]))
        ro = R[o]
        ch |= _set(R, a, ro and vb)
        ch |= _set(R, b, ro and va)
        return ch


class Pipelined(Unit):
    """arith/muli.v (join -> mul_4_stage + delay_buffer(3) -> oehb_dataless; latency 4) and arith/divsi.v, divui.v,
    remsi.v (delay_buffer(34) -> oehb; latency 35): a lock-step pipeline of L stages whose clock enable is the
    output oehb's ready; the data enters with the join's valid and comes out L enables later."""
    kind = "pipelined"
    seq = True

    def __init__(self, sim, name, bb, ins, outs, fn, lat):
        super().__init__(sim, name, bb, ins, outs)
        self.fn, self.lat = fn, lat

    def reset(self):
        self.st = collections.deque([(False, 0)] * self.lat)

    def comb(self):
        V, R, D = self.V, self.R, self.D
        a, b = self.ins
        o = self.outs[0]
        ov, od = self.st[-1]
        ch = _set(V, o, ov)
        ch |= _set(D, o, od)
        ce = (not ov) or R[o]
        ch |= _set(R, a, ce and V[b])
        ch |= _set(R, b, ce and V[a])
        return ch

    def tick(self):
        V, R, D = self.V, self.R, self.D
        a, b = self.ins
        ov = self.st[-1][0]
        if (not ov) or R[self.outs[0]]:
            self.st.pop()
            self.st.appendleft((V[a] and V[b], self.fn(D[a], D[b])))


class Select(Unit):
    """arith/select.v (selector + antitokens).  ins = [condition, trueValue, falseValue]."""
    kind = "select"
    seq = True

    def reset(self):
        self.r0 = self.r1 = False

    def _sig(self):
        V, R, D = self.V, self.R, self.D
        c, tch, fch = self.ins
        cv, cond, tv, fv = V[c], D[c] & 1, V[tch], V[fch]
        ee = cv and ((not cond and fv) or (bool(cond) and tv))
        vi = ee and not (self.r0 or self.r1)
        ro = R[self.outs[0]]
        g0 = (not tv) and vi and ro
        g1 = (not fv) and vi and ro
        return cv, cond, tv, fv, vi, ro, g0, g1

    def comb(self):
        V, R, D = self.V, self.R, self.D
        c, tch, fch = self.ins
        o = self.outs[0]
        cv, cond, tv, fv, vi, ro, g0, g1 = self._sig()
        ch = _set(V, o, vi)
        ch |= _set(D, o, D[tch] if cond else D[fch])
        ch |= _set(R, tch, (not tv) or (vi and ro) or g0 or self.r0)
        ch |= _set(R, fch, (not fv) or (vi and ro) or g1 or self.r1)
        ch |= _set(R, c, (not cv) or (vi and ro))
        return ch

    def tick(self):
        cv, cond, tv, fv, vi, ro, g0, g1 = self._sig()
        self.r0, self.r1 = (not tv) and (g0 or self.r0), (not fv) and (g1 or self.r1)


class Oehb(Unit):
    """handshake/oehb.v = buffer ONE_SLOT_BREAK_DV, 1 slot (dvLatency 1)."""
    kind = "oehb"
    seq = True

    def reset(self):
        self.v, self.d = False, 0

    def comb(self):
        V, R, D = self.V, self.R, self.D
        i, o = self.ins[0], self.outs[0]
        ch = _set(V, o, self.v)
        ch |= _set(D, o, self.d)
        ch |= _set(R, i, (not self.v) or R[o])
        return ch

    def tick(self):
        V, R, D = self.V, self.R, self.D
        i, o = self.ins[0], self.outs[0]
        rin = (not self.v) or R[o]
        if rin and V[i]:
            self.d = D[i]
        self.v = V[i] or ((not R[o]) and self.v)


class Tehb(Unit):
    """handshake/tehb.v = buffer ONE_SLOT_BREAK_R, 1 slot (dvLatency 0)."""
    kind = "tehb"
    seq = True

    def reset(self):
        self.full, self.reg = False, 0

    def comb(self):
        V, R, D = self.V, self.R, self.D
        i, o = self.ins[0], self.outs[0]
        ch = _set(V, o, V[i] or self.full)
        ch |= _set(D, o, self.reg if self.full else D[i])
        ch |= _set(R, i, not self.full)
        return ch

    def tick(self):
        V, R, D = self.V, self.R, self.D
        i, o = self.ins[0], self.outs[0]
        if (not self.full) and V[i] and not R[o]:
            self.reg = D[i]
        self.full = (V[i] or self.full) and not R[o]


class Load(Unit):
    """handshake/load.v: addr_tehb (circuit address -> memory interface) and data_tehb (interface -> circuit).
    ins = [address, data from interface]; outs = [address to interface, data to circuit]."""
    kind = "load"
    seq = True

    def reset(self):
        self.af, self.ar, self.df, self.dr = False, 0, False, 0

    def comb(self):
        V, R, D = self.V, self.R, self.D
        ai, di = self.ins
        ao, do = self.outs
        ch = _set(V, ao, V[ai] or self.af)
        ch |= _set(D, ao, self.ar if self.af else D[ai])
        ch |= _set(R, ai, not self.af)
        ch |= _set(V, do, V[di] or self.df)
        ch |= _set(D, do, self.dr if self.df else D[di])
        ch |= _set(R, di, not self.df)
        return ch

    def tick(self):
        V, R, D = self.V, self.R, self.D
        ai, di = self.ins
        ao, do = self.outs
        if (not self.af) and V[ai] and not R[ao]:
            self.ar = D[ai]
        self.af = (V[ai] or self.af) and not R[ao]
        if (not self.df) and V[di] and not R[do]:
            self.dr = D[di]
        self.df = (V[di] or self.df) and not R[do]


class Store(Unit):
    """handshake/store.v: two wires.  ins = [address, data]; outs = [address to interface, data to interface]."""
    kind = "store"

    def comb(self):
        V, R, D = self.V, self.R, self.D
        ai, di = self.ins
        ao, do = self.outs
        ch = _set(V, ao, V[ai])
        ch |= _set(D, ao, D[ai])
        ch |= _set(R, ai, R[ao])
        ch |= _set(V, do, V[di])
        ch |= _set(D, do, D[di])
        ch |= _set(R, di, R[do])
        return ch


class MemController(Unit):
    """handshake/mem_controller{,_loadless,_storeless}.v + support/mc_support.v: read_memory_arbiter (fixed
    priority, address accepted only when that port's data slot is ready, BRAM data one cycle later),
    write_memory_arbiter (fixed priority over ports with address and data valid), the pending-store counter fed by
    the ctrl channels, and mc_control (memStart / ctrlEnd / memEnd).  The memory is an array with a 1-cycle read
    port (the testbench's BRAM)."""
    kind = "mem_controller"
    seq = True

    def __init__(self, sim, name, bb, mem_start, ctrls, ld_addr, ld_data, st_addr, st_data, ctrl_end, mem_end,
                 memref_arg, size, ewidth):
        ins = [mem_start] + ctrls + ld_addr + st_addr + st_data + [ctrl_end]
        outs = ld_data + [mem_end]
        super().__init__(sim, name, bb, ins, outs)
        self.mem_start, self.ctrls, self.ld_addr, self.ld_data = mem_start, ctrls, ld_addr, ld_data
        self.st_addr, self.st_data, self.ctrl_end, self.mem_end = st_addr, st_data, ctrl_end, mem_end
        self.memref_arg, self.size, self.ewidth = memref_arg, size, ewidth
        self.has_stores = bool(st_addr)

    def reset(self):
        n = len(self.ld_addr)
        self.valid = [False] * n
        self.sel_prev = [False] * n
        self.out_reg = [0] * n
        self.bram_q = 0
        self.counter = 0
        self.running = False
        self.no_more = False
        self.mem = self.sim.memories[self.memref_arg]

    def _ld_sel(self):
        V, R = self.V, self.R
        sel = [False] * len(self.ld_addr)
        for k, (a, d) in enumerate(zip(self.ld_addr, self.ld_data)):
            if V[a] and R[d]:
                sel[k] = True
                break
        return sel

    def _st_sel(self):
        V = self.V
        sel = [False] * len(self.st_addr)
        for k, (a, d) in enumerate(zip(self.st_addr, self.st_data)):
            if V[a] and V[d]:
                sel[k] = True
                break
        return sel

    def _done(self):
        if not self.has_stores:
            return True
        return self.counter == 0 and not any(self.V[c] for c in self.ctrls)

    def comb(self):
        V, R, D = self.V, self.R, self.D
        ch = _set(R, self.mem_start, not self.running)
        for c in self.ctrls:
            ch |= _set(R, c, True)
        sel = self._ld_sel()
        for k, (a, d) in enumerate(zip(self.ld_addr, self.ld_data)):
            ch |= _set(R, a, sel[k])
            ch |= _set(V, d, self.valid[k])
            ch |= _set(D, d, self.bram_q if self.sel_prev[k] else self.out_reg[k])
        ssel = self._st_sel()
        for k, (a, d) in enumerate(zip(self.st_addr, self.st_data)):
            ch |= _set(R, a, ssel[k])
            ch |= _set(R, d, ssel[k])
        ch |= _set(V, self.mem_end, self.no_more and self._done() and self.running)
        ch |= _set(R, self.ctrl_end, not self.no_more)
        return ch

    def tick(self):
        V, R, D = self.V, self.R, self.D
        sel = self._ld_sel()
        ssel = self._st_sel()
        done = self._done()
        for k, d in enumerate(self.ld_data):
            if self.sel_prev[k]:
                self.out_reg[k] = self.bram_q
        for k, d in enumerate(self.ld_data):
            if sel[k]:
                self.valid[k] = True
            elif R[d]:
                self.valid[k] = False
        self.sel_prev = sel
        if any(sel):
            addr = D[self.ld_addr[sel.index(True)]]
            self.bram_q = self.mem[addr] if addr < len(self.mem) else 0
        for c in self.ctrls:
            if V[c]:
                self.counter += sext(D[c], 32)
        if any(ssel):
            k = ssel.index(True)
            addr = D[self.st_addr[k]]
            if addr < len(self.mem):
                self.mem[addr] = D[self.st_data[k]] & mask(self.ewidth)
            self.counter -= 1
            self.sim.stores += 1
        fret = self.no_more and done and R[self.mem_end] and self.running
        if not self.running:
            if V[self.mem_start]:
                self.running = True
        elif fret:
            self.running = False
        if fret:
            self.no_more = False
        elif V[self.ctrl_end]:
            self.no_more = True


# ----------------------------------------------------------------------------------------------------------------
# The circuit: channels from the parsed handshake IR, one unit per op.

CMP = {
    "eq": lambda a, b, w: a == b, "ne": lambda a, b, w: a != b,
    "slt": lambda a, b, w: sext(a, w) < sext(b, w), "sle": lambda a, b, w: sext(a, w) <= sext(b, w),
    "sgt": lambda a, b, w: sext(a, w) > sext(b, w), "sge": lambda a, b, w: sext(a, w) >= sext(b, w),
    "ult": lambda a, b, w: a < b, "ule": lambda a, b, w: a <= b,
    "ugt": lambda a, b, w: a > b, "uge": lambda a, b, w: a >= b,
}


def binop(op, w, pred=None):
    m = mask(w)
    if op == "addi":
        return lambda a, b: (a + b) & m
    if op == "subi":
        return lambda a, b: (a - b) & m
    if op == "muli":
        return lambda a, b: (a * b) & m
    if op == "andi":
        return lambda a, b: a & b
    if op == "ori":
        return lambda a, b: a | b
    if op == "xori":
        return lambda a, b: a ^ b
    if op == "shli":   # Verilog <<: a shift of w or more gives 0
        return lambda a, b: (a << b) & m if b < w else 0
    if op == "shrui":
        return lambda a, b: a >> b if b < w else 0
    if op == "shrsi":  # Verilog >>> on a signed operand
        return lambda a, b: (sext(a, w) >> min(b, w)) & m
    if op == "cmpi":
        f = CMP[pred]
        return lambda a, b: 1 if f(a, b, w) else 0
    if op in ("divsi", "remsi", "divui"):
        def div(a, b):
            if op == "divui":
                return (a // b) & m if b else m
            sa, sb = sext(a, w), sext(b, w)
            if sb == 0:
                return m
            q = abs(sa) // abs(sb) * (1 if (sa < 0) == (sb < 0) else -1)
            return (q if op == "divsi" else sa - q * sb) & m
        return div
    raise Unsupported(op)


PIPE_LAT = {"muli": 4, "divsi": 35, "divui": 35, "remsi": 35}   # muli.v LATENCY 4; div/rem delay_buffer(34)+oehb
BINARY = {"addi", "subi", "andi", "ori", "xori", "shli", "shrui", "shrsi", "cmpi"}


class Circuit:
    def __init__(self, path):
        text = open(path).read()
        if '"handshake.ram"' in text:
            raise Unsupported("internal array (handshake.ram)")
        funcs = hsparse.parse_module(text, path)
        funcs = [f for f in funcs if not f.is_declaration]
        if len(funcs) != 1:
            raise Unsupported("%d functions" % len(funcs))
        f = self.func = funcs[0]
        self.path = path
        self.chan = {}       # value name -> channel id
        self.width = []      # channel -> bits (0 = control)
        self.prod = []       # channel -> (node index or ('arg', i), result index)
        self.cons = []       # channel -> (node index, operand index)
        self.args = []       # (name, kind, channel or None, width or memref (size, ew))
        for i, a in enumerate(f.args):
            m = re.fullmatch(r"memref<(\d+)xi(\d+)>", a.raw.strip())
            if a.raw.startswith("memref"):
                if not m:
                    raise Unsupported(("floating point (%s)" if "xf" in a.raw else "memref type %s") % a.raw)
                self.args.append((a.name, "memref", None, (int(m.group(1)), int(m.group(2)))))
                continue
            if "channel<f" in a.raw:
                raise Unsupported("float argument")
            c = self._new(("arg", i), 0, a.width if not a.is_control else 0)
            for nm in (a.ssa_name.lstrip("%") or "arg%d" % i, "arg%d" % i):
                self.chan[nm] = c
                self.chan[nm + "#0"] = c
            self.args.append((a.name, "control" if a.is_control else "scalar", c, a.width))
        self.nodes = f.nodes
        self.node_w = []
        for ni, n in enumerate(f.nodes):
            ws = self._result_widths(n)
            for ri, r in enumerate(n.results):
                c = self._new(ni, ri, ws[ri])
                self.chan[r] = c
                if "#" not in r:
                    self.chan[r + "#0"] = c
        self.cons = [None] * len(self.width)
        self.end_ins = []
        for ni, n in enumerate(f.nodes):
            for oi, v in enumerate(n.operands):
                if v not in self.chan:
                    if n.op == "mem_controller" and oi == 0:
                        continue  # the memref itself
                    raise Unsupported("operand %%%s of %s" % (v, n.op))
                c = self.chan[v]
                if self.cons[c] is not None:
                    raise Unsupported("value %%%s has two consumers" % v)
                self.cons[c] = (ni, oi)
            if n.op == "end":
                self.end_ins = [self.chan[v] for v in n.operands]
        self.res_names = [r.name for r in f.results]

    def _new(self, prod, ri, w):
        self.width.append(w)
        self.prod.append((prod, ri))
        return len(self.width) - 1

    def _result_widths(self, n):
        at = type_atoms(n.type_sig)
        op, nr = n.op, len(n.results)
        if nr == 0:
            return []
        if op in ("addf", "subf", "mulf", "divf", "cmpf", "sitofp", "uitofp", "fptosi", "extf", "truncf", "negf",
                  "absf", "maximumf", "minimumf"):
            raise Unsupported("floating point (%s)" % op)
        if op == "lsq":
            raise Unsupported("LSQ")
        if op == "cmpi":
            return [1]
        if op == "control_merge":
            return [width_of(at[-2]), width_of(at[-1])]
        if op in ("load", "store"):
            return [width_of(at[2]), width_of(at[3])]
        if op == "mem_controller":
            mt = re.search(r"memref<\d+xi(\d+)>", " ".join(str(x) for x in n.arg_items))
            ew = None
            for it in n.arg_items:
                for sub in getattr(it, "items", []):
                    ts = getattr(sub, "type_suffix", "")
                    mm = re.search(r"memref<\d+xi(\d+)>", ts)
                    if mm:
                        ew = int(mm.group(1))
                    if "memref<" in ts and "xf" in ts:
                        raise Unsupported("float memory")
            if ew is None:
                raise Unsupported("mem_controller element type")
            return [ew] * (nr - 1) + [0]
        return [width_of(at[-1])] * nr


def build(sim, cir):
    """One unit per op, plus the environment (arguments and end)."""
    units = []
    for ni, n in enumerate(cir.nodes):
        op = n.op
        name = n.attrs.get("handshake.name", "%s%d" % (op, ni))
        bb = attr_int(n.attrs.get("handshake.bb"))
        ins = [cir.chan[v] for v in n.operands if v in cir.chan]
        outs = [cir.chan[r] for r in n.results]
        w = cir.width[outs[0]] if outs else (cir.width[ins[0]] if ins else 0)
        if op == "fork":
            u = Fork(sim, name, bb, ins, outs)
        elif op == "lazy_fork":
            u = LazyFork(sim, name, bb, ins, outs)
        elif op == "join":
            u = Join(sim, name, bb, ins, outs)
        elif op == "merge":
            u = Merge(sim, name, bb, ins, outs)
        elif op == "mux":
            u = Mux(sim, name, bb, ins, outs)
        elif op == "control_merge":
            u = ControlMerge(sim, name, bb, ins, outs)
        elif op == "cond_br":
            u = CondBr(sim, name, bb, ins, outs)
        elif op == "sink":
            u = Sink(sim, name, bb, ins, outs)
        elif op == "source":
            u = Source(sim, name, bb, ins, outs)
        elif op == "constant":
            v = n.attrs.get("value")
            v = int(v) if isinstance(v, bool) else attr_int(v)
            if not isinstance(v, int):
                raise Unsupported("constant %r" % (v,))
            u = Constant(sim, name, bb, ins, outs, v & mask(w))
        elif op == "br":
            u = Pass(sim, name, bb, ins, outs, lambda x: x)
        elif op in ("extui", "trunci"):
            m = mask(w)
            u = Pass(sim, name, bb, ins, outs, (lambda x, m=m: x & m), trunc_ready=(op == "trunci"))
        elif op == "extsi":
            wi, m = cir.width[ins[0]], mask(w)
            u = Pass(sim, name, bb, ins, outs, lambda x, wi=wi, m=m: sext(x, wi) & m)
        elif op == "not":
            m = mask(w)
            u = Pass(sim, name, bb, ins, outs, lambda x, m=m: ~x & m)
        elif op in BINARY:
            pred = None
            if op == "cmpi":
                pred = n.arg_items[0].items[0].text
            wi = cir.width[ins[0]]
            u = Binary(sim, name, bb, ins, outs, binop(op, wi, pred))
        elif op in PIPE_LAT:
            u = Pipelined(sim, name, bb, ins, outs, binop(op, cir.width[ins[0]]), PIPE_LAT[op])
        elif op == "select":
            u = Select(sim, name, bb, ins, outs)
        elif op == "buffer":
            bt = n.attrs.get("bufferType")
            bt = getattr(bt, "text", bt)
            slots = attr_int(n.attrs.get("numSlots"))
            if bt == "ONE_SLOT_BREAK_DV" and slots == 1:
                u = Oehb(sim, name, bb, ins, outs)
            elif bt == "ONE_SLOT_BREAK_R" and slots == 1:
                u = Tehb(sim, name, bb, ins, outs)
            else:
                raise Unsupported("buffer %s x%s" % (bt, slots))
        elif op == "load":
            u = Load(sim, name, bb, ins, outs)
        elif op == "store":
            u = Store(sim, name, bb, ins, outs)
        elif op == "mem_controller":
            memref = n.operands[0]
            ai = [i for i, a in enumerate(cir.func.args) if (a.ssa_name.lstrip("%") or "arg%d" % i) == memref
                  or "arg%d" % i == memref]
            if not ai:
                raise Unsupported("mem_controller on %s" % memref)
            mname = cir.args[ai[0]][0]
            size, ew = cir.args[ai[0]][3]
            acc = [cir.chan[v] for v in n.operands[1:]]
            mem_start, ctrl_end, ports = acc[0], acc[-1], acc[1:-1]
            ctrls, ld_addr, st_addr, st_data = [], [], [], []
            for c in ports:
                pn, pr = cir.prod[c]
                while isinstance(pn, int) and cir.nodes[pn].op == "buffer":
                    pn, pr = cir.prod[cir.chan[cir.nodes[pn].operands[0]]]
                pop = cir.nodes[pn].op if isinstance(pn, int) else "arg"
                if pop == "load":
                    ld_addr.append(c)
                elif pop == "store":
                    (st_addr if pr == 0 else st_data).append(c)
                else:
                    ctrls.append(c)
            ld_data, mem_end = outs[:-1], outs[-1]
            if len(ld_data) != len(ld_addr) or len(st_addr) != len(st_data):
                raise Unsupported("mem_controller ports of %s" % name)
            u = MemController(sim, name, bb, mem_start, ctrls, ld_addr, ld_data, st_addr, st_data, ctrl_end,
                              mem_end, mname, size, ew)
        elif op == "end":
            continue
        else:
            raise Unsupported("op %s" % op)
        u.op = op
        units.append(u)
    return units


EVENT_DRIVEN = os.environ.get("DYNREF_SWEEP") != "1"   # DYNREF_SWEEP=1: evaluate every unit every cycle


class Sim:
    """Cycle-level simulation of one call."""

    def __init__(self, cir):
        self.cir = cir
        n = len(cir.width)
        self.V, self.R, self.D = [False] * n, [False] * n, [0] * n
        self.memories = {}
        self.stores = 0
        self.units = build(self, cir)
        self.order = self._order()
        self.bb_units = collections.defaultdict(list)
        for u in self.units:
            if u.bb is not None:
                self.bb_units[u.bb].append(u)

    def _order(self):
        """Units in a forward topological order of the channel graph (arguments first); used for the sweeps."""
        cir = self.cir
        by_out = {}
        for u in self.units:
            for o in u.outs:
                by_out[o] = u
        indeg = {id(u): 0 for u in self.units}
        succ = collections.defaultdict(list)
        for u in self.units:
            for i in u.ins:
                p = by_out.get(i)
                if p is not None and not isinstance(p, (Oehb, Pipelined, MemController)):
                    succ[id(p)].append(u)
                    indeg[id(u)] += 1
        q = collections.deque(u for u in self.units if indeg[id(u)] == 0)
        out, seen = [], set()
        while q:
            u = q.popleft()
            if id(u) in seen:
                continue
            seen.add(id(u))
            out.append(u)
            for v in succ[id(u)]:
                indeg[id(v)] -= 1
                if indeg[id(v)] <= 0:
                    q.append(v)
        out += [u for u in self.units if id(u) not in seen]
        return out

    def run(self, scalars, memories, max_cycles):
        """scalars: arg name -> value; memories: memref name -> list.  Returns a dict with the cycle count, the
        result values (by result name) and per-BB firing records."""
        cir = self.cir
        V, R, D = self.V, self.R, self.D
        for i in range(len(V)):
            V[i] = R[i] = False
            D[i] = 0
        self.memories = {k: list(v) for k, v in memories.items()}
        self.stores = 0
        for u in self.units:
            u.reset()
        env = []   # (channel, data) still to be taken
        for name, kind, c, w in cir.args:
            if kind == "memref":
                continue
            env.append([c, (scalars.get(name, 0) & mask(w)) if kind == "scalar" else 0, False])
        ends = {c: None for c in cir.end_ins}
        for c in cir.end_ins:
            R[c] = True
        order = self.order
        seq = [u for u in self.units if u.seq]
        by_chan = collections.defaultdict(list)
        for u in self.units:
            for c in u.ins + u.outs:
                by_chan[c].append(u)
        nbr = {id(u): [v for c in u.ins + u.outs for v in by_chan[c] if v is not u] for u in self.units}
        env_chans = set(cir.end_ins) | {e[0] for e in env}
        start = seq + [u for u in self.units if not u.seq and (set(u.ins + u.outs) & env_chans)]
        # firing records: for each control_merge / mux / merge, the cycles it fired and from which input
        merges = [u for u in self.units if u.kind in ("control_merge", "merge", "mux")]
        fires = {u.name: [] for u in merges}
        bbfire = collections.Counter()
        bb_rep = {}
        for bb, us in self.bb_units.items():
            # one unit per block that fires exactly once per block execution: its control_merge if it has one,
            # else the first unit of the block in program order that is not a source / constant / sink
            cm = [u for u in us if u.kind == "control_merge"]
            cands = cm or [u for u in us if u.kind not in ("source", "constant", "sink") and u.outs]
            if cands:
                bb_rep[bb] = cands[0]
        sweeps_max = 0
        for cyc in range(max_cycles):
            for e in env:
                c = e[0]
                V[c] = not e[2]
                D[c] = e[1]
            # settle: event-driven to the fixed point (a unit whose nets changed wakes the units that share them);
            # every sequential unit and every unit next to the environment is evaluated at least once per cycle
            if cyc == 0 or not EVENT_DRIVEN:
                work = list(order)
            else:
                work = list(start)
            queued = set(map(id, work))
            dq = collections.deque(work)
            evals = 0
            limit = 1000 * len(order)
            while dq:
                u = dq.popleft()
                queued.discard(id(u))
                evals += 1
                if u.comb():
                    for v in nbr[id(u)]:
                        if id(v) not in queued:
                            queued.add(id(v))
                            dq.append(v)
                if evals > limit:
                    raise RuntimeError("combinational loop: nets do not settle at cycle %d" % cyc)
            sweep = evals
            sweeps_max = max(sweeps_max, sweep)
            for c in ends:
                if ends[c] is None and V[c] and R[c]:
                    ends[c] = (cyc + 1, D[c])
            for e in env:
                if not e[2] and V[e[0]] and R[e[0]]:
                    e[2] = True
            for u in merges:
                o = u.outs[0]
                if V[o] and R[o]:
                    if u.kind == "mux":
                        src = D[u.ins[0]]
                    elif u.kind == "control_merge":
                        src = D[u.outs[1]]
                    else:
                        src = next((k for k, c in enumerate(u.ins) if V[c]), -1)
                    fires[u.name].append((cyc, src))
            for bb, u in bb_rep.items():
                o = u.outs[0]
                if V[o] and R[o]:
                    bbfire[bb] += 1
            if all(v is not None for v in ends.values()):
                break
            for u in seq:
                u.tick()
        else:
            return dict(done=False, cycles=max_cycles)
        res = {}
        for name, c in zip(cir.res_names, cir.end_ins):
            res[name] = ends[c][1]
        return dict(done=True, cycles=max(v[0] for v in ends.values()), results=res, fires=fires,
                    bbfire=dict(bbfire), memories=self.memories, sweeps=sweeps_max, stores=self.stores,
                    args_taken=all(e[2] for e in env))


# ----------------------------------------------------------------------------------------------------------------
# The period: the longest combinational path of the buffered circuit in Dynamatic's own timing model.
#
# Nodes are (channel, D | V | R).  Inside a unit, the arcs and their delays are those of components.json for that
# op: data in -> data out ("data", by bit width), valid in -> valid out ("valid"), ready out -> ready in ("ready"),
# and the mixed arcs of its FPL22 model: valid -> ready ("VR"), condition -> valid ("CV"), condition -> ready ("CR"),
# valid -> data ("VD").  Ops it does not list (buffers, constants, extensions, branches) are 0.  Registers cut the
# arcs they hold: ONE_SLOT_BREAK_DV cuts data and valid, ONE_SLOT_BREAK_R cuts ready, a pipelined unit (muli, div)
# cuts data and valid, a load's two TEHBs cut ready, control_merge's internal TEHB cuts ready, and the memory
# controller's read data comes from a register.  Additions beyond components.json, made because the Verilog has the
# path: control_merge valid -> index data (the priority encoder, at its "valid" delay).

def _delay(comp, op, key, width=None):
    e = comp.get("handshake." + op)
    if e is None:
        return 0.0
    d = e["delay"].get(key, 0.0)
    if isinstance(d, dict):
        ks = sorted(int(k) for k in d)
        if not ks:
            return 0.0
        w = width or 1
        pick = next((k for k in ks if k >= w), ks[-1])
        return float(d[str(pick)])
    return float(d)


def timing_arcs(sim, comp):
    arcs = []

    def a(c1, s1, c2, s2, d):
        arcs.append(((c1, s1), (c2, s2), d))

    W = sim.cir.width
    for u in sim.units:
        op, ins, outs = u.op, u.ins, u.outs
        if u.kind in ("fork", "lazy_fork"):
            i = ins[0]
            for o in outs:
                a(i, "D", o, "D", _delay(comp, op, "data", W[i]))
                a(i, "V", o, "V", _delay(comp, op, "valid"))
                a(o, "R", i, "R", _delay(comp, op, "ready"))
                if u.kind == "lazy_fork":
                    for o2 in outs:
                        if o2 != o:
                            a(o2, "R", o, "V", 0.0)
        elif u.kind in ("join", "merge"):
            o = outs[0]
            for i in ins:
                if u.kind == "merge":
                    a(i, "D", o, "D", _delay(comp, op, "data", W[o]))
                    a(i, "V", o, "D", _delay(comp, op, "VD"))
                a(i, "V", o, "V", _delay(comp, op, "valid"))
                a(o, "R", i, "R", _delay(comp, op, "ready"))
                for j in ins:
                    if j != i:
                        a(j, "V", i, "R", _delay(comp, op, "VR"))
        elif u.kind == "mux":
            sel, data, o = ins[0], ins[1:], outs[0]
            dv, vv, rr, vr = (_delay(comp, op, "data", W[o]), _delay(comp, op, "valid"), _delay(comp, op, "ready"),
                              _delay(comp, op, "VR"))
            a(sel, "D", o, "D", dv)
            a(sel, "D", o, "V", _delay(comp, op, "CV"))
            a(sel, "V", o, "V", vv)
            a(sel, "V", o, "D", _delay(comp, op, "VD"))
            a(o, "R", sel, "R", rr)
            a(sel, "D", sel, "R", _delay(comp, op, "CR"))
            for i in data:
                a(i, "D", o, "D", dv)
                a(i, "V", o, "V", vv)
                a(i, "V", o, "D", _delay(comp, op, "VD"))
                a(o, "R", i, "R", rr)
                a(sel, "V", i, "R", vr)
                a(i, "V", sel, "R", vr)
                a(sel, "D", i, "R", _delay(comp, op, "CR"))
        elif u.kind == "control_merge":
            vv = _delay(comp, op, "valid")
            for i in ins:
                for o in outs:
                    a(i, "V", o, "V", vv)
                a(i, "V", outs[1], "D", vv)
                for j in ins:
                    if j != i:
                        a(j, "V", i, "R", _delay(comp, op, "VR"))
        elif u.kind == "cond_br":
            c, d = ins
            for o in outs:
                a(d, "D", o, "D", _delay(comp, op, "data", W[d]))
                a(d, "V", o, "V", _delay(comp, op, "valid"))
                a(c, "V", o, "V", _delay(comp, op, "valid"))
                a(c, "D", o, "V", _delay(comp, op, "CV"))
                a(o, "R", d, "R", _delay(comp, op, "ready"))
                a(o, "R", c, "R", _delay(comp, op, "ready"))
            a(c, "V", d, "R", _delay(comp, op, "VR"))
            a(d, "V", c, "R", _delay(comp, op, "VR"))
            a(c, "D", d, "R", _delay(comp, op, "CR"))
            a(c, "D", c, "R", _delay(comp, op, "CR"))
        elif u.kind in ("constant", "pass"):
            i, o = ins[0], outs[0]
            a(i, "D", o, "D", 0.0)
            a(i, "V", o, "V", 0.0)
            a(o, "R", i, "R", 0.0)
        elif u.kind in ("binary", "pipelined"):
            x, y = ins
            o = outs[0]
            if u.kind == "binary":
                for i in ins:
                    a(i, "D", o, "D", _delay(comp, op, "data", W[x]))
                    a(i, "V", o, "V", _delay(comp, op, "valid"))
            for i in ins:
                a(o, "R", i, "R", _delay(comp, op, "ready"))
            a(x, "V", y, "R", _delay(comp, op, "VR"))
            a(y, "V", x, "R", _delay(comp, op, "VR"))
        elif u.kind == "select":
            c, t, f = ins
            o = outs[0]
            for i in ins:
                a(i, "D", o, "D", _delay(comp, op, "data", W[o]))
                a(i, "V", o, "V", _delay(comp, op, "valid"))
                a(c, "D", i, "R", _delay(comp, op, "CR"))
                a(o, "R", i, "R", _delay(comp, op, "ready"))
                for j in ins:
                    if j != i:
                        a(j, "V", i, "R", _delay(comp, op, "VR"))
            a(c, "D", o, "V", _delay(comp, op, "CV"))
        elif u.kind == "oehb":
            a(outs[0], "R", ins[0], "R", 0.0)
        elif u.kind == "tehb":
            a(ins[0], "D", outs[0], "D", 0.0)
            a(ins[0], "V", outs[0], "V", 0.0)
        elif u.kind == "load":
            for i, o in zip(ins, outs):
                a(i, "D", o, "D", _delay(comp, op, "data", W[o]))
                a(i, "V", o, "V", _delay(comp, op, "valid"))
        elif u.kind == "store":
            for i, o in zip(ins, outs):
                a(i, "D", o, "D", _delay(comp, op, "data", W[o]))
                a(i, "V", o, "V", _delay(comp, op, "valid"))
                a(o, "R", i, "R", _delay(comp, op, "ready"))
            a(ins[0], "V", ins[1], "R", _delay(comp, op, "VR"))
            a(ins[1], "V", ins[0], "R", _delay(comp, op, "VR"))
        elif u.kind == "mem_controller":
            for k, (ad, dd) in enumerate(zip(u.ld_addr, u.ld_data)):
                for j in range(k + 1):
                    a(u.ld_addr[j], "V", ad, "R", 0.0)
                    a(u.ld_data[j], "R", ad, "R", 0.0)
            for k in range(len(u.st_addr)):
                for j in range(k + 1):
                    for x in (u.st_addr[j], u.st_data[j]):
                        a(x, "V", u.st_addr[k], "R", 0.0)
                        a(x, "V", u.st_data[k], "R", 0.0)
            for c in u.ctrls:
                a(c, "V", u.mem_end, "V", 0.0)
    return arcs


def critical_path(sim, comp):
    """Longest path (ns) over the arcs; returns (delay, [(channel, signal), ...]).  Raises on a cycle."""
    arcs = timing_arcs(sim, comp)
    succ = collections.defaultdict(list)
    indeg = collections.Counter()
    nodes = set()
    for s, t, d in arcs:
        succ[s].append((t, d))
        indeg[t] += 1
        nodes.add(s)
        nodes.add(t)
    dist = {n: 0.0 for n in nodes}
    pred = {}
    q = collections.deque(n for n in nodes if indeg[n] == 0)
    seen = 0
    while q:
        n = q.popleft()
        seen += 1
        for t, d in succ[n]:
            if dist[n] + d > dist[t]:
                dist[t] = dist[n] + d
                pred[t] = n
            indeg[t] -= 1
            if indeg[t] == 0:
                q.append(t)
    if seen != len(nodes):
        raise RuntimeError("timing graph has a combinational cycle (%d nodes on or behind it)" % (len(nodes) - seen))
    end = max(dist, key=dist.get)
    path = [end]
    while path[-1] in pred:
        path.append(pred[path[-1]])
    return dist[end], path[::-1]


def describe_path(sim, path):
    by_out, by_in = {}, {}
    for u in sim.units:
        for o in u.outs:
            by_out[o] = u.name
        for i in u.ins:
            by_in[i] = u.name
    out = []
    for c, s in path:
        out.append("%s>%s.%s" % (by_out.get(c, "arg"), by_in.get(c, "end"), s))
    return " -> ".join(out)


# ----------------------------------------------------------------------------------------------------------------
# Fixtures, buffer placement, sources

def fixture_dirs(extra):
    ds = [os.path.join(REPO, "build", "frontend"), os.path.join(REPO, "cloud", "fixtures", "frontend")]
    for e in extra + [x for x in os.environ.get("DYNREF_FIXTURES", "").split(":") if x]:
        ds.append(e)
    return ds


def find_fixture(k, dirs):
    for d in dirs:
        p = os.path.join(d, k, "comp", "handshake_transformed.mlir")
        if os.path.isfile(p):
            return p
    return None


def find_source(k, fixture):
    """kernels/<k>/<k>.c of the repo that holds the fixture, then of this repo, then Dynamatic's integration-test."""
    roots = []
    if fixture:
        roots.append(os.path.abspath(os.path.join(os.path.dirname(fixture), "..", "..", "..", "..")))
    roots.append(REPO)
    for r in roots:
        p = os.path.join(r, "kernels", k, k + ".c")
        if os.path.isfile(p):
            return p
    # the suite's copy of Dynamatic's test (oracle_mem.sh / oracle.sh read it before dynamatic/integration-test)
    for r in roots:
        p = os.path.join(r, "research", "data", "suite", "dynsrc", k, k + ".c")
        if os.path.isfile(p):
            return p
    for p in [os.path.join(DYN, "integration-test", k, k + ".c")] + sorted(
            glob.glob(os.path.join(DYN, "integration-test", "*", k, k + ".c"))):
        if os.path.isfile(p):
            return p
    return None


def place_buffers(fixture, work):
    """compile.sh's on-merges branch, then its export canonicalization.  Returns the path of the buffered IR."""
    os.makedirs(work, exist_ok=True)
    buf = os.path.join(work, "handshake_buffered.mlir")
    exp = os.path.join(work, "handshake_export.mlir")
    with open(buf, "w") as fo:
        subprocess.run([DOPT, fixture, "--handshake-set-buffering-properties=version=fpga20",
                        "--handshake-place-buffers=algorithm=on-merges timing-models=%s" % COMPONENTS],
                       stdout=fo, check=True, stderr=subprocess.PIPE)
    with open(exp, "w") as fo:
        subprocess.run([DOPT, buf, "--handshake-canonicalize", "--handshake-hoist-ext-instances"],
                       stdout=fo, check=True, stderr=subprocess.PIPE)
    return exp


# ----------------------------------------------------------------------------------------------------------------
# Arguments: vector words -> scalar arguments (the bench's masks), and the C oracle

def domain_restrictions():
    """cells/hw/gen_bench.py DOMAIN_RESTRICTIONS, read (not imported) so the masks are the bench's own."""
    p = os.path.join(REPO, "cells", "hw", "gen_bench.py")
    try:
        src = open(p).read()
        tree = ast.parse(src)
        for node in tree.body:
            if isinstance(node, ast.Assign) and any(getattr(t, "id", "") == "DOMAIN_RESTRICTIONS"
                                                    for t in node.targets):
                return ast.literal_eval(node.value)
    except (OSError, SyntaxError, ValueError):
        pass
    return {}


def _vlit(s):
    """"32'h0000FFFF" -> 0xFFFF."""
    m = re.fullmatch(r"\d+'h([0-9a-fA-F]+)", s.strip())
    return int(m.group(1), 16) if m else int(s, 0)


def words_to_args(k, scalars, words):
    """scalars: [(name, width)]; words: list of 32-bit ints.  Applies gen_bench.py's apply_domain_masks rules."""
    restr = domain_restrictions().get(k, {})
    out, wi = {}, 0
    for name, w in scalars:
        nw = max(1, (w + 31) // 32)
        ws = [(words[wi + j] if wi + j < len(words) else 0) & 0xFFFFFFFF for j in range(nw)]
        rule = restr.get(name)
        if rule:
            if rule["kind"] == "positive_nonzero":
                m = _vlit(rule.get("mask", "32'h7FFFFFFF"))
                ws[-1] &= m
                if all(x == 0 for x in ws):
                    ws[0] = 1
            elif rule["kind"] == "and_mask":
                ws[0] &= _vlit(rule["value"])
            elif rule["kind"] == "nonnegative":
                ws[-1] &= 0x7FFFFFFF
        v = 0
        for j, x in enumerate(ws):
            v |= x << (32 * j)
        out[name] = v & mask(w)
        wi += nw
    return out


def read_vectors(path):
    vs = []
    for line in open(path):
        line = line.split("#")[0].split("//")[0].strip()
        if line:
            vs.append([int(x, 16) for x in line.split()])
    return vs


def is_v2(path):
    """A v2 bench vector file (research/data/suite/bench/README.md): first line `// benchvec words=W mems=M`."""
    with open(path) as f:
        return f.readline().startswith("// benchvec")


def read_v2(path, cir):
    """The bench's v2 layout (memvec.py, oracle_mem.sh, cells/hw/gen_bench.py): per call the operand words (scalar
    arguments in signature order, an i64 as its low word then its high word), then every element of each memref
    argument of the handshake function in signature order, one 32-bit word per element (an element narrower than 32
    bits takes the word's low bits, as the bench's host port writes it).  Returns [(operand words, {memref name:
    elements})], one per call.  Refuses a file whose header or length does not fit this kernel's signature."""
    lines = open(path).read().splitlines()
    m = re.match(r"// benchvec words=(\d+) mems=(\d+)", lines[0] if lines else "")
    if not m:
        raise Unsupported("%s: no v2 header" % path)
    nw, nm = int(m.group(1)), int(m.group(2))
    mems = [(name, w) for name, kind, c, w in cir.args if kind == "memref"]
    scal = [w for name, kind, c, w in cir.args if kind == "scalar"]
    if any(w % 32 for w in scal):
        # memvec.py gives an argument width // 32 words: a narrower scalar has no word of its own in the file
        raise Unsupported("v2 file and a scalar argument narrower than 32 bits (%s)" % scal)
    if nw != sum(w // 32 for w in scal) or nm != len(mems):
        raise Unsupported("%s says words=%d mems=%d, the handshake function has %d words and %d memrefs"
                          % (path, nw, nm, sum(w // 32 for w in scal), len(mems)))
    words = [int(x, 16) for l in lines[1:] for x in l.split("//")[0].split()]
    per = nw + sum(size for _, (size, ew) in mems)
    if per == 0 or len(words) % per:
        raise Unsupported("%s: %d words is not a whole number of %d-word calls" % (path, len(words), per))
    calls = []
    for j in range(0, len(words), per):
        k = j + nw
        mm = {}
        for name, (size, ew) in mems:
            mm[name] = [x & mask(ew) for x in words[k:k + size]]
            k += size
        calls.append((words[j:j + nw], mm))
    return calls


def oracle_mem(k, path, cir):
    """The suite's own memory oracle (research/tools/suite/oracle_mem.sh: the kernel's C, gcc -O1 -fwrapv, on the v2
    file's calls, arrays refilled from the file before every call).  Returns [(result or None, {memref name: final
    contents})], one per call, the result masked to 32 bits as the bench's out0 is, the arrays to their element width.
    The oracle holds the handshake function's memrefs in signature order (it refuses otherwise)."""
    mems = [(name, w) for name, kind, c, w in cir.args if kind == "memref"]
    fd, mo = tempfile.mkstemp(prefix="dynref_memout_")
    os.close(fd)
    try:
        p = subprocess.run([os.path.join(REPO, "research", "tools", "suite", "oracle_mem.sh"), k, path],
                           capture_output=True, text=True, timeout=600, env=dict(os.environ, ORACLE_MEMOUT=mo),
                           cwd=REPO)
        if p.returncode != 0:
            raise RuntimeError("oracle_mem.sh: " + (p.stderr.strip().splitlines() or ["exit %d" % p.returncode])[0])
        rets = [int(x, 16) for x in p.stdout.split()]
        out = [(r, {}) for r in rets]
        for line in open(mo):
            mm = re.match(r"call=(\d+) mem=(\d+) data=(\S*)", line.strip())
            if not mm:
                continue
            j, mi = int(mm.group(1)), int(mm.group(2))
            name, (size, ew) = mems[mi]
            out[j][1][name] = [int(x, 16) & mask(ew) for x in mm.group(3).split(",") if x]
        return out
    finally:
        os.unlink(mo)


CTYPE = {8: "unsigned char", 16: "unsigned short", 32: "unsigned int", 64: "unsigned long long"}


def ctype(ew):
    """The C type an element of `ew` bits is read through (an _BitInt(5) array has 1-byte elements)."""
    for w in (8, 16, 32, 64):
        if ew <= w:
            return CTYPE[w]
    raise Unsupported("element width %d" % ew)


def c_params(src, k):
    """The kernel's C parameter list: [(name, is_array)], or None if the definition is not found."""
    text = re.sub(r"//[^\n]*|/\*.*?\*/", " ", open(src).read(), flags=re.S)
    m = re.search(r"\b%s\s*\(([^()]*)\)\s*\{" % re.escape(k), text)
    if not m:
        return None
    ps = [x.strip() for x in m.group(1).split(",") if x.strip() and x.strip() != "void"]
    out = []
    for x in ps:
        mm = re.search(r"(\w+)\s*((?:\[[^\]]*\]\s*)*)$", x)
        if not mm:
            return None
        out.append((mm.group(1), "[" in x or "*" in x))
    return out


class Oracle:
    """The kernel's C, compiled with gcc -O1 -fwrapv (research/tools/fifteen/kernel_oracle.sh's flags; Dynamatic's
    clang if gcc refuses it, e.g. _BitInt) in one of two modes.  main(): the C's own main() runs, with CALL_KERNEL
    replaced by a wrapper that prints the arguments and the arrays it passes, calls the kernel, and prints the return
    value and the arrays after.  calls(): a driver that calls the kernel on given scalar arguments (arrays: copies of
    main()'s).  Parameters are matched to the handshake function's by name: Dynamatic drops memrefs nobody uses
    (--handshake-remove-unused-memrefs), and those get a zeroed dummy here."""

    def __init__(self, src, cir):
        self.src, self.cir = src, cir
        self.k = cir.func.name
        self.tmp = tempfile.mkdtemp(prefix="dynref_")
        hs = {}
        for name, kind, c, w in cir.args:
            if kind in ("scalar", "memref"):
                hs[name] = (kind, w)
        cp = c_params(src, self.k)
        if cp is None or any(n not in dict(cp) for n in hs):
            cp = [(n, kind == "memref") for n, (kind, w) in hs.items()]
        # (name, kind, width | (size, ew), in the handshake function?)
        self.params = []
        for n, is_arr in cp:
            if n in hs:
                self.params.append((n, hs[n][0], hs[n][1], True))
            else:
                self.params.append((n, "memref" if is_arr else "scalar", (0, 8) if is_arr else 32, False))
        self.ret_w = None
        for r in cir.func.results:
            if not r.is_control and r.width:
                self.ret_w = r.width
        os.makedirs(os.path.join(self.tmp, "dynamatic"), exist_ok=True)

    def close(self):
        shutil.rmtree(self.tmp, ignore_errors=True)

    def _proto(self):
        ps = [("void *p%d" if kind == "memref" else "long long p%d") % i
              for i, (name, kind, w, used) in enumerate(self.params)]
        return "void dynref_call(%s)" % (", ".join(ps) or "void")

    def _kernel_c(self):
        s = open(self.src).read()
        return re.sub(r"(?m)^(\s*int\s+)main(\s*\()", r"\1dynref_main_unused\2", s)

    def _compile(self, driver, use_main):
        with open(os.path.join(self.tmp, "dynamatic", "Integration.h"), "w") as f:
            f.write("#include <stdio.h>\n#include <string.h>\n%s;\n" % self._proto())
            if use_main:
                f.write("#define CALL_KERNEL(f, ...) dynref_call(__VA_ARGS__)\n")
            else:
                f.write("#define CALL_KERNEL(f, ...) f(__VA_ARGS__)\n")
        kc = open(self.src).read() if use_main else self._kernel_c()
        with open(os.path.join(self.tmp, "k.c"), "w") as f:
            f.write(kc + "\n" + driver)
        exe = os.path.join(self.tmp, "o_main" if use_main else "o_calls")
        err = ""
        for cc in ("gcc", os.path.join(DYN, "build", "llvm-project", "bin", "clang")):
            r = subprocess.run([cc, "-O1", "-fwrapv", "-w", "-I", self.tmp, "-I", os.path.dirname(self.src),
                                os.path.join(self.tmp, "k.c"), "-o", exe, "-lm"], capture_output=True, text=True)
            if r.returncode == 0:
                return exe
            err = err or next((l for l in r.stderr.splitlines() if "error" in l), r.stderr.strip()[:200])
        raise RuntimeError("oracle does not compile: " + err)

    def _dump_mem(self, tag, i, name, size, ew):
        return ('  printf("%s %s"); for (int j = 0; j < %d; j++) printf(" %%llx", (unsigned long long)((%s *)p%d)[j]);'
                ' printf("\\n");\n' % (tag, name, size, ctype(ew), i))

    def main_call(self):
        """Runs the C's main(); returns (scalars, memories, ret, memories_after)."""
        body = []
        for i, (name, kind, w, used) in enumerate(self.params):
            if not used:
                continue
            if kind == "memref":
                body.append(self._dump_mem("MEM", i, name, *w))
            else:
                body.append('  printf("ARG %s %%llx\\n", (unsigned long long)p%d);\n' % (name, i))
        args = ", ".join("p%d" % i for i in range(len(self.params)))
        if self.ret_w:
            body.append('  { long long r = (long long)%s(%s); printf("RET %%llx\\n", (unsigned long long)r); }\n'
                        % (self.k, args))
        else:
            body.append("  %s(%s);\n" % (self.k, args))
        for i, (name, kind, w, used) in enumerate(self.params):
            if used and kind == "memref":
                body.append(self._dump_mem("MEMOUT", i, name, *w))
        driver = "%s {\n%s}\n" % (self._proto(), "".join(body))
        exe = self._compile(driver, True)
        out = subprocess.run([exe], capture_output=True, text=True, timeout=60).stdout
        widths = {n: w for n, kind, w, used in self.params if kind == "scalar" and used}
        sc, mem, memo, ret = {}, {}, {}, None
        for line in out.splitlines():
            t = line.split()
            if not t:
                continue
            if t[0] == "ARG" and len(t) == 3:
                sc[t[1]] = int(t[2], 16) & mask(widths[t[1]])
            elif t[0] == "MEM":
                ew = dict((n, w[1]) for n, kind, w, used in self.params if kind == "memref")[t[1]]
                mem[t[1]] = [int(x, 16) & mask(ew) for x in t[2:]]
            elif t[0] == "MEMOUT":
                ew = dict((n, w[1]) for n, kind, w, used in self.params if kind == "memref")[t[1]]
                memo[t[1]] = [int(x, 16) & mask(ew) for x in t[2:]]
            elif t[0] == "RET":
                ret = int(t[1], 16) & mask(self.ret_w)
        if not out.strip() and self.params:
            raise RuntimeError("main() made no CALL_KERNEL call")
        return sc, mem, ret, memo

    def calls(self, arglist, memories):
        """Calls the kernel on each scalar-argument dict, arrays starting from `memories` every call.  Returns one
        (return value or None, {array: contents after}) per call."""
        decl, body, cargs = [], [], []
        if not any(kind == "scalar" and used for name, kind, w, used in self.params):
            body.append('    { unsigned long long z; if (scanf("%llx", &z) != 1) return 0; }\n')  # one line per call
        for i, (name, kind, w, used) in enumerate(self.params):
            if kind == "memref" and used:
                size, ew = w
                init = memories.get(name, [0] * size)
                decl.append("static const %s init%d[%d] = {%s};\nstatic %s m%d[%d];\n"
                            % (ctype(ew), i, size, ", ".join("%dull" % x for x in init), ctype(ew), i, size))
                body.append("    memcpy(m%d, init%d, sizeof m%d);\n" % (i, i, i))
                cargs.append("m%d" % i)
            elif kind == "memref":
                decl.append("static unsigned long long m%d[4096];\n" % i)
                cargs.append("(void *)m%d" % i)
            elif used:
                # the value arrives sign-extended to 64 bits; C's conversion to the parameter's own type keeps
                # its low bits (gcc), so int, unsigned, char and long long parameters all see the right word
                body.append('    if (scanf("%%llx", &a%d) != 1) return 0;\n' % i)
                cargs.append("(long long)a%d" % i)
            else:
                cargs.append("0")
        call = "%s(%s)" % (self.k, ", ".join(cargs))
        if self.ret_w:
            body.append('    printf("RET %%llx\\n", (unsigned long long)(long long)%s);\n' % call)
        else:
            body.append('    %s; printf("RET -\\n");\n' % call)
        for i, (name, kind, w, used) in enumerate(self.params):
            if kind == "memref" and used:
                body.append('    printf("MEMOUT %s"); for (int j = 0; j < %d; j++) printf(" %%llx", '
                            '(unsigned long long)m%d[j]); printf("\\n");\n' % (name, w[0], i))
        body.append('    printf("END\\n"); fflush(stdout);\n')
        avars = "".join("  unsigned long long a%d = 0;\n" % i for i in range(len(self.params)))
        driver = ("".join(decl) + "%s { }\nint main(void) {\n%s  for (;;) {\n%s  }\n}\n"
                  % (self._proto(), avars, "".join(body)))
        exe = self._compile(driver, False)
        lines = []
        for a in arglist:
            ws = ["%x" % (sext(a.get(name, 0), w) & 0xFFFFFFFFFFFFFFFF)
                  for name, kind, w, used in self.params if kind == "scalar" and used]
            lines.append(" ".join(ws) or "0")
        out = subprocess.run([exe], input="\n".join(lines) + "\n", capture_output=True, text=True,
                             timeout=600).stdout
        widths = {n: w[1] for n, kind, w, used in self.params if kind == "memref"}
        res, ret, memo = [], None, {}
        for line in out.splitlines():
            t = line.split()
            if not t:
                continue
            if t[0] == "RET":
                ret = None if t[1] == "-" else int(t[1], 16) & mask(self.ret_w)
            elif t[0] == "MEMOUT":
                memo[t[1]] = [int(x, 16) & mask(widths[t[1]]) for x in t[2:]]
            elif t[0] == "END":
                res.append((ret, memo))
                ret, memo = None, {}
        if len(res) != len(arglist):
            raise RuntimeError("oracle answered %d of %d calls" % (len(res), len(arglist)))
        return res


# ----------------------------------------------------------------------------------------------------------------
# Loops: natural loops of the block graph that the handshake IR carries (handshake.bb on every op)

def block_loops(sim):
    """Returns {header bb: set of body bbs} from the block graph: an edge b1 -> b2 wherever a channel goes from an
    op of b1 to an op of b2; back edges are those whose target dominates their source (entry bb 0)."""
    cir = sim.cir
    by_out = {}
    for u in sim.units:
        for o in u.outs:
            by_out[o] = u
    succ = collections.defaultdict(set)
    blocks = set()
    for u in sim.units:
        if u.bb is None:
            continue
        blocks.add(u.bb)
        for i in u.ins:
            p = by_out.get(i)
            if p is None or p.bb is None:
                continue
            # a block edge: a channel between blocks, or a branch feeding a merge-like op of its own block (the
            # back edge of a one-block loop; inside a block, merges sit at the entry and branches at the exit)
            if p.bb != u.bb or (p.kind == "cond_br" or p.op == "br") and u.kind in ("mux", "merge",
                                                                                     "control_merge"):
                succ[p.bb].add(u.bb)
    if not blocks:
        return {}
    entry = min(blocks)
    pred = collections.defaultdict(set)
    for b, ss in succ.items():
        for s in ss:
            pred[s].add(b)
    dom = {b: set(blocks) for b in blocks}
    dom[entry] = {entry}
    changed = True
    while changed:
        changed = False
        for b in sorted(blocks):
            if b == entry:
                continue
            ps = [dom[p] for p in pred[b] if p in dom]
            nd = ({b} | set.intersection(*ps)) if ps else {b}
            if nd != dom[b]:
                dom[b] = nd
                changed = True
    loops = collections.defaultdict(set)
    sim.dom, sim.latches = dom, collections.defaultdict(set)
    for b, ss in succ.items():
        for h in ss:
            if h in dom[b]:
                sim.latches[h].add(b)
                body = {h, b}
                stack = [b] if b != h else []
                while stack:
                    x = stack.pop()
                    for p in pred[x]:
                        if p not in body:
                            body.add(p)
                            stack.append(p)
                loops[h] |= body
    return dict(loops)


def loop_ii(sim, res, loops):
    """For each loop header: the intervals between consecutive firings of its control_merge where the second firing
    came in over a back edge (from a block of the loop)."""
    out = {}
    by_out = {}
    for u in sim.units:
        for o in u.outs:
            by_out[o] = u
    for h, body in loops.items():
        cms = [u for u in sim.bb_units.get(h, []) if u.kind == "control_merge"]
        if not cms:
            continue
        cm = cms[0]
        back = set()
        for k, c in enumerate(cm.ins):
            p = by_out.get(c)
            while p is not None and p.bb is None and p.ins:
                p = by_out.get(p.ins[0])
            if p is not None and p.bb in body and p.bb != h or (p is not None and p.bb == h):
                back.add(k)
        fs = res["fires"].get(cm.name, [])
        iv = [fs[j][0] - fs[j - 1][0] for j in range(1, len(fs)) if fs[j][1] in back]
        out[h] = dict(entries=sum(1 for f in fs if f[1] not in back), backs=len(iv), intervals=iv)
    return out


def recurrence_bound(sim, loops):
    """A LOWER bound on the cycles per iteration ANY buffer placement of this circuit could reach (e.g. Dynamatic's
    MILP, which this build cannot run): for each loop, the largest latency of a ring from one of its header's
    merge-like units back to that same unit's back-edge input (each such ring carries one token per iteration),
    counting Dynamatic's unit latencies (muli 4, div / rem 35, a memory read 1) and at least 1 per ring (a ring needs
    one register).  Only blocks that run on EVERY iteration count (those that dominate all the loop's latches): a
    ring through an if-arm binds only the iterations that take it.  Paths through other units' back edges (inner
    loops) are cut, so for an outer loop this ignores its inner loops' iterations.  Returns {header: bound}."""
    by_out = {}
    for u in sim.units:
        for o in u.outs:
            by_out[o] = u
    merge_like = ("mux", "merge", "control_merge")
    back_in = set()   # channels that are back-edge inputs of some loop header's merge-like unit
    for h, body in loops.items():
        for u in sim.bb_units.get(h, []):
            if u.kind in merge_like:
                for c in (u.ins[1:] if u.kind == "mux" else u.ins):
                    p = by_out.get(c)
                    while p is not None and p.bb is None and p.ins:
                        p = by_out.get(p.ins[0])
                    if p is not None and p.bb in body:
                        back_in.add(c)

    def lat(u):
        return u.lat if u.kind == "pipelined" else 1 if u.kind == "mem_controller" else 0

    cons = collections.defaultdict(list)
    for u in sim.units:
        for i in u.ins:
            cons[i].append(u)
    out = {}
    for h, body0 in loops.items():
        lat_bbs = sim.latches.get(h, set())
        body = {b for b in body0 if all(b in sim.dom.get(l, ()) for l in lat_bbs)}
        best = 1
        for hu in sim.bb_units.get(h, []):
            if hu.kind not in merge_like:
                continue
            targets = {c for c in (hu.ins[1:] if hu.kind == "mux" else hu.ins) if c in back_in}
            if not targets:
                continue
            memo = {}

            def longest(u, depth=0):
                # the largest latency from u's outputs to one of hu's back-edge inputs (None: does not get there)
                if id(u) in memo:
                    return memo[id(u)]
                memo[id(u)] = None
                bestv = None
                for o in u.outs:
                    if o in targets:
                        bestv = 0 if bestv is None else max(bestv, 0)
                        continue
                    if o in back_in:
                        continue
                    for v in cons.get(o, []):
                        if v is hu or (v.bb is not None and v.bb not in body):
                            continue
                        r = longest(v, depth + 1)
                        if r is not None:
                            r += lat(v)
                            bestv = r if bestv is None else max(bestv, r)
                memo[id(u)] = bestv
                return bestv

            r = longest(hu)
            if r is not None:
                best = max(best, r)
        out[h] = best
    return out


# ----------------------------------------------------------------------------------------------------------------
# One kernel

def analyse(k, vecfile=None, dirs=(), work=None, max_cycles=2000000, comp=None, verbose=False):
    """Everything for one kernel.  Returns a dict; 'status' is 'ok', or says why there is no number."""
    comp = comp or json.load(open(COMPONENTS))
    r = dict(kernel=k, vectors=vecfile or "main()")
    fixture = find_fixture(k, list(dirs))
    if not fixture:
        r["status"] = "no fixture"
        return r
    r["fixture"] = fixture
    work = work or tempfile.mkdtemp(prefix="dynref_w_")
    try:
        exp = place_buffers(fixture, os.path.join(work, k))
    except subprocess.CalledProcessError as e:
        r["status"] = "buffer placement failed: %s" % (e.stderr or b"").decode(errors="replace").strip()[:120]
        return r
    r["buffered"] = exp
    try:
        cir = Circuit(exp)
        sim = Sim(cir)
    except Unsupported as e:
        r["status"] = "not simulated (%s)" % e
        return r
    r["n_units"] = len(sim.units)
    r["n_buffers"] = sum(1 for u in sim.units if u.kind in ("oehb", "tehb"))
    try:
        cp, path = critical_path(sim, comp)
        r["cp_model_ns"] = cp
        r["cp_path"] = describe_path(sim, path)
    except RuntimeError as e:
        r["cp_model_ns"] = None
        r["cp_path"] = str(e)
    src = find_source(k, fixture)
    if not src:
        r["status"] = "no C source"
        return r
    r["source"] = src
    orc = Oracle(src, cir)
    call_mems = None    # v2 vectors: each call's own arrays
    try:
        scalars = [(name, w) for name, kind, c, w in cir.args if kind == "scalar"]
        has_mem = any(kind == "memref" for name, kind, c, w in cir.args)
        if vecfile and is_v2(vecfile):
            # the bench's v2 file: operand words and every array, per call; expected values from the suite's own
            # oracle_mem.sh (the C), the result and every array after the call
            v2 = read_v2(vecfile, cir)
            calls = [words_to_args(k, scalars, ws) for ws, _ in v2]
            call_mems = [mm for _, mm in v2]
            mems = {}
            expect = oracle_mem(k, vecfile, cir)
            if len(expect) != len(calls):
                raise RuntimeError("oracle_mem.sh answered %d of %d calls" % (len(expect), len(calls)))
            r["oracle"] = "research/tools/suite/oracle_mem.sh (v2 vectors: result and every array after each call)"
        elif vecfile:
            mems = orc.main_call()[1] if has_mem else {}
            calls = [words_to_args(k, scalars, v) for v in read_vectors(vecfile)]
            expect = orc.calls(calls, mems)
        else:
            sc, mems, _, _ = orc.main_call()
            calls = [sc]
            expect = orc.calls(calls, mems)
    except (RuntimeError, Unsupported, subprocess.TimeoutExpired) as e:
        r["status"] = "no oracle (%s)" % e
        return r
    finally:
        orc.close()
    loops = block_loops(sim)
    r["loops"] = {h: sorted(b) for h, b in loops.items()}
    sys.setrecursionlimit(max(10000, 4 * len(sim.units)))
    r["ii_bound"] = recurrence_bound(sim, loops)
    rows = []
    for j, (call, (eret, emem)) in enumerate(zip(calls, expect)):
        res = sim.run(call, call_mems[j] if call_mems is not None else mems, max_cycles)
        row = dict(args=call)
        if not res["done"]:
            row.update(status="no result within %d cycles" % max_cycles, cycles=None)
            rows.append(row)
            continue
        vals = [v for (n, v), c in zip(res["results"].items(), cir.end_ins) if cir.width[c] > 0]
        got = vals[0] if vals else None
        if call_mems is not None and got is not None:
            got &= 0xFFFFFFFF          # oracle_mem.sh prints the bench's 32-bit out0
        ok = (got == eret) if eret is not None else True
        bad_mem = [m for m, cont in emem.items() if res["memories"].get(m, [])[:len(cont)] != cont]
        ok = ok and not bad_mem
        row.update(cycles=res["cycles"], got=got, exp=eret, ok=ok, bad_mem=bad_mem, sweeps=res["sweeps"],
                   bbfire=res["bbfire"], ii=loop_ii(sim, res, loops), args_taken=res["args_taken"])
        rows.append(row)
        if verbose:
            print("  %s cycles %s got %s exp %s %s" % (call, res["cycles"], got, eret, "ok" if ok else "WRONG"),
                  file=sys.stderr)
    r["rows"] = rows
    good = [x for x in rows if x.get("ok")]
    r["n_ok"], r["n"] = len(good), len(rows)
    if len(good) != len(rows):
        r["status"] = "WRONG ANSWER in the model (%d of %d calls)" % (len(rows) - len(good), len(rows))
    else:
        r["status"] = "ok"
    # cycles per iteration: a least-squares fit of cycles per call on each loop header's executions over the calls
    # (one loop: the slope; several: one coefficient per loop = its cost per iteration net of the loops inside it),
    # and the intervals between back-edge entries of each header (its steady-state initiation interval)
    if loops and good:
        hs = sorted(loops)
        X = [[1.0] + [float(x["bbfire"].get(h, 0)) for h in hs] for x in good]
        Y = [float(x["cycles"]) for x in good]
        import numpy as np
        A, B = np.array(X), np.array(Y)
        if len(good) > len(hs) + 1 and np.linalg.matrix_rank(A) == len(hs) + 1:
            coef = np.linalg.lstsq(A, B, rcond=None)[0]
            r["fit"] = dict(a=float(coef[0]), per_loop={h: float(c) for h, c in zip(hs, coef[1:])},
                            worst=float(max(abs(A @ coef - B))), n=len(good))
        per = {}
        for h in hs:
            iv = [i for x in good for i in x["ii"].get(h, {}).get("intervals", [])]
            ex = sum(x["bbfire"].get(h, 0) for x in good)
            per[h] = dict(execs=ex, iv=(statistics.median(iv), min(iv), max(iv), len(iv), statistics.mean(iv))
                          if iv else None)
        r["per_loop"] = per
        for x in good:
            for v in x["ii"].values():
                v.pop("intervals", None)
        hot = max(hs, key=lambda h: per[h]["execs"])
        r["iter_block"] = hot
        r["iterations"] = [x["bbfire"].get(hot, 0) for x in good]
        tag = "" if len(hs) == 1 else "%d loops, the most executed (header bb%d): " % (len(hs), hot)
        if "fit" in r:
            r["cpi"] = r["fit"]["per_loop"][hot]
            r["cpi_how"] = tag + "fitted cycles per execution of the loop header over %d calls" % len(good)
        elif per[hot]["iv"]:
            r["cpi"] = per[hot]["iv"][4]
            r["cpi_how"] = tag + "mean interval between back-edge entries of the loop header (%d)" % per[hot]["iv"][3]
    return r


def calibrate(dirs, work, comp):
    """The one factor of the period estimate: least squares through 0 of the routed periods on the model's critical
    paths, with each kernel's leave-one-out error."""
    pts = []
    for k, p in MEASURED.items():
        f = find_fixture(k, list(dirs))
        if not f:
            continue
        sim = Sim(Circuit(place_buffers(f, os.path.join(work, k))))
        pts.append((k, critical_path(sim, comp)[0], p))
    if not pts:
        return None
    fac = sum(c * p for _, c, p in pts) / sum(c * c for _, c, p in pts)
    out = dict(factor=fac, points=[])
    for k, c, p in pts:
        rest = [(c2, p2) for k2, c2, p2 in pts if k2 != k]
        f1 = sum(c2 * p2 for c2, p2 in rest) / sum(c2 * c2 for c2, p2 in rest) if rest else fac
        out["points"].append(dict(kernel=k, cp=c, measured=p, est=fac * c, err=(fac * c - p) / p,
                                  loo_est=f1 * c, loo_err=(f1 * c - p) / p))
    out["rms_err"] = math.sqrt(sum(x["err"] ** 2 for x in out["points"]) / len(out["points"]))
    out["max_loo_err"] = max(abs(x["loo_err"]) for x in out["points"])
    return out


def report(r, cal):
    print("== %s (%s)" % (r["kernel"], r.get("vectors")))
    print("method: " + METHOD)
    if r.get("status") != "ok" and "rows" not in r:
        print("status: " + r["status"])
        return
    print("fixture: %s" % r.get("fixture"))
    print("buffered (on-merges): %s units, %s buffer slots; loops (header: blocks): %s"
          % (r.get("n_units"), r.get("n_buffers"), r.get("loops")))
    for x in r.get("rows", []):
        a = " ".join("%s=%x" % kv for kv in x["args"].items())
        if x.get("cycles") is None:
            print("  call %-40s %s" % (a, x.get("status")))
            continue
        a = " ".join("%s=0x%x" % kv for kv in x["args"].items())
        print("  call %-40s cycles %6d  result %s  C %s  %s%s" % (
            a, x["cycles"], "-" if x["got"] is None else "%x" % x["got"], "-" if x["exp"] is None else "%x" % x["exp"],
            "ok" if x["ok"] else "WRONG", (" (arrays differ: %s)" % x["bad_mem"]) if x.get("bad_mem") else ""))
    print("status: %s (%d of %d calls right)" % (r["status"], r.get("n_ok", 0), r.get("n", 0)))
    if "cpi" in r:
        print("cycles per iteration: %.3f  [%s]" % (r["cpi"], r["cpi_how"]))
    if "fit" in r:
        f = r["fit"]
        print("  fit over %d calls: cycles = %.2f + %s  (worst residual %.2f cycles)" % (
            f["n"], f["a"], " + ".join("%.3f x execs(bb%d)" % (c, h) for h, c in sorted(f["per_loop"].items())),
            f["worst"]))
    if r.get("ii_bound"):
        print("  lower bound on cycles per iteration for ANY buffer placement (loop recurrences): %s"
              % ", ".join("bb%s %s" % kv for kv in sorted(r["ii_bound"].items())))
    for h, v in sorted(r.get("per_loop", {}).items()):
        if v["iv"]:
            print("  loop bb%d %s: %d header executions; back-edge intervals median %g, range %g-%g (n=%d), mean %.3f"
                  % ((h, r["loops"][h], v["execs"]) + v["iv"]))
    cp = r.get("cp_model_ns")
    if cp is not None:
        print("critical path in Dynamatic's timing model: %.3f ns: %s" % (cp, r["cp_path"][:300]))
        if cal:
            p = cal["factor"] * cp
            print("period ESTIMATE: %.2f ns (= %.4f x %.3f; calibration rms error %.1f %%, worst leave-one-out %.1f %%)"
                  % (p, cal["factor"], cp, 100 * cal["rms_err"], 100 * cal["max_loo_err"]))
            if "cpi" in r and r["status"] == "ok":
                print("ns per iteration ESTIMATE: %.2f" % (p * r["cpi"]))
            la = call_latency(dict(r, period_est_ns=p))
            if la:
                print("latency per call ESTIMATE (cycles x period, %d calls): mean %.1f ns, median %.1f, range %.1f-%.1f"
                      % (la["n"], la["mean_ns"], la["med_ns"], la["min_ns"], la["max_ns"]))
            if r["kernel"] in MEASURED:
                print("measured (routed 2026-08, 1 seed): %.2f ns period" % MEASURED[r["kernel"]])


# The verification vectors of the six original kernels, as research/tools/suite/suite_one.sh picks them (per kernel by
# nature: where its verification data lives).  Any other kernel: kernels/<k>/vec.hex beside its fixture, else main().
GATE_VECTORS = {
    "xorshift": "research/data/eventgraph/gate/xor19.hex", "collatz": "research/data/eventgraph/gate/col18.hex",
    "collatz64": "research/data/eventgraph/gate/c6419.hex", "ipow": "research/data/eventgraph/gate/ipow17.hex",
    "isprime": "research/data/alltable/isp17.hex", "gcd": "research/data/eventgraph/gate/gcd18.hex",
}


def pick_vectors(k, fixture, dirs=()):
    if k in GATE_VECTORS and os.path.isfile(os.path.join(REPO, GATE_VECTORS[k])):
        return os.path.join(REPO, GATE_VECTORS[k])
    roots = [os.path.abspath(os.path.join(os.path.dirname(fixture), "..", "..", "..", ".."))] if fixture else []
    roots += [REPO] + [os.path.abspath(os.path.join(d, "..", "..")) for d in dirs]
    for r in roots:
        v = os.path.join(r, "kernels", k, "vec.hex")
        if os.path.isfile(v):
            return v
    # Dynamatic's tests in the suite keep their vectors here (suite_one.sh: no kernels/ directory, it would shadow
    # the test in bdc/frontend.sh)
    for r in roots:
        v = os.path.join(r, "research", "data", "suite", "vec", k + ".hex")
        if os.path.isfile(v):
            return v
    return None


# The calls the suite's routes are judged and timed on (research/tools/suite/suite_one.sh's V), where they differ from
# the vectors above: gcd's draws run gcd8 (gcd18 stays the vector set of the cycles-per-iteration fit, which is
# VERIFIED on it).  The per-call figure (cycles x period, for the latency-per-call ratio) is taken on these calls.
SUITE_VECTORS = {"gcd": "research/data/suite/vec/gcd8.hex"}


def suite_vectors(k, fixture, dirs=()):
    if k in SUITE_VECTORS and os.path.isfile(os.path.join(REPO, SUITE_VECTORS[k])):
        return os.path.join(REPO, SUITE_VECTORS[k])
    return pick_vectors(k, fixture, dirs)


def call_latency(r):
    """Dynamatic's latency per call, ESTIMATE: cycles per call (simulated, answers = C) x the period estimate, over
    every call of the run.  None unless every call was right and the period has an estimate."""
    p = r.get("period_est_ns")
    cs = [x.get("cycles") for x in r.get("rows", [])]
    if not p or not cs or r.get("status") != "ok" or any(c is None for c in cs):
        return None
    ns = [c * p for c in cs]
    # the trip counts of the same calls (header executions of the most executed loop; JSON keys are strings), for a
    # fit of another circuit's call latencies on them (suite_table.py)
    hot, loops = r.get("iter_block"), r.get("loops") or {}
    execs = None
    if hot is not None:
        execs = [(x.get("bbfire") or {}).get(str(hot), (x.get("bbfire") or {}).get(hot, 0)) for x in r["rows"]]
    return dict(n=len(cs), cycles=cs, period_ns=p, mean_ns=sum(ns) / len(ns), med_ns=statistics.median(ns),
                min_ns=min(ns), max_ns=max(ns), sum_ns=sum(ns), execs=execs, n_loops=len(loops), hot=hot)


def table(kernels, dirs, work, max_cycles, timeout, out_dir):
    """Every kernel in its own process (a wall-clock limit per kernel), then the markdown table and a TSV."""
    def one(k, v):
        cmd = [sys.executable, os.path.abspath(__file__), k] + ([v] if v else []) + [
            "--json", "--work", work, "--max-cycles", str(max_cycles)]
        for d in dirs[2:]:
            cmd += ["--fixtures", d]
        try:
            p = subprocess.run(cmd, capture_output=True, text=True, timeout=timeout)
            j = p.stdout[p.stdout.index("{"):] if "{" in p.stdout else ""
            return json.loads(j) if j else dict(kernel=k, status="tool error: " + (p.stderr.strip().splitlines()
                                                                                    or ["?"])[-1][:100])
        except subprocess.TimeoutExpired:
            return dict(kernel=k, status="not finished in %d s" % timeout)

    def rel(v):
        return re.sub(r"^.*/(kernels/)", r"\1", os.path.relpath(v, REPO)) if v else "main()"

    rows = []
    for k in kernels:
        f = find_fixture(k, dirs)
        v = pick_vectors(k, f, dirs)
        r = one(k, v)
        r["vectors"] = rel(v)
        r["vectors_path"] = v
        # the per-call figure on the suite's own calls (suite_one.sh's V), a second run where they differ
        sv = suite_vectors(k, f, dirs)
        rs = r if sv == v else one(k, sv)
        r["lat"] = call_latency(rs)
        if r["lat"]:
            r["lat"]["vectors"] = rel(sv)
            r["lat"]["vectors_md5"] = md5(sv) if sv else None
        elif sv != v:
            r["lat_status"] = rs.get("status")
        rows.append(r)
        print("%-24s %s" % (k, r.get("status")), file=sys.stderr, flush=True)
    return rows


def md5(path):
    import hashlib
    return hashlib.md5(open(path, "rb").read()).hexdigest()[:8]


def add_estimate(r, cal):
    cp = r.get("cp_model_ns")
    if cp and cal:   # a circuit whose every arc is registered or 0 in the model (a lone divider) has no estimate
        r["period_est_ns"] = cal["factor"] * cp
        r["cal_factor"] = cal["factor"]
        if "cpi" in r and r.get("status") == "ok":
            r["ns_per_iter_est"] = r["period_est_ns"] * r["cpi"]
    if r.get("kernel") in MEASURED:
        r["measured_period_ns"] = MEASURED[r["kernel"]]
    return r


def cell_cycles(r):
    cs = [x["cycles"] for x in r.get("rows", []) if x.get("ok")]
    if not cs:
        return "-"
    if len(cs) == 1:
        return "%d (1 call)" % cs[0]
    if min(cs) == max(cs):
        return "%d (%d calls)" % (cs[0], len(cs))
    return "%d-%d (%d calls)" % (min(cs), max(cs), len(cs))


def cell_cpi(r):
    if "cpi" not in r or r.get("status") != "ok":
        return "-"
    per = r.get("per_loop", {})
    hot = r.get("iter_block")
    s = "%.2f" % r["cpi"]
    if len(per) > 1:
        s += " (bb%s, the most executed of %d loops" % (hot, len(per))
        other = []
        for h, v in sorted(per.items(), key=lambda kv: int(kv[0])):
            if str(h) != str(hot) and v.get("iv"):
                other.append("bb%s %g" % (h, v["iv"][0]))
        if other:
            s += "; median back-edge interval of the others: " + ", ".join(other)
        s += ")"
    return s


def cell_lat(r):
    """Latency per call, ns (ESTIMATE): mean over the suite's calls (min-max), and on which calls."""
    la = r.get("lat")
    if not la:
        return "-" + (" (%s)" % r["lat_status"] if r.get("lat_status") else "")
    s = "%.1f (%.1f-%.1f; %d calls" % (la["mean_ns"], la["min_ns"], la["max_ns"], la["n"])
    if la.get("vectors") and la["vectors"] != r.get("vectors"):
        s += ", %s" % la["vectors"]
    return s + ")"


def write_table(rows, cal, path_md, path_tsv, path_lat=None):
    L = []
    L.append("| kernel | vectors | Dynamatic cycles per call (simulated; answers = C) | cycles per iteration "
             "(simulated, on-merges) | lower bound, any placement | period, ns (ESTIMATE) | ns per iteration "
             "(ESTIMATE) | latency per call, ns (ESTIMATE): mean (range) | measured period, ns (routed, 1 seed, "
             "2026-08) |")
    L.append("|---|---|---|---|---|---|---|---|---|")
    tsv = ["# kernel\tns per iteration\ttag\thow it was obtained (research/data/suite/dynamatic/README.md)"]
    lat = ["# kernel\tcalls\tmean ns per call\ttag\tvectors\tvectors md5\tcycles per call\tperiod ns (ESTIMATE)\t"
           "model path ns\tloops\theader executions per call (most executed loop)\thow it was obtained "
           "(research/data/suite/dynamatic/README.md)"]
    for r in rows:
        st = r.get("status", "?")
        k = r["kernel"]
        if st != "ok":
            what = st if "rows" not in r else st
            L.append("| %s | %s | %s | - | - | %s | - | - | %s |" % (
                k, r.get("vectors", "-"), what, "-",
                ("%.2f" % r["measured_period_ns"]) if r.get("measured_period_ns") else "-"))
            continue
        npi = r.get("ns_per_iter_est")
        hot = r.get("iter_block")
        bnd = (r.get("ii_bound") or {}).get(str(hot), (r.get("ii_bound") or {}).get(hot))
        L.append("| %s | %s | %s | %s | %s | %s | %s | %s | %s |" % (
            k, r.get("vectors", "-"), cell_cycles(r), cell_cpi(r),
            ("%d" % bnd + (" (ABOVE the simulated value: analysis error)" if bnd > 1.05 * r["cpi"] else ""))
            if bnd and "cpi" in r else "-",
            ("%.2f" % r["period_est_ns"]) if r.get("period_est_ns") else "- (no arc in the model)",
            ("%.1f" % npi) if npi else "- (no loop)", cell_lat(r),
            ("%.2f (cycles x period = %.2f)" % (r["measured_period_ns"], r["measured_period_ns"] * r["cpi"]))
            if r.get("measured_period_ns") and "cpi" in r else "-"))
        if npi:
            tsv.append("%s\t%.2f\tESTIMATE\tDynamatic on-merges, simulated %.2f cycles per iteration (answers = C; "
                       "any placement >= %s) x period %.2f ns ESTIMATED from Dynamatic's timing model (x%.3f fitted "
                       "on 3 routed kernels, worst leave-one-out %.0f %%); research/tools/suite/dynamatic_est.py"
                       % (k, npi, r["cpi"], bnd, r["period_est_ns"], cal["factor"], 100 * cal["max_loo_err"]))
        la = r.get("lat")
        if la and la.get("vectors") not in (None, "main()"):
            if k in MEASURED:
                # the routed period where one exists (as the per-iteration column uses it): cycles x measured period
                pm = MEASURED[k]
                lat.append("%s\t%d\t%.2f\tcycles simulated, period measured (1 route)\t%s\t%s\t%s\t%.3f\t%.3f\t%d\t%s\t"
                           "Dynamatic on-merges, simulated cycles per call on the suite's calls (answers = C) x the "
                           "routed period %.2f ns (one nextpnr route, 2026-08; research/data/dynamatic_ref/README.md); "
                           "research/tools/suite/dynamatic_est.py"
                           % (k, la["n"], la["mean_ns"] / la["period_ns"] * pm, la["vectors"], la["vectors_md5"],
                              ",".join(str(c) for c in la["cycles"]), pm, r["cp_model_ns"], la["n_loops"],
                              ",".join(str(e) for e in la["execs"]) if la.get("execs") else "-", pm))
                continue
            lat.append("%s\t%d\t%.2f\tESTIMATE\t%s\t%s\t%s\t%.3f\t%.3f\t%d\t%s\tDynamatic on-merges, simulated cycles per "
                       "call on the suite's calls (answers = C) x period %.2f ns ESTIMATED from Dynamatic's timing model "
                       "(x%.3f fitted on 3 routed kernels, worst leave-one-out %.0f %%); "
                       "research/tools/suite/dynamatic_est.py"
                       % (k, la["n"], la["mean_ns"], la["vectors"], la["vectors_md5"],
                          ",".join(str(c) for c in la["cycles"]), la["period_ns"], r["cp_model_ns"], la["n_loops"],
                          ",".join(str(e) for e in la["execs"]) if la.get("execs") else "-", la["period_ns"],
                          cal["factor"], 100 * cal["max_loo_err"]))
    open(path_md, "w").write("\n".join(L) + "\n")
    open(path_tsv, "w").write("\n".join(tsv) + "\n")
    if path_lat:
        open(path_lat, "w").write("\n".join(lat) + "\n")


def main():
    ap = argparse.ArgumentParser(description=__doc__.split("\n")[0])
    ap.add_argument("kernel", nargs="?")
    ap.add_argument("vectors", nargs="?")
    ap.add_argument("--fixtures", action="append", default=[], help="another build/frontend directory (read only)")
    ap.add_argument("--work", default=None, help="where the buffered IR goes (default: a temporary directory)")
    ap.add_argument("--max-cycles", type=int, default=2000000)
    ap.add_argument("--calibrate", action="store_true")
    ap.add_argument("--json", action="store_true")
    ap.add_argument("--table", nargs="*", metavar="KERNEL",
                    help="run KERNELs (default: every fixture found) and write --out/table.md and dynamatic_est.tsv")
    ap.add_argument("--out", default=os.path.join(REPO, "research", "data", "suite", "dynamatic"))
    ap.add_argument("--timeout", type=int, default=600, help="seconds per kernel in --table")
    ap.add_argument("-v", "--verbose", action="store_true")
    a = ap.parse_args()
    dirs = fixture_dirs(a.fixtures)
    work = a.work or tempfile.mkdtemp(prefix="dynref_w_")
    comp = json.load(open(COMPONENTS))
    cal = calibrate(dirs, os.path.join(work, "_cal"), comp)
    if a.table is not None:
        ks = a.table or sorted({k for d in dirs if os.path.isdir(d) for k in os.listdir(d)
                                if find_fixture(k, [d])})
        rows = table(ks, dirs, work, a.max_cycles, a.timeout, a.out)
        os.makedirs(a.out, exist_ok=True)
        json.dump(dict(calibration=cal, rows=rows), open(os.path.join(a.out, "dynamatic_est.json"), "w"),
                  default=str, indent=1)
        write_table(rows, cal, os.path.join(a.out, "table.md"), os.path.join(a.out, "dynamatic_est.tsv"),
                    os.path.join(a.out, "dynamatic_lat.tsv"))
        print(open(os.path.join(a.out, "table.md")).read())
        return
    if a.calibrate or not a.kernel:
        if not cal:
            sys.exit("no fixture for any of the routed kernels %s" % sorted(MEASURED))
        print("period calibration: P = %.4f x (critical path in Dynamatic's timing model)" % cal["factor"])
        for x in cal["points"]:
            print("  %-10s model %.3f ns  routed %.2f  fit %.2f (%+.1f %%)  leave-one-out %.2f (%+.1f %%)"
                  % (x["kernel"], x["cp"], x["measured"], x["est"], 100 * x["err"], x["loo_est"], 100 * x["loo_err"]))
        print("  rms error %.1f %%, worst leave-one-out %.1f %%" % (100 * cal["rms_err"], 100 * cal["max_loo_err"]))
        if not a.kernel:
            return
    r = add_estimate(analyse(a.kernel, a.vectors, dirs, work, a.max_cycles, comp, a.verbose), cal)
    if a.json:
        print(json.dumps(r, default=str, indent=1))
    else:
        report(r, cal)
        print("does NOT capture: " + "; ".join(NOT_CAPTURED))


if __name__ == "__main__":
    main()
