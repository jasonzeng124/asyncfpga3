"""tckmodel.py -- gate-level circuits as networks of DENSE-TIME timed automata,
emitted in TChecker's input format and checked with tck-reach (zone graph,
covering reachability, ExtraLU+ abstraction).

Probe C-12c (formal/notes/C-12c-zone.md).  This is the port of C-12b's
formal/tools/async/tamodel.py (Storm, digital clocks) to a zone-based checker.
The node semantics are the same as 12b's, except that time is dense (real
valued clocks) and every delay bound may be any non-negative integer (the unit
is free; arb.py uses 1 ps):

  * a node x has a Boolean output (int variable x in {0,1}) and a next-value
    function f_x, given as an expression AST over node names.  LUT nodes take
    the REAL INIT constant and pin map and are Shannon-expanded (no hand
    simplification), exactly as in 12b.
  * INERTIAL channel: one process per node, locations S (stable), ER (excited
    to rise, invariant c_x <= rise_hi), EF (excited to fall, invariant
    c_x <= fall_hi).  The clock is reset when the excitation starts; an
    excitation withdrawn before x fires is swallowed (hz_x flags it).  x may
    fire once c_x >= lo.  hi = None: no deadline (free environment move).
  * TRANSPORT channel (FIFO pure delay): locations T<x><len> (current output x,
    len edges in flight, len <= K).  In-flight edges alternate in value, so
    the queue is (x, len) plus one clock per slot.  A zero-width reversal
    (the newest edge has age 0) is cancelled; when the second edge is already
    due (c_1 >= its lo) it annihilates with the head (pulse shrinkage under
    asymmetric rise/fall, as in 12b); ovf_x flags overflow (exact only where
    unreachable), mlt_x flags a second edge queued behind an undelivered one
    (a runt at x's input).
  * a node firing is one TChecker event f_<x>, strongly synchronised with
    u_<x> edges of every node that reads x.  Each reader has an exhaustive set
    of u_<x> edges from every location (guards evaluated in the pre-state with
    x substituted by its new value), so the synchronisation never blocks.
  * a property "F cond" is a monitor process mon (ok -> bad{labels:bad},
    guard cond); tck-reach -l bad answers it.  cond may read flags.

Everything is integer-bounded and closed, so zone reachability with ExtraLU+
is exact for dense time (Alur-Dill; Behrmann et al. 2006 for ExtraLU+).
"""

from dataclasses import dataclass, field
from typing import Dict, List, Optional, Tuple
import itertools

# ----------------------------------------------------------------- expressions
# AST: ('c', 0|1) | ('v', name) | ('ite', c, t, e) | ('not', a) | ('and', a, b)
#      | ('or', a, b) | ('eq', a, b)


def C(b):
    return ('c', 1 if b else 0)


def V(n):
    return ('v', n)


def NOT(a):
    return ('not', a)


def AND(*xs):
    e = xs[0]
    for x in xs[1:]:
        e = ('and', e, x)
    return e


def OR(*xs):
    e = xs[0]
    for x in xs[1:]:
        e = ('or', e, x)
    return e


def EQ(a, b):
    return ('eq', a, b)


def ITE(c, t, e):
    return ('ite', c, t, e)


def subst(e, env):
    """substitute and constant-fold.  env: name -> AST."""
    k = e[0]
    if k == 'c':
        return e
    if k == 'v':
        return env.get(e[1], e)
    a = [subst(x, env) for x in e[1:]]
    if k == 'not':
        return C(not a[0][1]) if a[0][0] == 'c' else ('not', a[0])
    if k == 'and':
        if a[0] == C(0) or a[1] == C(0):
            return C(0)
        if a[0] == C(1):
            return a[1]
        if a[1] == C(1):
            return a[0]
        return ('and', a[0], a[1])
    if k == 'or':
        if a[0] == C(1) or a[1] == C(1):
            return C(1)
        if a[0] == C(0):
            return a[1]
        if a[1] == C(0):
            return a[0]
        return ('or', a[0], a[1])
    if k == 'eq':
        if a[0][0] == 'c' and a[1][0] == 'c':
            return C(a[0][1] == a[1][1])
        if a[0] == a[1]:
            return C(1)
        return ('eq', a[0], a[1])
    if k == 'ite':
        c, t, f = a
        if c[0] == 'c':
            return t if c[1] else f
        if t == f:
            return t
        if t == C(1) and f == C(0):
            return c
        if t == C(0) and f == C(1):
            return ('not', c)
        return ('ite', c, t, f)
    raise ValueError(k)


def evalb(e, vals):
    r = subst(e, {n: C(v) for n, v in vals.items()})
    assert r[0] == 'c', r
    return r[1]


def names(e, acc=None):
    acc = set() if acc is None else acc
    if e[0] == 'v':
        acc.add(e[1])
    elif e[0] != 'c':
        for x in e[1:]:
            names(x, acc)
    return acc


def term(e):
    """TChecker integer term with value 0/1."""
    k = e[0]
    if k == 'c':
        return str(e[1])
    if k == 'v':
        return e[1]
    if k == 'not':
        return f"(1-{term(e[1])})"
    if k == 'and':
        return f"({term(e[1])}*{term(e[2])})"
    if k == 'or':
        return f"(if {term(e[1])}==1 then 1 else {term(e[2])})"
    if k == 'eq':
        return f"(if {term(e[1])}=={term(e[2])} then 1 else 0)"
    if k == 'ite':
        return f"(if {term(e[1])}==1 then {term(e[2])} else {term(e[3])})"
    raise ValueError(k)


def is1(e):
    """guard expression 'e holds' (None if constant true, False if const false)"""
    e = subst(e, {})
    if e == C(1):
        return None
    if e == C(0):
        return False
    if e[0] == 'v':
        return f"{e[1]}==1"
    if e[0] == 'not' and e[1][0] == 'v':
        return f"{e[1][1]}==0"
    return f"{term(e)}==1"


def lut(init: int, pins: List[Optional[str]], out: str = "O6"):
    """6-input LUT: pins I0..I5 (None = tied 0, '1' = tied 1).  O6 reads
    INIT[63:0] by I5..I0; O5 reads INIT[31:0] by I4..I0 (LUT6_2 with I5=1)."""
    pins = list(pins) + [None] * (6 - len(pins))

    def build(k, idx):
        if k < 0:
            return C((init >> idx) & 1)
        if out == "O5" and k == 5:
            return build(k - 1, idx)
        p = pins[k]
        if p is None:
            return build(k - 1, idx)
        if p == "1":
            return build(k - 1, idx | (1 << k))
        hi, lo = build(k - 1, idx | (1 << k)), build(k - 1, idx)
        return subst(ITE(V(p), hi, lo), {})

    return build(5, 0)


# ----------------------------------------------------------------- circuit
@dataclass
class Node:
    name: str
    f: tuple
    init: bool
    rise: Tuple[int, Optional[int]]
    fall: Tuple[int, Optional[int]]
    watch_hazard: bool = False
    on_fire: List[Tuple[str, tuple]] = field(default_factory=list)
    on_fire_set: List[Tuple[str, tuple]] = field(default_factory=list)
    mode: str = "inertial"
    K: int = 3


def _conj(gs):
    gs = [g for g in gs if g is not None]
    if any(g is False for g in gs):
        return False
    return " && ".join(gs) if gs else None


class Circuit:
    def __init__(self):
        self.nodes: List[Node] = []
        self.flags: List[str] = []

    def add(self, *a, **k):
        n = Node(*a, **k)
        self.nodes.append(n)
        return n

    def flag(self, name):
        self.flags.append(name)

    def node(self, name):
        return next(n for n in self.nodes if n.name == name)

    # -------------------------------------------------------------- helpers
    def _initvals(self):
        return {n.name: int(n.init) for n in self.nodes}

    def _init_loc(self, n):
        v = self._initvals()
        fx = evalb(n.f, v)
        x = int(n.init)
        if n.mode == "inertial":
            if fx == x:
                return "S"
            return "ER" if x == 0 else "EF"
        return f"T{x}{1 if fx != x else 0}"

    def _locs(self, n):
        if n.mode == "inertial":
            out = [("S", None)]
            if n.rise[1] is not None:
                out.append(("ER", f"c_{n.name}<={n.rise[1]}"))
            else:
                out.append(("ER", None))
            if n.fall[1] is not None:
                out.append(("EF", f"c_{n.name}<={n.fall[1]}"))
            else:
                out.append(("EF", None))
            return out
        out = []
        for x in (0, 1):
            for ln in range(n.K + 1):
                inv = None
                if ln >= 1:
                    hi = n.rise[1] if x == 0 else n.fall[1]
                    assert hi is not None
                    inv = f"c_{n.name}_0<={hi}"
                out.append((f"T{x}{ln}", inv))
        return out

    def _clocks(self, n):
        if n.mode == "inertial":
            return [f"c_{n.name}"]
        return [f"c_{n.name}_{j}" for j in range(n.K)]

    def _update_cases(self, m, loc, fp):
        """node m in location loc sees its next-value become fp (an AST over
        the pre-state).  Returns [(guard, target, [stmts])], exhaustive."""
        x = m.name
        g1, g0 = is1(fp), is1(NOT(fp))
        out = []
        if m.mode == "inertial":
            c = f"c_{x}"
            if loc == "S":
                out.append((_conj([f"{x}==0", g1]), "ER", [f"{c}=0"]))
                out.append((_conj([f"{x}==1", g0]), "EF", [f"{c}=0"]))
                out.append((_conj([is1(EQ(fp, V(x)))]), "S", []))
            else:
                stay = g1 if loc == "ER" else g0
                leave = g0 if loc == "ER" else g1
                out.append((stay, loc, []))
                st = [f"{c}=0"]
                if m.watch_hazard:
                    st.append(f"hz_{x}=1")
                out.append((leave, "S", st))
            return [o for o in out if o[0] is not False]
        # transport
        xv, ln = int(loc[1]), int(loc[2:])
        lastv = xv if ln % 2 == 0 else 1 - xv
        same = g1 if lastv == 1 else g0
        diff = g0 if lastv == 1 else g1
        out.append((same, loc, []))
        if diff is not False:
            if ln == 0:
                out.append((diff, f"T{xv}1", [f"c_{x}_0=0"]))
            else:
                cl = f"c_{x}_{ln-1}"
                out.append((_conj([diff, f"{cl}==0"]), f"T{xv}{ln-1}", []))
                if ln < m.K:
                    out.append((_conj([diff, f"{cl}>0"]), f"T{xv}{ln+1}",
                                [f"c_{x}_{ln}=0", f"mlt_{x}=1"]))
                else:
                    out.append((_conj([diff, f"{cl}>0"]), loc,
                                [f"ovf_{x}=1", f"mlt_{x}=1"]))
        return [o for o in out if o[0] is not False]

    def _readers(self, n):
        return [m for m in self.nodes if m is not n and n.name in names(m.f)]

    # -------------------------------------------------------------- emit
    def tck(self, monitor_cond, label="bad") -> str:
        L = ["system:circ", ""]
        for n in self.nodes:
            L.append(f"int:1:0:1:{int(n.init)}:{n.name}")
        flags = list(self.flags)
        for n in self.nodes:
            if n.mode == "inertial" and n.watch_hazard:
                flags.append(f"hz_{n.name}")
            if n.mode == "transport":
                flags += [f"ovf_{n.name}", f"mlt_{n.name}"]
        for fl in flags:
            L.append(f"int:1:0:1:0:{fl}")
        for n in self.nodes:
            for c in self._clocks(n):
                L.append(f"clock:1:{c}")
        for n in self.nodes:
            L.append(f"event:f_{n.name}")
            L.append(f"event:u_{n.name}")
            L.append(f"event:a_{n.name}")
        L.append("event:mon_e")
        L.append("")
        for n in self.nodes:
            L.append(f"process:{n.name}")
            il = self._init_loc(n)
            for loc, inv in self._locs(n):
                at = []
                if loc == il:
                    at.append("initial:")
                if inv:
                    at.append(f"invariant:{inv}")
                L.append(f"location:{n.name}:{loc}{{{' : '.join(at)}}}")
            # firing edges
            for loc, _ in self._locs(n):
                for g, tgt, st in self._fire(n, loc):
                    L.append(self._edge(n.name, loc, tgt, f"f_{n.name}", g, st))
                if n.mode == "transport":
                    xv, ln = int(loc[1]), int(loc[2:])
                    if ln >= 2:
                        lo1 = n.fall[0] if xv == 0 else n.rise[0]  # edge 1 = back to x
                        shifts = [f"c_{n.name}_{j}=c_{n.name}_{j+2}"
                                  for j in range(n.K - 2)]
                        shifts += [f"c_{n.name}_{j}=0"
                                   for j in range(max(n.K - 2, 0), n.K)]
                        L.append(self._edge(n.name, loc, f"T{xv}{ln-2}",
                                            f"a_{n.name}",
                                            f"c_{n.name}_1>={lo1}", shifts))
            # reader edges
            for src in self.nodes:
                if src is n or src.name not in names(n.f):
                    continue
                for loc, _ in self._locs(n):
                    for g, tgt, st in self._reader_cases(n, loc, src):
                        L.append(self._edge(n.name, loc, tgt, f"u_{src.name}",
                                            g, st))
            L.append("")
        L.append("process:mon")
        L.append("location:mon:ok{initial:}")
        L.append(f"location:mon:bad{{labels:{label}}}")
        g = is1(monitor_cond)
        if g is not False:
            L.append(self._edge("mon", "ok", "bad", "mon_e", g, []))
        L.append("")
        for n in self.nodes:
            rd = self._readers(n)
            if rd:
                L.append(f"sync:{n.name}@f_{n.name}:" +
                         ":".join(f"{m.name}@u_{n.name}" for m in rd))
        return "\n".join(L) + "\n"

    @staticmethod
    def _edge(p, s, t, ev, guard, stmts):
        at = []
        if guard:
            at.append(f"provided:{guard}")
        if stmts:
            at.append(f"do:{';'.join(stmts)}")
        return f"edge:{p}:{s}:{t}:{ev}{{{' : '.join(at)}}}"

    def _reader_cases(self, m, loc, src):
        """m reads src; src fires (src := !src).  Guards over the pre-state."""
        post = {src.name: NOT(V(src.name))}
        fp = subst(m.f, post)
        return self._update_cases(m, loc, fp)

    def _fire(self, n, loc):
        """firing edges of n out of loc: [(guard, target, stmts)]."""
        x = n.name
        out = []
        flag_st = []
        for fl, cond in n.on_fire:
            g = subst(cond, {})
            if g != C(0):
                flag_st.append(f"{fl}={term(OR(V(fl), g))}")
        for fl, ex in n.on_fire_set:
            flag_st.append(f"{fl}={term(subst(ex, {}))}")
        if n.mode == "inertial":
            if loc == "S":
                return []
            newv = 1 if loc == "ER" else 0
            lo = n.rise[0] if loc == "ER" else n.fall[0]
            fp = subst(n.f, {x: C(newv)})
            base = flag_st + [f"{x}={newv}", f"c_{x}=0"]  # flags read the PRE-state
            # after firing x is stable unless f reads x itself
            g_st = is1(EQ(fp, C(newv)))
            g_ex = is1(EQ(fp, C(1 - newv)))
            tgt_ex = "EF" if newv == 1 else "ER"
            for g, t in ((g_st, "S"), (g_ex, tgt_ex)):
                if g is not False:
                    out.append((_conj([f"c_{x}>={lo}", g]), t, list(base)))
            return out
        xv, ln = int(loc[1]), int(loc[2:])
        if ln == 0:
            return []
        lo = n.rise[0] if xv == 0 else n.fall[0]
        g = [f"c_{x}_0>={lo}"]
        if ln >= 2:
            lo1 = n.fall[0] if xv == 0 else n.rise[0]
            g.append(f"c_{x}_1<{lo1}")
        shifts = [f"c_{x}_{j}=c_{x}_{j+1}" for j in range(n.K - 1)]
        shifts.append(f"c_{x}_{n.K-1}=0")
        newv = 1 - xv
        base = flag_st + [f"{x}={newv}"] + shifts  # flags read the PRE-state
        # self-dependence: queue of the post location sees fp (x := newv).
        # The clock shift happens first, so c_{x}_{j} in the case guards
        # below refers to the PRE-state slot j+1: rename.
        fp = subst(n.f, {x: C(newv)})
        ploc = f"T{newv}{ln-1}"
        for g2, t2, st2 in self._update_cases(n, ploc, fp):
            if g2:
                g2 = re.sub(rf"\bc_{re.escape(x)}_(\d+)\b",
                            lambda mo: f"c_{x}_{int(mo.group(1))+1}", g2)
            out.append((_conj(g + [g2]), t2, base + st2))
        return out


# ----------------------------------------------------------------- running
import os
import re
import subprocess
import tempfile
import time

TCK = os.environ.get("TCK_REACH") or os.path.join(
    os.path.dirname(os.path.abspath(__file__)), "build", "tchecker", "bin",
    "tck-reach")


def reach(text, label="bad", mem_gb=3.5, timeout=3600, algo="covreach",
          extra=(), keep=None):
    """run tck-reach; returns dict(reachable, nodes, seconds, maxrss_mb)."""
    fd, path = tempfile.mkstemp(suffix=".tck")
    with os.fdopen(fd, "w") as fh:
        fh.write(text)
    if keep:
        with open(keep, "w") as fh:
            fh.write(text)
    cmd = (f"ulimit -v {int(mem_gb*1024*1024)}; "
           f"exec {TCK} -a {algo} -l {label} -s bfs "
           + " ".join(extra) + f" {path}")
    t0 = time.time()
    # resource usage of the child
    import resource
    before = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    try:
        p = subprocess.run(["bash", "-c", cmd], capture_output=True,
                           text=True, timeout=timeout)
        out = p.stdout + p.stderr
    except subprocess.TimeoutExpired:
        os.unlink(path)
        return dict(reachable=None, err="timeout", seconds=time.time() - t0)
    os.unlink(path)
    rss = resource.getrusage(resource.RUSAGE_CHILDREN).ru_maxrss
    st = dict(re.findall(r"^(\w+)\s+(\S+)\s*$", out, re.M))
    res = dict(seconds=time.time() - t0, rc=p.returncode,
               maxrss_mb=rss / 1024.0 if rss > before else None)
    if "REACHABLE" in st:
        res["reachable"] = st["REACHABLE"] == "true"
    else:
        res["reachable"] = None
        res["err"] = out[-2000:]
    for k in ("VISITED_STATES", "STORED_STATES", "VISITED_TRANSITIONS",
              "RUNNING_TIME_SECONDS", "MEMORY_MAX_RSS"):
        if k in st:
            res[k] = st[k]
    return res


def witness(text, label="bad", show=None, mem_gb=3.5, timeout=3600):
    """concrete run to `label` (tck-reach -a reach -C concrete).  Returns a
    list of (time, {var: value}) at every change of a variable in `show`,
    plus the event vector of each step."""
    fd, path = tempfile.mkstemp(suffix=".tck")
    with os.fdopen(fd, "w") as fh:
        fh.write(text)
    cmd = (f"ulimit -v {int(mem_gb*1024*1024)}; "
           f"exec {TCK} -a reach -l {label} -s bfs -C concrete {path}")
    p = subprocess.run(["bash", "-c", cmd], capture_output=True, text=True,
                       timeout=timeout)
    os.unlink(path)
    nodes, edges = {}, {}
    for m in re.finditer(r'^\s*(\d+) \[(.*)\]\s*$', p.stdout, re.M):
        attrs = dict(re.findall(r'(\w+)="([^"]*)"', m.group(2)))
        nodes[int(m.group(1))] = attrs
    for m in re.finditer(r'^\s*(\d+) -> (\d+) \[(.*)\]\s*$', p.stdout, re.M):
        attrs = dict(re.findall(r'(\w+)="([^"]*)"', m.group(3)))
        edges[int(m.group(1))] = (int(m.group(2)), attrs)
    if not nodes:
        return None
    cur = next(k for k, a in nodes.items() if a.get("initial") == "true")
    t, out, prev = 0.0, [], None
    while True:
        iv = dict(kv.split("=") for kv in nodes[cur]["intval"].split(","))
        vals = {k: int(v) for k, v in iv.items() if show is None or k in show}
        if vals != prev:
            out.append((t, vals))
            prev = vals
        if cur not in edges:
            break
        nxt, ea = edges[cur]
        t += float(eval(ea.get("delay", "0").replace("/", "/")))
        out[-1] = out[-1]
        cur = nxt
    return out
