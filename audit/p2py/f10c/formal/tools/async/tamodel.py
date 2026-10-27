"""tamodel.py -- gate-level circuits as networks of timed automata, emitted as
PRISM-language MDPs with DIGITAL-CLOCK semantics, model-checked with Storm.

Probe C-12b (formal/notes/C-12b-async-tools.md).  UPPAAL, TChecker and
Workcraft could not be obtained in this sandbox (see the notes), so this file
is the timed-automata front end and Storm (stormpy 2.0.0, PyPI wheel) is the
checker.

Semantics (one timed automaton per node):
  * every node x is a Boolean output with a next-value function f_x(state);
    x is EXCITED when f_x != x.
  * each node has a clock c_x that runs while x is excited and is reset to 0
    whenever x becomes excited or stops being excited (INERTIAL bounded delay:
    an excitation withdrawn before the node fires is swallowed).
  * x may fire (x := !x) once c_x >= lo, and time may not pass while some
    excited node has c_x == hi.  Rise and fall have separate [lo,hi].
    hi = None means no deadline (a free environment move).
  * time advances in integer ticks (one synchronous 'tick' command).  For
    closed timed automata with integer bounds, reachability under the digital
    clock semantics equals reachability under dense time (Henzinger, Manna,
    Pnueli 1992), so these checks are exact for integer delay bounds.
  * the MDP's nondeterminism is the scheduler of delays and interleavings;
    Pmax=? [F bad] = 0 means "no delay choice inside the bounds reaches bad",
    Pmax = 1 means a violating run exists.

LUT nodes take the REAL INIT constant and pin map from cells/rtl and build the
next-value function by Shannon expansion over the pins (no hand-simplified
Boolean equation is used anywhere).
"""

from dataclasses import dataclass, field
from typing import Callable, Dict, List, Optional, Tuple

Expr = Callable[[Dict[str, str]], str]   # env: node name -> PRISM expr string


def var(n: str) -> Expr:
    return lambda env: env.get(n, n)


def const(b: bool) -> Expr:
    return lambda env: "true" if b else "false"


def lut(init: int, pins: List[Optional[str]], out: str = "O6") -> Expr:
    """6-input LUT (pins I0..I5; None = tied 0, '1' = tied 1).  out in
    {'O6','O5'}: O6 reads INIT[63:0] by I5..I0; O5 reads INIT[31:0] by I4..I0
    (LUT6_2 with I5 tied high, as in bd_arb.v)."""
    pins = list(pins) + [None] * (6 - len(pins))

    def bit(idx):
        return (init >> idx) & 1

    def build(k, idx, env):
        # k: next pin to decide (descending), idx: partial index
        if k < 0:
            return "true" if bit(idx) else "false"
        if out == "O5" and k == 5:
            return build(k - 1, idx, env)          # O5 ignores I5
        p = pins[k]
        if p is None:
            return build(k - 1, idx, env)
        if p == "1":
            return build(k - 1, idx | (1 << k), env)
        hi = build(k - 1, idx | (1 << k), env)
        lo = build(k - 1, idx, env)
        if hi == lo:
            return hi
        return f"({env.get(p, p)} ? {hi} : {lo})"

    return lambda env: build(5, 0, env)


@dataclass
class Node:
    name: str
    f: Expr
    init: bool
    rise: Tuple[int, Optional[int]]
    fall: Tuple[int, Optional[int]]
    watch_hazard: bool = False     # flag if excitation is withdrawn unfired
    on_fire: List[Tuple[str, Expr]] = field(default_factory=list)
    # on_fire: (flag, condition evaluated in the PRE-state) -> flag |= cond
    on_fire_set: List[Tuple[str, Expr]] = field(default_factory=list)
    # on_fire_set: (monitor var, expr in the PRE-state) -> var := expr
    mode: str = "inertial"   # or "transport": FIFO pure delay, queue of K
    K: int = 2               # in-flight edges; ovf_<name> flags overflow
    pending0: bool = False   # transport: one edge to !init already in flight


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

    # ------------------------------------------------------------------
    def _exc(self, n: Node, env) -> str:
        return f"(({n.f(env)}) != {env.get(n.name, n.name)})"

    def _cap(self, n):
        his = [d[1] if d[1] is not None else d[0] for d in (n.rise, n.fall)]
        return max(max(his), 1)

    # transport-queue helpers.  Q = (len_expr, [(v_expr, c_expr)] * K)
    @staticmethod
    def _Q(n):
        return (f"len_{n.name}",
                [(f"v_{n.name}_{j}", f"c_{n.name}_{j}") for j in range(n.K)])

    @staticmethod
    def _Qshift(n):
        L, sl = Circuit._Q(n)
        return (f"({L}-1)", sl[1:] + [("false", "0")])

    @staticmethod
    def _chain(L, items, default):
        e = default
        for k in reversed(range(len(items))):
            e = f"({L}={k} ? {items[k]} : {e})"
        return e

    def _tp_updates(self, m, env_post, Q, out_post):
        """updates of transport node m's queue after a move whose post-state
        outputs are env_post, starting from queue Q."""
        L, sl = Q
        K = m.K
        fp = f"({m.f(env_post)})"
        lastv = self._chain(L, [out_post] + [v for v, _ in sl], "false")
        prevv = self._chain(L, ["false", out_post] + [v for v, _ in sl[:-1]],
                            "false")
        clast = self._chain(L, ["0"] + [c for _, c in sl], "0")
        push = f"({fp} != {lastv})"
        cancel = f"({push} & {L}>=1 & {clast}=0 & {fp}={prevv})"
        add = f"({push} & !{cancel})"
        ups = [f"(len_{m.name}'={cancel} ? {L}-1 : ({add} ? min({L}+1,{K}) : {L}))",
               f"(ovf_{m.name}'=ovf_{m.name} | ({add} & {L}>={K}))",
               # a second edge queued behind an undelivered one: the node's
               # excitation reversed within its delay (a runt at its input)
               f"(mlt_{m.name}'=mlt_{m.name} | ({add} & {L}>=1))"]
        for j in range(K):
            v, c = sl[j]
            ups.append(f"(v_{m.name}_{j}'=({add} & {L}={j}) ? {fp} : {v})")
            ups.append(f"(c_{m.name}_{j}'=({add} & {L}={j}) ? 0 : {c})")
        return ups

    def _others(self, n, post, ident):
        ups = []
        for m in self.nodes:
            if m is n:
                continue
            if m.mode == "inertial":
                eb = self._exc(m, ident)
                ea = self._exc(m, post)
                ups.append(f"(c_{m.name}'=({eb} & {ea}) ? c_{m.name} : 0)")
                if m.watch_hazard:
                    ups.append(f"(hz_{m.name}'=hz_{m.name} | ({eb} & !{ea}))")
            else:
                ups += self._tp_updates(m, post, self._Q(m), m.name)
        for fl, cond in n.on_fire:
            ups.append(f"({fl}'={fl} | ({cond(ident)}))")
        for fl, ex in n.on_fire_set:
            ups.append(f"({fl}'={ex(ident)})")
        return ups

    def prism(self) -> str:
        L = ["mdp", "", "module circuit"]
        for n in self.nodes:
            L.append(f"  {n.name} : bool init {'true' if n.init else 'false'};")
            if n.mode == "inertial":
                L.append(f"  c_{n.name} : [0..{self._cap(n)}] init 0;")
            else:
                L.append(f"  len_{n.name} : [0..{n.K}] init {1 if n.pending0 else 0};")
                L.append(f"  ovf_{n.name} : bool init false;")
                L.append(f"  mlt_{n.name} : bool init false;")
                for j in range(n.K):
                    v0 = "true" if (j == 0 and n.pending0 and not n.init) else "false"
                    L.append(f"  v_{n.name}_{j} : bool init {v0};")
                    L.append(f"  c_{n.name}_{j} : [0..{self._cap(n)}] init 0;")
        for fl in self.flags + [f"hz_{n.name}" for n in self.nodes
                                if n.watch_hazard and n.mode == "inertial"]:
            L.append(f"  {fl} : bool init false;")
        L.append("")
        ident: Dict[str, str] = {}
        # --- fire commands
        for n in self.nodes:
            if n.mode == "inertial":
                exc = self._exc(n, ident)
                for tgt, (lo, _hi) in ((True, n.rise), (False, n.fall)):
                    guard = (f"{exc} & {n.name}={'false' if tgt else 'true'}"
                             f" & c_{n.name}>={lo}")
                    post = {n.name: ("true" if tgt else "false")}
                    ups = [f"({n.name}'={'true' if tgt else 'false'})",
                           f"(c_{n.name}'=0)"] + self._others(n, post, ident)
                    L.append(f"  [] {guard} -> " + " & ".join(ups) + ";")
            else:
                h = f"v_{n.name}_0"
                # the next queued edge already due: it overtakes the head and
                # the pulse between them is swallowed (pulse shrinkage with
                # asymmetric rise/fall delays; no zero-width output pulses)
                nxt = (f"(len_{n.name}>=2 & c_{n.name}_1 >= "
                       f"(v_{n.name}_1 ? {n.rise[0]} : {n.fall[0]}))")
                if n.K >= 2:
                    ann = [f"(len_{n.name}'=len_{n.name}-2)"]
                    for j in range(n.K):
                        src = j + 2
                        v = f"v_{n.name}_{src}" if src < n.K else "false"
                        c = f"c_{n.name}_{src}" if src < n.K else "0"
                        ann.append(f"(v_{n.name}_{j}'={v})")
                        ann.append(f"(c_{n.name}_{j}'={c})")
                    L.append(f"  [] {nxt} -> " + " & ".join(ann) + ";")
                guard = (f"len_{n.name}>0 & c_{n.name}_0 >= "
                         f"({h} ? {n.rise[0]} : {n.fall[0]})"
                         + (f" & !{nxt}" if n.K >= 2 else ""))
                post = {n.name: h}
                ups = [f"({n.name}'={h})"]
                ups += self._tp_updates(n, post, self._Qshift(n), h)
                ups += self._others(n, post, ident)
                L.append(f"  [] {guard} -> " + " & ".join(ups) + ";")
        # --- time step
        block = []
        for n in self.nodes:
            if n.mode == "inertial":
                exc = self._exc(n, ident)
                for tgt, (_lo, hi) in ((True, n.rise), (False, n.fall)):
                    if hi is not None:
                        block.append(f"({exc} & {n.name}={'false' if tgt else 'true'}"
                                     f" & c_{n.name}>={hi})")
            else:
                assert n.rise[1] is not None and n.fall[1] is not None
                block.append(f"(len_{n.name}>0 & c_{n.name}_0 >= "
                             f"(v_{n.name}_0 ? {n.rise[1]} : {n.fall[1]}))")
        g = "!(" + " | ".join(block) + ")" if block else "true"
        ups = []
        for n in self.nodes:
            cap = self._cap(n)
            if n.mode == "inertial":
                exc = self._exc(n, ident)
                ups.append(f"(c_{n.name}'={exc} ? min(c_{n.name}+1,{cap}) : 0)")
            else:
                for j in range(n.K):
                    ups.append(f"(c_{n.name}_{j}'=len_{n.name}>{j} ? "
                               f"min(c_{n.name}_{j}+1,{cap}) : 0)")
        L.append(f"  [tick] {g} -> " + " & ".join(ups) + ";")
        L.append("endmodule")
        return "\n".join(L) + "\n"


def check(prog_text: str, props: Dict[str, str]):
    """Build the MDP with Storm and evaluate each property in the initial
    state.  Returns ({name: value}, nstates, ntransitions, seconds)."""
    import time
    import stormpy
    t0 = time.time()
    import tempfile, os
    fd, path = tempfile.mkstemp(suffix=".prism")
    with os.fdopen(fd, "w") as fh:
        fh.write(prog_text)
    prog = stormpy.parse_prism_program(path)
    os.unlink(path)
    plist = stormpy.parse_properties(";".join(props.values()), prog)
    model = stormpy.build_model(prog, plist)
    out = {}
    for name, p in zip(props, plist):
        r = stormpy.model_checking(model, p)
        out[name] = r.get_value(model.initial_states[0])
    return out, model.nr_states, model.nr_transitions, time.time() - t0


def witness(prog_text: str, target: str, show, maxlen=5000):
    """A run reaching `target` (a PRISM state formula), read off Storm's
    optimal scheduler for Pmax=? [F target].  Returns a list of
    (time, {var: value}) at every change of a variable in `show`."""
    import tempfile, os
    import stormpy
    fd, path = tempfile.mkstemp(suffix=".prism")
    with os.fdopen(fd, "w") as fh:
        fh.write(prog_text)
    prog = stormpy.parse_prism_program(path)
    os.unlink(path)
    props = stormpy.parse_properties(f"Pmax=? [F {target}]", prog)
    opts = stormpy.BuilderOptions([p.get_raw_formula() for p in props])
    opts.set_build_state_valuations()
    opts.set_build_choice_labels()
    model = stormpy.build_model(prog, options=opts)
    res = stormpy.model_checking(model, props[0], extract_scheduler=True)
    sched = res.get_scheduler()
    s = model.initial_states[0]
    if res.get_value(s) == 0:
        return None
    out, t, prev = [], 0, None
    for _ in range(maxlen):
        val = _js(model.state_valuations.to_json(s))
        vals = {k: val[k] for k in show if k in val}
        if vals != prev:
            out.append((t, vals))
            prev = vals
        if res.get_value(s) == 1 and _sat(val, target):
            break
        ch = sched.get_choice(s).get_deterministic_choice()
        row = model.transition_matrix.get_row(
            model.transition_matrix.get_row_group_start(s) + ch)
        labs = model.choice_labeling.get_labels_of_choice(
            model.transition_matrix.get_row_group_start(s) + ch) \
            if model.has_choice_labeling() else set()
        if "tick" in labs:
            t += 1
        s = [e.column for e in row][0]
    return out


def _sat(val, target):
    expr = target.replace("&", " and ").replace("|", " or ").replace("!", " not ")
    return bool(eval(expr, {}, {k: bool(v) for k, v in val.items()}))


def _js(x):
    import json
    return x if isinstance(x, dict) else json.loads(str(x))
