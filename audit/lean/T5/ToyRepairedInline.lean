import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

/-!
# Formal.Target.Spec — THE statement: the gcd_hw bitstream computes gcd

Shard A, 2026-11-01. `formal/PROGRAM.md`, "THE goal". This file holds only
definitions: no theorem, no proof. It is the statement every shard works
toward. Changing it needs a journaled reason and an audit row.

**Status (v1, 2026-11-01 07:55 UTC).** Part I (sections 1-6: the semantics, H_DELAY,
H_PRIM, H_ARB, H_ENV, the conclusion, `NetCorrect` and `NetCorrectSeq`) compiles
(`formal/check.sh`) and is FROZEN from this commit: a change needs a journaled
reason and an audit row; additions that do not change an existing definition are
journaled. Part II (section 7: the decoder in Lean, the round trip, the theorem
about the target's bytes) is still a stub, so the statement is so far "for the
netlist `N`", not yet "for the bitstream". See `formal/target/STATUS.md`.

## In plain words

The circuit is a set of **nodes** (every routing node, site pin and LUT output
of the configured fabric that the target uses) and a set of **gates**. Every
gate is a LUT-like primitive: `k` input nodes, one output node, an INIT table,
and for each input pin one **arc** (the delay from that pin to the output) with
its four prjxray numbers `FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX` in ps. A LUT
pin, a pip (a 1-input buffer, INIT `0b10`), a wire, a site hop, a MUXF7/F8
input and a CARRY4 arc are all gates of this one kind (H_PRIM: a primitive is
the Boolean function of its inputs, each input read through its own delay).

A **behaviour** is a Boolean trace for every node, time in ps (`Nat`). A gate
holds in a behaviour if there are, for each of its pins, a non-decreasing read
time `f i t ≤ t` such that, for every time `t` past the gate's longest delay,
(a) the delay `t - f i t` is admissible for the pin's arc (H_DELAY), and (b) the
output at `t` is INIT at the address formed by pin `i` read at `f i t`. Each pin
has its own read time, so input skew glitches the output exactly as a mux tree
fed through unequal pin delays does; a read time that jumps swallows a pulse
(inertial behaviour), one that does not jump copies it (transport). Before the
gate's longest delay the output is arbitrary: any power-up state.

**H_DELAY(g, κ).** One shared corner `c ∈ [0,1]` for the whole die. Every delay
lies in the prjxray band widened by the guard `g ≥ 1`, `[FAST_MIN/g,
SLOW_MAX·g]`, and within the local scatter `κ ≥ 0` of the corner-`c` window,
`[(1-κ)·lerp(FAST_MIN,SLOW_MIN,c), (1+κ)·lerp(FAST_MAX,SLOW_MAX,c)]`. A large
`κ` switches the correlation off (the band alone remains); larger `g` and `κ`
are weaker hypotheses, so the theorem's value is the largest `g, κ` for which
it holds.

**H_ARB(T).** For every arbiter of the target, given by its state node and the
other inputs of its state LUT (requests, reset, hold): whenever those inputs are
constant on `[t1, t2]`, the state node is constant on `[t1 + T, t2]`.

**H_ENV.** The environment drives the reset and the request and data nodes of
the input channels `a`, `b`, `start` and the acknowledge nodes of the output
channels `out0`, `end`. Reset is high on `[0, R)` and low from `R` on. Each
channel, on its own, follows the four-phase protocol from `R` on, with no
timing assumption except two stated margins: the input data is held from `su`
ps before its request rises until its acknowledge has FALLEN again (broad
four-phase; holding it only until the acknowledge rises breaks the target in
simulation, see `formal/FOR-RESEARCH.md` 2), and the output
acknowledge does not rise earlier than `Δo` ps after the output request rose.
(The kernel's `out0_req` leads `out0_data` by a latch arc, so some `Δo` is
inherent at this boundary; the rig pads it with a delay line.) The channels are
independent: pair `k + 1` may be offered on `a` as soon as the `a` handshake of
pair `k` is complete, whatever `out0` is doing (pipelining). The environment
is live (it eventually takes every step the protocol allows it), and it offers
`n ≤ ∞` pairs.

**Conclusion.** Every behaviour of the circuit with such an environment, from
`R` on: the circuit's acknowledge and request nodes follow the protocol; the
`k`-th value on `out0` (read from `Δo` after its request rises until its
acknowledge rises) is `Nat.gcd (a k) (b k)` for every `k < n`; every offered
input handshake completes and `out0` and `end` complete one handshake per
pair; if `n` is finite, `out0` completes exactly `n` and every boundary node
is eventually low for ever (idle, ready for more).

## What this does NOT cover
* Analog effects (no slew, no metastability voltage, no MTBF): digital model only.
* A value at a node is `true` or `false` at every ps. A slow or runt input that a
  real LUT might read as either value at different pins is covered (pins are
  independent); an output that is neither value is not (no Kleene `X` here).
* Delays are per gate pin, not per (pin, edge): prjxray-db has no rise/fall split.
-/

namespace Formal.Target

/-! ## 1. The netlist -/

/-- The four prjxray delay numbers of one arc, in ps:
`(FAST_MIN::FAST_MAX)(SLOW_MIN::SLOW_MAX)`. -/
structure Arc where
  fmin : Nat
  fmax : Nat
  smin : Nat
  smax : Nat
  deriving Repr, DecidableEq, Inhabited

/-- One gate: `k` pins, INIT (bit `a` is the output at address `a`, pin 0 the
least significant address bit), pin nodes, one arc per pin, the output node.
`name` is provenance only (the FASM feature or site/BEL it came from). -/
structure Gate where
  name : String
  k : Nat
  init : Nat
  ins : List Nat
  arcs : List Arc
  out : Nat
  deriving Repr, Inhabited

/-- A decoded netlist: nodes `0 .. n-1` with physical names, and gates. -/
structure Net where
  n : Nat
  names : List String
  gates : List Gate
  deriving Repr, Inhabited

/-- Well-formed: pin lists and arc lists have length `k`, every node index is in
range, every band is ordered, and no node has two drivers. -/
def Net.WF (N : Net) : Prop :=
  (∀ g ∈ N.gates, g.ins.length = g.k ∧ g.arcs.length = g.k ∧ g.out < N.n ∧
      (∀ i ∈ g.ins, i < N.n) ∧ g.init < 2 ^ 2 ^ g.k ∧
      (∀ e ∈ g.arcs, e.fmin ≤ e.fmax ∧ e.smin ≤ e.smax ∧ e.fmin ≤ e.smin ∧ e.fmax ≤ e.smax)) ∧
  (N.gates.map Gate.out).Nodup

/-! ## 2. Behaviours and the gate relation (H_PRIM, H_DELAY) -/

/-- A signal: its value at every ps. -/
abbrev Sig := Nat → Bool

/-- A behaviour: a signal for every node. -/
abbrev Beh := Nat → Sig

/-- The delay model's parameters: guard `g ≥ 1`, scatter `κ ≥ 0`, corner `c ∈ [0,1]`. -/
structure DelayPar where
  g : ℚ
  κ : ℚ
  deriving Repr

def lerp (a b : Nat) (c : ℚ) : ℚ := (1 - c) * a + c * b

/-- **H_DELAY(g, κ) at corner `c`**: delay `d` (ps) is admissible for arc `e`. -/
def Adm (p : DelayPar) (c : ℚ) (e : Arc) (d : Nat) : Prop :=
  (e.fmin : ℚ) / p.g ≤ d ∧ (d : ℚ) ≤ e.smax * p.g ∧
  (1 - p.κ) * lerp e.fmin e.smin c ≤ d ∧ (d : ℚ) ≤ (1 + p.κ) * lerp e.fmax e.smax c

/-- The address formed by `k` pin values (pin 0 = bit 0). -/
def addr : (k : Nat) → (Nat → Bool) → Nat
  | 0, _ => 0
  | k + 1, v => addr k v + (if v k then 2 ^ k else 0)

/-- The time from which a gate's relation is required: its longest band end
(before that, a read could fall before time 0; the output is arbitrary there,
which is any power-up state). -/
def Gate.start (p : DelayPar) (g : Gate) : Nat :=
  (g.arcs.map fun e => (Rat.ceil ((e.smax : ℚ) * p.g)).toNat).foldr max 0

/-- **The gate relation (H_PRIM with H_DELAY).** Pin `i` is read at time `f i t`,
non-decreasing in `t`; from the gate's start on, every read delay is admissible
and the output is the INIT bit at the address of the reads. -/
def GateOK (p : DelayPar) (c : ℚ) (g : Gate) (x : Beh) : Prop :=
  ∃ f : Nat → Nat → Nat,
    (∀ i, i < g.k → Monotone (f i)) ∧
    ∀ t, g.start p ≤ t →
      (∀ i, i < g.k → f i t ≤ t ∧ Adm p c (g.arcs.getD i default) (t - f i t)) ∧
      x g.out t = g.init.testBit (addr g.k fun i => x (g.ins.getD i 0) (f i t))

/-- **A behaviour of the netlist**: one corner `c ∈ [0,1]` for the die, and every
gate holds. Nodes driven by no gate (environment inputs, floating nodes) are
unconstrained here. -/
def Behaves (p : DelayPar) (N : Net) (x : Beh) : Prop :=
  ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ g ∈ N.gates, GateOK p c g x

/-! ## 3. The boundary and the arbiters (named nodes of the target) -/

/-- An input channel: request and data driven by the environment, acknowledge by
the circuit. `data` lists the data nodes, bit 0 first (empty for `start`). -/
structure InCh where
  req : Nat
  ack : Nat
  data : List Nat
  deriving Repr

/-- An output channel: request and data driven by the circuit, acknowledge by the
environment. -/
structure OutCh where
  req : Nat
  ack : Nat
  data : List Nat
  deriving Repr

/-- The kernel's boundary in the target (node indices of `N`). `env` lists the
nodes the environment drives; their drivers in the bitstream (the rig's) are
removed. Channels may share nodes and a data list may name a node that the
circuit drives (a constant tie), exactly as the target is wired; see the
target notes below. -/
structure Boundary where
  rst : Nat
  a : InCh
  b : InCh
  start : InCh
  out0 : OutCh
  pend : OutCh
  env : List Nat
  deriving Repr

/-- The nodes the environment drives. -/
def Boundary.envNodes (B : Boundary) : List Nat := B.env

/-- The boundary is consistent: the environment drives exactly the reset, the
input requests, the output acknowledges and the input data nodes that the
circuit does not tie (a data node outside `env` must be driven by a gate). -/
def Boundary.OK (N : Net) (B : Boundary) : Prop :=
  B.rst ∈ B.env ∧ B.a.req ∈ B.env ∧ B.b.req ∈ B.env ∧ B.start.req ∈ B.env ∧
  B.out0.ack ∈ B.env ∧ B.pend.ack ∈ B.env ∧
  (∀ v ∈ B.env, v = B.rst ∨ v = B.a.req ∨ v = B.b.req ∨ v = B.start.req ∨ v = B.out0.ack ∨
      v = B.pend.ack ∨ v ∈ B.a.data ∨ v ∈ B.b.data) ∧
  (∀ v ∈ B.a.data ++ B.b.data, v ∉ B.env → v ∈ N.gates.map Gate.out) ∧
  B.a.data.length = 32 ∧ B.b.data.length = 32 ∧ B.out0.data.length = 32

/-- **The circuit**: the decoded netlist without the gates that drive an
environment node (in the bitstream those are the rig's; the theorem replaces
the rig by every environment that obeys H_ENV). -/
def circuit (N : Net) (B : Boundary) : Net :=
  { N with gates := N.gates.filter fun g => g.out ∉ B.envNodes }

/-- One arbiter: its state (decision) node `q`, the output of the arbiter's state
LUT (`bd_arbiter.ustate`, O6), and `ins`, the nodes that LUT reads other than its
own feedback (in `bd_arbiter`: the two requests, the reset and the hold input `A0`).
(Changed 2026-11-01, before any proof used it: the first version listed only the
two requests, which wrongly forbade `q` to move at `A0`'s fall with both requests
held, a normal arbiter step.) -/
structure ArbNodes where
  q : Nat
  ins : List Nat
  deriving Repr

/-- A signal is constant on `[t1, t2]`. -/
def ConstOn (s : Sig) (t1 t2 : Nat) : Prop := ∀ t, t1 ≤ t → t ≤ t2 → s t = s t1

/-- **H_ARB(T)**: whenever every input of the arbiter's state LUT (other than its
feedback) is constant on `[t1, t2]`, the state node is constant on `[t1 + T, t2]`:
the internal race resolves within `T` once its inputs stop moving. -/
def ArbOK (T : Nat) (A : List ArbNodes) (x : Beh) : Prop :=
  ∀ a ∈ A, ∀ t1 t2, (∀ n ∈ a.ins, ConstOn (x n) t1 t2) → ConstOn (x a.q) (t1 + T) t2

/-! ## 4. Four-phase handshakes -/

/-- Number of rising edges of `s` at times in `(R, t]` (edges before the end of
reset, power-up glitches included, are not counted). -/
def rises (s : Sig) (R : Nat) : Nat → Nat
  | 0 => 0
  | t + 1 => rises s R t + (if R ≤ t ∧ s t = false ∧ s (t + 1) = true then 1 else 0)

/-- The value of a data bus (bit 0 first) at time `t`. -/
def busVal (x : Beh) (d : List Nat) (t : Nat) : Nat :=
  (d.zipIdx.map fun (n, i) => if x n t then 2 ^ i else 0).sum

/-- The side that drives `r` moves it only as four-phase allows, from `t0` on:
`r` rises only while `a` is low, falls only while `a` is high. -/
def ReqMoves (r a : Sig) (t0 : Nat) : Prop :=
  ∀ t, t0 ≤ t → r (t + 1) ≠ r t → r t = a t

/-- The side that drives `a` moves it only as four-phase allows, from `t0` on:
`a` rises only while `r` is high, falls only while `r` is low. -/
def AckMoves (r a : Sig) (t0 : Nat) : Prop :=
  ∀ t, t0 ≤ t → a (t + 1) ≠ a t → a t ≠ r t

/-- From `t0` on, whenever the driver of `r` may move, it eventually does:
`r = a` is not kept for ever. `more` says whether it still has something to
send (a rise needs it; a fall is always owed). -/
def ReqLive (r a : Sig) (t0 : Nat) (more : Nat → Prop) : Prop :=
  ∀ t, t0 ≤ t → r t = a t → (r t = true ∨ more (rises r t0 t)) → ∃ s, t ≤ s ∧ r s ≠ a s

/-- From `t0` on, the driver of `a` eventually follows `r`. -/
def AckLive (r a : Sig) (t0 : Nat) : Prop :=
  ∀ t, t0 ≤ t → a t ≠ r t → ∃ s, t ≤ s ∧ a s = r s

/-- The offer counts: `n = none` is an infinite sequence, `some m` exactly `m` items. -/
def Offered (n : Option Nat) (k : Nat) : Prop := match n with
  | none => True
  | some m => k < m

/-! ## 5. H_ENV -/

/-- The environment's obligations on an input channel: request low on `[0, R]`;
from `R` on it moves only as allowed, rises at most `n` times, is live; from `su`
ps before each rise until the acknowledge has fallen again (while the request or
the acknowledge is high: the "broad" four-phase data rule), the data holds item
`k` of `vals` (`k` = rises so far minus one). -/
def EnvIn (x : Beh) (ch : InCh) (R su : Nat) (n : Option Nat) (vals : Nat → Nat) : Prop :=
  (∀ t, t ≤ R → x ch.req t = false) ∧
  ReqMoves (x ch.req) (x ch.ack) R ∧
  ReqLive (x ch.req) (x ch.ack) R (Offered n) ∧
  (∀ t, R ≤ t → x ch.req t = true → Offered n (rises (x ch.req) R t - 1)) ∧
  (∀ t, R ≤ t → x ch.req t = false → x ch.req (t + 1) = true →
      ∀ s, t + 1 - su ≤ s → s ≤ t + 1 → busVal x ch.data s = vals (rises (x ch.req) R (t + 1) - 1)) ∧
  (∀ t, R ≤ t → (x ch.req t = true ∨ x ch.ack t = true) → 1 ≤ rises (x ch.req) R t →
      busVal x ch.data t = vals (rises (x ch.req) R t - 1))

/-- The environment's obligations on an output channel: acknowledge low on
`[0, R]`; from `R` on it moves only as allowed, live, and it rises no earlier than `Δo` ps
after the request rose. -/
def EnvOut (x : Beh) (ch : OutCh) (R Δo : Nat) : Prop :=
  (∀ t, t ≤ R → x ch.ack t = false) ∧
  AckMoves (x ch.req) (x ch.ack) R ∧
  AckLive (x ch.req) (x ch.ack) R ∧
  (∀ t, R ≤ t → x ch.ack t = false → x ch.ack (t + 1) = true →
      ∀ s, t + 1 - Δo ≤ s → s ≤ t + 1 → x ch.req s = true)

/-- **H_ENV**: reset high on `[0, R)`, low from `R` on; the three input channels
and the two output channels each obey their side of the protocol; `n` pairs
are offered, with values `va`, `vb` below `2^31`. -/
def Env (x : Beh) (B : Boundary) (R su Δo : Nat) (n : Option Nat) (va vb : Nat → Nat) : Prop :=
  (∀ t, t < R → x B.rst t = true) ∧ (∀ t, R ≤ t → x B.rst t = false) ∧
  (∀ k, Offered n k → va k < 2 ^ 31 ∧ vb k < 2 ^ 31) ∧
  EnvIn x B.a R su n va ∧ EnvIn x B.b R su n vb ∧ EnvIn x B.start R su n (fun _ => 0) ∧
  EnvOut x B.out0 R Δo ∧ EnvOut x B.pend R Δo

/-! ## 6. The conclusion -/

/-- The circuit's obligations on an input channel from `R` on. -/
def CircIn (x : Beh) (ch : InCh) (R : Nat) : Prop :=
  x ch.ack R = false ∧ AckMoves (x ch.req) (x ch.ack) R ∧ AckLive (x ch.req) (x ch.ack) R

/-- The circuit's obligations on an output channel from `R` on (request side). -/
def CircOut (x : Beh) (ch : OutCh) (R : Nat) (n : Option Nat) : Prop :=
  x ch.req R = false ∧ ReqMoves (x ch.req) (x ch.ack) R ∧ ReqLive (x ch.req) (x ch.ack) R (Offered n) ∧
  (∀ t, R ≤ t → x ch.req t = true → Offered n (rises (x ch.req) R t - 1))

/-- **Correct**: safety and liveness at the boundary, from `R` on.
* the acknowledges of `a`, `b`, `start` follow the protocol and are live;
* `out0` and `end` requests follow the protocol, rise once per offered pair
  and no more, and are live (every owed rise and fall happens);
* while `out0`'s `k`-th request is high, from `Δo` after it rose until its
  acknowledge rises, the data is `Nat.gcd (va k) (vb k)`;
* if `n = some m`, every boundary node is eventually low for ever, and `out0`
  and `end` then have risen exactly `m` times. -/
def Correct (x : Beh) (B : Boundary) (R Δo : Nat) (n : Option Nat) (va vb : Nat → Nat) : Prop :=
  CircIn x B.a R ∧ CircIn x B.b R ∧ CircIn x B.start R ∧
  CircOut x B.out0 R n ∧ CircOut x B.pend R n ∧
  (∀ t0 t, R ≤ t0 → x B.out0.req t0 = false → x B.out0.req (t0 + 1) = true →
      t0 + 1 + Δo ≤ t → (∀ s, t0 + 1 ≤ s → s ≤ t → x B.out0.req s = true ∧ x B.out0.ack s = false) →
      busVal x B.out0.data t =
        Nat.gcd (va (rises (x B.out0.req) R (t0 + 1) - 1)) (vb (rises (x B.out0.req) R (t0 + 1) - 1))) ∧
  (∀ m, n = some m → ∃ T, ∀ t, T ≤ t →
      (∀ v ∈ [B.a.req, B.a.ack, B.b.req, B.b.ack, B.start.req, B.start.ack,
              B.out0.req, B.out0.ack, B.pend.req, B.pend.ack], x v t = false) ∧
      rises (x B.out0.req) R t = m ∧ rises (x B.pend.req) R t = m)

/-- **The statement for a decoded netlist `N`** with boundary `B` and arbiters `A`:
for every delay assignment allowed by H_DELAY(g, κ) (and H_PRIM, built into
`Behaves`), every arbiter behaviour allowed by H_ARB(T), and every environment
allowed by H_ENV with reset length `R`, margins `su`, `Δo`, any number of pairs
`n` and any values: the boundary is correct. -/
def NetCorrect (N : Net) (B : Boundary) (A : List ArbNodes) (p : DelayPar) (T R su Δo : Nat) : Prop :=
  ∀ (x : Beh) (n : Option Nat) (va vb : Nat → Nat),
    Behaves p (circuit N B) x → ArbOK T A x → Env x B R su Δo n va vb → Correct x B R Δo n va vb

/-- **The sequential environment** (an extra restriction of `Env`): each input
request rises for the `k+1`-th time only after `out0` has completed `k`
handshakes (its acknowledge has risen `k` times and both its request and
acknowledge are low again). gcd_rig.v's env and gcd_bench.v's FSM are of this
kind. -/
def SeqEnv (x : Beh) (B : Boundary) (R : Nat) : Prop :=
  ∀ ch ∈ [B.a, B.b, B.start], ∀ t, R ≤ t → x ch.req t = false → x ch.req (t + 1) = true →
    rises (x ch.req) R t ≤ rises (x B.out0.ack) R t ∧ x B.out0.req t = false ∧ x B.out0.ack t = false

/-- **The sequential statement**: `NetCorrect` for sequential environments only. -/
def NetCorrectSeq (N : Net) (B : Boundary) (A : List ArbNodes) (p : DelayPar) (T R su Δo : Nat) : Prop :=
  ∀ (x : Beh) (n : Option Nat) (va vb : Nat → Nat),
    Behaves p (circuit N B) x → ArbOK T A x → Env x B R su Δo n va vb → SeqEnv x B R →
      Correct x B R Δo n va vb

/-! ## 7. Part II (stub): the target

**Status of the two statements for the target (2026-11-01).** `NetCorrect` (the
owner's pipelined environment) is expected FALSE for the target: in simulation of
the netlist decoded from the target's bits, with every arc inside its band, pipelined
pairs come out reordered or deadlock (`formal/FOR-RESEARCH.md` 2 and C1; shard C's
`Formal/Net/PipeGcd.lean` proves the reordering at token level). The deliverable for
it is a Lean-checked counterexample behaviour. `NetCorrectSeq` is the statement that
can still be true, and the one to prove.

**How the target's boundary is wired (found 2026-11-01, yosys netlist of the target
build).** THE goal's wording ("every `a, b < 2^31`", independent channels) does not fit
this bitstream, and the statement above is written for what the bitstream is:
* `a_req`, `b_req` and `start_req` are ONE node: the rig's `bd_fork` is
  `assign req_out = {N{req}}`. So `B.a.req = B.b.req = B.start.req`, and `Env`'s
  per-channel rules, conjoined, say: the shared request rises only when all three
  acknowledges are low and falls only when all three are high. Offering pair `k+1`
  "as soon as the input handshake of pair `k` completes" is still allowed and covered,
  but it is the handshake of all three channels together. (gcd_rig.v's header says
  `start` is acknowledged only at completion; on the decoded target it is not: 141 ns
  vs 934 ns, so the target does take a second pair early, and then reorders.)
* The rig feeds the kernel from a 16-entry table, and yosys merged equal bits: of
  `a`'s 32 bits only 19 are distinct nodes and `a[31]` is the constant 0; of `b`'s,
  21 distinct nodes and 7 bits are the constant 0 (exact map:
  `formal/target/BOUNDARY.md`). `Env` requires the bus to show `va k`, so it holds
  only for pairs the
  wiring can represent, which include all 16 vectors. For any other pair the theorem
  says nothing: this bitstream cannot be offered it.

To be written with the decoder (`formal/target/`):

To be written with the decoder (`formal/target/`):
* `targetFasm : List String`: the FASM lines of `formal/target/gcd_hw_03e82630.fasm`;
* `decode : List String → Option (Net × Boundary × List ArbNodes)`, a Lean function
  over the FASM features and the prjxray tables it needs (tile wires to nodes, pip
  and site arcs with their delay numbers), generated as data from prjxray-db
  (H_DECODE: those tables say what the bits mean);
* `encode : Net → List String` and the round trip `encode N ~ targetFasm`, so a
  decoder that drops or invents a feature fails the build;
* **THE theorem**: `decode targetFasm = some (N, B, A) ∧ N.WF ∧ B.OK N ∧ NetCorrectSeq N B A p T R su Δo`,
  for stated `p = ⟨g, κ⟩`, `T`, `R`, `su`, `Δo`; and the refutation
  `decode targetFasm = some (N, B, A) ∧ ¬ NetCorrect N B A p T R su Δo` (for every `T`, at `g = 1`).
-/

end Formal.Target

-- ===== end of verbatim Spec.lean (6f094d32), start of audit T5 toy =====

/-!
# Audit T5: T3's never-answering toy under the REPAIRED H_ARB (formal 3d3ebb61 .. 6f094d32)

Against `Formal.Target.Spec` as changed in 3d3ebb61 (`ArbNodes = ⟨q, ins⟩`, `ArbOK`: all of `ins`
constant on `[t1, t2]` → `q` constant on `[t1 + T, t2]`). Every Spec name used here is the
Spec's definition; nothing is copied. (Before the formal build of 6f094d32 existed, this file was
also run with the 6f094d32 Spec text inlined verbatim: see `ToyRepairedInline.lean`, generated by
`mkinline.sh`, which checks the inlined text byte for byte against `git show 6f094d32:...`.)

## The toy netlist (T3's, with the state gate's delay `D` now a parameter)
nodes: 0 rst (env), 1 r1, 2 r2, 3 q, 4 A0, 5 input request (env, shared by a/b/start),
6 input acknowledge, 7 out0/end request, 8 out0/end acknowledge (env).
gates: r1 := 0, r2 := 1, q := bd_arbiter ustate O6 table `0xFFF0FFB2` on pins (r1, r2, q, rst, A0)
with every arc exactly `D` ps (feedback loop), A0 := rst after exactly `L` ps, input ack := 0,
out0 req := 0. The circuit NEVER acknowledges its input.
Arbiter list, repaired form: `[⟨3, [1, 2, 0, 4]⟩]` (q and the state LUT's non-feedback inputs).
`g = 1, κ = 0`.

## Results
* `toy_arbOK_iff`: the witness behaviour (one pair offered, rst high on [0,R), A0 falls at R+L,
  q falls at R+L+D) satisfies the repaired `ArbOK T` iff `D ≤ T`. The server wait `L` is gone
  from the condition (T3: the frozen v1 ArbOK needed `T > R + L`).
* `toy_no_model`: for `T < D` there is NO behaviour with Behaves ∧ ArbOK T ∧ Env: residual vacuity
  below the state gate's own delay.
* `toy_iff`: `NetCorrect toy … T … ↔ T < D` (same for `NetCorrectSeq`). So for every `T ≥ D` the
  repaired statement is FALSE for the never-answering circuit, as it should be; for `T < D` it is
  vacuously TRUE.
* `arbOK_mono`, `netCorrect_anti`: larger `T` is the weaker hypothesis; NetCorrect at `T'`
  implies NetCorrect at every `T ≤ T'`, and a refutation at `T` refutes every `T' ≥ T`.
-/

open Formal.Target

namespace Audit.T5.Toy

def aD (D : Nat) : Arc := ⟨D, D, D, D⟩

def qInit : Nat := 0xFFF0FFB2

def gR1 : Gate := ⟨"r1 := 0", 0, 0, [], [], 1⟩
def gR2 : Gate := ⟨"r2 := 1", 0, 1, [], [], 2⟩
def gQ (D : Nat) : Gate := ⟨"ustate.O6", 5, qInit, [1, 2, 3, 0, 4], [aD D, aD D, aD D, aD D, aD D], 3⟩
def gA0 (L : Nat) : Gate := ⟨"A0 := rst after L", 1, 2, [0], [aD L], 4⟩
def gAck : Gate := ⟨"in ack := 0", 0, 0, [], [], 6⟩
def gOreq : Gate := ⟨"out0 req := 0", 0, 0, [], [], 7⟩

def toyNet (L D : Nat) : Net := ⟨9, [], [gR1, gR2, gQ D, gA0 L, gAck, gOreq]⟩

def inCh : InCh := ⟨5, 6, []⟩
def outCh : OutCh := ⟨7, 8, []⟩
def toyB : Boundary := ⟨0, inCh, inCh, inCh, outCh, outCh, [0, 5, 8]⟩
/-- The repaired arbiter list: q = 3, ins = the state LUT's pins other than its feedback. -/
def toyA : List ArbNodes := [⟨3, [1, 2, 0, 4]⟩]

def p1 : DelayPar := ⟨1, 0⟩

theorem circuit_gates (L D : Nat) : (circuit (toyNet L D) toyB).gates = (toyNet L D).gates := by
  simp [circuit, toyNet, toyB, Boundary.envNodes, gR1, gR2, gQ, gA0, gAck, gOreq]

/-! ### small facts -/

theorem start_const (p : DelayPar) (g : Gate) (h : g.arcs = []) : g.start p = 0 := by
  simp [Gate.start, h]

theorem ceil_one (m : Nat) : (Rat.ceil ((m : ℚ) * 1)).toNat = m := by
  have e : ((m : ℕ) : ℚ) = ((m : ℤ) : ℚ) := (Int.cast_natCast m).symm
  rw [mul_one, e, Rat.ceil_intCast]
  simp

theorem start_q (D : Nat) : (gQ D).start p1 = D := by
  simp only [Gate.start, gQ, aD, p1, List.map, List.foldr, ceil_one]
  omega

theorem start_A0 (L : Nat) : (gA0 L).start p1 = L := by
  simp only [Gate.start, gA0, aD, p1, List.map, List.foldr, ceil_one]
  omega

/-- With `g = 1, κ = 0` an arc whose four numbers are all `m` admits exactly delay `m`. -/
theorem adm_exact (c : ℚ) (m d : Nat) (h : Adm p1 c ⟨m, m, m, m⟩ d) : d = m := by
  obtain ⟨h1, h2, -, -⟩ := h
  simp only [p1, div_one, mul_one] at h1 h2
  have : (d : ℚ) = m := le_antisymm h2 h1
  exact_mod_cast this

theorem adm_of (c : ℚ) (m : Nat) : Adm p1 c ⟨m, m, m, m⟩ m := by
  have e : (1 - c) * (m : ℚ) + c * m = m := by ring
  simp [Adm, p1, lerp, e]

/-- The ustate O6 table with r1 = 0, r2 = 1: q' = rst ∨ (A0 ∧ q). -/
theorem qbit (v : Nat → Bool) (h0 : v 0 = false) (h1 : v 1 = true) :
    qInit.testBit (addr 5 v) = (v 3 || (v 4 && v 2)) := by
  simp only [addr, h0, h1]
  cases v 2 <;> cases v 3 <;> cases v 4 <;> decide

theorem bufbit (v : Nat → Bool) : (2 : Nat).testBit (addr 1 v) = v 0 := by
  simp only [addr]
  cases v 0 <;> decide

/-! ### the witness behaviour -/

def xw (L R D : Nat) : Beh := fun n t =>
  if n = 0 then decide (t < R)
  else if n = 2 then true
  else if n = 3 then decide (t < R + L + D)
  else if n = 4 then decide (t < R + L)
  else if n = 5 then decide (R < t)
  else false

theorem rises_req (L R D t : Nat) : rises (xw L R D 5) R t = if R < t then 1 else 0 := by
  induction t with
  | zero => simp [rises]
  | succ t ih =>
    simp only [rises, ih, xw]
    by_cases h1 : R < t
    · have : R < t + 1 := by omega
      simp [h1, this] <;> omega
    · by_cases h2 : t = R
      · subst h2; simp
      · have : ¬ R < t + 1 := by omega
        simp [h1, this] <;> omega

theorem rises_zero (s : Sig) (R t : Nat) (h : ∀ u, s u = false) : rises s R t = 0 := by
  induction t with
  | zero => simp [rises]
  | succ t ih => simp [rises, ih, h]

theorem constGate (c : ℚ) (g : Gate) (x : Beh) (hk : g.k = 0) (ha : g.arcs = [])
    (hv : ∀ t, x g.out t = g.init.testBit 0) : GateOK p1 c g x := by
  refine ⟨fun _ _ => 0, fun i hi => by omega, fun t _ => ⟨fun i hi => by omega, ?_⟩⟩
  rw [hk, hv t]; rfl

theorem toy_behaves (L R D : Nat) : Behaves p1 (circuit (toyNet L D) toyB) (xw L R D) := by
  refine ⟨0, le_rfl, zero_le_one, ?_⟩
  rw [circuit_gates]
  intro g hg
  simp only [toyNet, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · exact constGate 0 _ _ rfl rfl (fun t => by simp [gR1, xw])
  · exact constGate 0 _ _ rfl rfl (fun t => by simp [gR2, xw])
  · -- the arbiter's state gate, D ps reads on every pin
    refine ⟨fun _ t => t - D, fun _ _ _ _ h => Nat.sub_le_sub_right h D, ?_⟩
    intro t ht
    rw [start_q] at ht
    refine ⟨fun i hi => ⟨Nat.sub_le t D, ?_⟩, ?_⟩
    · have hi' : (gQ D).arcs.getD i default = aD D := by
        simp only [gQ] at hi ⊢
        rcases i with _ | _ | _ | _ | _ | i <;> first | rfl | (exfalso; omega)
      rw [hi']
      have e : t - (t - D) = D := by omega
      rw [e]; exact adm_of 0 D
    · show xw L R D 3 t = qInit.testBit (addr 5 fun i => xw L R D ([1, 2, 3, 0, 4].getD i 0) (t - D))
      rw [qbit _ (by simp [xw]) (by simp [xw])]
      simp only [xw, List.getD_cons_succ, List.getD_cons_zero]
      simp
      by_cases h : t < R + L + D <;> simp [h] <;> omega
  · -- A0 := rst after exactly L ps
    refine ⟨fun _ t => t - L, fun _ _ _ _ h => Nat.sub_le_sub_right h L, ?_⟩
    intro t ht
    rw [start_A0] at ht
    refine ⟨fun i hi => ⟨Nat.sub_le t L, ?_⟩, ?_⟩
    · have hi0 : i = 0 := by simp [gA0] at hi; omega
      subst hi0
      have e : t - (t - L) = L := by omega
      rw [e]; exact adm_of 0 L
    · show xw L R D 4 t = (2 : Nat).testBit (addr 1 fun i => xw L R D ([0].getD i 0) (t - L))
      rw [bufbit]
      simp [xw]
      omega
  · exact constGate 0 _ _ rfl rfl (fun t => by simp [gAck, xw])
  · exact constGate 0 _ _ rfl rfl (fun t => by simp [gOreq, xw])

theorem envIn_w (L R D su : Nat) : EnvIn (xw L R D) inCh R su (some 1) (fun _ => 0) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t ht; simp [inCh, xw]; omega
  · intro t ht hne
    simp only [inCh, xw] at hne ⊢
    simp at hne ⊢
    omega
  · intro t ht _ _
    exact ⟨t + 1, by omega, by simp [inCh, xw]; omega⟩
  · intro t ht _
    simp only [inCh, Offered, rises_req]
    split <;> omega
  · intro t _ _ _ s _ _; simp [busVal, inCh]
  · intro t _ _ _; simp [busVal, inCh]

theorem envOut_w (L R D Δo : Nat) : EnvOut (xw L R D) outCh R Δo := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro t _; simp [outCh, xw]
  · intro t _ h; simp [outCh, xw] at h
  · intro t _ h; simp [outCh, xw] at h
  · intro t _ _ h; simp [outCh, xw] at h

theorem toy_env (L R D su Δo : Nat) :
    Env (xw L R D) toyB R su Δo (some 1) (fun _ => 0) (fun _ => 0) := by
  refine ⟨?_, ?_, ?_, envIn_w L R D su, envIn_w L R D su, envIn_w L R D su, envOut_w L R D Δo,
    envOut_w L R D Δo⟩
  · intro t ht; simp [toyB, xw, ht]
  · intro t ht; simp [toyB, xw]; omega
  · intro k _; show 0 < 2 ^ 31 ∧ 0 < 2 ^ 31; decide

theorem toy_seq (L R D : Nat) : SeqEnv (xw L R D) toyB R := by
  intro ch hch t ht h0 _
  simp only [toyB, List.mem_cons, List.not_mem_nil, or_false, or_self] at hch
  subst hch
  have e8 : rises (xw L R D toyB.out0.ack) R t = 0 :=
    rises_zero _ R t (fun u => by show xw L R D 8 u = false; simp [xw])
  refine ⟨?_, ?_, ?_⟩
  · rw [e8]
    show rises (xw L R D 5) R t ≤ 0
    rw [rises_req]
    have : t ≤ R := by
      have h0' : xw L R D 5 t = false := h0
      simp [xw] at h0'; omega
    split <;> omega
  · show xw L R D 7 t = false; simp [xw]
  · show xw L R D 8 t = false; simp [xw]

theorem toy_not_correct (L R D Δo : Nat) :
    ¬ Correct (xw L R D) toyB R Δo (some 1) (fun _ => 0) (fun _ => 0) := by
  intro hc
  obtain ⟨⟨_, _, hlive⟩, _⟩ := hc
  obtain ⟨s, hs, he⟩ := hlive (R + 1) (by omega) (by simp [toyB, inCh, xw])
  simp [toyB, inCh, xw] at he
  omega

/-- The witness meets the REPAIRED H_ARB(T) for every `T ≥ D`, whatever the server wait `L`. -/
theorem toy_arbOK (L R D T : Nat) (hRL : 1 ≤ R + L) (hT : D ≤ T) : ArbOK T toyA (xw L R D) := by
  intro a ha t1 t2 hins t h1 h2
  simp only [toyA, List.mem_singleton] at ha
  subst ha
  have hA0 := hins 4 (by simp)
  have e1 := hA0 (R + L - 1)
  have e2 := hA0 (R + L)
  simp only [xw] at e1 e2 ⊢
  simp only [show (3 : Nat) ≠ 0 by omega, show (3 : Nat) ≠ 2 by omega, show (4 : Nat) ≠ 0 by omega,
    show (4 : Nat) ≠ 2 by omega, show (4 : Nat) ≠ 3 by omega, if_true, if_false] at e1 e2 ⊢
  by_cases hc1 : t2 < R + L + D
  · simp [show t < R + L + D by omega, show t1 + T < R + L + D by omega]
  · by_cases hc2 : R + L + D ≤ t1 + T
    · simp [show ¬ t < R + L + D by omega, show ¬ t1 + T < R + L + D by omega]
    · -- the interval [t1, t2] contains A0's fall at R + L: impossible
      exfalso
      have f1 := e1 (by omega) (by omega)
      have f2 := e2 (by omega) (by omega)
      rw [← f2] at f1
      simp at f1; omega

/-- Negative control: for `T < D` the same witness violates the repaired H_ARB(T). -/
theorem toy_arbOK_small_fails (L R D T : Nat) (hT : T < D) : ¬ ArbOK T toyA (xw L R D) := by
  intro h
  have := h ⟨3, [1, 2, 0, 4]⟩ (by simp [toyA]) (R + L) (R + L + D)
    (fun n hn t h1 h2 => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hn
      rcases hn with rfl | rfl | rfl | rfl <;> simp [xw] <;> omega)
    (R + L + D) (by omega) le_rfl
  simp [xw] at this
  omega

theorem toy_arbOK_iff (L R D T : Nat) (hRL : 1 ≤ R + L) : ArbOK T toyA (xw L R D) ↔ D ≤ T :=
  ⟨fun h => by by_contra hT; exact toy_arbOK_small_fails L R D T (by omega) h,
   fun h => toy_arbOK L R D T hRL h⟩

/-! ### residual vacuity: no model of Behaves ∧ ArbOK T ∧ Env when T < D -/

theorem toy_no_model (L R D T su Δo : Nat) (hL : 1 ≤ L) (hLR : L ≤ R) (hD : 1 ≤ D) (hDR : D ≤ R)
    (hT : T < D) (x : Beh) (n : Option Nat) (va vb : Nat → Nat)
    (hB : Behaves p1 (circuit (toyNet L D) toyB) x) (hA : ArbOK T toyA x)
    (hE : Env x toyB R su Δo n va vb) : False := by
  obtain ⟨c, -, -, hg⟩ := hB
  rw [circuit_gates] at hg
  have mem : ∀ g, g = gR1 ∨ g = gR2 ∨ g = gQ D ∨ g = gA0 L → g ∈ (toyNet L D).gates := by
    intro g hg'; rcases hg' with rfl | rfl | rfl | rfl <;> simp [toyNet]
  have hrst : ∀ t, x 0 t = decide (t < R) := by
    intro t
    by_cases h : t < R
    · simp [h]; exact hE.1 t h
    · simp [h]; exact hE.2.1 t (by omega)
  have hr1 : ∀ t, x 1 t = false := by
    intro t
    obtain ⟨f, -, h⟩ := hg gR1 (mem _ (Or.inl rfl))
    have := (h t (by rw [start_const p1 gR1 rfl]; omega)).2
    simpa [gR1, addr] using this
  have hr2 : ∀ t, x 2 t = true := by
    intro t
    obtain ⟨f, -, h⟩ := hg gR2 (mem _ (Or.inr (Or.inl rfl)))
    have := (h t (by rw [start_const p1 gR2 rfl]; omega)).2
    simpa [gR2, addr] using this
  have hA0 : ∀ t, L ≤ t → x 4 t = x 0 (t - L) := by
    intro t ht
    obtain ⟨f, -, h⟩ := hg (gA0 L) (mem _ (Or.inr (Or.inr (Or.inr rfl))))
    obtain ⟨hr, hv⟩ := h t (by rw [start_A0]; exact ht)
    obtain ⟨hle, hadm⟩ := hr 0 (by simp [gA0])
    have hd := adm_exact c L _ (by simpa [gA0, aD] using hadm)
    have hf : f 0 t = t - L := by omega
    have : x 4 t = (2 : Nat).testBit (addr 1 fun i => x ([0].getD i 0) (f i t)) := by
      simpa [gA0] using hv
    rw [this, bufbit]
    simp [hf]
  have hq : ∀ t, D ≤ t → x 3 t = (x 0 (t - D) || (x 4 (t - D) && x 3 (t - D))) := by
    intro t ht
    obtain ⟨f, -, h⟩ := hg (gQ D) (mem _ (Or.inr (Or.inr (Or.inl rfl))))
    obtain ⟨hr, hv⟩ := h t (by rw [start_q]; exact ht)
    have hf : ∀ i, i < 5 → f i t = t - D := by
      intro i hi
      obtain ⟨hle, hadm⟩ := hr i (by simpa [gQ] using hi)
      have harc : (gQ D).arcs.getD i default = ⟨D, D, D, D⟩ := by
        simp only [gQ, aD]
        rcases i with _ | _ | _ | _ | _ | i <;> first | rfl | (exfalso; omega)
      rw [harc] at hadm
      have := adm_exact c D _ hadm
      omega
    have : x 3 t = qInit.testBit (addr 5 fun i => x ([1, 2, 3, 0, 4].getD i 0) (f i t)) := by
      simpa [gQ] using hv
    rw [this, qbit _ (by simp [hf 0 (by omega), hr1]) (by simp [hf 1 (by omega), hr2])]
    simp [hf 2 (by omega), hf 3 (by omega), hf 4 (by omega)]
  -- q is high on [D, R + L + D - 1]
  have hhigh : ∀ t, D ≤ t → t < R + L + D → x 3 t = true := by
    intro t
    induction t using Nat.strong_induction_on with
    | _ t ih =>
      intro h1 h2
      rw [hq t h1, hrst]
      by_cases h : t - D < R
      · simp [h]
      · rw [hA0 (t - D) (by omega), hrst, ih (t - D) (by omega) (by omega) (by omega)]
        simp; omega
  -- q is low at R + L + D
  have hlow : x 3 (R + L + D) = false := by
    rw [hq _ (by omega), show R + L + D - D = R + L by omega, hrst, hA0 (R + L) (by omega), hrst]
    simp
  -- ArbOK on [R + L, R + L + D]: every input of the state LUT is constant there
  have hc := hA ⟨3, [1, 2, 0, 4]⟩ (by simp [toyA]) (R + L) (R + L + D)
    (fun m hm t h1 h2 => by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with rfl | rfl | rfl | rfl
      · rw [hr1, hr1]
      · rw [hr2, hr2]
      · rw [hrst, hrst]; simp; omega
      · rw [hA0 t (by omega), hA0 (R + L) (by omega), hrst, hrst]; simp; omega)
  have := hc (R + L + D) (by omega) le_rfl
  rw [hlow, hhigh (R + L + T) (by omega) (by omega)] at this
  exact Bool.false_ne_true this

theorem toy_vacuous (L R D T su Δo : Nat) (hL : 1 ≤ L) (hLR : L ≤ R) (hD : 1 ≤ D) (hDR : D ≤ R)
    (hT : T < D) :
    NetCorrect (toyNet L D) toyB toyA p1 T R su Δo ∧ NetCorrectSeq (toyNet L D) toyB toyA p1 T R su Δo :=
  ⟨fun x n va vb hB hA hE => (toy_no_model L R D T su Δo hL hLR hD hDR hT x n va vb hB hA hE).elim,
   fun x n va vb hB hA hE _ => (toy_no_model L R D T su Δo hL hLR hD hDR hT x n va vb hB hA hE).elim⟩

/-- **The repaired statement on the never-answering toy**: true exactly for `T` below the state
gate's own delay `D` (vacuously), false for every `T ≥ D` (whatever the server wait `L`). -/
theorem toy_iff (L R D T su Δo : Nat) (hL : 1 ≤ L) (hLR : L ≤ R) (hD : 1 ≤ D) (hDR : D ≤ R) :
    (NetCorrect (toyNet L D) toyB toyA p1 T R su Δo ↔ T < D) ∧
    (NetCorrectSeq (toyNet L D) toyB toyA p1 T R su Δo ↔ T < D) := by
  refine ⟨⟨fun h => ?_, fun h => (toy_vacuous L R D T su Δo hL hLR hD hDR h).1⟩,
          ⟨fun h => ?_, fun h => (toy_vacuous L R D T su Δo hL hLR hD hDR h).2⟩⟩
  · by_contra hT
    exact toy_not_correct L R D Δo (h (xw L R D) (some 1) _ _ (toy_behaves L R D)
      (toy_arbOK L R D T (by omega) (by omega)) (toy_env L R D su Δo))
  · by_contra hT
    exact toy_not_correct L R D Δo (h (xw L R D) (some 1) _ _ (toy_behaves L R D)
      (toy_arbOK L R D T (by omega) (by omega)) (toy_env L R D su Δo) (toy_seq L R D))

/-- T3's exact toy (1 ps state gate, `vacuous_every_T` used `L = R = T`) is no longer vacuous:
for every `T ≥ 1` the repaired NetCorrect and NetCorrectSeq are FALSE on it. -/
theorem t3_toy_now_refuted (T : Nat) (hT : 1 ≤ T) (su Δo : Nat) :
    ¬ NetCorrect (toyNet T 1) toyB toyA p1 T T su Δo ∧ ¬ NetCorrectSeq (toyNet T 1) toyB toyA p1 T T su Δo := by
  have h := toy_iff T T 1 T su Δo hT le_rfl le_rfl hT
  exact ⟨fun h1 => absurd (h.1.1 h1) (by omega), fun h1 => absurd (h.2.1 h1) (by omega)⟩

/-! ### monotonicity in T (general, any net) -/

theorem arbOK_mono {T T' : Nat} (A : List ArbNodes) (x : Beh) (h : T ≤ T') (hA : ArbOK T A x) :
    ArbOK T' A x := by
  intro a ha t1 t2 hins t h1 h2
  have e1 := hA a ha t1 t2 hins t (by omega) h2
  have e2 := hA a ha t1 t2 hins (t1 + T') (by omega) (by omega)
  rw [e1, e2]

/-- NetCorrect at `T'` gives NetCorrect at every `T ≤ T'` (a larger `T` is the stronger theorem),
so a refutation at `T` refutes every larger `T'`. -/
theorem netCorrect_anti (N : Net) (B : Boundary) (A : List ArbNodes) (p : DelayPar) {T T' : Nat}
    (R su Δo : Nat) (h : T ≤ T') (hN : NetCorrect N B A p T' R su Δo) : NetCorrect N B A p T R su Δo :=
  fun x n va vb hB hA hE => hN x n va vb hB (arbOK_mono A x h hA) hE

end Audit.T5.Toy

#print axioms Audit.T5.Toy.toy_iff
#print axioms Audit.T5.Toy.toy_arbOK_iff
#print axioms Audit.T5.Toy.t3_toy_now_refuted
#print axioms Audit.T5.Toy.netCorrect_anti
