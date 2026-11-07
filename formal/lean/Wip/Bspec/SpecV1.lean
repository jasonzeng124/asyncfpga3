-- B: verbatim copy of Wip/Target/Spec.lean at commit , plus the import Mathlib.Data.Rat.Floor it needs (v1 does not compile without it: ⌈⌉ at line 152).
import Mathlib.Data.Rat.Defs
import Mathlib.Algebra.Order.Field.Rat
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.Rat.Floor

/-!
# Formal.Target.Spec — THE statement: the gcd_hw bitstream computes gcd

Shard A, 2026-11-01. `formal/PROGRAM.md`, "THE goal". This file holds only
definitions: no theorem, no proof. It is the statement every shard works
toward. Changing it needs a journaled reason and an audit row.

**Status (v1, 2026-11-01): part I written (sections 1-6); part II (section 7)
is a stub.** Part I is the semantics, the hypotheses H_DELAY, H_PRIM, H_ARB and
H_ENV, and the conclusion, for an arbitrary decoded netlist `N`. Part II ties
`N` to the target FASM through a decoder written in Lean (H_DECODE). Until part
II lands, the statement is "for the netlist `N`", not yet "for the bitstream".
See `formal/target/README.md` and `formal/target/STATUS.md`.

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

**H_ARB(T).** For every arbiter of the target, given by its two request nodes
and its state node: whenever both requests are constant on `[t1, t2]`, the
state node is constant on `[t1 + T, t2]`.

**H_ENV.** The environment drives the reset and the request and data nodes of
the input channels `a`, `b`, `start` and the acknowledge nodes of the output
channels `out0`, `end`. Reset is high on `[0, R)` and low from `R` on. Each
channel, on its own, follows the four-phase protocol from `R` on, with no
timing assumption except two stated margins: the input data is held from `su`
ps before its request rises until its acknowledge rises, and the output
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
  (g.arcs.map fun e => ⌈(e.smax : ℚ) * p.g⌉.toNat).foldr max 0

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

/-- One arbiter: its two request nodes and its state (decision) node. -/
structure ArbNodes where
  r1 : Nat
  r2 : Nat
  q : Nat
  deriving Repr

/-- A signal is constant on `[t1, t2]`. -/
def ConstOn (s : Sig) (t1 t2 : Nat) : Prop := ∀ t, t1 ≤ t → t ≤ t2 → s t = s t1

/-- **H_ARB(T)**: whenever both requests are constant on `[t1, t2]`, the state
node is constant on `[t1 + T, t2]`. -/
def ArbOK (T : Nat) (A : List ArbNodes) (x : Beh) : Prop :=
  ∀ a ∈ A, ∀ t1 t2, ConstOn (x a.r1) t1 t2 → ConstOn (x a.r2) t1 t2 →
    ConstOn (x a.q) (t1 + T) t2

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
from `R` on it moves only as allowed, rises at most `n` times, is live; while the request
is high and not yet acknowledged, and from `su` ps before each rise, the data
holds item `k` of `vals` (`k` = rises so far minus one). -/
def EnvIn (x : Beh) (ch : InCh) (R su : Nat) (n : Option Nat) (vals : Nat → Nat) : Prop :=
  (∀ t, t ≤ R → x ch.req t = false) ∧
  ReqMoves (x ch.req) (x ch.ack) R ∧
  ReqLive (x ch.req) (x ch.ack) R (Offered n) ∧
  (∀ t, R ≤ t → x ch.req t = true → Offered n (rises (x ch.req) R t - 1)) ∧
  (∀ t, R ≤ t → x ch.req t = false → x ch.req (t + 1) = true →
      ∀ s, t + 1 - su ≤ s → s ≤ t + 1 → busVal x ch.data s = vals (rises (x ch.req) R (t + 1) - 1)) ∧
  (∀ t, R ≤ t → x ch.req t = true → x ch.ack t = false →
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

/-! ## 7. Part II (stub): the target

**How the target's boundary is wired (found 2026-11-01, yosys netlist of the target
build).** THE goal's wording ("every `a, b < 2^31`", independent channels) does not fit
this bitstream, and the statement above is written for what the bitstream is:
* `a_req`, `b_req` and `start_req` are ONE node: the rig's `bd_fork` is
  `assign req_out = {N{req}}`. So `B.a.req = B.b.req = B.start.req`, and `Env`'s
  per-channel rules, conjoined, say: the shared request rises only when all three
  acknowledges are low and falls only when all three are high. Offering pair `k+1`
  "as soon as the input handshake of pair `k` completes" is still allowed and covered,
  but it is the handshake of all three channels together, and `start` is
  acknowledged only at completion (gcd_rig.v's header; not proved here), so the target
  would not hold two pairs.
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
* **THE theorem**: `decode targetFasm = some (N, B, A) ∧ N.WF ∧ B.OK N ∧ NetCorrect N B A p T R su Δo`,
  for stated `p = ⟨g, κ⟩`, `T`, `R`, `su`, `Δo`.
-/

end Formal.Target
