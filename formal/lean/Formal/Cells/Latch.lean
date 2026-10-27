import Formal.Cells.Prelim

/-!
# Track 6a: the LUT latch `bd_latch` / `bd_latch_rst` (cells/rtl/bd_latch.v)

Gate model. Each latch bit is a LUT whose output is routed back to one of its
own input pins. We evaluate the cells' REAL INIT constants with the Prelim
semantics (`lutB` binary, `lutK` Kleene closure = hypothesis H_KLEENE_LUT):

* `bd_latch` pair: `LUT6_2 #(INIT 64'hFF33_CC00_B8B8_B8B8)`,
  pins `I0=d[i] I1=en I2=q[i] I3=d[i+1] I4=q[i+1] I5=1`, `O5=q[i] O6=q[i+1]`.
* `bd_latch` odd bit: `LUT6 #(INIT 64'hB8B8_..._B8B8)`,
  pins `I0=d I1=en I2=q I3=I4=I5=0`.
* `bd_latch_rst`: `LUT6 #(INIT 64'h00B8_00B8_00B8_00B8)` (clear) or
  `64'hFFB8_...` (preset), pins `I0=d I1=en I2=q I3=rst I4=I5=0`.

Part 1: the functions (binary, then Kleene, for all inputs).
Part 2: Kleene corollaries (no static hazard on close/open with d = q, X on d
while closed is contained, en = X with d ≠ q gives X).
Part 3: discrete-time timing with a feedback loop of bounded delay: the
setup/hold window, the theorem that the latch holds the right value under it,
counter-traces when it is violated, and the bridge to `bd_link`'s DACK line.
-/

namespace Formal.Cells.Latch
open Formal.Cells

/-! ## The constants, copied from cells/rtl/bd_latch.v -/

/-- `bd_latch` pair LUT6_2 INIT. -/
def PAIR : Nat := 0xFF33CC00B8B8B8B8
/-- `bd_latch` odd-bit LUT6 INIT. -/
def ODD : Nat := 0xB8B8B8B8B8B8B8B8
/-- `bd_latch_rst` INIT for a bit whose RESET_VALUE is 0. -/
def RST0 : Nat := 0x00B800B800B800B8
/-- `bd_latch_rst` INIT for a bit whose RESET_VALUE is 1. -/
def RST1 : Nat := 0xFFB8FFB8FFB8FFB8

/-- Decidability of `∀ k : K3, P k` (three cases), so `decide` can enumerate. -/
instance K3.decForall (P : K3 → Prop) [DecidablePred P] : Decidable (∀ k, P k) :=
  decidable_of_iff (P .f ∧ P .t ∧ P .x)
    ⟨fun ⟨a, b, c⟩ k => by cases k <;> assumption, fun h => ⟨h _, h _, h _⟩⟩

/-! ## Part 1a: binary functions -/

/-- Binary transparent-high latch next state. -/
def bmux (en d q : Bool) : Bool := if en then d else q

/-- O5 of the pair (bit i) is the mux latch of bit i, for every value of the
other bit's pins `d[i+1]`, `q[i+1]`: independence of the pair, binary. -/
theorem pair_o5_bin : ∀ d0 en q0 d1 q1 : Bool,
    o5B PAIR [d0, en, q0, d1, q1, true] = bmux en d0 q0 := by decide

/-- O6 of the pair (bit i+1) is the mux latch of bit i+1, for every value of
`d[i]`, `q[i]`. -/
theorem pair_o6_bin : ∀ d0 en q0 d1 q1 : Bool,
    o6B PAIR [d0, en, q0, d1, q1, true] = bmux en d1 q1 := by decide

theorem odd_bin : ∀ d en q : Bool,
    lutB ODD [d, en, q, false, false, false] = bmux en d q := by decide

/-- `bd_latch_rst`, RESET_VALUE 0: rst = 1 clears, rst = 0 is the latch. -/
theorem rst0_bin : ∀ d en q rst : Bool,
    lutB RST0 [d, en, q, rst, false, false] = (if rst then false else bmux en d q) := by
  decide

/-- `bd_latch_rst`, RESET_VALUE 1: rst = 1 presets. -/
theorem rst1_bin : ∀ d en q rst : Bool,
    lutB RST1 [d, en, q, rst, false, false] = (if rst then true else bmux en d q) := by
  decide

/-! ## Part 1b: Kleene functions (H_KLEENE_LUT closure semantics)

`K3.mux en q d` is: en = f gives q, en = t gives d, en = x gives q if q = d,
else x. The pair's closure semantics equals exactly this, for ALL 3^5 inputs:
in particular X on the other bit's pins never reaches this bit. -/

theorem pair_o5_kleene : ∀ d0 en q0 d1 q1 : K3,
    o5K PAIR [d0, en, q0, d1, q1, .t] = K3.mux en q0 d0 := by decide

theorem pair_o6_kleene : ∀ d0 en q0 d1 q1 : K3,
    o6K PAIR [d0, en, q0, d1, q1, .t] = K3.mux en q1 d1 := by decide

theorem odd_kleene : ∀ d en q : K3,
    lutK ODD [d, en, q, .f, .f, .f] = K3.mux en q d := by decide

/-- Reset variant, Kleene: rst is itself a Kleene mux select between the
latch and the reset value. -/
theorem rst0_kleene : ∀ d en q rst : K3,
    lutK RST0 [d, en, q, rst, .f, .f] = K3.mux rst (K3.mux en q d) .f := by decide

theorem rst1_kleene : ∀ d en q rst : K3,
    lutK RST1 [d, en, q, rst, .f, .f] = K3.mux rst (K3.mux en q d) .t := by decide

/-- The same function under the per-mux reading of H_KLEENE_LUT (`muxTree`,
Prelim's I0-at-root order), for O5 of the pair: the claims below do not
depend on choosing closure over the mux-tree reading, for this order. -/
theorem pair_o5_muxTree : ∀ d0 en q0 d1 q1 : K3,
    muxTree (fun j => (PAIR % 2 ^ 32).testBit j) [d0, en, q0, d1, q1] = K3.mux en q0 d0 := by
  decide

theorem pair_o6_muxTree : ∀ d0 en q0 d1 q1 : K3,
    muxTree (fun j => PAIR.testBit j) [d0, en, q0, d1, q1, .t] = K3.mux en q1 d1 := by
  decide


/-! ## Part 2: Kleene corollaries

`en = x` stands for the enable pin in the middle of an edge (a slow or runt
edge, H_KLEENE_LUT). One static fact covers both closing (en t → x → f) and
opening (en f → x → t): it needs only d = q at the pin. -/

/-- Closing or opening with d = q (definite): the output is definite. The
INIT contains the consensus term (d ∧ q), so there is no static hazard. -/
theorem no_hazard_en_x (v : K3) (d1 q1 : K3) :
    o5K PAIR [v, .x, v, d1, q1, .t] = v ∧ o6K PAIR [d1, .x, q1, v, v, .t] = v := by
  rw [pair_o5_kleene, pair_o6_kleene]
  cases v <;> exact ⟨rfl, rfl⟩

/-- While closed (en = 0), X on d does not reach q. -/
theorem closed_contains_dx (q0 d1 q1 : K3) :
    o5K PAIR [.x, .f, q0, d1, q1, .t] = q0 ∧ o6K PAIR [d1, .f, q1, .x, q0, .t] = q0 := by
  rw [pair_o5_kleene, pair_o6_kleene]; exact ⟨rfl, rfl⟩

/-- Setup violation: the enable is mid-edge while d ≠ q (both definite): the
output is X. The LUT latch can go metastable; nothing in the cell resolves it. -/
theorem en_x_d_ne_q_is_x (d q : Bool) (h : d ≠ q) (d1 q1 : K3) :
    o5K PAIR [K3.ofBool d, .x, K3.ofBool q, d1, q1, .t] = .x ∧
    o6K PAIR [d1, .x, q1, K3.ofBool d, K3.ofBool q, .t] = .x := by
  rw [pair_o5_kleene, pair_o6_kleene]
  cases d <;> cases q <;> first | exact absurd rfl h | exact ⟨rfl, rfl⟩

/-- Reset variant: rst = 1 forces the reset value whatever d, en, q are (even
all X). -/
theorem rst_forces (d en q : K3) :
    lutK RST0 [d, en, q, .t, .f, .f] = .f ∧ lutK RST1 [d, en, q, .t, .f, .f] = .t := by
  rw [rst0_kleene, rst1_kleene]; exact ⟨rfl, rfl⟩

/-- Reset variant: an X on rst while closed is harmless exactly when the
held value equals the reset value, and gives X otherwise. -/
theorem rst_x_closed (d : K3) :
    lutK RST0 [d, .f, .f, .x, .f, .f] = .f ∧ lutK RST0 [d, .f, .t, .x, .f, .f] = .x ∧
    lutK RST1 [d, .f, .t, .x, .f, .f] = .t ∧ lutK RST1 [d, .f, .f, .x, .f, .f] = .x := by
  rw [rst0_kleene, rst0_kleene, rst1_kleene, rst1_kleene]
  exact ⟨rfl, rfl, rfl, rfl⟩

/-! ## Part 3: timing in discrete time

Time is ℕ (one tick = the model's time grain, e.g. 1 ps). Traces are
`ℕ → K3`, so a binary trace is the special case with no `x`, and an `x` on
`en` is an edge in flight at the pin.

Gate model of one latch bit (bit i of a pair; the other bit's pins are
arbitrary traces, which is legitimate by `pair_o5_kleene`):

* **LUT** (`hlut`): `q t = o5K PAIR [d t, en t, p t, d1 t, p1 t, t]`, where
  `d`, `en`, `p` are the values AT THE LUT PINS. The LUT's own arc is folded
  into the loop delay below (hypothesis H_LUT_LUMPED: the pin-to-O5 arc is a
  pure delay, so moving it from the output to the loop only shifts `q` in
  time; it ignores the LUT's inertial filtering of short pulses).
* **Feedback loop** (`LoopDelay`): `p t = q (t - k t)` with `1 ≤ k t ≤ L`:
  a bounded pure delay whose value may vary from tick to tick (jitter, PVT).
  It is a relation, not a function: every theorem holds for every `k`
  within the bounds.
-/

/-- The feedback loop of one latch bit: the routed wire from O5/O6 back to the
latch's own q pin, plus the LUT arc (H_LUT_LUMPED), as a bounded pure delay. -/
structure LoopDelay (L : Nat) where
  /-- delay seen at tick t -/
  k : Nat → Nat
  /-- H_LOOP_MIN: the loop (LUT arc + wire) takes at least one tick. Physically
  > 0 ps; test: any routed SDF. -/
  H_LOOP_MIN : ∀ t, 1 ≤ k t
  /-- H_LOOP_MAX: the loop takes at most `L` ticks at the slow corner. Test:
  prjxray slow-max of the O5 arc plus the q→I2 route, or routed GLS. -/
  H_LOOP_MAX : ∀ t, k t ≤ L

/-- One latch bit (O5 of a pair) with its feedback, as relations on traces at
the LUT pins. -/
structure LatchBit (L : Nat) where
  d : Nat → K3
  en : Nat → K3
  /-- the feedback pin I2 -/
  p : Nat → K3
  /-- the other bit's pins I3, I4 (arbitrary) -/
  d1 : Nat → K3
  p1 : Nat → K3
  /-- the O5 output -/
  q : Nat → K3
  loop : LoopDelay L
  /-- the LUT relation at every tick -/
  hlut : ∀ t, q t = o5K PAIR [d t, en t, p t, d1 t, p1 t, .t]
  /-- the wire relation: once the loop has existed for `k t` ticks -/
  hloop : ∀ t, loop.k t ≤ t → p t = q (t - loop.k t)

/-- **The latch holds the right value.** Window `[s, T]`.
* `H_EN_OPEN`: en is definitely high on `[s, s + L)`: the latch has been open
  for a full loop delay, so the loop is filled with the value.
* `H_DATA`: d = v whenever en is not definitely low: before the close this is
  the setup condition (stable for the loop delay `L` before en starts to fall);
  during the edge (`en = x`) it is the hold condition (stable until en has
  fallen at the LUT pin). While en = f, d is unconstrained (may be X).
Then q = v on the whole window, including any reopening with d = v. -/
theorem holds_value {L : Nat} (b : LatchBit L) (v : K3) (s T : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → b.en t ≠ .t → s + L ≤ t)
    (H_DATA : ∀ t, s ≤ t → t ≤ T → b.en t ≠ .f → b.d t = v) :
    ∀ t, s ≤ t → t ≤ T → b.q t = v := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro hs hT
    have hq : b.q t = K3.mux (b.en t) (b.p t) (b.d t) := by
      rw [b.hlut t, pair_o5_kleene]
    -- the feedback pin carries v once en has left t
    have hp : b.en t ≠ .t → b.p t = v := by
      intro hne
      have h1 := H_EN_OPEN t hs hT hne
      have k1 := b.loop.H_LOOP_MIN t
      have kL := b.loop.H_LOOP_MAX t
      rw [b.hloop t (by omega)]
      exact ih (t - b.loop.k t) (by omega) (by omega) (by omega)
    cases he : b.en t with
    | t => rw [hq, he]; exact H_DATA t hs hT (by rw [he]; decide)
    | f => rw [hq, he]; exact hp (by rw [he]; decide)
    | x =>
      rw [hq, he, hp (by rw [he]; decide), H_DATA t hs hT (by rw [he]; decide)]
      simp [K3.mux, K3.join]

/-- Binary special case, phrased with the close time `te`: en = 1 on
`[te - L, te)`, en = 0 on `[te, T]`, d = v on `[te - L, te)`. Then q = v on
`[te - L, T]`. (Setup = stable for the loop delay before en falls; hold = up to
the tick en falls at the pin.) -/
theorem holds_value_bin {L : Nat} (b : LatchBit L) (v : Bool) (te T : Nat)
    (hL : L ≤ te)
    (H_EN : ∀ t, te - L ≤ t → t ≤ T → b.en t = K3.ofBool (decide (t < te)))
    (H_DATA : ∀ t, te - L ≤ t → t < te → b.d t = K3.ofBool v) :
    ∀ t, te - L ≤ t → t ≤ T → b.q t = K3.ofBool v := by
  apply holds_value b (K3.ofBool v) (te - L) T
  · intro t h1 h2 hne
    rw [H_EN t h1 h2] at hne
    by_cases h : t < te
    · simp [h, K3.ofBool] at hne
    · omega
  · intro t h1 h2 hne
    rw [H_EN t h1 h2] at hne
    by_cases h : t < te
    · exact H_DATA t h1 h
    · simp [h, K3.ofBool] at hne

/-- Every `L' ≤ L` is covered: data stable for the slow-corner loop delay
suffices for every faster loop. (A `LoopDelay L'` is a `LoopDelay L`.) -/
def LoopDelay.widen {L' L : Nat} (h : L' ≤ L) (l : LoopDelay L') : LoopDelay L :=
  ⟨l.k, l.H_LOOP_MIN, fun t => Nat.le_trans (l.H_LOOP_MAX t) h⟩

/-! ### Counter-traces

Concrete traces satisfying every gate relation on a finite horizon, with a
constant loop delay, where the latch ends up holding the wrong thing. The
relations are checked tick by tick by `decide` over the horizon. -/

/-- The gate relations of one latch bit with constant loop delay `L`, checked
on ticks `< T`, the other bit's pins tied to `f`. -/
def relOK (L T : Nat) (d en q : Nat → K3) : Prop :=
  ∀ t, t < T → q t = o5K PAIR [d t, en t, (if L ≤ t then q (t - L) else q t), .f, .f, .t]
-- (before the loop has existed for L ticks the pin value is unconstrained;
-- the traces below use the output itself there, i.e. a consistent power-up.)

instance (L T : Nat) (d en q : Nat → K3) : Decidable (relOK L T d en q) := by
  unfold relOK; exact inferInstance

/-- **Hold violation, binary, L = 1.** en falls at the pin at tick 4; the
sender released the next value (d: t → f) at tick 3, before en had fallen
at the pin. The latch closes on the NEW value and holds it: q = f from tick 3
on, whereas the token was t. A silent wrong value (cf. the xorshift token
with two corrupted bits in cells/rtl/bd_link.v). -/
def ct1_en (t : Nat) : K3 := if t < 4 then .t else .f
def ct1_d (t : Nat) : K3 := if t < 3 then .t else .f
def ct1_q (t : Nat) : K3 := if t < 3 then .t else .f

theorem ct1_hold_violation :
    relOK 1 10 ct1_d ct1_en ct1_q ∧ ct1_q 9 = .f ∧ ct1_d 2 = .t := by decide

/-- **Hold violation during the edge, Kleene, L = 1.** en is mid-edge (x) at
tick 4 and d changes exactly then: q goes X at tick 4 and the loop keeps the X
(a metastable latch, never resolved within the model). -/
def ct2_en (t : Nat) : K3 := if t < 4 then .t else if t = 4 then .x else .f
def ct2_d (t : Nat) : K3 := if t < 4 then .t else .f
def ct2_q (t : Nat) : K3 := if t < 4 then .t else .x

theorem ct2_hold_violation_x :
    relOK 1 10 ct2_d ct2_en ct2_q ∧ ct2_q 9 = .x := by decide

/-- **Setup violation, L = 2.** d becomes t only at tick 3, one tick before en
falls at tick 4: less than the loop delay. The loop then holds the last two
samples (f, t) and circulates them: q oscillates with period 2 and is f at
tick 4, right after the close. (A real loop would also filter this pulse
inertially; the model shows the stored state is not a single value.) -/
def ct3_en (t : Nat) : K3 := if t < 4 then .t else .f
def ct3_d (t : Nat) : K3 := if t < 3 then .f else .t
def ct3_q (t : Nat) : K3 := if t < 3 then .f else if t % 2 = 1 then .t else .f

theorem ct3_setup_violation :
    relOK 2 12 ct3_d ct3_en ct3_q ∧ ct3_q 4 = .f ∧ ct3_q 5 = .t ∧ ct3_q 10 = .f := by
  decide

/-- Sanity: the same relation with the setup met (d = t from tick 2, i.e. for
`L = 2` ticks before the close) holds t: the counter-traces are not an
artefact of `relOK`. -/
def ok_d (t : Nat) : K3 := if t < 2 then .f else .t
def ok_q (t : Nat) : K3 := if t < 2 then .f else .t

theorem ok_setup_met : relOK 2 12 ok_d ct3_en ok_q ∧ ok_q 11 = .t := by decide

/-! ### Bridge to `bd_link`: the DACK hold condition

In `bd_link` one C-element node `c` drives the W/2 latch enables and, through
the DACK line (`bd_delay #(.N(DACK), .FASTRISE(1))`), the acknowledge `ack_in`
to the sender. The header note "ack_in FALLS BEFORE THE LATCH HAS CLOSED"
is the failure of the hold condition `H_DATA` during the edge. With `c`
falling at tick `tc`:
* `H_EN_FANOUT`: this latch's enable pin is definitely low from `tc + E` on
  (E = latest enable-net arrival incl. the edge; routed 32-bit link: ~1125 ps
  spread). Test: routed SDF / GLS of the enable net.
* `H_ACK_MIN`: the sender cannot see ack fall before `tc + A`
  (A = earliest ack wire + DACK chain fall).
* `H_DATA_MIN`: released data needs at least `R` ticks from the sender's ack
  pin to this latch's d pin (sender's controller, latch, route).
* The protocol: data at the pin is still `v` before `tc + A + R`.
Rule H (verify/tighten.py) is `E ≤ A + R`; under it `H_DATA` holds during the
edge.

Scope (claude/audit REPORT row 21): this is a one-line arithmetic (`omega`)
lemma about a SINGLE close/transaction: `H_RELEASE` fixes `d = v` for all
`t < tc + A + R` from time 0, so it says nothing about later transactions.
The windowed, per-transaction form on a routed netlist is
`OnNetlistTimed2.latch_rule_h_net`. -/
theorem hold_of_dack (en d : Nat → K3) (v : K3) (tc E A R : Nat)
    (H_EN_FANOUT : ∀ t, tc + E ≤ t → en t = .f)
    (H_RELEASE : ∀ t, t < tc + A + R → d t = v)
    (H_RULE_H : E ≤ A + R) :
    ∀ t, en t ≠ .f → d t = v := by
  intro t hne
  apply H_RELEASE
  have : ¬ (tc + E ≤ t) := fun h => hne (H_EN_FANOUT t h)
  omega

/-- The link-level statement: data at the pin is v from `s` until the
released next value can arrive (`H_RELEASE`, which before the close is the
setup condition), en is definitely high on `[s, s + L)` (`H_EN_OPEN`, the
open window is at least the loop delay), and rule H. Then the latch bit
holds v through `T`. -/
theorem link_latch_holds {L : Nat} (b : LatchBit L) (v : K3) (s T tc E A R : Nat)
    (H_EN_OPEN : ∀ t, s ≤ t → t ≤ T → b.en t ≠ .t → s + L ≤ t)
    (H_EN_FANOUT : ∀ t, tc + E ≤ t → b.en t = .f)
    (H_RELEASE : ∀ t, t < tc + A + R → s ≤ t → b.d t = v)
    (H_RULE_H : E ≤ A + R) :
    ∀ t, s ≤ t → t ≤ T → b.q t = v := by
  apply holds_value b v s T H_EN_OPEN
  intro t hs _ hne
  have : ¬ (tc + E ≤ t) := fun h => hne (H_EN_FANOUT t h)
  exact H_RELEASE t (by omega) hs

end Formal.Cells.Latch

#print axioms Formal.Cells.Latch.holds_value
#print axioms Formal.Cells.Latch.holds_value_bin
#print axioms Formal.Cells.Latch.ct3_setup_violation
#print axioms Formal.Cells.Latch.link_latch_holds
#print axioms Formal.Cells.Latch.pair_o5_kleene
#print axioms Formal.Cells.Latch.en_x_d_ne_q_is_x
