import Formal.Cells.Prelim

/-!
# Track 7, probe 7a: the arbiter in the binary model (tie and runt)

Cells: `bd_arbcell` and `bd_arbiter` from `cells/rtl/bd_arb.v`, with the real
INIT constants and pin maps, evaluated with `lutB` / `o5B` / `o6B` from
`Formal.Cells.Prelim`.

* `bd_arbcell` state node = `bd_c2n_set` (`cells/rtl/bd_ce.v`):
  LUT6 INIT `FFB2_FFB2_FFB2_FFB2`, pins `I0=r1 I1=r2 I2=q I3=rst I4=0 I5=0`, `O=q`.
* both grants: LUT6_2 INIT `0C0C_0C0C_A0A0_A0A0`,
  pins `I0=r1 I1=r2 I2=q I3=0 I4=0 I5=1`, `O5=g1 O6=g2`.
* `bd_arbiter` state node: LUT6_2 INIT `FFF0_FFB2_ACAC_ACAC`,
  pins `I0=r1 I1=r2 I2=q I3=rst I4=A0 I5=1`, `O6=q O5=R0`.
* `bd_arbiter` acks: `bd_c2` (INIT `00E8_00E8_00E8_00E8`, `I0=a I1=b I2=q I3=rst`).

Sections:
1. INIT decoding lemmas (the INIT equals the equation in the header).
2. Settled exclusion (structural) and the Kleene remark (an `x` on q reaches both grants).
3. The tie, in a settled-step (fundamental-mode) model: a tie grants the
   PREVIOUS WINNER again.
4. The runt, in a discrete-time transport-delay model of the q loop: a concrete
   trace with a forever-circulating pulse and overlapping grants; opposite-sense
   request moves are always clean; exclusion under named separation/skew hypotheses.
5. Sustained contention and alternation for `bd_arbiter` in an interleaving
   (unbounded gate delay) model: what fails without timing hypotheses and what
   holds with them.

All after reset (`rst = 0`); reset itself is not modelled beyond the initial state.
-/

namespace Formal.Cells.ArbBinary
open Formal.Cells

/-- Fold Boolean connectives over `decide`s into one `decide`, compare by `↔`,
and finish with `omega`. -/
macro "arbbin_omega" : tactic =>
  `(tactic| (simp only [← Bool.decide_and, ← Bool.decide_or, ← decide_not, Bool.false_eq, Bool.true_eq, decide_eq_decide, decide_eq_true_eq, decide_eq_false_iff_not] at *; omega))

/-! ## 1. The cells, from their INITs -/

/-- `bd_c2n_set` INIT (state node of `bd_arbcell`). -/
def C2N_SET : Nat := 0xFFB2FFB2FFB2FFB2
/-- grant LUT6_2 INIT (`ugrant`, both cells). -/
def GRANT : Nat := 0x0C0C0C0CA0A0A0A0
/-- `bd_arbiter` state/R0 LUT6_2 INIT (`ustate`, with the A0 hold). -/
def ARB_ST : Nat := 0xFFF0FFB2ACACACAC
/-- `bd_c2` INIT (the acks `A1`, `A2` of `bd_arbiter`). -/
def C2 : Nat := 0x00E800E800E800E8

/-- `bd_arbcell` state LUT output, rst = 0: pins `[r1, r2, q, rst=0, 0, 0]`. -/
def stF (r1 r2 q : Bool) : Bool := lutB C2N_SET [r1, r2, q, false, false, false]
/-- grant `g1` = O5 of `ugrant`, pins `[r1, r2, q, 0, 0, 1]`. -/
def gr1 (r1 r2 q : Bool) : Bool := o5B GRANT [r1, r2, q, false, false, true]
/-- grant `g2` = O6 of `ugrant`. -/
def gr2 (r1 r2 q : Bool) : Bool := o6B GRANT [r1, r2, q, false, false, true]
/-- `bd_arbiter` state: O6 of `ustate`, pins `[r1, r2, q, rst=0, A0, 1]`. -/
def stA (r1 r2 q a0 : Bool) : Bool := o6B ARB_ST [r1, r2, q, false, a0, true]
/-- `bd_arbiter` request to the server: O5 of `ustate`. -/
def r0A (r1 r2 q a0 : Bool) : Bool := o5B ARB_ST [r1, r2, q, false, a0, true]
/-- `bd_c2` output, rst = 0: pins `[a, b, q, 0, 0, 0]`. -/
def c2 (a b q : Bool) : Bool := lutB C2 [a, b, q, false, false, false]

/-- With rst = 1 the arbcell state LUT outputs 1 (reset value q = 1). -/
theorem stF_reset (r1 r2 q : Bool) :
    lutB C2N_SET [r1, r2, q, true, false, false] = true := by
  cases r1 <;> cases r2 <;> cases q <;> rfl

/-- The INIT is `C(r1, ~r2)`: set `r1.~r2`, reset `~r1.r2`, otherwise hold. -/
theorem stF_eq (r1 r2 q : Bool) :
    stF r1 r2 q = ((r1 && !r2) || (q && !(!r1 && r2))) := by
  cases r1 <;> cases r2 <;> cases q <;> rfl

theorem gr1_eq (r1 r2 q : Bool) : gr1 r1 r2 q = (r1 && q) := by
  cases r1 <;> cases r2 <;> cases q <;> rfl

theorem gr2_eq (r1 r2 q : Bool) : gr2 r1 r2 q = (r2 && !q) := by
  cases r1 <;> cases r2 <;> cases q <;> rfl

/-- The `bd_arbiter` state node: with A0 high it holds, with A0 low it is the
same C-element as `bd_c2n_set`. -/
theorem stA_eq (r1 r2 q a0 : Bool) :
    stA r1 r2 q a0 = (if a0 then q else stF r1 r2 q) := by
  cases r1 <;> cases r2 <;> cases q <;> cases a0 <;> rfl

/-- `bd_arbiter` reset: rst = 1 forces q = 1 whatever A0. -/
theorem stA_reset (r1 r2 q a0 : Bool) :
    o6B ARB_ST [r1, r2, q, true, a0, true] = true := by
  cases r1 <;> cases r2 <;> cases q <;> cases a0 <;> rfl

/-- `R0 = g1 + g2`, independent of A0 (and of rst). -/
theorem r0A_eq (r1 r2 q a0 : Bool) : r0A r1 r2 q a0 = (gr1 r1 r2 q || gr2 r1 r2 q) := by
  cases r1 <;> cases r2 <;> cases q <;> cases a0 <;> rfl

theorem c2_eq (a b q : Bool) : c2 a b q = ((a && b) || (q && (a || b))) := by
  cases a <;> cases b <;> cases q <;> rfl

/-- The state LUT settles in one evaluation: `F(r, F(r, q)) = F(r, q)`. -/
theorem stF_idem (r1 r2 q : Bool) : stF r1 r2 (stF r1 r2 q) = stF r1 r2 q := by
  cases r1 <;> cases r2 <;> cases q <;> rfl

/-- **q only moves while exactly one request is up** (`bd_arbcell`). -/
theorem stF_moves_only_if_alone (r1 r2 q : Bool) (h : stF r1 r2 q ≠ q) : r1 ≠ r2 := by
  cases r1 <;> cases r2 <;> cases q <;> simp_all [stF_eq]

/-- **q only moves while exactly one request is up AND A0 is low** (`bd_arbiter`). -/
theorem stA_moves_only_if_alone (r1 r2 q a0 : Bool) (h : stA r1 r2 q a0 ≠ q) :
    r1 ≠ r2 ∧ a0 = false := by
  cases r1 <;> cases r2 <;> cases q <;> cases a0 <;> simp_all [stA_eq, stF_eq]

/-! ## 2. Settled exclusion -/

/-- **Tier 1, structural.** For every input and every value of q (both grant
outputs reading the SAME value of q), `g1 && g2 = false`. No timing argument. -/
theorem settled_exclusion (r1 r2 q : Bool) : (gr1 r1 r2 q && gr2 r1 r2 q) = false := by
  cases r1 <;> cases r2 <;> cases q <;> rfl

/-- Settled exclusion for `bd_arbiter` too (same grant LUT): stated for every A0. -/
theorem settled_exclusion_arbiter (r1 r2 q _a0 : Bool) :
    (gr1 r1 r2 q && gr2 r1 r2 q) = false := settled_exclusion r1 r2 q

/-- Kleene remark (hypothesis H_KLEENE_LUT of Prelim): with both requests up
and q at an intermediate level, BOTH grant outputs are `x`. So settled
exclusion is a statement about Boolean q only; it says nothing about a
metastable q (tier 3). -/
theorem kleene_x_reaches_both :
    o5K GRANT [.t, .t, .x, .f, .f, .t] = .x ∧ o6K GRANT [.t, .t, .x, .f, .f, .t] = .x := by
  decide

/-! ## 3. The tie

Settled-step (fundamental-mode) model of `bd_arbcell`: the environment changes
the request vector only when q has settled; q then settles in one LUT
evaluation (`stF_idem`). `last` records the side whose grant was last high
(`some true` = side 1). This model has no timing in it; the timing condition it
silently assumes is exactly what Section 4 makes explicit.
-/

/-- Settled state: q and the ghost "last granted side". -/
structure SState where
  q : Bool
  last : Option Bool

/-- One settled step under the new request vector `(r1, r2)`. -/
def sstep (s : SState) (r : Bool × Bool) : SState :=
  let q' := stF r.1 r.2 s.q
  { q := q'
    last := if gr1 r.1 r.2 q' then some true else if gr2 r.1 r.2 q' then some false else s.last }

/-- Run from the reset state (`rst` drives q to 1, nobody granted yet). -/
def srun (rs : List (Bool × Bool)) : SState := rs.foldl sstep ⟨true, none⟩

/-- Invariant: q points at the last granted side (or is the reset value 1
when nobody has been granted yet). -/
def SInv (s : SState) : Prop := s.last = some s.q ∨ (s.last = none ∧ s.q = true)

theorem sstep_inv (s : SState) (r : Bool × Bool) (h : SInv s) : SInv (sstep s r) := by
  obtain ⟨q, last⟩ := s
  obtain ⟨r1, r2⟩ := r
  unfold SInv at *
  simp only [sstep]
  cases r1 <;> cases r2 <;> cases q <;> rcases h with h | ⟨h1, h2⟩ <;>
    simp_all [stF_eq, gr1_eq, gr2_eq]

theorem foldl_inv (rs : List (Bool × Bool)) (s : SState) (h : SInv s) :
    SInv (rs.foldl sstep s) := by
  induction rs generalizing s with
  | nil => exact h
  | cons r rs ih => exact ih _ (sstep_inv s r h)

theorem srun_inv (rs : List (Bool × Bool)) : SInv (srun rs) :=
  foldl_inv rs _ (Or.inr ⟨rfl, rfl⟩)

/-- The bare tie from either q: both requests up, q unchanged, and the grant
goes to the side q points at. -/
theorem tie_holds (q : Bool) :
    stF true true q = q ∧ gr1 true true q = q ∧ gr2 true true q = !q := by
  cases q <;> decide

/-- **The tie grants the previous winner.** After any settled history ending
with both requests down, raising both requests together leaves q unchanged and
grants side 1 iff side 1 was the last side granted (or nobody was yet: reset
value). Side 2 is granted iff side 2 was the last side granted. Exactly one
grant is high. -/
theorem tie_grants_previous_winner (rs : List (Bool × Bool)) :
    let s := sstep (srun rs) (false, false)
    let s' := sstep s (true, true)
    s'.q = s.q ∧
    (gr1 true true s'.q = true ↔ (s.last = some true ∨ s.last = none)) ∧
    (gr2 true true s'.q = true ↔ s.last = some false) ∧
    (gr1 true true s'.q != gr2 true true s'.q) = true := by
  have h := sstep_inv (srun rs) (false, false) (srun_inv rs)
  generalize sstep (srun rs) (false, false) = s at h ⊢
  obtain ⟨q, last⟩ := s
  unfold SInv at h
  simp only [sstep]
  cases q <;> rcases h with h | ⟨h1, h2⟩ <;> simp_all [stF_eq, gr1_eq, gr2_eq]

/-- The same for `bd_arbiter` whatever A0 is during the tie: with A0 low the
state LUT is the arbcell's; with A0 high q is frozen anyway. -/
theorem tie_holds_arbiter (q a0 : Bool) : stA true true q a0 = q := by
  cases q <;> cases a0 <;> rfl

/-! ## 4. The runt: discrete-time transport-delay model of `bd_arbcell`

Time is `Nat` (one tick = an arbitrary quantum). Delay channel: **pure
(transport) delay**, constant within one trace. A trace with constant delays
`L, d5, d6` is in particular a trace of the bounded-delay model for every delay
interval containing them, so the counterexample below is a counterexample for
any interval containing `L = 4`; the positive theorem is proved for every `L`.

* `L`  = the q loop: state-LUT arc plus the routed feedback wire back to the
  state LUT's own `I2` pin AND to the grant LUT's `I2` pin (one net, one delay:
  the grant LUT reads the same q value the state LUT reads; routing skew
  between those two branches is NOT modelled).
* `d5`, `d6` = grant LUT `I*`-to-`O5` / `I*`-to-`O6` (including output routing).
  The requests reach both LUTs at the same instant (no request-routing skew).

Values are binary: a runt that would be an intermediate voltage in silicon shows
up here as a short pulse that circulates in the loop. -/

structure Delays where
  /-- loop delay of q (LUT arc + feedback wire) -/
  L : Nat
  /-- grant LUT to `g1` (O5) -/
  d5 : Nat
  /-- grant LUT to `g2` (O6) -/
  d6 : Nat

structure Trace where
  r1 : Nat → Bool
  r2 : Nat → Bool
  q : Nat → Bool
  g1 : Nat → Bool
  g2 : Nat → Bool

/-- The gate relations of `bd_arbcell` (rst = 0) under transport delay. -/
structure Sat (D : Delays) (tr : Trace) : Prop where
  hq : ∀ t, tr.q (t + D.L) = stF (tr.r1 t) (tr.r2 t) (tr.q t)
  hg1 : ∀ t, tr.g1 (t + D.d5) = gr1 (tr.r1 t) (tr.r2 t) (tr.q t)
  hg2 : ∀ t, tr.g2 (t + D.d6) = gr2 (tr.r1 t) (tr.r2 t) (tr.q t)

/-- A request edge between tick `i` and tick `i+1`. Simultaneous moves of both
requests count as ONE edge. -/
def redge (tr : Trace) (i : Nat) : Prop := tr.r1 (i + 1) ≠ tr.r1 i ∨ tr.r2 (i + 1) ≠ tr.r2 i

/-- **H_INIT_SETTLED**: the trace starts settled: requests and q constant on
`[0, L]`, and q a fixpoint of the state LUT for those requests. (Physically:
reset released and the loop quiet before the first request edge. GLS: check q
and the requests are flat for one loop delay after reset release.) -/
def H_INIT_SETTLED (D : Delays) (tr : Trace) : Prop :=
  (∀ t, t ≤ D.L → tr.r1 t = tr.r1 0 ∧ tr.r2 t = tr.r2 0 ∧ tr.q t = tr.q 0) ∧
  stF (tr.r1 0) (tr.r2 0) (tr.q 0) = tr.q 0

/-- **H_REQ_SEP**: any two request edges (any signal, any sense) are more than
one loop delay apart. This is the timing hypothesis the header's "runt"
paragraph is about; it is a property of the ENVIRONMENT, not of the cell, and it
cannot hold for independent clients (two free-running requesters violate it
with nonzero rate; that rate is the MTBF question). GLS/board: measure the
minimum separation of request edges at the state LUT pins against the routed
loop delay. -/
def H_REQ_SEP (D : Delays) (tr : Trace) : Prop :=
  ∀ i j, i < j → redge tr i → redge tr j → D.L < j - i

/-- **H_GRANT_SKEW**: the O5/O6 skew of the grant LUT is at most one loop delay.
(Header/ARBITER.md: tens of ps in one fractured site against a loop of a LUT
arc plus a hop. GLS: compare the routed O5 and O6 arcs with the q loop.) -/
def H_GRANT_SKEW (D : Delays) : Prop := D.d6 ≤ D.d5 + D.L ∧ D.d5 ≤ D.d6 + D.L

/-! ### helper lemmas -/

/-- Discrete intermediate-value lemma: a Boolean signal that differs at `x` and
`y ≥ x` has an edge in `[x, y)` leaving the value it had at `x`. -/
theorem exists_edge (f : Nat → Bool) (x : Nat) :
    ∀ y, x ≤ y → f y ≠ f x → ∃ u, x ≤ u ∧ u < y ∧ f u = f x ∧ f (u + 1) ≠ f x := by
  intro y
  induction y with
  | zero => intro h hne; have : x = 0 := by omega
            subst this; exact absurd rfl hne
  | succ y ih =>
    intro hxy hne
    by_cases hy : x ≤ y
    · by_cases hfy : f y = f x
      · exact ⟨y, hy, by omega, hfy, hne⟩
      · obtain ⟨u, h1, h2, h3, h4⟩ := ih hy hfy
        exact ⟨u, h1, by omega, h3, h4⟩
    · have : x = y + 1 := by omega
      subst this; exact absurd rfl hne

/-- No request edge on `[x, x+k)` means the requests are equal at `x` and `x+k`. -/
theorem const_of_noedge (tr : Trace) (x : Nat) :
    ∀ k, (∀ i, x ≤ i → i < x + k → ¬ redge tr i) →
      tr.r1 (x + k) = tr.r1 x ∧ tr.r2 (x + k) = tr.r2 x := by
  intro k
  induction k with
  | zero => intro _; exact ⟨rfl, rfl⟩
  | succ k ih =>
    intro h
    obtain ⟨h1, h2⟩ := ih (fun i hi hi' => h i hi (by omega))
    have hk := h (x + k) (by omega) (by omega)
    unfold redge at hk
    have e1 : tr.r1 (x + k + 1) = tr.r1 (x + k) := by
      cases h' : tr.r1 (x + k + 1) <;> cases h'' : tr.r1 (x + k) <;> simp_all
    have e2 : tr.r2 (x + k + 1) = tr.r2 (x + k) := by
      cases h' : tr.r2 (x + k + 1) <;> cases h'' : tr.r2 (x + k) <;> simp_all
    rw [← Nat.add_assoc, e1, e2]; exact ⟨h1, h2⟩

/-- An edge of `r2` alone (or `r1` alone) is a request edge. -/
theorem redge_of_r2 (tr : Trace) (x y : Nat) (hxy : x ≤ y) (h : tr.r2 y ≠ tr.r2 x) :
    ∃ i, x ≤ i ∧ i < y ∧ redge tr i := by
  obtain ⟨u, h1, h2, h3, h4⟩ := exists_edge tr.r2 x y hxy h
  exact ⟨u, h1, h2, Or.inr (by rw [h3]; exact h4)⟩

theorem redge_of_r1 (tr : Trace) (x y : Nat) (hxy : x ≤ y) (h : tr.r1 y ≠ tr.r1 x) :
    ∃ i, x ≤ i ∧ i < y ∧ redge tr i := by
  obtain ⟨u, h1, h2, h3, h4⟩ := exists_edge tr.r1 x y hxy h
  exact ⟨u, h1, h2, Or.inl (by rw [h3]; exact h4)⟩

/-- When the state LUT output differs for two values of q under the same
requests, the requests are a hold state (a tie or both down). -/
theorem stF_dep (a b x y : Bool) (h : stF a b x ≠ stF a b y) : a = b ∧ x ≠ y := by
  cases a <;> cases b <;> cases x <;> cases y <;> simp_all [stF_eq]

theorem stF_hold (a x : Bool) : stF a a x = x := by
  cases a <;> cases x <;> rfl

theorem stF_alone (a b x : Bool) (h : a ≠ b) : stF a b x = a := by
  cases a <;> cases b <;> cases x <;> simp_all [stF_eq]

section transport
variable {D : Delays} {tr : Trace}

/-- Under separation, no request edge lies within `L` before a request edge. -/
theorem sep_before (hSep : H_REQ_SEP D tr) {e : Nat} (he : redge tr e) :
    ∀ i, i < e → e ≤ i + D.L → ¬ redge tr i := by
  intro i h1 h2 hi; have := hSep i e h1 hi he; omega

theorem sep_after (hSep : H_REQ_SEP D tr) {e : Nat} (he : redge tr e) :
    ∀ i, e < i → i ≤ e + D.L → ¬ redge tr i := by
  intro i h1 h2 hi; have := hSep e i h1 he hi; omega

/-- Just before a request edge, q is a fixpoint of the state LUT under the
current requests (the loop had a full loop delay with constant inputs). -/
theorem fix_at_redge (hS : Sat D tr) (hI : H_INIT_SETTLED D tr) (hSep : H_REQ_SEP D tr)
    {e : Nat} (he : redge tr e) : stF (tr.r1 e) (tr.r2 e) (tr.q e) = tr.q e := by
  by_cases hle : e ≤ D.L
  · obtain ⟨a, b, c⟩ := hI.1 e hle
    rw [a, b, c]; exact hI.2
  · obtain ⟨s, rfl⟩ : ∃ s, e = s + D.L := ⟨e - D.L, by omega⟩
    obtain ⟨c1, c2⟩ := const_of_noedge tr s D.L
      (fun i hi hi' => sep_before hSep he i (by omega) (by omega))
    rw [hS.hq s, c1, c2, stF_idem]

/-- **Every q edge is caused by a request edge exactly one loop delay earlier**
(under H_INIT_SETTLED and H_REQ_SEP). Strong induction on time. -/
theorem qedge_cause (hL : 0 < D.L) (hS : Sat D tr) (hI : H_INIT_SETTLED D tr)
    (hSep : H_REQ_SEP D tr) : ∀ s, tr.q (s + D.L + 1) ≠ tr.q (s + D.L) → redge tr s := by
  intro s
  induction s using Nat.strongRecOn with
  | _ s ih =>
  intro hne
  -- q is quiet across any request edge strictly earlier than s
  have quiet : ∀ e, e < s → redge tr e → tr.q (e + 1) = tr.q e := by
    intro e hes he
    by_cases hle : e < D.L
    · rw [(hI.1 (e + 1) (by omega)).2.2, (hI.1 e (by omega)).2.2]
    · obtain ⟨m, rfl⟩ : ∃ m, e = m + D.L := ⟨e - D.L, by omega⟩
      by_cases hq : tr.q (m + D.L + 1) = tr.q (m + D.L)
      · exact hq
      · have hm := ih m (by omega) hq
        have := hSep m (m + D.L) (by omega) hm he
        omega
  by_cases hred : redge tr s
  · exact hred
  exfalso
  have hn := hred
  unfold redge at hn
  have e1 : tr.r1 (s + 1) = tr.r1 s := by
    cases h' : tr.r1 (s + 1) <;> cases h'' : tr.r1 s <;> simp_all
  have e2 : tr.r2 (s + 1) = tr.r2 s := by
    cases h' : tr.r2 (s + 1) <;> cases h'' : tr.r2 s <;> simp_all
  have hq1 : tr.q (s + D.L + 1) = stF (tr.r1 s) (tr.r2 s) (tr.q (s + 1)) := by
    rw [show s + D.L + 1 = (s + 1) + D.L by omega, hS.hq (s + 1), e1, e2]
  have hq0 := hS.hq s
  rw [hq1, hq0] at hne
  obtain ⟨hab, hqs⟩ := stF_dep _ _ _ _ hne
  -- a q edge at s itself
  by_cases hsL : s < D.L
  · exact hqs ((hI.1 (s + 1) (by omega)).2.2.trans (hI.1 s (by omega)).2.2.symm)
  obtain ⟨s', rfl⟩ : ∃ s', s = s' + D.L := ⟨s - D.L, by omega⟩
  have hs' : redge tr s' := ih s' (by omega) (fun h => hqs (by
    rw [show s' + D.L + 1 = s' + D.L + 1 from rfl] at h ⊢; exact h.symm ▸ rfl))
  -- requests constant on [s'+1, s'+L+1]
  obtain ⟨c1, c2⟩ := const_of_noedge tr (s' + 1) D.L
    (fun i hi hi' => sep_after hSep hs' i (by omega) (by omega))
  rw [show s' + 1 + D.L = s' + D.L + 1 by omega] at c1 c2
  -- q(s+1) = q(s'+1) by the hold
  have hA : tr.q (s' + D.L + 1) = tr.q (s' + 1) := by
    rw [show s' + D.L + 1 = (s' + 1) + D.L by omega, hS.hq (s' + 1),
      show s' + 1 + D.L = s' + D.L + 1 by omega] at *
    rw [← c1, ← c2, e1, e2, hab, stF_hold]
  -- q(s) = q(s')
  have hB : tr.q (s' + D.L) = tr.q s' := by rw [hS.hq s', fix_at_redge hS hI hSep hs']
  have hC : tr.q (s' + 1) = tr.q s' := quiet s' (by omega) hs'
  exact hqs (by rw [hA, hB, hC])

/-- A q edge at `s + L` goes to the value the lone request asks for: the
requests one tick after the causing edge are `r1 ≠ r2` and `q` follows `r1`. -/
theorem qedge_kind (hL : 0 < D.L) (hS : Sat D tr) (hI : H_INIT_SETTLED D tr)
    (hSep : H_REQ_SEP D tr) (s : Nat) (hne : tr.q (s + D.L + 1) ≠ tr.q (s + D.L)) :
    tr.r1 (s + 1) ≠ tr.r2 (s + 1) ∧ tr.q (s + D.L + 1) = tr.r1 (s + 1) := by
  have hs := qedge_cause hL hS hI hSep s hne
  have hq1 : tr.q (s + D.L + 1) = stF (tr.r1 (s + 1)) (tr.r2 (s + 1)) (tr.q (s + 1)) := by
    rw [show s + D.L + 1 = (s + 1) + D.L by omega, hS.hq (s + 1)]
  have hquiet : tr.q (s + 1) = tr.q s := by
    by_cases hle : s < D.L
    · rw [(hI.1 (s + 1) (by omega)).2.2, (hI.1 s (by omega)).2.2]
    · obtain ⟨m, rfl⟩ : ∃ m, s = m + D.L := ⟨s - D.L, by omega⟩
      by_cases hq : tr.q (m + D.L + 1) = tr.q (m + D.L)
      · exact hq
      · have hm := qedge_cause hL hS hI hSep m hq
        have := hSep m (m + D.L) (by omega) hm hs
        omega
  have hfix : tr.q (s + D.L) = tr.q s := by rw [hS.hq s, fix_at_redge hS hI hSep hs]
  by_cases hab : tr.r1 (s + 1) = tr.r2 (s + 1)
  · exfalso; apply hne; rw [hq1, hab, stF_hold, hquiet, hfix]
  · exact ⟨hab, by rw [hq1, stF_alone _ _ _ hab]⟩

/-- **Exclusion in the transport model, under named timing hypotheses.**
With the loop delay `L ≥ 1`, a settled start, request edges more than one loop
delay apart, and grant O5/O6 skew at most one loop delay, `g1` and `g2` are
never high together (at every instant where both grant outputs are defined by
their relations). -/
theorem exclusion_transport (hL : 0 < D.L) (hS : Sat D tr) (hI : H_INIT_SETTLED D tr)
    (hSep : H_REQ_SEP D tr) (hSk : H_GRANT_SKEW D) (T : Nat) (h5 : D.d5 ≤ T) (h6 : D.d6 ≤ T) :
    (tr.g1 T && tr.g2 T) = false := by
  obtain ⟨sk1, sk2⟩ := hSk
  obtain ⟨b, rfl⟩ : ∃ b, T = b + D.d5 := ⟨T - D.d5, by omega⟩
  obtain ⟨a, ha⟩ : ∃ a, b + D.d5 = a + D.d6 := ⟨b + D.d5 - D.d6, by omega⟩
  have g1v := hS.hg1 b
  have g2v := hS.hg2 a
  rw [← ha] at g2v
  rw [g1v, g2v, gr1_eq, gr2_eq]
  cases hr1 : tr.r1 b <;> cases hr2 : tr.r2 a <;> cases hqb : tr.q b <;> cases hqa : tr.q a <;>
    simp only [Bool.false_and, Bool.and_false, Bool.true_and, Bool.not_true, Bool.not_false]
  all_goals first | rfl | skip
  -- remaining: r1 b, r2 a, q b = true, q a = false
  · exfalso
    by_cases hab : a ≤ b
    · -- q rises in [a, b): set at s+L, but r2 was up at a
      obtain ⟨u, hu1, hu2, hu3, hu4⟩ := exists_edge tr.q a b hab (by rw [hqb, hqa]; decide)
      rw [hqa] at hu3 hu4
      by_cases huL : u < D.L
      · have := (hI.1 (u + 1) (by omega)).2.2.trans (hI.1 u (by omega)).2.2.symm
        rw [this, hu3] at hu4; exact hu4 rfl
      obtain ⟨s, rfl⟩ : ∃ s, u = s + D.L := ⟨u - D.L, by omega⟩
      have hne : tr.q (s + D.L + 1) ≠ tr.q (s + D.L) := by rw [hu3]; exact hu4
      obtain ⟨k1, k2⟩ := qedge_kind hL hS hI hSep s hne
      have hcs := qedge_cause hL hS hI hSep s hne
      have hq1 : tr.q (s + D.L + 1) = true := by
        cases h : tr.q (s + D.L + 1) <;> simp_all
      rw [hq1] at k2
      have hr2s : tr.r2 (s + 1) = false := by
        cases h : tr.r2 (s + 1) <;> simp_all
      obtain ⟨i, hi1, hi2, hi3⟩ := redge_of_r2 tr (s + 1) a (by omega) (by rw [hr2, hr2s]; decide)
      have := hSep s i (by omega) hcs hi3
      omega
    · -- q falls in [b, a): reset at s+L, but r1 was up at b
      obtain ⟨u, hu1, hu2, hu3, hu4⟩ := exists_edge tr.q b a (by omega) (by rw [hqb, hqa]; decide)
      rw [hqb] at hu3 hu4
      by_cases huL : u < D.L
      · have := (hI.1 (u + 1) (by omega)).2.2.trans (hI.1 u (by omega)).2.2.symm
        rw [this, hu3] at hu4; exact hu4 rfl
      obtain ⟨s, rfl⟩ : ∃ s, u = s + D.L := ⟨u - D.L, by omega⟩
      have hne : tr.q (s + D.L + 1) ≠ tr.q (s + D.L) := by rw [hu3]; exact hu4
      obtain ⟨k1, k2⟩ := qedge_kind hL hS hI hSep s hne
      have hcs := qedge_cause hL hS hI hSep s hne
      have hq1 : tr.q (s + D.L + 1) = false := by
        cases h : tr.q (s + D.L + 1) <;> simp_all
      rw [hq1] at k2
      obtain ⟨i, hi1, hi2, hi3⟩ := redge_of_r1 tr (s + 1) b (by omega) (by rw [hr1, ← k2]; decide)
      have := hSep s i (by omega) hcs hi3
      omega

/-- With zero grant skew (`d5 = d6`) exclusion holds for EVERY trace, even an
oscillating one: both outputs then sample the same q at the same instant. -/
theorem exclusion_zero_skew (hS : Sat D tr) (h : D.d5 = D.d6) (t : Nat) :
    (tr.g1 (t + D.d5) && tr.g2 (t + D.d5)) = false := by
  rw [hS.hg1 t]; rw [h, hS.hg2 t]; exact settled_exclusion _ _ _

end transport

/-! ### The hypotheses are not vacuous: a clean contended handover

r1 rises at 6, r2 rises at 12 (r2 waits), r1 falls at 18 (r2 takes over).
Edges 6 ticks apart, `L = 4`. -/

def runtD : Delays := ⟨4, 1, 2⟩

/-- `L = 4, d5 = 1, d6 = 2`: grant skew within one loop delay. -/
theorem runt_skew : H_GRANT_SKEW runtD := by unfold H_GRANT_SKEW runtD; decide

def hoR1 (t : Nat) : Bool := decide (6 ≤ t ∧ t < 18)
def hoR2 (t : Nat) : Bool := decide (12 ≤ t)
def hoQ (t : Nat) : Bool := decide (10 ≤ t ∧ t < 22)
def hoG1 : Nat → Bool
  | 0 => false
  | t + 1 => gr1 (hoR1 t) (hoR2 t) (hoQ t)
def hoG2 : Nat → Bool
  | 0 => false
  | 1 => false
  | t + 2 => gr2 (hoR1 t) (hoR2 t) (hoQ t)
def hoTrace : Trace := ⟨hoR1, hoR2, hoQ, hoG1, hoG2⟩

theorem ho_sat : Sat runtD hoTrace where
  hq := by intro t; simp only [hoTrace, runtD, hoQ, hoR1, hoR2, stF_eq]; arbbin_omega
  hg1 := fun _ => rfl
  hg2 := fun _ => rfl

theorem ho_init : H_INIT_SETTLED runtD hoTrace := by
  refine ⟨fun t ht => ?_, rfl⟩
  simp only [hoTrace, runtD, hoR1, hoR2, hoQ] at *
  refine ⟨?_, ?_, ?_⟩ <;> arbbin_omega

theorem ho_sep : H_REQ_SEP runtD hoTrace := by
  intro i j hij hi hj
  simp only [redge, hoTrace, hoR1, hoR2, runtD, ne_eq] at *
  arbbin_omega

/-- Both clients are actually served (g1 at 11, g2 at 24), so the exclusion
theorem applies to a trace with a real contended handover. -/
theorem ho_serves : hoG1 11 = true ∧ hoG2 24 = true := by decide

theorem ho_exclusion (T : Nat) (h : 2 ≤ T) : (hoG1 T && hoG2 T) = false :=
  exclusion_transport (D := runtD) (tr := hoTrace) (by decide) ho_sat ho_init ho_sep runt_skew T
    (by simp [runtD]; omega) (by simp [runtD]; omega)

/-! ### The runt: a concrete trace

`L = 4`, `d5 = 1`, `d6 = 2` (O6 slower than O5, as in prjxray's fall arcs; any
nonzero skew would do, see `runt_overlap_needs_skew`). Both requests start low,
r1 rises at tick 6, r2 rises at tick 8: two SAME-sense edges 2 ticks apart,
less than one loop delay. The set condition `r1.~r2` is a runt of width 2; the
loop captures it and, since `r1 = r2 = 1` afterwards is a hold state, the
pulse circulates forever: q never settles. -/

def runtR1 (t : Nat) : Bool := decide (6 ≤ t)
def runtR2 (t : Nat) : Bool := decide (8 ≤ t)
def runtQ (t : Nat) : Bool := decide (10 ≤ t ∧ (t % 4 = 2 ∨ t % 4 = 3))
def runtG1 : Nat → Bool
  | 0 => false
  | t + 1 => gr1 (runtR1 t) (runtR2 t) (runtQ t)
def runtG2 : Nat → Bool
  | 0 => false
  | 1 => false
  | t + 2 => gr2 (runtR1 t) (runtR2 t) (runtQ t)

def runtTrace : Trace := ⟨runtR1, runtR2, runtQ, runtG1, runtG2⟩

/-- The runt trace satisfies every gate relation (real INITs, transport delay). -/
theorem runt_sat : Sat runtD runtTrace where
  hq := by
    intro t
    simp only [runtTrace, runtD, runtQ, runtR1, runtR2, stF_eq]
    by_cases h1 : 6 ≤ t <;> by_cases h2 : 8 ≤ t <;> by_cases h3 : 10 ≤ t <;>
      simp [h1, h2, h3] <;> omega
  hg1 := fun _ => rfl
  hg2 := fun _ => rfl

/-- It starts settled (so the failure is not an initial-condition artefact). -/
theorem runt_init : H_INIT_SETTLED runtD runtTrace := by
  refine ⟨fun t ht => ?_, rfl⟩
  simp only [runtTrace, runtD, runtR1, runtR2, runtQ] at *
  refine ⟨?_, ?_, ?_⟩ <;> simp <;> omega


/-- It violates request separation: edges at ticks 5 and 7 (r1 and r2 both RISING). -/
theorem runt_not_sep : ¬ H_REQ_SEP runtD runtTrace := by
  intro h
  have := h 5 7 (by decide) (Or.inl (by decide)) (Or.inr (by decide))
  simp [runtD] at this

/-- **q oscillates forever**: in every loop period it is high at `4k+10` and low
at `4k+12` (a 2-tick pulse every 4 ticks). -/
theorem runt_oscillates (k : Nat) : runtQ (4 * k + 10) = true ∧ runtQ (4 * k + 12) = false := by
  simp only [runtQ]; constructor <;> simp <;> omega

/-- **Binary overlap**: both grants are high at `4k+11`, for every `k`. -/
theorem runt_overlap (k : Nat) : runtG1 (4 * k + 11) = true ∧ runtG2 (4 * k + 11) = true := by
  show gr1 (runtR1 (4 * k + 10)) (runtR2 (4 * k + 10)) (runtQ (4 * k + 10)) = true ∧
    gr2 (runtR1 (4 * k + 9)) (runtR2 (4 * k + 9)) (runtQ (4 * k + 9)) = true
  simp only [gr1_eq, gr2_eq, runtR1, runtR2, runtQ]
  constructor <;> simp <;> omega

/-- So exclusion is not a consequence of the gate relations, the settled start
and the skew bound alone: the separation hypothesis cannot be dropped. -/
theorem exclusion_needs_sep :
    ∃ (D : Delays) (tr : Trace), 0 < D.L ∧ Sat D tr ∧ H_INIT_SETTLED D tr ∧ H_GRANT_SKEW D ∧
      ∃ T, D.d5 ≤ T ∧ D.d6 ≤ T ∧ (tr.g1 T && tr.g2 T) = true :=
  ⟨runtD, runtTrace, by decide, runt_sat, runt_init, runt_skew, 11, by decide, by decide,
    by have := runt_overlap 0; simp only [runtTrace]; rw [this.1, this.2]; rfl⟩

/-- In the same trace with zero skew the grants never overlap (they pulse
together with q instead): overlap in the binary model needs a runt AND skew. -/
theorem runt_overlap_needs_skew (t : Nat) :
    (gr1 (runtR1 t) (runtR2 t) (runtQ t) && gr2 (runtR1 t) (runtR2 t) (runtQ t)) = false :=
  settled_exclusion _ _ _

/-! ### Opposite-sense request moves are clean

The header and ARBITER.md locate the runt at "r1 and r2 moving in OPPOSITE
senses within one loop delay". In this model that case is always clean, at any
separation, even zero or less than `L`: the set condition `r1.~r2` is monotone
and the reset `~r1.r2` is antitone, so q makes exactly one clean edge. The runt
needs the set/reset LITERALS (`r1`, `~r2`) to move in opposite senses, i.e.
r1 and r2 moving in the SAME sense (the trace above), or one request pulsing. -/

/-- r1 rises at `e1`, r2 falls at `e2` (any order, any gap), q starts low
(r2 was being served): q has exactly one edge, at `max e1 e2 + L`. -/
theorem opposite_sense_clean_rise (D : Delays) (tr : Trace) (hL : 0 < D.L) (hS : Sat D tr)
    (e1 e2 : Nat) (h1 : ∀ t, tr.r1 t = decide (e1 ≤ t)) (h2 : ∀ t, tr.r2 t = !decide (e2 ≤ t))
    (h0 : ∀ t, t < D.L → tr.q t = false) :
    ∀ t, tr.q t = decide (max e1 e2 + D.L ≤ t) := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
  by_cases ht : t < D.L
  · rw [h0 t ht]; simp; omega
  obtain ⟨s, rfl⟩ : ∃ s, t = s + D.L := ⟨t - D.L, by omega⟩
  rw [hS.hq s, ih s (by omega), h1, h2, stF_eq]
  by_cases a : e1 ≤ s <;> by_cases b : e2 ≤ s <;> simp [a, b] <;> omega

/-- r1 falls at `e1`, r2 rises at `e2`, q starts high: one clean falling edge. -/
theorem opposite_sense_clean_fall (D : Delays) (tr : Trace) (hL : 0 < D.L) (hS : Sat D tr)
    (e1 e2 : Nat) (h1 : ∀ t, tr.r1 t = !decide (e1 ≤ t)) (h2 : ∀ t, tr.r2 t = decide (e2 ≤ t))
    (h0 : ∀ t, t < D.L → tr.q t = true) :
    ∀ t, tr.q t = !decide (max e1 e2 + D.L ≤ t) := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
  by_cases ht : t < D.L
  · rw [h0 t ht]; simp; omega
  obtain ⟨s, rfl⟩ : ∃ s, t = s + D.L := ⟨t - D.L, by omega⟩
  rw [hS.hq s, ih s (by omega), h1, h2, stF_eq]
  by_cases a : e1 ≤ s <;> by_cases b : e2 ≤ s <;> simp [a, b] <;> omega

/-- And in the opposite-sense handover the grants never overlap, at ANY request
separation, given only the skew bound. -/
theorem opposite_sense_exclusion (D : Delays) (tr : Trace) (hL : 0 < D.L) (hS : Sat D tr)
    (hSk : H_GRANT_SKEW D)
    (e1 e2 : Nat) (h1 : ∀ t, tr.r1 t = decide (e1 ≤ t)) (h2 : ∀ t, tr.r2 t = !decide (e2 ≤ t))
    (h0 : ∀ t, t < D.L → tr.q t = false) (T : Nat) (h5 : D.d5 ≤ T) (h6 : D.d6 ≤ T) :
    (tr.g1 T && tr.g2 T) = false := by
  have hq := opposite_sense_clean_rise D tr hL hS e1 e2 h1 h2 h0
  obtain ⟨sk1, sk2⟩ := hSk
  obtain ⟨b, rfl⟩ : ∃ b, T = b + D.d5 := ⟨T - D.d5, by omega⟩
  obtain ⟨a, ha⟩ : ∃ a, b + D.d5 = a + D.d6 := ⟨b + D.d5 - D.d6, by omega⟩
  have g2v := hS.hg2 a
  rw [← ha] at g2v
  rw [hS.hg1 b, g2v, gr1_eq, gr2_eq, hq a, hq b, h1, h2]
  cases hx : decide (max e1 e2 + D.L ≤ a) <;> cases hy : decide (max e1 e2 + D.L ≤ b) <;>
    cases hz : decide (e1 ≤ b) <;> cases hw : decide (e2 ≤ a) <;> simp_all <;> omega

/-! ### Does an inertial delay change the runt result?

Discrete inertial channel with window `δ`: the output takes the input's value
`x(t+1)` at tick `t+δ+1` only if the input stayed at that value over the whole
window `[t+1, t+δ+1]`; otherwise the output holds. A pulse of `δ` ticks or fewer
is swallowed; a pulse of `δ+1` ticks or more is passed, delayed by `δ`, with its
width unchanged. Loop of `bd_arbcell`: the state LUT's function `x`
(zero-delay part), the inertial channel to the LUT output `y`, and a transport
feedback wire `W` back to the `I2` pin (`qfb`). Total loop delay `δ + W`.

Result (concrete, `δ = 1`, `W = 3`, loop 4, as in the transport trace): a runt
of width 1 is swallowed (q never moves; r1 asked first and r2 is granted after
it rises: the race is decided silently and arbitrarily), and a runt of width 2
still circulates forever. So an inertial channel only moves the threshold; any
runt wider than the window but narrower than the loop survives (argued, proved
here only for the instance). The window of surviving runt widths is non-empty
whenever the feedback wire adds delay beyond the inertial window. Neither binary channel is faithful here: in silicon the runt neither
vanishes cleanly nor circulates unchanged, it decays or grows (that needs the
involution channel or the analog model, probe 7c). -/


/-- The inertial channel, window `δ`: if the input was stable on
`[t+1, t+δ+1]` the output takes that value at `t+δ+1`, else it holds. -/
def inertialOK (δ : Nat) (x y : Nat → Bool) : Prop :=
  ∀ t, ((∀ i, i ≤ δ → x (t + 1 + i) = x (t + 1)) → y (t + δ + 1) = x (t + 1)) ∧
       (¬ (∀ i, i ≤ δ → x (t + 1 + i) = x (t + 1)) → y (t + δ + 1) = y (t + δ))

theorem window1 (x : Nat → Bool) (t : Nat) :
    (∀ i, i ≤ 1 → x (t + 1 + i) = x (t + 1)) ↔ x (t + 2) = x (t + 1) := by
  constructor
  · intro h; exact h 1 (by omega)
  · intro h i hi
    cases i with
    | zero => rfl
    | succ i => have : i = 0 := by omega
                subst this; exact h

/-- The `bd_arbcell` loop with an inertial LUT and a transport feedback wire. -/
structure InSat (δ W : Nat) (r1 r2 x y qfb : Nat → Bool) : Prop where
  hx : ∀ t, x t = stF (r1 t) (r2 t) (qfb t)
  hy : inertialOK δ x y
  hw : ∀ t, qfb (t + W) = y t
  hw0 : ∀ t, t < W → qfb t = false
  hy0 : ∀ t, t ≤ δ → y t = false

/-- Width-1 runt (r1 at 6, r2 at 7), `δ = 1`: swallowed, q stays 0 forever. -/
theorem inertial_swallows_narrow_runt :
    InSat 1 3 (fun t => decide (6 ≤ t)) (fun t => decide (7 ≤ t))
      (fun t => decide (t = 6)) (fun _ => false) (fun _ => false) where
  hx := by intro t; simp only [stF_eq, Bool.false_and, Bool.or_false]; arbbin_omega
  hy := by
    intro t; rw [window1 (fun t => decide (t = 6)) t]
    constructor
    · intro h; simp only at *; arbbin_omega
    · intro _; rfl
  hw := fun _ => rfl
  hw0 := fun _ _ => rfl
  hy0 := fun _ _ => rfl

def inQ (t : Nat) : Bool := decide (7 ≤ t ∧ (t % 4 = 3 ∨ t % 4 = 0))
def inFb (t : Nat) : Bool := decide (10 ≤ t ∧ (t % 4 = 2 ∨ t % 4 = 3))
def inX (t : Nat) : Bool := decide (t = 6 ∨ t = 7 ∨ (10 ≤ t ∧ (t % 4 = 2 ∨ t % 4 = 3)))

/-- Width-2 runt (r1 at 6, r2 at 8), `δ = 1`: passes the inertial window and
circulates forever. -/
theorem inertial_passes_wider_runt :
    InSat 1 3 (fun t => decide (6 ≤ t)) (fun t => decide (8 ≤ t)) inX inQ inFb where
  hx := by intro t; simp only [stF_eq, inX, inFb]; arbbin_omega
  hy := by
    intro t; rw [window1 inX t]
    constructor
    · intro h; simp only [inX, inQ] at *; arbbin_omega
    · intro h; simp only [inX, inQ] at *; arbbin_omega
  hw := by intro t; simp only [inFb, inQ]; arbbin_omega
  hw0 := by intro t ht; simp only [inFb]; arbbin_omega
  hy0 := by intro t ht; simp only [inQ]; arbbin_omega

theorem inertial_runt_oscillates (k : Nat) : inQ (4 * k + 7) = true ∧ inQ (4 * k + 9) = false := by
  simp only [inQ]; constructor <;> simp <;> omega

/-! ## 5. `bd_arbiter` under sustained contention: interleaving model

Speed-independent (unbounded, unknown gate delays) interleaving semantics: at
each step any ONE excited gate fires (its output takes its function's value).
Gates, all from the real INITs (rst = 0):
`q = stA(r1,r2,q,A0)` (O6) and `R0 = r0A(..)` (O5) of `ustate`; `g1`, `g2` (O5,
O6 of `ugrant`); `A1 = C(g1,A0)`, `A2 = C(g2,A0)` (`bd_c2`). Environment:
two always-wanting four-phase clients (`ri` rises when `Ai` is low, falls when
`Ai` is high) and a four-phase server (`A0` follows `R0`).
Initial state: after reset, q = 1, everything else 0.

Each gate is ATOMIC here: no intermediate values, a disabled excitation simply
does not fire. In silicon a disabled excitation is a runt; this model shows
WHERE runts can happen, not what they do.

State encoding (for fast kernel evaluation): bits 0..8 =
`r1 r2 q R0 g1 g2 A1 A2 A0`; the value `s / 512` holds two ghost variables:
`last = (s/512) % 3` (0 none, 1, 2: the side last acknowledged) and
`owed = (s/512) / 3` (0 none, 1, 2: the side that was waiting when the server
ended the previous transaction; alternation says the next grant goes to it).

Timing hypotheses, as switches that disable transitions:
* `h1` **H_SERVER_AFTER_GRANTS**: the server does not move A0 while `g1` or
  `g2` is excited. (One grant-LUT arc versus R0-LUT arc + server response;
  GLS: grant-fall to A0-fall margin.)
* `h2` **H_Q_BEFORE_REREQ**: a client does not raise its request while q is
  excited. (q's LUT arc + feedback versus A1-fall + client response + request
  route; this is the header's "one arc of margin". GLS/board: alternation count.)
* `h3` **H_SERVER_AFTER_ACKS**: the server does not move A0 while `A1` or `A2`
  is excited. (Ack C-element arc versus q + R0 + server; GLS: A1-fall to
  A0-rise margin.) -/

structure Hyp where
  h1 : Bool
  h2 : Bool
  h3 : Bool

def bitAt (s i : Nat) : Bool := s.testBit i

/-- Gate function of node `i` (0..8) in state `s`. -/
def fn (s i : Nat) : Bool :=
  let r1 := bitAt s 0; let r2 := bitAt s 1; let q := bitAt s 2; let R0 := bitAt s 3
  let g1 := bitAt s 4; let g2 := bitAt s 5; let A1 := bitAt s 6; let A2 := bitAt s 7
  let A0 := bitAt s 8
  match i with
  | 0 => !A1
  | 1 => !A2
  | 2 => stA r1 r2 q A0
  | 3 => r0A r1 r2 q A0
  | 4 => gr1 r1 r2 q
  | 5 => gr2 r1 r2 q
  | 6 => c2 g1 A0 A1
  | 7 => c2 g2 A0 A2
  | _ => R0

def excited (s i : Nat) : Bool := fn s i != bitAt s i

def enabled (h : Hyp) (s i : Nat) : Bool :=
  decide (i < 9) && excited s i &&
  !(h.h2 && decide (i < 2) && fn s i && excited s 2) &&
  !(h.h1 && decide (i = 8) && (excited s 4 || excited s 5)) &&
  !(h.h3 && decide (i = 8) && (excited s 6 || excited s 7))

def lastOf (s : Nat) : Nat := (s / 512) % 3
def owedOf (s : Nat) : Nat := (s / 512) / 3

/-- Fire node `i`: flip its bit and update the ghosts. -/
def fire (s i : Nat) : Nat :=
  let v := fn s i
  let core := s % 512
  let core' := if v then core + 2 ^ i else core - 2 ^ i
  let last := lastOf s
  let owed := owedOf s
  let last' := if i = 6 && v then 1 else if i = 7 && v then 2 else last
  let owed' :=
    if i = 8 && !v && last == 1 && bitAt s 1 then 2
    else if i = 8 && !v && last == 2 && bitAt s 0 then 1
    else if i = 4 && v && owed == 1 then 0
    else if i = 5 && v && owed == 2 then 0
    else owed
  core' + 512 * (last' + 3 * owed')

/-- Alternation violation: a grant rises for one side while the OTHER side is owed. -/
def altBad (s i : Nat) : Bool :=
  (i == 4 && fn s i && owedOf s == 2) || (i == 5 && fn s i && owedOf s == 1)

/-- Exclusion / protocol violation in a state. -/
def stateBad (s : Nat) : Bool :=
  (bitAt s 4 && bitAt s 5) || (bitAt s 6 && bitAt s 7)

/-- After reset: q = 1, all else 0, no ghost. -/
def init0 : Nat := 4

inductive Reach (h : Hyp) : Nat → Prop
  | init : Reach h init0
  | step (s i : Nat) : Reach h s → enabled h s i = true → Reach h (fire s i)

/-- Breadth-first exploration with fuel (structural recursion only). -/
def explore (h : Hyp) : Nat → List Nat → List Nat → List Nat
  | 0, _, seen => seen
  | _ + 1, [], seen => seen
  | n + 1, x :: front, seen =>
    let new := (List.range 9).foldl
      (fun acc i => if enabled h x i then
          (let y := fire x i; if seen.contains y || acc.contains y then acc else acc ++ [y])
        else acc) []
    explore h n (front ++ new) (seen ++ new)

def allHyp : Hyp := ⟨true, true, true⟩

/-- Reachable-set certificate under all three hypotheses. -/
def R3 : List Nat := explore allHyp 400 [init0] [init0]

/-- Certificate, checked by kernel evaluation (one evaluation of `R3`): `R3`
contains the initial state, is closed under every enabled transition, has no
bad state, and has no enabled alternation-violating transition. -/
def certOK (h : Hyp) (R : List Nat) : Bool :=
  R.contains init0 &&
  R.all (fun s => !stateBad s &&
    (List.range 9).all (fun i => !enabled h s i || (R.contains (fire s i) && !altBad s i)))

theorem R3_cert : certOK allHyp R3 = true := by decide +kernel

theorem R3_init : R3.contains init0 = true := by
  have h := R3_cert; unfold certOK at h; simp only [Bool.and_eq_true] at h; exact h.1

theorem R3_all : R3.all (fun s => !stateBad s &&
    (List.range 9).all (fun i => !enabled allHyp s i || (R3.contains (fire s i) && !altBad s i)))
    = true := by
  have h := R3_cert; unfold certOK at h; simp only [Bool.and_eq_true] at h; exact h.2

theorem reach_R3 (s : Nat) (h : Reach allHyp s) : R3.contains s = true := by
  induction h with
  | init => exact R3_init
  | step s i _ hen ih =>
    have hc := R3_all
    rw [List.all_eq_true] at hc
    have hs := hc s (by simpa using ih)
    simp only [Bool.and_eq_true] at hs
    have hs := hs.2
    rw [List.all_eq_true] at hs
    have hi : i < 9 := by
      unfold enabled at hen
      cases hd : decide (i < 9) <;> simp_all
    have := hs i (List.mem_range.mpr hi)
    rw [hen] at this
    simp at this
    simpa using this.1

/-- **Under H_SERVER_AFTER_GRANTS, H_Q_BEFORE_REREQ and H_SERVER_AFTER_ACKS,
`bd_arbiter` never has both grants high and never acknowledges both clients.** -/
theorem arbiter_exclusion (s : Nat) (h : Reach allHyp s) :
    (bitAt s 4 && bitAt s 5) = false ∧ (bitAt s 6 && bitAt s 7) = false := by
  have hm := reach_R3 s h
  have hs := R3_all
  rw [List.all_eq_true] at hs
  have := hs s (by simpa using hm)
  simp only [Bool.and_eq_true] at this
  have := this.1
  unfold stateBad at this
  cases h1 : (bitAt s 4 && bitAt s 5) <;> cases h2 : (bitAt s 6 && bitAt s 7) <;> simp_all

/-- **Alternation under sustained contention** (same hypotheses): if a client
was waiting when the server ended the other client's transaction, the next grant
to rise is the waiting client's. -/
theorem arbiter_alternates (s i : Nat) (h : Reach allHyp s) (hen : enabled allHyp s i = true) :
    altBad s i = false := by
  have hm := reach_R3 s h
  have hs := R3_all
  rw [List.all_eq_true] at hs
  have h2 := hs s (by simpa using hm)
  simp only [Bool.and_eq_true] at h2
  have h2 := h2.2
  rw [List.all_eq_true] at h2
  have hi : i < 9 := by
    unfold enabled at hen
    cases hd : decide (i < 9) <;> simp_all
  have := h2 i (List.mem_range.mpr hi)
  rw [hen] at this
  simp at this
  cases hb : altBad s i <;> simp_all

/-! ### Each hypothesis is needed: concrete firing sequences -/

/-- Follow a list of firings; `none` if one is not enabled. -/
def runFires (h : Hyp) : Nat → List Nat → Option Nat
  | s, [] => some s
  | s, i :: is => if enabled h s i then runFires h (fire s i) is else none

theorem runFires_reach (h : Hyp) : ∀ (is : List Nat) (s t : Nat), Reach h s →
    runFires h s is = some t → Reach h t := by
  intro is
  induction is with
  | nil => intro s t hs hr; simp [runFires] at hr; exact hr ▸ hs
  | cons i is ih =>
    intro s t hs hr
    simp only [runFires] at hr
    split at hr
    · exact ih _ _ (Reach.step s i hs (by assumption)) hr
    · cases hr

/-- Without H_SERVER_AFTER_GRANTS (h2, h3 on): both grants high. `g1` is slow to
fall after `r1` falls; the server finishes, q flips and `g2` rises.
Firings: r1 r2 R0 g1 A0 A1 r1 R0 A0 q g2. -/
theorem need_h1 : ∃ t, Reach ⟨false, true, true⟩ t ∧ (bitAt t 4 && bitAt t 5) = true :=
  ⟨_, runFires_reach _ [0, 1, 3, 4, 8, 6, 0, 3, 8, 2, 5] init0 _ Reach.init rfl, by decide⟩

/-- Without H_SERVER_AFTER_ACKS (h1, h2 on): both clients acknowledged. `A1` is
slow to fall; the server serves client 2 while `A1` still holds high.
Firings: r1 r2 R0 g1 A0 A1 r1 R0 g1 A0 q R0 g2 A0 A2. -/
theorem need_h3 : ∃ t, Reach ⟨true, true, false⟩ t ∧ (bitAt t 6 && bitAt t 7) = true :=
  ⟨_, runFires_reach _ [0, 1, 3, 4, 8, 6, 0, 3, 4, 8, 2, 3, 5, 8, 7] init0 _ Reach.init rfl,
    by decide⟩

/-- Without H_Q_BEFORE_REREQ (h1, h3 on): **no alternation**. Client 2 is
waiting when the server ends client 1's transaction (q excited to fall); A1
falls, client 1 re-raises r1 before q fires, the tie holds q, and client 1 is
granted again. This is the header's "request coincident with A0-fall": in
silicon the withdrawn excitation of q is a runt.
Firings: r1 r2 R0 g1 A0 A1 r1 R0 g1 A0 A1 r1 [g1 rises]. -/
theorem need_h2 : ∃ t i, Reach ⟨true, false, true⟩ t ∧ enabled ⟨true, false, true⟩ t i = true ∧
    altBad t i = true :=
  ⟨_, 4, runFires_reach _ [0, 1, 3, 4, 8, 6, 0, 3, 4, 8, 6, 0] init0 _ Reach.init rfl,
    by decide, by decide⟩

/-- In that run q was excited (to hand over to client 2) when r1 rose, and the
r1 rise withdrew the excitation: the tie rule (`tie_holds_arbiter`). -/
theorem need_h2_q_disabled :
    (runFires ⟨true, false, true⟩ init0 [0, 1, 3, 4, 8, 6, 0, 3, 4, 8, 6]).map
      (fun t => excited t 2 && !excited (fire t 0) 2 && bitAt t 1) = some true := by decide

/-- Without any hypothesis all three failures are reachable (the unbounded-delay
model proves none of the header's three-tier claims beyond tier 1). -/
theorem no_hyp_fails :
    (∃ t, Reach ⟨false, false, false⟩ t ∧ (bitAt t 4 && bitAt t 5) = true) ∧
    (∃ t, Reach ⟨false, false, false⟩ t ∧ (bitAt t 6 && bitAt t 7) = true) :=
  ⟨⟨_, runFires_reach _ [0, 1, 3, 4, 8, 6, 0, 3, 8, 2, 5] init0 _ Reach.init rfl, by decide⟩,
   ⟨_, runFires_reach _ [0, 1, 3, 4, 8, 6, 0, 3, 8, 2, 3, 5, 8, 7] init0 _ Reach.init rfl,
    by decide⟩⟩

/-- **q moves only while exactly one request is up and A0 is low**, in every
state of the interleaving model (it is a property of the INIT). -/
theorem q_moves_only_alone (s : Nat) (h : excited s 2 = true) :
    bitAt s 0 ≠ bitAt s 1 ∧ bitAt s 8 = false := by
  have hf : fn s 2 = stA (bitAt s 0) (bitAt s 1) (bitAt s 2) (bitAt s 8) := rfl
  unfold excited at h
  rw [hf] at h
  have hne : stA (bitAt s 0) (bitAt s 1) (bitAt s 2) (bitAt s 8) ≠ bitAt s 2 := by
    intro e; rw [e] at h; simp at h
  exact stA_moves_only_if_alone _ _ _ _ hne

end Formal.Cells.ArbBinary
