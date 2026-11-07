import Formal.Cells.ArbBinary
import Formal.Cells.LibGapSteer

/-!
# ArbPin: `bd_arbcell` with per-pin, NON-monotone read maps

Probe Barp (shard B, PROGRAM.md item 4). The arbiter as a digital race of
LUTs and wires, in the most general per-pin model used in this shard so far
(`LibGapSteer.Rd`): every LUT pin shows its driver at SOME instant of its
delay window, chosen freely at every output instant (no FIFO, no monotonicity,
no transport). Strictly more behaviours than transport/FIFO or atomic LUTs.

## The cell (`cells/rtl/bd_arb.v`, `bd_arbcell`), real INITs, real pin maps

    ustate  bd_c2n_set  INIT FFB2_FFB2_FFB2_FFB2  I0=r1 I1=r2 I2=q I3=rst  -> q
    ugrant  LUT6_2      INIT 0C0C_0C0C_A0A0_A0A0  I0=r1 I1=r2 I2=q I5=1
                                                    O5 = g1,  O6 = g2

evaluated through `ArbBinary.stF / gr1 / gr2` (= `lutB / o5B / o6B` on the
INIT); `stF_eq`, `gr1_eq`, `gr2_eq` (7a) prove them `C(r1,~r2)`, `r1.q`,
`r2.~q`. The q feedback is a read map like any other pin.

## Named hypotheses (fields of `Cell`)

* **H_PIN_READ** (`p1 p2 pq u1 x2 v5 x1 u2 v6 : Rd`): ustate's pins r1, r2, q
  (the FEEDBACK) and ugrant's pins (r1 -> O5, r2 -> O5, q -> O5, r1 -> O6,
  r2 -> O6, q -> O6) each read their driver at `σ t ∈ [t - hi, t - lo]`
  (wire + site pin + that pin's arc to that output). `x1`, `x2` (the pins the
  INIT ignores) are unconstrained. The read maps live in a box `Box`
  (`H_BOX`: `p1 ∈ [a1,A1]`, ..., `v6 ∈ [c6,C6]`).
* **H_ST**: for `t ≥ 0` (rst released at 0) `q t = stF (r1 ∘ p1) (r2 ∘ p2)
  (q ∘ pq)`; **H_PRE**: `q t = q0` for `t < 0`.
* **H_O5 / H_O6**: the two grants from the one fractured LUT.
* Box sanity `Box.Ok` (lo ≤ hi, lo ≥ 0, feedback `l ≥ 1`), and for necessity
  only: **H_LOOP2** `2 ≤ L`, **H_LOOP_WIN** `l < L` (the feedback window has
  two instants), **H_QWIN** `c5 < C6 ∧ c6 ≤ C5 + 1` (the q -> O5 and q -> O6
  windows overlap to within 1 ps; used only by the same-sense oscillation
  witness).

Times are Int ps. Requests are single steps (`up e`, `dn e`).

## Results (see formal/notes/B-arb-pin.md for the comparison table)

* `ov_iff`: grants overlap at `t` iff both requests read 1 and q reads 1 at
  O5 and 0 at O6 (by the INIT). `same_read_excl`: if O5 and O6 shared ONE q
  read map, exclusion would hold for every behaviour (tier 1); with two maps
  it is timing.
* `trans_split`: if q is 0 before `X0` and 1 from `X1`, any overlap is of RISE
  type (`RiseAt`: O5 sees the new q, O6 the old) or of FALL type (`FallAt`: a
  q runt, O5 sees its 1, O6 the 0 after it).
* Same sense, both rise (`su_*`, q0 = 0): `su_box_iff` (exact, per pin) and
  `su_transport_iff` (exact, transport cells of the same box): exclusion for
  every behaviour iff QUIET (`e2 + A2 ≤ e1 + a1`) or COMMIT
  (`e1 + A1 + L ≤ e2 + a2`) with no late overlap (`SuOv` / `SuOvT`). In
  between, `su_osc`: q oscillates for ever and the grants overlap after every
  time bound. `su_same`: under `c5 < C6` the per-pin and transport windows
  coincide.
* Opposite sense, r1 rises / r2 falls (`o1_*`, q0 = 0): every behaviour settles
  by `X1` (`o1_after`); `o1_box_iff`: exclusion iff `¬ O1Ov` (rise OR fall
  type); `o1_transport_iff`: transport iff `¬ O1OvT` (rise type only).
  `o1_same`: equal when `c5 < C6`; `o1_differs`: a concrete box where
  transport proves exclusion and the non-monotone model has an overlap.
* Handover, r2 waiting, holder r1 falls (`h12_*`, q0 = 1): `h12_box_iff`
  (per pin: `¬ H12Ov`, clean-fall OR dip-runt type), `h12_transport_iff`
  (transport: `¬ H12OvT`, closed form `h12OvT_closed`: exclusion iff
  `C5 ≤ c6 ∨ B1 ≤ a1 + c6`), `h12_same` (equal when `c6 < C5`),
  `h12_differs` (q -> O5 faster than q -> O6, as with q on A5: transport
  exclusive, a per-pin behaviour overlaps).
* `su_overlap_forever` (+ `_instance` in `boxS`): with q -> O5/O6 windows at
  least one loop wide, a per-pin behaviour keeps BOTH grants high at every
  instant from some time on: the transport cap `ArbOverlapRace.grant_cap`
  (|b5 - b6|) does not hold in this model.
* Downstream (`reader_*`): a reader through its own windows is again a cell
  (`Cell.reader`), so every sufficient condition applies with composed
  windows; `reader_handover_iff` (exact): a clean exclusive handover with gap
  `h' - h` is seen as overlap iff `h' - h < Y2 - y1`; `reader_mono_step` /
  `reader_glitch`: a FIFO reader sees one edge, a non-monotone one can see a
  runt from a clean edge.

NOT covered: the `bd_arbiter` A0 hold (ArbHeldTimed*, ArbA0Fork); both-fall,
same-sense with q0 = 1, r1 falls / r2 rises, and the r2-holder handover
(mirrors, not proved); same-sense oscillation regime without H_QWIN (open:
number-theoretic in fixed-delay boxes); request waveforms other than single
steps; Kleene/X values (ArbKleene);
analog resolution (ArbInvolution, context only); inertial filtering
(none here: a non-monotone pin can always reproduce any sample of its window).
-/

namespace Formal.Cells.ArbPin
open Formal.Cells
open Formal.Cells.ArbBinary (stF gr1 gr2 stF_eq gr1_eq gr2_eq)
open Formal.Cells.LibGapSteer (Rd)

/-! ## 0. Signals, box, cell -/

/-- A request that rises at `e`. -/
def up (e t : Int) : Bool := decide (e ≤ t)
/-- A request that falls at `e`. -/
def dn (e t : Int) : Bool := decide (t < e)

theorem up_t {e t : Int} : up e t = true ↔ e ≤ t := by simp [up]
theorem up_f {e t : Int} : up e t = false ↔ t < e := by simp [up]
theorem dn_t {e t : Int} : dn e t = true ↔ t < e := by simp [dn]
theorem dn_f {e t : Int} : dn e t = false ↔ e ≤ t := by simp [dn]

/-- The delay box (Int ps): ustate pins r1 `[a1,A1]`, r2 `[a2,A2]`, feedback
`[l,L]`; ugrant r1 -> O5 `[b1,B1]`, r2 -> O6 `[b2,B2]`, q -> O5 `[c5,C5]`,
q -> O6 `[c6,C6]`. -/
structure Box where
  a1 : Int
  A1 : Int
  a2 : Int
  A2 : Int
  l : Int
  L : Int
  b1 : Int
  B1 : Int
  b2 : Int
  B2 : Int
  c5 : Int
  C5 : Int
  c6 : Int
  C6 : Int

/-- Box sanity. -/
def Box.Ok (B : Box) : Prop :=
  0 ≤ B.a1 ∧ B.a1 ≤ B.A1 ∧ 0 ≤ B.a2 ∧ B.a2 ≤ B.A2 ∧ 1 ≤ B.l ∧ B.l ≤ B.L ∧
  0 ≤ B.b1 ∧ B.b1 ≤ B.B1 ∧ 0 ≤ B.b2 ∧ B.b2 ≤ B.B2 ∧
  0 ≤ B.c5 ∧ B.c5 ≤ B.C5 ∧ 0 ≤ B.c6 ∧ B.c6 ≤ B.C6

/-- A read map inside `[lo, hi]`. -/
def In (p : Rd) (lo hi : Int) : Prop := lo ≤ p.lo ∧ p.hi ≤ hi

/-- One behaviour of `bd_arbcell` in the box (every field a named hypothesis). -/
structure Cell (B : Box) (q0 : Bool) (r1 r2 : Int → Bool) where
  p1 : Rd
  p2 : Rd
  pq : Rd
  u1 : Rd
  x2 : Rd
  v5 : Rd
  x1 : Rd
  u2 : Rd
  v6 : Rd
  q : Int → Bool
  g1 : Int → Bool
  g2 : Int → Bool
  H_P1 : In p1 B.a1 B.A1
  H_P2 : In p2 B.a2 B.A2
  H_PQ : In pq B.l B.L
  H_U1 : In u1 B.b1 B.B1
  H_U2 : In u2 B.b2 B.B2
  H_V5 : In v5 B.c5 B.C5
  H_V6 : In v6 B.c6 B.C6
  H_PRE : ∀ t, t < 0 → q t = q0
  H_ST : ∀ t, 0 ≤ t → q t = stF (r1 (p1.σ t)) (r2 (p2.σ t)) (q (pq.σ t))
  H_O5 : ∀ t, g1 t = gr1 (r1 (u1.σ t)) (r2 (x2.σ t)) (q (v5.σ t))
  H_O6 : ∀ t, g2 t = gr2 (r1 (x1.σ t)) (r2 (u2.σ t)) (q (v6.σ t))

/-- Mutual exclusion of the grants, at every instant. -/
def Excl {B : Box} {q0 : Bool} {r1 r2 : Int → Bool} (c : Cell B q0 r1 r2) : Prop :=
  ∀ t, ¬ (c.g1 t = true ∧ c.g2 t = true)

/-- A transport (fixed-delay) behaviour: every constrained read map has a
one-point window. -/
def Transport {B : Box} {q0 : Bool} {r1 r2 : Int → Bool} (c : Cell B q0 r1 r2) : Prop :=
  c.p1.lo = c.p1.hi ∧ c.p2.lo = c.p2.hi ∧ c.pq.lo = c.pq.hi ∧ c.u1.lo = c.u1.hi ∧
  c.u2.lo = c.u2.hi ∧ c.v5.lo = c.v5.hi ∧ c.v6.lo = c.v6.hi

theorem Rd.lo_le_hi (p : Rd) : p.lo ≤ p.hi := by have := p.ge 0; have := p.le 0; omega

/-- A map with explicit window. -/
def mk (f : Int → Int) (lo hi : Int) (h1 : ∀ t, t - hi ≤ f t) (h2 : ∀ t, f t ≤ t - lo) : Rd :=
  ⟨f, lo, hi, h1, h2⟩

def cst (d : Int) : Rd := LibGapSteer.Rd.const d

theorem cst_σ (d t : Int) : (cst d).σ t = t - d := rfl
theorem cst_lo (d : Int) : (cst d).lo = d := rfl
theorem cst_hi (d : Int) : (cst d).hi = d := rfl

/-- Strong induction on Int time (base: all negative times). -/
theorem int_ind (P : Int → Prop) (hneg : ∀ t, t < 0 → P t)
    (h : ∀ t, 0 ≤ t → (∀ u, u < t → P u) → P t) : ∀ t, P t := by
  have key : ∀ n : Nat, ∀ t : Int, t < n → P t := by
    intro n
    induction n with
    | zero => intro t ht; exact hneg t (by omega)
    | succ n ih =>
      intro t ht
      by_cases h1 : t < n
      · exact ih t h1
      · by_cases h0 : t < 0
        · exact hneg t h0
        · exact h t (by omega) (fun u hu => ih u (by omega))
  intro t
  exact key (t.toNat + 1) t (by omega)

/-! ## 1. General facts (any request waveforms, any read maps) -/

theorem stF_val (r1 r2 q : Bool) : stF r1 r2 q = ((r1 && !r2) || (q && !(!r1 && r2))) := stF_eq r1 r2 q

/-- **Overlap, pointwise exact** (from the INIT). -/
theorem ov_iff {B : Box} {q0 : Bool} {r1 r2 : Int → Bool} (c : Cell B q0 r1 r2) (t : Int) :
    (c.g1 t = true ∧ c.g2 t = true) ↔
    (r1 (c.u1.σ t) = true ∧ r2 (c.u2.σ t) = true ∧ c.q (c.v5.σ t) = true ∧
      c.q (c.v6.σ t) = false) := by
  rw [c.H_O5, c.H_O6, gr1_eq, gr2_eq]
  cases r1 (c.u1.σ t) <;> cases r2 (c.u2.σ t) <;> cases c.q (c.v5.σ t) <;>
    cases c.q (c.v6.σ t) <;> simp

/-- Tier 1, per pin: if O5 and O6 read q through ONE map, no behaviour ever
overlaps, whatever q does (oscillation included). -/
theorem same_read_excl {B : Box} {q0 : Bool} {r1 r2 : Int → Bool} (c : Cell B q0 r1 r2)
    (H_SHARED : ∀ t, c.v5.σ t = c.v6.σ t) : Excl c := by
  intro t h
  have := (ov_iff c t).mp h
  rw [H_SHARED t] at this
  rw [this.2.2.1] at this
  exact Bool.noConfusion this.2.2.2

/-- Rise-type overlap at `t` for a q transition 0 -> 1 confined to `[X0, X1)`:
O5 can show the new 1 while O6 still shows the old 0. -/
def RiseAt (B : Box) (X0 X1 t : Int) : Prop :=
  B.c5 < B.C6 ∧ X0 + B.c5 ≤ t ∧ t ≤ X1 - 1 + B.C6

/-- Fall-type overlap at `t`: a q RUNT inside `[X0, X1)`; O5 shows its 1, O6
the 0 after it. Needs `X1 - X0 ≥ 2`. -/
def FallAt (B : Box) (X0 X1 t : Int) : Prop :=
  B.c6 < B.C5 ∧ X0 + 2 ≤ X1 ∧ X0 + B.c5 ≤ t ∧ X0 + 1 + B.c6 ≤ t ∧
  t ≤ X1 - 1 + B.C6 ∧ t ≤ X1 - 2 + B.C5

/-- Under `c5 < C6` every fall-type instant is also a rise-type instant. -/
theorem fall_rise (B : Box) (X0 X1 t : Int) (h : B.c5 < B.C6) :
    FallAt B X0 X1 t → RiseAt B X0 X1 t := by
  intro ⟨_, _, h3, _, h5, _⟩; exact ⟨h, h3, h5⟩

/-- **Transition split** (any read maps): q 0 before `X0`, 1 from `X1` ⇒ an
instant where O5 reads 1 and O6 reads 0 is of rise or fall type. -/
theorem trans_split {B : Box} {q0 : Bool} {r1 r2 : Int → Bool} (c : Cell B q0 r1 r2)
    (X0 X1 : Int) (h0 : ∀ s, s < X0 → c.q s = false) (h1 : ∀ s, X1 ≤ s → c.q s = true)
    (t : Int) (h5 : c.q (c.v5.σ t) = true) (h6 : c.q (c.v6.σ t) = false) :
    RiseAt B X0 X1 t ∨ FallAt B X0 X1 t := by
  have a1 := c.v5.ge t; have a2 := c.v5.le t; have a3 := c.v6.ge t; have a4 := c.v6.le t
  have b5 := c.H_V5; have b6 := c.H_V6
  unfold In at b5 b6
  have hs5 : X0 ≤ c.v5.σ t := by
    apply Classical.byContradiction; intro hn
    rw [h0 _ (by omega)] at h5; exact Bool.noConfusion h5
  have hs6 : c.v6.σ t < X1 := by
    apply Classical.byContradiction; intro hn
    rw [h1 _ (by omega)] at h6; exact Bool.noConfusion h6
  rcases Int.lt_trichotomy (c.v6.σ t) (c.v5.σ t) with hl | he | hg
  · left; exact ⟨by omega, by omega, by omega⟩
  · rw [he, h5] at h6; exact absurd h6 (by decide)
  · right; exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-! ## 2. Same sense: both requests rise (q0 = 0: side 2 was the last winner) -/

section su
variable {B : Box} {e1 e2 : Int}

/-- Before r1 can be read at ustate, q stays 0 (any read maps). -/
theorem su_before (hB : B.Ok) (c : Cell B false (up e1) (up e2)) :
    ∀ t, t < e1 + B.a1 → c.q t = false := by
  have hP1 := c.H_P1; have hPQ := c.H_PQ; unfold In at hP1 hPQ; unfold Box.Ok at hB
  refine int_ind _ (fun t ht _ => c.H_PRE t ht) ?_
  intro t ht ih hlt
  rw [c.H_ST t ht]
  have g1 := c.p1.le t; have g3 := c.pq.le t
  have hq : c.q (c.pq.σ t) = false := ih _ (by omega) (by omega)
  have hr : up e1 (c.p1.σ t) = false := up_f.mpr (by omega)
  rw [hq, hr, stF_val]; simp

/-- **QUIET**: if r2 is surely seen before r1 can be (`e2 + A2 ≤ e1 + a1`), q
never moves, in every behaviour. -/
theorem su_quiet (hB : B.Ok) (H_QUIET : e2 + B.A2 ≤ e1 + B.a1) (c : Cell B false (up e1) (up e2)) :
    ∀ t, c.q t = false := by
  have hP1 := c.H_P1; have hP2 := c.H_P2; have hPQ := c.H_PQ
  unfold In at hP1 hP2 hPQ; unfold Box.Ok at hB
  refine int_ind _ (fun t ht => c.H_PRE t ht) ?_
  intro t ht ih
  rw [c.H_ST t ht]
  have g1 := c.p1.le t; have g2 := c.p2.ge t; have g3 := c.pq.le t
  have hq : c.q (c.pq.σ t) = false := ih _ (by omega)
  rw [hq, stF_val]
  cases h1 : up e1 (c.p1.σ t)
  · simp
  · have := up_t.mp h1
    have h2 : up e2 (c.p2.σ t) = true := up_t.mpr (by omega)
    rw [h2]; simp

theorem su_quiet_excl (hB : B.Ok) (H_QUIET : e2 + B.A2 ≤ e1 + B.a1)
    (c : Cell B false (up e1) (up e2)) : Excl c := by
  intro t h
  have := ((ov_iff c t).mp h).2.2.1
  rw [su_quiet hB H_QUIET c] at this; exact Bool.noConfusion this

/-- **COMMIT**: if r1 is surely seen at least one loop window before r2 can be
(`e1 + A1 + L ≤ e2 + a2`), q is 1 from `e1 + A1` on, in every behaviour. -/
theorem su_commit (hB : B.Ok) (H_COMMIT : e1 + B.A1 + B.L ≤ e2 + B.a2)
    (he : 0 ≤ e1) (c : Cell B false (up e1) (up e2)) :
    ∀ t, e1 + B.A1 ≤ t → c.q t = true := by
  have hP1 := c.H_P1; have hP2 := c.H_P2; have hPQ := c.H_PQ
  unfold In at hP1 hP2 hPQ; unfold Box.Ok at hB
  refine int_ind _ (fun t ht h => by omega) ?_
  intro t ht ih hT
  rw [c.H_ST t ht]
  have g1 := c.p1.ge t; have g2 := c.p2.le t; have g3 := c.pq.le t; have g4 := c.pq.ge t
  have hr1 : up e1 (c.p1.σ t) = true := up_t.mpr (by omega)
  rw [hr1, stF_val]
  by_cases hlt : t < e2 + B.a2
  · have : up e2 (c.p2.σ t) = false := up_f.mpr (by omega)
    rw [this]; simp
  · have : c.q (c.pq.σ t) = true := ih _ (by omega) (by omega)
    rw [this]; simp

/-- Overlap after commit (per pin): some instant where both grant request
reads can be 1 and the transition `[e1 + a1, e1 + A1)` gives rise or fall type. -/
def SuOv (B : Box) (e1 e2 : Int) : Prop :=
  ∃ t, e1 + B.b1 ≤ t ∧ e2 + B.b2 ≤ t ∧
    (RiseAt B (e1 + B.a1) (e1 + B.A1) t ∨ FallAt B (e1 + B.a1) (e1 + B.A1) t)

/-- The transport version: rise type only. -/
def SuOvT (B : Box) (e1 e2 : Int) : Prop :=
  ∃ t, e1 + B.b1 ≤ t ∧ e2 + B.b2 ≤ t ∧ RiseAt B (e1 + B.a1) (e1 + B.A1) t

theorem su_commit_excl (hB : B.Ok) (H_COMMIT : e1 + B.A1 + B.L ≤ e2 + B.a2) (he : 0 ≤ e1)
    (hno : ¬ SuOv B e1 e2) (c : Cell B false (up e1) (up e2)) : Excl c := by
  intro t h
  obtain ⟨h1, h2, h5, h6⟩ := (ov_iff c t).mp h
  have hU1 := c.H_U1; have hU2 := c.H_U2; unfold In at hU1 hU2
  have := up_t.mp h1; have := up_t.mp h2
  have := c.u1.le t; have := c.u2.le t
  exact hno ⟨t, by omega, by omega,
    trans_split c _ _ (su_before hB c) (su_commit hB H_COMMIT he c) t h5 h6⟩

end su

/-! ### Emod helpers for the oscillating witness -/

theorem emod_shift (a L : Int) : (a - L) % L = a % L := by
  have := Int.add_mul_emod_self_left (a - L) L 1
  rw [Int.mul_one] at this
  have e : a - L + L = a := by omega
  rw [e] at this; exact this.symm

theorem emod_small (a L : Int) (h0 : 0 ≤ a) (h1 : a < L) : a % L = a := Int.emod_eq_of_lt h0 h1

theorem emod_kL (k L : Int) : (k * L) % L = 0 := Int.mul_emod_left k L

theorem emod_kL_pred (k L : Int) (hL : 1 ≤ L) : (k * L - 1) % L = L - 1 := by
  have e : k * L - 1 = (L - 1) + L * (k - 1) := by
    rw [Int.mul_sub, Int.mul_one, Int.mul_comm]; omega
  rw [e, Int.add_mul_emod_self_left]; exact Int.emod_eq_of_lt (by omega) (by omega)

theorem le_kL (k L : Int) (hk : 0 ≤ k) (hL : 1 ≤ L) : k ≤ k * L := by
  have : 0 ≤ k * (L - 1) := Int.mul_nonneg hk (by omega)
  have e : k * L = k + k * (L - 1) := by rw [Int.mul_sub, Int.mul_one]; omega
  omega

/-! ## 3. Building behaviours (witness constructor) -/

/-- A behaviour from explicit read maps and an explicit q trace; the grants
are DEFINED by the INIT (so H_O5/H_O6 hold by `rfl`). The ignored pins read
through `cst 0`. -/
def mkCell (B : Box) (q0 : Bool) (r1 r2 : Int → Bool) (p1 p2 pq u1 v5 u2 v6 : Rd)
    (q : Int → Bool) (h1 : In p1 B.a1 B.A1) (h2 : In p2 B.a2 B.A2) (h3 : In pq B.l B.L)
    (h4 : In u1 B.b1 B.B1) (h5 : In u2 B.b2 B.B2) (h6 : In v5 B.c5 B.C5)
    (h7 : In v6 B.c6 B.C6) (hpre : ∀ t, t < 0 → q t = q0)
    (hst : ∀ t, 0 ≤ t → q t = stF (r1 (p1.σ t)) (r2 (p2.σ t)) (q (pq.σ t))) :
    Cell B q0 r1 r2 :=
  { p1 := p1, p2 := p2, pq := pq, u1 := u1, x2 := cst 0, v5 := v5, x1 := cst 0, u2 := u2,
    v6 := v6, q := q,
    g1 := fun t => gr1 (r1 (u1.σ t)) (r2 ((cst 0).σ t)) (q (v5.σ t)),
    g2 := fun t => gr2 (r1 ((cst 0).σ t)) (r2 (u2.σ t)) (q (v6.σ t)),
    H_P1 := h1, H_P2 := h2, H_PQ := h3, H_U1 := h4, H_U2 := h5, H_V5 := h6, H_V6 := h7,
    H_PRE := hpre, H_ST := hst, H_O5 := fun _ => rfl, H_O6 := fun _ => rfl }

theorem in_cst {d lo hi : Int} (h1 : lo ≤ d) (h2 : d ≤ hi) : In (cst d) lo hi := ⟨h1, h2⟩

/-- The constructed cell overlaps at `t` as soon as the four reads say so. -/
theorem mk_overlap {B : Box} {q0 : Bool} {r1 r2 : Int → Bool} {p1 p2 pq u1 v5 u2 v6 : Rd}
    {q : Int → Bool} {h1 h2 h3 h4 h5 h6 h7 hpre hst} (t : Int)
    (a : r1 (u1.σ t) = true) (b : r2 (u2.σ t) = true) (c5 : q (v5.σ t) = true)
    (c6 : q (v6.σ t) = false) :
    ¬ Excl (mkCell B q0 r1 r2 p1 p2 pq u1 v5 u2 v6 q h1 h2 h3 h4 h5 h6 h7 hpre hst) :=
  fun h => h t ((ov_iff _ t).mpr ⟨a, b, c5, c6⟩)

/-- The loop map that skips one instant `s` (needs `l < L`): reads `t - L`,
except `t - L + 1` when `t - L = s`. -/
def skipMap (s l L : Int) (hl : l < L) : Rd :=
  mk (fun t => if t - L = s then t - L + 1 else t - L) l L
    (fun t => by show t - L ≤ (if t - L = s then t - L + 1 else t - L); split <;> omega)
    (fun t => by show (if t - L = s then t - L + 1 else t - L) ≤ t - l; split <;> omega)

theorem skipMap_ne (s l L : Int) (hl : l < L) (t : Int) : (skipMap s l L hl).σ t ≠ s := by
  show (if t - L = s then t - L + 1 else t - L) ≠ s
  split <;> omega

theorem skipMap_ge (s l L : Int) (hl : l < L) (t : Int) : t - L ≤ (skipMap s l L hl).σ t := by
  show t - L ≤ (if t - L = s then t - L + 1 else t - L)
  split <;> omega

theorem skipMap_lt (s l L : Int) (hl : l < L) (hl1 : 1 ≤ l) (t : Int) : (skipMap s l L hl).σ t < t := by
  show (if t - L = s then t - L + 1 else t - L) < t
  split <;> omega

/-- A pin that reads early (`a`) at the single instant `s`, late (`A`)
elsewhere: the NON-monotone read (a sample out of order). -/
def jumpMap (s a A : Int) (h : a ≤ A) : Rd :=
  mk (fun t => if t = s then t - a else t - A) a A
    (fun t => by show t - A ≤ (if t = s then t - a else t - A); split <;> omega)
    (fun t => by show (if t = s then t - a else t - A) ≤ t - a; split <;> omega)

theorem jumpMap_s (s a A : Int) (h : a ≤ A) : (jumpMap s a A h).σ s = s - a := by
  show (if s = s then s - a else s - A) = s - a
  simp

theorem jumpMap_ne (s a A : Int) (h : a ≤ A) (t : Int) (ht : t ≠ s) :
    (jumpMap s a A h).σ t = t - A := by
  show (if t = s then t - a else t - A) = t - A
  simp [ht]

/-- The runt trace: 1 at the single instant `s`, then 1 from `X1` on. -/
def qR (s X1 t : Int) : Bool := decide (t = s ∨ X1 ≤ t)

/-! ## 4. Same sense: witnesses and the exact windows -/

/-- The oscillating trace: from `x`, a 1-runt of width `w` every `L`. -/
def qOsc (x w L t : Int) : Bool := decide (x ≤ t ∧ (t - x) % L < w)

theorem qOsc_st (e1 e2 d1 d2 L w : Int) (hw1 : 1 ≤ w) (hwL : w < L)
    (hw : e2 + d2 = e1 + d1 + w) (t : Int) :
    qOsc (e1 + d1) w L t =
      stF (up e1 (t - d1)) (up e2 (t - d2)) (qOsc (e1 + d1) w L (t - L)) := by
  rw [stF_val]
  by_cases h1 : t < e1 + d1
  · have a : qOsc (e1 + d1) w L t = false := by simp only [qOsc]; simp; omega
    have b : qOsc (e1 + d1) w L (t - L) = false := by simp only [qOsc]; simp; omega
    rw [a, b, up_f.mpr (show t - d1 < e1 by omega), up_f.mpr (show t - d2 < e2 by omega)]; rfl
  · by_cases h2 : t < e2 + d2
    · have a : qOsc (e1 + d1) w L t = true := by
        simp only [qOsc, decide_eq_true_eq]
        rw [emod_small _ _ (by omega) (by omega)]; omega
      rw [a, up_t.mpr (show e1 ≤ t - d1 by omega), up_f.mpr (show t - d2 < e2 by omega)]; rfl
    · rw [up_t.mpr (show e1 ≤ t - d1 by omega), up_t.mpr (show e2 ≤ t - d2 by omega)]
      simp only [Bool.not_true, Bool.and_false, Bool.not_false, Bool.false_or, Bool.and_true]
      by_cases h3 : t - L < e1 + d1
      · have a : qOsc (e1 + d1) w L t = false := by
          simp only [qOsc]; simp
          intro _; rw [emod_small _ _ (by omega) (by omega)]; omega
        have b : qOsc (e1 + d1) w L (t - L) = false := by simp only [qOsc]; simp; omega
        rw [a, b]
      · simp only [qOsc]
        have e : t - L - (e1 + d1) = (t - (e1 + d1)) - L := by omega
        rw [e, emod_shift]
        simp only [decide_eq_decide]; omega

section su2
variable {B : Box} {e1 e2 : Int}

/-- **Same sense, between QUIET and COMMIT: eternal oscillation and overlap.**
For every request gap strictly between the two thresholds there is a TRANSPORT
behaviour in the box in which q takes both values after every time bound and
both grants are high together after every time bound. -/
theorem su_osc (hB : B.Ok) (H_LOOP2 : 2 ≤ B.L) (H_QWIN : B.c5 < B.C6 ∧ B.c6 ≤ B.C5 + 1)
    (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (hnq : e1 + B.a1 < e2 + B.A2) (hnc : e2 + B.a2 < e1 + B.A1 + B.L) :
    ∃ c : Cell B false (up e1) (up e2), Transport c ∧
      (∀ T, ∃ t, T ≤ t ∧ c.g1 t = true ∧ c.g2 t = true) ∧
      (∀ T, ∃ t1 t2, T ≤ t1 ∧ T ≤ t2 ∧ c.q t1 = true ∧ c.q t2 = false) := by
  unfold Box.Ok at hB
  obtain ⟨w, hw⟩ : ∃ w, w = max 1 (e2 - e1 + B.a2 - B.A1) := ⟨_, rfl⟩
  obtain ⟨d2, hd2⟩ : ∃ d, d = max B.a2 (w - (e2 - e1) + B.a1) := ⟨_, rfl⟩
  obtain ⟨d1, hd1⟩ : ∃ d, d = d2 - (w - (e2 - e1)) := ⟨_, rfl⟩
  obtain ⟨d5, hd5⟩ : ∃ d, d = max B.c5 (B.c6 - 1) := ⟨_, rfl⟩
  have hw1 : 1 ≤ w := by omega
  have hwL : w < B.L := by omega
  have hwe : e2 + d2 = e1 + d1 + w := by omega
  let c := mkCell B false (up e1) (up e2) (cst d1) (cst d2) (cst B.L) (cst B.b1) (cst d5)
    (cst B.b2) (cst (d5 + 1)) (qOsc (e1 + d1) w B.L)
    (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega))
    (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega))
    (in_cst (by omega) (by omega))
    (fun t ht => by simp only [qOsc]; simp; omega)
    (fun t _ => qOsc_st e1 e2 d1 d2 B.L w hw1 hwL hwe t)
  -- the late instants x + K and x + K - 1, K a positive multiple of L
  have late : ∀ M : Int, ∃ K, M ≤ K ∧ 1 ≤ K ∧ K % B.L = 0 ∧ (K - 1) % B.L = B.L - 1 := by
    intro M
    refine ⟨((M.toNat : Int) + 1) * B.L, ?_, ?_, emod_kL _ _, emod_kL_pred _ _ (by omega)⟩
    · have := le_kL ((M.toNat : Int) + 1) B.L (by omega) (by omega); omega
    · have := le_kL ((M.toNat : Int) + 1) B.L (by omega) (by omega); omega
  have qt : ∀ K, 1 ≤ K → K % B.L = 0 → qOsc (e1 + d1) w B.L (e1 + d1 + K) = true := by
    intro K _ hK; simp only [qOsc, decide_eq_true_eq]
    rw [show e1 + d1 + K - (e1 + d1) = K by omega, hK]; omega
  have qf : ∀ K, 1 ≤ K → (K - 1) % B.L = B.L - 1 →
      qOsc (e1 + d1) w B.L (e1 + d1 + K - 1) = false := by
    intro K _ hK; simp only [qOsc]; simp
    intro _; rw [show e1 + d1 + K - 1 - (e1 + d1) = K - 1 by omega, hK]; omega
  refine ⟨c, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_, ?_⟩
  · intro T
    obtain ⟨K, hK1, hK2, hK3, hK4⟩ := late (max T 0 + B.b1 + B.b2 + e2 + w)
    refine ⟨e1 + d1 + K + d5, by omega, ?_⟩
    have := (ov_iff c (e1 + d1 + K + d5)).mpr
    apply this
    refine ⟨up_t.mpr ?_, up_t.mpr ?_, ?_, ?_⟩
    · show e1 ≤ e1 + d1 + K + d5 - B.b1; omega
    · show e2 ≤ e1 + d1 + K + d5 - B.b2; omega
    · show qOsc (e1 + d1) w B.L (e1 + d1 + K + d5 - d5) = true
      rw [show e1 + d1 + K + d5 - d5 = e1 + d1 + K by omega]; exact qt K hK2 hK3
    · show qOsc (e1 + d1) w B.L (e1 + d1 + K + d5 - (d5 + 1)) = false
      rw [show e1 + d1 + K + d5 - (d5 + 1) = e1 + d1 + K - 1 by omega]; exact qf K hK2 hK4
  · intro T
    obtain ⟨K, hK1, hK2, hK3, hK4⟩ := late (max T 0 + 1)
    exact ⟨e1 + d1 + K, e1 + d1 + K - 1, by omega, by omega, qt K hK2 hK3, qf K hK2 hK4⟩

/-- **Commit-regime counter-trace (transport)**: a rise-type instant with both
grant reads possibly high is a real overlap. -/
theorem su_rise_cex (hB : B.Ok) (he1 : 0 ≤ e1) (H_COMMIT : e1 + B.A1 + B.L ≤ e2 + B.a2)
    (hov : SuOvT B e1 e2) :
    ∃ c : Cell B false (up e1) (up e2), Transport c ∧ ¬ Excl c := by
  unfold Box.Ok at hB
  obtain ⟨t, ht1, ht2, hr1, hr2, hr3⟩ := hov
  obtain ⟨x, hx⟩ : ∃ x, x = max (e1 + B.a1) (t - B.C6 + 1) := ⟨_, rfl⟩
  have hst : ∀ s, 0 ≤ s → up x s = stF (up e1 (s - (x - e1))) (up e2 (s - B.a2)) (up x (s - B.L)) := by
    intro s _
    rw [stF_val]
    by_cases h : s < x
    · rw [up_f.mpr h, up_f.mpr (show s - (x - e1) < e1 by omega),
        up_f.mpr (show s - B.a2 < e2 by omega), up_f.mpr (show s - B.L < x by omega)]; rfl
    · rw [up_t.mpr (show x ≤ s by omega), up_t.mpr (show e1 ≤ s - (x - e1) by omega)]
      by_cases h2 : s < e2 + B.a2
      · rw [up_f.mpr (show s - B.a2 < e2 by omega)]; rfl
      · rw [up_t.mpr (show e2 ≤ s - B.a2 by omega), up_t.mpr (show x ≤ s - B.L by omega)]; rfl
  refine ⟨mkCell B false (up e1) (up e2) (cst (x - e1)) (cst B.a2) (cst B.L) (cst B.b1)
    (cst B.c5) (cst B.b2) (cst B.C6) (up x)
    (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega))
    (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega))
    (in_cst (by omega) (by omega)) (fun s hs => up_f.mpr (by omega)) hst,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  exact mk_overlap t (up_t.mpr (show e1 ≤ t - B.b1 by omega)) (up_t.mpr (show e2 ≤ t - B.b2 by omega))
    (up_t.mpr (show x ≤ t - B.c5 by omega)) (up_f.mpr (show t - B.C6 < x by omega))

end su2

/-! ## 5. Transport cells as degenerate boxes -/

/-- The box made of a behaviour's own windows. -/
def tightBox {B : Box} {q0 : Bool} {r1 r2 : Int → Bool} (c : Cell B q0 r1 r2) : Box :=
  ⟨c.p1.lo, c.p1.hi, c.p2.lo, c.p2.hi, c.pq.lo, c.pq.hi, c.u1.lo, c.u1.hi, c.u2.lo, c.u2.hi,
   c.v5.lo, c.v5.hi, c.v6.lo, c.v6.hi⟩

/-- Every behaviour is a behaviour of its own tight box (same traces). -/
def Cell.tight {B : Box} {q0 : Bool} {r1 r2 : Int → Bool} (c : Cell B q0 r1 r2) :
    Cell (tightBox c) q0 r1 r2 :=
  { c with
    H_P1 := ⟨Int.le_refl _, Int.le_refl _⟩, H_P2 := ⟨Int.le_refl _, Int.le_refl _⟩,
    H_PQ := ⟨Int.le_refl _, Int.le_refl _⟩, H_U1 := ⟨Int.le_refl _, Int.le_refl _⟩,
    H_U2 := ⟨Int.le_refl _, Int.le_refl _⟩, H_V5 := ⟨Int.le_refl _, Int.le_refl _⟩,
    H_V6 := ⟨Int.le_refl _, Int.le_refl _⟩ }

theorem tight_ok {B : Box} {q0 : Bool} {r1 r2 : Int → Bool} (hB : B.Ok) (c : Cell B q0 r1 r2) :
    (tightBox c).Ok := by
  have := c.H_P1; have := c.H_P2; have := c.H_PQ; have := c.H_U1; have := c.H_U2
  have := c.H_V5; have := c.H_V6
  have := Rd.lo_le_hi c.p1; have := Rd.lo_le_hi c.p2; have := Rd.lo_le_hi c.pq
  have := Rd.lo_le_hi c.u1; have := Rd.lo_le_hi c.u2; have := Rd.lo_le_hi c.v5
  have := Rd.lo_le_hi c.v6
  unfold In at *; unfold Box.Ok at *
  simp only [tightBox]; omega

/-! ## 6. Same sense: the exact windows -/

section su3
variable {B : Box} {e1 e2 : Int}

theorem su_transport_excl (hB : B.Ok) (H_COMMIT : e1 + B.A1 + B.L ≤ e2 + B.a2) (he : 0 ≤ e1)
    (hno : ¬ SuOvT B e1 e2) (c : Cell B false (up e1) (up e2)) (hT : Transport c) : Excl c := by
  have h1 := c.H_P1; have h2 := c.H_P2; have h3 := c.H_PQ; have h4 := c.H_U1
  have h5 := c.H_U2; have h6 := c.H_V5; have h7 := c.H_V6
  unfold In at h1 h2 h3 h4 h5 h6 h7; unfold Transport at hT
  have hc : e1 + (tightBox c).A1 + (tightBox c).L ≤ e2 + (tightBox c).a2 := by
    simp only [tightBox]; omega
  refine su_commit_excl (tight_ok hB c) hc he ?_ c.tight
  rintro ⟨t, ht1, ht2, hr | hf⟩
  · apply hno; refine ⟨t, ?_, ?_, ?_⟩
    · simp only [tightBox] at ht1; omega
    · simp only [tightBox] at ht2; omega
    · obtain ⟨a, b, d⟩ := hr; simp only [tightBox] at a b d; exact ⟨by omega, by omega, by omega⟩
  · obtain ⟨_, b, _⟩ := hf; simp only [tightBox] at b; omega

/-- Closed form of the commit-regime overlap condition. -/
theorem suOvT_closed (hB : B.Ok) :
    SuOvT B e1 e2 ↔ (B.c5 < B.C6 ∧ max (e1 + B.b1) (e2 + B.b2) ≤ e1 + B.A1 - 1 + B.C6) := by
  unfold Box.Ok at hB
  constructor
  · rintro ⟨t, h1, h2, a, b, d⟩; exact ⟨a, by omega⟩
  · rintro ⟨a, b⟩
    exact ⟨max (max (e1 + B.b1) (e2 + B.b2)) (e1 + B.a1 + B.c5), by omega, by omega,
      a, by omega, by omega⟩

/-- Under `c5 < C6` the per-pin and transport commit conditions coincide. -/
theorem su_same (h : B.c5 < B.C6) : SuOv B e1 e2 ↔ SuOvT B e1 e2 := by
  constructor
  · rintro ⟨t, a, b, r | f⟩
    · exact ⟨t, a, b, r⟩
    · exact ⟨t, a, b, fall_rise B _ _ t h f⟩
  · rintro ⟨t, a, b, r⟩; exact ⟨t, a, b, Or.inl r⟩

/-- **Same sense, exact over the box, TRANSPORT behaviours.** -/
theorem su_transport_iff (hB : B.Ok) (H_LOOP2 : 2 ≤ B.L)
    (H_QWIN : B.c5 < B.C6 ∧ B.c6 ≤ B.C5 + 1) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) :
    (∀ c : Cell B false (up e1) (up e2), Transport c → Excl c) ↔
    (e2 + B.A2 ≤ e1 + B.a1 ∨ (e1 + B.A1 + B.L ≤ e2 + B.a2 ∧ ¬ SuOvT B e1 e2)) := by
  constructor
  · intro h
    by_cases hq : e2 + B.A2 ≤ e1 + B.a1
    · exact Or.inl hq
    · right
      by_cases hc : e1 + B.A1 + B.L ≤ e2 + B.a2
      · refine ⟨hc, fun hov => ?_⟩
        obtain ⟨c, hT, hn⟩ := su_rise_cex hB he1 hc hov
        exact hn (h c hT)
      · exfalso
        obtain ⟨c, hT, hov, _⟩ := su_osc hB H_LOOP2 H_QWIN he1 he2 (by omega) (by omega)
        obtain ⟨t, _, h1, h2⟩ := hov 0
        exact h c hT t ⟨h1, h2⟩
  · rintro (hq | ⟨hc, hno⟩) c hT
    · exact su_quiet_excl hB hq c
    · exact su_transport_excl hB hc he1 hno c hT

/-- **Same sense, exact over the box, EVERY per-pin behaviour** (non-monotone
reads included): the same window as transport. -/
theorem su_box_iff (hB : B.Ok) (H_LOOP2 : 2 ≤ B.L)
    (H_QWIN : B.c5 < B.C6 ∧ B.c6 ≤ B.C5 + 1) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) :
    (∀ c : Cell B false (up e1) (up e2), Excl c) ↔
    (e2 + B.A2 ≤ e1 + B.a1 ∨ (e1 + B.A1 + B.L ≤ e2 + B.a2 ∧ ¬ SuOvT B e1 e2)) := by
  constructor
  · intro h
    exact (su_transport_iff hB H_LOOP2 H_QWIN he1 he2).mp (fun c _ => h c)
  · rintro (hq | ⟨hc, hno⟩) c
    · exact su_quiet_excl hB hq c
    · exact su_commit_excl hB hc he1 (fun h => hno ((su_same H_QWIN.1).mp h)) c

end su3

/-! ## 7. Opposite sense: r1 rises at `e1`, r2 falls at `e2` (q0 = 0) -/

section o1
variable {B : Box} {e1 e2 : Int}

/-- First instant the set `r1.~r2` can be read at ustate. -/
def X0 (B : Box) (e1 e2 : Int) : Int := max (e1 + B.a1) (e2 + B.a2)
/-- First instant from which the set is FORCED. -/
def X1 (B : Box) (e1 e2 : Int) : Int := max (e1 + B.A1) (e2 + B.A2)

theorem o1_before (hB : B.Ok) (c : Cell B false (up e1) (dn e2)) :
    ∀ t, t < X0 B e1 e2 → c.q t = false := by
  have hP1 := c.H_P1; have hP2 := c.H_P2; have hPQ := c.H_PQ
  unfold In at hP1 hP2 hPQ; unfold Box.Ok at hB
  refine int_ind _ (fun t ht _ => c.H_PRE t ht) ?_
  intro t ht ih hlt
  unfold X0 at hlt ih
  rw [c.H_ST t ht]
  have g1 := c.p1.le t; have g2 := c.p2.le t; have g3 := c.pq.le t
  have hq : c.q (c.pq.σ t) = false := ih _ (by omega) (by omega)
  rw [hq, stF_val]
  cases h1 : up e1 (c.p1.σ t)
  · simp
  · have := up_t.mp h1
    have h2 : dn e2 (c.p2.σ t) = true := dn_t.mpr (by omega)
    rw [h2]; simp

/-- **Opposite sense resolves in bounded time, in EVERY behaviour**: q = 1
from `X1` on (no induction: the set is forced). -/
theorem o1_after (hB : B.Ok) (he1 : 0 ≤ e1) (c : Cell B false (up e1) (dn e2)) :
    ∀ t, X1 B e1 e2 ≤ t → c.q t = true := by
  have hP1 := c.H_P1; have hP2 := c.H_P2
  unfold In at hP1 hP2; unfold Box.Ok at hB
  intro t ht; unfold X1 at ht
  rw [c.H_ST t (by omega)]
  have g1 := c.p1.ge t; have g2 := c.p2.ge t
  rw [up_t.mpr (show e1 ≤ c.p1.σ t by omega), dn_f.mpr (show e2 ≤ c.p2.σ t by omega), stF_val]
  simp

/-- Per-pin overlap condition (rise OR fall type). -/
def O1Ov (B : Box) (e1 e2 : Int) : Prop :=
  ∃ t, e1 + B.b1 ≤ t ∧ t < e2 + B.B2 ∧
    (RiseAt B (X0 B e1 e2) (X1 B e1 e2) t ∨ FallAt B (X0 B e1 e2) (X1 B e1 e2) t)

/-- Transport overlap condition (rise type only). -/
def O1OvT (B : Box) (e1 e2 : Int) : Prop :=
  ∃ t, e1 + B.b1 ≤ t ∧ t < e2 + B.B2 ∧ RiseAt B (X0 B e1 e2) (X1 B e1 e2) t

/-- **Sufficient, every per-pin behaviour.** -/
theorem o1_excl (hB : B.Ok) (he1 : 0 ≤ e1) (hno : ¬ O1Ov B e1 e2)
    (c : Cell B false (up e1) (dn e2)) : Excl c := by
  intro t h
  obtain ⟨h1, h2, h5, h6⟩ := (ov_iff c t).mp h
  have hU1 := c.H_U1; have hU2 := c.H_U2; unfold In at hU1 hU2
  have := up_t.mp h1; have := dn_t.mp h2
  have := c.u1.le t; have := c.u2.ge t
  exact hno ⟨t, by omega, by omega,
    trans_split c _ _ (o1_before hB c) (o1_after hB he1 c) t h5 h6⟩

/-- **Sufficient, transport behaviours** (rise type only). -/
theorem o1_transport_excl (hB : B.Ok) (he1 : 0 ≤ e1) (hno : ¬ O1OvT B e1 e2)
    (c : Cell B false (up e1) (dn e2)) (hT : Transport c) : Excl c := by
  have h1 := c.H_P1; have h2 := c.H_P2; have h3 := c.H_PQ; have h4 := c.H_U1
  have h5 := c.H_U2; have h6 := c.H_V5; have h7 := c.H_V6
  unfold In at h1 h2 h3 h4 h5 h6 h7; unfold Transport at hT
  refine o1_excl (tight_ok hB c) he1 ?_ c.tight
  rintro ⟨t, ht1, ht2, hr | hf⟩
  · apply hno; refine ⟨t, ?_, ?_, ?_⟩
    · simp only [tightBox] at ht1; omega
    · simp only [tightBox] at ht2; omega
    · obtain ⟨a, b, d⟩ := hr; simp only [X0, X1, tightBox] at a b d ⊢
      exact ⟨by omega, by omega, by omega⟩
  · obtain ⟨_, b, _⟩ := hf; unfold X0 X1 at b; simp only [tightBox] at b; omega

/-- **Rise-type counter-trace (transport).** -/
theorem o1_rise_cex (hB : B.Ok) (he2 : 0 ≤ e2) (hov : O1OvT B e1 e2) :
    ∃ c : Cell B false (up e1) (dn e2), Transport c ∧ ¬ Excl c := by
  unfold Box.Ok at hB
  obtain ⟨t, ht1, ht2, hr1, hr2, hr3⟩ := hov
  simp only [X0, X1] at hr2 hr3
  obtain ⟨x, hx⟩ : ∃ x, x = max (max (e1 + B.a1) (e2 + B.a2)) (t - B.C6 + 1) := ⟨_, rfl⟩
  obtain ⟨d1, hd1⟩ : ∃ d, d = max B.a1 (min B.A1 (x - e1)) := ⟨_, rfl⟩
  obtain ⟨d2, hd2⟩ : ∃ d, d = max B.a2 (min B.A2 (x - e2)) := ⟨_, rfl⟩
  have hxm : max (e1 + d1) (e2 + d2) = x := by omega
  have hst : ∀ s, 0 ≤ s → up x s = stF (up e1 (s - d1)) (dn e2 (s - d2)) (up x (s - B.L)) := by
    intro s _
    rw [stF_val]
    by_cases h : s < x
    · rw [up_f.mpr h, up_f.mpr (show s - B.L < x by omega)]
      by_cases h' : s < e1 + d1
      · rw [up_f.mpr (show s - d1 < e1 by omega)]; rfl
      · rw [dn_t.mpr (show s - d2 < e2 by omega)]; simp
    · rw [up_t.mpr (show x ≤ s by omega), up_t.mpr (show e1 ≤ s - d1 by omega),
        dn_f.mpr (show e2 ≤ s - d2 by omega)]; rfl
  refine ⟨mkCell B false (up e1) (dn e2) (cst d1) (cst d2) (cst B.L) (cst B.b1)
    (cst B.c5) (cst B.B2) (cst B.C6) (up x)
    (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega))
    (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega))
    (in_cst (by omega) (by omega)) (fun s hs => up_f.mpr (by omega)) hst,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  exact mk_overlap t (up_t.mpr (show e1 ≤ t - B.b1 by omega)) (dn_t.mpr (show t - B.B2 < e2 by omega))
    (up_t.mpr (show x ≤ t - B.c5 by omega)) (up_f.mpr (show t - B.C6 < x by omega))

/-- **Fall-type counter-trace (NON-monotone reads).** At the single instant
`s5` both ustate request pins sample EARLY (`a1`, `a2`), everywhere else LATE
(`A1`, `A2`): q makes a 1-instant runt at `s5`, falls at `s5 + 1` (the loop
reads around the runt: H_LOOP_WIN), and rises for good at `X1`. O5 reads the
runt, O6 the 0 after it: both grants high at `t`. -/
theorem o1_fall_cex (hB : B.Ok) (H_LOOP_WIN : B.l < B.L) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2)
    (t : Int) (ht1 : e1 + B.b1 ≤ t) (ht2 : t < e2 + B.B2)
    (hf : FallAt B (X0 B e1 e2) (X1 B e1 e2) t) :
    ∃ c : Cell B false (up e1) (dn e2), ¬ Excl c ∧
      ∃ s, c.q s = true ∧ c.q (s + 1) = false ∧ s + 1 < X1 B e1 e2 := by
  unfold Box.Ok at hB
  obtain ⟨f1, f2, f3, f4, f5, f6⟩ := hf
  simp only [X0, X1] at f2 f3 f4 f5 f6 ⊢
  obtain ⟨Y, hY⟩ : ∃ Y, Y = max (e1 + B.A1) (e2 + B.A2) := ⟨_, rfl⟩
  rw [← hY] at f2 f5 f6 ⊢
  obtain ⟨s5, hs5⟩ : ∃ s, s = max (max (e1 + B.a1) (e2 + B.a2)) (t - B.C5) := ⟨_, rfl⟩
  obtain ⟨s6, hs6⟩ : ∃ s, s = min (Y - 1) (t - B.c6) := ⟨_, rfl⟩
  have hlt : s5 < s6 := by omega
  have hA1 : B.a1 ≤ B.A1 := by omega
  have hA2 : B.a2 ≤ B.A2 := by omega
  have qRt : ∀ u, qR s5 Y u = true ↔ (u = s5 ∨ Y ≤ u) := by intro u; simp [qR]
  have qRf : ∀ u, qR s5 Y u = false ↔ (u ≠ s5 ∧ u < Y) := by
    intro u; unfold qR; rw [decide_eq_false_iff_not]; omega
  have hst : ∀ u, 0 ≤ u → qR s5 Y u = stF (up e1 ((jumpMap s5 B.a1 B.A1 hA1).σ u))
      (dn e2 ((jumpMap s5 B.a2 B.A2 hA2).σ u)) (qR s5 Y ((skipMap s5 B.l B.L H_LOOP_WIN).σ u)) := by
    intro u _
    rw [stF_val]
    by_cases hu : u = s5
    · subst hu
      rw [jumpMap_s, jumpMap_s, up_t.mpr (show e1 ≤ u - B.a1 by omega),
        dn_f.mpr (show e2 ≤ u - B.a2 by omega), (qRt u).mpr (Or.inl rfl)]; rfl
    · rw [jumpMap_ne _ _ _ _ u hu, jumpMap_ne _ _ _ _ u hu]
      by_cases hX : Y ≤ u
      · rw [up_t.mpr (show e1 ≤ u - B.A1 by omega), dn_f.mpr (show e2 ≤ u - B.A2 by omega),
          (qRt u).mpr (Or.inr hX)]; rfl
      · have hne := skipMap_ne s5 B.l B.L H_LOOP_WIN u
        have hlt' := skipMap_lt s5 B.l B.L H_LOOP_WIN (by omega) u
        rw [(qRf u).mpr ⟨hu, by omega⟩, (qRf _).mpr ⟨hne, by omega⟩]
        by_cases h' : u < e1 + B.A1
        · rw [up_f.mpr (show u - B.A1 < e1 by omega)]; rfl
        · rw [dn_t.mpr (show u - B.A2 < e2 by omega)]; simp
  refine ⟨mkCell B false (up e1) (dn e2) (jumpMap s5 B.a1 B.A1 hA1) (jumpMap s5 B.a2 B.A2 hA2)
    (skipMap s5 B.l B.L H_LOOP_WIN) (cst B.b1) (cst (t - s5)) (cst B.B2) (cst (t - s6)) (qR s5 Y)
    ⟨Int.le_refl _, Int.le_refl _⟩ ⟨Int.le_refl _, Int.le_refl _⟩ ⟨Int.le_refl _, Int.le_refl _⟩
    (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega))
    (in_cst (by omega) (by omega)) (fun u hu => (qRf u).mpr ⟨by omega, by omega⟩) hst, ?_, ?_⟩
  · exact mk_overlap t (up_t.mpr (show e1 ≤ t - B.b1 by omega)) (dn_t.mpr (show t - B.B2 < e2 by omega))
      ((qRt _).mpr (Or.inl (show t - (t - s5) = s5 by omega)))
      ((qRf _).mpr ⟨show t - (t - s6) ≠ s5 by omega, show t - (t - s6) < Y by omega⟩)
  · exact ⟨s5, (qRt s5).mpr (Or.inl rfl), (qRf _).mpr ⟨by omega, by omega⟩, by omega⟩

/-- **Opposite sense, exact over the box, EVERY per-pin behaviour.** -/
theorem o1_box_iff (hB : B.Ok) (H_LOOP_WIN : B.l < B.L) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) :
    (∀ c : Cell B false (up e1) (dn e2), Excl c) ↔ ¬ O1Ov B e1 e2 := by
  constructor
  · rintro h ⟨t, h1, h2, hr | hf⟩
    · obtain ⟨c, _, hn⟩ := o1_rise_cex hB he2 ⟨t, h1, h2, hr⟩; exact hn (h c)
    · obtain ⟨c, hn, _⟩ := o1_fall_cex hB H_LOOP_WIN he1 he2 t h1 h2 hf; exact hn (h c)
  · intro hno c; exact o1_excl hB he1 hno c

/-- **Opposite sense, exact over the box, TRANSPORT behaviours.** -/
theorem o1_transport_iff (hB : B.Ok) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) :
    (∀ c : Cell B false (up e1) (dn e2), Transport c → Excl c) ↔ ¬ O1OvT B e1 e2 := by
  constructor
  · intro h hov
    obtain ⟨c, hT, hn⟩ := o1_rise_cex hB he2 hov; exact hn (h c hT)
  · intro hno c hT; exact o1_transport_excl hB he1 hno c hT

/-- Under `c5 < C6` the two windows coincide. -/
theorem o1_same (h : B.c5 < B.C6) : O1Ov B e1 e2 ↔ O1OvT B e1 e2 := by
  constructor
  · rintro ⟨t, a, b, r | f⟩
    · exact ⟨t, a, b, r⟩
    · exact ⟨t, a, b, fall_rise B _ _ t h f⟩
  · rintro ⟨t, a, b, r⟩; exact ⟨t, a, b, Or.inl r⟩

/-- **Non-monotone reads CHANGE the opposite-sense window.** A box where every
transport behaviour is exclusive but a per-pin behaviour overlaps: q -> O6
fixed 10 ps, q -> O5 fixed 20 ps (rise-type break-before-make holds), ustate's
request pins `[0, 20]`, both requests move at 100. -/
def boxD : Box := ⟨0, 20, 0, 20, 1, 3, 5, 5, 50, 50, 20, 20, 10, 10⟩

theorem o1_differs :
    boxD.Ok ∧ (∀ c : Cell boxD false (up 100) (dn 100), Transport c → Excl c) ∧
    ∃ c : Cell boxD false (up 100) (dn 100), ¬ Excl c := by
  have hok : boxD.Ok := by simp only [Box.Ok, boxD]; omega
  refine ⟨hok, (o1_transport_iff (e1 := 100) (e2 := 100) hok (by omega) (by omega)).mpr ?_, ?_⟩
  · rintro ⟨t, _, _, a, _⟩; simp only [boxD] at a; omega
  · obtain ⟨c, hn, _⟩ := o1_fall_cex (e1 := 100) (e2 := 100) hok (by simp only [boxD]; omega)
      (by omega) (by omega) 120
      (by simp only [boxD]; omega) (by simp only [boxD]; omega)
      (by simp only [FallAt, X0, X1, boxD]; omega)
    exact ⟨c, hn⟩

/-- Non-vacuity of `o1_excl`: requests moving at the SAME instant in opposite
senses, every behaviour of this box is exclusive (the grant pins see the
requests faster than the q path can move). -/
def boxN : Box := ⟨10, 20, 10, 20, 1, 3, 5, 15, 5, 15, 30, 40, 30, 40⟩

theorem o1_nonvacuous : boxN.Ok ∧ ¬ O1Ov boxN 100 100 ∧
    (∀ c : Cell boxN false (up 100) (dn 100), Excl c) ∧
    ∃ c : Cell boxN false (up 100) (dn 100), Transport c := by
  have hok : boxN.Ok := by simp only [Box.Ok, boxN]; omega
  have hno : ¬ O1Ov boxN 100 100 := by
    rintro ⟨t, h1, h2, ⟨_, a, _⟩ | ⟨_, _, a, _⟩⟩ <;> simp only [X0, boxN] at h1 h2 a <;> omega
  refine ⟨hok, hno, fun c => o1_excl hok (by omega) hno c, ?_⟩
  -- a transport behaviour: r1 via 10, r2 via 10, q rises at 110
  have hst : ∀ s, 0 ≤ s → up 110 s = stF (up 100 (s - 10)) (dn 100 (s - 10)) (up 110 (s - 3)) := by
    intro s _
    rw [stF_val]
    by_cases h : s < 110
    · rw [up_f.mpr h, up_f.mpr (show s - 3 < 110 by omega), up_f.mpr (show s - 10 < 100 by omega)]; rfl
    · rw [up_t.mpr (show 110 ≤ s by omega), up_t.mpr (show 100 ≤ s - 10 by omega),
        dn_f.mpr (show 100 ≤ s - 10 by omega)]; rfl
  exact ⟨mkCell boxN false (up 100) (dn 100) (cst 10) (cst 10) (cst 3) (cst 5) (cst 30) (cst 5)
    (cst 30) (up 110) (in_cst (by decide) (by decide)) (in_cst (by decide) (by decide))
    (in_cst (by decide) (by decide)) (in_cst (by decide) (by decide)) (in_cst (by decide) (by decide))
    (in_cst (by decide) (by decide)) (in_cst (by decide) (by decide))
    (fun s hs => up_f.mpr (by omega)) hst, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end o1

/-! ## 8. Non-vacuity, same sense -/

section su
variable {B : Box} {e1 e2 : Int}

/-- A transport behaviour with one clean q rise at any `x ∈ [e1+a1, e1+A1]`
(commit regime), grants through any fixed delays of the box. -/
theorem su_step (hB : B.Ok) (H_COMMIT : e1 + B.A1 + B.L ≤ e2 + B.a2) (x : Int)
    (hx1 : e1 + B.a1 ≤ x) (hx2 : x ≤ e1 + B.A1) (he : 0 ≤ e1)
    (db1 db2 d5 d6 : Int) (h1 : B.b1 ≤ db1 ∧ db1 ≤ B.B1) (h2 : B.b2 ≤ db2 ∧ db2 ≤ B.B2)
    (h5 : B.c5 ≤ d5 ∧ d5 ≤ B.C5) (h6 : B.c6 ≤ d6 ∧ d6 ≤ B.C6) :
    ∃ c : Cell B false (up e1) (up e2), Transport c ∧ (∀ t, c.q t = up x t) ∧
      (∀ t, c.g1 t = (up e1 (t - db1) && up x (t - d5))) ∧
      (∀ t, c.g2 t = (up e2 (t - db2) && !up x (t - d6))) := by
  unfold Box.Ok at hB
  have hst : ∀ s, 0 ≤ s → up x s = stF (up e1 (s - (x - e1))) (up e2 (s - B.a2)) (up x (s - B.L)) := by
    intro s _
    rw [stF_val]
    by_cases h : s < x
    · rw [up_f.mpr h, up_f.mpr (show s - (x - e1) < e1 by omega),
        up_f.mpr (show s - B.a2 < e2 by omega), up_f.mpr (show s - B.L < x by omega)]; rfl
    · rw [up_t.mpr (show x ≤ s by omega), up_t.mpr (show e1 ≤ s - (x - e1) by omega)]
      by_cases h2 : s < e2 + B.a2
      · rw [up_f.mpr (show s - B.a2 < e2 by omega)]; rfl
      · rw [up_t.mpr (show e2 ≤ s - B.a2 by omega), up_t.mpr (show x ≤ s - B.L by omega)]; rfl
  refine ⟨mkCell B false (up e1) (up e2) (cst (x - e1)) (cst B.a2) (cst B.L) (cst db1)
    (cst d5) (cst db2) (cst d6) (up x)
    (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega))
    (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega))
    (in_cst (by omega) (by omega)) (fun s hs => up_f.mpr (by omega)) hst,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, fun _ => rfl, fun t => ?_, fun t => ?_⟩
  · show gr1 _ _ _ = _; rw [gr1_eq]; rfl
  · show gr2 _ _ _ = _; rw [gr2_eq]; rfl

/-- Box for the same-sense non-vacuity witness. -/
def boxS : Box := ⟨10, 20, 10, 20, 1, 3, 5, 15, 5, 15, 30, 40, 30, 40⟩

/-- Non-vacuity of `su_box_iff`'s COMMIT branch: r1 at 100, r2 at 200; every
behaviour is exclusive, and a behaviour exists in which side 1 is granted. -/
theorem su_nonvacuous : boxS.Ok ∧ 2 ≤ boxS.L ∧ boxS.c5 < boxS.C6 ∧ boxS.c6 ≤ boxS.C5 + 1 ∧
    (100 + boxS.A1 + boxS.L ≤ 200 + boxS.a2 ∧ ¬ SuOvT boxS 100 200) ∧
    (∀ c : Cell boxS false (up 100) (up 200), Excl c) ∧
    ∃ c : Cell boxS false (up 100) (up 200), c.g1 200 = true ∧ c.g2 200 = false := by
  have hok : boxS.Ok := by simp only [Box.Ok, boxS]; omega
  have hno : ¬ SuOvT boxS 100 200 := by
    rw [suOvT_closed hok]; simp only [boxS]; omega
  refine ⟨hok, by decide, by decide, by decide, ⟨by decide, hno⟩, ?_, ?_⟩
  · exact (su_box_iff hok (by decide) (by decide) (by omega) (by omega)).mpr (Or.inr ⟨by decide, hno⟩)
  · obtain ⟨c, _, _, hg1, hg2⟩ := su_step (e1 := 100) (e2 := 200) hok (by decide) 120
      (by decide) (by decide) (by omega) 5 5 30 30 (by decide) (by decide) (by decide) (by decide)
    exact ⟨c, by rw [hg1]; decide, by rw [hg2]; decide⟩

/-- Non-vacuity of `su_osc`'s premises: the gap window between QUIET and
COMMIT is nonempty in `boxS` (r1 at 100, r2 at 105: within one window). -/
theorem su_osc_instance : ∃ c : Cell boxS false (up 100) (up 105), Transport c ∧
    (∀ T, ∃ t, T ≤ t ∧ c.g1 t = true ∧ c.g2 t = true) ∧
    (∀ T, ∃ t1 t2, T ≤ t1 ∧ T ≤ t2 ∧ c.q t1 = true ∧ c.q t2 = false) :=
  su_osc (by simp only [Box.Ok, boxS]; omega) (by decide) (by decide) (by omega) (by omega)
    (by decide) (by decide)

end su

/-! ### The transport grant-overlap cap does not survive non-monotone reads

`ArbOverlapRace.grant_cap` (transport): every g1.g2 run is at most |b5 - b6|
long. With per-pin windows at least one loop wide, an oscillating q is sampled
at a 1 by O5 and at a 0 by O6 at EVERY instant: both grants high for ever. -/

section cap
variable {B : Box} {e1 e2 : Int}

/-- The O5 sampler: the latest instant `≤ t - c5` congruent to `x` mod `L`. -/
def sampler (x c L : Int) (t : Int) : Int := t - c - ((t - c - x) % L)

theorem su_overlap_forever (hB : B.Ok) (H_LOOP2 : 2 ≤ B.L)
    (H_WIDE5 : B.L - 1 ≤ B.C5 - B.c5) (H_WIDE6 : B.c5 + B.L ≤ B.C6) (H_NEAR : B.c6 ≤ B.c5 + 1)
    (he1 : 0 ≤ e1)
    (hnq : e1 + B.a1 < e2 + B.A2) (hnc : e2 + B.a2 < e1 + B.A1 + B.L) :
    ∃ c : Cell B false (up e1) (up e2), ∃ T0, ∀ t, T0 ≤ t → c.g1 t = true ∧ c.g2 t = true := by
  unfold Box.Ok at hB
  obtain ⟨w, hw⟩ : ∃ w, w = max 1 (e2 - e1 + B.a2 - B.A1) := ⟨_, rfl⟩
  obtain ⟨d2, hd2⟩ : ∃ d, d = max B.a2 (w - (e2 - e1) + B.a1) := ⟨_, rfl⟩
  obtain ⟨d1, hd1⟩ : ∃ d, d = d2 - (w - (e2 - e1)) := ⟨_, rfl⟩
  have hw1 : 1 ≤ w := by omega
  have hwL : w < B.L := by omega
  have hwe : e2 + d2 = e1 + d1 + w := by omega
  have hL0 : B.L ≠ 0 := by omega
  have hLp : 0 < B.L := by omega
  have m0 : ∀ a, 0 ≤ a % B.L := fun a => Int.emod_nonneg a hL0
  have m1 : ∀ a, a % B.L < B.L := fun a => Int.emod_lt_of_pos a hLp
  let v5 : Rd := mk (sampler (e1 + d1) B.c5 B.L) B.c5 B.C5
    (fun t => by have := m1 (t - B.c5 - (e1 + d1)); simp only [sampler]; omega)
    (fun t => by have := m0 (t - B.c5 - (e1 + d1)); simp only [sampler]; omega)
  let v6 : Rd := mk (fun t => sampler (e1 + d1) B.c5 B.L t - 1) B.c6 B.C6
    (fun t => by have := m1 (t - B.c5 - (e1 + d1)); simp only [sampler]; omega)
    (fun t => by have := m0 (t - B.c5 - (e1 + d1)); simp only [sampler]; omega)
  let c := mkCell B false (up e1) (up e2) (cst d1) (cst d2) (cst B.L) (cst B.b1) v5
    (cst B.b2) v6 (qOsc (e1 + d1) w B.L)
    (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega))
    (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega))
    ⟨Int.le_refl _, Int.le_refl _⟩ ⟨Int.le_refl _, Int.le_refl _⟩
    (fun t ht => by simp only [qOsc]; simp; omega)
    (fun t _ => qOsc_st e1 e2 d1 d2 B.L w hw1 hwL hwe t)
  refine ⟨c, max (max (e1 + d1 + B.c5 + B.L) (e1 + B.b1)) (e2 + B.b2), ?_⟩
  intro t ht
  apply (ov_iff c t).mpr
  obtain ⟨a, ha⟩ : ∃ a, a = t - B.c5 - (e1 + d1) := ⟨_, rfl⟩
  have haL : B.L ≤ a := by omega
  have hk : 1 ≤ a / B.L := (Int.le_ediv_iff_mul_le hLp).mpr (by omega)
  have hdef := Int.emod_def a B.L
  obtain ⟨k, hkk⟩ : ∃ k, k = a / B.L := ⟨_, rfl⟩
  rw [← hkk] at hk hdef
  have hs : sampler (e1 + d1) B.c5 B.L t = e1 + d1 + k * B.L := by
    simp only [sampler]; rw [← ha, hdef, Int.mul_comm]; omega
  refine ⟨up_t.mpr ?_, up_t.mpr ?_, ?_, ?_⟩
  · show e1 ≤ t - B.b1; omega
  · show e2 ≤ t - B.b2; omega
  · show qOsc (e1 + d1) w B.L (sampler (e1 + d1) B.c5 B.L t) = true
    rw [hs]; simp only [qOsc, decide_eq_true_eq]
    rw [show e1 + d1 + k * B.L - (e1 + d1) = k * B.L by omega, emod_kL]
    have := le_kL k B.L (by omega) (by omega); omega
  · show qOsc (e1 + d1) w B.L (sampler (e1 + d1) B.c5 B.L t - 1) = false
    rw [hs]; simp only [qOsc]; simp
    intro _
    rw [show e1 + d1 + k * B.L - 1 - (e1 + d1) = k * B.L - 1 by omega,
      emod_kL_pred k B.L (by omega)]
    omega

/-- Instance: `boxS`, r1 at 100, r2 at 105: both grants high at every instant
from some time on (per-pin behaviour). -/
theorem su_overlap_forever_instance :
    ∃ c : Cell boxS false (up 100) (up 105), ∃ T0, ∀ t, T0 ≤ t → c.g1 t = true ∧ c.g2 t = true :=
  su_overlap_forever (by simp only [Box.Ok, boxS]; omega) (by decide) (by decide) (by decide)
    (by decide) (by omega) (by decide) (by decide)

end cap

/-! ## 9. Downstream: what a reader through its own windows can see -/

/-- The box seen by a reader that reads g1 through `[y1, Y1]` and g2 through
`[y2, Y2]`: the grant pins' windows grow by the reader's. -/
def readerBox (B : Box) (y1 Y1 y2 Y2 : Int) : Box :=
  { B with b1 := B.b1 + y1, B1 := B.B1 + Y1, c5 := B.c5 + y1, C5 := B.C5 + Y1,
           b2 := B.b2 + y2, B2 := B.B2 + Y2, c6 := B.c6 + y2, C6 := B.C6 + Y2 }

/-- **The reader is a cell**: what a reader sees of the two grants is the
grant pair of a behaviour of `readerBox` (composed read maps,
`LibGapSteer.Rd.comp`). So every sufficient condition of §2-§7 holds for the
reader with the composed windows. -/
def Cell.reader {B : Box} {q0 : Bool} {r1 r2 : Int → Bool} (c : Cell B q0 r1 r2)
    {y1 Y1 y2 Y2 : Int} (m1 m2 : Rd) (h1 : In m1 y1 Y1) (h2 : In m2 y2 Y2) :
    Cell (readerBox B y1 Y1 y2 Y2) q0 r1 r2 :=
  { p1 := c.p1, p2 := c.p2, pq := c.pq,
    u1 := Rd.comp c.u1 m1, x2 := Rd.comp c.x2 m1, v5 := Rd.comp c.v5 m1,
    x1 := Rd.comp c.x1 m2, u2 := Rd.comp c.u2 m2, v6 := Rd.comp c.v6 m2,
    q := c.q, g1 := fun t => c.g1 (m1.σ t), g2 := fun t => c.g2 (m2.σ t),
    H_P1 := c.H_P1, H_P2 := c.H_P2, H_PQ := c.H_PQ,
    H_U1 := by have := c.H_U1; unfold In at *; simp only [readerBox, Rd.comp]; omega,
    H_U2 := by have := c.H_U2; unfold In at *; simp only [readerBox, Rd.comp]; omega,
    H_V5 := by have := c.H_V5; unfold In at *; simp only [readerBox, Rd.comp]; omega,
    H_V6 := by have := c.H_V6; unfold In at *; simp only [readerBox, Rd.comp]; omega,
    H_PRE := c.H_PRE, H_ST := c.H_ST,
    H_O5 := fun t => c.H_O5 (m1.σ t), H_O6 := fun t => c.H_O6 (m2.σ t) }

theorem readerBox_ok (B : Box) (hB : B.Ok) (y1 Y1 y2 Y2 : Int) (h1 : 0 ≤ y1) (h2 : y1 ≤ Y1)
    (h3 : 0 ≤ y2) (h4 : y2 ≤ Y2) : (readerBox B y1 Y1 y2 Y2).Ok := by
  unfold Box.Ok at *; simp only [readerBox]; omega

/-- Opposite sense, downstream: if the composed box has no overlap instant,
the reader never sees both grants high. -/
theorem o1_reader_excl {B : Box} {e1 e2 : Int} (hB : B.Ok) (he1 : 0 ≤ e1)
    (c : Cell B false (up e1) (dn e2)) {y1 Y1 y2 Y2 : Int} (m1 m2 : Rd)
    (h1 : In m1 y1 Y1) (h2 : In m2 y2 Y2) (hy : 0 ≤ y1 ∧ 0 ≤ y2)
    (hno : ¬ O1Ov (readerBox B y1 Y1 y2 Y2) e1 e2) :
    ∀ t, ¬ (c.g1 (m1.σ t) = true ∧ c.g2 (m2.σ t) = true) := by
  have := Rd.lo_le_hi m1; have := Rd.lo_le_hi m2; unfold In at h1 h2
  exact o1_excl (readerBox_ok B hB _ _ _ _ hy.1 (by omega) hy.2 (by omega)) he1 hno
    (c.reader m1 m2 h1 h2)

/-- Same sense (commit), downstream. -/
theorem su_reader_excl {B : Box} {e1 e2 : Int} (hB : B.Ok) (he1 : 0 ≤ e1)
    (H_COMMIT : e1 + B.A1 + B.L ≤ e2 + B.a2)
    (c : Cell B false (up e1) (up e2)) {y1 Y1 y2 Y2 : Int} (m1 m2 : Rd)
    (h1 : In m1 y1 Y1) (h2 : In m2 y2 Y2) (hy : 0 ≤ y1 ∧ 0 ≤ y2)
    (hno : ¬ SuOv (readerBox B y1 Y1 y2 Y2) e1 e2) :
    ∀ t, ¬ (c.g1 (m1.σ t) = true ∧ c.g2 (m2.σ t) = true) := by
  have := Rd.lo_le_hi m1; have := Rd.lo_le_hi m2; unfold In at h1 h2
  exact su_commit_excl (readerBox_ok B hB _ _ _ _ hy.1 (by omega) hy.2 (by omega))
    (by simp only [readerBox]; exact H_COMMIT) he1 hno (c.reader m1 m2 h1 h2)

/-- **Reader of a clean exclusive handover, exact.** g2 falls at `h`, g1 rises
at `h' ≥ h` (never both high at the source). A reader through `[y1, Y1]` (g1)
and `[y2, Y2]` (g2) never sees both high, for every pair of read maps, iff
`Y2 - y1 ≤ h' - h`: the handover gap must cover the reader's own skew. -/
theorem reader_handover_iff (h h' y1 Y1 y2 Y2 : Int) (hy1 : y1 ≤ Y1) (hy2 : y2 ≤ Y2) :
    (∀ m1 m2 : Rd, In m1 y1 Y1 → In m2 y2 Y2 → ∀ t,
      ¬ (up h' (m1.σ t) = true ∧ dn h (m2.σ t) = true)) ↔ Y2 - y1 ≤ h' - h := by
  constructor
  · intro H
    apply Classical.byContradiction; intro hn
    exact H (cst y1) (cst Y2) (in_cst (Int.le_refl _) hy1) (in_cst hy2 (Int.le_refl _)) (h' + y1)
      ⟨up_t.mpr (show h' ≤ h' + y1 - y1 by omega), dn_t.mpr (show h' + y1 - Y2 < h by omega)⟩
  · intro hg m1 m2 i1 i2 t ⟨a, b⟩
    have := up_t.mp a; have := dn_t.mp b; unfold In at i1 i2
    have := m1.le t; have := m2.ge t; omega

/-- A FIFO (monotone) reader of a clean step sees a clean step. -/
theorem reader_mono_step (e : Int) (m : Rd) (hm : ∀ t t', t ≤ t' → m.σ t ≤ m.σ t')
    (t1 t2 : Int) (h12 : t1 ≤ t2) (h : up e (m.σ t1) = true) : up e (m.σ t2) = true :=
  up_t.mpr (Int.le_trans (up_t.mp h) (hm _ _ h12))

/-- **A non-monotone reader can see a runt in a clean edge, exact**: there
are a read map in `[lo, hi]` and instants `t1 < t2` with the view of a rising
step 1 at `t1` and 0 at `t2` iff the window has at least 3 instants. -/
theorem reader_glitch_iff (e lo hi : Int) :
    (∃ m : Rd, In m lo hi ∧ ∃ t1 t2, t1 < t2 ∧ up e (m.σ t1) = true ∧ up e (m.σ t2) = false) ↔
    lo + 2 ≤ hi := by
  constructor
  · rintro ⟨m, hm, t1, t2, h12, a, b⟩
    have := up_t.mp a; have := up_f.mp b; unfold In at hm
    have := m.le t1; have := m.ge t2; omega
  · intro hw
    let m : Rd := mk (fun t => if t = e + lo + 1 then t - hi else t - lo) lo hi
      (fun t => by show t - hi ≤ (if t = e + lo + 1 then t - hi else t - lo); split <;> omega)
      (fun t => by show (if t = e + lo + 1 then t - hi else t - lo) ≤ t - lo; split <;> omega)
    refine ⟨m, ⟨Int.le_refl _, Int.le_refl _⟩, e + lo, e + lo + 1, by omega, ?_, ?_⟩
    · show up e (if e + lo = e + lo + 1 then e + lo - hi else e + lo - lo) = true
      rw [ite_eq_right (by omega)]; exact up_t.mpr (by omega)
    · show up e (if e + lo + 1 = e + lo + 1 then e + lo + 1 - hi else e + lo + 1 - lo) = false
      rw [ite_eq_left rfl]; exact up_f.mpr (by omega)

/-! ## 10. Handover: r2 waiting, the holder r1 falls at `f` (q0 = 1)

The bd_arb.v header's handover (r1 -> r2 direction): r2 has been high for
ever, r1 held the grant (q = 1) and falls at `f`. The transition is q 1 -> 0,
confined to `[f + a1, f + A1)`. -/

/-- Transport-type (clean fall seen): O5 still shows the old 1, O6 the new 0. -/
def DownAt (B : Box) (Y0 Y1 t : Int) : Prop :=
  B.c6 < B.C5 ∧ Y0 + B.c6 ≤ t ∧ t ≤ Y1 - 1 + B.C5

/-- Runt type: q dips to 0 for an instant and comes back (non-monotone reads);
O6 shows the dip, O5 the 1 after it. -/
def UpRuntAt (B : Box) (Y0 Y1 t : Int) : Prop :=
  B.c5 < B.C6 ∧ Y0 + 2 ≤ Y1 ∧ Y0 + B.c6 ≤ t ∧ Y0 + 1 + B.c5 ≤ t ∧
  t ≤ Y1 - 1 + B.C5 ∧ t ≤ Y1 - 2 + B.C6

theorem uprunt_down (B : Box) (Y0 Y1 t : Int) (h : B.c6 < B.C5) :
    UpRuntAt B Y0 Y1 t → DownAt B Y0 Y1 t := by
  intro ⟨_, _, h3, _, h5, _⟩; exact ⟨h, h3, h5⟩

/-- Transition split for q 1 -> 0. -/
theorem trans_split_dn {B : Box} {q0 : Bool} {r1 r2 : Int → Bool} (c : Cell B q0 r1 r2)
    (Y0 Y1 : Int) (h0 : ∀ s, s < Y0 → c.q s = true) (h1 : ∀ s, Y1 ≤ s → c.q s = false)
    (t : Int) (h5 : c.q (c.v5.σ t) = true) (h6 : c.q (c.v6.σ t) = false) :
    DownAt B Y0 Y1 t ∨ UpRuntAt B Y0 Y1 t := by
  have a1 := c.v5.ge t; have a2 := c.v5.le t; have a3 := c.v6.ge t; have a4 := c.v6.le t
  have b5 := c.H_V5; have b6 := c.H_V6
  unfold In at b5 b6
  have hs6 : Y0 ≤ c.v6.σ t := by
    apply Classical.byContradiction; intro hn
    rw [h0 _ (by omega)] at h6; exact Bool.noConfusion h6
  have hs5 : c.v5.σ t < Y1 := by
    apply Classical.byContradiction; intro hn
    rw [h1 _ (by omega)] at h5; exact Bool.noConfusion h5
  rcases Int.lt_trichotomy (c.v5.σ t) (c.v6.σ t) with hl | he | hg
  · left; exact ⟨by omega, by omega, by omega⟩
  · rw [he, h6] at h5; exact absurd h5 (by decide)
  · right; exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

section h12
variable {B : Box} {f : Int}

/-- r2: high for ever. -/
def hi1 : Int → Bool := fun _ => true

theorem h12_before (hB : B.Ok) (c : Cell B true (dn f) hi1) :
    ∀ t, t < f + B.a1 → c.q t = true := by
  have hP1 := c.H_P1; have hPQ := c.H_PQ; unfold In at hP1 hPQ; unfold Box.Ok at hB
  refine int_ind _ (fun t ht _ => c.H_PRE t ht) ?_
  intro t ht ih hlt
  rw [c.H_ST t ht]
  have g1 := c.p1.le t; have g3 := c.pq.le t
  have hq : c.q (c.pq.σ t) = true := ih _ (by omega) (by omega)
  rw [hq, dn_t.mpr (show c.p1.σ t < f by omega), stF_val]; rfl

theorem h12_after (hB : B.Ok) (hf : 0 ≤ f) (c : Cell B true (dn f) hi1) :
    ∀ t, f + B.A1 ≤ t → c.q t = false := by
  have hP1 := c.H_P1; unfold In at hP1; unfold Box.Ok at hB
  intro t ht
  rw [c.H_ST t (by omega), dn_f.mpr (show f ≤ c.p1.σ t by have := c.p1.ge t; omega), stF_val]; simp [hi1]

def H12Ov (B : Box) (f : Int) : Prop :=
  ∃ t, t < f + B.B1 ∧ (DownAt B (f + B.a1) (f + B.A1) t ∨ UpRuntAt B (f + B.a1) (f + B.A1) t)

def H12OvT (B : Box) (f : Int) : Prop :=
  ∃ t, t < f + B.B1 ∧ DownAt B (f + B.a1) (f + B.A1) t

theorem h12OvT_closed (hB : B.Ok) : H12OvT B f ↔ (B.c6 < B.C5 ∧ B.a1 + B.c6 < B.B1) := by
  unfold Box.Ok at hB
  constructor
  · rintro ⟨t, h1, a, b, _⟩; exact ⟨a, by omega⟩
  · rintro ⟨a, b⟩; exact ⟨f + B.a1 + B.c6, by omega, a, by omega, by omega⟩

theorem h12_excl (hB : B.Ok) (hf : 0 ≤ f) (hno : ¬ H12Ov B f) (c : Cell B true (dn f) hi1) :
    Excl c := by
  intro t h
  obtain ⟨h1, _, h5, h6⟩ := (ov_iff c t).mp h
  have hU1 := c.H_U1; unfold In at hU1
  have := dn_t.mp h1; have := c.u1.ge t
  exact hno ⟨t, by omega, trans_split_dn c _ _ (h12_before hB c) (h12_after hB hf c) t h5 h6⟩

theorem h12_transport_excl (hB : B.Ok) (hf : 0 ≤ f) (hno : ¬ H12OvT B f)
    (c : Cell B true (dn f) hi1) (hT : Transport c) : Excl c := by
  have h1 := c.H_P1; have h3 := c.H_PQ; have h4 := c.H_U1
  have h6 := c.H_V5; have h7 := c.H_V6
  unfold In at h1 h3 h4 h6 h7; unfold Transport at hT
  refine h12_excl (tight_ok hB c) hf ?_ c.tight
  rintro ⟨t, ht1, hd | hu⟩
  · apply hno; refine ⟨t, ?_, ?_⟩
    · simp only [tightBox] at ht1; omega
    · obtain ⟨a, b, d⟩ := hd; simp only [tightBox] at a b d; exact ⟨by omega, by omega, by omega⟩
  · obtain ⟨_, b, _⟩ := hu; simp only [tightBox] at b; omega

/-- Transport counter-trace: a clean q fall at `y`, O5 reading late, O6 early. -/
theorem h12_down_cex (hB : B.Ok) (hf : 0 ≤ f) (hov : H12OvT B f) :
    ∃ c : Cell B true (dn f) hi1, Transport c ∧ ¬ Excl c := by
  unfold Box.Ok at hB
  obtain ⟨t, ht, h1, h2, h3⟩ := hov
  obtain ⟨y, hy⟩ : ∃ y, y = max (f + B.a1) (t - B.C5 + 1) := ⟨_, rfl⟩
  have hst : ∀ s, 0 ≤ s → dn y s = stF (dn f (s - (y - f))) (hi1 (s - B.a2)) (dn y (s - B.L)) := by
    intro s _
    rw [stF_val]; simp only [hi1]
    by_cases h : s < y
    · rw [dn_t.mpr h, dn_t.mpr (show s - (y - f) < f by omega), dn_t.mpr (show s - B.L < y by omega)]; rfl
    · rw [dn_f.mpr (show y ≤ s by omega), dn_f.mpr (show f ≤ s - (y - f) by omega)]; simp
  refine ⟨mkCell B true (dn f) hi1 (cst (y - f)) (cst B.a2) (cst B.L) (cst B.B1)
    (cst B.C5) (cst B.b2) (cst B.c6) (dn y)
    (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega))
    (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega))
    (in_cst (by omega) (by omega)) (fun s hs => dn_t.mpr (by omega)) hst,
    ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩, ?_⟩
  exact mk_overlap t (dn_t.mpr (show t - B.B1 < f by omega)) rfl
    (dn_t.mpr (show t - B.C5 < y by omega)) (dn_f.mpr (show y ≤ t - B.c6 by omega))

/-- The dip trace: 1 except 0 at the single instant `s` and 0 from `Y1`. -/
def qD (s Y1 t : Int) : Bool := decide (t ≠ s ∧ t < Y1)

/-- Non-monotone counter-trace: at the single instant `s6` the r1 pin samples
EARLY (sees the fall), elsewhere LATE; q dips to 0 at `s6` and the loop
(skipping `s6`) restores 1 until `Y1`. O6 reads the dip, O5 the 1 after it. -/
theorem h12_runt_cex (hB : B.Ok) (H_LOOP_WIN : B.l < B.L) (hf : 0 ≤ f) (t : Int)
    (ht : t < f + B.B1) (hu : UpRuntAt B (f + B.a1) (f + B.A1) t) :
    ∃ c : Cell B true (dn f) hi1, ¬ Excl c ∧
      ∃ s, c.q (s - 1) = true ∧ c.q s = false ∧ c.q (s + 1) = true := by
  unfold Box.Ok at hB
  obtain ⟨u1, u2, u3, u4, u5, u6⟩ := hu
  obtain ⟨s6, hs6⟩ : ∃ s, s = max (f + B.a1) (t - B.C6) := ⟨_, rfl⟩
  obtain ⟨s5, hs5⟩ : ∃ s, s = min (f + B.A1 - 1) (t - B.c5) := ⟨_, rfl⟩
  have hlt : s6 < s5 := by omega
  have hA1 : B.a1 ≤ B.A1 := by omega
  have qDt : ∀ u, qD s6 (f + B.A1) u = true ↔ (u ≠ s6 ∧ u < f + B.A1) := by
    intro u; unfold qD; rw [decide_eq_true_iff]
  have qDf : ∀ u, qD s6 (f + B.A1) u = false ↔ (u = s6 ∨ f + B.A1 ≤ u) := by
    intro u; unfold qD; rw [decide_eq_false_iff_not]; omega
  have hst : ∀ u, 0 ≤ u → qD s6 (f + B.A1) u = stF (dn f ((jumpMap s6 B.a1 B.A1 hA1).σ u))
      (hi1 ((cst B.a2).σ u)) (qD s6 (f + B.A1) ((skipMap s6 B.l B.L H_LOOP_WIN).σ u)) := by
    intro u _
    rw [stF_val]; simp only [hi1]
    by_cases hu : u = s6
    · subst hu
      rw [jumpMap_s, dn_f.mpr (show f ≤ u - B.a1 by omega), (qDf u).mpr (Or.inl rfl)]; simp
    · rw [jumpMap_ne _ _ _ _ u hu]
      by_cases hX : f + B.A1 ≤ u
      · rw [dn_f.mpr (show f ≤ u - B.A1 by omega), (qDf u).mpr (Or.inr hX)]; simp
      · have hne := skipMap_ne s6 B.l B.L H_LOOP_WIN u
        have hlt' := skipMap_lt s6 B.l B.L H_LOOP_WIN (by omega) u
        rw [dn_t.mpr (show u - B.A1 < f by omega), (qDt u).mpr ⟨hu, by omega⟩,
          (qDt _).mpr ⟨hne, by omega⟩]; rfl
  refine ⟨mkCell B true (dn f) hi1 (jumpMap s6 B.a1 B.A1 hA1) (cst B.a2)
    (skipMap s6 B.l B.L H_LOOP_WIN) (cst B.B1) (cst (t - s5)) (cst B.b2) (cst (t - s6))
    (qD s6 (f + B.A1))
    ⟨Int.le_refl _, Int.le_refl _⟩ (in_cst (by omega) (by omega)) ⟨Int.le_refl _, Int.le_refl _⟩
    (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega))
    (in_cst (by omega) (by omega)) (fun u hu => (qDt u).mpr ⟨by omega, by omega⟩) hst, ?_, ?_⟩
  · exact mk_overlap t (dn_t.mpr (show t - B.B1 < f by omega)) rfl
      ((qDt _).mpr ⟨show t - (t - s5) ≠ s6 by omega, show t - (t - s5) < f + B.A1 by omega⟩)
      ((qDf _).mpr (Or.inl (show t - (t - s6) = s6 by omega)))
  · exact ⟨s6, (qDt _).mpr ⟨by omega, by omega⟩, (qDf _).mpr (Or.inl rfl),
      (qDt _).mpr ⟨by omega, by omega⟩⟩

/-- **Handover, exact over the box, EVERY per-pin behaviour.** -/
theorem h12_box_iff (hB : B.Ok) (H_LOOP_WIN : B.l < B.L) (hf : 0 ≤ f) :
    (∀ c : Cell B true (dn f) hi1, Excl c) ↔ ¬ H12Ov B f := by
  constructor
  · rintro h ⟨t, h1, hd | hu⟩
    · obtain ⟨c, _, hn⟩ := h12_down_cex hB hf ⟨t, h1, hd⟩; exact hn (h c)
    · obtain ⟨c, hn, _⟩ := h12_runt_cex hB H_LOOP_WIN hf t h1 hu; exact hn (h c)
  · intro hno c; exact h12_excl hB hf hno c

/-- **Handover, exact over the box, TRANSPORT behaviours**; closed form
`h12OvT_closed`: exclusion iff `C5 ≤ c6 ∨ B1 ≤ a1 + c6`. -/
theorem h12_transport_iff (hB : B.Ok) (hf : 0 ≤ f) :
    (∀ c : Cell B true (dn f) hi1, Transport c → Excl c) ↔ ¬ H12OvT B f := by
  constructor
  · intro h hov; obtain ⟨c, hT, hn⟩ := h12_down_cex hB hf hov; exact hn (h c hT)
  · intro hno c hT; exact h12_transport_excl hB hf hno c hT

theorem h12_same (h : B.c6 < B.C5) : H12Ov B f ↔ H12OvT B f := by
  constructor
  · rintro ⟨t, a, d | u⟩
    · exact ⟨t, a, d⟩
    · exact ⟨t, a, uprunt_down B _ _ t h u⟩
  · rintro ⟨t, a, d⟩; exact ⟨t, a, Or.inl d⟩

/-- **Non-monotone reads change the handover window** (q on the fast O5 pin,
`C5 ≤ c6`, as with q on A5): transport proves exclusion, a per-pin behaviour
overlaps. Box: ustate r1 `[0, 20]`, ugrant r1 -> O5 fixed 60, q -> O5 fixed
20, q -> O6 fixed 30; r1 falls at 100. -/
def boxH : Box := ⟨0, 20, 0, 20, 1, 3, 60, 60, 5, 5, 20, 20, 30, 30⟩

theorem h12_differs :
    boxH.Ok ∧ (∀ c : Cell boxH true (dn 100) hi1, Transport c → Excl c) ∧
    ∃ c : Cell boxH true (dn 100) hi1, ¬ Excl c := by
  have hok : boxH.Ok := by simp only [Box.Ok, boxH]; omega
  refine ⟨hok, (h12_transport_iff (f := 100) hok (by omega)).mpr ?_, ?_⟩
  · rw [h12OvT_closed hok]; simp only [boxH]; omega
  · obtain ⟨c, hn, _⟩ := h12_runt_cex (f := 100) hok (by simp only [boxH]; omega) (by omega) 139
      (by simp only [boxH]; omega) (by simp only [UpRuntAt, boxH]; omega)
    exact ⟨c, hn⟩

end h12

end Formal.Cells.ArbPin
