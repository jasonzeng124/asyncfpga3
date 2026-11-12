import Formal.Cells.ArbPin

/-!
# ArbPin2: the mirror cases of `bd_arbcell`'s per-pin race, and the per-pin conditions on the 36 routed gcd_hw arbiters

Probe Barp2 (shard B, 2026-10-27). Core Lean, no Mathlib. Note: `formal/notes/B-arb-pin2.md`.
Builds on `ArbPin` (probe Barp): the same cell, the same per-pin, NON-monotone read model
(`LibGapSteer.Rd`: every pin shows its driver at some instant of its window, chosen freely
at every output instant: no FIFO), the same `Box` / `Cell` / `Excl` / `Transport`.

## Part 1: the mirror cases, exact over the box

* `cswap` (side swap): a behaviour of box `B` with requests `(r1, r2)` and initial `q0` IS a
  behaviour of `swapB B` (pins of side 1 and side 2 exchanged, q -> O5 and q -> O6 exchanged)
  with requests `(r2, r1)`, initial `!q0` and trace `!q` (from the real INITs: `stF_swap`,
  `gr1_swap`, `gr2_swap`). `all_excl_swap` / `all_transport_swap`: exclusion of every
  (transport) behaviour transfers both ways. So every ArbPin window has an exact mirror:
  - `sd_box_iff` / `sd_transport_iff`: both rise, q0 = 1 (side 1 won last);
  - `o2_box_iff` / `o2_transport_iff`: r1 falls, r2 rises, q0 = 1;
  - `h21_box_iff` / `h21_transport_iff`: the r2 -> r1 handover (r1 waiting, holder r2 falls).
* Closed forms: `h12Ov_closed` (per-pin handover window), `o1OvT_closed`, `o1Ov_closed`.
* NEW, both requests fall, q0 = 0 (`dd_*`: side 2 holds, r1 withdraws at `e1`, r2 releases
  at `e2`): `dd_quiet` (QUIET: `e1 + A1 ≤ e2 + a2`, q never moves), `dd_excl` (sufficient,
  every behaviour, under H_DDLATE `B1 ≤ A1 + c5`), `dd_runt_cex` (a one-instant q runt,
  under H_NOFORCE `e1 + a1 ≤ e2 + A2` and H_LOOP_WIN), `dd_box_iff` (exact under H_DDLATE and
  H_NOFORCE), `dd_closed`; mirror `dd2_box_iff` (q0 = 1).
* The remaining single-step class, (r1 rises, r2 falls, q0 = 1) and its mirror, starts from an
  INCONSISTENT state (the cell is in reset with q = 1): NOT covered.

## Part 2: the gcd_hw instances (§ Instances, generated)

Rows from probe Bar's corrected extraction (`Bar/out/part_*.json`, UNTRUSTED front end),
36 arbiters x 7 rows: point corners FMIN, FMAX, SMIN, SMAX (integer hull of each read's
one-corner sum, H_ONE_CORNER), corner ranges FR = [FMIN, FMAX], SR = [SMIN, SMAX] and the
independent box BOX = [FMIN, SMAX] (each read anywhere in its range independently, H_INDEP).
Per read (H_R_SPLIT: the r_k net's shared prefix carries a clean step, so it cancels; the q
net's prefix `cq` is in every q read; arcs are the per-pin prjxray arcs):
  `a1 = rs1 + aq`, `a2 = rs2 + aq`, `l = cq + qs + aq`, `b1 = rg1 + ag1r`, `b2 = rg2 + ag2`,
  `c5 = cq + qgw + pqg + ag1q`, `c6 = cq + qgw + pqg + ag2`.
H_A0_LOW / H_RST_LOW: ustate's A0 (I4) and rst (I3) pins are 0 during the race (the
gcd_hw ustate INIT FFF0FFB2 is then `bd_c2n_set`'s FFB2 = `stF`): the bare cell race, no
A0 hold (the held handover is RT1/RT2's business, OnGcdArbFix / OnGcdArbA0).

General theorems used by the instances (κ conditions, every per-pin behaviour, no FIFO):
`h12_kappa` (`B1 ≤ a1 + c6`), `h21_kappa` (`B2 ≤ a2 + c5`), `o1_kappa` (all gaps:
`B2 ≤ a2 + c5 ∧ B2 ≤ a2 + c6 + 1`), `o2_kappa` (all gaps: `B1 ≤ a1 + c6 ∧ B1 ≤ a1 + c5 + 1`);
transport counter-traces when the κ fails with the q windows overlapping; `o1T_allgaps_iff`:
the opposite-sense race is transport-safe at EVERY gap iff the r2 -> r1 handover is
(`¬ (c5 < C6 ∧ a2 + c5 < B2)`), and `o1T_onset`: the exact first overlapping gap.
-/

namespace Formal.Cells.ArbPin2
open Formal.Cells
open Formal.Cells.ArbPin
open Formal.Cells.ArbBinary (stF gr1 gr2 stF_eq gr1_eq gr2_eq)
open Formal.Cells.LibGapSteer (Rd)

/-! ## 1. The side swap -/

/-- Exchange side 1 and side 2: ustate's r1/r2 pins, ugrant's r1 -> O5 / r2 -> O6 and
q -> O5 / q -> O6 windows. -/
def swapB (B : Box) : Box :=
  ⟨B.a2, B.A2, B.a1, B.A1, B.l, B.L, B.b2, B.B2, B.b1, B.B1, B.c6, B.C6, B.c5, B.C5⟩

theorem swapB_swapB (B : Box) : swapB (swapB B) = B := rfl

theorem swapB_ok {B : Box} (h : B.Ok) : (swapB B).Ok := by
  unfold Box.Ok at *; simp only [swapB]; omega

/-- ustate's INIT is symmetric under (r1, r2, q) -> (r2, r1, ~q). -/
theorem stF_swap (a b q : Bool) : stF b a (!q) = !(stF a b q) := by
  cases a <;> cases b <;> cases q <;> rfl

/-- ugrant: O5 of the swapped cell is O6 of the cell, and vice versa. -/
theorem gr1_swap (x y z : Bool) : gr1 y x (!z) = gr2 x y z := by
  cases x <;> cases y <;> cases z <;> rfl

theorem gr2_swap (x y z : Bool) : gr2 y x (!z) = gr1 x y z := by
  cases x <;> cases y <;> cases z <;> rfl

/-- **The swapped behaviour.** Every field is a field of `c`, permuted; q is complemented. -/
def cswap {B : Box} {q0 : Bool} {r1 r2 : Int → Bool} (c : Cell B q0 r1 r2) :
    Cell (swapB B) (!q0) r2 r1 where
  p1 := c.p2
  p2 := c.p1
  pq := c.pq
  u1 := c.u2
  x2 := c.x1
  v5 := c.v6
  x1 := c.x2
  u2 := c.u1
  v6 := c.v5
  q := fun t => !c.q t
  g1 := c.g2
  g2 := c.g1
  H_P1 := c.H_P2
  H_P2 := c.H_P1
  H_PQ := c.H_PQ
  H_U1 := c.H_U2
  H_U2 := c.H_U1
  H_V5 := c.H_V6
  H_V6 := c.H_V5
  H_PRE := fun t ht => by show (!c.q t) = !q0; rw [c.H_PRE t ht]
  H_ST := fun t ht => by
    show (!c.q t) = stF (r2 (c.p2.σ t)) (r1 (c.p1.σ t)) (!c.q (c.pq.σ t))
    rw [c.H_ST t ht, stF_swap]
  H_O5 := fun t => by
    show c.g2 t = gr1 (r2 (c.u2.σ t)) (r1 (c.x1.σ t)) (!c.q (c.v6.σ t))
    rw [c.H_O6 t, gr1_swap]
  H_O6 := fun t => by
    show c.g1 t = gr2 (r2 (c.x2.σ t)) (r1 (c.u1.σ t)) (!c.q (c.v5.σ t))
    rw [c.H_O5 t, gr2_swap]

theorem excl_cswap {B : Box} {q0 : Bool} {r1 r2 : Int → Bool} (c : Cell B q0 r1 r2) :
    Excl (cswap c) ↔ Excl c := by
  unfold Excl
  constructor
  · intro h t ⟨a, b⟩; exact h t ⟨b, a⟩
  · intro h t ⟨a, b⟩; exact h t ⟨b, a⟩

theorem transport_cswap {B : Box} {q0 : Bool} {r1 r2 : Int → Bool} (c : Cell B q0 r1 r2) :
    Transport (cswap c) ↔ Transport c := by
  unfold Transport
  constructor
  · rintro ⟨a, b, d, e, f, g, h⟩; exact ⟨b, a, d, f, e, h, g⟩
  · rintro ⟨a, b, d, e, f, g, h⟩; exact ⟨b, a, d, f, e, h, g⟩

/-- **Exclusion of every behaviour transfers across the swap** (both directions). -/
theorem all_excl_swap (B : Box) (q0 : Bool) (r1 r2 : Int → Bool) :
    (∀ c : Cell B q0 r1 r2, Excl c) ↔ (∀ c : Cell (swapB B) (!q0) r2 r1, Excl c) := by
  cases q0
  · constructor
    · intro h c; exact (excl_cswap c).mp (h (cswap c))
    · intro h c; exact (excl_cswap c).mp (h (cswap c))
  · constructor
    · intro h c; exact (excl_cswap c).mp (h (cswap c))
    · intro h c; exact (excl_cswap c).mp (h (cswap c))

theorem all_transport_swap (B : Box) (q0 : Bool) (r1 r2 : Int → Bool) :
    (∀ c : Cell B q0 r1 r2, Transport c → Excl c) ↔
    (∀ c : Cell (swapB B) (!q0) r2 r1, Transport c → Excl c) := by
  cases q0
  · constructor
    · intro h c hT; exact (excl_cswap c).mp (h (cswap c) ((transport_cswap c).mpr hT))
    · intro h c hT; exact (excl_cswap c).mp (h (cswap c) ((transport_cswap c).mpr hT))
  · constructor
    · intro h c hT; exact (excl_cswap c).mp (h (cswap c) ((transport_cswap c).mpr hT))
    · intro h c hT; exact (excl_cswap c).mp (h (cswap c) ((transport_cswap c).mpr hT))

/-- A counter-trace transfers too. -/
theorem cex_swap {B : Box} {q0 : Bool} {r1 r2 : Int → Bool}
    (h : ∃ c : Cell B q0 r1 r2, Transport c ∧ ¬ Excl c) :
    ∃ c : Cell (swapB B) (!q0) r2 r1, Transport c ∧ ¬ Excl c := by
  obtain ⟨c, hT, hn⟩ := h
  exact ⟨cswap c, (transport_cswap c).mpr hT, fun hx => hn ((excl_cswap c).mp hx)⟩

/-! ## 2. Closed forms of ArbPin's windows -/

section closed
variable {B : Box} {e1 e2 f : Int}

/-- **Per-pin handover window, closed form** (`H12Ov`: clean-fall OR dip-runt type). -/
theorem h12Ov_closed (hB : B.Ok) : H12Ov B f ↔
    ((B.c6 < B.C5 ∧ B.a1 + B.c6 < B.B1) ∨
     (B.c5 < B.C6 ∧ B.a1 + 2 ≤ B.A1 ∧
      B.a1 + B.c6 ≤ B.B1 - 1 ∧ B.a1 + 1 + B.c5 ≤ B.B1 - 1 ∧
      B.a1 + B.c6 ≤ B.A1 - 1 + B.C5 ∧ B.a1 + 1 + B.c5 ≤ B.A1 - 1 + B.C5 ∧
      B.a1 + B.c6 ≤ B.A1 - 2 + B.C6 ∧ B.a1 + 1 + B.c5 ≤ B.A1 - 2 + B.C6)) := by
  unfold Box.Ok at hB
  constructor
  · rintro ⟨t, h1, ⟨a, b, d⟩ | ⟨a, b, d, e, g, h⟩⟩
    · left; exact ⟨a, by omega⟩
    · right; exact ⟨a, by omega, by omega, by omega, by omega, by omega, by omega, by omega⟩
  · rintro (⟨a, b⟩ | ⟨a, b, h1, h2, h3, h4, h5, h6⟩)
    · exact ⟨f + B.a1 + B.c6, by omega, Or.inl ⟨a, by omega, by omega⟩⟩
    · exact ⟨f + max (B.a1 + B.c6) (B.a1 + 1 + B.c5), by omega,
        Or.inr ⟨a, by omega, by omega, by omega, by omega, by omega⟩⟩

/-- Transport opposite-sense window, closed form (pairwise bounds). -/
theorem o1OvT_closed : O1OvT B e1 e2 ↔
    (B.c5 < B.C6 ∧ e1 + B.b1 ≤ e2 + B.B2 - 1 ∧ e1 + B.b1 ≤ X1 B e1 e2 - 1 + B.C6 ∧
      X0 B e1 e2 + B.c5 ≤ e2 + B.B2 - 1 ∧ X0 B e1 e2 + B.c5 ≤ X1 B e1 e2 - 1 + B.C6) := by
  constructor
  · rintro ⟨t, h1, h2, a, b, d⟩; exact ⟨a, by omega, by omega, by omega, by omega⟩
  · rintro ⟨a, h1, h2, h3, h4⟩
    exact ⟨max (e1 + B.b1) (X0 B e1 e2 + B.c5), by omega, by omega, a, by omega, by omega⟩

/-- Fall-type (per-pin only) part of the opposite-sense window, closed form. -/
def O1FallC (B : Box) (e1 e2 : Int) : Prop :=
  B.c6 < B.C5 ∧ X0 B e1 e2 + 2 ≤ X1 B e1 e2 ∧
  e1 + B.b1 ≤ e2 + B.B2 - 1 ∧ e1 + B.b1 ≤ X1 B e1 e2 - 1 + B.C6 ∧
  e1 + B.b1 ≤ X1 B e1 e2 - 2 + B.C5 ∧
  X0 B e1 e2 + B.c5 ≤ e2 + B.B2 - 1 ∧ X0 B e1 e2 + B.c5 ≤ X1 B e1 e2 - 1 + B.C6 ∧
  X0 B e1 e2 + B.c5 ≤ X1 B e1 e2 - 2 + B.C5 ∧
  X0 B e1 e2 + 1 + B.c6 ≤ e2 + B.B2 - 1 ∧ X0 B e1 e2 + 1 + B.c6 ≤ X1 B e1 e2 - 1 + B.C6 ∧
  X0 B e1 e2 + 1 + B.c6 ≤ X1 B e1 e2 - 2 + B.C5

/-- **Per-pin opposite-sense window, closed form**: transport part or fall part. -/
theorem o1Ov_closed : O1Ov B e1 e2 ↔ (O1OvT B e1 e2 ∨ O1FallC B e1 e2) := by
  constructor
  · rintro ⟨t, h1, h2, ⟨a, b, d⟩ | ⟨a, b, d, e, g, h⟩⟩
    · exact Or.inl ⟨t, h1, h2, a, b, d⟩
    · right; exact ⟨a, b, by omega, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega, by omega⟩
  · rintro (⟨t, h1, h2, r⟩ | ⟨a, b, h1, h2, h3, h4, h5, h6, h7, h8, h9⟩)
    · exact ⟨t, h1, h2, Or.inl r⟩
    · refine ⟨max (max (e1 + B.b1) (X0 B e1 e2 + B.c5)) (X0 B e1 e2 + 1 + B.c6), by omega,
        by omega, Or.inr ⟨a, b, by omega, by omega, by omega, by omega⟩⟩

end closed

/-! ## 3. The mirrors, exact over the box -/

section mirror
variable {B : Box} {e1 e2 f : Int}

/-- **Same sense, both rise, q0 = 1 (side 1 won last), exact, EVERY per-pin behaviour.**
The mirror of `su_box_iff`: QUIET is `e1 + A1 ≤ e2 + a2` (r1 surely seen before r2 can
be), COMMIT is `e2 + A2 + L ≤ e1 + a1`, the late overlap is the mirrored `SuOvT`.
Hypotheses: H_LOOP2, and the mirrored H_QWIN (`c6 < C5 ∧ c5 ≤ C6 + 1`). -/
theorem sd_box_iff (hB : B.Ok) (H_LOOP2 : 2 ≤ B.L) (H_QWIN' : B.c6 < B.C5 ∧ B.c5 ≤ B.C6 + 1)
    (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) :
    (∀ c : Cell B true (up e1) (up e2), Excl c) ↔
    (e1 + B.A1 ≤ e2 + B.a2 ∨ (e2 + B.A2 + B.L ≤ e1 + B.a1 ∧
      ¬ (B.c6 < B.C5 ∧ max (e2 + B.b2) (e1 + B.b1) ≤ e2 + B.A2 - 1 + B.C5))) := by
  refine (all_excl_swap B true (up e1) (up e2)).trans ?_
  refine (su_box_iff (swapB_ok hB) H_LOOP2 H_QWIN' he2 he1).trans ?_
  rw [suOvT_closed (swapB_ok hB)]; exact Iff.rfl

/-- The same window for TRANSPORT behaviours. -/
theorem sd_transport_iff (hB : B.Ok) (H_LOOP2 : 2 ≤ B.L)
    (H_QWIN' : B.c6 < B.C5 ∧ B.c5 ≤ B.C6 + 1) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) :
    (∀ c : Cell B true (up e1) (up e2), Transport c → Excl c) ↔
    (e1 + B.A1 ≤ e2 + B.a2 ∨ (e2 + B.A2 + B.L ≤ e1 + B.a1 ∧
      ¬ (B.c6 < B.C5 ∧ max (e2 + B.b2) (e1 + B.b1) ≤ e2 + B.A2 - 1 + B.C5))) := by
  refine (all_transport_swap B true (up e1) (up e2)).trans ?_
  refine (su_transport_iff (swapB_ok hB) H_LOOP2 H_QWIN' he2 he1).trans ?_
  rw [suOvT_closed (swapB_ok hB)]; exact Iff.rfl

/-- **Opposite sense, r1 FALLS at `e1`, r2 RISES at `e2`, q0 = 1, exact, every per-pin
behaviour** (H_LOOP_WIN): exclusion iff no overlap instant of the mirrored window
(closed form: `o1Ov_closed` on `swapB B` with the gaps exchanged). -/
theorem o2_box_iff (hB : B.Ok) (H_LOOP_WIN : B.l < B.L) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) :
    (∀ c : Cell B true (dn e1) (up e2), Excl c) ↔ ¬ O1Ov (swapB B) e2 e1 :=
  (all_excl_swap B true (dn e1) (up e2)).trans (o1_box_iff (swapB_ok hB) H_LOOP_WIN he2 he1)

theorem o2_transport_iff (hB : B.Ok) (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) :
    (∀ c : Cell B true (dn e1) (up e2), Transport c → Excl c) ↔ ¬ O1OvT (swapB B) e2 e1 :=
  (all_transport_swap B true (dn e1) (up e2)).trans (o1_transport_iff (swapB_ok hB) he2 he1)

/-- **The r2 -> r1 handover, exact, every per-pin behaviour** (H_LOOP_WIN): r1 waiting
(high for ever), the holder r2 falls at `f`, q0 = 0. -/
theorem h21_box_iff (hB : B.Ok) (H_LOOP_WIN : B.l < B.L) (hf : 0 ≤ f) :
    (∀ c : Cell B false hi1 (dn f), Excl c) ↔ ¬ H12Ov (swapB B) f :=
  (all_excl_swap B false hi1 (dn f)).trans (h12_box_iff (swapB_ok hB) H_LOOP_WIN hf)

/-- The r2 -> r1 handover, transport, closed form: exclusion iff
`C6 ≤ c5 ∨ B2 ≤ a2 + c5` (the mirror of `h12OvT_closed`). -/
theorem h21_transport_iff (hB : B.Ok) (hf : 0 ≤ f) :
    (∀ c : Cell B false hi1 (dn f), Transport c → Excl c) ↔
    ¬ (B.c5 < B.C6 ∧ B.a2 + B.c5 < B.B2) := by
  refine (all_transport_swap B false hi1 (dn f)).trans ?_
  refine (h12_transport_iff (swapB_ok hB) hf).trans ?_
  rw [h12OvT_closed (swapB_ok hB)]; exact Iff.rfl

/-- `h21` per pin, closed form. -/
theorem h21Ov_closed (hB : B.Ok) : H12Ov (swapB B) f ↔
    ((B.c5 < B.C6 ∧ B.a2 + B.c5 < B.B2) ∨
     (B.c6 < B.C5 ∧ B.a2 + 2 ≤ B.A2 ∧
      B.a2 + B.c5 ≤ B.B2 - 1 ∧ B.a2 + 1 + B.c6 ≤ B.B2 - 1 ∧
      B.a2 + B.c5 ≤ B.A2 - 1 + B.C6 ∧ B.a2 + 1 + B.c6 ≤ B.A2 - 1 + B.C6 ∧
      B.a2 + B.c5 ≤ B.A2 - 2 + B.C5 ∧ B.a2 + 1 + B.c6 ≤ B.A2 - 2 + B.C5)) :=
  h12Ov_closed (swapB_ok hB)

end mirror

/-! ## 4. Both requests fall (q0 = 0: side 2 holds the grant, r1 is waiting)

r1 (waiting) withdraws at `e1`, the holder r2 releases at `e2`. The set condition
`r1.~r2` can be read at ustate only in `[e2 + a2, e1 + A1)`. -/

section dd
variable {B : Box} {e1 e2 : Int}

/-- Before r2's fall can be read at ustate, q stays 0 (any read maps). -/
theorem dd_before (hB : B.Ok) (c : Cell B false (dn e1) (dn e2)) :
    ∀ t, t < e2 + B.a2 → c.q t = false := by
  have hP2 := c.H_P2; have hPQ := c.H_PQ; unfold In at hP2 hPQ; unfold Box.Ok at hB
  refine int_ind _ (fun t ht _ => c.H_PRE t ht) ?_
  intro t ht ih hlt
  rw [c.H_ST t ht]
  have g2 := c.p2.le t; have g3 := c.pq.le t
  have hq : c.q (c.pq.σ t) = false := ih _ (by omega) (by omega)
  rw [hq, dn_t.mpr (show c.p2.σ t < e2 by omega), stF_val]; simp

/-- **QUIET**: if r1's withdrawal is surely seen before r2's release can be
(`e1 + A1 ≤ e2 + a2`), q never moves, in every behaviour. -/
theorem dd_quiet (hB : B.Ok) (H_QUIET : e1 + B.A1 ≤ e2 + B.a2) (c : Cell B false (dn e1) (dn e2)) :
    ∀ t, c.q t = false := by
  have hP1 := c.H_P1; have hP2 := c.H_P2; have hPQ := c.H_PQ
  unfold In at hP1 hP2 hPQ; unfold Box.Ok at hB
  refine int_ind _ (fun t ht => c.H_PRE t ht) ?_
  intro t ht ih
  rw [c.H_ST t ht]
  have g1 := c.p1.ge t; have g2 := c.p2.le t; have g3 := c.pq.le t
  have hq : c.q (c.pq.σ t) = false := ih _ (by omega)
  rw [hq, stF_val]
  by_cases h : t < e2 + B.a2
  · rw [dn_t.mpr (show c.p2.σ t < e2 by omega)]; simp
  · rw [dn_f.mpr (show e1 ≤ c.p1.σ t by omega)]; simp

theorem dd_quiet_excl (hB : B.Ok) (H_QUIET : e1 + B.A1 ≤ e2 + B.a2)
    (c : Cell B false (dn e1) (dn e2)) : Excl c := by
  intro t h
  have := ((ov_iff c t).mp h).2.2.1
  rw [dd_quiet hB H_QUIET c] at this; exact Bool.noConfusion this

/-- Overlap condition: an instant `t` where both grant request reads can be 1, and an
instant `x` of the set window that O5 can read, with an O6 read different from `x`. -/
def DDOv (B : Box) (e1 e2 : Int) : Prop :=
  ∃ t x, t < e1 + B.B1 ∧ t < e2 + B.B2 ∧ e2 + B.a2 ≤ x ∧ x < e1 + B.A1 ∧
    t - B.C5 ≤ x ∧ x ≤ t - B.c5 ∧ (B.c6 < B.C6 ∨ t - B.c6 ≠ x)

/-- **Sufficient, every per-pin behaviour**, under H_DDLATE (`B1 ≤ A1 + c5`: r1's fall
reaches O5 no later than the latest set read plus the fastest q -> O5 path). -/
theorem dd_excl (hB : B.Ok) (H_DDLATE : B.B1 ≤ B.A1 + B.c5) (hno : ¬ DDOv B e1 e2)
    (c : Cell B false (dn e1) (dn e2)) : Excl c := by
  intro t h
  obtain ⟨h1, h2, h5, h6⟩ := (ov_iff c t).mp h
  have hU1 := c.H_U1; have hU2 := c.H_U2; have hV5 := c.H_V5; have hV6 := c.H_V6
  unfold In at hU1 hU2 hV5 hV6; unfold Box.Ok at hB
  have := dn_t.mp h1; have := dn_t.mp h2
  have := c.u1.ge t; have := c.u2.ge t
  have := c.v5.ge t; have := c.v5.le t; have := c.v6.ge t; have := c.v6.le t
  have hx : e2 + B.a2 ≤ c.v5.σ t := by
    apply Classical.byContradiction; intro hn
    rw [dd_before hB c _ (by omega)] at h5; exact Bool.noConfusion h5
  refine hno ⟨t, c.v5.σ t, by omega, by omega, hx, by omega, by omega, by omega, ?_⟩
  by_cases hc : B.c6 < B.C6
  · exact Or.inl hc
  · right; intro heq
    have e : c.v6.σ t = c.v5.σ t := by omega
    rw [e, h5] at h6; exact Bool.noConfusion h6

/-- A pin that reads LATE (`A`) at the single instant `s`, early (`a`) elsewhere. -/
def lateAt (s a A : Int) (h : a ≤ A) : Rd :=
  mk (fun t => if t = s then t - A else t - a) a A
    (fun t => by show t - A ≤ (if t = s then t - A else t - a); split <;> omega)
    (fun t => by show (if t = s then t - A else t - a) ≤ t - a; split <;> omega)

/-- The one-instant runt trace. -/
def qI (x t : Int) : Bool := decide (t = x)

/-- **Necessity: the one-instant set runt (NON-monotone reads).** Under H_NOFORCE
(`e1 + a1 ≤ e2 + A2`: the set is never forced) and H_LOOP_WIN, for every overlap
instant of `DDOv`, a behaviour in which ustate sees the set `r1.~r2` at the single instant
`x` (r1's pin late, r2's early, everywhere else the reverse), q is 1 at `x` only (the loop
skips `x`), O5 reads that 1 and O6 a 0: both grants high. -/
theorem dd_runt_cex (hB : B.Ok) (H_LOOP_WIN : B.l < B.L) (H_NOFORCE : e1 + B.a1 ≤ e2 + B.A2)
    (he2 : 0 ≤ e2) (hov : DDOv B e1 e2) :
    ∃ c : Cell B false (dn e1) (dn e2), ¬ Excl c ∧ ∃ x, ∀ s, c.q s = true ↔ s = x := by
  unfold Box.Ok at hB
  obtain ⟨t, x, h1, h2, h3, h4, h5, h6, h7⟩ := hov
  have hA1 : B.a1 ≤ B.A1 := by omega
  have hA2 : B.a2 ≤ B.A2 := by omega
  obtain ⟨s6, hs6⟩ : ∃ s, s = if t - B.c6 = x then t - B.c6 - 1 else t - B.c6 := ⟨_, rfl⟩
  have hs6x : s6 ≠ x := by rw [hs6]; split <;> omega
  have hs6a : B.c6 ≤ t - s6 ∧ t - s6 ≤ B.C6 := by
    rw [hs6]; split
    · rcases h7 with h7 | h7
      · omega
      · omega
    · omega
  have qIt : ∀ u, qI x u = true ↔ u = x := by intro u; simp [qI]
  have qIf : ∀ u, qI x u = false ↔ u ≠ x := by intro u; simp [qI]
  have hst : ∀ u, 0 ≤ u → qI x u = stF (dn e1 ((lateAt x B.a1 B.A1 hA1).σ u))
      (dn e2 ((jumpMap x B.a2 B.A2 hA2).σ u)) (qI x ((skipMap x B.l B.L H_LOOP_WIN).σ u)) := by
    intro u _
    rw [stF_val]
    by_cases hu : u = x
    · rw [hu]
      have e1' : (lateAt x B.a1 B.A1 hA1).σ x = x - B.A1 := by
        show (if x = x then x - B.A1 else x - B.a1) = x - B.A1; simp
      rw [e1', jumpMap_s, dn_t.mpr (show x - B.A1 < e1 by omega),
        dn_f.mpr (show e2 ≤ x - B.a2 by omega), (qIt x).mpr rfl]; rfl
    · have e1' : (lateAt x B.a1 B.A1 hA1).σ u = u - B.a1 := by
        show (if u = x then u - B.A1 else u - B.a1) = u - B.a1; simp [hu]
      rw [e1', jumpMap_ne _ _ _ _ u hu, (qIf u).mpr hu,
        (qIf _).mpr (skipMap_ne x B.l B.L H_LOOP_WIN u)]
      by_cases h' : u < e1 + B.a1
      · rw [dn_t.mpr (show u - B.a1 < e1 by omega), dn_t.mpr (show u - B.A2 < e2 by omega)]; rfl
      · rw [dn_f.mpr (show e1 ≤ u - B.a1 by omega)]; simp
  refine ⟨mkCell B false (dn e1) (dn e2) (lateAt x B.a1 B.A1 hA1) (jumpMap x B.a2 B.A2 hA2)
    (skipMap x B.l B.L H_LOOP_WIN) (cst B.B1) (cst (t - x)) (cst B.B2) (cst (t - s6)) (qI x)
    ⟨Int.le_refl _, Int.le_refl _⟩ ⟨Int.le_refl _, Int.le_refl _⟩ ⟨Int.le_refl _, Int.le_refl _⟩
    (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega))
    (in_cst hs6a.1 hs6a.2) (fun u hu => (qIf u).mpr (by omega)) hst, ?_, x, qIt⟩
  exact mk_overlap t (dn_t.mpr (show t - B.B1 < e1 by omega)) (dn_t.mpr (show t - B.B2 < e2 by omega))
    ((qIt _).mpr (show t - (t - x) = x by omega)) ((qIf _).mpr (show t - (t - s6) ≠ x by omega))

/-- **Both fall, exact over the box, EVERY per-pin behaviour**, under H_DDLATE and
H_NOFORCE (and H_LOOP_WIN for the counter-trace). -/
theorem dd_box_iff (hB : B.Ok) (H_LOOP_WIN : B.l < B.L) (H_NOFORCE : e1 + B.a1 ≤ e2 + B.A2)
    (H_DDLATE : B.B1 ≤ B.A1 + B.c5) (he2 : 0 ≤ e2) :
    (∀ c : Cell B false (dn e1) (dn e2), Excl c) ↔ ¬ DDOv B e1 e2 := by
  constructor
  · intro h hov
    obtain ⟨c, hn, _⟩ := dd_runt_cex hB H_LOOP_WIN H_NOFORCE he2 hov; exact hn (h c)
  · intro hno c; exact dd_excl hB H_DDLATE hno c

/-- Closed form of `DDOv`: the set window is nonempty, and the earliest set instant plus the
fastest q -> O5 path comes before both grant-request reads can show the falls; the
degenerate case `c5 = c6 = C6` needs one more instant. Note `e2 + a2 + c5 < e2 + B2` is the
r2 -> r1 handover's κ inequality failing. -/
theorem dd_closed (hB : B.Ok) : DDOv B e1 e2 ↔
    (e2 + B.a2 < e1 + B.A1 ∧
      ((e2 + B.a2 + B.c5 < e1 + B.B1 ∧ B.a2 + B.c5 < B.B2 ∧ (B.c6 < B.C6 ∨ B.c5 ≠ B.c6)) ∨
       (e2 + B.a2 + B.c5 + 1 < e1 + B.B1 ∧ B.a2 + B.c5 + 1 < B.B2 ∧ B.c5 = B.c6 ∧
         B.c5 < B.C5))) := by
  unfold Box.Ok at hB
  constructor
  · rintro ⟨t, x, h1, h2, h3, h4, h5, h6, h7⟩
    refine ⟨by omega, ?_⟩
    by_cases hA : B.c6 < B.C6 ∨ B.c5 ≠ B.c6
    · exact Or.inl ⟨by omega, by omega, hA⟩
    · right
      have hc : B.c6 = B.C6 ∧ B.c5 = B.c6 := by omega
      rcases h7 with h7 | h7
      · omega
      · exact ⟨by omega, by omega, hc.2, by omega⟩
  · rintro ⟨h0, ⟨a, b, d⟩ | ⟨a, b, d, g⟩⟩
    · exact ⟨e2 + B.a2 + B.c5, e2 + B.a2, by omega, by omega, by omega, by omega, by omega,
        by omega, by omega⟩
    · exact ⟨e2 + B.a2 + B.c5 + 1, e2 + B.a2, by omega, by omega, by omega, by omega, by omega,
        by omega, Or.inr (by omega)⟩

/-- **Both fall, q0 = 1 (the mirror: side 1 holds, r2 waiting)**, exact under the mirrored
H_NOFORCE (`e2 + a2 ≤ e1 + A1`) and H_DDLATE (`B2 ≤ A2 + c6`). -/
theorem dd2_box_iff (hB : B.Ok) (H_LOOP_WIN : B.l < B.L) (H_NOFORCE' : e2 + B.a2 ≤ e1 + B.A1)
    (H_DDLATE' : B.B2 ≤ B.A2 + B.c6) (he1 : 0 ≤ e1) :
    (∀ c : Cell B true (dn e1) (dn e2), Excl c) ↔ ¬ DDOv (swapB B) e2 e1 :=
  (all_excl_swap B true (dn e1) (dn e2)).trans
    (dd_box_iff (swapB_ok hB) H_LOOP_WIN H_NOFORCE' H_DDLATE' he1)

end dd

/-! ## 5. κ conditions over all request gaps (sufficient, every per-pin behaviour) -/

section kappa
variable {B : Box}

/-- **r1 -> r2 handover, κ form, no FIFO**: `B1 ≤ a1 + c6` (r1's fall reaches O5 no later
than the earliest r1 read at ustate plus the fastest q -> O6 path) gives exclusion for every
per-pin behaviour, whatever the q -> O5 / O6 ordering. -/
theorem h12_kappa (hB : B.Ok) (hk : B.B1 ≤ B.a1 + B.c6) {f : Int} (hf : 0 ≤ f) :
    ∀ c : Cell B true (dn f) hi1, Excl c :=
  fun c => h12_excl hB hf (by rw [h12Ov_closed hB]; omega) c

/-- **r2 -> r1 handover, κ form**: `B2 ≤ a2 + c5`. -/
theorem h21_kappa (hB : B.Ok) (hk : B.B2 ≤ B.a2 + B.c5) {f : Int} (hf : 0 ≤ f) :
    ∀ c : Cell B false hi1 (dn f), Excl c :=
  (all_excl_swap B false hi1 (dn f)).mpr (h12_kappa (B := swapB B) (swapB_ok hB) hk hf)

/-- **Opposite sense (r1 rises, r2 falls, q0 = 0) at EVERY gap, κ form, no FIFO**:
`B2 ≤ a2 + c5` (rise type) and `B2 ≤ a2 + c6 + 1` (fall type). -/
theorem o1_kappa (hB : B.Ok) (hk5 : B.B2 ≤ B.a2 + B.c5) (hk6 : B.B2 ≤ B.a2 + B.c6 + 1)
    {e1 e2 : Int} (he1 : 0 ≤ e1) : ∀ c : Cell B false (up e1) (dn e2), Excl c := by
  intro c
  have k5 := hk5; have k6 := hk6
  refine o1_excl hB he1 ?_ c
  rintro ⟨t, h1, h2, ⟨_, a, _⟩ | ⟨_, _, a, b, _⟩⟩ <;> unfold X0 at * <;> omega

/-- **Opposite sense mirrored (r1 falls, r2 rises, q0 = 1) at every gap**:
`B1 ≤ a1 + c6` and `B1 ≤ a1 + c5 + 1`. -/
theorem o2_kappa (hB : B.Ok) (hk6 : B.B1 ≤ B.a1 + B.c6) (hk5 : B.B1 ≤ B.a1 + B.c5 + 1)
    {e1 e2 : Int} (he2 : 0 ≤ e2) : ∀ c : Cell B true (dn e1) (up e2), Excl c :=
  (all_excl_swap B true (dn e1) (up e2)).mpr (o1_kappa (B := swapB B) (swapB_ok hB) hk6 hk5 he2)

/-- Transport counter-trace for the r1 -> r2 handover when the κ fails and the q -> O6 window
can be faster than q -> O5's. -/
theorem h12_kfail (hB : B.Ok) (hc : B.c6 < B.C5) (hk : B.a1 + B.c6 < B.B1) {f : Int}
    (hf : 0 ≤ f) : ∃ c : Cell B true (dn f) hi1, Transport c ∧ ¬ Excl c :=
  h12_down_cex hB hf ((h12OvT_closed hB).mpr ⟨hc, hk⟩)

theorem h21_kfail (hB : B.Ok) (hc : B.c5 < B.C6) (hk : B.a2 + B.c5 < B.B2) {f : Int}
    (hf : 0 ≤ f) : ∃ c : Cell B false hi1 (dn f), Transport c ∧ ¬ Excl c :=
  cex_swap (h12_kfail (B := swapB B) (swapB_ok hB) hc hk hf)

/-- **Opposite sense, transport, exact over ALL gaps**: every transport behaviour at every
gap is exclusive iff the r2 -> r1 handover is transport-safe (`¬ (c5 < C6 ∧ a2 + c5 < B2)`).
A large gap IS the handover (r1 has been waiting). -/
theorem o1T_allgaps_iff (hB : B.Ok) :
    (∀ e1 e2 : Int, 0 ≤ e1 → 0 ≤ e2 → ∀ c : Cell B false (up e1) (dn e2), Transport c → Excl c) ↔
    ¬ (B.c5 < B.C6 ∧ B.a2 + B.c5 < B.B2) := by
  have hB' := hB; unfold Box.Ok at hB'
  constructor
  · rintro h ⟨a, b⟩
    obtain ⟨G, hG⟩ : ∃ G, G = B.b1 + B.a1 + B.A1 + B.c5 := ⟨_, rfl⟩
    have hov : O1OvT B 0 G := ⟨G + B.a2 + B.c5, by omega, by omega, a,
      by unfold X0; omega, by unfold X1; omega⟩
    obtain ⟨c, hT, hn⟩ := o1_rise_cex hB (by omega) hov
    exact hn (h 0 G (by omega) (by omega) c hT)
  · intro hn e1 e2 he1 _ c hT
    refine o1_transport_excl hB he1 ?_ c hT
    rintro ⟨t, h1, h2, a, b, d⟩; unfold X0 at b; omega

/-- **Opposite sense, transport, exact onset**: when the κ fails (and `b1 ≤ A1 - 1 + C6`,
true on every routed row), the gaps with an overlapping transport behaviour are exactly `e2 - e1 ≥ G` with
`G = max (b1 - B2 + 1) (a1 + c5 - B2 + 1)`. -/
theorem o1T_onset (hB : B.Ok) (hc : B.c5 < B.C6) (hk : B.a2 + B.c5 < B.B2)
    (hb : B.b1 ≤ B.A1 - 1 + B.C6) {e1 e2 : Int} :
    O1OvT B e1 e2 ↔ max (B.b1 - B.B2 + 1) (B.a1 + B.c5 - B.B2 + 1) ≤ e2 - e1 := by
  unfold Box.Ok at hB
  rw [o1OvT_closed]; unfold X0 X1
  constructor
  · rintro ⟨_, h1, _, h3, _⟩; omega
  · intro h; exact ⟨hc, by omega, by omega, by omega, by omega⟩

/-- The same at the exact onset, as a transport behaviour: for every gap `≥ G` there is an
overlapping transport behaviour, for every gap `< G` none. -/
theorem o1T_gap_iff (hB : B.Ok) (hc : B.c5 < B.C6) (hk : B.a2 + B.c5 < B.B2)
    (hb : B.b1 ≤ B.A1 - 1 + B.C6) {e1 e2 : Int} (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) :
    (∃ c : Cell B false (up e1) (dn e2), Transport c ∧ ¬ Excl c) ↔
    max (B.b1 - B.B2 + 1) (B.a1 + B.c5 - B.B2 + 1) ≤ e2 - e1 := by
  rw [← o1T_onset hB hc hk hb]
  constructor
  · rintro ⟨c, hT, hn⟩
    apply Classical.byContradiction; intro hno
    exact hn (o1_transport_excl hB he1 hno c hT)
  · intro h; exact o1_rise_cex hB he2 h

/-- Mirror: r1 falls, r2 rises (q0 = 1), transport, exact over all gaps. -/
theorem o2T_allgaps_iff (hB : B.Ok) :
    (∀ e1 e2 : Int, 0 ≤ e1 → 0 ≤ e2 → ∀ c : Cell B true (dn e1) (up e2), Transport c → Excl c) ↔
    ¬ (B.c6 < B.C5 ∧ B.a1 + B.c6 < B.B1) := by
  refine Iff.trans ?_ (o1T_allgaps_iff (B := swapB B) (swapB_ok hB))
  constructor
  · intro h e1 e2 he1 he2
    exact (all_transport_swap B true (dn e2) (up e1)).mp (h e2 e1 he2 he1)
  · intro h e1 e2 he1 he2
    exact (all_transport_swap B true (dn e1) (up e2)).mpr (h e2 e1 he2 he1)

/-- Mirror onset: gaps with an overlapping transport behaviour for (r1 falls at `e1`, r2 rises at `e2`, q0 = 1) are
exactly `e1 - e2 ≥ max (b2 - B1 + 1) (a2 + c6 - B1 + 1)`. -/
theorem o2T_gap_iff (hB : B.Ok) (hc : B.c6 < B.C5) (hk : B.a1 + B.c6 < B.B1)
    (hb : B.b2 ≤ B.A2 - 1 + B.C5) {e1 e2 : Int} (he1 : 0 ≤ e1) (he2 : 0 ≤ e2) :
    (∃ c : Cell B true (dn e1) (up e2), Transport c ∧ ¬ Excl c) ↔
    max (B.b2 - B.B1 + 1) (B.a2 + B.c6 - B.B1 + 1) ≤ e1 - e2 := by
  refine Iff.trans ?_ (o1T_gap_iff (B := swapB B) (swapB_ok hB) hc hk hb he2 he1)
  constructor
  · rintro ⟨c, hT, hn⟩
    exact ⟨cswap c, (transport_cswap c).mpr hT, fun hx => hn ((excl_cswap c).mp hx)⟩
  · rintro ⟨c, hT, hn⟩
    exact ⟨cswap c, (transport_cswap c).mpr hT, fun hx => hn ((excl_cswap c).mp hx)⟩

end kappa

/-! ## 6. Non-vacuity and the mirrored finding -/

/-- Mirror of `su_nonvacuous` (q0 = 1, r2 at 100, r1 at 200: r2 commits): every behaviour of
`boxS` is exclusive, and one grants side 2. -/
theorem sd_nonvacuous :
    (∀ c : Cell boxS true (up 200) (up 100), Excl c) ∧
    ∃ c : Cell boxS true (up 200) (up 100), c.g2 200 = true ∧ c.g1 200 = false := by
  obtain ⟨_, _, _, _, _, hall, c, h1, h2⟩ := su_nonvacuous
  refine ⟨(all_excl_swap boxS true (up 200) (up 100)).mpr hall, cswap c, h1, h2⟩

/-- **The mirrored finding** (`h12_differs` swapped): a box with q -> O6 faster than q -> O5
for the r2 -> r1 handover; every transport behaviour is exclusive, a per-pin one overlaps. -/
theorem h21_differs :
    (swapB boxH).Ok ∧ (∀ c : Cell (swapB boxH) false hi1 (dn 100), Transport c → Excl c) ∧
    ∃ c : Cell (swapB boxH) false hi1 (dn 100), ¬ Excl c := by
  obtain ⟨hok, hT, c, hn⟩ := h12_differs
  refine ⟨swapB_ok hok, (all_transport_swap boxH true (dn 100) hi1).mp hT, cswap c,
    fun hx => hn ((excl_cswap c).mp hx)⟩

/-- Both-fall boxes. `boxDS`: the r2 -> r1 κ holds (`a2 + c5 ≥ B2`); `boxDU`: it fails. -/
def boxDS : Box := ⟨10, 20, 10, 20, 1, 3, 5, 15, 5, 15, 30, 40, 30, 40⟩
def boxDU : Box := ⟨10, 20, 10, 20, 1, 3, 30, 40, 50, 60, 20, 30, 20, 30⟩

/-- **Non-vacuity of `dd_excl`** (holder r2 releases at 95, waiting r1 withdraws at 100: not
QUIET, H_NOFORCE and H_DDLATE hold): every per-pin behaviour is exclusive, and a transport
behaviour exists in which q DOES move (r1 is handed the state before it withdraws). -/
theorem dd_nonvacuous :
    boxDS.Ok ∧ ¬ (100 + boxDS.A1 ≤ 95 + boxDS.a2) ∧ 100 + boxDS.a1 ≤ 95 + boxDS.A2 ∧
    boxDS.B1 ≤ boxDS.A1 + boxDS.c5 ∧ ¬ DDOv boxDS 100 95 ∧
    (∀ c : Cell boxDS false (dn 100) (dn 95), Excl c) ∧
    ∃ c : Cell boxDS false (dn 100) (dn 95), Transport c ∧ c.q 110 = true := by
  have hok : boxDS.Ok := by simp only [Box.Ok, boxDS]; omega
  have hno : ¬ DDOv boxDS 100 95 := by rw [dd_closed hok]; simp only [boxDS]; omega
  refine ⟨hok, by simp only [boxDS]; omega, by simp only [boxDS]; omega,
    by simp only [boxDS]; omega, hno, fun c => dd_excl hok (by simp only [boxDS]; omega) hno c, ?_⟩
  have hst : ∀ s, 0 ≤ s → up 105 s = stF (dn 100 (s - 20)) (dn 95 (s - 10)) (up 105 (s - 3)) := by
    intro s _
    rw [stF_val]
    by_cases h : s < 105
    · rw [up_f.mpr h, up_f.mpr (show s - 3 < 105 by omega), dn_t.mpr (show s - 10 < 95 by omega)]
      simp
    · rw [up_t.mpr (show 105 ≤ s by omega), dn_f.mpr (show 95 ≤ s - 10 by omega)]
      by_cases h2 : s < 120
      · rw [dn_t.mpr (show s - 20 < 100 by omega)]; rfl
      · rw [dn_f.mpr (show 100 ≤ s - 20 by omega), up_t.mpr (show 105 ≤ s - 3 by omega)]; rfl
  exact ⟨mkCell boxDS false (dn 100) (dn 95) (cst 20) (cst 10) (cst 3) (cst 5) (cst 30) (cst 5)
    (cst 30) (up 105) (in_cst (by decide) (by decide)) (in_cst (by decide) (by decide))
    (in_cst (by decide) (by decide)) (in_cst (by decide) (by decide)) (in_cst (by decide) (by decide))
    (in_cst (by decide) (by decide)) (in_cst (by decide) (by decide))
    (fun s hs => up_f.mpr (by omega)) hst, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩,
    up_t.mpr (by omega)⟩

/-- **Non-vacuity of `dd_runt_cex`**: in `boxDU` (same requests) a per-pin behaviour with a
one-instant q runt overlaps; H_NOFORCE, H_DDLATE, H_LOOP_WIN hold. -/
theorem dd_instance :
    boxDU.Ok ∧ 100 + boxDU.a1 ≤ 95 + boxDU.A2 ∧ boxDU.B1 ≤ boxDU.A1 + boxDU.c5 ∧
    ∃ c : Cell boxDU false (dn 100) (dn 95), ¬ Excl c := by
  have hok : boxDU.Ok := by simp only [Box.Ok, boxDU]; omega
  have hov : DDOv boxDU 100 95 := by rw [dd_closed hok]; simp only [boxDU]; omega
  obtain ⟨c, hn, _⟩ := dd_runt_cex hok (by simp only [boxDU]; omega)
    (by simp only [boxDU]; omega) (by omega) hov
  exact ⟨hok, by simp only [boxDU]; omega, by simp only [boxDU]; omega, c, hn⟩

/-- Non-vacuity of the κ theorems: a behaviour exists in each scenario (any box). -/
theorem h12_exists {B : Box} (hB : B.Ok) {f : Int} (hf : 0 ≤ f) : ∃ c : Cell B true (dn f) hi1, Transport c := by
  unfold Box.Ok at hB
  have hst : ∀ s, 0 ≤ s → dn (f + B.a1) s = stF (dn f (s - B.a1)) (hi1 (s - B.a2))
      (dn (f + B.a1) (s - B.L)) := by
    intro s _
    rw [stF_val]; simp only [hi1]
    by_cases h : s < f + B.a1
    · rw [dn_t.mpr h, dn_t.mpr (show s - B.a1 < f by omega), dn_t.mpr (show s - B.L < f + B.a1 by omega)]; rfl
    · rw [dn_f.mpr (show f + B.a1 ≤ s by omega), dn_f.mpr (show f ≤ s - B.a1 by omega)]; simp
  exact ⟨mkCell B true (dn f) hi1 (cst B.a1) (cst B.a2) (cst B.L) (cst B.b1) (cst B.c5) (cst B.b2)
    (cst B.c6) (dn (f + B.a1)) (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega))
    (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega))
    (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega))
    (fun s hs => dn_t.mpr (by omega)) hst, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

theorem o1_exists {B : Box} (hB : B.Ok) {e1 e2 : Int} (he1 : 0 ≤ e1) :
    ∃ c : Cell B false (up e1) (dn e2), Transport c := by
  unfold Box.Ok at hB
  obtain ⟨x, hx⟩ : ∃ x, x = max (e1 + B.a1) (e2 + B.a2) := ⟨_, rfl⟩
  have hst : ∀ s, 0 ≤ s → up x s = stF (up e1 (s - B.a1)) (dn e2 (s - B.a2)) (up x (s - B.L)) := by
    intro s _
    rw [stF_val]
    by_cases h : s < x
    · rw [up_f.mpr h, up_f.mpr (show s - B.L < x by omega)]
      by_cases h' : s < e1 + B.a1
      · rw [up_f.mpr (show s - B.a1 < e1 by omega)]; rfl
      · rw [dn_t.mpr (show s - B.a2 < e2 by omega)]; simp
    · rw [up_t.mpr (show x ≤ s by omega), up_t.mpr (show e1 ≤ s - B.a1 by omega),
        dn_f.mpr (show e2 ≤ s - B.a2 by omega)]; rfl
  exact ⟨mkCell B false (up e1) (dn e2) (cst B.a1) (cst B.a2) (cst B.L) (cst B.b1) (cst B.c5)
    (cst B.b2) (cst B.c6) (up x) (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega))
    (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega))
    (in_cst (by omega) (by omega)) (in_cst (by omega) (by omega))
    (fun s hs => up_f.mpr (by omega)) hst, ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩⟩

/-! ## 7. Instances: the 36 routed gcd_hw arbiters (generated by scratchpad `Barp2/gen.py`)

Arbiter index `id` (seed_instance):
`0` 2_merge10_uarb1,
`1` 2_merge11_uarb1,
`2` 2_merge12_uarb1,
`3` 2_merge12_uarb2,
`4` 2_merge2_uarb1,
`5` 2_merge3_uarb1,
`6` 2_merge4_uarb1,
`7` 2_merge6_uarb1,
`8` 2_merge9_uarb1,
`9` 3_merge10_uarb1,
`10` 3_merge11_uarb1,
`11` 3_merge12_uarb1,
`12` 3_merge12_uarb2,
`13` 3_merge2_uarb1,
`14` 3_merge3_uarb1,
`15` 3_merge4_uarb1,
`16` 3_merge6_uarb1,
`17` 3_merge9_uarb1,
`18` 4_merge10_uarb1,
`19` 4_merge11_uarb1,
`20` 4_merge12_uarb1,
`21` 4_merge12_uarb2,
`22` 4_merge2_uarb1,
`23` 4_merge3_uarb1,
`24` 4_merge4_uarb1,
`25` 4_merge6_uarb1,
`26` 4_merge9_uarb1,
`27` d_merge10_uarb1,
`28` d_merge11_uarb1,
`29` d_merge12_uarb1,
`30` d_merge12_uarb2,
`31` d_merge2_uarb1,
`32` d_merge3_uarb1,
`33` d_merge4_uarb1,
`34` d_merge6_uarb1,
`35` d_merge9_uarb1.

Corner tag `cor`: 0 FMIN, 1 FMAX, 2 SMIN, 3 SMAX (point rows), 4 FR = [FMIN, FMAX],
5 SR = [SMIN, SMAX], 6 BOX = [FMIN, SMAX]. Box fields in `Box` order
(a1 A1 a2 A2 l L b1 B1 b2 B2 c5 C5 c6 C6), Int ps. Verdicts `v12 v21 vo1 vo2`: `true` =
the κ condition holds (safe for EVERY per-pin behaviour, no FIFO), `false` = a transport
(FIFO) behaviour overlaps. -/

/-- One routed row. -/
structure Row where
  id : Nat
  cor : Nat
  B : Box
  v12 : Bool
  v21 : Bool
  vo1 : Bool
  vo2 : Bool

instance (B : Box) : Decidable B.Ok := by unfold Box.Ok; infer_instance

/-- κ margins (ps): ≥ 0 is safe without FIFO. -/
def k12 (B : Box) : Int := B.a1 + B.c6 - B.B1
def k21 (B : Box) : Int := B.a2 + B.c5 - B.B2
def kO1 (B : Box) : Int := min (B.a2 + B.c5 - B.B2) (B.a2 + B.c6 + 1 - B.B2)
def kO2 (B : Box) : Int := min (B.a1 + B.c6 - B.B1) (B.a1 + B.c5 + 1 - B.B1)
/-- Transport onset gaps (`o1T_gap_iff`, `o2T_gap_iff`). -/
def onO1 (B : Box) : Int := max (B.b1 - B.B2 + 1) (B.a1 + B.c5 - B.B2 + 1)
def onO2 (B : Box) : Int := max (B.b2 - B.B1 + 1) (B.a2 + B.c6 - B.B1 + 1)

def safe12 (B : Box) : Bool := decide (B.B1 ≤ B.a1 + B.c6)
def bad12 (B : Box) : Bool := decide (B.c6 < B.C5 ∧ B.a1 + B.c6 < B.B1)
def safe21 (B : Box) : Bool := decide (B.B2 ≤ B.a2 + B.c5)
def bad21 (B : Box) : Bool := decide (B.c5 < B.C6 ∧ B.a2 + B.c5 < B.B2)
def safeO1 (B : Box) : Bool := decide (B.B2 ≤ B.a2 + B.c5 ∧ B.B2 ≤ B.a2 + B.c6 + 1)
def badO1 (B : Box) : Bool := decide (B.c5 < B.C6 ∧ B.a2 + B.c5 < B.B2 ∧ B.b1 ≤ B.A1 - 1 + B.C6)
def safeO2 (B : Box) : Bool := decide (B.B1 ≤ B.a1 + B.c6 ∧ B.B1 ≤ B.a1 + B.c5 + 1)
def badO2 (B : Box) : Bool := decide (B.c6 < B.C5 ∧ B.a1 + B.c6 < B.B1 ∧ B.b2 ≤ B.A2 - 1 + B.C5)

/-- `v` selects which of the two checks must hold. -/
def pick (v s b : Bool) : Bool := (!v || s) && (v || b)

theorem pick_sound {v s b : Bool} (h : pick v s b = true) :
    (v = true → s = true) ∧ (v = false → b = true) := by
  unfold pick at h; cases v <;> cases s <;> cases b <;> simp_all

def rowOk (r : Row) : Bool :=
  decide r.B.Ok && pick r.v12 (safe12 r.B) (bad12 r.B) && pick r.v21 (safe21 r.B) (bad21 r.B) &&
    pick r.vo1 (safeO1 r.B) (badO1 r.B) && pick r.vo2 (safeO2 r.B) (badO2 r.B)

/-- **What a checked row means** (every theorem of §3-5, instantiated). -/
theorem rowOk_sound (r : Row) (h : rowOk r = true) :
    r.B.Ok ∧
    (∀ f : Int, 0 ≤ f →
      (r.v12 = true → ∀ c : Cell r.B true (dn f) hi1, Excl c) ∧
      (r.v12 = false → ∃ c : Cell r.B true (dn f) hi1, Transport c ∧ ¬ Excl c)) ∧
    (∀ f : Int, 0 ≤ f →
      (r.v21 = true → ∀ c : Cell r.B false hi1 (dn f), Excl c) ∧
      (r.v21 = false → ∃ c : Cell r.B false hi1 (dn f), Transport c ∧ ¬ Excl c)) ∧
    (∀ e1 e2 : Int, 0 ≤ e1 → 0 ≤ e2 →
      (r.vo1 = true → ∀ c : Cell r.B false (up e1) (dn e2), Excl c) ∧
      (r.vo1 = false → ((∃ c : Cell r.B false (up e1) (dn e2), Transport c ∧ ¬ Excl c) ↔
        onO1 r.B ≤ e2 - e1))) ∧
    (∀ e1 e2 : Int, 0 ≤ e1 → 0 ≤ e2 →
      (r.vo2 = true → ∀ c : Cell r.B true (dn e1) (up e2), Excl c) ∧
      (r.vo2 = false → ((∃ c : Cell r.B true (dn e1) (up e2), Transport c ∧ ¬ Excl c) ↔
        onO2 r.B ≤ e1 - e2))) := by
  unfold rowOk at h
  simp only [Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hok, p12⟩, p21⟩, po1⟩, po2⟩ := h
  have hB : r.B.Ok := of_decide_eq_true hok
  obtain ⟨s12, b12⟩ := pick_sound p12
  obtain ⟨s21, b21⟩ := pick_sound p21
  obtain ⟨so1, bo1⟩ := pick_sound po1
  obtain ⟨so2, bo2⟩ := pick_sound po2
  refine ⟨hB, fun f hf => ⟨fun hv => ?_, fun hv => ?_⟩, fun f hf => ⟨fun hv => ?_, fun hv => ?_⟩,
    fun e1 e2 he1 he2 => ⟨fun hv => ?_, fun hv => ?_⟩,
    fun e1 e2 he1 he2 => ⟨fun hv => ?_, fun hv => ?_⟩⟩
  · exact h12_kappa hB (of_decide_eq_true (s12 hv)) hf
  · obtain ⟨a, b⟩ := of_decide_eq_true (b12 hv); exact h12_kfail hB a b hf
  · exact h21_kappa hB (of_decide_eq_true (s21 hv)) hf
  · obtain ⟨a, b⟩ := of_decide_eq_true (b21 hv); exact h21_kfail hB a b hf
  · obtain ⟨a, b⟩ := of_decide_eq_true (so1 hv); exact o1_kappa hB a b he1
  · obtain ⟨a, b, d⟩ := of_decide_eq_true (bo1 hv); exact o1T_gap_iff hB a b d he1 he2
  · obtain ⟨a, b⟩ := of_decide_eq_true (so2 hv); exact o2_kappa hB a b he2
  · obtain ⟨a, b, d⟩ := of_decide_eq_true (bo2 hv); exact o2T_gap_iff hB a b d he1 he2

set_option maxRecDepth 100000

/-- All 252 rows (36 arbiters x 7). -/
def rows : List Row := [
  ⟨0, 0, ⟨291, 292, 286, 287, 136, 137, 431, 432, 190, 190, 334, 335, 335, 336⟩, true, true, true, true⟩,
  ⟨0, 1, ⟨374, 375, 395, 396, 177, 178, 522, 523, 236, 236, 405, 406, 405, 406⟩, true, true, true, true⟩,
  ⟨0, 2, ⟨658, 659, 657, 658, 308, 309, 980, 981, 492, 492, 810, 811, 790, 791⟩, true, true, true, true⟩,
  ⟨0, 3, ⟨891, 892, 964, 965, 421, 422, 1199, 1200, 606, 606, 992, 993, 962, 963⟩, true, true, true, true⟩,
  ⟨0, 4, ⟨291, 375, 286, 396, 136, 178, 431, 523, 190, 236, 334, 406, 335, 406⟩, true, true, true, true⟩,
  ⟨0, 5, ⟨658, 892, 657, 965, 308, 422, 980, 1200, 492, 606, 810, 993, 790, 963⟩, true, true, true, true⟩,
  ⟨0, 6, ⟨291, 892, 286, 965, 136, 422, 431, 1200, 190, 606, 334, 993, 335, 963⟩, false, true, true, false⟩,
  ⟨1, 0, ⟨779, 780, 548, 549, 392, 393, 314, 315, 321, 322, 514, 515, 511, 512⟩, true, true, true, true⟩,
  ⟨1, 1, ⟨915, 916, 636, 637, 469, 470, 384, 385, 394, 395, 589, 590, 584, 585⟩, true, true, true, true⟩,
  ⟨1, 2, ⟨1614, 1615, 1155, 1156, 895, 896, 816, 817, 769, 770, 1000, 1001, 1007, 1008⟩, true, true, true, true⟩,
  ⟨1, 3, ⟨1930, 1931, 1370, 1371, 1084, 1085, 1000, 1001, 941, 942, 1178, 1179, 1183, 1184⟩, true, true, true, true⟩,
  ⟨1, 4, ⟨779, 916, 548, 637, 392, 470, 314, 385, 321, 395, 514, 590, 511, 585⟩, true, true, true, true⟩,
  ⟨1, 5, ⟨1614, 1931, 1155, 1371, 895, 1085, 816, 1001, 769, 942, 1000, 1179, 1007, 1184⟩, true, true, true, true⟩,
  ⟨1, 6, ⟨779, 1931, 548, 1371, 392, 1085, 314, 1001, 321, 942, 514, 1179, 511, 1184⟩, true, true, true, true⟩,
  ⟨2, 0, ⟨223, 224, 343, 344, 327, 328, 254, 255, 366, 367, 208, 209, 205, 206⟩, true, true, true, true⟩,
  ⟨2, 1, ⟨274, 275, 421, 422, 398, 399, 317, 318, 448, 449, 250, 251, 243, 244⟩, true, true, true, true⟩,
  ⟨2, 2, ⟨560, 561, 858, 859, 767, 768, 646, 647, 867, 868, 452, 453, 458, 459⟩, true, true, true, true⟩,
  ⟨2, 3, ⟨685, 686, 1048, 1049, 939, 940, 801, 802, 1062, 1063, 548, 549, 552, 553⟩, true, true, true, true⟩,
  ⟨2, 4, ⟨223, 275, 343, 422, 327, 399, 254, 318, 366, 449, 208, 251, 205, 244⟩, true, true, true, true⟩,
  ⟨2, 5, ⟨560, 686, 858, 1049, 767, 940, 646, 802, 867, 1063, 452, 549, 458, 553⟩, true, true, true, true⟩,
  ⟨2, 6, ⟨223, 686, 343, 1049, 327, 940, 254, 802, 366, 1063, 208, 549, 205, 553⟩, false, false, false, false⟩,
  ⟨3, 0, ⟨263, 263, 249, 250, 143, 144, 126, 126, 309, 310, 280, 281, 281, 282⟩, true, true, true, true⟩,
  ⟨3, 1, ⟨328, 328, 305, 306, 173, 174, 158, 158, 381, 382, 346, 347, 344, 345⟩, true, true, true, true⟩,
  ⟨3, 2, ⟨642, 642, 629, 630, 338, 339, 314, 314, 738, 739, 677, 678, 656, 657⟩, true, true, true, true⟩,
  ⟨3, 3, ⟨793, 793, 772, 773, 410, 411, 390, 390, 907, 908, 837, 838, 805, 806⟩, true, true, true, true⟩,
  ⟨3, 4, ⟨263, 328, 249, 306, 143, 174, 126, 158, 309, 382, 280, 347, 281, 345⟩, true, true, true, true⟩,
  ⟨3, 5, ⟨642, 793, 629, 773, 338, 411, 314, 390, 738, 908, 677, 838, 656, 806⟩, true, true, true, true⟩,
  ⟨3, 6, ⟨263, 793, 249, 773, 143, 411, 126, 390, 309, 908, 280, 838, 281, 806⟩, true, false, false, true⟩,
  ⟨4, 0, ⟨234, 235, 352, 353, 144, 145, 314, 315, 227, 228, 200, 201, 197, 198⟩, true, true, true, true⟩,
  ⟨4, 1, ⟨286, 287, 426, 427, 174, 175, 392, 393, 274, 275, 242, 243, 237, 238⟩, true, true, true, true⟩,
  ⟨4, 2, ⟨616, 617, 829, 830, 339, 340, 779, 780, 544, 545, 449, 450, 456, 457⟩, true, true, true, true⟩,
  ⟨4, 3, ⟨754, 755, 1045, 1046, 411, 412, 964, 965, 664, 665, 546, 547, 551, 552⟩, true, true, true, true⟩,
  ⟨4, 4, ⟨234, 287, 352, 427, 144, 175, 314, 393, 227, 275, 200, 243, 197, 238⟩, true, true, true, true⟩,
  ⟨4, 5, ⟨616, 755, 829, 1046, 339, 412, 779, 965, 544, 665, 449, 547, 456, 552⟩, true, true, true, true⟩,
  ⟨4, 6, ⟨234, 755, 352, 1046, 144, 412, 314, 965, 227, 665, 200, 547, 197, 552⟩, false, false, false, false⟩,
  ⟨5, 0, ⟨254, 254, 116, 116, 339, 340, 175, 175, 263, 263, 203, 204, 200, 201⟩, true, true, true, true⟩,
  ⟨5, 1, ⟨316, 316, 145, 145, 411, 412, 221, 221, 328, 328, 245, 246, 240, 241⟩, true, true, true, true⟩,
  ⟨5, 2, ⟨623, 623, 306, 306, 812, 813, 478, 478, 642, 642, 457, 458, 464, 465⟩, true, true, true, true⟩,
  ⟨5, 3, ⟨769, 769, 376, 376, 991, 992, 594, 594, 793, 793, 555, 556, 560, 561⟩, true, true, true, true⟩,
  ⟨5, 4, ⟨254, 316, 116, 145, 339, 412, 175, 221, 263, 328, 203, 246, 200, 241⟩, true, false, false, true⟩,
  ⟨5, 5, ⟨623, 769, 306, 376, 812, 992, 478, 594, 642, 793, 457, 556, 464, 561⟩, true, false, false, true⟩,
  ⟨5, 6, ⟨254, 769, 116, 376, 339, 992, 175, 594, 263, 793, 203, 556, 200, 561⟩, false, false, false, false⟩,
  ⟨6, 0, ⟨295, 296, 239, 240, 152, 153, 236, 237, 164, 165, 337, 338, 338, 339⟩, true, true, true, true⟩,
  ⟨6, 1, ⟨365, 366, 291, 292, 181, 182, 293, 294, 202, 203, 409, 410, 408, 409⟩, true, true, true, true⟩,
  ⟨6, 2, ⟨733, 734, 578, 579, 341, 342, 605, 606, 427, 428, 794, 795, 776, 777⟩, true, true, true, true⟩,
  ⟨6, 3, ⟨900, 901, 705, 706, 410, 411, 746, 747, 520, 521, 977, 978, 944, 945⟩, true, true, true, true⟩,
  ⟨6, 4, ⟨295, 366, 239, 292, 152, 182, 236, 294, 164, 203, 337, 410, 338, 409⟩, true, true, true, true⟩,
  ⟨6, 5, ⟨733, 901, 578, 706, 341, 411, 605, 747, 427, 521, 794, 978, 776, 945⟩, true, true, true, true⟩,
  ⟨6, 6, ⟨295, 901, 239, 706, 152, 411, 236, 747, 164, 521, 337, 978, 338, 945⟩, false, true, true, false⟩,
  ⟨7, 0, ⟨255, 255, 190, 190, 137, 138, 169, 169, 228, 228, 297, 298, 298, 299⟩, true, true, true, true⟩,
  ⟨7, 1, ⟨317, 317, 236, 236, 166, 167, 246, 246, 329, 329, 407, 408, 406, 407⟩, true, true, true, true⟩,
  ⟨7, 2, ⟨630, 630, 492, 492, 326, 327, 443, 443, 519, 519, 663, 664, 645, 646⟩, true, true, true, true⟩,
  ⟨7, 3, ⟨778, 778, 606, 606, 395, 396, 668, 668, 802, 802, 976, 977, 943, 944⟩, true, true, true, true⟩,
  ⟨7, 4, ⟨255, 317, 190, 236, 137, 167, 169, 246, 228, 329, 297, 408, 298, 407⟩, true, true, true, true⟩,
  ⟨7, 5, ⟨630, 778, 492, 606, 326, 396, 443, 668, 519, 802, 663, 977, 645, 944⟩, true, true, true, true⟩,
  ⟨7, 6, ⟨255, 778, 190, 606, 137, 396, 169, 668, 228, 802, 297, 977, 298, 944⟩, false, false, false, false⟩,
  ⟨8, 0, ⟨253, 253, 254, 254, 273, 274, 251, 251, 255, 255, 189, 190, 190, 191⟩, true, true, true, true⟩,
  ⟨8, 1, ⟨315, 315, 316, 316, 330, 331, 314, 314, 317, 317, 232, 233, 231, 232⟩, true, true, true, true⟩,
  ⟨8, 2, ⟨622, 622, 631, 631, 674, 675, 644, 644, 630, 630, 484, 485, 464, 465⟩, true, true, true, true⟩,
  ⟨8, 3, ⟨768, 768, 780, 780, 821, 822, 799, 799, 778, 778, 596, 597, 567, 568⟩, true, true, true, true⟩,
  ⟨8, 4, ⟨253, 315, 254, 316, 273, 331, 251, 314, 255, 317, 189, 233, 190, 232⟩, true, true, true, true⟩,
  ⟨8, 5, ⟨622, 768, 631, 780, 674, 822, 644, 799, 630, 778, 484, 597, 464, 568⟩, true, true, true, true⟩,
  ⟨8, 6, ⟨253, 768, 254, 780, 273, 822, 251, 799, 255, 778, 189, 597, 190, 568⟩, false, false, false, false⟩,
  ⟨9, 0, ⟨255, 256, 263, 263, 144, 145, 178, 179, 383, 384, 342, 343, 343, 344⟩, true, true, true, true⟩,
  ⟨9, 1, ⟨310, 311, 328, 328, 174, 175, 221, 222, 463, 464, 413, 414, 413, 414⟩, true, true, true, true⟩,
  ⟨9, 2, ⟨652, 653, 642, 642, 339, 340, 473, 474, 881, 882, 805, 806, 785, 786⟩, true, true, true, true⟩,
  ⟨9, 3, ⟨796, 797, 793, 793, 411, 412, 585, 586, 1071, 1072, 984, 985, 954, 955⟩, true, true, true, true⟩,
  ⟨9, 4, ⟨255, 311, 263, 328, 144, 175, 178, 222, 383, 464, 342, 414, 343, 414⟩, true, true, true, true⟩,
  ⟨9, 5, ⟨652, 797, 642, 793, 339, 412, 473, 586, 881, 1072, 805, 985, 785, 955⟩, true, true, true, true⟩,
  ⟨9, 6, ⟨255, 797, 263, 793, 144, 412, 178, 586, 383, 1072, 342, 985, 343, 955⟩, true, false, false, true⟩,
  ⟨10, 0, ⟨257, 257, 192, 192, 137, 138, 255, 255, 193, 193, 140, 141, 137, 138⟩, true, true, true, true⟩,
  ⟨10, 1, ⟨319, 319, 239, 239, 166, 167, 318, 318, 240, 240, 173, 174, 166, 167⟩, true, true, true, true⟩,
  ⟨10, 2, ⟨635, 635, 493, 493, 326, 327, 651, 651, 497, 497, 321, 322, 327, 328⟩, true, true, true, true⟩,
  ⟨10, 3, ⟨784, 784, 608, 608, 396, 397, 809, 809, 613, 613, 393, 394, 397, 398⟩, true, true, true, true⟩,
  ⟨10, 4, ⟨257, 319, 192, 239, 137, 167, 255, 318, 193, 240, 140, 174, 137, 167⟩, true, true, true, true⟩,
  ⟨10, 5, ⟨635, 784, 493, 608, 326, 397, 651, 809, 497, 613, 321, 394, 327, 398⟩, true, true, true, true⟩,
  ⟨10, 6, ⟨257, 784, 192, 608, 137, 397, 255, 809, 193, 613, 140, 394, 137, 398⟩, false, false, false, false⟩,
  ⟨11, 0, ⟨308, 309, 272, 273, 338, 339, 241, 242, 358, 359, 202, 203, 199, 200⟩, true, true, true, true⟩,
  ⟨11, 1, ⟨380, 381, 331, 332, 410, 411, 298, 299, 438, 439, 245, 246, 238, 239⟩, true, true, true, true⟩,
  ⟨11, 2, ⟨740, 741, 721, 722, 811, 812, 631, 632, 901, 902, 481, 482, 487, 488⟩, true, true, true, true⟩,
  ⟨11, 3, ⟨909, 910, 878, 879, 990, 991, 779, 780, 1102, 1103, 585, 586, 589, 590⟩, true, true, true, true⟩,
  ⟨11, 4, ⟨308, 381, 272, 332, 338, 411, 241, 299, 358, 439, 202, 246, 199, 239⟩, true, true, true, true⟩,
  ⟨11, 5, ⟨740, 910, 721, 879, 811, 991, 631, 780, 901, 1103, 481, 586, 487, 590⟩, true, true, true, true⟩,
  ⟨11, 6, ⟨308, 910, 272, 879, 338, 991, 241, 780, 358, 1103, 202, 586, 199, 590⟩, false, false, false, false⟩,
  ⟨12, 0, ⟨372, 373, 255, 255, 137, 138, 245, 246, 307, 308, 193, 194, 190, 191⟩, true, true, true, true⟩,
  ⟨12, 1, ⟨452, 453, 317, 317, 166, 167, 299, 300, 379, 380, 236, 237, 229, 230⟩, true, true, true, true⟩,
  ⟨12, 2, ⟨869, 870, 630, 630, 326, 327, 650, 651, 746, 747, 437, 438, 443, 444⟩, true, true, true, true⟩,
  ⟨12, 3, ⟨1059, 1060, 778, 778, 395, 396, 797, 798, 917, 918, 531, 532, 535, 536⟩, true, true, true, true⟩,
  ⟨12, 4, ⟨372, 453, 255, 317, 137, 167, 245, 300, 307, 380, 193, 237, 190, 230⟩, true, true, true, true⟩,
  ⟨12, 5, ⟨869, 1060, 630, 778, 326, 396, 650, 798, 746, 918, 437, 532, 443, 536⟩, true, true, true, true⟩,
  ⟨12, 6, ⟨372, 1060, 255, 778, 137, 396, 245, 798, 307, 918, 193, 532, 190, 536⟩, false, false, false, false⟩,
  ⟨13, 0, ⟨192, 192, 131, 132, 192, 193, 199, 200, 130, 131, 200, 201, 201, 202⟩, true, true, true, true⟩,
  ⟨13, 1, ⟨239, 239, 160, 161, 233, 234, 245, 246, 159, 160, 243, 244, 242, 243⟩, true, true, true, true⟩,
  ⟨13, 2, ⟨495, 495, 321, 322, 465, 466, 524, 525, 319, 320, 495, 496, 475, 476⟩, true, true, true, true⟩,
  ⟨13, 3, ⟨611, 611, 392, 393, 567, 568, 647, 648, 388, 389, 607, 608, 578, 579⟩, true, true, true, true⟩,
  ⟨13, 4, ⟨192, 239, 131, 161, 192, 234, 199, 246, 130, 160, 200, 244, 201, 243⟩, true, true, true, true⟩,
  ⟨13, 5, ⟨495, 611, 321, 393, 465, 568, 524, 648, 319, 389, 495, 608, 475, 579⟩, true, true, true, true⟩,
  ⟨13, 6, ⟨192, 611, 131, 393, 192, 568, 199, 648, 130, 389, 200, 608, 201, 579⟩, false, false, false, false⟩,
  ⟨14, 0, ⟨253, 253, 264, 265, 152, 153, 255, 255, 193, 193, 193, 194, 190, 191⟩, true, true, true, true⟩,
  ⟨14, 1, ⟨315, 315, 326, 327, 181, 182, 318, 318, 240, 240, 236, 237, 229, 230⟩, true, true, true, true⟩,
  ⟨14, 2, ⟨623, 623, 639, 640, 341, 342, 651, 651, 497, 497, 438, 439, 444, 445⟩, true, true, true, true⟩,
  ⟨14, 3, ⟨769, 769, 787, 788, 410, 411, 809, 809, 613, 613, 533, 534, 537, 538⟩, true, true, true, true⟩,
  ⟨14, 4, ⟨253, 315, 264, 327, 152, 182, 255, 318, 193, 240, 193, 237, 190, 230⟩, true, true, true, true⟩,
  ⟨14, 5, ⟨623, 769, 639, 788, 341, 411, 651, 809, 497, 613, 438, 534, 444, 538⟩, true, true, true, true⟩,
  ⟨14, 6, ⟨253, 769, 264, 788, 152, 411, 255, 809, 193, 613, 193, 534, 190, 538⟩, false, false, false, false⟩,
  ⟨15, 0, ⟨375, 376, 317, 318, 144, 145, 263, 264, 342, 343, 318, 319, 320, 321⟩, true, true, true, true⟩,
  ⟨15, 1, ⟨455, 456, 370, 371, 174, 175, 319, 320, 396, 397, 389, 390, 390, 391⟩, true, true, true, true⟩,
  ⟨15, 2, ⟨886, 887, 666, 667, 339, 340, 588, 589, 712, 713, 779, 780, 758, 759⟩, true, true, true, true⟩,
  ⟨15, 3, ⟨1080, 1081, 797, 798, 411, 412, 713, 714, 847, 848, 955, 956, 925, 926⟩, true, true, true, true⟩,
  ⟨15, 4, ⟨375, 456, 317, 371, 144, 175, 263, 320, 342, 397, 318, 390, 320, 391⟩, true, true, true, true⟩,
  ⟨15, 5, ⟨886, 1081, 666, 798, 339, 412, 588, 714, 712, 848, 779, 956, 758, 926⟩, true, true, true, true⟩,
  ⟨15, 6, ⟨375, 1081, 317, 798, 144, 412, 263, 714, 342, 848, 318, 956, 320, 926⟩, false, false, false, false⟩,
  ⟨16, 0, ⟨164, 165, 263, 263, 339, 340, 163, 164, 193, 193, 334, 335, 336, 337⟩, true, true, true, true⟩,
  ⟨16, 1, ⟨202, 203, 328, 328, 411, 412, 204, 205, 240, 240, 407, 408, 408, 409⟩, true, true, true, true⟩,
  ⟨16, 2, ⟨427, 428, 642, 642, 807, 808, 425, 426, 497, 497, 824, 825, 803, 804⟩, true, true, true, true⟩,
  ⟨16, 3, ⟨520, 521, 793, 793, 985, 986, 521, 522, 613, 613, 1010, 1011, 980, 981⟩, true, true, true, true⟩,
  ⟨16, 4, ⟨164, 203, 263, 328, 339, 412, 163, 205, 193, 240, 334, 408, 336, 409⟩, true, true, true, true⟩,
  ⟨16, 5, ⟨427, 521, 642, 793, 807, 986, 425, 522, 497, 613, 824, 1011, 803, 981⟩, true, true, true, true⟩,
  ⟨16, 6, ⟨164, 521, 263, 793, 339, 986, 163, 522, 193, 613, 334, 1011, 336, 981⟩, false, false, false, false⟩,
  ⟨17, 0, ⟨222, 223, 130, 131, 338, 339, 275, 276, 264, 265, 275, 276, 278, 279⟩, true, true, true, true⟩,
  ⟨17, 1, ⟨271, 272, 159, 160, 404, 405, 336, 337, 326, 327, 331, 332, 334, 335⟩, true, true, true, true⟩,
  ⟨17, 2, ⟨564, 565, 319, 320, 802, 803, 702, 703, 639, 640, 664, 665, 644, 645⟩, true, true, true, true⟩,
  ⟨17, 3, ⟨688, 689, 388, 389, 970, 971, 858, 859, 787, 788, 810, 811, 781, 782⟩, true, true, true, true⟩,
  ⟨17, 4, ⟨222, 272, 130, 160, 338, 405, 275, 337, 264, 327, 275, 332, 278, 335⟩, true, true, true, true⟩,
  ⟨17, 5, ⟨564, 689, 319, 389, 802, 971, 702, 859, 639, 788, 664, 811, 644, 782⟩, true, true, true, true⟩,
  ⟨17, 6, ⟨222, 689, 130, 389, 338, 971, 275, 859, 264, 788, 275, 811, 278, 782⟩, false, false, false, false⟩,
  ⟨18, 0, ⟨226, 227, 399, 400, 144, 145, 235, 236, 272, 273, 398, 399, 399, 400⟩, true, true, true, true⟩,
  ⟨18, 1, ⟨278, 279, 482, 483, 174, 175, 286, 287, 326, 327, 479, 480, 479, 480⟩, true, true, true, true⟩,
  ⟨18, 2, ⟨574, 575, 873, 874, 339, 340, 611, 612, 642, 643, 924, 925, 904, 905⟩, true, true, true, true⟩,
  ⟨18, 3, ⟨704, 705, 1065, 1066, 411, 412, 747, 748, 777, 778, 1126, 1127, 1096, 1097⟩, true, true, true, true⟩,
  ⟨18, 4, ⟨226, 279, 399, 483, 144, 175, 235, 287, 272, 327, 398, 480, 399, 480⟩, true, true, true, true⟩,
  ⟨18, 5, ⟨574, 705, 873, 1066, 339, 412, 611, 748, 642, 778, 924, 1127, 904, 1097⟩, true, true, true, true⟩,
  ⟨18, 6, ⟨226, 705, 399, 1066, 144, 412, 235, 748, 272, 778, 398, 1127, 399, 1097⟩, false, true, true, false⟩,
  ⟨19, 0, ⟨258, 258, 197, 197, 194, 195, 262, 262, 197, 197, 196, 197, 195, 196⟩, true, true, true, true⟩,
  ⟨19, 1, ⟨321, 321, 244, 244, 236, 237, 330, 330, 244, 244, 242, 243, 237, 238⟩, true, true, true, true⟩,
  ⟨19, 2, ⟨634, 634, 512, 512, 477, 478, 663, 663, 514, 514, 499, 500, 479, 480⟩, true, true, true, true⟩,
  ⟨19, 3, ⟨783, 783, 632, 632, 583, 584, 825, 825, 634, 634, 615, 616, 586, 587⟩, true, true, true, true⟩,
  ⟨19, 4, ⟨258, 321, 197, 244, 194, 237, 262, 330, 197, 244, 196, 243, 195, 238⟩, true, true, true, true⟩,
  ⟨19, 5, ⟨634, 783, 512, 632, 477, 584, 663, 825, 514, 634, 499, 616, 479, 587⟩, true, true, true, true⟩,
  ⟨19, 6, ⟨258, 783, 197, 632, 194, 584, 262, 825, 197, 634, 196, 616, 195, 587⟩, false, false, false, false⟩,
  ⟨20, 0, ⟨265, 266, 309, 310, 334, 335, 362, 363, 364, 365, 333, 334, 335, 336⟩, true, true, true, true⟩,
  ⟨20, 1, ⟨320, 321, 381, 382, 406, 407, 439, 440, 446, 447, 406, 407, 407, 408⟩, true, true, true, true⟩,
  ⟨20, 2, ⟨619, 620, 737, 738, 773, 774, 875, 876, 865, 866, 784, 785, 763, 764⟩, true, true, true, true⟩,
  ⟨20, 3, ⟨750, 751, 906, 907, 945, 946, 1070, 1071, 1060, 1061, 962, 963, 932, 933⟩, true, true, true, true⟩,
  ⟨20, 4, ⟨265, 321, 309, 382, 334, 407, 362, 440, 364, 447, 333, 407, 335, 408⟩, true, true, true, true⟩,
  ⟨20, 5, ⟨619, 751, 737, 907, 773, 946, 875, 1071, 865, 1061, 784, 963, 763, 933⟩, true, true, true, true⟩,
  ⟨20, 6, ⟨265, 751, 309, 907, 334, 946, 362, 1071, 364, 1061, 333, 963, 335, 933⟩, false, false, false, false⟩,
  ⟨21, 0, ⟨253, 254, 289, 290, 339, 340, 126, 126, 309, 310, 257, 258, 256, 257⟩, true, true, true, true⟩,
  ⟨21, 1, ⟨308, 309, 348, 349, 411, 412, 158, 158, 381, 382, 311, 312, 306, 307⟩, true, true, true, true⟩,
  ⟨21, 2, ⟨637, 638, 710, 711, 812, 813, 314, 314, 738, 739, 641, 642, 621, 622⟩, true, true, true, true⟩,
  ⟨21, 3, ⟨777, 778, 860, 861, 991, 992, 390, 390, 907, 908, 780, 781, 751, 752⟩, true, true, true, true⟩,
  ⟨21, 4, ⟨253, 309, 289, 349, 339, 412, 126, 158, 309, 382, 257, 312, 256, 307⟩, true, true, true, true⟩,
  ⟨21, 5, ⟨637, 778, 710, 861, 812, 992, 314, 390, 738, 908, 641, 781, 621, 752⟩, true, true, true, true⟩,
  ⟨21, 6, ⟨253, 778, 289, 861, 339, 992, 126, 390, 309, 908, 257, 781, 256, 752⟩, true, false, false, true⟩,
  ⟨22, 0, ⟨314, 315, 257, 257, 151, 152, 179, 180, 460, 461, 395, 396, 396, 397⟩, true, true, true, true⟩,
  ⟨22, 1, ⟨365, 366, 319, 319, 180, 181, 220, 221, 541, 542, 457, 458, 456, 457⟩, true, true, true, true⟩,
  ⟨22, 2, ⟨647, 648, 635, 635, 340, 341, 427, 428, 962, 963, 822, 823, 802, 803⟩, true, true, true, true⟩,
  ⟨22, 3, ⟨773, 774, 784, 784, 410, 411, 520, 521, 1154, 1155, 978, 979, 949, 950⟩, true, true, true, true⟩,
  ⟨22, 4, ⟨314, 366, 257, 319, 151, 181, 179, 221, 460, 542, 395, 458, 396, 457⟩, true, true, true, true⟩,
  ⟨22, 5, ⟨647, 774, 635, 784, 340, 411, 427, 521, 962, 1155, 822, 979, 802, 950⟩, true, true, true, true⟩,
  ⟨22, 6, ⟨314, 774, 257, 784, 151, 411, 179, 521, 460, 1155, 395, 979, 396, 950⟩, true, false, false, true⟩,
  ⟨23, 0, ⟨202, 203, 437, 438, 152, 153, 401, 402, 223, 224, 461, 462, 463, 464⟩, true, true, true, true⟩,
  ⟨23, 1, ⟨248, 249, 515, 516, 181, 182, 475, 476, 274, 275, 540, 541, 541, 542⟩, true, true, true, true⟩,
  ⟨23, 2, ⟨504, 505, 955, 956, 341, 342, 866, 867, 559, 560, 989, 990, 968, 969⟩, true, true, true, true⟩,
  ⟨23, 3, ⟨618, 619, 1146, 1147, 410, 411, 1050, 1051, 685, 686, 1187, 1188, 1157, 1158⟩, true, true, true, true⟩,
  ⟨23, 4, ⟨202, 249, 437, 516, 152, 182, 401, 476, 223, 275, 461, 541, 463, 542⟩, true, true, true, true⟩,
  ⟨23, 5, ⟨504, 619, 955, 1147, 341, 411, 866, 1051, 559, 686, 989, 1188, 968, 1158⟩, true, true, true, true⟩,
  ⟨23, 6, ⟨202, 619, 437, 1147, 152, 411, 401, 1051, 223, 686, 461, 1188, 463, 1158⟩, false, true, true, false⟩,
  ⟨24, 0, ⟨306, 307, 231, 232, 150, 151, 319, 320, 253, 253, 260, 261, 261, 262⟩, true, true, true, true⟩,
  ⟨24, 1, ⟨378, 379, 282, 283, 179, 180, 392, 393, 315, 315, 313, 314, 312, 313⟩, true, true, true, true⟩,
  ⟨24, 2, ⟨740, 741, 601, 602, 339, 340, 784, 785, 623, 623, 653, 654, 633, 634⟩, true, true, true, true⟩,
  ⟨24, 3, ⟨910, 911, 735, 736, 409, 410, 966, 967, 769, 769, 796, 797, 767, 768⟩, true, true, true, true⟩,
  ⟨24, 4, ⟨306, 379, 231, 283, 150, 180, 319, 393, 253, 315, 260, 314, 261, 313⟩, true, true, true, true⟩,
  ⟨24, 5, ⟨740, 911, 601, 736, 339, 410, 784, 967, 623, 769, 653, 797, 633, 768⟩, true, true, true, true⟩,
  ⟨24, 6, ⟨306, 911, 231, 736, 150, 410, 319, 967, 253, 769, 260, 797, 261, 768⟩, false, false, false, false⟩,
  ⟨25, 0, ⟨359, 360, 170, 170, 276, 277, 298, 299, 228, 229, 323, 324, 326, 327⟩, true, true, true, true⟩,
  ⟨25, 1, ⟨439, 440, 211, 211, 333, 334, 369, 370, 279, 280, 390, 391, 393, 394⟩, true, true, true, true⟩,
  ⟨25, 2, ⟨862, 863, 441, 441, 678, 679, 762, 763, 558, 559, 783, 784, 763, 764⟩, true, true, true, true⟩,
  ⟨25, 3, ⟨1054, 1055, 543, 543, 825, 826, 941, 942, 683, 684, 955, 956, 926, 927⟩, true, true, true, true⟩,
  ⟨25, 4, ⟨359, 440, 170, 211, 276, 334, 298, 370, 228, 280, 323, 391, 326, 394⟩, true, true, true, true⟩,
  ⟨25, 5, ⟨862, 1055, 441, 543, 678, 826, 762, 942, 558, 684, 783, 956, 763, 927⟩, true, true, true, true⟩,
  ⟨25, 6, ⟨359, 1055, 170, 543, 276, 826, 298, 942, 228, 684, 323, 956, 326, 927⟩, false, false, false, false⟩,
  ⟨26, 0, ⟨173, 173, 258, 258, 259, 260, 175, 175, 263, 263, 277, 278, 279, 280⟩, true, true, true, true⟩,
  ⟨26, 1, ⟨215, 215, 321, 321, 308, 309, 221, 221, 328, 328, 335, 336, 336, 337⟩, true, true, true, true⟩,
  ⟨26, 2, ⟨456, 456, 634, 634, 593, 594, 478, 478, 642, 642, 714, 715, 694, 695⟩, true, true, true, true⟩,
  ⟨26, 3, ⟨562, 562, 783, 783, 713, 714, 594, 594, 793, 793, 874, 875, 845, 846⟩, true, true, true, true⟩,
  ⟨26, 4, ⟨173, 215, 258, 321, 259, 309, 175, 221, 263, 328, 277, 336, 279, 337⟩, true, true, true, true⟩,
  ⟨26, 5, ⟨456, 562, 634, 783, 593, 714, 478, 594, 642, 793, 714, 875, 694, 846⟩, true, true, true, true⟩,
  ⟨26, 6, ⟨173, 562, 258, 783, 259, 714, 175, 594, 263, 793, 277, 875, 279, 846⟩, false, false, false, false⟩,
  ⟨27, 0, ⟨288, 289, 327, 328, 135, 136, 175, 175, 211, 212, 283, 284, 284, 285⟩, true, true, true, true⟩,
  ⟨27, 1, ⟨399, 400, 429, 430, 176, 177, 221, 221, 249, 250, 351, 352, 349, 350⟩, true, true, true, true⟩,
  ⟨27, 2, ⟨677, 678, 743, 744, 307, 308, 478, 478, 475, 476, 684, 685, 663, 664⟩, true, true, true, true⟩,
  ⟨27, 3, ⟨991, 992, 1053, 1054, 420, 421, 594, 594, 568, 569, 846, 847, 814, 815⟩, true, true, true, true⟩,
  ⟨27, 4, ⟨288, 400, 327, 430, 135, 177, 175, 221, 211, 250, 283, 352, 284, 350⟩, true, true, true, true⟩,
  ⟨27, 5, ⟨677, 992, 743, 1054, 307, 421, 478, 594, 475, 569, 684, 847, 663, 815⟩, true, true, true, true⟩,
  ⟨27, 6, ⟨288, 992, 327, 1054, 135, 421, 175, 594, 211, 569, 283, 847, 284, 815⟩, false, true, true, false⟩,
  ⟨28, 0, ⟨315, 316, 256, 257, 144, 145, 366, 367, 197, 197, 340, 341, 341, 342⟩, true, true, true, true⟩,
  ⟨28, 1, ⟨389, 390, 314, 315, 174, 175, 450, 451, 244, 244, 415, 416, 414, 415⟩, true, true, true, true⟩,
  ⟨28, 2, ⟨757, 758, 638, 639, 339, 340, 901, 902, 514, 514, 795, 796, 777, 778⟩, true, true, true, true⟩,
  ⟨28, 3, ⟨931, 932, 782, 783, 411, 412, 1105, 1106, 634, 634, 982, 983, 949, 950⟩, true, true, true, true⟩,
  ⟨28, 4, ⟨315, 390, 256, 315, 144, 175, 366, 451, 197, 244, 340, 416, 341, 415⟩, true, true, true, true⟩,
  ⟨28, 5, ⟨757, 932, 638, 783, 339, 412, 901, 1106, 514, 634, 795, 983, 777, 950⟩, true, true, true, true⟩,
  ⟨28, 6, ⟨315, 932, 256, 783, 144, 412, 366, 1106, 197, 634, 340, 983, 341, 950⟩, false, false, false, false⟩,
  ⟨29, 0, ⟨197, 197, 174, 174, 144, 145, 187, 187, 253, 253, 330, 331, 331, 332⟩, true, true, true, true⟩,
  ⟨29, 1, ⟨244, 244, 216, 216, 174, 175, 233, 233, 315, 315, 403, 404, 403, 404⟩, true, true, true, true⟩,
  ⟨29, 2, ⟨514, 514, 458, 458, 339, 340, 512, 512, 623, 623, 790, 791, 770, 771⟩, true, true, true, true⟩,
  ⟨29, 3, ⟨634, 634, 565, 565, 411, 412, 635, 635, 769, 769, 971, 972, 941, 942⟩, true, true, true, true⟩,
  ⟨29, 4, ⟨197, 244, 174, 216, 144, 175, 187, 233, 253, 315, 330, 404, 331, 404⟩, true, true, true, true⟩,
  ⟨29, 5, ⟨514, 634, 458, 565, 339, 412, 512, 635, 623, 769, 790, 972, 770, 942⟩, true, true, true, true⟩,
  ⟨29, 6, ⟨197, 634, 174, 565, 144, 412, 187, 635, 253, 769, 330, 972, 331, 942⟩, false, false, false, false⟩,
  ⟨30, 0, ⟨409, 410, 297, 298, 137, 138, 283, 284, 323, 324, 251, 252, 248, 249⟩, true, true, true, true⟩,
  ⟨30, 1, ⟨495, 496, 367, 368, 166, 167, 376, 377, 442, 443, 314, 315, 309, 310⟩, true, true, true, true⟩,
  ⟨30, 2, ⟨936, 937, 734, 735, 326, 327, 705, 706, 759, 760, 575, 576, 582, 583⟩, true, true, true, true⟩,
  ⟨30, 3, ⟨1139, 1140, 901, 902, 395, 396, 975, 976, 1089, 1090, 744, 745, 749, 750⟩, true, true, true, true⟩,
  ⟨30, 4, ⟨409, 496, 297, 368, 137, 167, 283, 377, 323, 443, 251, 315, 248, 310⟩, true, true, true, true⟩,
  ⟨30, 5, ⟨936, 1140, 734, 902, 326, 396, 705, 976, 759, 1090, 575, 745, 582, 750⟩, true, true, true, true⟩,
  ⟨30, 6, ⟨409, 1140, 297, 902, 137, 396, 283, 976, 323, 1090, 251, 745, 248, 750⟩, false, false, false, false⟩,
  ⟨31, 0, ⟨258, 258, 255, 255, 194, 195, 262, 262, 257, 257, 196, 197, 195, 196⟩, true, true, true, true⟩,
  ⟨31, 1, ⟨321, 321, 317, 317, 236, 237, 330, 330, 319, 319, 242, 243, 237, 238⟩, true, true, true, true⟩,
  ⟨31, 2, ⟨634, 634, 620, 620, 477, 478, 663, 663, 627, 627, 499, 500, 479, 480⟩, true, true, true, true⟩,
  ⟨31, 3, ⟨783, 783, 766, 766, 583, 584, 825, 825, 774, 774, 615, 616, 586, 587⟩, true, true, true, true⟩,
  ⟨31, 4, ⟨258, 321, 255, 317, 194, 237, 262, 330, 257, 319, 196, 243, 195, 238⟩, true, true, true, true⟩,
  ⟨31, 5, ⟨634, 783, 620, 766, 477, 584, 663, 825, 627, 774, 499, 616, 479, 587⟩, true, true, true, true⟩,
  ⟨31, 6, ⟨258, 783, 255, 766, 194, 584, 262, 825, 257, 774, 196, 616, 195, 587⟩, false, false, false, false⟩,
  ⟨32, 0, ⟨257, 257, 263, 263, 143, 144, 326, 327, 193, 193, 334, 335, 336, 337⟩, true, true, true, true⟩,
  ⟨32, 1, ⟨319, 319, 328, 328, 173, 174, 402, 403, 240, 240, 407, 408, 408, 409⟩, true, true, true, true⟩,
  ⟨32, 2, ⟨627, 627, 642, 642, 338, 339, 804, 805, 497, 497, 824, 825, 803, 804⟩, true, true, true, true⟩,
  ⟨32, 3, ⟨774, 774, 793, 793, 410, 411, 991, 992, 613, 613, 1010, 1011, 980, 981⟩, true, true, true, true⟩,
  ⟨32, 4, ⟨257, 319, 263, 328, 143, 174, 326, 403, 193, 240, 334, 408, 336, 409⟩, true, true, true, true⟩,
  ⟨32, 5, ⟨627, 774, 642, 793, 338, 411, 804, 992, 497, 613, 824, 1011, 803, 981⟩, true, true, true, true⟩,
  ⟨32, 6, ⟨257, 774, 263, 793, 143, 411, 326, 992, 193, 613, 334, 1011, 336, 981⟩, false, false, false, false⟩,
  ⟨33, 0, ⟨116, 116, 256, 256, 192, 193, 170, 170, 303, 304, 338, 339, 339, 340⟩, true, true, true, true⟩,
  ⟨33, 1, ⟨145, 145, 318, 318, 233, 234, 213, 213, 359, 360, 411, 412, 411, 412⟩, true, true, true, true⟩,
  ⟨33, 2, ⟨306, 306, 631, 631, 463, 464, 463, 463, 667, 668, 835, 836, 815, 816⟩, true, true, true, true⟩,
  ⟨33, 3, ⟨376, 376, 779, 779, 565, 566, 575, 575, 805, 806, 1025, 1026, 995, 996⟩, true, true, true, true⟩,
  ⟨33, 4, ⟨116, 145, 256, 318, 192, 234, 170, 213, 303, 360, 338, 412, 339, 412⟩, true, true, true, true⟩,
  ⟨33, 5, ⟨306, 376, 631, 779, 463, 566, 463, 575, 667, 806, 835, 1026, 815, 996⟩, true, true, true, true⟩,
  ⟨33, 6, ⟨116, 376, 256, 779, 192, 566, 170, 575, 303, 806, 338, 1026, 339, 996⟩, false, false, false, false⟩,
  ⟨34, 0, ⟨254, 254, 256, 256, 192, 193, 174, 174, 125, 125, 339, 340, 340, 341⟩, true, true, true, true⟩,
  ⟨34, 1, ⟨316, 316, 318, 318, 233, 234, 220, 220, 155, 155, 415, 416, 413, 414⟩, true, true, true, true⟩,
  ⟨34, 2, ⟨623, 623, 631, 631, 463, 464, 476, 476, 325, 325, 835, 836, 814, 815⟩, true, true, true, true⟩,
  ⟨34, 3, ⟨769, 769, 779, 779, 565, 566, 591, 591, 399, 399, 1026, 1027, 994, 995⟩, true, true, true, true⟩,
  ⟨34, 4, ⟨254, 316, 256, 318, 192, 234, 174, 220, 125, 155, 339, 416, 340, 414⟩, true, true, true, true⟩,
  ⟨34, 5, ⟨623, 769, 631, 779, 463, 566, 476, 591, 325, 399, 835, 1027, 814, 995⟩, true, true, true, true⟩,
  ⟨34, 6, ⟨254, 769, 256, 779, 192, 566, 174, 591, 125, 399, 339, 1027, 340, 995⟩, true, true, true, true⟩,
  ⟨35, 0, ⟨121, 121, 263, 263, 330, 331, 187, 187, 255, 255, 252, 253, 249, 250⟩, true, true, true, true⟩,
  ⟨35, 1, ⟨151, 151, 328, 328, 396, 397, 233, 233, 317, 317, 304, 305, 297, 298⟩, true, true, true, true⟩,
  ⟨35, 2, ⟨316, 316, 642, 642, 781, 782, 512, 512, 630, 630, 566, 567, 572, 573⟩, true, true, true, true⟩,
  ⟨35, 3, ⟨388, 388, 793, 793, 947, 948, 635, 635, 778, 778, 683, 684, 687, 688⟩, true, true, true, true⟩,
  ⟨35, 4, ⟨121, 151, 263, 328, 330, 397, 187, 233, 255, 317, 252, 305, 249, 298⟩, true, true, true, true⟩,
  ⟨35, 5, ⟨316, 388, 642, 793, 781, 948, 512, 635, 630, 778, 566, 684, 572, 688⟩, true, true, true, true⟩,
  ⟨35, 6, ⟨121, 388, 263, 793, 330, 948, 187, 635, 255, 778, 252, 684, 249, 688⟩, false, false, false, false⟩
]

theorem rows_length : rows.length = 252 := by decide

/-- Every row is checked (kernel). -/
theorem rows_ok : rows.all rowOk = true := by decide +kernel

/-- **Headline.** On every routed row, every check is DECIDED: either the κ condition holds
(exclusion for every per-pin behaviour, no FIFO needed) or a FIFO (transport) behaviour
overlaps. No row needs H_PIN_FIFO. -/
theorem gcd_rows : ∀ r ∈ rows, r.B.Ok ∧
    (∀ f : Int, 0 ≤ f →
      (r.v12 = true → ∀ c : Cell r.B true (dn f) hi1, Excl c) ∧
      (r.v12 = false → ∃ c : Cell r.B true (dn f) hi1, Transport c ∧ ¬ Excl c)) ∧
    (∀ f : Int, 0 ≤ f →
      (r.v21 = true → ∀ c : Cell r.B false hi1 (dn f), Excl c) ∧
      (r.v21 = false → ∃ c : Cell r.B false hi1 (dn f), Transport c ∧ ¬ Excl c)) ∧
    (∀ e1 e2 : Int, 0 ≤ e1 → 0 ≤ e2 →
      (r.vo1 = true → ∀ c : Cell r.B false (up e1) (dn e2), Excl c) ∧
      (r.vo1 = false → ((∃ c : Cell r.B false (up e1) (dn e2), Transport c ∧ ¬ Excl c) ↔
        onO1 r.B ≤ e2 - e1))) ∧
    (∀ e1 e2 : Int, 0 ≤ e1 → 0 ≤ e2 →
      (r.vo2 = true → ∀ c : Cell r.B true (dn e1) (up e2), Excl c) ∧
      (r.vo2 = false → ((∃ c : Cell r.B true (dn e1) (up e2), Transport c ∧ ¬ Excl c) ↔
        onO2 r.B ≤ e1 - e2))) :=
  fun r hr => rowOk_sound r (List.all_eq_true.mp rows_ok r hr)

/-- Point corners (144 rows): all four checks safe without FIFO, κ margin ≥ 54 ps. -/
theorem pt_safe : rows.all (fun r => decide (4 ≤ r.cor) ||
    (r.v12 && r.v21 && r.vo1 && r.vo2 && decide (54 ≤ min (min (k12 r.B) (k21 r.B)) (min (kO1 r.B) (kO2 r.B))))) = true := by
  decide +kernel

/-- At a point corner every window has at most 2 instants, so no runt is possible at all. -/
theorem pt_narrow : rows.all (fun r => decide (4 ≤ r.cor) ||
    decide (r.B.A1 ≤ r.B.a1 + 1 ∧ r.B.A2 ≤ r.B.a2 + 1 ∧ r.B.C5 ≤ r.B.c5 + 1 ∧ r.B.C6 ≤ r.B.c6 + 1)) = true := by
  decide +kernel

/-- Corner ranges FR / SR (72 rows): every check safe without FIFO (κ margin ≥ 33 ps)
except the rows listed (arbiter, corner), which fail the r2 -> r1 handover and the
opposite-sense race EVEN WITH FIFO. -/
theorem rng_rows : (rows.filter (fun r => (r.cor == 4 || r.cor == 5) &&
    !(r.v12 && r.v21 && r.vo1 && r.vo2))).length = 2 ∧
    rows.all (fun r => !(r.cor == 4 || r.cor == 5) || (r.v12 && r.v21 && r.vo1 && r.vo2) ||
      (r.id == 5 && r.cor == 4 && r.v12 && !r.v21 && !r.vo1 && r.vo2 && decide (k21 r.B = -9) && decide (onO1 r.B = 130)) || (r.id == 5 && r.cor == 5 && r.v12 && !r.v21 && !r.vo1 && r.vo2 && decide (k21 r.B = -30) && decide (onO1 r.B = 288))) = true := by
  decide +kernel

theorem rng_safe_margin : rows.all (fun r => !(r.cor == 4 || r.cor == 5) || !(r.v12 && r.v21 && r.vo1 && r.vo2) ||
    decide (33 ≤ min (min (k12 r.B) (k21 r.B)) (min (kO1 r.B) (kO2 r.B)))) = true := by
  decide +kernel

/-- Independent box (36 rows): counts of checks failing even with FIFO for h12, h21, o1, o2. -/
theorem box_counts :
    ((rows.filter (fun r => r.cor == 6 && !r.v12)).length,
     (rows.filter (fun r => r.cor == 6 && !r.v21)).length,
     (rows.filter (fun r => r.cor == 6 && !r.vo1)).length,
     (rows.filter (fun r => r.cor == 6 && !r.vo2)).length,
     (rows.filter (fun r => r.cor == 6 && r.v12 && r.v21 && r.vo1 && r.vo2)).length) =
    (30, 29, 29, 30, 2) := by
  decide +kernel


end Formal.Cells.ArbPin2
