import Formal.Cells.LibGapMux

/-!
# RuleK: what shard C's "rule K" checks, derived from shard B's exact join theorem

Probe C-10l2. Core Lean only (the import closure is Mathlib-free).

## Which obligation rule K is

10l named its rule K after B's X4 row (`bd_mux.isochronic_forks`, the
`ctl_req -> {uj0, uj1}` fork), but B's X4 row says that half needs NO
condition under FIFO wire branches (`OpsCounter.mux_ok_noskew`). The condition
rule K evaluates -- "the ctl_req pulse at a join has ended before `s` can
change there" -- is B's X3 hold half `bd_mux.bundled_s_hold`
(`LibGapMux.join_box_exact`, exact per join over the delay box):

    H_HOLD_PIN (join k):   Cf + pc_k.hi ≤ S1 + ps_k.lo

with `Cf` the fall of ctl_req at its driver, `S1` the next change of `s` at its
driver, and `pc_k`, `ps_k` the read windows of join k's ctl_req and s pins
(wire + site pin + that pin's LUT arc to O6).

`S1` is not a routed quantity. This file derives it from the selected join:
`sel_fall_after_ctl_fall` (from the REAL INIT, through B's `LutEq`) shows
that the SELECTED join cannot fall before it reads ctl_req low, i.e. before
`Cf + pc_sel.lo`. The rest of the causal chain (selected join fall -> uor ->
delay line -> server -> z_ack fall -> control sender -> its latch reopens ->
`s` changes) is the named hypothesis **H_ROUND_TRIP** `tf + Rt ≤ S1`, with
`Rt` its minimum delay. Then:

* `ruleK_hold`: the fork form `pc_k.hi ≤ pc_sel.lo + Rt + ps_k.lo` gives B's
  H_HOLD_PIN at join k;
* `mux_joins_ruleK`: with B's setup halves, both joins meet B's spec
  (`JSpec`) for the token -- the selected one fires correctly and the
  deselected one never takes the other input's token;
* `ruleK_exact`: at the minimum round trip (`S1 = Cf + pc_sel.lo + Rt`) the
  fork form is EXACT over the delay box (B's `join_box_exact`).

So rule K is a weak-isochrony condition on the ctl_req fork: the skew between
the branch to join k (max) and the branch to the selected join (min) must be
below one control round trip plus join k's s-pin read. A launch-based static
check (launch = the control sender's state node, which drives both ctl_req
and the latch holding `s`) evaluates exactly this when its late side runs
through the selected join; see notes/C-10l2-rulek.md for what 10l's front end
did instead.

## Hypotheses (all named in the statements)

* B's `LutEq` (H_PIN_READ), `Stable` (H_S_STABLE), `pulse` (H_CTL_PULSE).
* **H_SEL_FIRED** (`hhigh`, `hta0`, `hsetS`, `hcr`): the selected join is high
  on `[ta - pq.hi, ta)`, with `ta` after both its ctl_req and s reads of the
  token are valid. Witness: `witness` below (B's own numbers).
* **H_SEL_FELL** (`htf`, `hfall`): it is low again at `tf ≥ ta`.
* **H_ROUND_TRIP** (`hRT`): `tf + Rt ≤ S1`. A protocol + delay fact about the
  rest of the loop, NOT proved here (it is what the static late side bounds).

NOT covered: the uxa/uya acknowledges, z bundling, reset; more than one
token per statement; Kleene reads; where `Rt` comes from on a route.
-/

namespace Formal.Timing.RuleK
open Formal.Cells.LibGapSteer
open Formal.Cells.LibGapMux

/-- The selected join holds while it reads ctl_req high and `s = b` (real INIT). -/
theorem jB_hold : ∀ b r : Bool, jB b r true b true = true := by decide

/-- **The selected join cannot fall before it reads ctl_req low.** -/
theorem sel_fall_after_ctl_fall (b : Bool) (pr pc ps pq : Rd) (r s j : Int → Bool)
    (Cr Cf S0 S1 ta tf : Int)
    (hL : LutEq b pr pc ps pq r (pulse Cr Cf) s j) (hs : Stable s b S0 S1)
    (hq : 1 ≤ pq.lo)
    (hhigh : ∀ u, ta - pq.hi ≤ u → u < ta → j u = true) (hta0 : 0 ≤ ta)
    (hsetS : S0 + ps.hi ≤ ta) (hcr : Cr + pc.hi ≤ ta)
    (hS1 : tf - ps.lo < S1) (htf : ta ≤ tf) (hfall : j tf = false) :
    Cf + pc.lo ≤ tf := by
  apply Classical.byContradiction
  intro hlt
  have key : ∀ n : Nat, ∀ u : Int, u - (ta - pq.hi) < n → ta - pq.hi ≤ u → u ≤ tf →
      j u = true := by
    intro n
    induction n with
    | zero => intro u h1 h2 _; omega
    | succ n ih =>
      intro u h1 h2 h3
      by_cases hu : u < ta
      · exact hhigh u h2 hu
      · rw [hL u (by omega)]
        have c1 := pc.ge u; have c2 := pc.le u
        have s1 := ps.ge u; have s2 := ps.le u
        have q1 := pq.ge u; have q2 := pq.le u
        have hc : pulse Cr Cf (pc.σ u) = true := by
          simp only [pulse, decide_eq_true_eq]; constructor <;> omega
        have hsv : s (ps.σ u) = b := hs _ (by omega) (by omega)
        have hj : j (pq.σ u) = true := ih _ (by omega) (by omega) (by omega)
        rw [hc, hsv, hj]
        exact jB_hold b _
  have := key ((tf - (ta - pq.hi)).toNat + 1) tf (by omega)
    (by have := pq.le 0; have := pq.ge 0; omega) (Int.le_refl _)
  rw [hfall] at this
  exact absurd this (by decide)

/-- **Rule K's fork form gives B's hold at join k** (arithmetic). -/
theorem ruleK_hold (Cf S1 tf Rt pcS_lo pcK_hi psK_lo : Int)
    (htf : Cf + pcS_lo ≤ tf) (hRT : tf + Rt ≤ S1)
    (hK : pcK_hi ≤ pcS_lo + Rt + psK_lo) : Cf + pcK_hi ≤ S1 + psK_lo := by
  omega

/-- **Both joins of one bd_mux meet B's spec for the token**, under B's
setup halves, H_SEL_FIRED / H_SEL_FELL, H_ROUND_TRIP and rule K's fork form
at each join (`K_S` for the selected join, `K_D` for the deselected one). -/
theorem mux_joins_ruleK (v : Bool) (prS pcS psS pqS prD pcD psD pqD : Rd)
    (rS rD s jS jD : Int → Bool) (Cr Cf S0 S1 ta tf Rt : Int)
    (hs : Stable s v S0 S1)
    (hLS : LutEq v prS pcS psS pqS rS (pulse Cr Cf) s jS)
    (hLD : LutEq (!v) prD pcD psD pqD rD (pulse Cr Cf) s jD)
    (hq : 1 ≤ pqS.lo)
    (hhigh : ∀ u, ta - pqS.hi ≤ u → u < ta → jS u = true) (hta0 : 0 ≤ ta)
    (hsetS : S0 + psS.hi ≤ ta) (hcr : Cr + pcS.hi ≤ ta)
    (htf : ta ≤ tf) (hfall : jS tf = false)
    (hRT : tf + Rt ≤ S1) (hRt : 1 ≤ Rt + psS.lo)
    (H_SETUP_S : S0 + psS.hi ≤ Cr + pcS.lo) (H_SETUP_D : S0 + psD.hi ≤ Cr + pcD.lo)
    (K_S : pcS.hi ≤ pcS.lo + Rt + psS.lo) (K_D : pcD.hi ≤ pcS.lo + Rt + psD.lo) :
    JSpec v v prS pcS pqS rS (pulse Cr Cf) jS ∧
    JSpec (!v) v prD pcD pqD rD (pulse Cr Cf) jD := by
  have hf := sel_fall_after_ctl_fall v prS pcS psS pqS rS s jS Cr Cf S0 S1 ta tf hLS hs hq
    hhigh hta0 hsetS hcr (by omega) htf hfall
  exact ⟨join_pin_ok v v _ _ _ _ Cr Cf S0 S1 rS s jS hs hLS H_SETUP_S
      (ruleK_hold Cf S1 tf Rt pcS.lo pcS.hi psS.lo hf hRT K_S),
    join_pin_ok (!v) v _ _ _ _ Cr Cf S0 S1 rD s jD hs hLD H_SETUP_D
      (ruleK_hold Cf S1 tf Rt pcS.lo pcD.hi psD.lo hf hRT K_D)⟩

/-- **Exactness at the minimum round trip.** If `s` changes as early as the
causal chain allows (`S1 = Cf + ClS + Rt`, `ClS` = the selected join's
minimum ctl_req read), then over join k's delay box B's spec holds for every
trace iff the setup half and rule K's fork form `Chi ≤ ClS + Rt + Slo` hold. -/
theorem ruleK_exact (b v : Bool) (Rlo Rhi Clo Chi Slo Shi Qlo Qhi Cr Cf S0 ClS Rt : Int)
    (hR : Rlo ≤ Rhi) (hC : Clo ≤ Chi) (hS : Slo ≤ Shi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (hCF : Cr < Cf) (hRst : 0 ≤ Cr + Clo) :
    (∀ pr pc ps pq : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Clo ≤ pc.lo → pc.hi ≤ Chi →
      Slo ≤ ps.lo → ps.hi ≤ Shi → Qlo ≤ pq.lo → pq.hi ≤ Qhi →
      ∀ r s j : Int → Bool, Stable s v S0 (Cf + ClS + Rt) → LutEq b pr pc ps pq r (pulse Cr Cf) s j →
        Rest j → JSpec b v pr pc pq r (pulse Cr Cf) j) ↔
    (S0 + Shi ≤ Cr + Clo ∧ Chi ≤ ClS + Rt + Slo) := by
  rw [join_box_exact b v Rlo Rhi Clo Chi Slo Shi Qlo Qhi Cr Cf S0 (Cf + ClS + Rt) hR hC hS hQ1 hQ
    hCF hRst]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

/-! ## Non-vacuity: every hypothesis of `mux_joins_ruleK` on one constructed run

B's numbers (`LibGapMux.wj`): ctl_req `[1000, 3000)` read through 300 ps, `s = 1`
on `[500, 4000)` read through 450 ps, loop 100 ps; here the y request falls at
2000 so the selected uj1 falls (at 3300); x waits (high) at uj0. Round trip
`Rt = 700`: `3300 + 700 ≤ 4000`. -/

def wS : Int → Bool :=
  run (jf true 0 300 450 (pulse 0 2000) (pulse 1000 3000) (sAdv true 500 4000)) 100 (by decide)
def wD : Int → Bool :=
  run (jf false 0 300 450 (fun _ => true) (pulse 1000 3000) (sAdv true 500 4000)) 100 (by decide)

theorem witness_luteqS : LutEq true (Rd.const 0) (Rd.const 300) (Rd.const 450) (Rd.const (100 : Nat))
    (pulse 0 2000) (pulse 1000 3000) (sAdv true 500 4000) wS :=
  run_luteq true 0 300 450 100 (by decide) _ _ _

theorem witness_luteqD : LutEq false (Rd.const 0) (Rd.const 300) (Rd.const 450) (Rd.const (100 : Nat))
    (fun _ => true) (pulse 1000 3000) (sAdv true 500 4000) wD :=
  run_luteq false 0 300 450 100 (by decide) _ _ _

/-- The selected join is high on `[1300, 1400)` and low at 3300. -/
theorem witness_sel : (∀ u : Int, 1400 - 100 ≤ u → u < 1400 → wS u = true) ∧ wS 3300 = false := by
  have hspec := join_pin_ok true true _ _ _ _ 1000 3000 500 4000 _ _ _ (sAdv_stable true 500 4000)
    witness_luteqS (by simp [Rd.const]) (by simp [Rd.const])
  refine ⟨fun u h1 h2 => ?_, ?_⟩
  · rw [hspec u (by omega)]
    simp only [specB, pulse]
    have e1 : decide ((0 : Int) ≤ (Rd.const 0).σ u ∧ (Rd.const 0).σ u < 2000) = true :=
      decide_eq_true (show (0 : Int) ≤ u - 0 ∧ u - 0 < 2000 by omega)
    have e2 : decide ((1000 : Int) ≤ (Rd.const 300).σ u ∧ (Rd.const 300).σ u < 3000) = true :=
      decide_eq_true (show (1000 : Int) ≤ u - 300 ∧ u - 300 < 3000 by omega)
    rw [e1, e2]
    exact cS_11 _
  · rw [hspec 3300 (by decide)]
    simp only [specB, pulse]
    generalize wS _ = q
    cases q <;> decide

theorem witness :
    ∃ (S0 S1 Cr Cf ta tf Rt : Int),
      Stable (sAdv true 500 4000) true S0 S1 ∧
      LutEq true (Rd.const 0) (Rd.const 300) (Rd.const 450) (Rd.const (100 : Nat))
        (pulse 0 2000) (pulse Cr Cf) (sAdv true 500 4000) wS ∧
      LutEq (!true) (Rd.const 0) (Rd.const 300) (Rd.const 450) (Rd.const (100 : Nat))
        (fun _ => true) (pulse Cr Cf) (sAdv true 500 4000) wD ∧
      (∀ u, ta - (Rd.const (100 : Nat)).hi ≤ u → u < ta → wS u = true) ∧ 0 ≤ ta ∧
      S0 + (Rd.const 450).hi ≤ ta ∧ Cr + (Rd.const 300).hi ≤ ta ∧ ta ≤ tf ∧ wS tf = false ∧
      tf + Rt ≤ S1 ∧ 1 ≤ Rt + (Rd.const 450).lo ∧
      S0 + (Rd.const 450).hi ≤ Cr + (Rd.const 300).lo ∧
      (Rd.const 300).hi ≤ (Rd.const 300).lo + Rt + (Rd.const 450).lo :=
  ⟨500, 4000, 1000, 3000, 1400, 3300, 700, sAdv_stable true 500 4000, witness_luteqS,
    witness_luteqD, fun u h1 h2 => witness_sel.1 u (by simpa [Rd.const] using h1) h2, by decide,
    by simp [Rd.const], by simp [Rd.const], by decide, witness_sel.2, by decide,
    by simp [Rd.const], by simp [Rd.const], by simp [Rd.const]⟩

/-- The witness run through `mux_joins_ruleK`: uj1 obeys the spec and uj0
(x waiting) stays low for ever. -/
theorem witness_conclusion : ∀ t, wD t = false := by
  have h := (mux_joins_ruleK true (Rd.const 0) (Rd.const 300) (Rd.const 450) (Rd.const (100 : Nat))
    (Rd.const 0) (Rd.const 300) (Rd.const 450) (Rd.const (100 : Nat))
    (pulse 0 2000) (fun _ => true) (sAdv true 500 4000) wS wD 1000 3000 500 4000 1400 3300 700
    (sAdv_stable true 500 4000) witness_luteqS witness_luteqD (by simp [Rd.const])
    (fun u h1 h2 => witness_sel.1 u (by simpa [Rd.const] using h1) h2) (by decide)
    (by simp [Rd.const]) (by simp [Rd.const]) (by decide) witness_sel.2 (by decide)
    (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const])
    (by simp [Rd.const])).2
  exact unsel_low false true (by decide) _ _ _ (by simp [Rd.const]) _ _ _ h (run_rest _ 100 (by decide))

end Formal.Timing.RuleK
