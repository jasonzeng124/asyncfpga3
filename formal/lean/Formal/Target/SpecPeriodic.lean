import Formal.Target.SpecRunt
import Formal.Net.Periodic

/-!
# Eventually periodic behaviours under H_RUNT(w): from a finite window to every time (shard A, 2026-11-09)

**Problem, plainly.** Below κ = 0.40 the known adversary on THE target does not deadlock: the circuit oscillates for
ever and never answers (a livelock; shard B, JOURNAL-B 2026-11-08 17:2x). Such a run is infinite, but if every node
is periodic with period `Q` from some time `t0` on, it is finite data. This file reduces "it is a `GateOKRuntOn`
behaviour" (Spec's gate relation, with the H_RUNT(w) read restriction on a class `L` of gates) to checks on a
finite window, so that a Lean witness of a livelock needs only finitely many kernel checks.

**Proved (generic, no data).**
* `gateOKRunt_of_window` (the periodic extension): let the gate's output and input nodes be `Q`-periodic from `t0`, and let the read maps
  `f` of one gate be monotone, satisfy every clause of the gate relation at every `t ∈ [g.start, V + Q)` (`CondAt`),
  with `V ≥ g.start`, `V ≥ t0`, the *seam* `f i (V + Q - 1) ≤ f i V + Q` and the *floor* `t0 + w ≤ f i V`. Then the
  gate satisfies `GateOKRuntOn L w p c g x` at every time: the read map is extended by `f i (t + Q) = f i t + Q`.
* `condAt_transfer`: the window clauses transfer from a behaviour `y` to a behaviour `x` that agrees with it on
  `[0, H)`, for `t < U` with `U + w ≤ H` (a pulse narrower than `w` around a read before `U` ends before `H`).
* `sigQ_eq_unr`: C's eventually periodic code `sigQ` (Formal.Net.Periodic) equals, below `t0 + m·Q`, the finite code
  with the period unrolled `m` times (`unr`).

**Not shown here.** Any particular run; the environment, arbiter and conclusion clauses.
-/

namespace Formal.Target.SpecPeriodic
open Formal.Target Formal.Net.Periodic

/-! ## The gate relation at one time -/

/-- Every clause of `GateOKRuntOn L w p c g x` at time `t`, for read maps `f`. -/
def CondAt (L : Gate → Bool) (w : Nat) (p : DelayPar) (c : ℚ) (g : Gate) (x : Beh) (f : Nat → Nat → Nat)
    (t : Nat) : Prop :=
  (∀ i, i < g.k → f i t ≤ t ∧ Adm p c (g.arcs.getD i default) (t - f i t) ∧
      (L g = true → NoRuntRead w (x (g.ins.getD i 0)) (f i t))) ∧
    x g.out t = g.init.testBit (addr g.k fun i => x (g.ins.getD i 0) (f i t))

/-! ## The periodic extension of a read map -/

/-- `f` below `V`; from `V` on, `f` on `[V, V + Q)` shifted by whole periods. -/
def ext (Q V : Nat) (f : Nat → Nat) (t : Nat) : Nat :=
  if t < V then f t else f (V + (t - V) % Q) + (t - V) / Q * Q

theorem ext_lt {Q V : Nat} (hQ : 0 < Q) (f : Nat → Nat) {t : Nat} (ht : t < V + Q) : ext Q V f t = f t := by
  unfold ext
  split
  · rfl
  · rename_i h
    rw [Nat.mod_eq_of_lt (by omega), Nat.div_eq_of_lt (by omega)]
    rw [show V + (t - V) = t by omega]; simp

theorem ext_shift {Q V : Nat} (hQ : 0 < Q) (f : Nat → Nat) {t : Nat} (ht : V ≤ t) :
    ext Q V f (t + Q) = ext Q V f t + Q := by
  unfold ext
  rw [if_neg (by omega), if_neg (by omega)]
  rw [show t + Q - V = (t - V) + Q by omega, Nat.add_mod_right, Nat.add_div_right _ hQ, Nat.succ_mul]
  omega

/-- For `t ≥ V + Q`, `ext t = ext (t - Q) + Q`. -/
theorem ext_back {Q V : Nat} (hQ : 0 < Q) (f : Nat → Nat) {t : Nat} (ht : V + Q ≤ t) :
    ext Q V f t = ext Q V f (t - Q) + Q := by
  have := ext_shift hQ f (V := V) (t := t - Q) (by omega)
  rwa [show t - Q + Q = t by omega] at this

theorem ext_mono {Q V : Nat} (hQ : 0 < Q) {f : Nat → Nat} (hm : Monotone f) (hseam : f (V + Q - 1) ≤ f V + Q) :
    Monotone (ext Q V f) := by
  apply monotone_nat_of_le_succ
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    by_cases h1 : t + 1 < V + Q
    · rw [ext_lt hQ f h1, ext_lt hQ f (by omega)]; exact hm (by omega)
    · by_cases h2 : t + 1 = V + Q
      · have e1 : ext Q V f t = f t := ext_lt hQ f (t := t) (by omega)
        have e2 : ext Q V f (t + 1) = f V + Q := by
          rw [h2, ext_shift hQ f (le_refl V), ext_lt hQ f (t := V) (by omega)]
        rw [e1, e2, show t = V + Q - 1 by omega]; exact hseam
      · rw [ext_back hQ f (t := t) (by omega), ext_back hQ f (t := t + 1) (by omega)]
        have := ih (t - Q) (by omega)
        rw [show t - Q + 1 = t + 1 - Q by omega] at this
        omega

/-! ## Periodic signals and pulses -/

/-- A pulse late enough is a pulse one period earlier. -/
theorem pulse_back {s : Sig} {Q t0 a b : Nat} (hper : ∀ t, t0 ≤ t → s (t + Q) = s t) (ha : t0 + Q + 1 ≤ a)
    (hp : Pulse s a b) : Pulse s (a - Q) (b - Q) := by
  obtain ⟨hab, hc, hpre, hend⟩ := hp
  have e : ∀ t, t0 + Q ≤ t → s (t - Q) = s t := fun t ht => by
    have := hper (t - Q) (by omega); rw [show t - Q + Q = t by omega] at this; exact this.symm
  refine ⟨by omega, fun t h1 h2 => ?_, fun _ => ?_, ?_⟩
  · rw [← hper t (by omega), hc (t + Q) (by omega) (by omega), e a (by omega)]
  · rw [show a - Q - 1 = a - 1 - Q by omega, e (a - 1) (by omega), e a (by omega)]
    exact hpre (by omega)
  · rw [e b (by omega), e a (by omega)]; exact hend

/-! ## The periodic extension theorem -/

theorem gateOKRunt_of_window {L : Gate → Bool} {w : Nat} {p : DelayPar} {c : ℚ} {g : Gate} {x : Beh}
    {Q t0 V : Nat} (hQ : 0 < Q) (hpo : ∀ t, t0 ≤ t → x g.out (t + Q) = x g.out t)
    (hpi : ∀ i, i < g.k → ∀ t, t0 ≤ t → x (g.ins.getD i 0) (t + Q) = x (g.ins.getD i 0) t)
    {f : Nat → Nat → Nat} (hmono : ∀ i, i < g.k → Monotone (f i))
    (hV : g.start p ≤ V) (ht0 : t0 ≤ V)
    (hwin : ∀ t, g.start p ≤ t → t < V + Q → CondAt L w p c g x f t)
    (hseam : ∀ i, i < g.k → f i (V + Q - 1) ≤ f i V + Q)
    (hfloor : ∀ i, i < g.k → t0 + w ≤ f i V) :
    GateOKRuntOn L w p c g x := by
  refine ⟨fun i => ext Q V (f i), fun i hi => ext_mono hQ (hmono i hi) (hseam i hi), ?_⟩
  -- the floor of the extended read map from `V` on
  have hfl : ∀ i, i < g.k → ∀ t, V ≤ t → t0 + w ≤ ext Q V (f i) t := by
    intro i hi t ht
    have := ext_mono hQ (hmono i hi) (hseam i hi) ht
    rw [ext_lt hQ _ (by omega : V < V + Q)] at this
    have := hfloor i hi; omega
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro hst
    dsimp only at ih ⊢
    by_cases ht : t < V + Q
    · obtain ⟨h1, h2⟩ := hwin t hst ht
      refine ⟨fun i hi => ?_, ?_⟩
      · rw [ext_lt hQ _ ht]; exact h1 i hi
      · rw [h2]; congr 1
        apply Formal.Timing.SpecSettle.addr_congr
        intro i _; rw [ext_lt hQ _ ht]
    · obtain ⟨h1, h2⟩ := ih (t - Q) (by omega) (by omega)
      have hb : ∀ i, ext Q V (f i) t = ext Q V (f i) (t - Q) + Q := fun i => ext_back hQ _ (by omega)
      refine ⟨fun i hi => ⟨?_, ?_, fun hl => ?_⟩, ?_⟩
      · rw [hb i]; have := (h1 i hi).1; omega
      · rw [hb i, show t - (ext Q V (f i) (t - Q) + Q) = t - Q - ext Q V (f i) (t - Q) by omega]
        exact (h1 i hi).2.1
      · intro a b hpl hw ⟨hu1, hu2⟩
        have hfl2 := hfl i hi (t - Q) (by omega)
        rw [hb i] at hu1 hu2
        by_cases ha : t0 + Q + 1 ≤ a
        · have hp' := pulse_back (hpi i hi) ha hpl
          exact (h1 i hi).2.2 hl (a - Q) (b - Q) hp' (by omega) ⟨by omega, by omega⟩
        · omega
      · have e1 : x g.out t = x g.out (t - Q) := by
          have := hpo (t - Q) (by omega); rwa [show t - Q + Q = t by omega] at this
        rw [e1, h2]; congr 1
        apply Formal.Timing.SpecSettle.addr_congr
        intro i hi
        rw [hb i]
        exact (hpi i hi _ (by have := hfl i hi (t - Q) (by omega); omega)).symm

/-! ## Agreement on a window -/

theorem pulse_transfer {s s' : Sig} {H a b : Nat} (hag : ∀ t, t < H → s t = s' t) (hb : b < H)
    (hp : Pulse s a b) : Pulse s' a b := by
  obtain ⟨hab, hc, hpre, hend⟩ := hp
  refine ⟨hab, fun t h1 h2 => ?_, fun h0 => ?_, ?_⟩
  · rw [← hag t (by omega), ← hag a (by omega)]; exact hc t h1 h2
  · rw [← hag (a - 1) (by omega), ← hag a (by omega)]; exact hpre h0
  · rw [← hag b hb, ← hag a (by omega)]; exact hend

/-- The window clauses at `t < U` transfer to a behaviour that agrees on `[0, H)`, `U + w ≤ H`. -/
theorem condAt_transfer {L : Gate → Bool} {w : Nat} {p : DelayPar} {c : ℚ} {g : Gate} {x y : Beh}
    {f : Nat → Nat → Nat} {U H t : Nat} (hag : ∀ n t, t < H → x n t = y n t) (hUH : U + w ≤ H) (htU : t < U)
    (h : CondAt L w p c g y f t) : CondAt L w p c g x f t := by
  obtain ⟨h1, h2⟩ := h
  refine ⟨fun i hi => ⟨(h1 i hi).1, (h1 i hi).2.1, fun hl a b hpl hw hu => ?_⟩, ?_⟩
  · have hle := (h1 i hi).1
    have hbH : b < H := by omega
    exact (h1 i hi).2.2 hl a b (pulse_transfer (fun t ht => hag _ t ht) hbH hpl) hw hu
  · rw [hag _ _ (by omega), h2]; congr 1
    apply Formal.Timing.SpecSettle.addr_congr
    intro i hi
    have := (h1 i hi).1
    exact (hag _ _ (by omega)).symm

/-! ## Unrolling an eventually periodic code -/

/-- The period's transitions repeated `m` times. -/
def unr (Q : Nat) (B : List Nat) : Nat → List Nat
  | 0 => []
  | m + 1 => unr Q B m ++ B.map (· + m * Q)

theorem countP_map_add (t s : Nat) : ∀ B : List Nat,
    ((B.map (· + s)).countP fun x => decide (x ≤ t)) = (B.map fun p => if p + s ≤ t then 1 else 0).sum
  | [] => rfl
  | p :: B => by
    simp only [List.map_cons, List.countP_cons, List.sum_cons, countP_map_add t s B]
    by_cases h : p + s ≤ t <;> simp [h] <;> omega

theorem sum_map_add (B : List Nat) (f g : Nat → Nat) :
    (B.map fun p => f p + g p).sum = (B.map f).sum + (B.map g).sum := by
  induction B with
  | nil => rfl
  | cons p B ih => simp only [List.map_cons, List.sum_cons, ih]; omega

/-- Counting the unrolled transitions: each periodic time `p` contributes `min m (cnt1 Q p t)`. -/
theorem countP_unr {Q : Nat} (hQ : 0 < Q) (B : List Nat) (t : Nat) : ∀ m : Nat,
    ((unr Q B m).countP fun x => decide (x ≤ t)) = (B.map fun p => min m (cnt1 Q p t)).sum
  | 0 => by simp [unr]
  | m + 1 => by
    simp only [unr, List.countP_append, countP_unr hQ B t m, countP_map_add, ← sum_map_add]
    congr 1
    apply List.map_congr_left
    intro p _
    unfold cnt1
    by_cases h : p ≤ t
    · rw [if_pos h]
      by_cases h2 : p + m * Q ≤ t
      · have : m ≤ (t - p) / Q := (Nat.le_div_iff_mul_le hQ).mpr (by rw [Nat.mul_comm] at *; omega)
        rw [if_pos h2]; omega
      · have : (t - p) / Q < m := (Nat.div_lt_iff_lt_mul hQ).mpr (by rw [Nat.mul_comm] at *; omega)
        rw [if_neg h2]; omega
    · rw [if_neg h, if_neg (by omega)]; simp

/-- **Unrolling**: below `t0 + m·Q`, C's periodic code is the finite code with the period unrolled `m` times. -/
theorem sigQ_eq_unr {Q t0 : Nat} (hQ : 0 < Q) (v0 : Bool) (A B : List Nat) (hB : ∀ p ∈ B, t0 ≤ p) (m t : Nat)
    (ht : t < t0 + m * Q) : sigQ Q v0 A B t = (v0 != (((A ++ unr Q B m).countP fun x => decide (x ≤ t)) % 2 == 1)) := by
  unfold sigQ
  rw [List.countP_append, countP_unr hQ B t m]
  congr 4
  refine congrArg List.sum (List.map_congr_left ?_)
  intro p hp
  have := hB p hp
  unfold cnt1
  split
  · have : (t - p) / Q < m := (Nat.div_lt_iff_lt_mul hQ).mpr (by omega)
    omega
  · simp

end Formal.Target.SpecPeriodic
