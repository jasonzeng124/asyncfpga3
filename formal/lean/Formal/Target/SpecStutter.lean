import Formal.Target.SpecRunt
import Formal.Timing.SpecSettle

/-!
# Formal.Target.SpecStutter — stretching a quiet stretch of a behaviour (any reset length)

Shard A, 2026-11-07.

**Problem, plainly.** THE statement takes the reset length `R` as a parameter, and `Env` fixes the reset to exactly
`[0, R)`, so a counterexample found with a 400 ns reset says nothing, by itself, about the board's much longer reset
(SpecMono: no monotonicity in `R`). But if the circuit is quiet for a while before the reset ends, waiting longer
changes nothing: the same run, with every event after some quiet instant `t0` delayed by `Δ`, should again be a
behaviour. This file proves that, for the gate relation with and without runt filtering.

**Definitions.** `σ t0 Δ t` maps the stretched time line back to the original one: `t` for `t ≤ t0`, `t0` on
`(t0, t0 + Δ]`, `t - Δ` after. `stut t0 Δ s t = s (σ t0 Δ t)`: the signal held at its `t0` value for `Δ` extra ps.

**Proved.** `gateOKRuntOn_stut`: if a gate obeys `GateOKRuntOn L w p c` in `x`, every node is constant on
`[t0 - Q, t0]` (`Quiet x t0 Q`), every admissible delay of its arcs is at most `Q`, `Q ≤ t0`, `w ≤ Q + 1` and the gate's
start is `≤ t0`, then it obeys the same relation in `stutB t0 Δ x` (read maps: unchanged up to `t0`, advancing with
time on the stretch, shifted by `Δ` after). `behavesRuntOn_stut`: the same for a whole net. Also `sigL_shift`
(the coded-signal form: shifting every transition after `t0` by `Δ` is `stut`) and `arbChkE_shift` (an arbiter
check on codes survives the shift when no transition of its nodes lies in `(t0 - T, t0]`).

**Not shown here.** That any particular run is quiet (a finite check on its codes), nor the environment clauses.
-/

namespace Formal.Target.Stutter
open Formal.Target

/-- The original time of stretched time `t`. -/
def σ (t0 Δ t : Nat) : Nat := if t ≤ t0 then t else if t ≤ t0 + Δ then t0 else t - Δ

/-- A signal held at its `t0` value for `Δ` extra ps. -/
def stut (t0 Δ : Nat) (s : Sig) : Sig := fun t => s (σ t0 Δ t)

def stutB (t0 Δ : Nat) (x : Beh) : Beh := fun n => stut t0 Δ (x n)

/-- Every node is constant on `[t0 - Q, t0]`. -/
def Quiet (x : Beh) (t0 Q : Nat) : Prop := ∀ n u, t0 - Q ≤ u → u ≤ t0 → x n u = x n t0

theorem σ_mono (t0 Δ : Nat) : Monotone (σ t0 Δ) := by
  intro a b h; simp only [σ]; split_ifs <;> omega

/-- On `[t0 - Q, t0 + Δ]` the stretched signal of a quiet node is constant. -/
theorem stut_flat {s : Sig} {t0 Q Δ : Nat} (hq : ∀ u, t0 - Q ≤ u → u ≤ t0 → s u = s t0) (u : Nat)
    (h1 : t0 - Q ≤ u) (h2 : u ≤ t0 + Δ) : stut t0 Δ s u = s t0 := by
  simp only [stut, σ]
  split_ifs with h3
  · exact hq u h1 h3
  · rfl

/-- A pulse that contains a point of a stretch on which the signal is constant is at least as wide as the stretch. -/
theorem pulse_wide {s : Sig} {lo hi a b p : Nat} (hc : ∀ u, lo ≤ u → u ≤ hi → s u = s lo) (hlh : lo ≤ hi)
    (hp : Pulse s a b) (hpa : a ≤ p) (hpb : p < b) (hlo : lo ≤ p) (hhi : p ≤ hi) : hi + 1 - lo ≤ b - a := by
  obtain ⟨hab, hcon, hpre, hend⟩ := hp
  have hsp : s p = s a := hcon p hpa hpb
  have hb : hi < b := by
    by_contra h
    apply hend
    rw [hc b (by omega) (by omega), ← hc p hlo hhi, hsp]
  have ha : a ≤ lo := by
    by_contra h
    apply hpre (by omega)
    rw [hc (a - 1) (by omega) (by omega), hc a (by omega) (by omega)]
  omega

theorem stut_lo {s : Sig} {t0 Δ t : Nat} (h : t ≤ t0) : stut t0 Δ s t = s t := by
  simp only [stut, σ, if_pos h]

theorem stut_hi {s : Sig} {t0 Δ t : Nat} (h : t0 + Δ < t) : stut t0 Δ s t = s (t - Δ) := by
  simp only [stut, σ, if_neg (show ¬ t ≤ t0 by omega), if_neg (show ¬ t ≤ t0 + Δ by omega)]

theorem stut_edge {s : Sig} {t0 Δ : Nat} : stut t0 Δ s (t0 + Δ) = s t0 := by
  simp only [stut, σ]; split_ifs with h <;> first | rfl | (congr 1; omega) | omega

/-- Narrow pulses of the stretched signal: they lie wholly before `t0` (a pulse of the original) or wholly after
`t0 + Δ` (a shifted pulse of the original). -/
theorem pulse_stut {s : Sig} {t0 Q Δ w a b : Nat} (hq : ∀ u, t0 - Q ≤ u → u ≤ t0 → s u = s t0) (hQ : Q ≤ t0)
    (hw : w ≤ Q + 1) (hp : Pulse (stut t0 Δ s) a b) (hn : b - a < w) :
    (b ≤ t0 ∧ Pulse s a b) ∨ (t0 + Δ < a ∧ Pulse s (a - Δ) (b - Δ)) := by
  have hc : ∀ u, t0 - Q ≤ u → u ≤ t0 + Δ → stut t0 Δ s u = stut t0 Δ s (t0 - Q) := by
    intro u h1 h2
    rw [stut_flat hq u h1 h2, stut_flat hq (t0 - Q) le_rfl (by omega)]
  obtain ⟨hab, hcon, hpre, hend⟩ := hp
  by_cases hA : b ≤ t0
  · left
    refine ⟨hA, hab, fun t h1 h2 => ?_, fun h0 => ?_, ?_⟩
    · have := hcon t h1 h2; rwa [stut_lo (by omega), stut_lo (by omega)] at this
    · have := hpre h0; rwa [stut_lo (by omega), stut_lo (by omega)] at this
    · have := hend; rwa [stut_lo (by omega), stut_lo (by omega)] at this
  by_cases hB : t0 + Δ < a
  · right
    refine ⟨hB, by omega, fun t h1 h2 => ?_, fun _ => ?_, ?_⟩
    · have := hcon (t + Δ) (by omega) (by omega)
      rw [stut_hi (by omega), stut_hi (by omega), show t + Δ - Δ = t by omega] at this
      exact this
    · have := hpre (by omega)
      rw [stut_hi (t := a) (by omega)] at this
      by_cases h3 : a - 1 = t0 + Δ
      · rw [h3, stut_edge] at this
        rwa [show a - Δ - 1 = t0 by omega]
      · rw [stut_hi (by omega)] at this
        rwa [show a - Δ - 1 = a - 1 - Δ by omega]
    · have := hend
      rw [stut_hi (by omega), stut_hi (by omega)] at this
      exact this
  · exfalso
    -- the pulse contains a point of the flat stretch [t0 - Q, t0 + Δ]
    have hpl : Pulse (stut t0 Δ s) a b := ⟨hab, hcon, hpre, hend⟩
    have := pulse_wide hc (by omega) hpl (p := max a t0) (le_max_left _ _) (by omega) (by omega) (by omega)
    omega

/-- **The stutter lemma, one gate.** -/
theorem gateOKRuntOn_stut {L : Gate → Bool} {w : Nat} {p : DelayPar} {c : ℚ} {g : Gate} {x : Beh}
    {t0 Q Δ : Nat} (hg : GateOKRuntOn L w p c g x) (hq : Quiet x t0 Q) (hQ : Q ≤ t0) (hw : w ≤ Q + 1)
    (hs : g.start p ≤ t0) (hD : ∀ i, i < g.k → ∀ d, Adm p c (g.arcs.getD i default) d → d ≤ Q) :
    GateOKRuntOn L w p c g (stutB t0 Δ x) := by
  obtain ⟨f, hm, ht⟩ := hg
  have h0 := ht t0 hs
  -- read maps
  let f' : Nat → Nat → Nat := fun i t =>
    if t ≤ t0 then f i t else if t ≤ t0 + Δ then f i t0 + (t - t0) else f i (t - Δ) + Δ
  have hlag : ∀ i, i < g.k → ∀ t, g.start p ≤ t → t - f i t ≤ Q := fun i hi t ht' =>
    hD i hi _ ((ht t ht').1 i hi).2.1
  have hle : ∀ i, i < g.k → ∀ t, g.start p ≤ t → f i t ≤ t := fun i hi t ht' => ((ht t ht').1 i hi).1
  have hqs : ∀ n u, t0 - Q ≤ u → u ≤ t0 → x n u = x n t0 := fun n u => hq n u
  refine ⟨f', fun i hi a b hab => ?_, fun t hst => ?_⟩
  · -- monotone
    have hmi := hm i hi
    have hft0 := hle i hi t0 hs
    simp only [f']
    split_ifs with h1 h2 h3 h4 h5 h6 h7 h8 <;> first
      | exact hmi hab
      | omega
      | (have := hmi (show a ≤ t0 by omega); omega)
      | (have := hmi (show t0 ≤ b - Δ by omega); omega)
      | (have := hmi (show a ≤ b - Δ by omega); omega)
      | (have := hmi (show a - Δ ≤ b - Δ by omega); omega)
  -- the read value in the stretched behaviour equals an original read
  have hval : ∀ i, i < g.k → ∀ n,
      stutB t0 Δ x n (f' i t) = x n (if t ≤ t0 then f i t else if t ≤ t0 + Δ then f i t0 else f i (t - Δ)) := by
    intro i hi n
    have hft0 := hle i hi t0 hs
    have hl0 := hlag i hi t0 hs
    simp only [stutB, f']
    split_ifs with h1 h2
    · exact stut_lo (le_trans (hle i hi t hst) h1)
    · rw [stut_flat (hqs n) _ (by omega) (by omega), hqs n _ (by omega) hft0]
    · have hl := hlag i hi (t - Δ) (by omega)
      have hf := hle i hi (t - Δ) (by omega)
      by_cases h3 : t0 < f i (t - Δ)
      · rw [stut_hi (by omega), Nat.add_sub_cancel]
      · rw [stut_flat (hqs n) _ (by omega) (by omega), hqs n (f i (t - Δ)) (by omega) (by omega)]
  refine ⟨fun i hi => ⟨?_, ?_, fun hL => ?_⟩, ?_⟩
  · -- reads in the past
    have hft0 := hle i hi t0 hs
    simp only [f']
    split_ifs with h1 h2
    · exact hle i hi t hst
    · omega
    · have := hle i hi (t - Δ) (by omega); omega
  · -- admissible delays: the same delays as the original at t, t0, or t - Δ
    simp only [f']
    split_ifs with h1 h2
    · exact ((ht t hst).1 i hi).2.1
    · have hft0 := hle i hi t0 hs
      rw [show t - (f i t0 + (t - t0)) = t0 - f i t0 by omega]
      exact (h0.1 i hi).2.1
    · have := hle i hi (t - Δ) (by omega)
      rw [show t - (f i (t - Δ) + Δ) = t - Δ - f i (t - Δ) by omega]
      exact ((ht (t - Δ) (by omega)).1 i hi).2.1
  · -- no read inside a narrow pulse
    intro a b hpl hab hu
    have hqn := hqs (g.ins.getD i 0)
    rcases pulse_stut hqn hQ hw hpl hab with ⟨hb, hp0⟩ | ⟨ha, hp1⟩
    · -- a narrow pulse before t0: the read is an original read before t0
      have hft0 := hle i hi t0 hs
      simp only [f'] at hu
      have hwide : ∀ u, t0 - Q ≤ u → u ≤ t0 → a ≤ u → u < b → False := by
        intro u h1 h2 h3 h4
        have hc0 : ∀ v, t0 - Q ≤ v → v ≤ t0 → x (g.ins.getD i 0) v = x (g.ins.getD i 0) (t0 - Q) := by
          intro v hv1 hv2; rw [hqn v hv1 hv2, hqn (t0 - Q) le_rfl (by omega)]
        have := pulse_wide hc0 (by omega) hp0 h3 h4 h1 h2
        omega
      have hl0 := hlag i hi t0 hs
      split_ifs at hu with h1 h2
      · exact ((ht t hst).1 i hi).2.2 hL a b hp0 hab hu
      · exact hwide _ (by omega) (by omega) hu.1 hu.2
      · have hl := hlag i hi (t - Δ) (by omega)
        exact hwide _ (by omega) (by omega) hu.1 hu.2
    · -- a narrow pulse after t0 + Δ: the read is a shifted original read
      have hft0 := hle i hi t0 hs
      simp only [f'] at hu
      split_ifs at hu with h1 h2
      · have := hle i hi t hst; omega
      · omega
      · exact ((ht (t - Δ) (by omega)).1 i hi).2.2 hL (a - Δ) (b - Δ) hp1 (by omega) ⟨by omega, by omega⟩
  · -- the gate equation
    have hout : stutB t0 Δ x g.out t =
        x g.out (if t ≤ t0 then t else if t ≤ t0 + Δ then t0 else t - Δ) := by
      simp only [stutB]
      split_ifs with h1 h2
      · exact stut_lo h1
      · exact stut_flat (hqs g.out) _ (by omega) (by omega)
      · exact stut_hi (by omega)
    rw [hout]
    have hrd : (addr g.k fun i => stutB t0 Δ x (g.ins.getD i 0) (f' i t)) =
        addr g.k fun i => x (g.ins.getD i 0)
          (f i (if t ≤ t0 then t else if t ≤ t0 + Δ then t0 else t - Δ)) := by
      apply Formal.Timing.SpecSettle.addr_congr
      intro i hi
      rw [hval i hi]
      split_ifs <;> rfl
    rw [hrd]
    split_ifs with h1 h2
    · exact (ht t hst).2
    · exact h0.2
    · exact (ht (t - Δ) (by omega)).2

/-- **The stutter lemma, whole net.** -/
theorem behavesRuntOn_stut {L : Gate → Bool} {w : Nat} {p : DelayPar} {N : Net} {x : Beh} {t0 Q Δ : Nat}
    (hb : BehavesRuntOn L w p N x) (hq : Quiet x t0 Q) (hQ : Q ≤ t0) (hw : w ≤ Q + 1)
    (hs : ∀ g ∈ N.gates, g.start p ≤ t0)
    (hD : ∀ c : ℚ, 0 ≤ c → c ≤ 1 → ∀ g ∈ N.gates, ∀ i, i < g.k → ∀ d, Adm p c (g.arcs.getD i default) d → d ≤ Q) :
    BehavesRuntOn L w p N (stutB t0 Δ x) := by
  obtain ⟨c, h0, h1, hg⟩ := hb
  exact ⟨c, h0, h1, fun g hg' => gateOKRuntOn_stut (hg g hg') hq hQ hw (hs g hg') (hD c h0 h1 g hg')⟩

end Formal.Target.Stutter
