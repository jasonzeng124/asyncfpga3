import Formal.Core.XAudit.Events6Gate
import Wip.E8Hyp.T1

namespace Formal.Core.XAudit.Events8Bridge

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp Mono)
open Formal.Core.XAudit.Events2Pin (SatPin PinRel PinTab shift_warp)
open Formal.Core.XAudit.Events6 (plG)

/-- The trace built by recursion in time: time 0 is `σ0`, a driven wire is its gate's
INIT of the inputs `lo` steps earlier, an undriven wire is `inp`. -/
def xs (d : Design) (σ0 : Fin d.n → Bool) (inp : Fin d.n → Sig) : Nat → Fin d.n → Bool
  | 0, w => σ0 w
  | t + 1, w =>
    match d.gates.find? (fun g => decide (d.wire g.out = w)) with
    | some g => g.init.testBit (addr (fun p : Fin g.k =>
        xs d σ0 inp (t - (g.lo - 1)) (d.wire (g.ins.getD p.val 0))))
    | none => inp w (t + 1)
termination_by t => t
decreasing_by omega

theorem inj_of_nodup_map {α β : Type} (f : α → β) :
    ∀ {l : List α}, (l.map f).Nodup → ∀ {a b : α}, a ∈ l → b ∈ l → f a = f b → a = b
  | [], _, _, _, ha, _, _ => absurd ha List.not_mem_nil
  | c :: l, h, a, b, ha, hb, he => by
    rw [List.map_cons, List.nodup_cons] at h
    rcases List.mem_cons.mp ha with ha' | ha' <;> rcases List.mem_cons.mp hb with hb' | hb'
    · rw [ha', hb']
    · subst ha'; exact absurd (List.mem_map.mpr ⟨b, hb', he.symm⟩) h.1
    · subst hb'; exact absurd (List.mem_map.mpr ⟨a, ha', he⟩) h.1
    · exact inj_of_nodup_map f h.2 ha' hb' he

theorem find_drv {d : Design} (hwf : d.WF) (hnd : (d.gates.map GSpec.out).Nodup) {g : GSpec}
    (hg : g ∈ d.gates) : d.gates.find? (fun g' => decide (d.wire g'.out = d.wire g.out)) = some g := by
  cases h : d.gates.find? (fun g' => decide (d.wire g'.out = d.wire g.out)) with
  | none =>
    rw [List.find?_eq_none] at h
    exact absurd (by simp) (h g hg)
  | some g' =>
    have hm := List.mem_of_find?_eq_some h
    have hp := List.find?_some h
    simp only [decide_eq_true_eq] at hp
    have e1 := Design.wire_val d (hwf g' hm).2.2.1
    have e2 := Design.wire_val d (hwf g hg).2.2.1
    have ho : g'.out = g.out := by rw [← e1, ← e2, hp]
    rw [inj_of_nodup_map GSpec.out hnd hm hg ho]

/-- **Existence (non-vacuity of SatPin, constants and reset).** On a well-formed netlist
with one driver per wire, every time-0 fixpoint `σ0` extends, for any undriven-wire
inputs agreeing with it at time 0, to a `SatPin d plG` behaviour (each pin read with
the fixed shift `t - lo`). -/
theorem satPin_exists {d : Design} (hwf : d.WF) (hnd : (d.gates.map GSpec.out).Nodup)
    (σ0 : Fin d.n → Bool)
    (hfix : ∀ g ∈ d.gates, σ0 (d.wire g.out) =
      g.init.testBit (addr (fun p : Fin g.k => σ0 (d.wire (g.ins.getD p.val 0)))))
    (inp : Fin d.n → Sig) (hi0 : ∀ w, inp w 0 = σ0 w) :
    ∃ x : Fin d.n → Sig, SatPin d plG x ∧ (∀ w, x w 0 = σ0 w) ∧
      ∀ w, (∀ g ∈ d.gates, d.wire g.out ≠ w) → ∀ t, x w t = inp w t := by
  refine ⟨fun w t => xs d σ0 inp t w, ?_, fun w => by simp [xs], ?_⟩
  · intro g hg
    have hw := hwf g hg
    refine ⟨fun _ t => t - g.lo, fun i _ => shift_warp _ _ hw.2.2.2.2.1, fun t => ?_⟩
    cases t with
    | zero =>
      show xs d σ0 inp 0 _ = _
      rw [show xs d σ0 inp 0 (d.wire g.out) = σ0 (d.wire g.out) by simp [xs], hfix g hg]
      congr 2
      funext p
      simp [xs]
    | succ t =>
      show xs d σ0 inp (t + 1) _ = _
      rw [xs, find_drv hwf hnd hg]
      simp only
      congr 2
      funext p
      have : t + 1 - g.lo = t - (g.lo - 1) := by have := hw.2.2.2.1; omega
      rw [this]
  · intro w hw t
    cases t with
    | zero => simp [xs, hi0]
    | succ t =>
      show xs d σ0 inp (t + 1) w = _
      have hn : d.gates.find? (fun g => decide (d.wire g.out = w)) = none := by
        rw [List.find?_eq_none]; intro g hg; simpa using hw g hg
      rw [xs, hn]

/-- **Necessity**: the time-0 values of a `SatPin` behaviour are a fixpoint (any band
table). Together with `satPin_exists`: `SatPin` behaviours with time-0 state `σ0` exist
iff `σ0` is a fixpoint. -/
theorem satPin_exists_iff {d : Design} (hwf : d.WF) (hnd : (d.gates.map GSpec.out).Nodup)
    (σ0 : Fin d.n → Bool) :
    (∃ x : Fin d.n → Sig, SatPin d plG x ∧ ∀ w, x w 0 = σ0 w) ↔
      ∀ g ∈ d.gates, σ0 (d.wire g.out) =
        g.init.testBit (addr (fun p : Fin g.k => σ0 (d.wire (g.ins.getD p.val 0)))) := by
  constructor
  · rintro ⟨x, hs, h0⟩ g hg
    have := Formal.Core.XAudit.Events8Bridge.satPin_origin hs g hg
    rw [h0] at this
    simp only [h0] at this
    exact this
  · intro hfix
    obtain ⟨x, hs, h0, _⟩ := satPin_exists hwf hnd σ0 hfix (fun w _ => σ0 w) (fun _ => rfl)
    exact ⟨x, hs, h0⟩

/-- **The outer hypotheses of `design_verdict8` that concern `x` alone** (SatPin, the
constant wires 0 / 1, reset high until `T`) are jointly satisfiable on every well-formed,
singly-driven netlist whose constant and reset wires are undriven, as soon as there is a
time-0 fixpoint with wire 0 low, wire 1 high and reset high. -/
theorem core_hyps_exist {d : Design} (hwf : d.WF) (hnd : (d.gates.map GSpec.out).Nodup)
    {rw T : Nat} (hT : 1 ≤ T) (h1rw : d.wire rw ≠ d.wire 1)
    (hu : ∀ g ∈ d.gates, d.wire g.out ≠ d.wire 0 ∧ d.wire g.out ≠ d.wire 1 ∧ d.wire g.out ≠ d.wire rw)
    (σ0 : Fin d.n → Bool)
    (hfix : ∀ g ∈ d.gates, σ0 (d.wire g.out) =
      g.init.testBit (addr (fun p : Fin g.k => σ0 (d.wire (g.ins.getD p.val 0)))))
    (s0 : σ0 (d.wire 0) = false) (s1 : σ0 (d.wire 1) = true) (sr : σ0 (d.wire rw) = true) :
    ∃ x : Fin d.n → Sig, SatPin d plG x ∧ (∀ t, x (d.wire 0) t = false) ∧
      (∀ t, x (d.wire 1) t = true) ∧ (∀ t, x (d.wire rw) t = decide (t < T)) := by
  have n01 : d.wire 1 ≠ d.wire 0 := fun h => by rw [h, s0] at s1; exact absurd s1 (by decide)
  have nr0 : d.wire rw ≠ d.wire 0 := fun h => by rw [h, s0] at sr; exact absurd sr (by decide)
  let inp : Fin d.n → Sig := fun w t =>
    if w = d.wire 0 then false else if w = d.wire 1 then true
    else if w = d.wire rw then decide (t < T) else σ0 w
  have hi0 : ∀ w, inp w 0 = σ0 w := by
    intro w
    by_cases a : w = d.wire 0
    · simp [inp, a, s0]
    · by_cases b : w = d.wire 1
      · simp [inp, a, b, s1]
      · by_cases c : w = d.wire rw
        · simp [inp, a, b, c, sr]; omega
        · simp [inp, a, b, c]
  obtain ⟨x, hs, _, hund⟩ := satPin_exists hwf hnd σ0 hfix inp hi0
  refine ⟨x, hs, fun t => ?_, fun t => ?_, fun t => ?_⟩
  · rw [hund _ (fun g hg => (hu g hg).1) t]; simp [inp]
  · rw [hund _ (fun g hg => (hu g hg).2.1) t]; simp [inp, n01]
  · rw [hund _ (fun g hg => (hu g hg).2.2) t]; simp [inp, nr0, h1rw]

/-! ### Negative control: SatPin can be unsatisfiable -/

/-- One inverter feeding itself (no reset): wire 2 = NOT wire 2. -/
def ringD : Design where
  m := 2
  gates := [{ name := "inv", k := 1, init := 1, ins := [2], out := 2, lo := 1, hi := 1 }]

/-- **`SatPin` has NO behaviour on an unreset inverter loop**: the time-0 fixpoint
`b = ¬b` does not exist. So the existence of a time-0 fixpoint (a reset state) is a
real condition, not a formality. -/
theorem ringD_unsat : ¬ ∃ x : Fin ringD.n → Sig, SatPin ringD plG x := by
  rintro ⟨x, hs⟩
  have h := Formal.Core.XAudit.Events8Bridge.satPin_origin hs _ (List.mem_singleton_self _)
  have ha : ∀ y : Fin 1 → Bool, addr y = (y 0).toNat := by intro y; simp [addr]
  simp only [ha] at h
  revert h
  cases x (ringD.wire 2) 0 <;> decide

end Formal.Core.XAudit.Events8Bridge
