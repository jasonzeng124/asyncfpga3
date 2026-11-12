import Formal.Timing.ChainSettle

/-!
# C-10o part 2: the pulse, a closed form, and a kernel-checked runt

Instantiates `ChainSettle` (the exact network theorem) for the input pulse of a delay
chain and for the smallest side-tapped chain, and checks the converse on numbers.

* **H_PULSE** (the environment, an instance of H_INPUT): the chain input is 1 before `F`
  (the previous token: the chain is full), 0 on `[F, F + T)`, 1 from `F + T` (the
  handshake brings it back up). `pulse F T`. In the routed rows `T` is bounded below by
  chainck's late side (the tail's earliest fall plus the shortest routed path back to
  the input: H_REUSE_CAUSAL, as rule F / Fd / Fc).
* `Lc_pulse`: the input's forced-low set is `[F, F + T)`.
* `net2`: node 0 = the input `a`, node 1 = the head `s1 = LUT1(a)` (arc `[hl, hh]`: route +
  LUT arc), node 2 = the tail `z = AND(s1, a)` (ripple arc `[rl, rh]`, tap arc `[pl, ph]`).
  This is `bd_delay #(.N(2), .FASTFALL(1))`, and by the network theorem the shape of every
  longer chain's last stage.
* **`chain2_Lc`** (closed form): `Lc z t ↔ t ∈ [F + hh + rh, F + T + hl + rl)` (if that
  ripple interval survives) `∨ t ∈ [F + ph, F + T + pl)` (the tap).
* **`chain2_settled_iff`** (exact closed form of H_CHAIN_SETTLED for N = 2): under the
  pulse-width side conditions (`hh < T`, `hh + rh < T + hl`, `ph < T`: every pulse is
  longer than the arc it crosses, so no interval vanishes),
  z is low on all of `[F + ph, F + T + hl + rl)` in EVERY run iff
  `hh + rh ≤ T + pl`: the head's latest fall, carried to z's chain pin, arrives no later
  than the input's next rise at z's tap pin. This is the per-stage form (shard B's
  H_GFLUSH, C-10k's rule Fd); `ChainSettle` gives the exact form for any chain.
* **`runt_example`** (kernel-checked counterexample, numbers of prjxray scale): head
  `[300, 400]`, hop `[200, 300]`, tap `[150, 250]`, input low for `T = 400` ps from
  `F = 1000`: there is a run (all hypotheses: BoundedDelay per arc, AND nodes, quiescent)
  in which z is low at 1250, HIGH at 1650 and low again at 1700: a runt, and the rise at
  1650 is 600 ps before the matched rise `F + T + hl + rl = 1900`.
  `settled_example`: the same chain with `T = 600` is settled (no runt in any run).
-/

namespace Formal.Timing.ChainSettle
open Formal.Net Formal.Timing

/-- H_PULSE: high before `F`, low on `[F, F + T)`, high from `F + T`. -/
def pulse (F T : Nat) : Trace := fun t => !(decide (F ≤ t ∧ t < F + T))

theorem pulse_false (F T t : Nat) : pulse F T t = false ↔ (F ≤ t ∧ t < F + T) := by
  unfold pulse; by_cases h : F ≤ t ∧ t < F + T <;> simp [h]

theorem Lc_pulse (net : Netlist) (F T t : Nat) :
    Lc net (pulse F T) 0 t ↔ (F ≤ t ∧ t < F + T) := by
  rw [Lc_zero, pulse_false]

theorem pulse_zero {F T : Nat} (hF : 0 < F) : pulse F T 0 = true := by
  unfold pulse; simp; omega

/-- The two-stage side-tapped chain (`bd_delay #(.N(2), .FASTFALL(1))`). -/
def net2 (hl hh rl rh pl ph : Nat) : Netlist :=
  ⟨[⟨0, 1, hl, hh⟩, ⟨1, 2, rl, rh⟩, ⟨0, 2, pl, ph⟩]⟩

theorem net2_wf {hl hh rl rh pl ph : Nat} (h1 : hl ≤ hh) (h2 : rl ≤ rh) (h3 : pl ≤ ph) :
    (net2 hl hh rl rh pl ph).WF := by
  intro a ha
  simp only [net2, List.mem_cons, List.not_mem_nil, or_false] at ha
  rcases ha with rfl | rfl | rfl <;> exact ⟨by simp, by assumption⟩

theorem chain2_Lc1 {hl hh rl rh pl ph : Nat} (h1 : hl ≤ hh) (h2 : rl ≤ rh) (h3 : pl ≤ ph)
    (F T t : Nat) :
    Lc (net2 hl hh rl rh pl ph) (pulse F T) 1 t ↔ (F + hh < F + T ∧ F + hh ≤ t ∧ t < F + T + hl) := by
  rw [Lc_pos (net2_wf h1 h2 h3) _ (by decide)]
  constructor
  · rintro ⟨k, a, hk, hd, hlw⟩
    rcases k with _ | _ | _ | k <;> simp [net2] at hk <;> subst hk <;> simp at hd
    have e : Lc (net2 hl hh rl rh pl ph) (pulse F T) 0 = fun w => F ≤ w ∧ w < F + T := by
      funext w; exact propext (Lc_pulse _ F T w)
    simp only at hlw; rw [e] at hlw
    exact (lowPin_Ico h1 F (F + T) t).1 hlw
  · intro h
    refine ⟨0, ⟨0, 1, hl, hh⟩, rfl, rfl, ?_⟩
    have e : Lc (net2 hl hh rl rh pl ph) (pulse F T) 0 = fun w => F ≤ w ∧ w < F + T := by
      funext w; exact propext (Lc_pulse _ F T w)
    simp only; rw [e]
    exact (lowPin_Ico h1 F (F + T) t).2 h

/-- **Closed form at the tail** (head pulse survives: `hh < T`). -/
theorem chain2_Lc {hl hh rl rh pl ph : Nat} (h1 : hl ≤ hh) (h2 : rl ≤ rh) (h3 : pl ≤ ph)
    {F T : Nat} (hT : hh < T) (t : Nat) :
    Lc (net2 hl hh rl rh pl ph) (pulse F T) 2 t ↔
      ((F + hh + rh < F + T + hl ∧ F + hh + rh ≤ t ∧ t < F + T + hl + rl) ∨
       (F + ph < F + T ∧ F + ph ≤ t ∧ t < F + T + pl)) := by
  have e1 : Lc (net2 hl hh rl rh pl ph) (pulse F T) 1 = fun w => F + hh ≤ w ∧ w < F + T + hl := by
    funext w; apply propext; rw [chain2_Lc1 h1 h2 h3]; omega
  have e0 : Lc (net2 hl hh rl rh pl ph) (pulse F T) 0 = fun w => F ≤ w ∧ w < F + T := by
    funext w; exact propext (Lc_pulse _ F T w)
  rw [Lc_pos (net2_wf h1 h2 h3) _ (by decide)]
  constructor
  · rintro ⟨k, a, hk, hd, hlw⟩
    rcases k with _ | _ | _ | k <;> simp [net2] at hk <;> subst hk <;> simp at hd
    · left; simp only at hlw; rw [e1] at hlw
      exact (lowPin_Ico h2 _ _ t).1 hlw
    · right; simp only at hlw; rw [e0] at hlw
      have := (lowPin_Ico h3 _ _ t).1 hlw; omega
  · rintro (h | h)
    · refine ⟨1, ⟨1, 2, rl, rh⟩, rfl, rfl, ?_⟩
      simp only; rw [e1]; exact (lowPin_Ico h2 _ _ t).2 h
    · refine ⟨2, ⟨0, 2, pl, ph⟩, rfl, rfl, ?_⟩
      simp only; rw [e0]; exact (lowPin_Ico h3 _ _ t).2 (by omega)

/-- **Exact closed form of H_CHAIN_SETTLED for N = 2.** -/
theorem chain2_settled_iff {hl hh rl rh pl ph : Nat} (h1 : hl ≤ hh) (h2 : rl ≤ rh)
    (h3 : pl ≤ ph) {F T : Nat} (hT : hh < T) (hrip : hh + rh < T + hl) (htap : ph < T) :
    (∀ sig, AndRun (net2 hl hh rl rh pl ph) (pulse F T) sig →
        ∀ t, F + ph ≤ t → t < F + T + hl + rl → sig 2 t = false) ↔ hh + rh ≤ T + pl := by
  rw [settled_iff (net2_wf h1 h2 h3)]
  unfold Settled
  constructor
  · intro h
    apply Classical.byContradiction; intro hne
    have := (chain2_Lc h1 h2 h3 hT (F + T + pl)).1 (h _ (by omega) (by omega))
    omega
  · intro h t ht1 ht2
    apply (chain2_Lc h1 h2 h3 hT t).2
    by_cases hc : t < F + T + pl
    · right; omega
    · left; omega

/-- **Kernel-checked runt** (converse on numbers). -/
theorem runt_example :
    ∃ sig, ∃ _r : AndRun (net2 300 400 200 300 150 250) (pulse 1000 500) sig,
      (∀ v, sig v 0 = true) ∧ sig 2 1250 = false ∧ sig 2 1650 = true ∧ sig 2 1700 = false := by
  have h1 : (300 : Nat) ≤ 400 := by decide
  have h2 : (200 : Nat) ≤ 300 := by decide
  have h3 : (150 : Nat) ≤ 250 := by decide
  have hwf := net2_wf h1 h2 h3
  have L := fun t => chain2_Lc h1 h2 h3 (F := 1000) (T := 500) (by decide) t
  refine ⟨extSig _ (pulse 1000 500), extRun hwf _, extRun_quiet hwf (pulse_zero (by decide)),
    extSig_false.2 ((L 1250).2 (by decide)), ?_, extSig_false.2 ((L 1700).2 (by decide))⟩
  cases h : extSig (net2 300 400 200 300 150 250) (pulse 1000 500) 2 1650 with
  | true => rfl
  | false => have := (L 1650).1 (extSig_false.1 h); omega

/-- The same chain with a longer low phase (`T = 600`) has no runt in any run. -/
theorem settled_example :
    ∀ sig, AndRun (net2 300 400 200 300 150 250) (pulse 1000 600) sig →
      ∀ t, 1250 ≤ t → t < 2100 → sig 2 t = false := by
  have := (chain2_settled_iff (F := 1000) (T := 600) (hl := 300) (hh := 400) (rl := 200)
    (rh := 300) (pl := 150) (ph := 250) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)).2 (by decide)
  intro sig r t a b; exact this sig r t (by omega) (by omega)

end Formal.Timing.ChainSettle
