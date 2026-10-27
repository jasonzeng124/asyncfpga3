
-- ==== AUDIT (shard C, track 10) ====
namespace Audit.C.Timing
open Formal.Net Formal.Timing

/-! ## Non-vacuity of check_sound on the toy: a Run exists, the check passes,
    and in that run the request really switches (so the conclusion has content). -/
theorem toy_run_exists : Nonempty (Run toyLink (earlySig toyLink)) :=
  ⟨(earlyRun toyLink toyLink_wf).toRun⟩

theorem toy_req_switches : changes (earlySig toyLink toyReq) 690 := by
  unfold changes earlySig; decide

theorem toy_nonvacuous :
    check toyLink toyReq toyData toySetup = true ∧
    Nonempty (Run toyLink (earlySig toyLink)) ∧ changes (earlySig toyLink toyReq) 690 :=
  ⟨toyLink_check, toy_run_exists, toy_req_switches⟩

/-! ## "per-node exact" is exact only over the CHOICE of cell functions.
The attaining runs (`earlyRun`/`lateRun`) pick OR / AND node functions. With the
cell function fixed (here XOR of two equal-delay arcs, as in any reconvergent
fanout), the window `(5,5)` reported by `win` is never attained. -/
def xorNet : Netlist where arcs := [⟨0, 1, 5, 5⟩, ⟨0, 1, 5, 5⟩]

theorem xorNet_wf : xorNet.WF := by decide
theorem xorNet_win : win xorNet 1 = some (5, 5) := by decide

theorem xor_never_switches {sig : Nat → Trace} (r : FixedRun xorNet sig)
    (hg : r.g 1 = fun x => x 0 != x 1) : ∀ t, ¬ changes (sig 1) t := by
  have h0 : r.d 0 = 5 := by have := r.range 0 _ rfl; simp only at this; omega
  have h1 : r.d 1 = 5 := by have := r.range 1 _ rfl; simp only at this; omega
  have hc : ∀ t, sig 1 t = false := by
    intro t
    rw [r.node 1 (by decide) t, hg]
    simp [fixedPin, xorNet, h0, h1]
  intro t h; exact h ((hc t).trans (hc (t+1)).symm)

/-! ## The shared-arc "exactness" relies on a single launch edge producing a
three-edge runt on a plain wire (arc 0→1, a buffer, g 1 = pin 0).
FEASIBILITY.md's own fidelity table says routing RC trees respond monotonically
(no glitch); the BoundedDelay channel admits this pulse anyway. -/
theorem launch_one_edge : ∀ t, changes launchSig t ↔ t = 0 := by
  intro t; unfold changes launchSig; constructor
  · intro h; apply Classical.byContradiction; intro h0; apply h
    rw [decide_eq_decide]; omega
  · intro h; subst h; decide

theorem glitch_three_edges : changes glitch 1 ∧ changes glitch 2 ∧ changes glitch 3 := by
  unfold changes glitch; decide

/-! ## Dropping H_SEPARATED in check_exact_disjoint breaks it: `corr` fails the
check, request and data share arc 0→1, and NO fixed-delay run violates bundling. -/
theorem drop_separated :
    check corr 2 [3] 1 = false ∧ (win corr 2).isSome = true ∧
    ¬ ∃ d ∈ [3], ∃ sig, Nonempty (FixedRun corr sig) ∧
      ∃ s t, changes (sig d) s ∧ changes (sig 2) t ∧ t < s + 1 := by
  refine ⟨corr_check, by decide, ?_⟩
  rintro ⟨d, hd, sig, ⟨r⟩, s, t, hs, ht, hlt⟩
  simp at hd; subst hd
  have := corr_fixed_safe r s t hs ht; omega

#print axioms changes_in_window
#print axioms check_sound
#print axioms check_stable
#print axioms win_exact
#print axioms check_exact_disjoint
#print axioms corr_fixed_safe
#print axioms corr_bd_violation
#print axioms toyLink_bundled
#print axioms toyShort_broken
#print axioms toy_nonvacuous
#print axioms xor_never_switches
#print axioms drop_separated

end Audit.C.Timing
