import Formal.Cells.SelfAuditB6
/-! P9 audit, item 1: SelfAuditB6 joint witness of RigSrc.gcd_rig_first_env. -/
namespace P9Rig
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
  Formal.Net.CapNet.Wit Formal.Cells.SelfAuditB6
set_option maxRecDepth 100000

#check @Formal.Cells.RigSrc.gcd_rig_first_env
#print axioms rig_env_feeds
#print axioms rig_env_relap
#print axioms cell_sh1

/-- Re-derive the feed myself: the witness terms typecheck against the theorem itself. -/
theorem feed_again : ∀ e', TokAt (chS out0) 0 e' → (chS out0).dat e' = 6 := by
  have h := Formal.Cells.RigSrc.gcd_rig_first_env 12 18 (by decide) (by decide) chS eS kS qS
    id id id (fun _ => id) w_ker w_bundle w_fork_wire w_dat w_rel w_rel0 (fun _ => rfl)
    (fun _ _ h => h) (fun _ => Nat.le_refl _) (fun _ _ _ h => h) (fun _ _ => Nat.le_refl _)
    (fun _ _ h => h) (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun _ => Nat.le_refl _)
    w_uenv1 w_c3 w_m1 w_m0
  intro e' he; rw [h.2 e' he]; decide

/-- Mutation b := 17: the same witness cannot be fed with b = 17 (w_ker/w_dat are about srcV 12 18). -/
example : True := by
  fail_if_success
    have := Formal.Cells.RigSrc.gcd_rig_first_env 12 17 (by decide) (by decide) chS eS kS qS
      id id id (fun _ => id) w_ker w_bundle w_fork_wire w_dat w_rel w_rel0 (fun _ => rfl)
      (fun _ _ h => h) (fun _ => Nat.le_refl _) (fun _ _ _ h => h) (fun _ _ => Nat.le_refl _)
      (fun _ _ h => h) (fun _ => Nat.le_refl _) (fun _ _ h => h) (fun _ => Nat.le_refl _)
      w_uenv1 w_c3 w_m1 w_m0
  trivial

/-- Mutation of the conclusion: gcd 12 17 = 1 is NOT what latches. -/
theorem mut_b_conclusion : ¬ (∀ e', TokAt (chS out0) 0 e' → (chS out0).dat e' = Nat.gcd 12 17) := by
  intro h; have := h 474 rig_env_latch.1; rw [rig_env_latch.2] at this; exact absurd this (by decide)

/-- Mutation of the env data: shifting the in_ack fall by one tick breaks envOK. -/
theorem mut_env : envOK [99, 200] = false := by decide +kernel

/-- Timeline facts (my own): e starts high, falls at 99, re-rises at 432;
out0.ack rises before 432 and falls at 474 (the first fall). -/
theorem timeline :
    eS 0 = true ∧ fallB eS 99 = true ∧ riseB eS 432 = true ∧
    cnt (riseB eS) 474 = 1 ∧ cnt (fallB eS) 474 = 1 ∧
    qS 431 = true ∧ qS 474 = true ∧ qS 475 = false ∧ cnt (fallB qS) 474 = 0 ∧
    eS 473 = true := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide +kernel

end P9Rig
