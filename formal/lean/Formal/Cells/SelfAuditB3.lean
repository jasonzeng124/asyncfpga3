import Formal.Cells.RigContract
/-!
# Self-audit of shard B (probe Bsa), part 3: a witness for `RigContract.idx_setup`

`idx_setup` composes the hk sequencer with `ResetContract.c2n_frontier`, but
the file has no run that meets all of its hypotheses (only `verdict_current`
and `stale_window` are witnessed). Here: hk period 7600 ps (`e n = 7600 n`),
rst and idx paths as fixed transport delays (600 ps, 1500 ps), a frontier
controller with the REAL `bd_c2n` INIT whose LUT arc and feedback wire are
1-tick transport delays (`O (t+1) = exc (qp t)`, `qp (t+1) = O t`), the
token static (`a = 1`, `b = 0`), setup 100 ps. For EVERY load edge `n0`,
every hypothesis is discharged, so the theorem is not vacuous, and its
conclusion (c) says this concrete controller is high from one tick after the
rst fall to the end of the window.

Caveat: with `lo = hi` paths the transition band of `PathOK` is empty and
`H_RST_ONE_FALL` holds trivially; the witness does not exercise a band.
-/
namespace Formal.Cells.SelfAuditB3
open Formal.Cells Formal.Cells.RigContract

/-- rst at the frontier's pin: `rig_rst` through a 600 ps transport path. -/
def rstW : Nat → Bool := fun t => rigRst (run false 0 ((t - 600) / 7600))
/-- operands: `idx` through a 1500 ps transport path. -/
def idxW : Nat → Nat := fun t => (run false 0 ((t - 1500) / 7600)).idx

/-- `(O t, qp t)`: unit LUT arc and unit feedback wire on the real `bd_c2n` INIT. -/
def oq : Nat → Bool × Bool
  | 0 => (false, false)
  | t + 1 => (CElemTiming.exc CElemTiming.INIT_c2n true false (oq t).2 (rstW t), (oq t).1)

def O (t : Nat) : Bool := (oq t).1
def qp (t : Nat) : Bool := (oq t).2

theorem loop : CTreeTimed.LoopG
    (fun t q => CElemTiming.exc CElemTiming.INIT_c2n ((fun _ => true) t) ((fun _ => false) t) q (rstW t))
    O qp 1 1 1 1 where
  H_LUT t ht := ⟨t - 1, by omega, by omega, by
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    show (oq (s + 1)).1 = _
    simp [oq, qp]⟩
  H_FB t ht := ⟨t - 1, by omega, by omega, by
    obtain ⟨s, rfl⟩ : ∃ s, t = s + 1 := ⟨t - 1, by omega⟩
    show (oq (s + 1)).2 = _
    simp [oq, O]⟩
  H_LOOP_POS := by decide

/-- **Every hypothesis of `idx_setup` holds** on this run, for every load edge. -/
theorem idx_setup_witness {n0 : Nat} (hL : Load n0) :
    (∀ t, 7600 * n0 + 1500 ≤ t → t < 7600 * (n0 + 65536) + 1500 → idxW t = (run false 0 n0).idx) ∧
    (∀ t, 7600 * (n0 + 16) + 600 + 1 ≤ t → t + 1 ≤ 7600 * (n0 + 65536) + 600 + 1 → O t = true) := by
  have W := idx_setup (pin := false) (vec := 0) (e := fun n => 7600 * n) (Tlo := 7600)
    (rlo := 600) (rhi := 600) (vlo := 1500) (vhi := 1500) (su := 100) (enlo := 0)
    (r := 7600 * (n0 + 16) + 600) (aF := fun _ => true) (bF := fun _ => false) (rstP := rstW)
    (idxP := idxW) loop
    (fun n => by show 7600 * n + 7600 ≤ 7600 * (n + 1); omega) (by decide)
    (pathOK_transport 7600 600 (by decide) _) (pathOK_transport 7600 1500 (by decide) _)
    (Nat.le_refl _) hL
    ⟨Nat.le_refl _, Nat.le_refl _, fun t a b => absurd (Nat.lt_of_le_of_lt a b) (Nat.lt_irrefl _),
      fun t a b => absurd (Nat.lt_of_le_of_lt a b) (Nat.lt_irrefl _)⟩
    (fun _ _ _ => ⟨rfl, rfl⟩) (by decide) (by decide)
  exact ⟨W.1, W.2.2⟩

end Formal.Cells.SelfAuditB3
