import Formal.Target.SpecRunt

/-! Audit T9 (auditor's own file, not part of formal/). Under SpecRunt's H_RUNT(w), a ZERO-DELAY one-input gate
(arc ⟨0,0,0,0⟩: every pseudo pip and site hop of the decoded target) cannot skip a pulse: Adm forces read delay 0.
So `GateOKRunt w` for such a gate forbids every pulse narrower than `w` on its input node, from time 0 on.
On the decoded target each kernel handshake output (out0_req, a_ack, b_ack, start_ack, pend_ack) is read by such
a hop (audit/t9/zero_readers.txt), so `BehavesRunt w` assumes those outputs never glitch narrower than `w`. -/

namespace Audit.T9
open Formal.Target

theorem start_zero (p : DelayPar) (g : Gate) (h : g.arcs = [⟨0, 0, 0, 0⟩]) : g.start p = 0 := by
  unfold Gate.start; rw [h]; simp; decide

theorem zero_pin_bans_runt {w : Nat} {p : DelayPar} {c : ℚ} {g : Gate} {x : Beh} (hk : 0 < g.k)
    (harc : g.arcs.getD 0 default = ⟨0, 0, 0, 0⟩) (h : GateOKRunt w p c g x) :
    ∀ a b, g.start p ≤ a → Pulse (x (g.ins.getD 0 0)) a b → b - a < w → False := by
  intro a b hs hP hw
  obtain ⟨f, _, hall⟩ := h
  obtain ⟨hle, hadm, hnr⟩ := (hall a hs).1 0 hk
  rw [harc] at hadm
  have h2 := hadm.2
  simp only [lerp, Nat.cast_zero, mul_zero, add_zero, zero_mul] at h2
  have h3 : a - f 0 a = 0 := by exact_mod_cast le_antisymm h2 (Nat.cast_nonneg _)
  have hfa : f 0 a = a := by omega
  exact hnr a b hP hw ⟨by omega, by rw [hfa]; exact hP.1⟩

/-- The same at the level of the whole net: any gate of the net with one zero arc on pin 0. -/
theorem behavesRunt_bans {w : Nat} {p : DelayPar} {N : Net} {x : Beh} (h : BehavesRunt w p N x)
    {g : Gate} (hg : g ∈ N.gates) (hk : 0 < g.k) (harc : g.arcs.getD 0 default = ⟨0, 0, 0, 0⟩) :
    ∀ a b, g.start p ≤ a → Pulse (x (g.ins.getD 0 0)) a b → b - a < w → False := by
  obtain ⟨c, _, _, hall⟩ := h
  exact zero_pin_bans_runt hk harc (hall g hg)

end Audit.T9

#print axioms Audit.T9.start_zero
#print axioms Audit.T9.zero_pin_bans_runt
#print axioms Audit.T9.behavesRunt_bans
