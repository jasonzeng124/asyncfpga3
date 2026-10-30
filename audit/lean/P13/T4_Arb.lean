import Formal.Core.LutAudit
open Formal.Core.LutAudit Formal.Core.LutCells

#check @arb_tie_from_idle_hazard
#check @arb_grant_near_tie_runt

-- The LUT data really is the RTL's (cells/rtl/bd_arb.v:245-251, bd_ce.v:55).
example : bd_arbiter_ustate.init = 0xFFF0FFB2ACACACAC := rfl
example : bd_arbiter_ugrant.init = 0x0C0C0C0CA0A0A0A0 := rfl
example : bd_c2n_set_u.init = 0xFFB2FFB2FFB2FFB2 := rfl

-- Free-pin order for ustate O6 is [A0, rst, q, r2, r1]: the intermediate vertices of the
-- tie cube give the opposite value of the held q (set via r1·¬r2, reset via ¬r1·r2).
example : outB bd_arbiter_ustate .O6 [false, false, false, false, true] = true := by decide
example : outB bd_arbiter_ustate .O6 [false, false, true, true, false] = false := by decide

/-! A timed instance of the grant runt (not in their file): transport delays on the
ugrant pins, r1 = 1 held, q rises at 0 (r1 has won), r2 rises at 0; the q branch into
ugrant is 2 ticks slower than r2's. g2 = outB ugrant O6 [q, r2, r1] pulses on [1, 3). -/
def stepAt (t0 : Nat) (t : Nat) : Bool := decide (t0 ≤ t)
def g2t (dq dr : Nat) (t : Nat) : Bool :=
  outB bd_arbiter_ugrant .O6 [stepAt (1 + dq) t, stepAt (1 + dr) t, true]
theorem grant_runt_timed :
    g2t 2 0 0 = false ∧ g2t 2 0 1 = true ∧ g2t 2 0 2 = true ∧ g2t 2 0 3 = false ∧
    ∀ t, t < 50 → g2t 0 0 t = false := by decide
