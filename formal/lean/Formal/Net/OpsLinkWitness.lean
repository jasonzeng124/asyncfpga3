import Formal.Net.OpsLink

/-!
# Probe C-8l: non-vacuity of the link model

`link_witness`: an explicit run (every gate and wire one tick, a four-phase sender that
offers one token of value `v`, a receiver that acknowledges one tick after the request)
satisfying every field of `Link` and the protocol on both channels, in which the link offers
its first token at t = 2 (`OffAt o 0 2`) with value `v`, and the receiver latches it at
t = 6 (`TokAt o 0 6`). So `link_op`'s hypotheses are satisfied by a run that moves a token,
and its conclusion is not vacuous (C-8j's lesson: 8b's graph met its safety theorem by
deadlocking). Traces are constant from t = 7 on.
-/

namespace Formal.Net.Ops.Link
open Formal.Net Formal.Net.Handshake Formal.Net.Ops
open Formal.Cells.LinkHandshake (ctlB)

/-- A trace given by a table for `t < 8` and its last entry afterwards. -/
def tr (l : List Bool) (t : Nat) : Bool := if t < 8 then l.getD t false else l.getD 7 false

theorem tr8 (l : List Bool) (t : Nat) : tr l (t + 8) = l.getD 7 false := by
  unfold tr; split
  · omega
  · rfl
theorem tr9 (l : List Bool) (t : Nat) : tr l (t + 8 + 1) = l.getD 7 false := by
  unfold tr; split
  · omega
  · rfl

--                 t: 0      1      2      3      4      5      6      7
def wIr : Trace := tr [false, true,  true,  true,  false, false, false, false]
def wC  : Trace := tr [false, false, true,  true,  true,  false, false, false]
def wIa : Trace := tr [false, false, false, true,  true,  true,  false, false]
def wOr : Trace := tr [false, false, false, true,  true,  true,  false, false]
def wOa : Trace := tr [false, false, false, false, true,  true,  true,  false]

def wI (v : Nat) : Chan := ⟨wIr, wIa, fun _ => v⟩
def wO (v : Nat) : Chan := ⟨wOr, wOa, fun _ => v⟩

/-- Check a step property on `t < 8` by evaluation; the tail is constant. -/
macro "wtac" : tactic => `(tactic| (
  intro t
  try simp only [wI, wO]
  match t with
  | 0 | 1 | 2 | 3 | 4 | 5 | 6 | 7 => decide
  | t + 8 => simp only [wI, wO, wIr, wC, wIa, wOr, wOa, tr8, tr9]; decide))

theorem link_witness (v : Nat) :
    Link (wI v) (wO v) wC ∧ Protocol (wI v) ∧ Protocol (wO v) ∧
      OffAt (wO v) 0 2 ∧ (wO v).dat 3 = v ∧ TokAt (wO v) 0 6 := by
  have cel : ∀ t, wC (t + 1) ≠ wC t → wC (t + 1) = ctlB (wIr t) (wOa t) (wC t) false := by wtac
  have ack : ∀ t, wIa (t + 1) ≠ wIa t → wIa (t + 1) = wC t := by wtac
  have req : ∀ t, wOr (t + 1) ≠ wOr t → wOr (t + 1) = wC t := by wtac
  have si : ∀ t, SendStep (wI v) t := by unfold SendStep; wtac
  have ri : ∀ t, RecvStep (wI v) t := by unfold RecvStep; wtac
  have so : ∀ t, SendStep (wO v) t := by unfold SendStep; wtac
  have ro : ∀ t, RecvStep (wO v) t := by unfold RecvStep; wtac
  exact ⟨⟨cel, ack, req, fun _ _ => rfl, fun _ _ => rfl, rfl, rfl, rfl⟩,
    ⟨⟨rfl, rfl⟩, fun t => ⟨si t, ri t⟩⟩, ⟨⟨rfl, rfl⟩, fun t => ⟨so t, ro t⟩⟩,
    ⟨rfl, rfl⟩, rfl, ⟨rfl, rfl⟩⟩

end Formal.Net.Ops.Link
