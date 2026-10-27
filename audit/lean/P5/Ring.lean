import Formal.Net.OpsRingLive
open Formal.Net Formal.Net.Bridge Formal.Net.Ops.RingLive Formal.Net.Bridge.RingT
-- iterate the unit step with sharing (unitTrace itself is unmemoised)
def stepS (N : Net) (s : State) : State := fun i => if i < N.n then N.f i s else s i
def trajL (N : Net) (s : State) (n T : Nat) : List (List Bool) :=
  ((List.range T).foldl (fun (acc : List (List Bool) × State) _ =>
    let s' := stepS N acc.2; let l := (List.range n).map s'; (acc.1 ++ [l], fun i => l.getD i false)) ([(List.range n).map s], s)).1
#eval (trajL (ringNet 5 1) (Ring.resetState 1) 5 20).map (fun l => l.headD false)
#eval (trajL (ringNet 5 0) (Ring.resetState 0) 5 20).map (fun l => l.headD false)
#print axioms ring_every_window_reset
#print axioms ring_unit_live
