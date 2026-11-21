import Formal.Timing.ChainSettleBridgeO4
open Formal.Net Formal.Timing Formal.Timing.ChainSettle Formal.Timing.ChainSettleBridge
example {lo hi F T F' T' : Nat} (h1 : 1 ≤ lo) (hT : 1 ≤ T) (hT' : 1 ≤ T')
    (ha : F + lo ≤ F') (hb : F' ≤ F + hi) (hc : F' ≤ F + T) (hd : F + T + lo ≤ F' + T')
    (he : F' + T' ≤ F + T + hi) (t : Nat) (e : t + 1 = F') (u : Nat) (a : t + 1 - lo ≤ u) (b : u ≤ t) :
    pulse F T u = pulse F' T' (t + 1) := by
  simp only [pulse_val]; simp
  trace_state
  sorry
