import Formal.Core.XAudit.Events2Design

/-!
# Formal.Core.XAudit.Events2Ring3 — ring3 through the generalised domain (subsumption check, E3 on a closed net)

Probe A-events2. The parsed ring3 of A-events (`Events.Ring3D.design`) is
recognised by `Recog2` with one-arc chains, `Back` holds with one-arc walks
(= `Pairing ∧ Race`), and the generic certificates of `Events2Time` give
the node rates that `EventsRing.node_period` proved by a ring-specific
argument: at most one event per 135 steps in every window (critical cycle
`cycle_le`, here per node), at least one per 171 steps in the long run
(`rate_lower`, certificate `T = 171` checked; `lo_tight`: no certificate
with `T < 171·K` exists).
-/

namespace Formal.Core.XAudit.Events2.Ring3

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.XSim (toCircuit)
open Formal.Core.TraceDiscrete (Sig)
open Formal.Core.XAudit.Events (ph)
open Formal.Core.XAudit.Events.Ring3D (design g)

def net : CNet 3 where
  v := fun j => decide (j.val = 0)
  ar := fun _ => 2
  ar_pos := fun _ => by decide
  src := fun j p => if p.val = 1 then j + 1 else j - 1
  inv := fun _ _ => false
  neg := fun _ p => p.val == 1

def sm : SMap2 net where
  lut := fun j => g (5 * j.val + 4)
  chain := fun j p => [g (5 * j.val + p.val)]
  pw := fun j p => (g (5 * j.val + p.val)).out
  fbG := fun j => g (5 * j.val + 2)
  rG := fun j => g (5 * j.val + 3)
  rst := 2

def back : (j : Fin 3) → Fin (net.ar j) → List (Arc net) := fun j p =>
  if p.val = 1 then [⟨j + 1, (0 : Fin 2)⟩] else [⟨j - 1, (1 : Fin 2)⟩]

theorem recog : Recog2 design net sm := by decide +kernel

theorem backOK : Back sm.bands back := by decide +kernel

/-- The b-pin cycle c0 → c2 → c1 → c0 (one token, three hops). -/
def crit (j : Fin 3) : List (Arc net) := [⟨j, (1 : Fin 2)⟩, ⟨j + 1, (1 : Fin 2)⟩, ⟨j + 2, (1 : Fin 2)⟩]

theorem crit_ok : ∀ j, walkOK net j j (crit j) = true ∧ wTok net (crit j) = 1 ∧
    wLo sm.bands (crit j) = 135 ∧ wHi sm.bands (crit j) = 171 := by decide +kernel

theorem lo_cert : Beh.LoCert sm.bands 171 1 (fun j => [57, 0, 114].getD j.val 0) := by decide +kernel

theorem hi57 : ∀ j p, sm.bands.hiF j + sm.bands.hiG j p ≤ 57 := by decide +kernel

theorem rst_hi : ∀ j : Fin 3, (sm.rG j).hi = 44 := by decide +kernel

/-- No lower certificate beats the max cycle ratio 171. -/
theorem lo_tight {T K : Nat} {π : Fin 3 → Nat} (hc : Beh.LoCert sm.bands T K π) : 171 * K ≤ T := by
  have := Beh.LoCert.cycle hc (crit 0) 0 (crit_ok 0).1
  rw [(crit_ok 0).2.2.2, (crit_ok 0).2.1] at this; omega

/-- **ring3 through Events2**: hazard-free for ever, at most one event per
135 steps in every window, at least one per 171 steps in the long run. -/
theorem ring3_rates (x : Fin design.n → Sig) (hsat : Circuit.Sat (toCircuit (build design)) x)
    (h0 : ∀ t, x (design.wire 0) t = false) (T : Nat) (hT : 1 ≤ T)
    (hrst : ∀ t, x (design.wire 2) t = decide (t < T)) :
    ∃ M : Nat → Fin 3 → Nat,
      (∀ t j, x (design.wire (sm.lut j).out) t = ph (net.v j) (M t j)) ∧
      (∀ t j, M (t + 135) j ≤ M t j + 1) ∧
      (∀ t j, t ≤ 171 * M t j + [57, 0, 114].getD j.val 0 + (T + 44 + 57)) := by
  obtain ⟨bh, hc, hr⟩ := design_beh2 design net sm recog x hsat h0 T hT hrst
  refine ⟨bh.M, fun t j => by rw [← hc]; exact bh.safe backOK t j, fun t j => ?_, fun t j => ?_⟩
  · have := bh.cycle_le (crit j) j (crit_ok j).1 t
    rw [(crit_ok j).2.1, (crit_ok j).2.2.1] at this; exact this
  · have := bh.rate_lower (R := T + 44) lo_cert hi57 (fun j s hs => hr j s (by rw [rst_hi]; exact hs)) t j
    omega

end Formal.Core.XAudit.Events2.Ring3
