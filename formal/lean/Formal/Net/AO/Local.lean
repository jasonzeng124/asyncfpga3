import Formal.Net.AO.Timed

/-!
# Local form of the AND-OR local check (shard C, instance support)

* `lcheckXA_congr`: the local check at `v` only reads `len` over `D v`, `v`'s alternatives, and the reader's bounds on
  pairs of `D v`; so each node can be checked against a small certificate of its own.

Not here yet: the AND-OR form of `OccWindow.lcheck_of_window` (shifted window certificates).
-/

namespace Formal.Net.AO
open Formal.Net.OccNet (st)
open Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX

variable {α : Type} [DecidableEq α]

theorem enabled_congrA {C C' : Cert α} {n : α → Nat} {v : α} (hl : C.len v = C'.len v)
    (hc : ∀ k, C.causes v k = C'.causes v k) : Enabled C n v ↔ Enabled C' n v := by
  unfold Enabled; rw [hl, hc]

theorem lcheckXA_congr {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {s0 : α → Bool}
    {C C' : Cert α} {L L' : α → Nat → α → Nat} {D : α → List α} {cl : List (Claim α)} {gd : α → α → List (Guard α)}
    {v : α} (hv : v ∈ D v) (hl : ∀ u ∈ D v, C.len u = C'.len u) (hc : ∀ k, C.causes v k = C'.causes v k)
    (hL : ∀ a ∈ D v, ∀ b ∈ D v, ∀ k, L a k b = L' a k b) (h : LCheckXA N dat envEn s0 C' L' D cl gd v) :
    LCheckXA N dat envEn s0 C L D cl gd v := by
  intro n h1 h2 h3 bb hbb
  rw [enabled_congrA (hl v hv) hc]
  exact h n (fun u hu => hl u hu ▸ h1 u hu) (fun a ha b hb k hk => hL a ha b hb k ▸ h2 a ha b hb k hk)
    (fun k hk => by rw [← hc k]; exact h3 k hk) bb hbb

end Formal.Net.AO
