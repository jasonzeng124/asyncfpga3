import Formal.Net.TimedOccX

/-!
# Local certificates: the local check needs only a node's own data (shard C, instance support)

**Problem, plainly.** In the kernel, looking a value up in one big table costs time proportional to its position,
so checking 400+ nodes against one global certificate is slow. The local check at node `v` only reads the event
counts' bounds of `v`'s dependency list, `v`'s own causes, and the bounds `L` between nodes of that list. So each
node can be checked against a small certificate holding just that data.

**Proved:** `lcheck_congr` and `lcheckX_congr`: if two certificates agree on `len` over `D v` and on `v`'s causes, and
two bound functions agree on pairs from `D v`, the local checks (`LCheck`, and `TimedX.LCheckX` with the same claims
and guards) at `v` are equivalent.
-/

namespace Formal.Net.OccNet
open Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX

variable {α : Type} [DecidableEq α]

theorem enabled_congr {C C' : Cert α} {n : α → Nat} {v : α} (hl : C.len v = C'.len v)
    (hc : ∀ k, C.causes v k = C'.causes v k) : Enabled C n v ↔ Enabled C' n v := by
  unfold Enabled; rw [hl, hc]

theorem lcheck_congr {en : α → (α → Bool) → Bool} {s0 : α → Bool} {C C' : Cert α} {L L' : α → Nat → α → Nat}
    {D : α → List α} {v : α} (hv : v ∈ D v) (hl : ∀ u ∈ D v, C.len u = C'.len u) (hc : ∀ k, C.causes v k = C'.causes v k)
    (hL : ∀ a ∈ D v, ∀ b ∈ D v, ∀ k, L a k b = L' a k b) (h : LCheck en s0 C' L' D v) : LCheck en s0 C L D v := by
  intro n h1 h2
  rw [enabled_congr (hl v hv) hc]
  exact h n (fun u hu => hl u hu ▸ h1 u hu) (fun a ha b hb k hk => hL a ha b hb k ▸ h2 a ha b hb k hk)

theorem lcheckX_congr {N : TNet α} {dat : α → Bool} {envEn : α → (α → Bool) → Bool} {s0 : α → Bool}
    {C C' : Cert α} {L L' : α → Nat → α → Nat} {D : α → List α} {cl : List (Claim α)} {gd : α → α → List (Guard α)}
    {v : α} (hv : v ∈ D v) (hl : ∀ u ∈ D v, C.len u = C'.len u) (hc : ∀ k, C.causes v k = C'.causes v k)
    (hL : ∀ a ∈ D v, ∀ b ∈ D v, ∀ k, L a k b = L' a k b) (h : LCheckX N dat envEn s0 C' L' D cl gd v) :
    LCheckX N dat envEn s0 C L D cl gd v := by
  intro n h1 h2 bb hbb
  rw [enabled_congr (hl v hv) hc]
  exact h n (fun u hu => hl u hu ▸ h1 u hu) (fun a ha b hb k hk => hL a ha b hb k ▸ h2 a ha b hb k hk) bb hbb

end Formal.Net.OccNet
