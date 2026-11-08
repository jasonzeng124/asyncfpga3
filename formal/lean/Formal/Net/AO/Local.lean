import Formal.Net.AO.Timed
import Formal.Net.OccWindow

/-!
# Local form of the AND-OR local check (shard C, instance support)

* `lcheckXA_congr`: the local check at `v` only reads `len` over `D v`, `v`'s alternatives, and the reader's bounds on
  pairs of `D v`; so each node can be checked against a small certificate of its own.
* `lcheckA_window`: the plain AND-OR local check (`AO.LCheck`, no data pins) at the count vectors inside a window's
  box follows from a shifted window certificate's check (event numbers shifted by `o`, alternatives shifted, bounds no
  stronger, the window starting from the state after `o`): the brick for certificates of unboundedly long runs.
-/

namespace Formal.Net.AO
open Formal.Net.OccNet (st st_shift)
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

theorem lcheckA_window {en : α → (α → Bool) → Bool} {s0 : α → Bool} {C C' : Cert α} {L L' : α → Nat → α → Nat}
    {D : α → List α} {F : α → List Bool → Bool} (hF : ∀ v s, en v s = F v ((D v).map s))
    (v : α) (o : α → Nat) (hc : LCheck en (st s0 o) C' L' D v)
    (n : α → Nat) (hbox : ∀ u ∈ D v, o u ≤ n u ∧ n u ≤ o u + C'.len u)
    (hlen : n v < C.len v ↔ n v - o v < C'.len v)
    (hcause : n v < C.len v → C.causes v (n v) =
      (C'.causes v (n v - o v)).map (fun alt => alt.map fun p => (p.1, p.2 + o p.1)))
    (hcD : ∀ alt ∈ C'.causes v (n v - o v), ∀ p ∈ alt, p.1 ∈ D v)
    (hL : ∀ a ∈ D v, ∀ b ∈ D v, ∀ k, k < n a - o a → L' a k b + o b ≤ L a (k + o a) b)
    (hn : (∀ u ∈ D v, n u ≤ C.len u) ∧ (∀ a ∈ D v, ∀ b ∈ D v, ∀ k, k < n a → L a k b ≤ n b)) :
    en v (st s0 n) = true ↔ Enabled C n v := by
  let n' : α → Nat := fun w => n w - o w
  have h1 := hc n' (fun u hu => by have := hbox u hu; simp only [n']; omega)
    (fun a ha b hb k hk => by
      have := hL a ha b hb k hk
      have := hn.2 a ha b hb (k + o a) (by simp only [n'] at hk; have := hbox a ha; omega)
      have := hbox b hb
      simp only [n']; omega)
  have hst : (D v).map (st s0 n) = (D v).map (st (st s0 o) n') :=
    List.map_congr_left (fun u hu => st_shift s0 o n u (hbox u hu).1)
  rw [hF, hst, ← hF, h1]
  unfold Enabled AltIn
  constructor
  · rintro ⟨h1, alt, halt, hin⟩
    have hl : n v < C.len v := hlen.2 h1
    refine ⟨hl, alt.map (fun p => (p.1, p.2 + o p.1)), ?_, fun q hq => ?_⟩
    · rw [hcause hl]; exact List.mem_map.2 ⟨alt, halt, rfl⟩
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.1 hq
      have e1 := hin p hp
      have e2 := hbox p.1 (hcD alt halt p hp)
      simp only [n'] at e1 e2 ⊢; omega
  · rintro ⟨h1, alt, halt, hin⟩
    refine ⟨hlen.1 h1, ?_⟩
    rw [hcause h1] at halt
    obtain ⟨alt', halt', rfl⟩ := List.mem_map.1 halt
    refine ⟨alt', halt', fun p hp => ?_⟩
    have e1 := hin (p.1, p.2 + o p.1) (List.mem_map.2 ⟨p, hp, rfl⟩)
    have e2 := hbox p.1 (hcD alt' halt' p hp)
    simp only [n'] at e1 e2 ⊢; omega

end Formal.Net.AO
