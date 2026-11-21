import Formal.Net.OccNet

/-!
# Window certificates: a local check proved on a shifted small certificate (shard C, all-pairs route)

**Problem, plainly.** For every operand pair the run of THE target is a different, possibly long, sequence of loop
iterations, so its certificate is different and long. The local check at a node only looks at the counts of a few
nodes near one event. If a small *window* certificate looks, after shifting every node's event numbers by an offset
`o`, exactly like the big one around those counts (same causes, bounds no stronger, the window's initial state is
the big run's state after `o`), the big local check at those counts follows from the window's.

**Proved:** `st_shift` (the state after `n` flips equals the window state after `n - o` flips, the window starting
from the state after `o`), `lcheck_of_window` (the big certificate's local check at every count vector inside the
window's box follows from the window's local check).

**Not shown here:** that windows cover every count vector of every run (an instance property: the bounds keep a
node's dependency counts within a bounded distance of its own), the same for the timing checks, any instance.
-/

namespace Formal.Net.OccNet

variable {α : Type} [DecidableEq α]

theorem st_shift (s0 : α → Bool) (o n : α → Nat) (u : α) (h : o u ≤ n u) :
    st s0 n u = st (st s0 o) (fun w => n w - o w) u := by
  unfold st
  obtain ⟨b, hb'⟩ : ∃ b, n u = o u + b := ⟨n u - o u, by omega⟩
  have e2 : n u - o u = b := by omega
  simp only [hb', e2]
  generalize o u = a
  cases s0 u <;> rcases Nat.mod_two_eq_zero_or_one a with ha | ha <;>
    rcases Nat.mod_two_eq_zero_or_one b with hb | hb <;> simp [Nat.add_mod, ha, hb]

/-- **The local check at a count vector inside a window follows from the window's local check.** -/
theorem lcheck_of_window {en : α → (α → Bool) → Bool} {s0 : α → Bool} {C C' : Cert α} {L L' : α → Nat → α → Nat}
    {D : α → List α} {F : α → List Bool → Bool} (hF : ∀ v s, en v s = F v ((D v).map s))
    (v : α) (o : α → Nat) (hv : v ∈ D v)
    (hc : LCheck en (st s0 o) C' L' D v)
    (n : α → Nat) (hbox : ∀ u ∈ D v, o u ≤ n u ∧ n u ≤ o u + C'.len u)
    (hlen : n v < C.len v ↔ n v - o v < C'.len v)
    (hcause : n v < C.len v → C.causes v (n v) = (C'.causes v (n v - o v)).map (fun p => (p.1, p.2 + o p.1)))
    (hcD : ∀ p ∈ C'.causes v (n v - o v), p.1 ∈ D v)
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
  unfold Enabled
  constructor
  · rintro ⟨h1, h2⟩
    have hl : n v < C.len v := hlen.2 h1
    refine ⟨hl, fun p hp => ?_⟩
    rw [hcause hl] at hp
    obtain ⟨q, hq, rfl⟩ := List.mem_map.1 hp
    have e1 := h2 q hq
    have e2 := hbox q.1 (hcD q hq)
    simp only [n'] at e1 e2 ⊢; omega
  · rintro ⟨h1, h2⟩
    refine ⟨hlen.1 h1, fun q hq => ?_⟩
    have e1 := h2 (q.1, q.2 + o q.1) (by rw [hcause h1]; exact List.mem_map.2 ⟨q, hq, rfl⟩)
    have e2 := hbox q.1 (hcD q hq)
    simp only [n'] at e1 e2 ⊢; omega

end Formal.Net.OccNet
