import Formal.Net.CapstoneLiveNd3Pers
import Formal.Net.CapstoneLiveNd3MuxN2

/-!
# Probe C-8z3 (4): persistence of every gcd_hw gate, mux input acknowledges excepted

`gcd_hw_muxn_persistent`: the 3-way mux, persistent up to `ZRise` (as the 2-way muxes).

**`gcd_hw_persistent_all`**: for `a, b < 2^31`, on every run meeting H_CELLS, H_BUNDLE and
H_START_ONCE, every gate of every operator (`gatesK ++ grantsK`, the gates of
`gcd_hw_live_final2`'s quiescence) is persistent, except that at a 2-way or 3-way mux with
output `z` a gate may lose its excitation in a step where `z_ack` rises. By `mux_pers_tbl`
and `npers0..3` only the input acknowledges' falling excitations can do that, and
`mux_ack_not_pers` shows it is possible. So gcd_hw is NOT a persistent (semi-modular) gate
network, and Keller's confluence theorem does not apply directly (see C-8z3's note).
-/

namespace Formal.Net.CapNet.Live.Nd3
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Live Formal.Net.CapNet.Live.Nd

section
variable {ch : Fin NC → Chan} {itr : Itr}

theorem pers_muxn {p : Fin NO} {c x0 x1 x2 z : Fin NC} {nw : NW}
    (M : MuxN.MuxN selD (fun k => ch (cx3 x0 x1 x2 k)) (ch c) (ch z) (itr p))
    (hp : ∀ c, Protocol (ch c)) (hh : ∀ c, Held (ch c)) :
    ∀ g ∈ gatesK p (.muxn c x0 x1 x2 z nw), PersB (gsAt ch itr) (ZRise ch z) g := by
  have K := fun u => muxn_step_pers M (fun k _ => hp _) (hp c) (hp z) (hh c) u
  have cb : ∀ (w : Nat) k, k < 3 → (MuxN.clip w == k) = (w == k) := fun w k hk => MuxN.clip_beq w k hk
  intro g hg
  simp only [gatesK, List.mem_append, List.mem_map, List.mem_range, List.mem_singleton] at hg
  rcases hg with ((⟨k, hk3, rfl⟩ | rfl) | ⟨k, hk3, rfl⟩) | rfl
  · rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
    · intro v u he hn
      have h2 : ((ch c).req u && (MuxN.clip (selD ((ch c).dat u)) == 0)) = v := by
        rw [cb _ 0 (by decide)]; exact he.2
      rcases (K u).1.app v he.1 h2 hn with ⟨h1, h3⟩ | h
      · left; refine ⟨h1, ?_⟩; rw [← cb _ 0 (by decide)]; exact h3
      · exact Or.inr (Or.inl h)
    · intro v u he hn
      have h2 : ((ch c).req u && (MuxN.clip (selD ((ch c).dat u)) == 1)) = v := by
        rw [cb _ 1 (by decide)]; exact he.2
      rcases (K u).2.1.app v he.1 h2 hn with ⟨h1, h3⟩ | h
      · left; refine ⟨h1, ?_⟩; rw [← cb _ 1 (by decide)]; exact h3
      · exact Or.inr (Or.inl h)
    · intro v u he hn
      have h2 : ((ch c).req u && (MuxN.clip (selD ((ch c).dat u)) == 2)) = v := by
        rw [cb _ 2 (by decide)]; exact he.2
      rcases (K u).2.2.1.app v he.1 h2 hn with ⟨h1, h3⟩ | h
      · left; refine ⟨h1, ?_⟩; rw [← cb _ 2 (by decide)]; exact h3
      · exact Or.inr (Or.inl h)
  · intro v u he hn
    exact ((K u).2.2.2.1.app v he hn).elim Or.inl (fun h => Or.inr (Or.inl h))
  · rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl
    · intro v u he hn
      rcases (K u).2.2.2.2.1.app v he.1 he.2 hn with h | h | ⟨rfl, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨he.2, h⟩)
    · intro v u he hn
      rcases (K u).2.2.2.2.2.1.app v he.1 he.2 hn with h | h | ⟨rfl, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨he.2, h⟩)
    · intro v u he hn
      rcases (K u).2.2.2.2.2.2.1.app v he.1 he.2 hn with h | h | ⟨rfl, h⟩
      · exact Or.inl h
      · exact Or.inr (Or.inl h)
      · exact Or.inr (Or.inr ⟨he.2, h⟩)
  · intro v u he hn
    exact ((K u).2.2.2.2.2.2.2.app v he hn).elim Or.inl (fun h => Or.inr (Or.inl h))

end

/-- **The 3-way mux of gcd_hw**: persistent up to `z_ack` rising. -/
theorem gcd_hw_muxn_persistent (a b : Nat) (ch : Fin NC → Chan) (itr : Itr)
    (H_CELLS : ∀ p : Fin NO, CellI ch (srcV a b) itr p (opAt p))
    (H_BUNDLE : ∀ c, Held (ch c)) :
    ∀ p c x0 x1 x2 z nw, opAt p = .muxn c x0 x1 x2 z nw →
      ∀ g ∈ gatesK p (opAt p), PersB (gsAt ch itr) (ZRise ch z) g := by
  have hC : ∀ p : Fin NO, Cell ch (srcV a b) (opAt p) := fun p => cellI_cell _ (H_CELLS p)
  have hp := gcd_hw_protocol a b ch hC H_BUNDLE
  intro p c x0 x1 x2 z nw hk g hg
  have M := H_CELLS p
  rw [hk] at hg M
  exact pers_muxn M hp H_BUNDLE g hg

/-- The output channel of a (2-way or 3-way) mux. -/
def MuxZ : K NC → Fin NC → Prop
  | .mux _ _ _ z _, z' => z' = z
  | .muxn _ _ _ _ z _, z' => z' = z
  | _, _ => False

/-- **Every gate of gcd_hw is persistent, except that a mux gate may lose its excitation in a
step where the mux's output acknowledge rises.** -/
theorem gcd_hw_persistent_all (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (ch : Fin NC → Chan) (itr : Itr)
    (H_CELLS : ∀ p : Fin NO, CellI ch (srcV a b) itr p (opAt p))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1) :
    ∀ p : Fin NO, ∀ g ∈ gatesK p (opAt p) ++ grantsK p (opAt p),
      PersB (gsAt ch itr) (fun t => ∃ z, MuxZ (opAt p) z ∧ ZRise ch z t) g := by
  intro p g hg
  cases hk : opAt p with
  | mux c x y z mw =>
    have hg' : g ∈ gatesK p (opAt p) := by rw [hk] at hg ⊢; simpa [grantsK] using hg
    have h := gcd_hw_mux_persistent a b ch itr H_CELLS H_BUNDLE p c x y z mw hk g hg'
    intro v t he hn
    rcases h v t he hn with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨z, rfl, h⟩)
  | muxn c x0 x1 x2 z nw =>
    have hg' : g ∈ gatesK p (opAt p) := by rw [hk] at hg ⊢; simpa [grantsK] using hg
    have h := gcd_hw_muxn_persistent a b ch itr H_CELLS H_BUNDLE p c x0 x1 x2 z nw hk g hg'
    intro v t he hn
    rcases h v t he hn with h | h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨z, rfl, h⟩)
  | _ =>
    have h := gcd_hw_persistent a b ha hb ch itr H_CELLS H_BUNDLE H_START_ONCE p
      (by intros; rw [hk]; simp) (by intros; rw [hk]; simp) g hg
    intro v t he hn
    exact (h v t he hn).elim Or.inl (fun h => Or.inr (Or.inl h))

end Formal.Net.CapNet.Live.Nd3
