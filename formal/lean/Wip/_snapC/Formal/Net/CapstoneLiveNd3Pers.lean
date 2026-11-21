import Formal.Net.CapstoneLiveNd2
import Formal.Net.CapstoneLiveNd3Loc

/-!
# Probe C-8z3 (2): persistence of the gcd_hw gate network on every run

`Pers S g`: along the state trace `S`, whenever gate `g` is excited toward `v` and its output
is not `v`, one tick later it is still excited toward `v` or shows `v`.

**`gcd_hw_persistent`**: for `a, b < 2^31` and every run meeting H_CELLS, H_BUNDLE and
H_START_ONCE, EVERY gate of EVERY operator of the 465-channel network is persistent, arbiter
grants included, except the gates of the 2-way and 3-way muxes. No timing hypothesis is used.
* The local facts come from `CapstoneLiveNd3Loc` (cell invariants + the protocol of every
  channel, `gcd_hw_protocol`).
* The grants are persistent because no gcd_hw arbiter stage is ever contested
  (`gcd_hw_never_contested`, 8q/8r/8s, which needs H_START_ONCE and the token-level walk).

**`gcd_hw_mux_persistent`**: the 21 two-way muxes are persistent except that the falling
excitation of an input acknowledge may be withdrawn by `z_ack` rising in the same step.
That exception is real: `CapstoneLiveNd3Loc.mux_ack_not_pers` exhibits it in the mux's
reachable table, and `Wip/C8z3/persim_slowack.py` reaches it on the whole network
(bounded delays, mux input acknowledges slow), with no deadlock and the right result.
So **the persistence invariant of the Keller route (C-8z2's note) is FALSE for gcd_hw as a
gate network**. The circuit is semi-modular except at the mux input-acknowledge
C-elements. Those are only ever disabled by `z_ack` rising, and a C-element whose
excitation is withdrawn just holds its output.

The 3-way mux (one instance) is not covered.
-/

namespace Formal.Net.CapNet.Live.Nd3
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Live Formal.Net.CapNet.Live.Nd
open Formal.Net.CapSafe (Good TS texec)

/-- Persistence of a gate along a state trace. -/
def Pers (S : Nat → GS) (g : Gate) : Prop :=
  ∀ v t, g.exc v (S t) → g.out (S t) ≠ v → g.exc v (S (t + 1)) ∨ g.out (S (t + 1)) = v

/-- Persistence up to an escape event `B t`. -/
def PersB (S : Nat → GS) (B : Nat → Prop) (g : Gate) : Prop :=
  ∀ v t, g.exc v (S t) → g.out (S t) ≠ v → g.exc v (S (t + 1)) ∨ g.out (S (t + 1)) = v ∨ B t

theorem map_all {ch : Fin NC → Chan} {l : List (Fin NC)} {P : Chan → Prop} :
    (∀ o ∈ l.map ch, P o) ↔ ∀ c ∈ l, P (ch c) := by simp

section
variable {a b : Nat} {ch : Fin NC → Chan} {itr : Itr}

theorem pers_src {z : Fin NC} (hp : Protocol (ch z)) :
    Pers (gsAt ch itr) (gw (fun s => s.rq z) (fun s => !s.ak z)) :=
  fun v t he hn => src_pers hp v t he hn

theorem pers_sink {i : Fin NC} (hp : Protocol (ch i)) :
    Pers (gsAt ch itr) (gw (fun s => s.ak i) (fun s => s.rq i)) :=
  fun v t he hn => sink_pers hp v t he hn

theorem pers_fork {i : Fin NC} {os : List (Fin NC)} (F : Fork.Fork (ch i) (os.map ch))
    (hp : ∀ c, Protocol (ch c)) :
    ∀ g ∈ os.map (fun c => gw (fun s => s.rq c) (fun s => s.rq i)) ++
      [⟨fun s => s.ak i, fun v s => ∀ c ∈ os, s.ak c = v⟩], Pers (gsAt ch itr) g := by
  have hpo : ∀ o ∈ os.map ch, Protocol o := fun o ho => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp ho; exact hp c
  intro g hg
  simp only [List.mem_append, List.mem_map, List.mem_singleton] at hg
  rcases hg with ⟨c, hc, rfl⟩ | rfl
  · intro v t he hn
    exact fork_req_pers F (hp i) hpo (List.mem_map_of_mem hc) v t he hn
  · intro v t he hn
    rcases fork_ack_pers F (hp i) hpo v t (map_all.mpr he) hn with h | h
    · exact Or.inl (map_all.mp h)
    · exact Or.inr h

theorem pers_join {o : Fin NC} {ins : List (Fin NC)} {gf : List Nat → Nat}
    (J : Join.Join gf (ins.map ch) (ch o)) (hp : ∀ c, Protocol (ch c)) :
    ∀ g ∈ (⟨fun s => s.rq o, fun v s => ∀ c ∈ ins, s.rq c = v⟩ : Gate) ::
      ins.map (fun c => gw (fun s => s.ak c) (fun s => s.ak o)), Pers (gsAt ch itr) g := by
  have hpi : ∀ i ∈ ins.map ch, Protocol i := fun i hi => by
    obtain ⟨c, -, rfl⟩ := List.mem_map.mp hi; exact hp c
  intro g hg
  simp only [List.mem_cons, List.mem_map] at hg
  rcases hg with rfl | ⟨c, hc, rfl⟩
  · intro v t he hn
    rcases join_req_pers J (hp o) hpi v t (map_all.mpr he) hn with h | h
    · exact Or.inl (map_all.mp h)
    · exact Or.inr h
  · intro v t he hn
    exact join_ack_pers J (hp o) hpi (List.mem_map_of_mem hc) v t he hn

theorem pers_steer {j t f : Fin NC} {fd : Nat → Nat}
    (S : Steer.Steer sel2 fd (ch j) (fun b => ch (bif b then t else f))) (hp : ∀ c, Protocol (ch c))
    (hh : ∀ c, Held (ch c)) :
    ∀ g ∈ [gw (fun s => s.rq t) (fun s => s.rq j && (sel2 (s.dt j) == true)),
      gw (fun s => s.rq f) (fun s => s.rq j && (sel2 (s.dt j) == false)),
      gw (fun s => s.ak j) (fun s => s.ak t || s.ak f)], Pers (gsAt ch itr) g := by
  have hpo : ∀ b, Protocol (ch (bif b then t else f)) := fun b => hp _
  intro g hg
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · intro v u he hn
    exact steer_t_pers S (hp j) hpo (hh j) v u he hn
  · intro v u he hn
    exact steer_f_pers S (hp j) hpo (hh j) v u he hn
  · intro v u he hn
    exact steer_a_pers S (hp j) hpo (hh j) v u he hn

theorem pers_link {p : Fin NO} {i o : Fin NC} (L : Link.Link (ch i) (ch o) (itr p 0))
    (hp : ∀ c, Protocol (ch c)) :
    ∀ g ∈ [gw (fun s => s.it p 0)
        (fun s => Formal.Cells.LinkHandshake.ctlB (s.rq i) (s.ak o) (s.it p 0) false),
      gw (fun s => s.ak i) (fun s => s.it p 0), gw (fun s => s.rq o) (fun s => s.it p 0)],
      Pers (gsAt ch itr) g := by
  intro g hg
  have K := fun u => link_step_pers L (hp i) (hp o) u
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl
  · intro v u he hn; exact (K u).1.app v he hn
  · intro v u he hn; exact (K u).2.1.app v he hn
  · intro v u he hn; exact (K u).2.2.app v he hn

theorem pers_amerge {p : Fin NO} {x y z : Fin NC} {w : Nat}
    (M : CM.AMerge (ch x) (ch y) (ch z) (itr p 0) (itr p 1)) (hp : ∀ c, Protocol (ch c))
    (hnc : ∀ t, ¬ CapNet.Live.Contested (ch x) (ch y) (itr p 0) (itr p 1) t) :
    ∀ g ∈ gatesK p (.amerge x y z w) ++ grantsK p (.amerge x y z w), Pers (gsAt ch itr) g := by
  intro g hg
  have K := fun u => amerge_step_pers M (hp x) (hp y) (hp z) u
  have G := fun u => grant_step_pers M (hp x) (hp y) (hp z) u (hnc u)
  simp only [gatesK, grantsK, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with (rfl | rfl | rfl) | (rfl | rfl)
  · intro v u he hn; exact (K u).1.app v he.1 he.2 hn
  · intro v u he hn; exact (K u).2.1.app v he.1 he.2 hn
  · intro v u he hn; exact (K u).2.2.app v he.1 he.2 hn
  · intro v u he hn; exact (G u).1.app v he.1 he.2 hn
  · intro v u he hn; exact (G u).2.app v he.1 he.2 hn

/-- The escape event of the mux exception: `z_ack` rises. -/
def ZRise (ch : Fin NC → Chan) (z : Fin NC) (t : Nat) : Prop :=
  (ch z).ack t = false ∧ (ch z).ack (t + 1) = true

theorem pers_mux {p : Fin NO} {c x y z : Fin NC} {mw : MW}
    (M : Mux.Mux sel2 (ch x) (ch y) (ch c) (ch z) (itr p 0) (itr p 1)) (hp : ∀ c, Protocol (ch c))
    (hh : ∀ c, Held (ch c)) :
    ∀ g ∈ gatesK p (.mux c x y z mw), PersB (gsAt ch itr) (ZRise ch z) g := by
  intro g hg
  have K := fun u => mux_step_pers M (hp x) (hp y) (hp c) (hp z) (hh c) u
  simp only [gatesK, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl | rfl | rfl
  · intro v u he hn; exact ((K u).1.app v he.1 he.2 hn).elim Or.inl (fun h => Or.inr (Or.inl h))
  · intro v u he hn; exact ((K u).2.1.app v he.1 he.2 hn).elim Or.inl (fun h => Or.inr (Or.inl h))
  · intro v u he hn; exact ((K u).2.2.1.app v he hn).elim Or.inl (fun h => Or.inr (Or.inl h))
  · intro v u he hn
    rcases (K u).2.2.2.1.app v he.1 he.2 hn with h | h | ⟨rfl, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨he.2, h⟩)
  · intro v u he hn
    rcases (K u).2.2.2.2.1.app v he.1 he.2 hn with h | h | ⟨rfl, h⟩
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr ⟨he.2, h⟩)
  · intro v u he hn; exact ((K u).2.2.2.2.2.app v he hn).elim Or.inl (fun h => Or.inr (Or.inl h))

end

/-- **Persistence of gcd_hw** (every operator except the muxes). For `a, b < 2^31`, on every
run meeting H_CELLS, H_BUNDLE and H_START_ONCE, every gate of every operator that is not a
2-way or 3-way mux is persistent, the arbiter grants included. -/
theorem gcd_hw_persistent (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (ch : Fin NC → Chan) (itr : Itr)
    (H_CELLS : ∀ p : Fin NO, CellI ch (srcV a b) itr p (opAt p))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1) :
    ∀ p : Fin NO, (∀ c x y z mw, opAt p ≠ .mux c x y z mw) →
      (∀ c x0 x1 x2 z nw, opAt p ≠ .muxn c x0 x1 x2 z nw) →
      ∀ g ∈ gatesK p (opAt p) ++ grantsK p (opAt p), Pers (gsAt ch itr) g := by
  have hC : ∀ p : Fin NO, Cell ch (srcV a b) (opAt p) := fun p => cellI_cell _ (H_CELLS p)
  have hp := gcd_hw_protocol a b ch hC H_BUNDLE
  obtain ⟨y, ls, hy, hex⟩ := good_run ha hb
  have hW := walk_ok hy hex
  intro p hm hmn g hg
  have M := H_CELLS p
  cases hk : opAt p with
  | mux c x y z mw => exact absurd hk (hm c x y z mw)
  | muxn c x0 x1 x2 z nw => exact absurd hk (hmn c x0 x1 x2 z nw)
  | forkG i os =>
    rw [hk] at hg M; simp only [grantsK, List.append_nil] at hg
    exact pers_fork M hp g hg
  | forkH i os l h d hs =>
    rw [hk] at hg M; simp only [grantsK, List.append_nil] at hg
    exact pers_fork M hp g hg
  | join ins o e js jw =>
    rw [hk] at hg M; simp only [grantsK, List.append_nil] at hg
    exact pers_join M hp g hg
  | bjoin ins o ec ed =>
    rw [hk] at hg M; simp only [grantsK, List.append_nil] at hg
    exact pers_join M hp g hg
  | steerC j t f =>
    rw [hk] at hg M; simp only [gatesK, grantsK, List.append_nil] at hg
    exact pers_steer M hp H_BUNDLE g hg
  | steerD j t f fd sw =>
    rw [hk] at hg M; simp only [gatesK, grantsK, List.append_nil] at hg
    exact pers_steer M hp H_BUNDLE g hg
  | amerge x u z w =>
    rw [hk] at hg M
    exact pers_amerge M hp
      (gcd_hw_never_contested a b ch hC H_BUNDLE H_START_ONCE y hy hW p x u z w hk _ _ M) g hg
  | link i o =>
    rw [hk] at hg M; simp only [gatesK, grantsK, List.append_nil] at hg
    exact pers_link M hp g hg
  | src z which d =>
    rw [hk] at hg; simp only [gatesK, grantsK, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hg
    subst hg; exact pers_src (hp z)
  | sink i =>
    rw [hk] at hg; simp only [gatesK, grantsK, List.append_nil, List.mem_cons, List.not_mem_nil,
      or_false] at hg
    subst hg; exact pers_sink (hp i)

/-- **The 2-way muxes of gcd_hw**: persistent except that an input acknowledge's falling
excitation may be withdrawn by `z_ack` rising in the same step (`ZRise`). -/
theorem gcd_hw_mux_persistent (a b : Nat) (ch : Fin NC → Chan) (itr : Itr)
    (H_CELLS : ∀ p : Fin NO, CellI ch (srcV a b) itr p (opAt p))
    (H_BUNDLE : ∀ c, Held (ch c)) :
    ∀ p c x y z mw, opAt p = .mux c x y z mw →
      ∀ g ∈ gatesK p (opAt p), PersB (gsAt ch itr) (ZRise ch z) g := by
  have hC : ∀ p : Fin NO, Cell ch (srcV a b) (opAt p) := fun p => cellI_cell _ (H_CELLS p)
  have hp := gcd_hw_protocol a b ch hC H_BUNDLE
  intro p c x y z mw hk g hg
  have M := H_CELLS p
  rw [hk] at hg M
  exact pers_mux M hp H_BUNDLE g hg

end Formal.Net.CapNet.Live.Nd3
