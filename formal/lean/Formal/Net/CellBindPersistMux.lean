import Formal.Net.CellBindPersistOps

/-!
# Probe C-O4b (persistence 3/3, part 1): mux and muxN without H_LEAF_PERSIST / H_REQ_PERSIST

bd_mux: the join C-elements `j0`, `j1` feed `uor` and the plain request delay `udly`.
O4 needed H_LEAF_PERSIST on `j0`, `j1` (they move only while equal to `z_req`) and
H_REQ_PERSIST on `udly` (its input `uor` moves only when `z_req` shows it). Here both come
out of one induction (`mux_core`): the first from C-8f's reachable-state table at that tick
(`mux_leaf0/1`: an excited join already equals `z_req`), the second from `or_inv` (when `uor`
differs from `z_req`, it already shows the OR of the joins, so it is not excited).

bdc_muxn3: the same for the three join C-elements in front of `|j` (H_MUXN_OR stays a
hypothesis) and the side-tapped request delay (H_CHAIN_SETTLED stays), using C-8l's generated
table (`muxn_leaf`, kernel `decide` over all 2^13 * 4 encoded states).
-/

namespace Formal.Net.CellBind.Persist
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CellBind Formal.Net.CellBind.Ops
open Formal.Gen Formal.Gen.Cells Formal.Net.Ops.Gen Formal.Net.CapNet

/-! ## Decided facts about the existing tables -/

set_option maxRecDepth 100000 in
theorem mux_leaf0 : ∀ e ∈ Mux.tbl, ∀ v : Bool, v ≠ e.j0 → e.xr = v → (e.cr && !e.s) = v →
    e.j0 = e.zr := by decide +kernel

set_option maxRecDepth 100000 in
theorem mux_leaf1 : ∀ e ∈ Mux.tbl, ∀ v : Bool, v ≠ e.j1 → e.yr = v → (e.cr && e.s) = v →
    e.j1 = e.zr := by decide +kernel

def LeafAt (e : MuxN.MS) : Prop := MuxN.mem e = true →
  (∀ v : Bool, v ≠ e.j0 → e.r0 = v → (e.cr && e.s == 0) = v → e.j0 = e.zr) ∧
  (∀ v : Bool, v ≠ e.j1 → e.r1 = v → (e.cr && e.s == 1) = v → e.j1 = e.zr) ∧
  (∀ v : Bool, v ≠ e.j2 → e.r2 = v → (e.cr && e.s == 2) = v → e.j2 = e.zr)

instance (e : MuxN.MS) : Decidable (LeafAt e) := by unfold LeafAt; exact inferInstance

def Leaf (s0 : Nat) : Prop := ∀ e0 e1 e2 e3 e4 e5 e6 e7 e8 e9 e10 e11 e12 : Bool,
    LeafAt ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, s0⟩

instance (s0 : Nat) : Decidable (Leaf s0) := by unfold Leaf; exact inferInstance

set_option maxRecDepth 100000 in
theorem leaf0 : Leaf 0 := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf1 : Leaf 1 := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf2 : Leaf 2 := by decide +kernel
set_option maxRecDepth 100000 in
theorem leaf3 : Leaf 3 := by decide +kernel

theorem muxn_leaf : ∀ e : MuxN.MS, e.s < 4 → LeafAt e := by
  intro ⟨e0, e1, e2, e3, e4, e5, e6, e7, e8, e9, e10, e11, e12, s⟩ hs
  simp only at hs
  match s, hs with
  | 0, _ => exact leaf0 _ _ _ _ _ _ _ _ _ _ _ _ _
  | 1, _ => exact leaf1 _ _ _ _ _ _ _ _ _ _ _ _ _
  | 2, _ => exact leaf2 _ _ _ _ _ _ _ _ _ _ _ _ _
  | 3, _ => exact leaf3 _ _ _ _ _ _ _ _ _ _ _ _ _

/-! ## Mux -/

/-- O4's `GenMux` without H_LEAF_PERSIST and without H_REQ_PERSIST on `udly`. -/
structure GenMuxP (sel : Nat → Bool) (x y c z : Chan) (j0 j1 : Trace) : Prop where
  cj0 : CNode muxJ0F (fun t => (x.req t, c.req t, sel (c.dat t))) j0
  cj1 : CNode muxJ1F (fun t => (y.req t, c.req t, sel (c.dat t))) j1
  cxa : CNode muxXaF (fun t => (j0 t, z.ack t)) x.ack
  cya : CNode muxYaF (fun t => (j1 t, z.ack t)) y.ack
  zr : ∃ e, LutSI (fun p : Bool × Bool => genF bd_mux_W2 "uor" .O ["j0", "j1"] [p.1, p.2])
      (fun t => (j0 t, j1 t)) e ∧ GenBufChainP e z.req ∧ e 0 = z.req 0
  H_WIRE_DI : ∀ t, c.ack (t + 1) ≠ c.ack t → c.ack (t + 1) = z.ack t
  H_DATA_COMB : ∀ t, z.dat t = if sel (c.dat t) then y.dat t else x.dat t
  i0 : j0 0 = false
  i1 : j1 0 = false
  iz : z.req 0 = false
  ix : x.ack 0 = false
  iy : y.ack 0 = false
  ic : c.ack 0 = false

theorem muxP_of {sel : Nat → Bool} {x y c z : Chan} {j0 j1 : Trace} (h : GenMux sel x y c z j0 j1) :
    GenMuxP sel x y c z j0 j1 := by
  obtain ⟨e, he, hch, he0, _⟩ := h.zr
  exact ⟨h.cj0, h.cj1, h.cxa, h.cya, ⟨e, he, bufchainP_of hch, he0⟩, h.H_WIRE_DI, h.H_DATA_COMB,
    h.i0, h.i1, h.iz, h.ix, h.iy, h.ic⟩

/-- The lumped request field of `Mux.Mux` at step `t`. -/
def ZR (z : Chan) (j0 j1 : Trace) (t : Nat) : Prop :=
  z.req (t + 1) ≠ z.req t → z.req (t + 1) = (j0 t || j1 t)

variable {sel : Nat → Bool} {x y c z : Chan} {j0 j1 : Trace}

theorem muxP_bound (h : GenMuxP sel x y c z j0 j1) :
    (∀ t, j0 (t + 1) ≠ j0 t → x.req t = j0 (t + 1) ∧ (c.req t && !sel (c.dat t)) = j0 (t + 1)) ∧
    (∀ t, j1 (t + 1) ≠ j1 t → y.req t = j1 (t + 1) ∧ (c.req t && sel (c.dat t)) = j1 (t + 1)) ∧
    (∀ t, x.ack (t + 1) ≠ x.ack t → j0 t = x.ack (t + 1) ∧ z.ack t = x.ack (t + 1)) ∧
    (∀ t, y.ack (t + 1) ≠ y.ack t → j1 t = y.ack (t + 1) ∧ z.ack t = y.ack (t + 1)) := by
  obtain ⟨q0, h0, f0⟩ := h.cj0
  obtain ⟨q1, h1, f1⟩ := h.cj1
  obtain ⟨q2, h2, f2⟩ := h.cxa
  obtain ⟨q3, h3, f3⟩ := h.cya
  exact mux_bound h0 f0 h1 f1 h2 f2 h3 f3

theorem mux_fz (h : GenMuxP sel x y c z j0 j1) (S : Nat) (hc : ∀ t, t < S → ZR z j0 j1 t) :
    Mux.Mux sel (fzC S x) (fzC S y) (fzC S c) (fzC S z) (fz S j0) (fz S j1) := by
  have B := muxP_bound h
  refine ⟨fun t hm => ?_, fun t hm => ?_, fun t hm => ?_, fun t hm => ?_, fun t hm => ?_,
    fun t hm => ?_, fun t => h.H_DATA_COMB _, by rw [fz0]; exact h.i0, by rw [fz0]; exact h.i1,
    by simp only [fzC, fz0]; exact h.iz, by simp only [fzC, fz0]; exact h.ix,
    by simp only [fzC, fz0]; exact h.iy, by simp only [fzC, fz0]; exact h.ic⟩ <;>
  · have ht := fz_move hm
    simp only [fzC, (fz_lt _ ht).1, (fz_lt _ ht).2, fzD_le _ (Nat.le_of_lt ht)] at hm ⊢
    first
    | exact B.1 t hm
    | exact B.2.1 t hm
    | exact hc t ht hm
    | exact B.2.2.1 t hm
    | exact B.2.2.2 t hm
    | exact h.H_WIRE_DI t hm

/-- **Mux, joint induction.** -/
theorem mux_core (h : GenMuxP sel x y c z j0 j1) (hx : x.req 0 = false) (hy : y.req 0 = false)
    (hc0 : c.req 0 = false) (hz : z.ack 0 = false) (hh : Held c) (T : Nat)
    (hp : ∀ s, s < T → SendStep x s ∧ SendStep y s ∧ SendStep c s ∧ RecvStep z s) :
    ∀ u, u ≤ T → ZR z j0 j1 u := by
  have B := muxP_bound h
  obtain ⟨e, he, hch, he0⟩ := h.zr
  have hE : ∀ t, e (t + 1) ≠ e t → e (t + 1) = [j0, j1].any (fun l => l t) := by
    intro t ht; rw [he t ht]
    show genF bd_mux_W2 "uor" .O ["j0", "j1"] [j0 t, j1 t] = _
    rw [uor_gate]; simp
  -- the joint claim: leaf persistence and the chain's lumping, at every step `≤ T`
  have Q : ∀ u, u ≤ T → (∀ l ∈ [j0, j1], l (u + 1) ≠ l u → l u = z.req u) ∧
      (z.req (u + 1) ≠ z.req u → z.req (u + 1) = e u) := by
    intro u
    induction u using Nat.strongRecOn with
    | _ u ih =>
      intro hu
      have hL : ∀ l ∈ [j0, j1], ∀ t, t < u → l (t + 1) ≠ l t → l t = z.req t :=
        fun l hl t ht => (ih t ht (by omega)).1 l hl
      have hR : ∀ t, t < u → z.req (t + 1) ≠ z.req t → z.req (t + 1) = e t :=
        fun t ht => (ih t ht (by omega)).2
      refine ⟨?_, ?_⟩
      · -- leaves: C-8f's table at `u`, on the run frozen at `u`
        have hZ : ∀ t, t < u → ZR z j0 j1 t := by
          intro t ht hm
          rw [or_lumped_upto t (fun t _ => hE t) (fun t' ht' => hR t' (by omega))
            (fun l hl t' ht' => hL l hl t' (by omega)) he0 hm]
          simp
        have M := mux_fz h u hZ
        obtain ⟨dc, dxo, dyo, hm, _⟩ := Mux.mux_inv M (by simp only [fzC, fz0]; exact hx)
          (by simp only [fzC, fz0]; exact hy) (by simp only [fzC, fz0]; exact hc0)
          (by simp only [fzC, fz0]; exact hz) (held_fz hh) u
          (fun s hs => by
            obtain ⟨a1, a2, a3, a4⟩ := hp s (by omega)
            simp only [SendStep, RecvStep, fzC, (fz_lt _ hs).1, (fz_lt _ hs).2]
            exact ⟨a1, a2, a3, a4⟩)
        simp only [Mux.st, fzC, fz_le _ (Nat.le_refl u), fzD_le _ (Nat.le_refl u)] at hm
        intro l hl hlm
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
        rcases hl with rfl | rfl
        · obtain ⟨b1, b2⟩ := B.1 u hlm
          exact mux_leaf0 _ (Mux.mem_of_contains hm) _ hlm b1 b2
        · obtain ⟨b1, b2⟩ := B.2.1 u hlm
          exact mux_leaf1 _ (Mux.mem_of_contains hm) _ hlm b1 b2
      · -- the chain: `uor` moves only when `z_req` shows it (or_inv), so it is lumped
        refine bufchain_lumped_upto hch u ?_
        intro t ht hem
        apply Classical.byContradiction; intro hne
        have hor := or_inv_upto t (fun t _ => hE t) (fun t' ht' => hR t' (by omega))
          (fun l hl t' ht' => hL l hl t' (by omega)) he0 (Ne.symm hne)
        exact hem (by rw [hE t hem, hor])
  intro u hu hm
  rw [or_lumped_upto u (fun t _ => hE t) (fun t ht => (Q t (by omega)).2)
    (fun l hl t ht => (Q t (by omega)).1 l hl) he0 hm]
  simp

theorem mux_all (h : GenMuxP sel x y c z j0 j1) (hz : ∀ u, ZR z j0 j1 u) :
    Mux.Mux sel x y c z j0 j1 := by
  have B := muxP_bound h
  exact ⟨B.1, B.2.1, hz, B.2.2.1, B.2.2.2, h.H_WIRE_DI, h.H_DATA_COMB, h.i0, h.i1, h.iz, h.ix,
    h.iy, h.ic⟩

/-! ## MuxN -/

/-- O4's `GenMuxN` without H_LEAF_PERSIST. -/
structure GenMuxNP (sel : Nat → Nat) (xs : Nat → Chan) (c z : Chan) (j : Nat → Trace) : Prop where
  cj : ∀ k, k < 3 → CNode c2F (fun t => ((xs k).req t, c.req t && (sel (c.dat t) == k))) (j k)
  xa : ∀ k, k < 3 → CNode c2F (fun t => (j k t, z.ack t)) (xs k).ack
  zr : ∃ e, (∀ t, e (t + 1) ≠ e t → e (t + 1) = [j 0, j 1, j 2].any (fun l => l t)) ∧
      GenChain e z.req ∧ e 0 = z.req 0
  H_WIRE_DI : ∀ t, c.ack (t + 1) ≠ c.ack t → c.ack (t + 1) = z.ack t
  H_DATA_COMB : ∀ t, sel (c.dat t) < 3 → z.dat t = (xs (sel (c.dat t))).dat t
  ij : ∀ k, k < 3 → j k 0 = false
  iz : z.req 0 = false
  ix : ∀ k, k < 3 → (xs k).ack 0 = false
  ic : c.ack 0 = false

theorem muxnP_of {sel : Nat → Nat} {xs : Nat → Chan} {c z : Chan} {j : Nat → Trace}
    (h : GenMuxN sel xs c z j) : GenMuxNP sel xs c z j := by
  obtain ⟨e, hE, hch, he0, _⟩ := h.zr
  exact ⟨h.cj, h.xa, ⟨e, hE, hch, he0⟩, h.H_WIRE_DI, h.H_DATA_COMB, h.ij, h.iz, h.ix, h.ic⟩

def ZRN (z : Chan) (j : Nat → Trace) (t : Nat) : Prop :=
  z.req (t + 1) ≠ z.req t → z.req (t + 1) = (j 0 t || j 1 t || j 2 t)

section muxn
variable {sel : Nat → Nat} {xs : Nat → Chan} {c z : Chan} {j : Nat → Trace}

theorem muxnP_cj (h : GenMuxNP sel xs c z j) : ∀ k, k < 3 → ∀ t, j k (t + 1) ≠ j k t →
    (xs k).req t = j k (t + 1) ∧ (c.req t && (sel (c.dat t) == k)) = j k (t + 1) := by
  intro k hk t ht
  have hg : ∀ (p : Bool × Bool) (q : Bool), c2F p q = cel2 p.1 p.2 q := fun p q => c2_gate p.1 p.2 q
  have e1 : j k (t + 1) = cel2 ((xs k).req t) (c.req t && (sel (c.dat t) == k)) (j k t) :=
    cnode_move hg (h.cj k hk) t ht
  have m := cel2_move ((xs k).req t) (c.req t && (sel (c.dat t) == k)) (j k t) (by rw [← e1]; exact ht)
  rw [← e1] at m; exact m

theorem muxnP_xa (h : GenMuxNP sel xs c z j) : ∀ k, k < 3 → ∀ t, (xs k).ack (t + 1) ≠ (xs k).ack t →
    j k t = (xs k).ack (t + 1) ∧ z.ack t = (xs k).ack (t + 1) := by
  intro k hk t ht
  have hg : ∀ (p : Bool × Bool) (q : Bool), c2F p q = cel2 p.1 p.2 q := fun p q => c2_gate p.1 p.2 q
  have e1 : (xs k).ack (t + 1) = cel2 (j k t) (z.ack t) ((xs k).ack t) := cnode_move hg (h.xa k hk) t ht
  have m := cel2_move (j k t) (z.ack t) ((xs k).ack t) (by rw [← e1]; exact ht)
  rw [← e1] at m; exact m

theorem muxn_fz (h : GenMuxNP sel xs c z j) (S : Nat) (hc : ∀ t, t < S → ZRN z j t) :
    MuxN.MuxN sel (fun k => fzC S (xs k)) (fzC S c) (fzC S z) (fun k => fz S (j k)) := by
  refine ⟨fun k hk t hm => ?_, fun t hm => ?_, fun k hk t hm => ?_, fun t hm => ?_,
    fun t hs => h.H_DATA_COMB _ hs, fun k hk => by rw [fz0]; exact h.ij k hk,
    by simp only [fzC, fz0]; exact h.iz, fun k hk => by simp only [fzC, fz0]; exact h.ix k hk,
    by simp only [fzC, fz0]; exact h.ic⟩ <;>
  · have ht := fz_move hm
    simp only [fzC, (fz_lt _ ht).1, (fz_lt _ ht).2, fzD_le _ (Nat.le_of_lt ht)] at hm ⊢
    first
    | exact muxnP_cj h k hk t hm
    | exact hc t ht hm
    | exact muxnP_xa h k hk t hm
    | exact h.H_WIRE_DI t hm

theorem cases3' {P : Nat → Prop} (h : ∀ k, k < 3 → P k) : P 0 ∧ P 1 ∧ P 2 :=
  ⟨h 0 (by omega), h 1 (by omega), h 2 (by omega)⟩

/-- **MuxN, joint induction.** -/
theorem muxn_core (h : GenMuxNP sel xs c z j) (hx : ∀ k, k < 3 → (xs k).req 0 = false)
    (hc0 : c.req 0 = false) (hz : z.ack 0 = false) (hh : Held c) (T : Nat)
    (hp : ∀ s, s < T → (∀ k, k < 3 → SendStep (xs k) s) ∧ SendStep c s ∧ RecvStep z s) :
    ∀ u, u ≤ T → ZRN z j u := by
  obtain ⟨e, hE, hch, he0⟩ := h.zr
  have hR := chain_lumped hch
  have Q : ∀ u, u ≤ T → ∀ l ∈ [j 0, j 1, j 2], l (u + 1) ≠ l u → l u = z.req u := by
    intro u
    induction u using Nat.strongRecOn with
    | _ u ih =>
      intro hu
      have hL : ∀ l ∈ [j 0, j 1, j 2], ∀ t, t < u → l (t + 1) ≠ l t → l t = z.req t :=
        fun l hl t ht => ih t ht (by omega) l hl
      have hZ : ∀ t, t < u → ZRN z j t := by
        intro t ht hm
        rw [or_lumped_upto t (fun t _ => hE t) (fun t' _ => hR t')
          (fun l hl t' ht' => hL l hl t' (by omega)) he0 hm]
        simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
      have M := muxn_fz h u hZ
      have I := MuxN.muxn_inv M (fun k hk => by simp only [fzC, fz0]; exact hx k hk)
        (by simp only [fzC, fz0]; exact hc0) (by simp only [fzC, fz0]; exact hz) (held_fz hh) u
        (fun s hs => by
          obtain ⟨a1, a2, a3⟩ := hp s (by omega)
          refine ⟨fun k hk => ?_, ?_, ?_⟩
          · have := a1 k hk
            simp only [SendStep, fzC, (fz_lt _ hs).1, (fz_lt _ hs).2]; exact this
          · simp only [SendStep, fzC, (fz_lt _ hs).1, (fz_lt _ hs).2]; exact a2
          · simp only [RecvStep, fzC, (fz_lt _ hs).1, (fz_lt _ hs).2]; exact a3)
      have hm := I.1
      simp only [MuxN.st, fzC, fz_le _ (Nat.le_refl u), fzD_le _ (Nat.le_refl u)] at hm
      have Lf := muxn_leaf _ (MuxN.clip_lt _) hm
      intro l hl hlm
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl
      · obtain ⟨b1, b2⟩ := muxnP_cj h 0 (by omega) u hlm
        rw [← MuxN.clip_beq _ _ (by omega)] at b2
        exact Lf.1 _ hlm b1 b2
      · obtain ⟨b1, b2⟩ := muxnP_cj h 1 (by omega) u hlm
        rw [← MuxN.clip_beq _ _ (by omega)] at b2
        exact Lf.2.1 _ hlm b1 b2
      · obtain ⟨b1, b2⟩ := muxnP_cj h 2 (by omega) u hlm
        rw [← MuxN.clip_beq _ _ (by omega)] at b2
        exact Lf.2.2 _ hlm b1 b2
  intro u hu hm
  rw [or_lumped_upto u (fun t _ => hE t) (fun t _ => hR t)
    (fun l hl t ht => Q t (by omega) l hl) he0 hm]
  simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]

theorem muxn_all (h : GenMuxNP sel xs c z j) (hz : ∀ u, ZRN z j u) : MuxN.MuxN sel xs c z j :=
  ⟨muxnP_cj h, hz, muxnP_xa h, h.H_WIRE_DI, h.H_DATA_COMB, h.ij, h.iz, h.ix, h.ic⟩

end muxn

end Formal.Net.CellBind.Persist
