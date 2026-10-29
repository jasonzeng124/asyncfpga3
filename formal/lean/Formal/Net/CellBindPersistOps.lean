import Formal.Net.CellBindPersist

/-!
# Probe C-O4b (persistence 2/3): fork, compute join and link without H_LEAF_PERSIST / H_REQ_PERSIST

For each kind: the generated structure WITHOUT the persistence hypothesis (`GenForkP`,
`GenJoinKP`, `GenLinkP`), and the **joint induction**: if the operator's channels obeyed the
four-phase protocol before `T`, its lumped Ops field holds at every step `≤ T`
(`fork_core`, `join_core`, `link_core`). The persistence at a step `s` comes from the
operator's existing reachable-state invariant at `s` (C-8f/8l's `fork_inv`, `join_inv`,
`link_inv`, applied to the run frozen at `s`, which needs the lumped field only before `s`)
plus one decided fact about the invariant:

* fork (`finv_leaf`): a branch acknowledge that is excited (`ack ≠ req`, the receiver's
  protocol) equals the fork's acknowledge;
* compute join (`jinv_leaf`): an input request that may move (`req = ack`, the sender's
  protocol) equals the joined output request;
* link (`link_leaf`): whenever the controller `c` is excited, `req_out` already equals `c`
  (so the rdly chain's input moves only when its end shows it: end-only persistence).
-/

namespace Formal.Net.CellBind.Persist
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CellBind Formal.Net.CellBind.Ops
open Formal.Gen Formal.Gen.Cells Formal.Net.Ops.Gen Formal.Net.CapNet Formal.Net.CellBind.KOps
open Formal.Cells.LinkHandshake (ctlB)

/-! ## Decided facts about the existing invariants -/

theorem finv_leaf : ∀ ar aa r k : Bool, Fork.FInv ar aa r k = true → k ≠ r → k = aa := by decide

theorem jinv_leaf : ∀ or oa r k : Bool, Join.JInv or oa r k = true → r = k → r = or := by decide

theorem link_leaf : ∀ e ∈ Link.ltbl, ctlB e.ir e.oa e.c false ≠ e.c → e.orq = e.c := by decide

/-! ## Fork -/

/-- O4's `ForkTree` without H_LEAF_PERSIST. -/
def ForkTreeP (r : Trace) : List Trace → Prop
  | [a0, a1] => CNode f2F (fun t => (a0 t, a1 t)) r
  | [a0, a1, a2] => CNode f3F (fun t => (a0 t, a1 t, a2 t)) r
  | [a0, a1, a2, a3] => CNode f4F (fun t => (a0 t, a1 t, a2 t, a3 t)) r
  | [a0, a1, a2, a3, a4] => ∃ m, CNode f5cF (fun t => (a0 t, a1 t, a2 t, a3 t)) m ∧
      CNode f5tF (fun t => (m t, a4 t)) r ∧ m 0 = r 0
  | [a0, a1, a2, a3, a4, a5] => ∃ m1 m2, CNode f6aF (fun t => (a0 t, a1 t, a2 t, a3 t)) m1 ∧
      CNode f6bF (fun t => (a4 t, a5 t)) m2 ∧ CNode f6tF (fun t => (m1 t, m2 t)) r ∧
      m1 0 = r 0 ∧ m2 0 = r 0
  | _ => False

theorem treeP_of {r : Trace} : ∀ {ls : List Trace}, ForkTree r ls → ForkTreeP r ls
  | [_, _], h => h
  | [_, _, _], h => h
  | [_, _, _, _], h => h
  | [_, _, _, _, _], h => by obtain ⟨m, a, b, c, _⟩ := h; exact ⟨m, a, b, c⟩
  | [_, _, _, _, _, _], h => by obtain ⟨m1, m2, a, b, c, d, e, _⟩ := h; exact ⟨m1, m2, a, b, c, d, e⟩
  | [], h => h.elim
  | [_], h => h.elim
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h => h.elim

theorem c4_cel {m : Trace} {F : Bool × Bool × Bool × Bool → Bool → Bool}
    (hg : ∀ p q, F p q = cel4 p.1 p.2.1 p.2.2.1 p.2.2.2 q) {a0 a1 a2 a3 : Trace}
    (h : CNode F (fun t => (a0 t, a1 t, a2 t, a3 t)) m) :
    ∀ t, m (t + 1) ≠ m t → ∀ l ∈ [a0, a1, a2, a3], l t = m (t + 1) := by
  intro t ht l hl
  have e := cnode_move hg h t ht
  have mv := cel4_move _ _ _ _ _ (by rw [← e]; exact ht); rw [← e] at mv
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
  rcases hl with rfl | rfl | rfl | rfl
  · exact mv.1
  · exact mv.2.1
  · exact mv.2.2.1
  · exact mv.2.2.2

theorem c2_cel {m : Trace} {F : Bool × Bool → Bool → Bool}
    (hg : ∀ p q, F p q = cel2 p.1 p.2 q) {a0 a1 : Trace} (h : CNode F (fun t => (a0 t, a1 t)) m) :
    ∀ t, m (t + 1) ≠ m t → a0 t = m (t + 1) ∧ a1 t = m (t + 1) := by
  intro t ht
  have e := cnode_move hg h t ht
  have mv := cel2_move _ _ _ (by rw [← e]; exact ht); rw [← e] at mv; exact mv

/-- The tree's lumped C-element field at step `u`, from leaf persistence before `u`. -/
theorem treeP_cel {r : Trace} : ∀ {ls : List Trace}, ForkTreeP r ls → ∀ u,
    (∀ l ∈ ls, ∀ t, t < u → l (t + 1) ≠ l t → l t = r t) →
    r (u + 1) ≠ r u → ∀ l ∈ ls, l u = r (u + 1)
  | [a0, a1], h, u, _, ht, l, hl => tree_cel (r := r) (ls := [a0, a1]) h u ht l hl
  | [a0, a1, a2], h, u, _, ht, l, hl => tree_cel (r := r) (ls := [a0, a1, a2]) h u ht l hl
  | [a0, a1, a2, a3], h, u, _, ht, l, hl => tree_cel (r := r) (ls := [a0, a1, a2, a3]) h u ht l hl
  | [a0, a1, a2, a3, a4], h, u, hL, ht, l, hl => by
    obtain ⟨mm, hc, htop, h0⟩ := h
    have hC := c4_cel f5c_gate hc
    have hT := c2_cel f5t_gate htop
    have hR : ∀ t, t ≤ u → r (t + 1) ≠ r t → r (t + 1) = mm t := fun t _ ht => (hT t ht).1.symm
    have hL4 : ∀ l ∈ [a0, a1, a2, a3], ∀ t, t < u → l (t + 1) ≠ l t → l t = r t :=
      fun l hl => hL l (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
        rcases hl with h | h | h | h <;> simp [h])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl
    · exact cel_lumped_upto u (fun t _ => hC t) hR hL4 h0 ht _ (by simp)
    · exact cel_lumped_upto u (fun t _ => hC t) hR hL4 h0 ht _ (by simp)
    · exact cel_lumped_upto u (fun t _ => hC t) hR hL4 h0 ht _ (by simp)
    · exact cel_lumped_upto u (fun t _ => hC t) hR hL4 h0 ht _ (by simp)
    · exact (hT u ht).2
  | [a0, a1, a2, a3, a4, a5], h, u, hL, ht, l, hl => by
    obtain ⟨m1, m2, hc1, hc2, htop, h01, h02⟩ := h
    have hC1 := c4_cel f6a_gate hc1
    have hC2 : ∀ t, m2 (t + 1) ≠ m2 t → ∀ l ∈ [a4, a5], l t = m2 (t + 1) := by
      intro t ht' l hl
      have := c2_cel f6b_gate hc2 t ht'
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact this.1
      · exact this.2
    have hT := c2_cel f6t_gate htop
    have hR1 : ∀ t, t ≤ u → r (t + 1) ≠ r t → r (t + 1) = m1 t := fun t _ ht => (hT t ht).1.symm
    have hR2 : ∀ t, t ≤ u → r (t + 1) ≠ r t → r (t + 1) = m2 t := fun t _ ht => (hT t ht).2.symm
    have hL1 : ∀ l ∈ [a0, a1, a2, a3], ∀ t, t < u → l (t + 1) ≠ l t → l t = r t :=
      fun l hl => hL l (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
        rcases hl with h | h | h | h <;> simp [h])
    have hL2 : ∀ l ∈ [a4, a5], ∀ t, t < u → l (t + 1) ≠ l t → l t = r t :=
      fun l hl => hL l (by
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
        rcases hl with h | h <;> simp [h])
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
    · exact cel_lumped_upto u (fun t _ => hC1 t) hR1 hL1 h01 ht _ (by simp)
    · exact cel_lumped_upto u (fun t _ => hC1 t) hR1 hL1 h01 ht _ (by simp)
    · exact cel_lumped_upto u (fun t _ => hC1 t) hR1 hL1 h01 ht _ (by simp)
    · exact cel_lumped_upto u (fun t _ => hC1 t) hR1 hL1 h01 ht _ (by simp)
    · exact cel_lumped_upto u (fun t _ => hC2 t) hR2 hL2 h02 ht _ (by simp)
    · exact cel_lumped_upto u (fun t _ => hC2 t) hR2 hL2 h02 ht _ (by simp)
  | [], h, _, _, _, _, _ => h.elim
  | [_], h, _, _, _, _, _ => h.elim
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h, _, _, _, _, _ => h.elim

theorem treeP_ne {r : Trace} : ∀ {ls : List Trace}, ForkTreeP r ls → ls ≠ []
  | [], h => h.elim
  | _ :: _, _ => List.cons_ne_nil _ _

/-- The fork, as generated, without H_LEAF_PERSIST. -/
structure GenForkP (a : Chan) (os : List Chan) : Prop where
  tree : ForkTreeP a.ack (os.map Chan.ack)
  H_WIRE_DI : ∀ o ∈ os, ∀ t, o.req (t + 1) ≠ o.req t → o.req (t + 1) = a.req t
  H_DATA_WIRE : ∀ o ∈ os, ∀ t, o.dat t = a.dat t
  initA : a.ack 0 = false
  initO : ∀ o ∈ os, o.req 0 = false

theorem forkP_of {a : Chan} {os : List Chan} (h : GenFork a os) : GenForkP a os :=
  ⟨treeP_of h.tree, h.H_WIRE_DI, h.H_DATA_WIRE, h.initA, h.initO⟩

/-- The lumped C-element field of `Fork.Fork` at step `t`. -/
def FCel (a : Chan) (os : List Chan) (t : Nat) : Prop :=
  a.ack (t + 1) ≠ a.ack t → ∀ o ∈ os, o.ack t = a.ack (t + 1)

variable {a : Chan} {os : List Chan}

theorem mem_fzC {S : Nat} {os : List Chan} {o : Chan} (h : o ∈ os.map (fzC S)) :
    ∃ o0, o0 ∈ os ∧ o = fzC S o0 := by
  obtain ⟨o0, h0, rfl⟩ := List.mem_map.mp h; exact ⟨o0, h0, rfl⟩

/-- The run frozen at `S` is a `Fork` once the field held before `S`. -/
theorem fork_fz (h : GenForkP a os) (S : Nat) (hc : ∀ t, t < S → FCel a os t) :
    Fork.Fork (fzC S a) (os.map (fzC S)) where
  ne := by
    intro he; exact treeP_ne h.tree (by simpa using he)
  wire := by
    intro o ho t hm
    obtain ⟨o0, h0, rfl⟩ := mem_fzC ho
    have ht := fz_move hm
    simp only [fzC, (fz_lt _ ht).1, (fz_lt _ ht).2] at hm ⊢
    exact h.H_WIRE_DI o0 h0 t hm
  cel := by
    intro t hm o ho
    obtain ⟨o0, h0, rfl⟩ := mem_fzC ho
    have ht := fz_move hm
    simp only [fzC, (fz_lt _ ht).1, (fz_lt _ ht).2] at hm ⊢
    exact hc t ht hm o0 h0
  dat := by
    intro o ho t
    obtain ⟨o0, h0, rfl⟩ := mem_fzC ho
    exact h.H_DATA_WIRE o0 h0 _
  initA := by simp only [fzC, fz0]; exact h.initA
  initO := by
    intro o ho
    obtain ⟨o0, h0, rfl⟩ := mem_fzC ho
    simp only [fzC, fz0]; exact h.initO o0 h0

/-- **Fork, joint induction.** Protocol before `T` ⟹ the lumped field at every step `≤ T`. -/
theorem fork_core (h : GenForkP a os) (hra : a.req 0 = false) (hka : ∀ o ∈ os, o.ack 0 = false)
    (T : Nat) (hp : ∀ s, s < T → Rules a s ∧ ∀ o ∈ os, Rules o s) : ∀ u, u ≤ T → FCel a os u := by
  intro u
  induction u using Nat.strongRecOn with
  | _ u ih =>
    intro hu hm o ho
    refine treeP_cel h.tree u ?_ hm o.ack (List.mem_map_of_mem ho)
    intro l hl s hs hlm
    obtain ⟨o', ho', rfl⟩ := List.mem_map.mp hl
    have hrec : o'.ack s ≠ o'.req s := ((hp s (by omega)).2 o' ho').2 hlm
    have F := fork_fz h s (fun t ht => ih t (by omega) (by omega))
    have hi := Fork.fork_inv F (by simp only [fzC, fz0]; exact hra)
      (fun o hom => by obtain ⟨o0, h0, rfl⟩ := mem_fzC hom; simp only [fzC, fz0]; exact hka o0 h0) s
      (fun s' hs' => ⟨rules_fz hs' (hp s' (by omega)).1, fun o hom => by
        obtain ⟨o0, h0, rfl⟩ := mem_fzC hom; exact rules_fz hs' ((hp s' (by omega)).2 o0 h0)⟩)
      (fzC s o') (List.mem_map_of_mem ho')
    simp only [fzC, fz_le _ (Nat.le_refl s)] at hi
    exact finv_leaf _ _ _ _ hi hrec

theorem fork_all (h : GenForkP a os) (hc : ∀ u, FCel a os u) : Fork.Fork a os :=
  ⟨by intro he; exact treeP_ne h.tree (by simp [he]), h.H_WIRE_DI, fun t ht o ho => hc t ht o ho,
    h.H_DATA_WIRE, h.initA, h.initO⟩

/-! ## Compute join (N = 1, 2, 3) -/

/-- O4b's `GenJoinK` without H_LEAF_PERSIST. -/
structure GenJoinKP (g : List Nat → Nat) (ins : List Chan) (o : Chan) : Prop where
  node : ∃ m, JoinNodeK m ins ∧ GenChain m o.req ∧ m 0 = o.req 0
  H_WIRE_DI : ∀ i ∈ ins, ∀ t, i.ack (t + 1) ≠ i.ack t → i.ack (t + 1) = o.ack t
  H_DATA_COMB : ∀ t, o.dat t = g (ins.map (fun i => i.dat t))
  initO : o.req 0 = false
  initI : ∀ i ∈ ins, i.ack 0 = false

theorem joinP_of {g : List Nat → Nat} {ins : List Chan} {o : Chan} (h : GenJoinK g ins o) :
    GenJoinKP g ins o := ⟨h.node, h.H_WIRE_DI, h.H_DATA_COMB, h.initO, h.initI⟩

def JCel (ins : List Chan) (o : Chan) (t : Nat) : Prop :=
  o.req (t + 1) ≠ o.req t → ∀ i ∈ ins, i.req t = o.req (t + 1)

variable {g : List Nat → Nat} {ins : List Chan} {o : Chan}

theorem joinP_ne (h : GenJoinKP g ins o) : ins ≠ [] := by
  obtain ⟨m, hJ, _, _⟩ := h.node; exact joinnode_ne hJ

theorem joinP_cel (h : GenJoinKP g ins o) (u : Nat)
    (hL : ∀ l ∈ ins.map Chan.req, ∀ t, t < u → l (t + 1) ≠ l t → l t = o.req t) : JCel ins o u := by
  obtain ⟨m, hJ, hch, h0⟩ := h.node
  have hR := chain_lumped hch
  intro ht i hi
  match ins, hJ, hi, hL with
  | [i0], hJ, hi, _ =>
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    rw [hi, hR u ht, hJ]
  | i0 :: i1 :: rest, hJ, hi, hL =>
    exact cel_lumped_upto u (fun t _ => joinnode_cel hJ (by simp) t) (fun t _ => hR t) hL h0 ht i.req
      (List.mem_map_of_mem hi)

theorem join_fz (h : GenJoinKP g ins o) (S : Nat) (hc : ∀ t, t < S → JCel ins o t) :
    Join.Join g (ins.map (fzC S)) (fzC S o) where
  ne := by intro he; exact joinP_ne h (by simpa using he)
  cel := by
    intro t hm i hi
    obtain ⟨i0, h0, rfl⟩ := mem_fzC hi
    have ht := fz_move hm
    simp only [fzC, (fz_lt _ ht).1, (fz_lt _ ht).2] at hm ⊢
    exact hc t ht hm i0 h0
  wire := by
    intro i hi t hm
    obtain ⟨i0, h0, rfl⟩ := mem_fzC hi
    have ht := fz_move hm
    simp only [fzC, (fz_lt _ ht).1, (fz_lt _ ht).2] at hm ⊢
    exact h.H_WIRE_DI i0 h0 t hm
  dat := by
    intro t
    simp only [fzC, fzD, List.map_map, Function.comp_def]
    exact h.H_DATA_COMB _
  initO := by simp only [fzC, fz0]; exact h.initO
  initI := by
    intro i hi
    obtain ⟨i0, h0, rfl⟩ := mem_fzC hi
    simp only [fzC, fz0]; exact h.initI i0 h0

/-- **Compute join, joint induction.** -/
theorem join_core (h : GenJoinKP g ins o) (hro : o.ack 0 = false) (hri : ∀ i ∈ ins, i.req 0 = false)
    (T : Nat) (hp : ∀ s, s < T → Rules o s ∧ ∀ i ∈ ins, Rules i s) : ∀ u, u ≤ T → JCel ins o u := by
  intro u
  induction u using Nat.strongRecOn with
  | _ u ih =>
    intro hu
    refine joinP_cel h u ?_
    intro l hl s hs hlm
    obtain ⟨i', hi', rfl⟩ := List.mem_map.mp hl
    have hsend : i'.req s = i'.ack s := ((hp s (by omega)).2 i' hi').1 hlm
    have J := join_fz h s (fun t ht => ih t (by omega) (by omega))
    have hv := Join.join_inv J (by simp only [fzC, fz0]; exact hro)
      (fun i hi => by obtain ⟨i0, h0, rfl⟩ := mem_fzC hi; simp only [fzC, fz0]; exact hri i0 h0) s
      (fun s' hs' => ⟨rules_fz hs' (hp s' (by omega)).1, fun i hi => by
        obtain ⟨i0, h0, rfl⟩ := mem_fzC hi; exact rules_fz hs' ((hp s' (by omega)).2 i0 h0)⟩)
      (fzC s i') (List.mem_map_of_mem hi')
    simp only [fzC, fz_le _ (Nat.le_refl s)] at hv
    exact jinv_leaf _ _ _ _ hv hsend

theorem join_all (h : GenJoinKP g ins o) (hc : ∀ u, JCel ins o u) : Join.Join g ins o :=
  ⟨joinP_ne h, fun t ht i hi => hc t ht i hi, h.H_WIRE_DI, h.H_DATA_COMB, h.initO, h.initI⟩

/-! ## Link -/

/-- O4's `GenLink` without H_REQ_PERSIST on `rdly`. (`uack` keeps H_CHAIN_SETTLED.) -/
structure GenLinkP (i o : Chan) (c : Trace) : Prop where
  ctl : CNode linkF (fun t => (i.req t, o.ack t)) c
  rdly : GenBufChainP c o.req
  uack : GenChain c i.ack
  H_LATCH_OPEN : ∀ t, c t = true → o.dat t = i.dat t
  H_LATCH_HOLD : ∀ t, c (t + 1) = false → o.dat (t + 1) = o.dat t
  ic : c 0 = false
  ii : i.ack 0 = false
  io : o.req 0 = false

theorem linkP_of {i o : Chan} {c : Trace} (h : GenLink i o c) : GenLinkP i o c :=
  ⟨h.ctl, bufchainP_of h.rdly, h.uack, h.H_LATCH_OPEN, h.H_LATCH_HOLD, h.ic, h.ii, h.io⟩

def LReq (o : Chan) (c : Trace) (t : Nat) : Prop := o.req (t + 1) ≠ o.req t → o.req (t + 1) = c t

variable {i : Chan} {c : Trace}

theorem linkP_cel (h : GenLinkP i o c) :
    ∀ t, c (t + 1) ≠ c t → c (t + 1) = ctlB (i.req t) (o.ack t) (c t) false := by
  obtain ⟨qp, hL, hF⟩ := h.ctl; exact link_bound hL hF

theorem link_fz (h : GenLinkP i o c) (S : Nat) (hc : ∀ t, t < S → LReq o c t) :
    Link.Link (fzC S i) (fzC S o) (fz S c) where
  H_CEL_SI := by
    intro t hm
    have ht := fz_move hm
    simp only [fzC, (fz_lt _ ht).1, (fz_lt _ ht).2] at hm ⊢
    exact linkP_cel h t hm
  H_ACK_DI := by
    intro t hm
    have ht := fz_move hm
    simp only [fzC, (fz_lt _ ht).1, (fz_lt _ ht).2] at hm ⊢
    exact chain_lumped h.uack t hm
  H_REQ_DI := by
    intro t hm
    have ht := fz_move hm
    simp only [fzC, (fz_lt _ ht).1, (fz_lt _ ht).2] at hm ⊢
    exact hc t ht hm
  H_LATCH_OPEN := by
    intro t hct
    exact h.H_LATCH_OPEN _ hct
  H_LATCH_HOLD := by
    intro t hct
    by_cases ht : t < S
    · simp only [(fz_lt _ ht).2] at hct
      simp only [fzC, fzD_le _ (show t ≤ S by omega), fzD_le _ (show t + 1 ≤ S by omega)]
      exact h.H_LATCH_HOLD t hct
    · exact fzD_succ S t o.dat ht
  ic := by rw [fz0]; exact h.ic
  ii := by simp only [fzC, fz0]; exact h.ii
  io := by simp only [fzC, fz0]; exact h.io

/-- **Link, joint induction.** -/
theorem link_core (h : GenLinkP i o c) (hi0 : i.req 0 = false) (ho0 : o.ack 0 = false) (T : Nat)
    (hp : ∀ s, s < T → SendStep i s ∧ RecvStep o s) : ∀ u, u ≤ T → LReq o c u := by
  intro u
  induction u using Nat.strongRecOn with
  | _ u ih =>
    intro hu
    refine bufchain_lumped_upto h.rdly u ?_
    intro s hs hcm
    have L := link_fz h s (fun t ht => ih t (by omega) (by omega))
    obtain ⟨d, q, hm, _⟩ := Link.link_inv L (by simp only [fzC, fz0]; exact hi0)
      (by simp only [fzC, fz0]; exact ho0) s
      (fun s' hs' => by
        have hr := hp s' (by omega)
        exact ⟨by simp only [SendStep, fzC, (fz_lt _ hs').1, (fz_lt _ hs').2]; exact hr.1,
          by simp only [RecvStep, fzC, (fz_lt _ hs').1, (fz_lt _ hs').2]; exact hr.2⟩)
    simp only [Link.lst, fzC, fz_le _ (Nat.le_refl s)] at hm
    have hx : ctlB (i.req s) (o.ack s) (c s) false ≠ c s := by
      rw [← linkP_cel h s hcm]; exact hcm
    exact link_leaf _ (Link.lmem hm) hx

theorem link_all (h : GenLinkP i o c) (hc : ∀ u, LReq o c u) : Link.Link i o c :=
  ⟨linkP_cel h, chain_lumped h.uack, hc, h.H_LATCH_OPEN, h.H_LATCH_HOLD, h.ic, h.ii, h.io⟩

/-! ## The protocol premise is needed (O4's run, as a `GenForkP` fork) -/

/-- O4's `tree_needs_persist` run is a `GenForkP` fork (bd_fork N = 5, every LUT obeying
H_LUT_SI and H_FB_FIRST) whose lumped field fails: without the protocol premise of
`fork_core` (here leaf 0 withdraws while its request never rose) the field is not derivable. -/
theorem fork_needs_protocol : ∃ (a : Chan) (os : List Chan), GenForkP a os ∧ ¬ ∀ u, FCel a os u := by
  let oc : Trace → Chan := fun l => ⟨fun _ => false, l, fun _ => 0⟩
  obtain ⟨h1, h2, h3, _⟩ := Formal.Net.CellBind.Gcd.tree_needs_persist
  refine ⟨⟨fun _ => false, Formal.Net.CellBind.Gcd.nR, fun _ => 0⟩,
    [Formal.Net.CellBind.Gcd.lA0, Formal.Net.CellBind.Gcd.lHi, Formal.Net.CellBind.Gcd.lHi,
      Formal.Net.CellBind.Gcd.lHi, Formal.Net.CellBind.Gcd.lHi].map oc, ⟨?_, ?_, ?_, rfl, ?_⟩, ?_⟩
  · exact ⟨Formal.Net.CellBind.Gcd.nM, h1, h2, h3⟩
  · intro o ho t h; obtain ⟨l, _, rfl⟩ := List.mem_map.mp ho; exact absurd rfl h
  · intro o ho t; obtain ⟨l, _, rfl⟩ := List.mem_map.mp ho; rfl
  · intro o ho; obtain ⟨l, _, rfl⟩ := List.mem_map.mp ho; rfl
  · intro H
    have := H 2 (by decide) (oc Formal.Net.CellBind.Gcd.lA0) (by simp)
    exact absurd this (by decide)

end Formal.Net.CellBind.Persist
