import Formal.Net.CellBindChain
import Formal.Net.CellBindNets
import Formal.Net.CapstoneNetDef

/-!
# Probe C-O4 (3/4): every Ops cell kind of gcd_hw from its generated netlist

For each operator kind `K` of the capstone network (`CapNet.K`), `GenCell ch sv k` states
the operator's GENERATED netlist under the per-gate SI model, plus the named hypotheses the
netlist cannot give; `cell_of_gen` derives the hand-written Ops gate model `Cell ch sv k`
from it. `CellBindGcd.lean` then replaces H_CELLS of the gcd_hw capstone by `GenCell`.

## The per-gate model

* **H_LUT_SI** (per LUT): the output moves only to the generated LUT function (`genF` of the
  yosys netlist, i.e. its INIT and pin map) of the previous tick's pin values. For a
  feedback LUT the feedback pin is its own routed trace `qp` (`LutFb`).
* **H_FB_FIRST** (per feedback LUT, B's C2): the feedback pin shows the output before the
  output moves again (`FbFirst`). `CNode F p o` = H_LUT_SI + H_FB_FIRST.
* **H_PIN_EQ** (convention, all non-feedback pins): a LUT pin reads its driving net's trace
  (the channel's trace IS the value at the reading pin). Route delays that matter are
  explicit nodes: delay-chain stages (`Stage.buf` may be a route), H_WIRE_DI.
* **H_CHAIN_SETTLED** (per side-tapped delay chain: compute / muxN / amerge request lines,
  bd_link's `uack`): `GenChain` (`CellBind.Settled`). Needed: `Chain.fastfall_hazard`.
* **H_REQ_PERSIST** (per plain buffer chain: bd_link `rdly`, bd_mux `udly`): only end-only
  persistence (`GenBufChain`, `CellBind.PersistEnd`), which the four-phase protocol gives.
* **H_LEAF_PERSIST** (`LeafPersist`): for a two-level C-tree (bd_fork N = 5, 6) and for a
  C-element / OR node in front of a delay chain (compute join, mux, muxN): a leaf moves
  only while it equals the lumped output. Needed: without it the lumped C-element field
  fails (`CellBindGcd.tree_needs_persist`).
* **H_WIRE_DI**: every netlist wire that the Ops model reads as a one-tick-delayed copy
  (fork `req_out`, join `ack_out`, mux `ctl_ack`, bd_snk `ack`) is a route of ≥ 1 tick. Needed:
  `CellBind.ident_wire_breaks`.

## Not derived from any generated cell (fields copied as named hypotheses)

Data (H_DATA_WIRE, H_DATA_COMB, H_LATCH_COMB = the link's `H_LATCH_OPEN/HOLD`), H_SEL_PIN
(the steer / mux select pin reads the decoded bus at the same tick), H_MUXN_OR (bdc_muxn3's
`|j` is yosys logic of an emitted unit, not a library cell), the arbiter's grant behaviour
(`H_ARB1`, `H_ARB2`, `H_ARB_EXCL`, `H_AMERGE_RTZ`, B's domain) and **H_R0_ISO** (bd_arbiter's
`R0 = ustate.O5` and the grants `ugrant.O5/O6` are separate LUTs computing `g1 ∨ g2` in
parallel; reading `R0` as `g1 ∨ g2` at the same tick is an isochrony assumption), and
H_RESET (initial values). The port order of a K operator's lists is taken as the netlist's
`ack_in[k]` / `req_in[k]` order (H_PORT_ORDER; it matters only for bd_fork N = 5, 6, where
the leaves are not symmetric).
-/

namespace Formal.Net.CellBind.Ops
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CellBind Formal.Net.CellBind.Chain
open Formal.Gen Formal.Gen.Cells Formal.Net.Ops.Gen Formal.Net.CapNet

/-! ## 1. Nodes and chains -/

/-- A feedback LUT node: H_LUT_SI with the feedback pin `qp`, and H_FB_FIRST. -/
def CNode {α : Type} (F : α → Bool → Bool) (p : Nat → α) (o : Trace) : Prop :=
  ∃ qp, LutFb F p qp o ∧ FbFirst qp o

theorem cnode_move {α : Type} {F G : α → Bool → Bool} {p : Nat → α} {o : Trace}
    (hg : ∀ a q, F a q = G a q) (h : CNode F p o) :
    ∀ t, o (t + 1) ≠ o t → o (t + 1) = G (p t) (o t) := by
  obtain ⟨qp, hL, hF⟩ := h
  intro t ht; rw [lutFb_si hL hF t ht, hg]

/-- H_LEAF_PERSIST. -/
def LeafPersist (ls : List Trace) (r : Trace) : Prop := ∀ l ∈ ls, ∀ t, l (t + 1) ≠ l t → l t = r t

/-- A delay-chain stage: a generated LUT1 buffer (also a route), or a generated LUT2 side
tap `s ∧ tap` (FASTFALL, gated) / `s ∨ tap` (FASTRISE), reading node `p` and tap `q`. -/
inductive Stage
  | buf (p : Nat)
  | andT (p q : Nat)
  | orT (p q : Nat)

def Stage.G : Stage → (Nat → Bool) → Bool
  | .buf p, f => genF bd_delay_N3 "chain.g[0].u" .O ["a"] [f p]
  | .andT p q, f => genF bd_delay_N3_FF "chain.g[1].u" .O ["chain.s[1]", "a"] [f p, f q]
  | .orT p q, f => genF bd_delay_N3_FR "chain.g[1].u" .O ["chain.s[1]", "a"] [f p, f q]

def Stage.Ok (n : Nat) : Stage → Prop
  | .buf p => p ≤ n
  | .andT p q => p ≤ n ∧ q ≤ n
  | .orT p q => p ≤ n ∧ q ≤ n

theorem stage_ok {n : Nat} : ∀ s : Stage, s.Ok n → MonoOn n s.G ∧ IdemOn n s.G
  | .buf p, hp => by
    refine ⟨fun f g h hf => ?_, fun f v h => ?_⟩
    · simp only [Stage.G, (sym_gate _).1] at hf ⊢; exact h p hp hf
    · simp only [Stage.G, (sym_gate _).1]; exact h p hp
  | .andT p q, ⟨hp, hq⟩ => by
    have e : ∀ f : Nat → Bool, Stage.G (.andT p q) f = stage2 (· && ·) p q f := by
      intro f; simp only [Stage.G, stage2, (ff_gate _ _).2.1]
    have := stage_mono hp hq (· && ·) and_mono (by decide)
    exact ⟨fun f g h hf => by rw [e] at hf ⊢; exact this.1 f g h hf,
           fun f v h => by rw [e]; exact this.2 f v h⟩
  | .orT p q, ⟨hp, hq⟩ => by
    have e : ∀ f : Nat → Bool, Stage.G (.orT p q) f = stage2 (· || ·) p q f := by
      intro f; simp only [Stage.G, stage2, (fr_gate _ _).1]
    have := stage_mono hp hq (· || ·) or_mono (by decide)
    exact ⟨fun f g h hf => by rw [e] at hf ⊢; exact this.1 f g h hf,
           fun f v h => by rw [e]; exact this.2 f v h⟩

/-- A side-tapped (or any) delay chain from `i` to `o`, with H_CHAIN_SETTLED. -/
def GenChain (i o : Trace) : Prop :=
  ∃ (n : Nat) (st : Nat → Stage) (x : Nat → Trace), 1 ≤ n ∧ x 0 = i ∧ x n = o ∧
    (∀ k, 1 ≤ k → k ≤ n → (st k).Ok n) ∧ NetSI n (fun k => (st k).G) x ∧
    Settled n x ∧ (∀ j, j ≤ n → x j 0 = x 0 0)

theorem chain_lumped {i o : Trace} (h : GenChain i o) : ∀ t, o (t + 1) ≠ o t → o (t + 1) = i t := by
  obtain ⟨n, st, x, hn, h0, hN, hok, hsi, hS, hI⟩ := h
  intro t ht
  rw [← hN] at ht ⊢; rw [← h0]
  exact mono_net (fun k h1 hk => stage_ok (st k) (hok k h1 hk)) hsi hS hI n hn (Nat.le_refl n) t ht

/-- A plain buffer chain (generated LUT1 stages or routes) from `i` to `o`, with only
end-only persistence (H_REQ_PERSIST). -/
def GenBufChain (i o : Trace) : Prop :=
  ∃ (n : Nat) (x : Nat → Trace), 1 ≤ n ∧ x 0 = i ∧ x n = o ∧
    NetSI n (fun k f => genF bd_delay_N3 "chain.g[0].u" .O ["a"] [f (k - 1)]) x ∧
    PersistEnd n x ∧ (∀ j, j ≤ n → x j 0 = x 0 0)

theorem bufchain_lumped {i o : Trace} (h : GenBufChain i o) : ∀ t, o (t + 1) ≠ o t → o (t + 1) = i t := by
  obtain ⟨n, x, hn, h0, hN, hsi, hP, hI⟩ := h
  have hsi' : NetSI n bufG x := by
    intro k h1 hk t hm; rw [hsi k h1 hk t hm]; simp only [bufG, (sym_gate _).1]
  intro t ht
  rw [← hN] at ht ⊢; rw [← h0]
  exact buf_chain hsi' hP hI t ht hn

/-! ## 2. Fork: bd_fork N = 2..6 -/

def cel4 (a b c d q : Bool) : Bool := if a = b ∧ b = c ∧ c = d then a else q

theorem cel4_move : ∀ a b c d q : Bool, cel4 a b c d q ≠ q →
    a = cel4 a b c d q ∧ b = cel4 a b c d q ∧ c = cel4 a b c d q ∧ d = cel4 a b c d q := by decide

def f2F (p : Bool × Bool) (q : Bool) : Bool :=
  genF bd_fork_N2 forkCell .O ["ack_in[0]", "ack_in[1]", "ack", "rst"] [p.1, p.2, q, false]
def f3F (p : Bool × Bool × Bool) (q : Bool) : Bool :=
  genF Nets.bd_fork_N3 "u.genblk1.genblk1.g3.u.u" .O ["ack_in[0]", "ack_in[1]", "ack_in[2]", "ack", "rst"]
    [p.1, p.2.1, p.2.2, q, false]
def f4F (p : Bool × Bool × Bool × Bool) (q : Bool) : Bool :=
  genF Nets.bd_fork_N4 "u.genblk1.genblk1.genblk1.g4.u.u" .O
    ["ack_in[0]", "ack_in[1]", "ack_in[2]", "ack_in[3]", "ack", "rst"] [p.1, p.2.1, p.2.2.1, p.2.2.2, q, false]

def chunk0 : String := "u.genblk1.genblk1.genblk1.gt.chunk[0].u.genblk1.genblk1.genblk1.g4.u.u"
def chunk1 : String := "u.genblk1.genblk1.genblk1.gt.chunk[1].u.genblk1.g2.u.u"
def utop : String := "u.genblk1.genblk1.genblk1.gt.utop.genblk1.g2.u.u"
def part0 : String := "u.genblk1.genblk1.genblk1.gt.part[0]"
def part1 : String := "u.genblk1.genblk1.genblk1.gt.part[1]"

def f5cF (p : Bool × Bool × Bool × Bool) (q : Bool) : Bool :=
  genF bd_fork_N5 chunk0 .O ["ack_in[0]", "ack_in[1]", "ack_in[2]", "ack_in[3]", part0, "rst"]
    [p.1, p.2.1, p.2.2.1, p.2.2.2, q, false]
def f5tF (p : Bool × Bool) (q : Bool) : Bool :=
  genF bd_fork_N5 utop .O [part0, "ack_in[4]", "ack", "rst"] [p.1, p.2, q, false]
def f6aF (p : Bool × Bool × Bool × Bool) (q : Bool) : Bool :=
  genF Nets.bd_fork_N6 chunk0 .O ["ack_in[0]", "ack_in[1]", "ack_in[2]", "ack_in[3]", part0, "rst"]
    [p.1, p.2.1, p.2.2.1, p.2.2.2, q, false]
def f6bF (p : Bool × Bool) (q : Bool) : Bool :=
  genF Nets.bd_fork_N6 chunk1 .O ["ack_in[4]", "ack_in[5]", part1, "rst"] [p.1, p.2, q, false]
def f6tF (p : Bool × Bool) (q : Bool) : Bool :=
  genF Nets.bd_fork_N6 utop .O [part0, part1, "ack", "rst"] [p.1, p.2, q, false]

theorem f2_gate : ∀ (p : Bool × Bool) q, f2F p q = cel2 p.1 p.2 q := by
  intro p q; exact fork2_gate p.1 p.2 q
theorem f3_gate : ∀ (p : Bool × Bool × Bool) q, f3F p q = cel3 p.1 p.2.1 p.2.2 q := by
  intro ⟨a, b, c⟩ q; revert a b c q; decide +kernel
theorem f4_gate : ∀ (p : Bool × Bool × Bool × Bool) q, f4F p q = cel4 p.1 p.2.1 p.2.2.1 p.2.2.2 q := by
  intro ⟨a, b, c, d⟩ q; revert a b c d q; decide +kernel
theorem f5c_gate : ∀ (p : Bool × Bool × Bool × Bool) q, f5cF p q = cel4 p.1 p.2.1 p.2.2.1 p.2.2.2 q := by
  intro ⟨a, b, c, d⟩ q; revert a b c d q; decide +kernel
theorem f5t_gate : ∀ (p : Bool × Bool) q, f5tF p q = cel2 p.1 p.2 q := by
  intro ⟨a, b⟩ q; revert a b q; decide +kernel
theorem f6a_gate : ∀ (p : Bool × Bool × Bool × Bool) q, f6aF p q = cel4 p.1 p.2.1 p.2.2.1 p.2.2.2 q := by
  intro ⟨a, b, c, d⟩ q; revert a b c d q; decide +kernel
theorem f6b_gate : ∀ (p : Bool × Bool) q, f6bF p q = cel2 p.1 p.2 q := by
  intro ⟨a, b⟩ q; revert a b q; decide +kernel
theorem f6t_gate : ∀ (p : Bool × Bool) q, f6tF p q = cel2 p.1 p.2 q := by
  intro ⟨a, b⟩ q; revert a b q; decide +kernel

/-- The acknowledge tree of `bd_fork` (`bd_ctree` of the branch acks) as generated, by
width: one LUT for N ≤ 4; for N = 5, 6 two levels with internal nodes `m`, which need
H_LEAF_PERSIST. -/
def ForkTree (r : Trace) : List Trace → Prop
  | [a0, a1] => CNode f2F (fun t => (a0 t, a1 t)) r
  | [a0, a1, a2] => CNode f3F (fun t => (a0 t, a1 t, a2 t)) r
  | [a0, a1, a2, a3] => CNode f4F (fun t => (a0 t, a1 t, a2 t, a3 t)) r
  | [a0, a1, a2, a3, a4] => ∃ m, CNode f5cF (fun t => (a0 t, a1 t, a2 t, a3 t)) m ∧
      CNode f5tF (fun t => (m t, a4 t)) r ∧ m 0 = r 0 ∧ LeafPersist [a0, a1, a2, a3] r
  | [a0, a1, a2, a3, a4, a5] => ∃ m1 m2, CNode f6aF (fun t => (a0 t, a1 t, a2 t, a3 t)) m1 ∧
      CNode f6bF (fun t => (a4 t, a5 t)) m2 ∧ CNode f6tF (fun t => (m1 t, m2 t)) r ∧
      m1 0 = r 0 ∧ m2 0 = r 0 ∧ LeafPersist [a0, a1, a2, a3, a4, a5] r
  | _ => False

theorem leaf_sub {ls ls' : List Trace} {r : Trace} (h : LeafPersist ls r) (hs : ∀ l ∈ ls', l ∈ ls) :
    LeafPersist ls' r := fun l hl => h l (hs l hl)

theorem tree_cel {r : Trace} : ∀ {ls : List Trace}, ForkTree r ls →
    ∀ t, r (t + 1) ≠ r t → ∀ l ∈ ls, l t = r (t + 1)
  | [a0, a1], h, t, ht, l, hl => by
    have e := cnode_move f2_gate h t ht
    have m := cel2_move _ _ _ (by rw [← e]; exact ht); rw [← e] at m
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl
    · exact m.1
    · exact m.2
  | [a0, a1, a2], h, t, ht, l, hl => by
    have e := cnode_move f3_gate h t ht
    have m := cel3_move _ _ _ _ (by rw [← e]; exact ht); rw [← e] at m
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl
    · exact m.1
    · exact m.2.1
    · exact m.2.2
  | [a0, a1, a2, a3], h, t, ht, l, hl => by
    have e := cnode_move f4_gate h t ht
    have m := cel4_move _ _ _ _ _ (by rw [← e]; exact ht); rw [← e] at m
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl
    · exact m.1
    · exact m.2.1
    · exact m.2.2.1
    · exact m.2.2.2
  | [a0, a1, a2, a3, a4], h, t, ht, l, hl => by
    obtain ⟨mm, hc, htop, h0, hL⟩ := h
    have hC : ∀ t, mm (t + 1) ≠ mm t → ∀ l ∈ [a0, a1, a2, a3], l t = mm (t + 1) := by
      intro t ht l hl
      have e := cnode_move f5c_gate hc t ht
      have m := cel4_move _ _ _ _ _ (by rw [← e]; exact ht); rw [← e] at m
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl
      · exact m.1
      · exact m.2.1
      · exact m.2.2.1
      · exact m.2.2.2
    have hT : ∀ t, r (t + 1) ≠ r t → mm t = r (t + 1) ∧ a4 t = r (t + 1) := by
      intro t ht
      have e := cnode_move f5t_gate htop t ht
      have m := cel2_move _ _ _ (by rw [← e]; exact ht); rw [← e] at m; exact m
    have hR : ∀ t, r (t + 1) ≠ r t → r (t + 1) = mm t := fun t ht => (hT t ht).1.symm
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl
    · exact cel_lumped hC hR hL h0 t ht l (by simp)
    · exact cel_lumped hC hR hL h0 t ht l (by simp)
    · exact cel_lumped hC hR hL h0 t ht l (by simp)
    · exact cel_lumped hC hR hL h0 t ht l (by simp)
    · exact (hT t ht).2
  | [a0, a1, a2, a3, a4, a5], h, t, ht, l, hl => by
    obtain ⟨m1, m2, hc1, hc2, htop, h01, h02, hL⟩ := h
    have hC1 : ∀ t, m1 (t + 1) ≠ m1 t → ∀ l ∈ [a0, a1, a2, a3], l t = m1 (t + 1) := by
      intro t ht l hl
      have e := cnode_move f6a_gate hc1 t ht
      have m := cel4_move _ _ _ _ _ (by rw [← e]; exact ht); rw [← e] at m
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl | rfl | rfl
      · exact m.1
      · exact m.2.1
      · exact m.2.2.1
      · exact m.2.2.2
    have hC2 : ∀ t, m2 (t + 1) ≠ m2 t → ∀ l ∈ [a4, a5], l t = m2 (t + 1) := by
      intro t ht l hl
      have e := cnode_move f6b_gate hc2 t ht
      have m := cel2_move _ _ _ (by rw [← e]; exact ht); rw [← e] at m
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact m.1
      · exact m.2
    have hT : ∀ t, r (t + 1) ≠ r t → m1 t = r (t + 1) ∧ m2 t = r (t + 1) := by
      intro t ht
      have e := cnode_move f6t_gate htop t ht
      have m := cel2_move _ _ _ (by rw [← e]; exact ht); rw [← e] at m; exact m
    have hR1 : ∀ t, r (t + 1) ≠ r t → r (t + 1) = m1 t := fun t ht => (hT t ht).1.symm
    have hR2 : ∀ t, r (t + 1) ≠ r t → r (t + 1) = m2 t := fun t ht => (hT t ht).2.symm
    have hL1 : LeafPersist [a0, a1, a2, a3] r := leaf_sub hL (by simp)
    have hL2 : LeafPersist [a4, a5] r := leaf_sub hL (by simp)
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
    rcases hl with rfl | rfl | rfl | rfl | rfl | rfl
    · exact cel_lumped hC1 hR1 hL1 h01 t ht l (by simp)
    · exact cel_lumped hC1 hR1 hL1 h01 t ht l (by simp)
    · exact cel_lumped hC1 hR1 hL1 h01 t ht l (by simp)
    · exact cel_lumped hC1 hR1 hL1 h01 t ht l (by simp)
    · exact cel_lumped hC2 hR2 hL2 h02 t ht l (by simp)
    · exact cel_lumped hC2 hR2 hL2 h02 t ht l (by simp)
  | [], h, _, _, _, _ => h.elim
  | [_], h, _, _, _, _ => h.elim
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h, _, _, _, _ => h.elim

theorem tree_ne {r : Trace} : ∀ {ls : List Trace}, ForkTree r ls → ls ≠ []
  | [], h => h.elim
  | _ :: _, _ => List.cons_ne_nil _ _

/-- The fork, as generated. -/
structure GenFork (a : Chan) (os : List Chan) : Prop where
  tree : ForkTree a.ack (os.map Chan.ack)
  H_WIRE_DI : ∀ o ∈ os, ∀ t, o.req (t + 1) ≠ o.req t → o.req (t + 1) = a.req t
  H_DATA_WIRE : ∀ o ∈ os, ∀ t, o.dat t = a.dat t
  initA : a.ack 0 = false
  initO : ∀ o ∈ os, o.req 0 = false

theorem fork_of_gen {a : Chan} {os : List Chan} (h : GenFork a os) : Fork.Fork a os where
  ne := by
    intro he; subst he; exact tree_ne h.tree rfl
  wire := h.H_WIRE_DI
  cel := fun t ht o ho => tree_cel h.tree t ht o.ack (List.mem_map_of_mem ho)
  dat := h.H_DATA_WIRE
  initA := h.initA
  initO := h.initO

/-! ## 3. Joins: `bjoin` (bd_join N = 2) and `join` (compute unit: bd_join, `uor`, request delay) -/

def j2F (p : Bool × Bool) (q : Bool) : Bool :=
  genF bd_join_N2 forkCell .O ["req_in[0]", "req_in[1]", "req", "rst"] [p.1, p.2, q, false]

theorem j2_gate : ∀ (p : Bool × Bool) q, j2F p q = cel2 p.1 p.2 q := by
  intro p q; exact join2_gate p.1 p.2 q

/-- A branch's (cond, data) join: one bd_join N = 2, output = the joined request. -/
structure GenBJoin (g : List Nat → Nat) (ins : List Chan) (o : Chan) : Prop where
  two : ∃ i0 i1, ins = [i0, i1] ∧ CNode j2F (fun t => (i0.req t, i1.req t)) o.req
  H_WIRE_DI : ∀ i ∈ ins, ∀ t, i.ack (t + 1) ≠ i.ack t → i.ack (t + 1) = o.ack t
  H_DATA_COMB : ∀ t, o.dat t = g (ins.map (fun i => i.dat t))
  initO : o.req 0 = false
  initI : ∀ i ∈ ins, i.ack 0 = false

theorem bjoin_of_gen {g : List Nat → Nat} {ins : List Chan} {o : Chan} (h : GenBJoin g ins o) :
    Join.Join g ins o := by
  obtain ⟨i0, i1, rfl, hc⟩ := h.two
  refine ⟨by simp, ?_, h.H_WIRE_DI, h.H_DATA_COMB, h.initO, h.initI⟩
  intro t ht i hi
  have e := cnode_move j2_gate hc t ht
  have m := cel2_move _ _ _ (by rw [← e]; exact ht); rw [← e] at m
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
  rcases hi with rfl | rfl
  · exact m.1
  · exact m.2

/-- The joined request of a compute unit's bd_join: the input itself for N = 1 (bd_ctree
N = 1 is a wire), the generated C-element node for N = 2. -/
def JoinNode (m : Trace) : List Chan → Prop
  | [i0] => m = i0.req
  | [i0, i1] => CNode j2F (fun t => (i0.req t, i1.req t)) m
  | _ => False

/-- A compute unit (`K.join`): bd_join → `uor` → request delay (any generated stages;
H_CHAIN_SETTLED) → `z_req`, plus H_LEAF_PERSIST of the input requests for N = 2. -/
structure GenJoin (g : List Nat → Nat) (ins : List Chan) (o : Chan) : Prop where
  node : ∃ m, JoinNode m ins ∧ GenChain m o.req ∧ m 0 = o.req 0
  H_LEAF_PERSIST : LeafPersist (ins.map Chan.req) o.req
  H_WIRE_DI : ∀ i ∈ ins, ∀ t, i.ack (t + 1) ≠ i.ack t → i.ack (t + 1) = o.ack t
  H_DATA_COMB : ∀ t, o.dat t = g (ins.map (fun i => i.dat t))
  initO : o.req 0 = false
  initI : ∀ i ∈ ins, i.ack 0 = false

theorem join_of_gen {g : List Nat → Nat} {ins : List Chan} {o : Chan} (h : GenJoin g ins o) :
    Join.Join g ins o := by
  obtain ⟨m, hJ, hch, h0⟩ := h.node
  have hR := chain_lumped hch
  match ins, hJ, h with
  | [i0], hJ, h =>
    refine ⟨by simp, ?_, h.H_WIRE_DI, h.H_DATA_COMB, h.initO, h.initI⟩
    intro t ht i hi
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hi
    subst hi; rw [hR t ht, hJ]
  | [i0, i1], hJ, h =>
    refine ⟨by simp, ?_, h.H_WIRE_DI, h.H_DATA_COMB, h.initO, h.initI⟩
    have hC : ∀ t, m (t + 1) ≠ m t → ∀ l ∈ [i0.req, i1.req], l t = m (t + 1) := by
      intro t ht l hl
      have e := cnode_move j2_gate hJ t ht
      have mv := cel2_move _ _ _ (by rw [← e]; exact ht); rw [← e] at mv
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl
      rcases hl with rfl | rfl
      · exact mv.1
      · exact mv.2
    intro t ht i hi
    have hL : LeafPersist [i0.req, i1.req] o.req := h.H_LEAF_PERSIST
    have hmem : i.req ∈ [i0.req, i1.req] := by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hi ⊢
      rcases hi with rfl | rfl
      · exact Or.inl rfl
      · exact Or.inr rfl
    exact cel_lumped hC hR hL h0 t ht i.req hmem

/-! ## 4. Steer (bd_steer) -/

structure GenSteer (sel : Nat → Bool) (f : Nat → Nat) (j : Chan) (out : Bool → Chan) : Prop where
  /-- H_LUT_SI on the generated LUT6_2, with H_SEL_PIN (the `s` pin reads `sel (j.dat t)`). -/
  lut : ∀ b, LutSI (steerF b) (fun t => (j.req t, sel (j.dat t))) (out b).req
  uack : LutSI (fun p : Bool × Bool => genF bd_steer "uack" .O ["ack0", "ack1"] [p.1, p.2])
    (fun t => ((out false).ack t, (out true).ack t)) j.ack
  H_DATA_WIRE : ∀ b t, (out b).dat t = f (j.dat t)
  initJ : j.ack 0 = false
  initO : ∀ b, (out b).req 0 = false

theorem steer_of_gen {sel : Nat → Bool} {f : Nat → Nat} {j : Chan} {out : Bool → Chan}
    (h : GenSteer sel f j out) : Steer.Steer sel f j out :=
  ⟨(steer_bound h.lut h.uack).1, (steer_bound h.lut h.uack).2, h.H_DATA_WIRE, h.initJ, h.initO⟩

/-! ## 5. Mux (bd_mux W) -/

theorem uor_gate : ∀ a b : Bool, genF bd_mux_W2 "uor" .O ["j0", "j1"] [a, b] = (a || b) := by decide +kernel

structure GenMux (sel : Nat → Bool) (x y c z : Chan) (j0 j1 : Trace) : Prop where
  cj0 : CNode muxJ0F (fun t => (x.req t, c.req t, sel (c.dat t))) j0
  cj1 : CNode muxJ1F (fun t => (y.req t, c.req t, sel (c.dat t))) j1
  cxa : CNode muxXaF (fun t => (j0 t, z.ack t)) x.ack
  cya : CNode muxYaF (fun t => (j1 t, z.ack t)) y.ack
  /-- `uor` (generated LUT2) then `udly` (plain bd_delay: H_REQ_PERSIST), H_LEAF_PERSIST. -/
  zr : ∃ e, LutSI (fun p : Bool × Bool => genF bd_mux_W2 "uor" .O ["j0", "j1"] [p.1, p.2])
      (fun t => (j0 t, j1 t)) e ∧ GenBufChain e z.req ∧ e 0 = z.req 0 ∧ LeafPersist [j0, j1] z.req
  H_WIRE_DI : ∀ t, c.ack (t + 1) ≠ c.ack t → c.ack (t + 1) = z.ack t
  H_DATA_COMB : ∀ t, z.dat t = if sel (c.dat t) then y.dat t else x.dat t
  i0 : j0 0 = false
  i1 : j1 0 = false
  iz : z.req 0 = false
  ix : x.ack 0 = false
  iy : y.ack 0 = false
  ic : c.ack 0 = false

theorem mux_of_gen {sel : Nat → Bool} {x y c z : Chan} {j0 j1 : Trace} (h : GenMux sel x y c z j0 j1) :
    Mux.Mux sel x y c z j0 j1 := by
  obtain ⟨q0, h0, f0⟩ := h.cj0
  obtain ⟨q1, h1, f1⟩ := h.cj1
  obtain ⟨q2, h2, f2⟩ := h.cxa
  obtain ⟨q3, h3, f3⟩ := h.cya
  have B := mux_bound h0 f0 h1 f1 h2 f2 h3 f3
  obtain ⟨e, he, hch, he0, hL⟩ := h.zr
  have hE : ∀ t, e (t + 1) ≠ e t → e (t + 1) = [j0, j1].any (fun l => l t) := by
    intro t ht; rw [he t ht]
    show genF bd_mux_W2 "uor" .O ["j0", "j1"] [j0 t, j1 t] = _
    rw [uor_gate]; simp
  have hzr : ∀ t, z.req (t + 1) ≠ z.req t → z.req (t + 1) = (j0 t || j1 t) := by
    intro t ht
    rw [or_lumped hE (bufchain_lumped hch) hL he0 t ht]; simp
  exact ⟨B.1, B.2.1, hzr, B.2.2.1, B.2.2.2, h.H_WIRE_DI, h.H_DATA_COMB, h.i0, h.i1, h.iz, h.ix, h.iy, h.ic⟩

/-! ## 6. MuxN (bdc_muxn3: `bd_c2` joins and acks, `|j`, `uor`, request delay) -/

structure GenMuxN (sel : Nat → Nat) (xs : Nat → Chan) (c z : Chan) (j : Nat → Trace) : Prop where
  /-- H_SEL_PIN: the `b` pin reads the decode `ctl_req ∧ (s == k)`. -/
  cj : ∀ k, k < 3 → CNode c2F (fun t => ((xs k).req t, c.req t && (sel (c.dat t) == k))) (j k)
  xa : ∀ k, k < 3 → CNode c2F (fun t => (j k t, z.ack t)) (xs k).ack
  /-- H_MUXN_OR: the `|j` node moves only to the OR of the joins (yosys logic of the emitted
  unit, not a generated library cell); then the request delay (H_CHAIN_SETTLED). -/
  zr : ∃ e, (∀ t, e (t + 1) ≠ e t → e (t + 1) = [j 0, j 1, j 2].any (fun l => l t)) ∧
      GenChain e z.req ∧ e 0 = z.req 0 ∧ LeafPersist [j 0, j 1, j 2] z.req
  H_WIRE_DI : ∀ t, c.ack (t + 1) ≠ c.ack t → c.ack (t + 1) = z.ack t
  H_DATA_COMB : ∀ t, sel (c.dat t) < 3 → z.dat t = (xs (sel (c.dat t))).dat t
  ij : ∀ k, k < 3 → j k 0 = false
  iz : z.req 0 = false
  ix : ∀ k, k < 3 → (xs k).ack 0 = false
  ic : c.ack 0 = false

theorem muxn_of_gen {sel : Nat → Nat} {xs : Nat → Chan} {c z : Chan} {j : Nat → Trace}
    (h : GenMuxN sel xs c z j) : MuxN.MuxN sel xs c z j := by
  obtain ⟨e, hE, hch, he0, hL⟩ := h.zr
  have hg : ∀ (p : Bool × Bool) (q : Bool), c2F p q = cel2 p.1 p.2 q := fun p q => c2_gate p.1 p.2 q
  refine ⟨fun k hk t ht => ?_, fun t ht => ?_, fun k hk t ht => ?_, h.H_WIRE_DI, h.H_DATA_COMB,
    h.ij, h.iz, h.ix, h.ic⟩
  · have e1 : j k (t + 1) = cel2 ((xs k).req t) (c.req t && (sel (c.dat t) == k)) (j k t) :=
      cnode_move hg (h.cj k hk) t ht
    have m := cel2_move ((xs k).req t) (c.req t && (sel (c.dat t) == k)) (j k t) (by rw [← e1]; exact ht)
    rw [← e1] at m; exact m
  · rw [or_lumped hE (chain_lumped hch) hL he0 t ht]
    simp only [List.any_cons, List.any_nil, Bool.or_false, Bool.or_assoc]
  · have e1 : (xs k).ack (t + 1) = cel2 (j k t) (z.ack t) ((xs k).ack t) :=
      cnode_move hg (h.xa k hk) t ht
    have m := cel2_move (j k t) (z.ack t) ((xs k).ack t) (by rw [← e1]; exact ht)
    rw [← e1] at m; exact m

/-! ## 7. AMerge (bd_arbiter stage): acknowledges bound, grants not -/

structure GenAMerge (x y z : Chan) (g1 g2 : Trace) : Prop where
  ca1 : CNode arbA1F (fun t => (g1 t, z.ack t)) x.ack
  ca2 : CNode arbA2F (fun t => (g2 t, z.ack t)) y.ack
  /-- `R0` → `uor` → request delay (H_CHAIN_SETTLED), and H_R0_ISO at the moments `z_req`
  moves (`R0` read as the OR of the grant nodes). -/
  zr : ∃ r0, GenChain r0 z.req ∧ ∀ t, z.req (t + 1) ≠ z.req t → r0 t = (g1 t || g2 t)
  H_ARB1 : ∀ t, g1 (t + 1) ≠ g1 t → g1 (t + 1) = x.req t ∧ (g1 (t + 1) = true → g2 t = false ∧ z.ack t = false)
  H_ARB2 : ∀ t, g2 (t + 1) ≠ g2 t → g2 (t + 1) = y.req t ∧ (g2 (t + 1) = true → g1 t = false ∧ z.ack t = false)
  H_ARB_EXCL : ∀ t, (g1 t && g2 t) = false
  H_AMERGE_RTZ : ∀ t, z.req t = false → z.req (t + 1) = true → x.ack t = false ∧ y.ack t = false
  H_DATA_COMB : ∀ t, z.dat t = 2 * (if (g2 t || y.ack t) then y.dat t else x.dat t) + Mux.b2n (g2 t || y.ack t)
  i1 : g1 0 = false
  i2 : g2 0 = false
  iz : z.req 0 = false
  ix : x.ack 0 = false
  iy : y.ack 0 = false

theorem amerge_of_gen {x y z : Chan} {g1 g2 : Trace} (h : GenAMerge x y z g1 g2) : CM.AMerge x y z g1 g2 := by
  obtain ⟨q1, h1, f1⟩ := h.ca1
  obtain ⟨q2, h2, f2⟩ := h.ca2
  have B := amerge_ack_bound h1 f1 h2 f2
  obtain ⟨r0, hch, hiso⟩ := h.zr
  have hzr : ∀ t, z.req (t + 1) ≠ z.req t → z.req (t + 1) = (g1 t || g2 t) := by
    intro t ht; rw [chain_lumped hch t ht, hiso t ht]
  exact ⟨h.H_ARB1, h.H_ARB2, h.H_ARB_EXCL, hzr, h.H_AMERGE_RTZ, B.1, B.2, h.H_DATA_COMB,
    h.i1, h.i2, h.iz, h.ix, h.iy⟩

/-! ## 8. Link (bd_link: controller LUT, `rdly`, `uack`), source, sink -/

structure GenLink (i o : Chan) (c : Trace) : Prop where
  ctl : CNode linkF (fun t => (i.req t, o.ack t)) c
  /-- `rdly` (plain bd_delay; with `DELAY = 0` the route alone): H_REQ_PERSIST. -/
  rdly : GenBufChain c o.req
  /-- `uack` (bd_delay FASTRISE, `DACK` stages, plus the route): H_CHAIN_SETTLED. -/
  uack : GenChain c i.ack
  H_LATCH_OPEN : ∀ t, c t = true → o.dat t = i.dat t
  H_LATCH_HOLD : ∀ t, c (t + 1) = false → o.dat (t + 1) = o.dat t
  ic : c 0 = false
  ii : i.ack 0 = false
  io : o.req 0 = false

theorem link_of_gen' {i o : Chan} {c : Trace} (h : GenLink i o c) : Link.Link i o c := by
  obtain ⟨qp, hL, hF⟩ := h.ctl
  exact link_of_gen hL hF (chain_lumped h.uack) (bufchain_lumped h.rdly) h.H_LATCH_OPEN h.H_LATCH_HOLD
    h.ic h.ii h.io

structure GenSrc (z : Chan) (v : Nat) : Prop where
  lut : LutSI (fun a => genF bd_src_W2 "u" .O ["ack"] [a]) z.ack z.req
  H_DATA_CONST : ∀ t, z.dat t = v
  iz : z.req 0 = false

theorem src_of_gen' {z : Chan} {v : Nat} (h : GenSrc z v) : Capstone.Src z v :=
  src_of_gen h.lut h.H_DATA_CONST h.iz

/-- bd_snk has no cell (`snk_wire`): its `ack` is the `req` net, so the only content is
the route (H_WIRE_DI). -/
structure GenSink (c : Chan) : Prop where
  H_WIRE_DI : ∀ t, c.ack (t + 1) ≠ c.ack t → c.ack (t + 1) = c.req t
  init : c.ack 0 = false

theorem sink_of_gen {c : Chan} (h : GenSink c) : Ops.Gcd.Sink c := ⟨h.H_WIRE_DI, h.init⟩

/-! ## 9. Every operator kind -/

variable {n : Nat}

/-- **The generated-netlist hypothesis of an operator** (replaces `Cell`). -/
def GenCell (ch : Fin n → Chan) (sv : Nat → Nat) : K n → Prop
  | .forkG i os => GenFork (ch i) (os.map ch)
  | .forkH i os _ _ _ _ => GenFork (ch i) ((os.map Prod.fst).map ch)
  | .join ins o e js _ => GenJoin (jg e js) (ins.map ch) (ch o)
  | .bjoin ins o ec ed => GenBJoin (bg ec ed) (ins.map ch) (ch o)
  | .steerC j t f => GenSteer sel2 (fun _ => 0) (ch j) (fun b => ch (bif b then t else f))
  | .steerD j t f fd _ =>
      GenSteer sel2 (fun v => fd.eval [v / 2]) (ch j) (fun b => ch (bif b then t else f))
  | .mux c x y z _ => ∃ j0 j1, GenMux sel2 (ch x) (ch y) (ch c) (ch z) j0 j1
  | .muxn c x0 x1 x2 z _ => ∃ j, GenMuxN selD (fun k => ch (cx3 x0 x1 x2 k)) (ch c) (ch z) j
  | .amerge x y z _ => ∃ g1 g2, GenAMerge (ch x) (ch y) (ch z) g1 g2
  | .link i o => ∃ c, GenLink (ch i) (ch o) c
  | .src z which _ => GenSrc (ch z) (sv which)
  | .sink i => GenSink (ch i)

/-- **H_CELLS from the generated netlists.** -/
theorem cell_of_gen (ch : Fin n → Chan) (sv : Nat → Nat) : ∀ k : K n, GenCell ch sv k → Cell ch sv k
  | .forkG _ _, h => fork_of_gen h
  | .forkH _ _ _ _ _ _, h => fork_of_gen h
  | .join _ _ _ _ _, h => join_of_gen h
  | .bjoin _ _ _ _, h => bjoin_of_gen h
  | .steerC _ _ _, h => steer_of_gen h
  | .steerD _ _ _ _ _, h => steer_of_gen h
  | .mux _ _ _ _ _, h => by obtain ⟨j0, j1, M⟩ := h; exact ⟨j0, j1, mux_of_gen M⟩
  | .muxn _ _ _ _ _ _, h => by obtain ⟨j, M⟩ := h; exact ⟨j, muxn_of_gen M⟩
  | .amerge _ _ _ _, h => by obtain ⟨g1, g2, M⟩ := h; exact ⟨g1, g2, amerge_of_gen M⟩
  | .link _ _, h => by obtain ⟨c, L⟩ := h; exact ⟨c, link_of_gen' L⟩
  | .src _ _ _, h => src_of_gen' h
  | .sink _, h => sink_of_gen h

end Formal.Net.CellBind.Ops
