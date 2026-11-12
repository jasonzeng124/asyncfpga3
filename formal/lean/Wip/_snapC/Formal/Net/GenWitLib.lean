import Formal.Net.CapstoneWitnessLib
import Formal.Net.CellBindPersistK

/-!
# Probe C-witgen (1/4): an event-list checker for the GENERATED-netlist hypothesis `GenCell`

C-8t's `kChk` checks the lumped Ops gate models (`Cell`) of an event-list run. O4's
`GenCell` (`CellBindOps`) asks more: every operator's generated netlist, node by node --
bd_ctree internal nodes (fork N = 5, 6), the compute unit's bd_join node and its `uor` +
`bd_delay_gated` chain (H_CHAIN_SETTLED), bd_mux's `uor` node and plain `udly` chain
(end-only persistence), bdc_muxn3's `|j` node and chain, the arbiter's `R0` and chain
(H_R0_ISO), bd_link's `rdly` buffer chain and FASTRISE `uack` chain (H_CHAIN_SETTLED),
H_LEAF_PERSIST, and every LUT as H_LUT_SI + H_FB_FIRST on its yosys INIT (`genF`).

* `OX`: per operator, the toggle lists of its internal nodes (`m`: tree / join / `uor` /
  `|j` / `R0` node; `ca`: the nodes strictly inside the side-tapped chain, with its stage
  list `sa`; `cb`: the nodes strictly inside the plain buffer chain).
* `chainChk` / `chain_sound`: a chain with the given stages (generated LUT1 / LUT2 AND / LUT2
  OR, `Stage`) satisfies `GenChain`, H_CHAIN_SETTLED included. `bufChk` / `buf_sound`:
  `GenBufChain`. `leafChk` / `leaf_sound`: H_LEAF_PERSIST.
* `kChkG x sv k = kChk sv k && xChk x k`; **`kChkG_sound`**: it implies `GenCell`. The
  lumped part supplies the fields that `GenCell` shares with `Cell` (wires, data, latch,
  arbiter, reset); every C-element / LUT node field (`CNode`, `LutSI` on `genF`) is derived
  from the lumped field through the generated gate lemmas (a unit-time C-element whose inputs
  all show the new value computes it); the internal nodes are checked by `xChk`.
* `genK_of_gen`: O4's `GenCell` implies O4b's `GenCellK` (hence `GenCellKP` by `genP_of`).
-/

namespace Formal.Net.CellBind.GenWit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Wit
open Formal.Net.CellBind Formal.Net.CellBind.Ops Formal.Net.CellBind.Chain Formal.Gen Formal.Gen.Cells Formal.Net.Ops.Gen

/-! ## Internal-node data -/

structure OX where
  m : List (List Nat)
  sa : List Stage
  ca : List (List Nat)
  cb : List (List Nat)

def OX.mm (x : OX) (k : Nat) : List Nat := x.m.getD k []

def ox0 : OX := ⟨[], [], [], []⟩

/-! ## Stages -/

def sG : Stage → (Nat → Bool) → Bool
  | .buf p, f => f p
  | .andT p q, f => f p && f q
  | .orT p q, f => f p || f q

theorem sG_eq : ∀ (s : Stage) (f : Nat → Bool), sG s f = s.G f
  | .buf p, f => by simp only [sG, Stage.G, (sym_gate _).1]
  | .andT p q, f => by simp only [sG, Stage.G, (ff_gate _ _).2.1]
  | .orT p q, f => by simp only [sG, Stage.G, (fr_gate _ _).1]

def sOk (n : Nat) : Stage → Bool
  | .buf p => decide (p ≤ n)
  | .andT p q => decide (p ≤ n) && decide (q ≤ n)
  | .orT p q => decide (p ≤ n) && decide (q ≤ n)

theorem sOk_ok {n : Nat} : ∀ s : Stage, sOk n s = true → s.Ok n
  | .buf p, h => by simpa [sOk, Stage.Ok] using h
  | .andT p q, h => by simpa [sOk, Stage.Ok] using h
  | .orT p q, h => by simpa [sOk, Stage.Ok] using h

/-! ## Chains -/

/-- Toggle list of chain node `k` (0: input, 1..n-1: internal, n: output). -/
def cL (iL oL : List Nat) (ns : List (List Nat)) (n k : Nat) : List Nat :=
  if k = 0 then iL else if k < n then ns.getD (k - 1) [] else oL

theorem cL_zero (iL oL : List Nat) (ns : List (List Nat)) (n : Nat) : cL iL oL ns n 0 = iL := by
  simp [cL]

theorem cL_n (iL oL : List Nat) (ns : List (List Nat)) {n : Nat} (h : 1 ≤ n) : cL iL oL ns n n = oL := by
  have h0 : n ≠ 0 := by omega
  simp [cL, h0]

def chainChk (iL oL : List Nat) (sa : List Stage) (ns : List (List Nat)) : Bool :=
  decide (1 ≤ sa.length) && sa.all (sOk sa.length) &&
  (List.range sa.length).all (fun k => (cL iL oL ns sa.length (k + 1)).all fun e =>
    bv (cL iL oL ns sa.length (k + 1)) (e + 1) ==
      sG (sa.getD k (.buf 0)) (fun j => bv (cL iL oL ns sa.length j) e)) &&
  iL.all (fun e => (List.range (sa.length + 1)).all fun j => bv (cL iL oL ns sa.length j) e == bv iL e)

theorem chain_sound {iL oL : List Nat} {sa : List Stage} {ns : List (List Nat)}
    (h : chainChk iL oL sa ns = true) : GenChain (bv iL) (bv oL) := by
  simp only [chainChk, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, hok⟩, hsi⟩, hS⟩ := h
  refine ⟨sa.length, fun k => sa.getD (k - 1) (.buf 0), fun k => bv (cL iL oL ns sa.length k), h1,
    by simp only [cL_zero], by simp only [cL_n _ _ _ h1], ?_, ?_, ?_, ?_⟩
  · intro k hk1 hkn
    apply sOk_ok
    apply List.all_eq_true.mp hok
    show sa.getD (k - 1) _ ∈ sa
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    exact List.getElem_mem _
  · intro k hk1 hkn t hmv
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk : k' ∈ List.range sa.length := List.mem_range.2 (by omega)
    have := step_of (List.all_eq_true.mp hsi k' hk) hmv
    simp only [beq_iff_eq] at this
    simp only [Nat.add_sub_cancel]
    rw [this, sG_eq]
  · intro t hmv j hj
    simp only [cL_zero] at hmv ⊢
    have := List.all_eq_true.mp (step_of hS hmv) j (List.mem_range.2 (by omega))
    simpa only [beq_iff_eq] using this
  · intro j _; simp only [bv_zero]

def bufChk (iL oL : List Nat) (ns : List (List Nat)) : Bool :=
  (List.range (ns.length + 1)).all (fun k => (cL iL oL ns (ns.length + 1) (k + 1)).all fun e =>
    bv (cL iL oL ns (ns.length + 1) (k + 1)) (e + 1) == bv (cL iL oL ns (ns.length + 1) k) e) &&
  iL.all (fun e => bv oL e == bv iL e)

theorem buf_sound {iL oL : List Nat} {ns : List (List Nat)} (h : bufChk iL oL ns = true) :
    GenBufChain (bv iL) (bv oL) := by
  simp only [bufChk, Bool.and_eq_true] at h
  obtain ⟨hsi, hP⟩ := h
  refine ⟨ns.length + 1, fun k => bv (cL iL oL ns (ns.length + 1) k), by omega,
    by simp only [cL_zero], by simp only [cL_n _ _ _ (Nat.le_add_left 1 _)], ?_, ?_, ?_⟩
  · intro k hk1 hkn t hmv
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    have hk : k' ∈ List.range (ns.length + 1) := List.mem_range.2 (by omega)
    have := step_of (List.all_eq_true.mp hsi k' hk) hmv
    simp only [beq_iff_eq] at this
    simp only [(sym_gate _).1, Nat.add_sub_cancel]
    exact this
  · intro t hmv
    simp only [cL_zero, cL_n _ _ _ (Nat.le_add_left 1 _)] at hmv ⊢
    simpa only [beq_iff_eq] using step_of hP hmv
  · intro j _; simp only [bv_zero]

def leafChk (ls : List (List Nat)) (rL : List Nat) : Bool :=
  ls.all fun L => L.all fun e => bv L e == bv rL e

theorem leaf_sound {ls : List (List Nat)} {rL : List Nat} (h : leafChk ls rL = true) :
    LeafPersist (ls.map bv) (bv rL) := by
  intro l hl t hmv
  obtain ⟨L, hL, rfl⟩ := List.mem_map.1 hl
  simpa only [beq_iff_eq] using step_of (List.all_eq_true.mp h L hL) hmv

/-! ## Nodes -/

theorem cnode_mk {α : Type} {F : α → Bool → Bool} {p : Nat → α} {o : Trace}
    (h : ∀ t, o (t + 1) ≠ o t → o (t + 1) = F (p t) (o t)) : CNode F p o :=
  ⟨o, h, fun _ _ => rfl⟩

theorem cnode_of {α : Type} {F G : α → Bool → Bool} {p : Nat → α} {L : List Nat}
    (hg : ∀ a q, F a q = G a q) (h : L.all (fun e => bv L (e + 1) == G (p e) (bv L e)) = true) :
    CNode F p (bv L) :=
  cnode_mk fun t ht => by rw [hg]; simpa only [beq_iff_eq] using step_of h ht

theorem cel2_eq {a b v : Bool} (q : Bool) (ha : a = v) (hb : b = v) : cel2 a b q = v := by
  subst ha hb; simp [cel2]

theorem cel3_eq {a b c v : Bool} (q : Bool) (ha : a = v) (hb : b = v) (hc : c = v) : cel3 a b c q = v := by
  subst ha hb hc; simp [cel3]

theorem cel4_eq {a b c d v : Bool} (q : Bool) (ha : a = v) (hb : b = v) (hc : c = v) (hd : d = v) :
    cel4 a b c d q = v := by
  subst ha hb hc hd; simp [cel4]

/-! ## Per-kind extra checks -/

variable {n : Nat} (cd : Fin n → CD)

def tree5Chk (r a0 a1 a2 a3 a4 : Fin n) (x : OX) : Bool :=
  (x.mm 0).all (fun e => bv (x.mm 0) (e + 1) ==
    cel4 (akv cd a0 e) (akv cd a1 e) (akv cd a2 e) (akv cd a3 e) (bv (x.mm 0) e)) &&
  (cd r).ak.all (fun e => akv cd r (e + 1) == cel2 (bv (x.mm 0) e) (akv cd a4 e) (akv cd r e)) &&
  leafChk [(cd a0).ak, (cd a1).ak, (cd a2).ak, (cd a3).ak] (cd r).ak

def tree6Chk (r a0 a1 a2 a3 a4 a5 : Fin n) (x : OX) : Bool :=
  (x.mm 0).all (fun e => bv (x.mm 0) (e + 1) ==
    cel4 (akv cd a0 e) (akv cd a1 e) (akv cd a2 e) (akv cd a3 e) (bv (x.mm 0) e)) &&
  (x.mm 1).all (fun e => bv (x.mm 1) (e + 1) == cel2 (akv cd a4 e) (akv cd a5 e) (bv (x.mm 1) e)) &&
  (cd r).ak.all (fun e => akv cd r (e + 1) == cel2 (bv (x.mm 0) e) (bv (x.mm 1) e) (akv cd r e)) &&
  leafChk [(cd a0).ak, (cd a1).ak, (cd a2).ak, (cd a3).ak, (cd a4).ak, (cd a5).ak] (cd r).ak

def treeChk (r : Fin n) (os : List (Fin n)) (x : OX) : Bool :=
  match os with
  | [_, _] => true
  | [_, _, _] => true
  | [_, _, _, _] => true
  | [a0, a1, a2, a3, a4] => tree5Chk cd r a0 a1 a2 a3 a4 x
  | [a0, a1, a2, a3, a4, a5] => tree6Chk cd r a0 a1 a2 a3 a4 a5 x
  | _ => false

def joinXChk (ins : List (Fin n)) (o : Fin n) (x : OX) : Bool :=
  (match ins with
   | [i0] => chainChk (cd i0).rq (cd o).rq x.sa x.ca
   | [i0, i1] =>
     (x.mm 0).all (fun e => bv (x.mm 0) (e + 1) == cel2 (rqv cd i0 e) (rqv cd i1 e) (bv (x.mm 0) e)) &&
     chainChk (x.mm 0) (cd o).rq x.sa x.ca
   | _ => false) &&
  leafChk (ins.map fun i => (cd i).rq) (cd o).rq

def muxXChk (z : Fin n) (x : OX) : Bool :=
  (x.mm 0).all (fun e => bv (x.mm 0) (e + 1) == (xv cd z 0 e || xv cd z 1 e)) &&
  bufChk (x.mm 0) (cd z).rq x.cb && leafChk [(cd z).aux 0, (cd z).aux 1] (cd z).rq

def muxnXChk (z : Fin n) (x : OX) : Bool :=
  (x.mm 0).all (fun e => bv (x.mm 0) (e + 1) == (xv cd z 0 e || xv cd z 1 e || xv cd z 2 e)) &&
  chainChk (x.mm 0) (cd z).rq x.sa x.ca && leafChk [(cd z).aux 0, (cd z).aux 1, (cd z).aux 2] (cd z).rq

def amXChk (z : Fin n) (x : OX) : Bool :=
  chainChk (x.mm 0) (cd z).rq x.sa x.ca &&
  (cd z).rq.all (fun e => bv (x.mm 0) e == (xv cd z 0 e || xv cd z 1 e))

def linkXChk (i o : Fin n) (x : OX) : Bool :=
  bufChk ((cd o).aux 0) (cd o).rq x.cb && chainChk ((cd o).aux 0) (cd i).ak x.sa x.ca

def xChk (x : OX) : K n → Bool
  | .forkG i os => treeChk cd i os x
  | .forkH i os _ _ _ _ => treeChk cd i (os.map Prod.fst) x
  | .join ins o _ _ _ => joinXChk cd ins o x
  | .bjoin ins _ _ _ => decide (ins.length = 2)
  | .mux _ _ _ z _ => muxXChk cd z x
  | .muxn _ _ _ _ z _ => muxnXChk cd z x
  | .amerge _ _ z _ => amXChk cd z x
  | .link i o => linkXChk cd i o x
  | _ => true

/-- **The generated-level checker.** -/
def kChkG (x : OX) (sv : Nat → Nat) (k : K n) : Bool := kChk cd sv k && xChk cd x k

/-! ## Soundness -/

variable {cd}

theorem fork_gsound {i : Fin n} {os : List (Fin n)} {x : OX} (h1 : forkChk cd i os = true)
    (h2 : treeChk cd i os x = true) : GenFork (wch cd i) (os.map (wch cd)) := by
  have F := fork_sound h1
  refine ⟨?_, F.wire, F.dat, F.initA, F.initO⟩
  have hc : ∀ t, (wch cd i).ack (t + 1) ≠ (wch cd i).ack t → ∀ c ∈ os,
      (wch cd c).ack t = (wch cd i).ack (t + 1) :=
    fun t ht c hc => F.cel t ht _ (List.mem_map_of_mem hc)
  match os, h2, hc with
  | [a0, a1], _, hc =>
    exact cnode_mk fun t ht => by
      rw [f2_gate]; exact (cel2_eq _ (hc t ht a0 (by simp)) (hc t ht a1 (by simp))).symm
  | [a0, a1, a2], _, hc =>
    exact cnode_mk fun t ht => by
      rw [f3_gate]
      exact (cel3_eq _ (hc t ht a0 (by simp)) (hc t ht a1 (by simp)) (hc t ht a2 (by simp))).symm
  | [a0, a1, a2, a3], _, hc =>
    exact cnode_mk fun t ht => by
      rw [f4_gate]
      exact (cel4_eq _ (hc t ht a0 (by simp)) (hc t ht a1 (by simp)) (hc t ht a2 (by simp))
        (hc t ht a3 (by simp))).symm
  | [a0, a1, a2, a3, a4], h2, _ =>
    simp only [treeChk, tree5Chk, Bool.and_eq_true] at h2
    obtain ⟨⟨hm, hr⟩, hl⟩ := h2
    exact ⟨bv (x.mm 0),
      cnode_of (G := fun p q => cel4 p.1 p.2.1 p.2.2.1 p.2.2.2 q) f5c_gate hm,
      cnode_of (G := fun p q => cel2 p.1 p.2 q) f5t_gate hr, by simp only [bv_zero, wch, CD.ch],
      leaf_sound hl⟩
  | [a0, a1, a2, a3, a4, a5], h2, _ =>
    simp only [treeChk, tree6Chk, Bool.and_eq_true] at h2
    obtain ⟨⟨⟨hm1, hm2⟩, hr⟩, hl⟩ := h2
    exact ⟨bv (x.mm 0), bv (x.mm 1),
      cnode_of (G := fun p q => cel4 p.1 p.2.1 p.2.2.1 p.2.2.2 q) f6a_gate hm1,
      cnode_of (G := fun p q => cel2 p.1 p.2 q) f6b_gate hm2,
      cnode_of (G := fun p q => cel2 p.1 p.2 q) f6t_gate hr,
      by simp only [bv_zero, wch, CD.ch], by simp only [bv_zero, wch, CD.ch], leaf_sound hl⟩
  | [], h2, _ => simp [treeChk] at h2
  | [_], h2, _ => simp [treeChk] at h2
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, h2, _ => simp [treeChk] at h2

theorem map_req (ins : List (Fin n)) :
    (ins.map (wch cd)).map Chan.req = (ins.map fun i => (cd i).rq).map bv := by
  simp [List.map_map, Function.comp_def, wch, CD.ch]

theorem join_gsound {g : List Nat → Nat} {ins : List (Fin n)} {o : Fin n} {x : OX}
    (h1 : joinChk cd g ins o = true) (h2 : joinXChk cd ins o x = true) :
    GenJoin g (ins.map (wch cd)) (wch cd o) := by
  have J := join_sound h1
  simp only [joinXChk, Bool.and_eq_true] at h2
  obtain ⟨hn, hl⟩ := h2
  refine ⟨?_, by rw [map_req]; exact leaf_sound hl, J.wire, J.dat, J.initO, J.initI⟩
  match ins, hn with
  | [i0], hn => exact ⟨(wch cd i0).req, rfl, chain_sound hn, by simp only [wch, CD.ch, bv_zero]⟩
  | [i0, i1], hn =>
    simp only [Bool.and_eq_true] at hn
    exact ⟨bv (x.mm 0), cnode_of (G := fun p q => cel2 p.1 p.2 q) j2_gate hn.1, chain_sound hn.2,
      by simp only [wch, CD.ch, bv_zero]⟩
  | [], hn => simp at hn
  | _ :: _ :: _ :: _, hn => simp at hn

theorem bjoin_gsound {g : List Nat → Nat} {ins : List (Fin n)} {o : Fin n}
    (h1 : joinChk cd g ins o = true) (h2 : decide (ins.length = 2) = true) :
    GenBJoin g (ins.map (wch cd)) (wch cd o) := by
  have J := join_sound h1
  refine ⟨?_, J.wire, J.dat, J.initO, J.initI⟩
  match ins, h2, J with
  | [i0, i1], _, J =>
    exact ⟨wch cd i0, wch cd i1, rfl, cnode_mk fun t ht => by
      rw [j2_gate]
      exact (cel2_eq _ (J.cel t ht (wch cd i0) (by simp)) (J.cel t ht (wch cd i1) (by simp))).symm⟩
  | [], h2, _ => simp at h2
  | [_], h2, _ => simp at h2
  | _ :: _ :: _ :: _, h2, _ => simp at h2

theorem steer_gsound {sel : Nat → Bool} {f : Nat → Nat} {j : Chan} {out : Bool → Chan}
    (S : Steer.Steer sel f j out) : GenSteer sel f j out := by
  refine ⟨fun b t ht => ?_, fun t ht => ?_, S.dat, S.initJ, S.initO⟩
  · rw [S.lut b t ht]
    cases b
    · simp only [steerF]; exact ((steer_gate _ _ false false).1).symm
    · simp only [steerF]; exact ((steer_gate _ _ false false).2.1).symm
  · rw [S.orr t ht]; exact ((steer_gate false false _ _).2.2).symm

theorem mux_gsound {c x y z : Fin n} {ox : OX} (h1 : muxChk cd c x y z = true)
    (h2 : muxXChk cd z ox = true) :
    GenMux sel2 (wch cd x) (wch cd y) (wch cd c) (wch cd z) (bv ((cd z).aux 0)) (bv ((cd z).aux 1)) := by
  have M := mux_sound h1
  simp only [muxXChk, Bool.and_eq_true] at h2
  obtain ⟨⟨he, hb⟩, hl⟩ := h2
  refine ⟨?_, ?_, ?_, ?_, ⟨bv (ox.mm 0), fun t ht => ?_, buf_sound hb,
      by simp only [wch, CD.ch, bv_zero], leaf_sound hl⟩, M.ca, M.dat, M.i0, M.i1, M.iz, M.ix, M.iy, M.ic⟩
  · exact cnode_mk fun t ht => by
      simp only [muxJ0F, (mux_gate _ false _ _ _ false).1]
      exact (cel2_eq _ (M.cj0 t ht).1 (M.cj0 t ht).2).symm
  · exact cnode_mk fun t ht => by
      simp only [muxJ1F, (mux_gate false _ _ _ _ false).2.1]
      exact (cel2_eq _ (M.cj1 t ht).1 (M.cj1 t ht).2).symm
  · exact cnode_mk fun t ht => by
      simp only [muxXaF, (mux_gate _ false false false _ _).2.2.1]
      exact (cel2_eq _ (M.xa t ht).1 (M.xa t ht).2).symm
  · exact cnode_mk fun t ht => by
      simp only [muxYaF, (mux_gate false _ false false _ _).2.2.2]
      exact (cel2_eq _ (M.ya t ht).1 (M.ya t ht).2).symm
  · have := step_of he ht
    simp only [beq_iff_eq] at this
    rw [this]; exact (uor_gate _ _).symm

theorem muxn_gsound {c x0 x1 x2 z : Fin n} {ox : OX} (h1 : muxnChk cd c x0 x1 x2 z = true)
    (h2 : muxnXChk cd z ox = true) :
    GenMuxN selD (fun k => wch cd (cx3 x0 x1 x2 k)) (wch cd c) (wch cd z) (fun k => bv ((cd z).aux k)) := by
  have M := muxn_sound h1
  simp only [muxnXChk, Bool.and_eq_true] at h2
  obtain ⟨⟨he, hc⟩, hl⟩ := h2
  refine ⟨fun k hk => cnode_mk fun t ht => ?_, fun k hk => cnode_mk fun t ht => ?_,
    ⟨bv (ox.mm 0), fun t ht => ?_, chain_sound hc, by simp only [wch, CD.ch, bv_zero], leaf_sound hl⟩,
    M.ca, M.dat, M.ij, M.iz, M.ix, M.ic⟩
  · rw [c2_gate]; exact (cel2_eq _ (M.cj k hk t ht).1 (M.cj k hk t ht).2).symm
  · rw [c2_gate]; exact (cel2_eq _ (M.xa k hk t ht).1 (M.xa k hk t ht).2).symm
  · have := step_of he ht
    simp only [beq_iff_eq] at this
    rw [this]; simp [List.any, Bool.or_assoc]

theorem am_gsound {x y z : Fin n} {ox : OX} (h1 : amChk cd x y z = true) (h2 : amXChk cd z ox = true) :
    GenAMerge (wch cd x) (wch cd y) (wch cd z) (bv ((cd z).aux 0)) (bv ((cd z).aux 1)) := by
  have M := am_sound h1
  simp only [amXChk, Bool.and_eq_true] at h2
  obtain ⟨hc, hi⟩ := h2
  refine ⟨cnode_mk fun t ht => ?_, cnode_mk fun t ht => ?_, ⟨bv (ox.mm 0), chain_sound hc, fun t ht => ?_⟩,
    M.H_ARB1, M.H_ARB2, M.H_ARB_EXCL, M.H_AMERGE_RTZ, M.dat, M.i1, M.i2, M.iz, M.ix, M.iy⟩
  · simp only [arbA1F, (arb_gate _ _ _).1]; exact (cel2_eq _ (M.xa t ht).1 (M.xa t ht).2).symm
  · simp only [arbA2F, (arb_gate _ _ _).2]; exact (cel2_eq _ (M.ya t ht).1 (M.ya t ht).2).symm
  · simpa only [beq_iff_eq] using step_of hi ht

theorem link_gsound {i o : Fin n} {ox : OX} (h1 : linkChk cd i o = true) (h2 : linkXChk cd i o ox = true) :
    GenLink (wch cd i) (wch cd o) (bv ((cd o).aux 0)) := by
  have L := link_sound h1
  simp only [linkXChk, Bool.and_eq_true] at h2
  exact ⟨cnode_mk fun t ht => by rw [link_gate]; exact L.H_CEL_SI t ht, buf_sound h2.1, chain_sound h2.2,
    L.H_LATCH_OPEN, L.H_LATCH_HOLD, L.ic, L.ii, L.io⟩

theorem src_gsound {z : Chan} {v : Nat} (S : Capstone.Src z v) : GenSrc z v :=
  ⟨fun t ht => by rw [S.H_LUT_SI t ht]; exact (src_gate _).symm, S.dat, S.iz⟩

theorem sink_gsound {c : Chan} (S : Ops.Gcd.Sink c) : GenSink c := ⟨S.wire, S.init⟩

/-- **The checker is sound for `GenCell`.** -/
theorem kChkG_sound (x : OX) (sv : Nat → Nat) (k : K n) (h : kChkG cd x sv k = true) :
    GenCell (wch cd) sv k := by
  simp only [kChkG, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  cases k with
  | forkG i os => exact fork_gsound h1 h2
  | forkH i os l hh d hs => exact fork_gsound h1 h2
  | join ins o e js _ => exact join_gsound h1 h2
  | bjoin ins o ec ed => exact bjoin_gsound h1 h2
  | steerC j t f => exact steer_gsound (steer_sound h1)
  | steerD j t f fd _ => exact steer_gsound (steer_sound h1)
  | mux c x y z _ => exact ⟨_, _, mux_gsound h1 h2⟩
  | muxn c x0 x1 x2 z _ => exact ⟨_, muxn_gsound h1 h2⟩
  | amerge x y z _ => exact ⟨_, _, am_gsound h1 h2⟩
  | link i o => exact ⟨_, link_gsound h1 h2⟩
  | src z which _ => exact src_gsound (src_sound h1)
  | sink i => exact sink_gsound (sink_sound h1)

/-! ## O4's `GenCell` gives O4b's `GenCellK` (and `GenCellKP`) -/

theorem joinK_of {m : Trace} : ∀ {ins : List Chan}, JoinNode m ins → KOps.JoinNodeK m ins
  | [_], h => h
  | [_, _], h => h
  | [], h => h.elim
  | _ :: _ :: _ :: _, h => h.elim

theorem genK_of_gen (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (h : GenCell ch sv k) :
    KOps.GenCellK ch sv k := by
  cases k with
  | join ins o e js jw =>
    have h : GenJoin (jg e js) (ins.map ch) (ch o) := h
    obtain ⟨m, hJ, hc, h0⟩ := h.node
    exact ⟨⟨m, joinK_of hJ, hc, h0⟩, h.H_LEAF_PERSIST, h.H_WIRE_DI, h.H_DATA_COMB, h.initO, h.initI⟩
  | _ => unfold KOps.GenCellK; exact h

theorem genKP_of_gen (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (h : GenCell ch sv k) :
    PersistK.GenCellKP ch sv k :=
  PersistK.genP_of ch sv k (genK_of_gen ch sv k h)

end Formal.Net.CellBind.GenWit
