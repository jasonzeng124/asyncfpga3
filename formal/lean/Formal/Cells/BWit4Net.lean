import Formal.Cells.BWit4NChk
import Formal.Cells.BWit4Cells

/-!
# Probe Bwit4 (shard B): a joint witness of the tree-extended driver-bound gcd_hw theorem

`FiniteNetBoundT.gcd_hw_safe_fin_netBT` (as `FiniteNetBoundA`, with every 5/6-way fork's
acknowledge tree gate-modelled too: `bd_ctree #(N)`'s chunk `C4` (leaves 0..3), chunk `C2`
(leaves 4, 5; N = 6) and top `C2`, each `FCelSpec` of its real gate; 170 of 175 links bound on
both sides) has a joint witness on the gate-timed run `chB` of `BWit4Data` (a = 12, b = 18;
every tied gate LUT 1 + wire 1-3):

* `bwit_okT : FGcdNetOKBT chB NBt LB nB` (every tied cell on its real LUT, kernel-checked:
  `BWit4NChk`);
* `gcd_hw_fin_netBT_witness`: jointly with C's H_OTHER, H_BUNDLE, H_CM_FORCED, out0 = 6;
  `gcd_hw_fin_netBT_consistent` applies the theorem.

## Assumed / proved / NOT covered

**Proved:** the items above; nothing assumed. **NOT covered:** one run, unit LUT delays,
simulator-chosen wire delays, R = 2; no arbiter race on this run (two arbiters hand a waiting
request over, but the closest request rises at one arbiter are 36 ticks apart, so
H_EXC_CLEAN is never tight); contract cells at muxn, sources, sinks;
C's H_OTHER is still a hypothesis of the theorem, discharged here on this run by C's checkers.
Core Lean only.
-/

namespace Formal.Cells.BWit4
open Formal.Cells
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe
open Formal.Net.CapNet.Wit (CD nv bv yW yW_good A0 B0)
open Formal.Cells.WinFifoCausal (nt nt_lo τs)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.LutFbBridge2Env (Wire ε ash isLink)
open Formal.Cells.FiniteRunsWit (sortedB cL rst2 bndD linkB wire_shift)
open Formal.Cells.AssumeGuaranteeEnds (GPin gE GC2 GC3 GC4)
open Formal.Cells.AssumeGuaranteeEndsNet (GD)
open Formal.Cells.AssumeGuaranteeEndsCap (forkOuts joinIns steerIn d0 LinkOut)
open Formal.Cells.FiniteNet
open Formal.Cells.FiniteNetBound (DK FU FCelTieB stJ brC stJ_of_steerIn)
open Formal.Cells.FiniteNetBoundM (DKM reqSrcM ackSrcM BoundRM BoundAM FGcdNetOKBM FTiedM muxC
  uorF)
open Formal.Cells.FiniteNetBoundA (DKA reqSrcA ackSrcA BoundRA BoundAA FGcdNetOKBA FGcdNetA qF r0F
  gF ArbPins)
open Formal.Cells.FiniteNetComb (FCombSpec)
open Formal.Cells.FiniteNetBoundT (DKT reqSrcT ackSrcT BoundRT BoundAT FGcdNetOKBT FGcdNetT treeOuts
  ArbPinsT)
open Formal.Cells.AssumeGuaranteeMuxNTree (rp5 ip4 rp6 ip2)
open Formal.Cells.BWit3 (combB combB_spec)
open Formal.Cells.BWit2 (mjB maB bufB mjB_spec maB_spec bufB_spec)
open Formal.Cells.FiniteNetWit2 (lkIO lkIO_some faOK jrOK Gf2 Gf3 Gf4 celB celT stB orB lstB
  orE σT κT finRange_getD' getD_ge1)
open Formal.Cells.BWit (shL wire_map gE_map celTm stTm orTm fkIn jnOut linkB_spec'
  celB_spec' stB_spec' orB_spec')
open Formal.Cells.AssumeGuaranteeMuxNFin (FMuxJSpec FMuxASpec FBufSpec)
open Formal.Net.Ops.Gen (genF)
open Formal.Gen Formal.Gen.Cells

/-! ## 1. Facts from the checks -/

theorem shL_length (k : Nat) (L : List Nat) : (shL k L).length = L.length := by
  simp [shL]

theorem wire_of (c : Fin NC) : 1 ≤ wR c ∧ 1 ≤ wA c ∧
    (cdB c).rq = shL (wR c - 1) (lstN (dR c)) ∧ (cdB c).ak = shL (wA c - 1) (lstN (dA c)) ∧
    sortedB (cdB c).rq = true ∧ sortedB (cdB c).ak = true := by
  have h := bw_all c
  unfold wireChk at h
  rw [dif_pos c.isLt] at h
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at h
  obtain ⟨⟨⟨⟨⟨a, b⟩, e1⟩, e2⟩, s1⟩, s2⟩ := h
  exact ⟨a, b, e1, e2, s1, s2⟩

theorem op_of (o : Fin NO) :
    lkChk o = true ∧ faChkB o = true ∧ jrChkB o = true ∧ stChkB o = true ∧ muxChk o = true ∧
    srtChk o = true ∧ arbChk o = true ∧ treeChk o = true := by
  have h := bopN_all o
  unfold opChkN at h
  rw [dif_pos o.isLt] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1, h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, barb_all o, h.2⟩

theorem cell_eq (d : DKT) : d.cell NBt = toCm d := by
  cases d with
  | base d =>
    cases d with
    | base d =>
      cases d with
      | base d => cases d <;> rfl
      | md o i => rfl
      | ma o b => rfl
    | aR o => rfl
    | aA o b => rfl
  | tR o => rfl

theorem boundR (c : Fin NC) : BoundRT NBt c (pRB c) := by
  intro d hd; show dR c = d.cell NBt; unfold dR; rw [hd, cell_eq]

theorem boundA (c : Fin NC) : BoundAT NBt c (pAB c) := by
  intro d hd; show dA c = d.cell NBt; unfold dA; rw [hd, cell_eq]

theorem srt_of (o : Fin NO) : sortedB (mjN o false) = true ∧ sortedB (mjN o true) = true ∧
    sortedB (moL.getD o.val []) = true ∧ sortedB (md0L.getD o.val []) = true ∧
    sortedB (aqL.getD o.val []) = true ∧ sortedB (ag1L.getD o.val []) = true ∧
    sortedB (ag2L.getD o.val []) = true ∧ sortedB (tc0L.getD o.val []) = true ∧
    sortedB (tc1L.getD o.val []) = true := by
  have h := (op_of o).2.2.2.2.2.1
  simp only [srtChk, Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2, h.1.1.1.1.1.2, h.1.1.1.1.2,
    h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem lstN_sorted (c : Cm) : sortedB (lstN c) = true := by
  cases c with
  | lk o => simp only [lstN]; split
            · exact (wire_of _).2.2.2.2.1
            · rfl
  | fa o => simp only [lstN]; split
            · split
              · exact (wire_of _).2.2.2.2.2
              · rfl
            · rfl
  | jr o => simp only [lstN]; split
            · split
              · exact (wire_of _).2.2.2.2.1
              · rfl
            · rfl
  | sb o b => simp only [lstN]; split
              · exact (wire_of _).2.2.2.2.1
              · rfl
  | ao o => simp only [lstN]; split
            · exact (wire_of _).2.2.2.2.2
            · rfl
  | mj o b =>
    show sortedB (mjN o b) = true
    cases b
    · exact (srt_of o).1
    · exact (srt_of o).2.1
  | ma o b => simp only [lstN]; split
              · exact (wire_of _).2.2.2.2.2
              · rfl
  | md o i =>
    simp only [lstN]; split
    · exact (srt_of o).2.2.2.1
    · split
      · exact (wire_of _).2.2.2.2.1
      · rfl
  | mo o => exact (srt_of o).2.2.1
  | aq o => exact (srt_of o).2.2.2.2.1
  | aR o => simp only [lstN]; split
            · exact (wire_of _).2.2.2.2.1
            · rfl
  | ag o b =>
    show sortedB ((if b then ag2L else ag1L).getD o.val []) = true
    cases b
    · exact (srt_of o).2.2.2.2.2.1
    · exact (srt_of o).2.2.2.2.2.2.1
  | aa o b => simp only [lstN]; split
              · exact (wire_of _).2.2.2.2.2
              · rfl
  | tr o => simp only [lstN]; split
            · split
              · exact (wire_of _).2.2.2.2.2
              · rfl
            · rfl
  | tn o k =>
    show sortedB ((if k.val = 0 then tc0L else tc1L).getD o.val []) = true
    by_cases hk : k.val = 0
    · rw [if_pos hk]; exact (srt_of o).2.2.2.2.2.2.2.1
    · rw [if_neg hk]; exact (srt_of o).2.2.2.2.2.2.2.2
  | rq c => exact (wire_of c).2.2.2.2.1
  | ak c => exact (wire_of c).2.2.2.2.2

theorem pinR_L (c : Fin NC) : LB (dR c) = fun j => j < (cdB c).rq.length := by
  funext j; show (j < (lstN (dR c)).length) = _
  rw [(wire_of c).2.2.1, shL_length]

theorem pinA_L (c : Fin NC) : LB (dA c) = fun j => j < (cdB c).ak.length := by
  funext j; show (j < (lstN (dA c)).length) = _
  rw [(wire_of c).2.2.2.1, shL_length]

theorem pinR_gE (c : Fin NC) : ∀ j, j < (cdB c).rq.length →
    gE DB.τ (pRB c) j = ε (bv (cdB c).rq) 1 1 (fun j => (cdB c).rq.getD j 1) j := by
  intro j hj
  obtain ⟨h1, _, e, _⟩ := wire_of c
  have hj' : j < (lstN (dR c)).length := by
    have := shL_length (wR c - 1) (lstN (dR c)); rw [← e] at this; omega
  have := gE_map (τ := DB.τ) (p := pRB c) (Ld := lstN (dR c)) h1
    (by show bv (cdB c).rq = _; rw [e]) rfl rfl hj' rfl
  rw [this, ← e]

theorem pinA_gE (c : Fin NC) : ∀ j, j < (cdB c).ak.length →
    gE DB.τ (pAB c) j = ε (bv (cdB c).ak) 1 1 (fun j => (cdB c).ak.getD j 1) j := by
  intro j hj
  obtain ⟨_, h1, _, e, _⟩ := wire_of c
  have hj' : j < (lstN (dA c)).length := by
    have := shL_length (wA c - 1) (lstN (dA c)); rw [← e] at this; omega
  have := gE_map (τ := DB.τ) (p := pAB c) (Ld := lstN (dA c)) h1
    (by show bv (cdB c).ak = _; rw [e]) rfl rfl hj' rfl
  rw [this, ← e]

theorem pinI_gE (d : Cm) : ∀ j, j < (lstN d).length →
    gE DB.τ (pIn d) j = ε (bv (lstN d)) 1 1 (fun j => (lstN d).getD j 1) j := fun _ _ => rfl

theorem pinI_L (d : Cm) : LB d = fun j => j < (lstN d).length := rfl

theorem pin_formB (c : Cm) (p : GPin Cm) (hp : p ∈ pinsB c) :
    ∃ x, p = pRB x ∨ p = pAB x ∨ ∃ d, p = pIn d := by
  cases c with
  | lk o =>
    revert hp; simp only [pinsB]; split
    · intro hp; simp at hp; rcases hp with rfl | rfl
      · exact ⟨_, Or.inl rfl⟩
      · exact ⟨_, Or.inr (Or.inl rfl)⟩
    · intro hp; simp at hp
  | fa o =>
    revert hp; simp only [pinsB, faPinsB]; split
    · intro hp; obtain ⟨x, _, rfl⟩ := List.mem_map.1 hp; exact ⟨x, Or.inr (Or.inl rfl)⟩
    · intro hp; simp at hp
  | jr o =>
    revert hp; simp only [pinsB, jrPinsB]; split
    · intro hp; obtain ⟨x, _, rfl⟩ := List.mem_map.1 hp; exact ⟨x, Or.inl rfl⟩
    · intro hp; simp at hp
  | sb o b =>
    revert hp; simp only [pinsB]; split
    · intro hp; simp at hp; subst hp; exact ⟨_, Or.inl rfl⟩
    · intro hp; simp at hp
  | ao o =>
    revert hp; simp only [pinsB]; split
    · intro hp; simp [apB] at hp; rcases hp with rfl | rfl
      · exact ⟨_, Or.inr (Or.inl rfl)⟩
      · exact ⟨_, Or.inr (Or.inl rfl)⟩
    · intro hp; simp at hp
  | mj o b =>
    revert hp; simp only [pinsB]; split
    · intro hp; simp at hp; rcases hp with rfl | rfl
      · exact ⟨_, Or.inl rfl⟩
      · exact ⟨_, Or.inl rfl⟩
    · intro hp; simp at hp
  | ma o b =>
    revert hp; simp only [pinsB]; split
    · intro hp; simp at hp; rcases hp with rfl | rfl
      · exact ⟨d0, Or.inr (Or.inr ⟨_, rfl⟩)⟩
      · exact ⟨_, Or.inr (Or.inl rfl)⟩
    · intro hp; simp at hp
  | md o i =>
    revert hp; simp only [pinsB]; split
    · intro hp; simp at hp; subst hp; exact ⟨d0, Or.inr (Or.inr ⟨_, rfl⟩)⟩
    · intro hp; simp at hp
  | mo o =>
    revert hp; simp only [pinsB]; split
    · intro hp; simp at hp; rcases hp with rfl | rfl
      · exact ⟨d0, Or.inr (Or.inr ⟨_, rfl⟩)⟩
      · exact ⟨d0, Or.inr (Or.inr ⟨_, rfl⟩)⟩
    · intro hp; simp at hp
  | aq o =>
    revert hp; simp only [pinsB]; split
    · intro hp; simp at hp; rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨_, Or.inl rfl⟩
      · exact ⟨_, Or.inl rfl⟩
      · exact ⟨d0, Or.inr (Or.inr ⟨_, rfl⟩)⟩
      · exact ⟨_, Or.inr (Or.inl rfl)⟩
    · intro hp; simp at hp
  | aR o =>
    revert hp; simp only [pinsB]; split
    · intro hp; simp at hp; rcases hp with rfl | rfl | rfl | rfl
      · exact ⟨_, Or.inl rfl⟩
      · exact ⟨_, Or.inl rfl⟩
      · exact ⟨d0, Or.inr (Or.inr ⟨_, rfl⟩)⟩
      · exact ⟨_, Or.inr (Or.inl rfl)⟩
    · intro hp; simp at hp
  | ag o b =>
    revert hp; simp only [pinsB]; split
    · intro hp; simp at hp; rcases hp with rfl | rfl | rfl
      · exact ⟨_, Or.inl rfl⟩
      · exact ⟨_, Or.inl rfl⟩
      · exact ⟨d0, Or.inr (Or.inr ⟨_, rfl⟩)⟩
    · intro hp; simp at hp
  | aa o b =>
    revert hp; simp only [pinsB]; split
    · intro hp; simp at hp; rcases hp with rfl | rfl
      · exact ⟨d0, Or.inr (Or.inr ⟨_, rfl⟩)⟩
      · exact ⟨_, Or.inr (Or.inl rfl)⟩
    · intro hp; simp at hp
  | tr o =>
    revert hp; simp only [pinsB]; split
    · split
      · intro hp; obtain ⟨i, _, rfl⟩ := List.mem_map.1 hp; unfold rp5; split
        · exact ⟨d0, Or.inr (Or.inr ⟨_, rfl⟩)⟩
        · exact ⟨_, Or.inr (Or.inl rfl)⟩
      · intro hp; obtain ⟨i, _, rfl⟩ := List.mem_map.1 hp; unfold rp6; split
        · exact ⟨d0, Or.inr (Or.inr ⟨_, rfl⟩)⟩
        · exact ⟨d0, Or.inr (Or.inr ⟨_, rfl⟩)⟩
    · intro hp; simp at hp
  | tn o k =>
    revert hp; simp only [pinsB]; split
    · split
      · intro hp; obtain ⟨i, _, rfl⟩ := List.mem_map.1 hp; exact ⟨_, Or.inr (Or.inl rfl)⟩
      · split
        · intro hp; obtain ⟨i, _, rfl⟩ := List.mem_map.1 hp; exact ⟨_, Or.inr (Or.inl rfl)⟩
        · intro hp; simp at hp
    · intro hp; simp at hp
  | rq c => simp [pinsB] at hp
  | ak c => simp [pinsB] at hp

theorem fnetWB : FNetW DB LB where
  H_RST _ := rfl
  H_WIRE c p hp := by
    obtain ⟨x, rfl | rfl | ⟨d, rfl⟩⟩ := pin_formB c p hp
    · obtain ⟨h1, _, e, _⟩ := wire_of x
      show Wire (wR x) (wR x) (cL (lstN (dR x))) (bv (cdB x).rq)
      rw [e]; exact wire_map _ h1
    · obtain ⟨_, h1, _, e, _⟩ := wire_of x
      show Wire (wA x) (wA x) (cL (lstN (dA x))) (bv (cdB x).ak)
      rw [e]; exact wire_map _ h1
    · exact wire_shift (lstN d)
  H_LUT_POS _ := Nat.le_refl 1
  H_FLOOR c p hp j _ := by
    obtain ⟨x, rfl | rfl | ⟨d, rfl⟩⟩ := pin_formB c p hp
    · show wR x ≤ _ + wR x; omega
    · show wA x ≤ _ + wA x; omega
    · show 1 ≤ _ + 1; omega

theorem cell_okB (c : Cm) : FCellOK DB LB c := by
  intro T _
  exact FiniteNetWit.cL_gph (lstN_sorted c) (T + 1)

/-! ## 2. The tied cells' specs -/

theorem lk_specB {o : Fin NO} {i o' : Fin NC} (h : opAt o = .link i o') :
    FLinkSpec DB LB (.lk o) (pRB i) (pAB o') 3 3 ∧ LinkOut DB (.lk o) (cdB i).ch (cdB o').ch 3 3 := by
  have hc := (op_of o).1
  have hio : lkIO (opAt o) = some (i, o') := lkIO_some.2 h
  unfold lkChk at hc; rw [hio] at hc
  simp only [Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at hc
  obtain ⟨⟨⟨⟨hb, htm⟩, hn⟩, h0⟩, hs⟩ := hc
  have hl : lstN (.lk o) = (cdB o').rq := by simp only [lstN, hio]
  refine linkB_spec' hb (by show cL (lstN _) = _; rw [hl]) (by show bv (lstN _) = _; rw [hl])
    rfl rfl rfl rfl rfl rfl (by show pinsB (Cm.lk o) = [pRB i, pAB o']; simp only [pinsB, hio])
    rfl (pinR_gE i) (fun j => ?_) rfl (pinA_gE o') (pinR_L i) (pinA_L o')
    (by funext j; show (j < (lstN (Cm.lk o)).length) = _; rw [hl, hn])
    (fun j _ => by show (lstN (Cm.lk o)).getD j 1 = _; rw [hl]) htm
  show 2 ≤ nt (bv (cdB i).rq) (wR i) (wR i) ((lstN (dR i)).getD j 1) (Vph j)
  have a := nt_lo (bv (cdB i).rq) (lo := wR i) (hi := wR i) ((lstN (dR i)).getD j 1) (Vph j)
    (Nat.le_refl _)
  have b := getD_ge1 hs h0 j
  have c := (wire_of i).1
  omega

theorem fa_specB {o : Fin NO} {os : List (Fin NC)} (hos : forkOuts (opAt o) = some os) {k : Nat}
    (hk : os.length = k) {G : (Fin k → Bool) → Bool → Bool → Bool}
    {Gf : (Fin k → Bool) → Bool → Bool} (hG : ∀ p q r, G p q r = (!r && Gf p q))
    (hL : LutFbBridge2.CelLaw G)
    (hchk : celB Gf (fun i : Fin k => (cdB (os.getD i.val d0)).ak) (lstN (.fa o)) = true)
    (htm : celTm (fun i : Fin k => (cdB (os.getD i.val d0)).ak) (lstN (.fa o)) = true) :
    FCelSpec G DB LB (.fa o) (fun i : Fin k => pAB (os.getD i.val d0)) 1 := by
  refine celB_spec' hG hL hchk rfl rfl rfl rfl rfl rfl rfl rfl ?_ (fun _ => rfl)
    (fun i => pinA_gE _) (fun i => pinA_L _) rfl (fun _ _ => rfl) htm
  show faPinsB o = _
  unfold faPinsB; rw [hos]
  have := congrArg (List.map pAB) (finRange_getD' os d0 k hk); rw [List.map_map] at this
  exact this.symm

theorem jr_specB {o : Fin NO} {ins : List (Fin NC)} (hos : joinIns (opAt o) = some ins)
    (hk : ins.length = 2)
    (hchk : celB Gf2 (fun i : Fin 2 => (cdB (ins.getD i.val d0)).rq) (lstN (.jr o)) = true)
    (htm : celTm (fun i : Fin 2 => (cdB (ins.getD i.val d0)).rq) (lstN (.jr o)) = true) :
    FCelSpec GC2 DB LB (.jr o) (fun i : Fin 2 => pRB (ins.getD i.val d0)) 1 := by
  refine celB_spec' (fun p q r => ?_) AssumeGuaranteeEnds.lawC2 hchk rfl rfl rfl rfl rfl rfl rfl
    rfl ?_ (fun _ => rfl) (fun i => pinR_gE _) (fun i => pinR_L _) rfl (fun _ _ => rfl) htm
  · unfold GC2; rw [AssumeGuaranteeEnds.c2_gen]; rfl
  · show jrPinsB o = _
    unfold jrPinsB; rw [hos]
    have := congrArg (List.map pRB) (finRange_getD' ins d0 2 hk); rw [List.map_map] at this
    exact this.symm

theorem st_facts {o : Fin NO} {j t f : Fin NC} (h : stJ (opAt o) = some (j, t, f)) :
    stB true (cdB j).rq (selB j) (tabOf o) (lstN (.sb o true)) = true ∧
    stTm true (cdB j).rq (tabOf o) (lstN (.sb o true)) = true ∧
    stB false (cdB j).rq (selB j) (tabOf o) (lstN (.sb o false)) = true ∧
    stTm false (cdB j).rq (tabOf o) (lstN (.sb o false)) = true ∧
    orB (tabOf o) (cdB f).ak (cdB t).ak (lstN (.ao o)) = true ∧
    orTm (tabOf o) (cdB f).ak (cdB t).ak (lstN (.ao o)) = true ∧ bndD (cdB j).dt = true := by
  have hc := (op_of o).2.2.2.1
  unfold stChkB at hc; rw [h] at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f'⟩, g⟩ := hc
  exact ⟨a, b, c, d, e, f', g⟩

theorem sb_specB {o : Fin NO} {j t f : Fin NC} (h : stJ (opAt o) = some (j, t, f)) (b : Bool) :
    FSteerSpec DB LB (.sb o b) (pRB j) b (selB j) (σT (tabOf o)) (κT (tabOf o) b) := by
  obtain ⟨hT, tT, hF, tF, _, _, hbd⟩ := st_facts h
  have hs : ∀ u, FiniteRunsWit.NB ≤ u → selB j u = selB j FiniteRunsWit.NB := fun u hu => by
    unfold selB; rw [FiniteRunsWit.nv_tail (cdB j).d0 hbd u hu]
  have hchk : stB b (cdB j).rq (selB j) (tabOf o) (lstN (.sb o b)) = true := by
    cases b
    · exact hF
    · exact hT
  have htm : stTm b (cdB j).rq (tabOf o) (lstN (.sb o b)) = true := by
    cases b
    · exact tF
    · exact tT
  exact stB_spec' hchk hs rfl rfl rfl
    (by show pinsB (Cm.sb o b) = [pRB j]; simp only [pinsB, h]) rfl (pinR_gE j) (pinR_L j) rfl
    (fun _ _ => rfl) htm

theorem ao_specB {o : Fin NO} {j t f : Fin NC} (h : stJ (opAt o) = some (j, t, f)) :
    FOrSpec DB LB (.ao o) (fun a0 a1 => genF bd_steer "uack" .O ["ack0", "ack1"] [a0, a1])
      (apB t f) (σT (tabOf o)) (κT (tabOf o)) := by
  obtain ⟨_, _, _, _, hO, tO, _⟩ := st_facts h
  refine orB_spec' (a0 := (cdB f).ak) (a1 := (cdB t).ak) hO AssumeGuaranteeMuxOr.uack_gate
    rfl rfl rfl ?_ (fun b => by cases b <;> rfl) (fun b => ?_) (fun b => ?_) rfl (fun _ _ => rfl) tO
  · show pinsB (Cm.ao o) = _; simp only [pinsB, h]
  · cases b
    · exact pinA_gE f
    · exact pinA_gE t
  · cases b
    · exact pinA_L f
    · exact pinA_L t

/-! ## 3. The mux cells -/

theorem muxC_of {o : Fin NO} {cc x y z : Fin NC} {mw : MW} (h : opAt o = .mux cc x y z mw) :
    muxC (opAt o) = some (cc, x, y, z) := by rw [h]; rfl

theorem mux_facts {o : Fin NO} {cc x y z : Fin NC} (h : muxC (opAt o) = some (cc, x, y, z)) :
    mjB false (cdB x).rq (cdB cc).rq (selB cc) (tabOf o) (mjN o false) = true ∧
    mjB true (cdB y).rq (cdB cc).rq (selB cc) (tabOf o) (mjN o true) = true ∧
    maB false (mjN o false) (cdB z).ak (tabOf o) (lstN (.ma o false)) = true ∧
    maB true (mjN o true) (cdB z).ak (tabOf o) (lstN (.ma o true)) = true ∧
    orB (tabOf o) (mjN o false) (mjN o true) (lstN (.mo o)) = true ∧
    orTm (tabOf o) (mjN o false) (mjN o true) (lstN (.mo o)) = true ∧
    bufB (lstN (.mo o)) (lstN (.md o 0)) = true ∧ bufB (lstN (.md o 0)) (lstN (.md o 1)) = true ∧
    bndD (cdB cc).dt = true := by
  have hc := (op_of o).2.2.2.2.1
  unfold muxChk at hc; rw [h] at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩, g⟩, i⟩, k⟩, _⟩, _⟩, _⟩, _⟩ := hc
  exact ⟨a, b, c, d, e, f, g, i, k⟩

theorem isMux_of {o : Fin NO} {cc x y z : Fin NC} (h : muxC (opAt o) = some (cc, x, y, z)) :
    isMux o = true := by unfold isMux; rw [h]; rfl

theorem mj_specB {o : Fin NO} {cc x y z : Fin NC} (h : muxC (opAt o) = some (cc, x, y, z))
    (b : Bool) :
    FMuxJSpec DB LB (.mj o b) (pRB (if b then y else x)) (pRB cc) b (selB cc)
      (σT (tabOf o)) (κT (tabOf o) b) 1 := by
  obtain ⟨h0, h1, _, _, _, _, _, _, hbd⟩ := mux_facts h
  have hs : ∀ u, FiniteRunsWit.NB ≤ u → selB cc u = selB cc FiniteRunsWit.NB := fun u hu => by
    unfold selB; rw [FiniteRunsWit.nv_tail (cdB cc).d0 hbd u hu]
  have hp : pinsB (Cm.mj o b) = [pRB (if b then y else x), pRB cc] := by simp only [pinsB, h]
  cases b
  · exact mjB_spec h0 hs rfl rfl rfl rfl rfl rfl rfl rfl hp rfl rfl (pinR_gE x) (pinR_gE cc)
      (pinR_L x) (pinR_L cc) rfl (fun _ _ => rfl)
  · exact mjB_spec h1 hs rfl rfl rfl rfl rfl rfl rfl rfl hp rfl rfl (pinR_gE y) (pinR_gE cc)
      (pinR_L y) (pinR_L cc) rfl (fun _ _ => rfl)

theorem ma_specB {o : Fin NO} {cc x y z : Fin NC} (h : muxC (opAt o) = some (cc, x, y, z))
    (b : Bool) :
    FMuxASpec DB LB (.ma o b) (pIn (.mj o b)) (pAB z) (κT (tabOf o) b) 1 := by
  obtain ⟨_, _, a0, a1, _, _, _, _, _⟩ := mux_facts h
  have hp : pinsB (Cm.ma o b) = [pIn (.mj o b), pAB z] := by simp only [pinsB, h]
  cases b
  · exact maB_spec a0 rfl rfl rfl rfl rfl rfl rfl rfl hp rfl rfl (pinI_gE (.mj o false))
      (pinA_gE z) (pinI_L (.mj o false)) (pinA_L z) rfl (fun _ _ => rfl)
  · exact maB_spec a1 rfl rfl rfl rfl rfl rfl rfl rfl hp rfl rfl (pinI_gE (.mj o true))
      (pinA_gE z) (pinI_L (.mj o true)) (pinA_L z) rfl (fun _ _ => rfl)

theorem mo_specB {o : Fin NO} {cc x y z : Fin NC} (h : muxC (opAt o) = some (cc, x, y, z)) :
    FOrSpec DB LB (.mo o) uorF (fun b => pIn (.mj o b)) (σT (tabOf o)) (κT (tabOf o)) := by
  obtain ⟨_, _, _, _, hO, tO, _, _, _⟩ := mux_facts h
  refine orB_spec' (a0 := mjN o false) (a1 := mjN o true) hO AssumeGuaranteeMuxOr.uor_gate
    rfl rfl rfl ?_ (fun b => by cases b <;> rfl) (fun b => ?_) (fun b => ?_) rfl (fun _ _ => rfl) tO
  · show pinsB (Cm.mo o) = _; simp only [pinsB, isMux_of h, ite_true]
  · cases b
    · exact pinI_gE (.mj o false)
    · exact pinI_gE (.mj o true)
  · cases b
    · exact pinI_L (.mj o false)
    · exact pinI_L (.mj o true)

theorem md_specB {o : Fin NO} {cc x y z : Fin NC} (h : muxC (opAt o) = some (cc, x, y, z))
    (i : Fin 2) :
    FBufSpec DB LB (.md o i) (pIn (if i.val = 0 then .mo o else .md o 0)) := by
  obtain ⟨_, _, _, _, _, _, b0, b1, _⟩ := mux_facts h
  have hp : pinsB (Cm.md o i) = [pIn (if i.val = 0 then .mo o else .md o 0)] := by
    simp only [pinsB, isMux_of h, ite_true]
  match i, hp with
  | ⟨0, _⟩, hp => exact bufB_spec b0 rfl rfl rfl hp rfl (pinI_gE _) (pinI_L _) rfl (fun _ _ => rfl)
  | ⟨1, _⟩, hp => exact bufB_spec b1 rfl rfl rfl hp rfl (pinI_gE _) (pinI_L _) rfl (fun _ _ => rfl)


/-! ## 3b. The arbiter cells -/

theorem ameC_of {o : Fin NO} {x y z : Fin NC} {w : Nat} (h : opAt o = .amerge x y z w) :
    ameC (opAt o) = some (x, y, z) := by rw [h]; rfl

theorem arb_facts {o : Fin NO} {x y z : Fin NC} (h : ameC (opAt o) = some (x, y, z)) :
    combB qF [(cdB x).rq, (cdB y).rq, lstN (.aq o), (cdB z).ak] (lstN (.aq o)) = true ∧
    combB r0F [(cdB x).rq, (cdB y).rq, lstN (.aq o), (cdB z).ak] (lstN (.aR o)) = true ∧
    (∀ b, combB (gF b) [(cdB x).rq, (cdB y).rq, lstN (.aq o)] (lstN (.ag o b)) = true) ∧
    ∀ b, maB b (lstN (.ag o b)) (cdB z).ak (tabA o) (lstN (.aa o b)) = true := by
  have hc := (op_of o).2.2.2.2.2.2.1
  unfold arbChk at hc; rw [h] at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨⟨⟨a, b⟩, c⟩, d⟩, e⟩, f⟩ := hc
  refine ⟨a, b, fun bb => ?_, fun bb => ?_⟩
  · cases bb
    · exact c
    · exact d
  · cases bb
    · exact e
    · exact f

theorem aq_specB {o : Fin NO} {x y z : Fin NC} (h : ameC (opAt o) = some (x, y, z)) :
    FCombSpec DB LB (.aq o) qF [pRB x, pRB y, pIn (.aq o), pAB z]
      (fun j => (lstN (.aq o)).getD j 1 - 1) (fun j => j < (lstN (.aq o)).length) :=
  combB_spec (D := DB) (L := LB) (c := Cm.aq o) (ps := [pRB x, pRB y, pIn (.aq o), pAB z])
    (arb_facts h).1 rfl rfl rfl rfl (by show pinsB (Cm.aq o) = _; simp only [pinsB, h])
    rfl (fun _ _ => rfl) rfl

theorem aR_specB {o : Fin NO} {x y z : Fin NC} (h : ameC (opAt o) = some (x, y, z)) :
    FCombSpec DB LB (.aR o) r0F [pRB x, pRB y, pIn (.aq o), pAB z]
      (fun j => (lstN (.aR o)).getD j 1 - 1) (fun j => j < (lstN (.aR o)).length) :=
  combB_spec (arb_facts h).2.1 rfl rfl rfl rfl (by show pinsB (Cm.aR o) = _; simp only [pinsB, h])
    rfl (fun _ _ => rfl) rfl

theorem ag_specB {o : Fin NO} {x y z : Fin NC} (h : ameC (opAt o) = some (x, y, z)) (b : Bool) :
    FCombSpec DB LB (.ag o b) (gF b) [pRB x, pRB y, pIn (.aq o)]
      (fun j => (lstN (.ag o b)).getD j 1 - 1) (fun j => j < (lstN (.ag o b)).length) :=
  combB_spec ((arb_facts h).2.2.1 b) rfl rfl rfl rfl
    (by show pinsB (Cm.ag o b) = _; simp only [pinsB, h]) rfl (fun _ _ => rfl) rfl

theorem aa_specB {o : Fin NO} {x y z : Fin NC} (h : ameC (opAt o) = some (x, y, z)) (b : Bool) :
    FMuxASpec DB LB (.aa o b) (pIn (.ag o b)) (pAB z) (κT (tabA o) b) 1 :=
  maB_spec ((arb_facts h).2.2.2 b) rfl rfl rfl rfl rfl rfl rfl rfl
    (by show pinsB (Cm.aa o b) = _; simp only [pinsB, h]) rfl rfl (pinI_gE (.ag o b))
    (pinA_gE z) (pinI_L (.ag o b)) (pinA_L z) rfl (fun _ _ => rfl)

theorem arbPinsB {o : Fin NO} (x y z : Fin NC) :
    ArbPinsT NBt chB o x y z [pRB x, pRB y, pIn (.aq o), pAB z] 4 :=
  ⟨pRB x, pRB y, pIn (.aq o), Or.inr ⟨pAB z, rfl, rfl, boundA z⟩, rfl, boundR x, rfl, boundR y,
    rfl, rfl⟩

theorem arbPinsB3 {o : Fin NO} (x y z : Fin NC) :
    ArbPinsT NBt chB o x y z [pRB x, pRB y, pIn (.aq o)] 3 :=
  ⟨pRB x, pRB y, pIn (.aq o), Or.inl rfl, rfl, boundR x, rfl, boundR y, rfl, rfl⟩

/-! ## 3c. The fork-tree cells -/

theorem tree_facts {o : Fin NO} {os : List (Fin NC)} (h : treeOuts (opAt o) = some os) :
    celB Gf4 (fun i : Fin 4 => (cdB (os.getD i.val d0)).ak) (lstN (.tn o 0)) = true ∧
    celTm (fun i : Fin 4 => (cdB (os.getD i.val d0)).ak) (lstN (.tn o 0)) = true ∧
    (if os.length = 5 then
      celB Gf2 (fun i : Fin 2 => if i.val = 0 then lstN (.tn o 0) else (cdB (os.getD 4 d0)).ak)
        (lstN (.tr o)) &&
      celTm (fun i : Fin 2 => if i.val = 0 then lstN (.tn o 0) else (cdB (os.getD 4 d0)).ak)
        (lstN (.tr o))
    else
      celB Gf2 (fun i : Fin 2 => (cdB (os.getD (i.val + 4) d0)).ak) (lstN (.tn o 1)) &&
      celTm (fun i : Fin 2 => (cdB (os.getD (i.val + 4) d0)).ak) (lstN (.tn o 1)) &&
      celB Gf2 (fun i : Fin 2 => if i.val = 0 then lstN (.tn o 0) else lstN (.tn o 1))
        (lstN (.tr o)) &&
      celTm (fun i : Fin 2 => if i.val = 0 then lstN (.tn o 0) else lstN (.tn o 1))
        (lstN (.tr o))) = true := by
  have hc := (op_of o).2.2.2.2.2.2.2
  unfold treeChk at hc; rw [h] at hc
  simp only [Bool.and_eq_true] at hc
  exact ⟨hc.1.1.1.1, hc.1.1.1.2, hc.1.1.2⟩

theorem tn0_specB {o : Fin NO} {os : List (Fin NC)} (h : treeOuts (opAt o) = some os) {m : Nat} :
    FCelSpec GC4 DB LB (.tn o 0) (ip4 (m := m) (lvB os)) 1 := by
  obtain ⟨hc, ht, _⟩ := tree_facts h
  refine celB_spec' (fun p q r => ?_) AssumeGuaranteeEnds.lawC4 hc rfl rfl rfl rfl rfl rfl rfl rfl
    ?_ (fun _ => rfl) (fun i => pinA_gE _) (fun i => pinA_L _) rfl (fun _ _ => rfl) ht
  · unfold GC4; rw [AssumeGuaranteeEnds.c4_gen]; rfl
  · show pinsB (Cm.tn o 0) = _; simp only [pinsB, h]; rfl

theorem tn1_specB {o : Fin NO} {os : List (Fin NC)} (h : treeOuts (opAt o) = some os)
    (e : os.length = 6) : FCelSpec GC2 DB LB (.tn o 1) (ip2 (lvB os)) 1 := by
  obtain ⟨_, _, hc⟩ := tree_facts h
  rw [if_neg (by omega)] at hc
  simp only [Bool.and_eq_true] at hc
  refine celB_spec' (fun p q r => ?_) AssumeGuaranteeEnds.lawC2 hc.1.1.1 rfl rfl rfl rfl rfl rfl
    rfl rfl ?_ (fun _ => rfl) (fun i => pinA_gE _) (fun i => pinA_L _) rfl (fun _ _ => rfl) hc.1.1.2
  · unfold GC2; rw [AssumeGuaranteeEnds.c2_gen]; rfl
  · show pinsB (Cm.tn o 1) = _; simp only [pinsB, h]
    rw [if_neg (by decide), if_pos e]; rfl

theorem tr5_specB {o : Fin NO} {os : List (Fin NC)} (h : treeOuts (opAt o) = some os)
    (e : os.length = 5) : FCelSpec GC2 DB LB (.tr o) (rp5 (pIn (.tn o 0)) (lvB os)) 1 := by
  obtain ⟨_, _, hc⟩ := tree_facts h
  rw [if_pos e] at hc
  simp only [Bool.and_eq_true] at hc
  refine celB_spec' (fun p q r => ?_) AssumeGuaranteeEnds.lawC2 hc.1 rfl rfl rfl rfl rfl rfl
    rfl rfl ?_ (fun i => ?_) (fun i => ?_) (fun i => ?_) rfl (fun _ _ => rfl) hc.2
  · unfold GC2; rw [AssumeGuaranteeEnds.c2_gen]; rfl
  · show pinsB (Cm.tr o) = _; simp only [pinsB, h]; rw [if_pos e]
  · by_cases hi : i.val = 0
    · simp only [rp5, hi, ite_true]; rfl
    · simp only [rp5, hi, ite_false]; rfl
  · by_cases hi : i.val = 0
    · simp only [rp5, hi, ite_true]; exact pinI_gE _
    · simp only [rp5, hi, ite_false]; exact pinA_gE _
  · by_cases hi : i.val = 0
    · simp only [rp5, hi, ite_true]; exact pinI_L _
    · simp only [rp5, hi, ite_false]; exact pinA_L _

theorem tr6_specB {o : Fin NO} {os : List (Fin NC)} (h : treeOuts (opAt o) = some os)
    (e : os.length = 6) : FCelSpec GC2 DB LB (.tr o) (rp6 (pIn (.tn o 0)) (pIn (.tn o 1))) 1 := by
  obtain ⟨_, _, hc⟩ := tree_facts h
  rw [if_neg (by omega)] at hc
  simp only [Bool.and_eq_true] at hc
  refine celB_spec' (fun p q r => ?_) AssumeGuaranteeEnds.lawC2 hc.1.2 rfl rfl rfl rfl rfl rfl
    rfl rfl ?_ (fun i => ?_) (fun i => ?_) (fun i => ?_) rfl (fun _ _ => rfl) hc.2
  · unfold GC2; rw [AssumeGuaranteeEnds.c2_gen]; rfl
  · show pinsB (Cm.tr o) = _; simp only [pinsB, h]; rw [if_neg (by omega)]
  · by_cases hi : i.val = 0
    · simp only [rp6, hi, ite_true]; rfl
    · simp only [rp6, hi, ite_false]; rfl
  · by_cases hi : i.val = 0
    · simp only [rp6, hi, ite_true]; exact pinI_gE _
    · simp only [rp6, hi, ite_false]; exact pinI_gE _
  · by_cases hi : i.val = 0
    · simp only [rp6, hi, ite_true]; exact pinI_L _
    · simp only [rp6, hi, ite_false]; exact pinI_L _

/-! ## Every tied cell drives its own output channel -/

theorem fkIn_eq (k : K NC) : fkIn k = FiniteNetBound.forkIn k := by cases k <;> rfl
theorem jnOut_eq (k : K NC) : jnOut k = FiniteNetBound.joinOut k := by cases k <;> rfl

theorem drv_fork (o : Fin NO) (os : List (Fin NC)) (i : Fin NC) (hos : forkOuts (opAt o) = some os)
    (h2 : 2 ≤ os.length) (h4 : os.length ≤ 4) (hi : FiniteNetBound.forkIn (opAt o) = some i) :
    ∃ wl wh, Wire wl wh (DB.O (.fa o)) (chB i).ack := by
  have hok : faOK o = true := by
    unfold faOK; rw [hos]; exact decide_eq_true ⟨h2, h4⟩
  have hl : lstN (.fa o) = (cdB i).ak := by
    simp only [lstN, hok, ite_true, fkIn_eq, hi]
  exact ⟨1, 1, by show Wire 1 1 (cL (lstN (.fa o))) (bv (cdB i).ak); rw [hl]; exact wire_shift _⟩

theorem drv_join (o : Fin NO) (ins : List (Fin NC)) (z : Fin NC) (hos : joinIns (opAt o) = some ins)
    (h2 : ins.length = 2) (hz : FiniteNetBound.joinOut (opAt o) = some z) :
    ∃ wl wh, Wire wl wh (DB.O (.jr o)) (chB z).req := by
  have hok : jrOK o = true := by
    unfold jrOK; rw [hos]; simp [h2]
  have hl : lstN (.jr o) = (cdB z).rq := by
    simp only [lstN, hok, ite_true, jnOut_eq, hz]
  exact ⟨1, 1, by show Wire 1 1 (cL (lstN (.jr o))) (bv (cdB z).rq); rw [hl]; exact wire_shift _⟩

theorem drv_steer (o : Fin NO) (j t f : Fin NC) (h : stJ (opAt o) = some (j, t, f)) :
    (∀ b, ∃ wl wh, Wire wl wh (DB.O (.sb o b)) (chB (brC t f b)).req) ∧
    ∃ wl wh, Wire wl wh (DB.O (.ao o)) (chB j).ack := by
  refine ⟨fun b => ⟨1, 1, ?_⟩, ⟨1, 1, ?_⟩⟩
  · have hl : lstN (.sb o b) = (cdB (brC t f b)).rq := by simp only [lstN, h]
    show Wire 1 1 (cL (lstN (.sb o b))) (bv (cdB (brC t f b)).rq); rw [hl]; exact wire_shift _
  · have hl : lstN (.ao o) = (cdB j).ak := by simp only [lstN, h]
    show Wire 1 1 (cL (lstN (.ao o))) (bv (cdB j).ak); rw [hl]; exact wire_shift _

theorem drv_mux (o : Fin NO) (cc x y z : Fin NC) (mw : MW) (h : opAt o = .mux cc x y z mw) :
    (∃ wl wh, Wire wl wh (DB.O (.md o 1)) (chB z).req) ∧
    ∀ b, ∃ wl wh, Wire wl wh (DB.O (.ma o b)) (chB (if b then y else x)).ack := by
  have hm := muxC_of h
  refine ⟨⟨1, 1, ?_⟩, fun b => ⟨1, 1, ?_⟩⟩
  · have hl : lstN (.md o 1) = (cdB z).rq := by simp only [lstN, hm]; rfl
    show Wire 1 1 (cL (lstN (.md o 1))) (bv (cdB z).rq); rw [hl]; exact wire_shift _
  · have hl : lstN (.ma o b) = (cdB (if b then y else x)).ak := by simp only [lstN, hm]
    show Wire 1 1 (cL (lstN (.ma o b))) (bv (cdB (if b then y else x)).ak); rw [hl]
    exact wire_shift _

theorem drv_arb (o : Fin NO) (x y z : Fin NC) (w : Nat) (h : opAt o = .amerge x y z w) :
    (∃ wl wh, Wire wl wh (DB.O (.aR o)) (chB z).req) ∧
    ∀ b, ∃ wl wh, Wire wl wh (DB.O (.aa o b)) (chB (if b then y else x)).ack := by
  have hm := ameC_of h
  refine ⟨⟨1, 1, ?_⟩, fun b => ⟨1, 1, ?_⟩⟩
  · have hl : lstN (.aR o) = (cdB z).rq := by simp only [lstN, hm]
    show Wire 1 1 (cL (lstN (.aR o))) (bv (cdB z).rq); rw [hl]; exact wire_shift _
  · have hl : lstN (.aa o b) = (cdB (if b then y else x)).ak := by simp only [lstN, hm]
    show Wire 1 1 (cL (lstN (.aa o b))) (bv (cdB (if b then y else x)).ak); rw [hl]
    exact wire_shift _

theorem drv_tree (o : Fin NO) (os : List (Fin NC)) (i : Fin NC) (h : treeOuts (opAt o) = some os)
    (hi : FiniteNetBound.forkIn (opAt o) = some i) :
    ∃ wl wh, Wire wl wh (DB.O (.tr o)) (chB i).ack := by
  have ht : isTree o = true := by unfold isTree; rw [h]; rfl
  have hl : lstN (.tr o) = (cdB i).ak := by
    simp only [lstN, ht, ite_true, fkIn_eq, hi]
  exact ⟨1, 1, by show Wire 1 1 (cL (lstN (.tr o))) (bv (cdB i).ak); rw [hl]; exact wire_shift _⟩

/-! ## 4. `FGcdNetOKBT` on `chB` -/

theorem h_forkB (o : Fin NO) (os : List (Fin NC)) (hos : forkOuts (opAt o) = some os)
    (h2 : 2 ≤ os.length) (h4 : os.length ≤ 4) :
    FCelTieB NBt.toFGcdNet LB (NBt.fa o) os (fun c => (chB c).ack) (BoundAT NBt) := by
  have hc := (op_of o).2.1
  unfold faChkB at hc; rw [hos] at hc; dsimp only at hc
  unfold celChkB at hc
  rcases (show os.length = 2 ∨ os.length = 3 ∨ os.length = 4 by omega) with e | e | e
  · rw [if_pos e] at hc; simp only [Bool.and_eq_true] at hc
    refine Or.inl ⟨e, _, 1, fa_specB hos e (fun p q r => ?_) AssumeGuaranteeEnds.lawC2 hc.1 hc.2,
      fun _ => ⟨rfl, boundA _⟩⟩
    unfold GC2; rw [AssumeGuaranteeEnds.c2_gen]; rfl
  · rw [if_neg (by omega), if_pos e] at hc; simp only [Bool.and_eq_true] at hc
    refine Or.inr (Or.inl ⟨e, _, 1, fa_specB hos e (fun p q r => ?_) AssumeGuaranteeEnds.lawC3
      hc.1 hc.2, fun _ => ⟨rfl, boundA _⟩⟩)
    unfold GC3; rw [AssumeGuaranteeEnds.c3_gen]; rfl
  · rw [if_neg (by omega), if_neg (by omega), if_pos e] at hc; simp only [Bool.and_eq_true] at hc
    refine Or.inr (Or.inr ⟨e, _, 1, fa_specB hos e (fun p q r => ?_) AssumeGuaranteeEnds.lawC4
      hc.1 hc.2, fun _ => ⟨rfl, boundA _⟩⟩)
    unfold GC4; rw [AssumeGuaranteeEnds.c4_gen]; rfl

theorem h_joinB (o : Fin NO) (ins : List (Fin NC)) (hos : joinIns (opAt o) = some ins)
    (h2 : ins.length = 2) :
    FCelTieB NBt.toFGcdNet LB (NBt.jr o) ins (fun c => (chB c).req) (BoundRT NBt) := by
  have hc := (op_of o).2.2.1
  unfold jrChkB at hc; rw [hos] at hc; dsimp only at hc; rw [if_pos h2] at hc
  unfold celChkB at hc; rw [if_pos h2] at hc; simp only [Bool.and_eq_true] at hc
  exact Or.inl ⟨h2, _, 1, jr_specB hos h2 hc.1 hc.2, fun _ => ⟨rfl, boundR _⟩⟩

/-- **`chB` meets the tree-extended driver-bound hypothesis** with the network `NBt`. -/
theorem bwit_okT : FGcdNetOKBT chB NBt LB nB where
  NW := fnetWB
  H_FIN _ _ := Iff.rfl
  H_LINK o i o' h := ⟨pRB i, pAB o', 3, 3, (lk_specB h).1, rfl, rfl, (lk_specB h).2,
    boundR i, boundA o'⟩
  H_FORK := h_forkB
  H_JOIN := h_joinB
  H_STEER o j h b := by
    obtain ⟨t, f, h'⟩ := stJ_of_steerIn h
    exact ⟨pRB j, selB j, σT (tabOf o), κT (tabOf o) b, sb_specB h' b, rfl, boundR j, rfl⟩
  H_SOR o j t f h := ⟨apB t f, σT (tabOf o), κT (tabOf o), ao_specB h,
    fun b => ⟨rfl, boundA _⟩⟩
  H_MUXJ o cc x y z mw h b := ⟨pRB (if b then y else x), pRB cc, selB cc, σT (tabOf o),
    κT (tabOf o) b, 1, mj_specB (muxC_of h) b, rfl, rfl, boundR _, boundR cc, rfl⟩
  H_MUXA o cc x y z mw h b := ⟨pIn (.mj o b), pAB z, κT (tabOf o) b, 1, ma_specB (muxC_of h) b,
    rfl, rfl, boundA z⟩
  H_MUXO o cc x y z mw h := ⟨fun b => pIn (.mj o b), σT (tabOf o), κT (tabOf o),
    mo_specB (muxC_of h), fun _ => rfl⟩
  H_MUXD o cc x y z mw h i := ⟨pIn (if i.val = 0 then .mo o else .md o 0),
    md_specB (muxC_of h) i, by split <;> rfl⟩
  H_ARBQ o x y z w h := ⟨_, _, _, aq_specB (ameC_of h), arbPinsB x y z⟩
  H_ARBR o x y z w h := ⟨_, _, _, aR_specB (ameC_of h), arbPinsB x y z⟩
  H_ARBG o x y z w h b := ⟨_, _, _, ag_specB (ameC_of h) b, arbPinsB3 x y z⟩
  H_ARBA o x y z w h b := ⟨pIn (.ag o b), pAB z, κT (tabA o) b, 1, aa_specB (ameC_of h) b, rfl,
    rfl, boundA z⟩
  H_TREE5 o os h e := ⟨pIn (.tn o 0), lvB (m := 5) os, 1, 1, tr5_specB h e, tn0_specB h, rfl,
    fun _ => ⟨rfl, boundA _⟩⟩
  H_TREE6 o os h e := ⟨pIn (.tn o 0), pIn (.tn o 1), lvB (m := 6) os, 1, 1, 1, tr6_specB h e,
    tn0_specB h, tn1_specB h e, rfl, rfl, fun _ => ⟨rfl, boundA _⟩⟩
  H_REST c _ := cell_okB c
  H_DRV_FORK := drv_fork
  H_DRV_JOIN := drv_join
  H_DRV_STEER := drv_steer
  H_DRV_MUX := drv_mux
  H_DRV_ARB := drv_arb
  H_DRV_TREE := drv_tree

/-! ## 5. The joint witness -/

/-- **Joint non-vacuity of the tree-extended driver-bound gate-level theorem**
(`FiniteNetBoundT.gcd_hw_safe_fin_netBT`) on the gate-timed run `chB` (a = 12, b = 18). -/
theorem gcd_hw_fin_netBT_witness :
    ∃ (ch : Fin NC → Chan) (N : FGcdNetT) (L : N.ι → Nat → Prop) (n : N.ι → Nat),
      FGcdNetOKBT ch N L n ∧
      (∀ o : Fin NO, isLink (opAt o) = false → Cell ch (srcV 12 18) (opAt o)) ∧
      (∀ c, Held (ch c)) ∧
      (∃ y, Good 12 18 y ∧ ∀ o : Fin NO, Forced ch (omOf 12 18 y) (opAt o)) ∧
      (∃ k e, TokAt (ch out0) k e ∧ (ch out0).dat e = 6) :=
  ⟨chB, NBt, LB, nB, bwit_okT, fun o _ => b_cells o, b_held, ⟨yW, yW_good, b_forced⟩,
    ⟨0, out0CloseB, b_out0⟩⟩

theorem gcd_hw_fin_netBT_consistent :
    (∀ k e, TokAt (chB out0) k e → (chB out0).dat e = 6) ∧ TokAt (chB out0) 0 out0CloseB := by
  have h := FiniteNetBoundT.gcd_hw_safe_fin_netBT 12 18 chB NBt LB nB bwit_okT
    (fun o _ => b_cells o) b_held ⟨yW, yW_good, b_forced⟩
  rw [show Nat.gcd 12 18 = 6 by decide] at h
  exact ⟨h.1, b_out0.1⟩

end Formal.Cells.BWit4
