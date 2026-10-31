import Formal.Cells.BWit2NChk
import Formal.Cells.BWit2Cells

/-!
# Probe Bwit2 (shard B): a joint witness of the mux-extended driver-bound gcd_hw theorem

`FiniteNetBoundM.gcd_hw_safe_fin_netBM` (links, forks N ≤ 4, 2-input joins, steers AND every
`bd_mux` gate-modelled, every tied pin's driver the cell the netlist names; 124 of 175 links
bound on both sides) has a joint witness on the gate-timed run `chB` of `BWit2Data` (a = 12,
b = 18; every tied gate LUT 1 + wire 1-3; C's mux join traces are B's join nodes 6 ticks late):

* `bwit_okM : FGcdNetOKBM chB NBm LB nB` (every tied cell on its real LUT, kernel-checked:
  `BWit2NChk`);
* `gcd_hw_fin_netBM_witness`: jointly with C's H_OTHER, H_BUNDLE, H_CM_FORCED, out0 = 6;
  `gcd_hw_fin_netBM_consistent` applies the theorem;
* `bwitM_link_env`: on this witness, the links bound on both sides take both environment
  pins from tied gate-model cells with pins.

## Assumed / proved / NOT covered

**Proved:** the three items; nothing assumed. **NOT covered:** one run, unit LUT delays,
simulator-chosen wire delays, R = 2 (no delay band exercised); contract cells at muxn,
amerge, sources, sinks, 1-input joins, fork trees; C's H_OTHER (192 non-link operators) is
still a hypothesis of the theorem, discharged here on this run by C's checkers. Core Lean only.
-/

namespace Formal.Cells.BWit2
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
    srtChk o = true := by
  have h := bop_all o
  unfold opChkB at h
  rw [dif_pos o.isLt] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1.1.1, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

theorem cell_eq (d : DKM) : d.cell NBm = toCm d := by
  cases d with
  | base d => cases d <;> rfl
  | md o i => rfl
  | ma o b => rfl

theorem boundR (c : Fin NC) : BoundRM NBm c (pRB c) := by
  intro d hd; show dR c = d.cell NBm; unfold dR; rw [hd, cell_eq]

theorem boundA (c : Fin NC) : BoundAM NBm c (pAB c) := by
  intro d hd; show dA c = d.cell NBm; unfold dA; rw [hd, cell_eq]

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
    have h := (op_of o).2.2.2.2.2
    simp only [srtChk, Bool.and_eq_true] at h
    show sortedB (mjN o b) = true
    cases b
    · exact h.1.1.1
    · exact h.1.1.2
  | ma o b => simp only [lstN]; split
              · exact (wire_of _).2.2.2.2.2
              · rfl
  | md o i =>
    have h := (op_of o).2.2.2.2.2
    simp only [srtChk, Bool.and_eq_true] at h
    simp only [lstN]; split
    · exact h.2
    · split
      · exact (wire_of _).2.2.2.2.1
      · rfl
  | mo o =>
    have h := (op_of o).2.2.2.2.2
    simp only [srtChk, Bool.and_eq_true] at h
    exact h.1.2
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

/-! ## 4. `FGcdNetOKBM` on `chB` -/

theorem h_forkB (o : Fin NO) (os : List (Fin NC)) (hos : forkOuts (opAt o) = some os)
    (h2 : 2 ≤ os.length) (h4 : os.length ≤ 4) :
    FCelTieB NBm.toFGcdNet LB (NBm.fa o) os (fun c => (chB c).ack) (BoundAM NBm) := by
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
    FCelTieB NBm.toFGcdNet LB (NBm.jr o) ins (fun c => (chB c).req) (BoundRM NBm) := by
  have hc := (op_of o).2.2.1
  unfold jrChkB at hc; rw [hos] at hc; dsimp only at hc; rw [if_pos h2] at hc
  unfold celChkB at hc; rw [if_pos h2] at hc; simp only [Bool.and_eq_true] at hc
  exact Or.inl ⟨h2, _, 1, jr_specB hos h2 hc.1 hc.2, fun _ => ⟨rfl, boundR _⟩⟩

/-- **`chB` meets the mux-extended driver-bound hypothesis** with the network `NBm`. -/
theorem bwit_okM : FGcdNetOKBM chB NBm LB nB where
  NW := fnetWB
  H_FIN _ _ := Iff.rfl
  H_LINK o i o' h := ⟨pRB i, pAB o', 3, 3, (lk_specB h).1, rfl, rfl, (lk_specB h).2,
    boundR i, boundA o'⟩
  H_FORK := h_forkB
  H_JOIN := h_joinB
  H_STEER o j h b := by
    obtain ⟨t, f, h'⟩ := stJ_of_steerIn h
    exact ⟨pRB j, selB j, σT (tabOf o), κT (tabOf o) b, sb_specB h' b, rfl, boundR j⟩
  H_SOR o j t f h := ⟨apB t f, σT (tabOf o), κT (tabOf o), ao_specB h,
    fun b => ⟨rfl, boundA _⟩⟩
  H_MUXJ o cc x y z mw h b := ⟨pRB (if b then y else x), pRB cc, selB cc, σT (tabOf o),
    κT (tabOf o) b, 1, mj_specB (muxC_of h) b, rfl, rfl, boundR _, boundR cc⟩
  H_MUXA o cc x y z mw h b := ⟨pIn (.mj o b), pAB z, κT (tabOf o) b, 1, ma_specB (muxC_of h) b,
    rfl, rfl, boundA z⟩
  H_MUXO o cc x y z mw h := ⟨fun b => pIn (.mj o b), σT (tabOf o), κT (tabOf o),
    mo_specB (muxC_of h), fun _ => rfl⟩
  H_MUXD o cc x y z mw h i := ⟨pIn (if i.val = 0 then .mo o else .md o 0),
    md_specB (muxC_of h) i, by split <;> rfl⟩
  H_REST c _ := cell_okB c

/-! ## 5. The joint witness -/

/-- **Joint non-vacuity of the mux-extended driver-bound gate-level theorem**
(`FiniteNetBoundM.gcd_hw_safe_fin_netBM`) on the gate-timed run `chB` (a = 12, b = 18). -/
theorem gcd_hw_fin_netBM_witness :
    ∃ (ch : Fin NC → Chan) (N : FiniteNetBoundM.FGcdNetM) (L : N.ι → Nat → Prop) (n : N.ι → Nat),
      FGcdNetOKBM ch N L n ∧
      (∀ o : Fin NO, isLink (opAt o) = false → Cell ch (srcV 12 18) (opAt o)) ∧
      (∀ c, Held (ch c)) ∧
      (∃ y, Good 12 18 y ∧ ∀ o : Fin NO, Forced ch (omOf 12 18 y) (opAt o)) ∧
      (∃ k e, TokAt (ch out0) k e ∧ (ch out0).dat e = 6) :=
  ⟨chB, NBm, LB, nB, bwit_okM, fun o _ => b_cells o, b_held, ⟨yW, yW_good, b_forced⟩,
    ⟨0, out0CloseB, b_out0⟩⟩

theorem gcd_hw_fin_netBM_consistent :
    (∀ k e, TokAt (chB out0) k e → (chB out0).dat e = 6) ∧ TokAt (chB out0) 0 out0CloseB := by
  have h := FiniteNetBoundM.gcd_hw_safe_fin_netBM 12 18 chB NBm LB nB bwit_okM
    (fun o _ => b_cells o) b_held ⟨yW, yW_good, b_forced⟩
  rw [show Nat.gcd 12 18 = 6 by decide] at h
  exact ⟨h.1, b_out0.1⟩

/-- On the witness, a link bound on both sides takes both environment pins from tied
gate-model cells (muxes included) with pins. -/
theorem bwitM_link_env {o : Fin NO} {i o' : Fin NC} (h : opAt o = .link i o') {dr da : DKM}
    (hr : reqSrcM FU i = some dr) (ha : ackSrcM FU o' = some da) :
    ∃ rp ap Es Ea, FLinkSpec DB LB (.lk o) rp ap Es Ea ∧ rp.drv = toCm dr ∧ ap.drv = toCm da ∧
      FTiedM NBm (toCm dr) ∧ FTiedM NBm (toCm da) ∧ DB.pins (toCm dr) ≠ [] ∧
      DB.pins (toCm da) ≠ [] := by
  obtain ⟨rp, ap, Es, Ea, S, _, _, e1, e2, t1, t2, p1, p2⟩ :=
    FiniteNetBoundM.link_env_boundM bwit_okM h hr ha
  rw [cell_eq] at e1 e2 t1 t2 p1 p2
  exact ⟨rp, ap, Es, Ea, S, e1, e2, t1, t2, p1, p2⟩

end Formal.Cells.BWit2
