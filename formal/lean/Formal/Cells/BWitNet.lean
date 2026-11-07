import Formal.Cells.BWitNChk
import Formal.Cells.BWitCells

/-!
# Probe Bwit (shard B): a joint witness of the DRIVER-BOUND gate-level gcd_hw theorem

`FiniteNetBound.gcd_hw_safe_fin_netB` (C's gcd_hw safety from ONE gate-level network whose
tied cells' pins are wired to the cells the netlist names) had no witness, and on C's own
unit-delay run it cannot have one (`FiniteNetSrc.chW_steer_unwired`). Here it has one, on the
gate-timed run `chB` (`BWitData`: a = 12, b = 18, B-tied operators take LUT 1 + wire 1):

* `bwit_ok : FGcdNetOKB chB NBn LB nB`: every link, 2..4-way fork acknowledge C-element,
  2-input join request C-element, steer branch and steer acknowledge OR is B's gate model on
  the REAL LUTs (Bfin3's checkers, generalised in `BWitLib`), its node IS the channel signal
  it drives (one tick earlier), and every one of its pins is driven, through a wire of delay
  1, 2 or 3, by the cell the netlist names (`dR`/`dA` = `reqSrc`/`ackSrc`), kernel-checked
  (`BWitNChk`). Contract cells (`rq c`, `ak c`) drive only the pins whose netlist driver is an
  operator B does not gate-model.
* `gcd_hw_fin_netB_witness`: `chB` meets `FGcdNetOKB` and C's H_OTHER, H_BUNDLE, H_CM_FORCED
  jointly, and out0 latches a token carrying 6; `gcd_hw_fin_netB_consistent` applies the
  theorem.
* `bwit_link_env`: on this witness, for the 63 links bound on both sides (`bound_census`),
  the request and acknowledge pin drivers are tied gate-model cells with pins.

## Assumed / proved / NOT covered

**Proved:** the three items above; nothing is assumed (all hypotheses are discharged on the
run). **NOT covered (what the witness does not show):** (i) one run, one input pair, unit LUT
delay and wire delays 1..3 chosen by the simulator; every window is met at width 0 (no delay
band exercised); (ii) the contract cells' truncated contracts hold because their conclusions
do (their nodes are clean step signals), exactly at the 112 link sides `bound_census`
counts as unbound, and on all non-link pins whose driver is untied; (iii) `R = 2`; (iv) C's
operator models still carry H_OTHER for the 192 non-link operators: B's models discharge only
the links' contracts. Core Lean only.
-/

namespace Formal.Cells.BWit
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
open Formal.Cells.FiniteNetBound (DK reqSrc ackSrc FU BoundR BoundA FCelTieB FGcdNetOKB stJ brC
  stJ_of_steerIn)
open Formal.Cells.FiniteNetWit2 (Cl lkIO lkIO_some faOK jrOK Gf2 Gf3 Gf4 celB celT stB orB lstB
  orE σT κT finRange_getD' getD_ge1)
open Formal.Net.Ops.Gen (genF)
open Formal.Gen Formal.Gen.Cells

/-! ## 1. Facts from the checks -/

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
    lkChk o = true ∧ faChkB o = true ∧ jrChkB o = true ∧ stChkB o = true := by
  have h := bop_all o
  unfold opChkB at h
  rw [dif_pos o.isLt] at h
  simp only [Bool.and_eq_true] at h
  exact ⟨h.1.1.1, h.1.1.2, h.1.2, h.2⟩

theorem cell_eq (d : DK) : d.cell NBn = toCl d := by cases d <;> rfl

theorem boundR (c : Fin NC) : BoundR NBn c (pRB c) := by
  intro d hd; show dR c = d.cell NBn; unfold dR; rw [hd, cell_eq]

theorem boundA (c : Fin NC) : BoundA NBn c (pAB c) := by
  intro d hd; show dA c = d.cell NBn; unfold dA; rw [hd, cell_eq]

theorem shL_length (k : Nat) (L : List Nat) : (shL k L).length = L.length := by simp [shL]

theorem lstN_form (c : Cl) : lstN c = [] ∨ ∃ x : Fin NC, lstN c = (cdB x).rq ∨ lstN c = (cdB x).ak := by
  cases c with
  | lk o => simp only [lstN]; split
            · exact Or.inr ⟨_, Or.inl rfl⟩
            · exact Or.inl rfl
  | fa o => simp only [lstN]; split
            · split
              · exact Or.inr ⟨_, Or.inr rfl⟩
              · exact Or.inl rfl
            · exact Or.inl rfl
  | jr o => simp only [lstN]; split
            · split
              · exact Or.inr ⟨_, Or.inl rfl⟩
              · exact Or.inl rfl
            · exact Or.inl rfl
  | sb o b => simp only [lstN]; split
              · exact Or.inr ⟨_, Or.inl rfl⟩
              · exact Or.inl rfl
  | ao o => simp only [lstN]; split
            · exact Or.inr ⟨_, Or.inr rfl⟩
            · exact Or.inl rfl
  | rq c => exact Or.inr ⟨c, Or.inl rfl⟩
  | ak c => exact Or.inr ⟨c, Or.inr rfl⟩

theorem lstN_sorted (c : Cl) : sortedB (lstN c) = true := by
  rcases lstN_form c with h | ⟨x, h | h⟩ <;> rw [h]
  · rfl
  · exact (wire_of x).2.2.2.2.1
  · exact (wire_of x).2.2.2.2.2

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

theorem pin_formB (c : Cl) (p : GPin Cl) (hp : p ∈ pinsB c) : ∃ x, p = pRB x ∨ p = pAB x := by
  cases c with
  | lk o =>
    revert hp; simp only [pinsB]; split
    · intro hp; simp at hp; rcases hp with rfl | rfl
      · exact ⟨_, Or.inl rfl⟩
      · exact ⟨_, Or.inr rfl⟩
    · intro hp; simp at hp
  | fa o =>
    revert hp; simp only [pinsB, faPinsB]; split
    · intro hp; obtain ⟨x, _, rfl⟩ := List.mem_map.1 hp; exact ⟨x, Or.inr rfl⟩
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
      · exact ⟨_, Or.inr rfl⟩
      · exact ⟨_, Or.inr rfl⟩
    · intro hp; simp at hp
  | rq c => simp [pinsB] at hp
  | ak c => simp [pinsB] at hp

/-- **The network's wires**: every pin is a wire of its bound driver's node. -/
theorem fnetWB : FNetW DB LB where
  H_RST _ := rfl
  H_WIRE c p hp := by
    obtain ⟨x, rfl | rfl⟩ := pin_formB c p hp
    · obtain ⟨h1, _, e, _⟩ := wire_of x
      show Wire (wR x) (wR x) (cL (lstN (dR x))) (bv (cdB x).rq)
      rw [e]; exact wire_map _ h1
    · obtain ⟨_, h1, _, e, _⟩ := wire_of x
      show Wire (wA x) (wA x) (cL (lstN (dA x))) (bv (cdB x).ak)
      rw [e]; exact wire_map _ h1
  H_LUT_POS _ := Nat.le_refl 1
  H_FLOOR c p hp j _ := by
    obtain ⟨x, rfl | rfl⟩ := pin_formB c p hp
    · show wR x ≤ _ + wR x; omega
    · show wA x ≤ _ + wA x; omega

/-- Every cell's node is a clean step signal, so every cell meets its truncated contract. -/
theorem cell_okB (c : Cl) : FCellOK DB LB c := by
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
    rfl rfl rfl rfl rfl rfl (by show pinsB (Cl.lk o) = [pRB i, pAB o']; simp only [pinsB, hio])
    rfl (pinR_gE i) (fun j => ?_) rfl (pinA_gE o') (pinR_L i) (pinA_L o')
    (by funext j; show (j < (lstN (Cl.lk o)).length) = _; rw [hl, hn])
    (fun j _ => by show (lstN (Cl.lk o)).getD j 1 = _; rw [hl]) htm
  -- reset ends before every request edge: the driver's edges are ≥ 1, the wire ≥ 1
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
  have hc := (op_of o).2.2.2
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
    (by show pinsB (Cl.sb o b) = [pRB j]; simp only [pinsB, h]) rfl (pinR_gE j) (pinR_L j) rfl
    (fun _ _ => rfl) htm

theorem ao_specB {o : Fin NO} {j t f : Fin NC} (h : stJ (opAt o) = some (j, t, f)) :
    FOrSpec DB LB (.ao o) (fun a0 a1 => genF bd_steer "uack" .O ["ack0", "ack1"] [a0, a1])
      (apB t f) (σT (tabOf o)) (κT (tabOf o)) := by
  obtain ⟨_, _, _, _, hO, tO, _⟩ := st_facts h
  refine orB_spec' (a0 := (cdB f).ak) (a1 := (cdB t).ak) hO AssumeGuaranteeMuxOr.uack_gate
    rfl rfl rfl ?_ (fun b => by cases b <;> rfl) (fun b => ?_) (fun b => ?_) rfl (fun _ _ => rfl) tO
  · show pinsB (Cl.ao o) = _; simp only [pinsB, h]
  · cases b
    · exact pinA_gE f
    · exact pinA_gE t
  · cases b
    · exact pinA_L f
    · exact pinA_L t


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

/-! ## 3. `FGcdNetOKB` on `chB` -/

theorem h_forkB (o : Fin NO) (os : List (Fin NC)) (hos : forkOuts (opAt o) = some os)
    (h2 : 2 ≤ os.length) (h4 : os.length ≤ 4) :
    FCelTieB NBn LB (NBn.fa o) os (fun c => (chB c).ack) (BoundA NBn) := by
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
    (h2 : ins.length = 2) : FCelTieB NBn LB (NBn.jr o) ins (fun c => (chB c).req) (BoundR NBn) := by
  have hc := (op_of o).2.2.1
  unfold jrChkB at hc; rw [hos] at hc; dsimp only at hc; rw [if_pos h2] at hc
  unfold celChkB at hc; rw [if_pos h2] at hc; simp only [Bool.and_eq_true] at hc
  exact Or.inl ⟨h2, _, 1, jr_specB hos h2 hc.1 hc.2, fun _ => ⟨rfl, boundR _⟩⟩

/-- **`chB` meets the driver-bound hypothesis** with the network `NBn`. -/
theorem bwit_ok : FGcdNetOKB chB NBn LB nB where
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
  H_REST c _ := cell_okB c
  H_DRV_FORK := drv_fork
  H_DRV_JOIN := drv_join
  H_DRV_STEER := drv_steer

/-! ## 4. The joint witness -/

/-- **Joint non-vacuity of the driver-bound gate-level theorem**
(`FiniteNetBound.gcd_hw_safe_fin_netB`) on the gate-timed run `chB` (a = 12, b = 18). -/
theorem gcd_hw_fin_netB_witness :
    ∃ (ch : Fin NC → Chan) (N : FGcdNet) (L : N.ι → Nat → Prop) (n : N.ι → Nat),
      FGcdNetOKB ch N L n ∧
      (∀ o : Fin NO, isLink (opAt o) = false → Cell ch (srcV 12 18) (opAt o)) ∧
      (∀ c, Held (ch c)) ∧
      (∃ y, Good 12 18 y ∧ ∀ o : Fin NO, Forced ch (omOf 12 18 y) (opAt o)) ∧
      (∃ k e, TokAt (ch out0) k e ∧ (ch out0).dat e = 6) :=
  ⟨chB, NBn, LB, nB, bwit_ok, fun o _ => b_cells o, b_held, ⟨yW, yW_good, b_forced⟩,
    ⟨0, out0CloseB, b_out0⟩⟩

/-- The driver-bound theorem applied to the witness gives the value it latches. -/
theorem gcd_hw_fin_netB_consistent :
    (∀ k e, TokAt (chB out0) k e → (chB out0).dat e = 6) ∧ TokAt (chB out0) 0 out0CloseB := by
  have h := FiniteNetBound.gcd_hw_safe_fin_netB 12 18 chB NBn LB nB bwit_ok
    (fun o _ => b_cells o) b_held ⟨yW, yW_good, b_forced⟩
  rw [show Nat.gcd 12 18 = 6 by decide] at h
  exact ⟨h.1, b_out0.1⟩

/-- **On the witness, links bound on both sides take their environment from gate models**:
both pin drivers are the tied cells the netlist names, with pins. -/
theorem bwit_link_env {o : Fin NO} {i o' : Fin NC} (h : opAt o = .link i o') {dr da : DK}
    (hr : reqSrc FU i = some dr) (ha : ackSrc FU o' = some da) :
    ∃ rp ap Es Ea, FLinkSpec DB LB (.lk o) rp ap Es Ea ∧ rp.drv = toCl dr ∧ ap.drv = toCl da ∧
      FTied NBn (toCl dr) ∧ FTied NBn (toCl da) ∧ DB.pins (toCl dr) ≠ [] ∧
      DB.pins (toCl da) ≠ [] := by
  obtain ⟨rp, ap, Es, Ea, S, _, _, e1, e2, t1, t2, p1, p2⟩ :=
    FiniteNetBound.link_env_bound bwit_ok h hr ha
  rw [cell_eq] at e1 e2 t1 t2 p1 p2
  exact ⟨rp, ap, Es, Ea, S, e1, e2, t1, t2, p1, p2⟩

/-! ## 5. Self-audit: the binding rejects Bfin3's relabelled network -/

namespace Rej
open Formal.Cells.FiniteNetWit2 (NW LW nW pR)

/-- **Bfin3's chW network does NOT meet the driver-bound hypothesis.** Its link 194 reads
channel 13, whose request the netlist says is driven by link 193; in Bfin3's network that
pin is driven by channel 13's pinless contract cell. So `FGcdNetOKB` excludes exactly the
re-labelling the audit (P12b) objected to, while `FGcdNetOK` admitted it
(`FiniteNetWit2.fgcdNetOK_chW`). -/
theorem chW_net_not_bound : ¬ FGcdNetOKB Formal.Net.CapNet.Wit.chW NW LW nW := by
  intro H
  have hio : lkIO (opAt ⟨194, by decide⟩) = some (⟨13, by decide⟩, ⟨14, by decide⟩) := by
    decide +kernel
  have hop := lkIO_some.1 hio
  have hr : reqSrc FU ⟨13, by decide⟩ = some (.lk ⟨193, by decide⟩) := by decide +kernel
  obtain ⟨rp, ap, Es, Ea, S, _, _, _, br, _⟩ := H.H_LINK _ _ _ hop
  have hp := S.H_PINS
  change Formal.Cells.FiniteNetWit2.pinsW (.lk ⟨194, by decide⟩) = [rp, ap] at hp
  simp only [Formal.Cells.FiniteNetWit2.pinsW, hio] at hp
  have h1 := (List.cons.inj hp).1
  have e := br _ hr
  rw [← h1] at e
  change Cl.rq _ = Cl.lk _ at e
  cases e

end Rej

end Formal.Cells.BWit
