import Formal.Cells.FiniteNetWit2Chk

/-!
# Probe Bfin3 (shard B): a joint witness of `FGcdNetOK` on C's terminating gcd run

Note: `formal/notes/B-finite-net-wit2.md`. Bfin2's `FiniteNetMixed.gcd_hw_safe_fin_net`
(one gate-level network of gcd_hw, links + forks N ≤ 4 + 2-input joins + steer branches +
steer acknowledge ORs gate-modelled, finite edge counts) had no witness. Here: a network
`NW` over C's run `chW` (a = 12, b = 18, quiet after 476 ticks) that meets `FGcdNetOK`, with
every one of its 377 gate-modelled cells' node trace SIMULATED with the REAL LUT (unit LUT
delay, unit feedback and pin wires) on chW's channel traces and kernel-checked.

## The network `NW`

* one contract cell per channel signal (`rq c`, `ak c`): node = the signal one tick earlier,
  no pins (Bfin2's END cells); every pin of the network is a channel signal driven by one
  of them through a unit wire;
* the 175 links (`lk o`): node = Bfin's controller node (the output request one tick
  earlier), pins the input request and the output acknowledge (Bfin's `linkB`);
* the 41 fork acknowledge C-elements (`fa o`, N = 2, 3, 4: REAL `bd_c2`, `bd_ctree` N = 3,
  `bd_c4`), the 47 join request C-elements (`jr o`), the 76 steer branches (`sb o b`, REAL
  `bd_steer` `u`, select = bit 0 of the input bus), the 38 steer acknowledge ORs (`ao o`, REAL
  `uack`, pins the two branch acknowledges): pins the channel traces, node SIMULATED
  (`/tmp/claude-0/probes/Bfin3/gen.py`, untrusted; `FiniteNetWit2Chk` checks every LUT tick,
  H_SND / H_SEL_STABLE / H_ORD / H_CNT, by `decide +kernel`).

## Assumed / proved / NOT covered

**Proved:** `fgcdNetOK_chW : FGcdNetOK chW NW LW nW`; `gcd_hw_fin_net_witness`: chW meets
ALL hypotheses of `gcd_hw_safe_fin_net` jointly (H_OTHER, H_BUNDLE, H_CM_FORCED from C) and
out0 latches a token carrying 6; `gcd_hw_fin_net_consistent` applies the theorem.

**NOT covered (degenerate parts, stated):** (i) the gate-modelled fork / join / steer / OR
nodes DRIVE NOTHING in `NW`: `FGcdNetOK` ties their PINS to the channel traces but not their
NODES, and on C's unit-delay run they cannot drive the channel signals (C's gate takes one
tick from channel to channel; B's LUT ≥ 1 plus wire ≥ 1 take two; see
`FiniteNetSrc.chW_steer_unwired` for the formal obstruction). Every channel signal is driven by
a contract cell whose truncated contract holds because its conclusion does; so no
gate-modelled cell's guarantee feeds another's assumption. (ii) unit delays: every window
met at width 0. (iii) `R = 2` chosen. Core Lean only.
-/

namespace Formal.Cells.FiniteNetWit2
open Formal.Cells
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe
open Formal.Net.CapNet.Wit (CD cdA chW nv bv)
open Formal.Cells.WinFifoCausal (nt τs)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.LutFbBridge2Env (Wire ε ash isLink)
open Formal.Cells.LutFbBridge2 (gc)
open Formal.Cells.FiniteRunsWit (sortedB cL rst2 wire_shift)
open Formal.Cells.AssumeGuaranteeEnds (GPin gE lmax cmax GC2 GC3 GC4)
open Formal.Cells.AssumeGuaranteeEndsNet (GD)
open Formal.Cells.AssumeGuaranteeEndsCap (GcdNet forkOuts joinIns steerIn d0)
open Formal.Cells.AssumeGuaranteeMuxOr (oe)
open Formal.Cells.FiniteNet
open Formal.Net.Ops.Gen (genF)
open Formal.Gen Formal.Gen.Cells

/-! ## 1. The network -/

inductive Cl
  | lk (o : Fin NO)
  | fa (o : Fin NO)
  | jr (o : Fin NO)
  | sb (o : Fin NO) (b : Bool)
  | ao (o : Fin NO)
  | rq (c : Fin NC)
  | ak (c : Fin NC)

def pR (c : Fin NC) : GPin Cl := ⟨.rq c, bv (cdA c).rq, 1, 1, fun _ => 0⟩
def pA (c : Fin NC) : GPin Cl := ⟨.ak c, bv (cdA c).ak, 1, 1, fun _ => 0⟩
def apO (f t : Fin NC) (b : Bool) : GPin Cl := if b then pA t else pA f

def lkIO : K NC → Option (Fin NC × Fin NC)
  | .link i o => some (i, o)
  | _ => none

def faOK (o : Fin NO) : Bool :=
  match forkOuts (opAt o) with
  | some os => decide (2 ≤ os.length ∧ os.length ≤ 4)
  | none => false

def jrOK (o : Fin NO) : Bool :=
  match joinIns (opAt o) with
  | some ins => ins.length == 2
  | none => false

def faPins (o : Fin NO) : List (GPin Cl) :=
  match forkOuts (opAt o) with
  | some os => os.map pA
  | none => []

def jrPins (o : Fin NO) : List (GPin Cl) :=
  match joinIns (opAt o) with
  | some ins => ins.map pR
  | none => []

def tabO (o : Fin NO) : List Bool := tabL.getD o.val []

/-- Every cell's node, as an event list (`cL`). -/
def lst : Cl → List Nat
  | .lk o => match lkIO (opAt o) with
    | some (_, o') => (cdA o').rq
    | none => []
  | .fa o => faL.getD o.val []
  | .jr o => jrL.getD o.val []
  | .sb o b => (if b then sbTL else sbFL).getD o.val []
  | .ao o => aoL.getD o.val []
  | .rq c => (cdA c).rq
  | .ak c => (cdA c).ak

def τC (c : Cl) (j : Nat) : Nat := (lst c).getD j 1

def τW : Cl → Nat → Nat
  | .lk o => match lkIO (opAt o) with
    | some (i, o') => τs (cL (cdA o').rq) 1 1 (gE τC (pR i)) (ash 2 (gE τC (pA o')))
    | none => τC (.lk o)
  | .fa o => if faOK o then fun j => nt (cL (lst (.fa o))) 1 1 (lmax (gE τC) j (faPins o)) (Vph j)
    else τC (.fa o)
  | .jr o => if jrOK o then fun j => nt (cL (lst (.jr o))) 1 1 (lmax (gE τC) j (jrPins o)) (Vph j)
    else τC (.jr o)
  | .sb o b => match stTF (opAt o) with
    | some (j, _, _) => fun k => nt (cL (lst (.sb o b))) 1 1 (gc (κT (tabO o) b) (gE τC (pR j)) k)
        (Vph k)
    | none => τC (.sb o b)
  | .ao o => match stTF (opAt o) with
    | some (_, t, f) => fun k => nt (cL (lst (.ao o))) 1 1
        (oe (σT (tabO o)) (fun b => gE τC (apO f t b)) k) (Vph k)
    | none => τC (.ao o)
  | .rq c => τC (.rq c)
  | .ak c => τC (.ak c)

def pinsW : Cl → List (GPin Cl)
  | .lk o => match lkIO (opAt o) with
    | some (i, o') => [pR i, pA o']
    | none => []
  | .fa o => faPins o
  | .jr o => jrPins o
  | .sb o _ => match stTF (opAt o) with
    | some (j, _, _) => [pR j]
    | none => []
  | .ao o => match stTF (opAt o) with
    | some (_, t, f) => [apO f t false, apO f t true]
    | none => []
  | .rq _ => []
  | .ak _ => []

def nW : Cl → Nat
  | .lk o => match lkIO (opAt o) with
    | some (i, o') => min (cdA i).rq.length ((cdA o').ak.length + 1)
    | none => 0
  | c => (lst c).length

def DW : GD Cl where
  O c := cL (lst c)
  τ := τW
  lo _ := 1
  hi _ := 1
  fl _ := 1
  fh _ := 1
  qp c := bv (lst c)
  rst := rst2
  R := 2
  pins := pinsW

def NW : FGcdNet where
  ι := Cl
  D := DW
  lk := .lk
  fa := .fa
  jr := .jr
  sb := .sb
  ao := .ao

def LW (c : Cl) (j : Nat) : Prop := j < nW c

/-! ## 2. Small facts about the network -/

theorem lkIO_some {k : K NC} {i o : Fin NC} : lkIO k = some (i, o) ↔ k = .link i o := by
  cases k <;> simp [lkIO]

theorem stTF_of {k : K NC} {j : Fin NC} (h : steerIn k = some j) :
    ∃ t f, stTF k = some (j, t, f) := by
  cases k <;> simp_all [steerIn, stTF]

theorem stTF_steer {k : K NC} {j t f : Fin NC} (h : stTF k = some (j, t, f)) :
    steerIn k = some j := by
  cases k <;> simp_all [steerIn, stTF]

theorem pin_form (c : Cl) (p : GPin Cl) (hp : p ∈ pinsW c) : ∃ x, p = pR x ∨ p = pA x := by
  cases c with
  | lk o =>
    revert hp; simp only [pinsW]; split
    · intro hp; simp at hp; rcases hp with rfl | rfl
      · exact ⟨_, Or.inl rfl⟩
      · exact ⟨_, Or.inr rfl⟩
    · intro hp; simp at hp
  | fa o =>
    revert hp; simp only [pinsW, faPins]; split
    · intro hp; obtain ⟨x, _, rfl⟩ := List.mem_map.1 hp; exact ⟨x, Or.inr rfl⟩
    · intro hp; simp at hp
  | jr o =>
    revert hp; simp only [pinsW, jrPins]; split
    · intro hp; obtain ⟨x, _, rfl⟩ := List.mem_map.1 hp; exact ⟨x, Or.inl rfl⟩
    · intro hp; simp at hp
  | sb o b =>
    revert hp; simp only [pinsW]; split
    · intro hp; simp at hp; subst hp; exact ⟨_, Or.inl rfl⟩
    · intro hp; simp at hp
  | ao o =>
    revert hp; simp only [pinsW]; split
    · intro hp; simp [apO] at hp; rcases hp with rfl | rfl
      · exact ⟨_, Or.inr rfl⟩
      · exact ⟨_, Or.inr rfl⟩
    · intro hp; simp at hp
  | rq c => simp [pinsW] at hp
  | ak c => simp [pinsW] at hp

theorem fnetW : FNetW DW LW where
  H_RST _ := rfl
  H_WIRE c p hp := by
    obtain ⟨x, rfl | rfl⟩ := pin_form c p hp
    · exact wire_shift (cdA x).rq
    · exact wire_shift (cdA x).ak
  H_LUT_POS _ := Nat.le_refl 1
  H_FLOOR c p hp j _ := by
    obtain ⟨x, rfl | rfl⟩ := pin_form c p hp
    · show 1 ≤ _ + 1; omega
    · show 1 ≤ _ + 1; omega

/-- A cell whose node is its event list with the list's edges: its truncated contract holds
(its conclusion does). -/
theorem rest_ok (c : Cl) (hτ : τW c = τC c) (hn : nW c = (lst c).length)
    (hs : sortedB (lst c) = true) : FCellOK DW LW c := by
  intro T _
  have := FiniteNetWit.cL_gph hs (T + 1)
  show GPhT (cL (lst c)) (τW c) (fun j => j < nW c) (T + 1)
  rw [hτ, hn]; exact this

/-! ## 3. The cell specs -/

section specs

theorem lk_spec {o : Fin NO} {i o' : Fin NC} (h : opAt o = .link i o') :
    FLinkSpec DW LW (.lk o) (pR i) (pA o') 3 3 ∧
      AssumeGuaranteeEndsCap.LinkOut DW (.lk o) (cdA i).ch (cdA o').ch 3 3 := by
  have hb : FiniteRunsWit.linkB (cdA i) (cdA o') = true := by
    have := List.all_eq_true.mp FiniteRunsWit.lk_all _ (getD_mem (o := o))
    rw [h] at this; exact this
  have hio : lkIO (opAt o) = some (i, o') := lkIO_some.2 h
  have hl : lst (.lk o) = (cdA o').rq := by simp only [lst, hio]
  refine linkB_spec hb (by show cL (lst _) = _; rw [hl]) (by show bv (lst _) = _; rw [hl])
    rfl rfl rfl rfl rfl rfl (by show pinsW (Cl.lk o) = [pR i, pA o']; simp only [pinsW, hio]) rfl rfl rfl rfl rfl rfl
    rfl rfl rfl rfl (by funext j; show (j < nW (Cl.lk o)) = _; simp only [nW, hio]) (fun j => ?_)
  show τW (.lk o) j = _
  simp only [τW, hio]
  show _ = τs (cL (lst (.lk o))) 1 1 _ _ j
  rw [hl]; rfl

theorem gE_pA (c : Fin NC) : gE DW.τ (pA c) = gE τC (pA c) := rfl
theorem gE_pR (c : Fin NC) : gE DW.τ (pR c) = gE τC (pR c) := rfl

theorem lmax_pins {k : Nat} (os : List (Fin NC)) (hk : os.length = k) (P : Fin NC → GPin Cl)
    (hP : ∀ c, gE DW.τ (P c) = gE τC (P c)) (j : Nat) :
    cmax (fun i : Fin k => gE DW.τ (P (os.getD i.val d0))) j = lmax (gE τC) j (os.map P) := by
  unfold cmax
  rw [lmax_map (gE DW.τ) (fun i : Fin k => P (os.getD i.val d0)) j,
    show (List.finRange k).map (fun i : Fin k => P (os.getD i.val d0)) = os.map P by
      have := congrArg (List.map P) (finRange_getD' os d0 k hk); rw [List.map_map] at this
      exact this]
  exact lmax_congr j _ (fun p hp => by
    obtain ⟨c, _, rfl⟩ := List.mem_map.1 hp; rw [hP])

theorem fa_spec {o : Fin NO} {os : List (Fin NC)} (hos : forkOuts (opAt o) = some os) {k : Nat}
    (hk : os.length = k) (h2 : 2 ≤ k) (h4 : k ≤ 4) {G : (Fin k → Bool) → Bool → Bool → Bool}
    {Gf : (Fin k → Bool) → Bool → Bool} (hG : ∀ p q r, G p q r = (!r && Gf p q))
    (hL : LutFbBridge2.CelLaw G)
    (hchk : celB Gf (fun i : Fin k => (cdA (os.getD i.val d0)).ak) (lst (.fa o)) = true) :
    FCelSpec G DW LW (.fa o) (fun i : Fin k => pA (os.getD i.val d0)) 1 := by
  have hok : faOK o = true := by
    unfold faOK; rw [hos]; simp; omega
  refine celB_spec hG hL hchk rfl rfl rfl rfl rfl rfl rfl rfl ?_ (fun _ => rfl) (fun _ => rfl)
    (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl (fun j => ?_)
  · show faPins o = _
    unfold faPins; rw [hos]
    have := congrArg (List.map pA) (finRange_getD' os d0 k hk); rw [List.map_map] at this
    exact this.symm
  · show τW (.fa o) j = nt (cL (lst (.fa o))) 1 1 _ (Vph j)
    simp only [τW, hok, ite_true]
    rw [lmax_pins os hk pA gE_pA j]
    unfold faPins; rw [hos]

theorem jr_spec {o : Fin NO} {ins : List (Fin NC)} (hos : joinIns (opAt o) = some ins)
    (hk : ins.length = 2)
    (hchk : celB Gf2 (fun i : Fin 2 => (cdA (ins.getD i.val d0)).rq) (lst (.jr o)) = true) :
    FCelSpec GC2 DW LW (.jr o) (fun i : Fin 2 => pR (ins.getD i.val d0)) 1 := by
  have hok : jrOK o = true := by
    unfold jrOK; rw [hos]; simp [hk]
  refine celB_spec (fun p q r => ?_) AssumeGuaranteeEnds.lawC2 hchk rfl rfl rfl rfl rfl rfl rfl
    rfl ?_ (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) (fun _ => rfl) rfl
    (fun j => ?_)
  · unfold GC2; rw [AssumeGuaranteeEnds.c2_gen]; rfl
  · show jrPins o = _
    unfold jrPins; rw [hos]
    have := congrArg (List.map pR) (finRange_getD' ins d0 2 hk); rw [List.map_map] at this
    exact this.symm
  · show τW (.jr o) j = nt (cL (lst (.jr o))) 1 1 _ (Vph j)
    simp only [τW, hok, ite_true]
    rw [lmax_pins ins hk pR gE_pR j]
    unfold jrPins; rw [hos]


theorem sb_spec {o : Fin NO} {j t f : Fin NC} (h : stTF (opAt o) = some (j, t, f)) (b : Bool) :
    FSteerSpec DW LW (.sb o b) (pR j) b (selS j) (σT (tabO o)) (κT (tabO o) b) := by
  have hc := (chk_of o).2.2.1
  unfold stChk at hc; rw [h] at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨⟨hT, hF⟩, _⟩, hbd⟩ := hc
  have hs : ∀ u, FiniteRunsWit.NB ≤ u → selS j u = selS j FiniteRunsWit.NB := fun u hu => by
    unfold selS; rw [FiniteRunsWit.nv_tail (cdA j).d0 hbd u hu]
  have hchk : stB b (cdA j).rq (selS j) (tabO o) (lst (.sb o b)) = true := by
    cases b
    · exact hF
    · exact hT
  refine stB_spec hchk hs rfl rfl rfl ?_ rfl rfl rfl rfl rfl rfl (fun k => ?_)
  · show pinsW (Cl.sb o b) = [pR j]; simp only [pinsW, h]
  · show τW (.sb o b) k = _
    simp only [τW, h]; rfl

theorem ao_spec {o : Fin NO} {j t f : Fin NC} (h : stTF (opAt o) = some (j, t, f)) :
    FOrSpec DW LW (.ao o) (fun a0 a1 => genF bd_steer "uack" .O ["ack0", "ack1"] [a0, a1])
      (apO f t) (σT (tabO o)) (κT (tabO o)) := by
  have hc := (chk_of o).2.2.1
  unfold stChk at hc; rw [h] at hc
  simp only [Bool.and_eq_true] at hc
  obtain ⟨⟨_, hO⟩, _⟩ := hc
  refine orB_spec (a0 := (cdA f).ak) (a1 := (cdA t).ak) hO AssumeGuaranteeMuxOr.uack_gate rfl rfl rfl
    ?_ (fun b => by cases b <;> rfl) (fun b => by cases b <;> rfl) (fun b => by cases b <;> rfl)
    (fun b => by cases b <;> rfl) (fun b => by cases b <;> rfl) rfl (fun k => ?_)
  · show pinsW (Cl.ao o) = _; simp only [pinsW, h]
  · show τW (.ao o) k = _
    simp only [τW, h]
    have : (fun b => gE τC (apO f t b)) = (fun b => gE DW.τ (apO f t b)) := by
      funext b; cases b <;> rfl
    rw [this]; rfl

end specs

/-! ## 4. `FGcdNetOK` on `chW` -/

theorem tied_lk {o : Fin NO} {i o' : Fin NC} (h : lkIO (opAt o) = some (i, o')) :
    FTied NW (.lk o) := Or.inl ⟨o, i, o', lkIO_some.1 h, rfl⟩

theorem tied_fa {o : Fin NO} (h : faOK o = true) : FTied NW (.fa o) := by
  unfold faOK at h; split at h
  · rename_i os hos
    simp only [decide_eq_true_eq] at h
    exact Or.inr (Or.inl ⟨o, os, hos, h.1, h.2, rfl⟩)
  · cases h

theorem tied_jr {o : Fin NO} (h : jrOK o = true) : FTied NW (.jr o) := by
  unfold jrOK at h; split at h
  · rename_i ins hos
    simp only [beq_iff_eq] at h
    exact Or.inr (Or.inr (Or.inl ⟨o, ins, hos, h, rfl⟩))
  · cases h

theorem h_rest (c : Cl) (hc : ¬ FTied NW c) : FCellOK DW LW c := by
  cases c with
  | lk o =>
    cases hio : lkIO (opAt o) with
    | some p => exact absurd (tied_lk (o := o) (i := p.1) (o' := p.2) hio) hc
    | none =>
      exact rest_ok _ (by simp only [τW, hio]) (by simp only [nW, lst, hio]; rfl)
        (by simp only [lst, hio]; rfl)
  | fa o =>
    cases hf : faOK o with
    | true => exact absurd (tied_fa hf) hc
    | false =>
      have := (chk_of o).2.2.2
      simp only [srtChk, Bool.and_eq_true] at this
      exact rest_ok _ (by simp only [τW, hf]; rfl) rfl this.1.1.1.1
  | jr o =>
    cases hf : jrOK o with
    | true => exact absurd (tied_jr hf) hc
    | false =>
      have := (chk_of o).2.2.2
      simp only [srtChk, Bool.and_eq_true] at this
      exact rest_ok _ (by simp only [τW, hf]; rfl) rfl this.1.1.1.2
  | sb o b =>
    cases hs : stTF (opAt o) with
    | some p =>
      exact absurd (Or.inr (Or.inr (Or.inr (Or.inl ⟨o, p.1, b, stTF_steer hs, rfl⟩)))) hc
    | none =>
      have := (chk_of o).2.2.2
      simp only [srtChk, Bool.and_eq_true] at this
      refine rest_ok _ (by simp only [τW, hs]) rfl ?_
      cases b
      · exact this.1.2
      · exact this.1.1.2
  | ao o =>
    cases hs : stTF (opAt o) with
    | some p =>
      exact absurd (Or.inr (Or.inr (Or.inr (Or.inr ⟨o, p.1, stTF_steer hs, rfl⟩)))) hc
    | none =>
      have := (chk_of o).2.2.2
      simp only [srtChk, Bool.and_eq_true] at this
      exact rest_ok _ (by simp only [τW, hs]) rfl this.2
  | rq c => exact rest_ok _ rfl rfl (ch_sorted c).1
  | ak c => exact rest_ok _ rfl rfl (ch_sorted c).2

theorem h_fork (o : Fin NO) (os : List (Fin NC)) (hos : forkOuts (opAt o) = some os)
    (h2 : 2 ≤ os.length) (h4 : os.length ≤ 4) :
    FCelTie DW LW (.fa o) os (fun c => (chW c).ack) := by
  have hc := (chk_of o).1
  unfold faChk at hc; rw [hos] at hc; dsimp only at hc
  unfold celChk at hc
  rcases (show os.length = 2 ∨ os.length = 3 ∨ os.length = 4 by omega) with e | e | e
  · rw [if_pos e] at hc
    refine Or.inl ⟨e, _, 1, fa_spec hos e (by omega) (by omega) (fun p q r => ?_)
      AssumeGuaranteeEnds.lawC2 hc, fun _ => rfl⟩
    unfold GC2; rw [AssumeGuaranteeEnds.c2_gen]; rfl
  · rw [if_neg (by omega), if_pos e] at hc
    refine Or.inr (Or.inl ⟨e, _, 1, fa_spec hos e (by omega) (by omega) (fun p q r => ?_)
      AssumeGuaranteeEnds.lawC3 hc, fun _ => rfl⟩)
    unfold GC3; rw [AssumeGuaranteeEnds.c3_gen]; rfl
  · rw [if_neg (by omega), if_neg (by omega), if_pos e] at hc
    refine Or.inr (Or.inr ⟨e, _, 1, fa_spec hos e (by omega) (by omega) (fun p q r => ?_)
      AssumeGuaranteeEnds.lawC4 hc, fun _ => rfl⟩)
    unfold GC4; rw [AssumeGuaranteeEnds.c4_gen]; rfl

theorem h_join (o : Fin NO) (ins : List (Fin NC)) (hos : joinIns (opAt o) = some ins)
    (h2 : ins.length = 2) : FCelTie DW LW (.jr o) ins (fun c => (chW c).req) := by
  have hc := (chk_of o).2.1
  unfold jrChk at hc; rw [hos] at hc; dsimp only at hc; rw [if_pos h2] at hc
  unfold celChk at hc; rw [if_pos h2] at hc
  exact Or.inl ⟨h2, _, 1, jr_spec hos h2 hc, fun _ => rfl⟩

/-- **`chW` meets `FGcdNetOK`** with the network `NW`. -/
theorem fgcdNetOK_chW : FGcdNetOK chW NW LW nW where
  NW := fnetW
  H_FIN _ _ := Iff.rfl
  H_LINK o i o' h := ⟨pR i, pA o', 3, 3, (lk_spec h).1, rfl, rfl, (lk_spec h).2⟩
  H_FORK := h_fork
  H_JOIN := h_join
  H_STEER o j h b := by
    obtain ⟨t, f, h'⟩ := stTF_of h
    exact ⟨pR j, selS j, σT (tabO o), κT (tabO o) b, sb_spec h' b, rfl⟩
  H_SOR o j h := by
    obtain ⟨t, f, h'⟩ := stTF_of h
    exact ⟨apO f t, σT (tabO o), κT (tabO o), ao_spec h'⟩
  H_REST := h_rest

open Formal.Net.CapNet.Wit (w_cells w_held w_start_once yW yW_good yW_walk w_out0 out0Close
  gcd_12_18)

/-- **Joint non-vacuity of `FiniteNetMixed.gcd_hw_safe_fin_net`** on C's terminating run
(a = 12, b = 18): a gate-level network with every link, fork N ≤ 4, 2-input join, steer
branch and steer acknowledge OR gate-modelled (node traces simulated with the REAL LUTs and
kernel-checked) meets `FGcdNetOK` together with C's H_OTHER, H_BUNDLE, H_CM_FORCED, and out0
latches a token carrying 6. -/
theorem gcd_hw_fin_net_witness :
    ∃ (ch : Fin NC → Chan) (N : FGcdNet) (L : N.ι → Nat → Prop) (n : N.ι → Nat),
      FGcdNetOK ch N L n ∧
      (∀ o : Fin NO, isLink (opAt o) = false → Cell ch (srcV 12 18) (opAt o)) ∧
      (∀ c, Held (ch c)) ∧
      (∃ y, Good 12 18 y ∧ ∀ o : Fin NO, Forced ch (omOf 12 18 y) (opAt o)) ∧
      (∃ k e, TokAt (ch out0) k e ∧ (ch out0).dat e = 6) :=
  ⟨chW, NW, LW, nW, fgcdNetOK_chW, fun o _ => w_cells o, w_held,
    ⟨yW, yW_good, gcd_hw_forced 12 18 chW yW yW_good w_cells w_held w_start_once yW_walk⟩,
    ⟨0, out0Close, w_out0⟩⟩

/-- The gate-level network theorem applied to the witness gives the value it latches. -/
theorem gcd_hw_fin_net_consistent :
    (∀ k e, TokAt (chW out0) k e → (chW out0).dat e = 6) ∧ TokAt (chW out0) 0 out0Close := by
  have h := gcd_hw_safe_fin_net 12 18 chW NW LW nW fgcdNetOK_chW (fun o _ => w_cells o)
    w_held ⟨yW, yW_good, gcd_hw_forced 12 18 chW yW yW_good w_cells w_held w_start_once yW_walk⟩
  rw [gcd_12_18] at h
  exact ⟨h.1, w_out0.1⟩

end Formal.Cells.FiniteNetWit2
