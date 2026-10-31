import Formal.Cells.FiniteNetWit2Lib

/-!
# Probe Bwit (shard B): checkers for a DRIVER-BOUND gate-level network on event lists

Generalises `FiniteNetWit2Lib` (Bfin3) so that tied cells may drive each other:
* a pin is a wire of ANY delay `w ≥ 1` from its driver's node (`wire_map`: the pin's event
  list is the driver's list shifted by `w - 1`), and its edges are read off the pin list
  (`gE_map`), only at existing edges;
* every cell's edge function may be its node's event list (`getD`), because the specs'
  H_TIMES is now required at existing edges only (`FiniteNetMixed`, 2026-10-31); the
  checker lemmas `celB_spec'`, `stB_spec'`, `orB_spec'`, `linkB_spec'` take H_TIMES at
  existing edges and the pin edges at existing edges.

**Assumed:** nothing (definitions and lemmas). Core Lean only.
-/

namespace Formal.Cells.BWit
open Formal.Cells
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo nt_eq lfind_eq noRevertI_shift)
open Formal.Cells.PipeTimed (Vph lfind lfind_le lfind_spec lfind_min)
open Formal.Cells.LutFbBridge2Env (Wire ε ash)
open Formal.Cells.FiniteRunsWit (sortedB bv_phase bv_low bv_tail all_t cL rst2 wire_shift NB)
open Formal.Net.CapNet.Wit (bv cntLt bv_zero)
open Formal.Cells.AssumeGuaranteeEnds (GPin gE)
open Formal.Cells.AssumeGuaranteeEndsNet (GD)

/-! ## 1. Wires of any delay on event lists -/

def shL (k : Nat) (L : List Nat) : List Nat := L.map (· + k)

theorem cntLt_shL (k : Nat) : ∀ (L : List Nat) (t : Nat), cntLt (shL k L) (t + k) = cntLt L t
  | [], _ => rfl
  | e :: L, t => by
    simp only [shL, List.map_cons, cntLt] at *
    have := cntLt_shL k L t
    simp only [shL] at this
    rw [this]
    by_cases h : e < t
    · rw [if_pos h, if_pos (show e + k < t + k by omega)]
    · rw [if_neg h, if_neg (show ¬ e + k < t + k by omega)]

theorem cntLt_shL_low (k : Nat) : ∀ (L : List Nat) (t : Nat), t ≤ k → cntLt (shL k L) t = 0
  | [], _, _ => rfl
  | e :: L, t, h => by
    simp only [shL, List.map_cons, cntLt] at *
    have := cntLt_shL_low k L t h
    simp only [shL] at this
    rw [this, if_neg (by omega)]

theorem bv_shL (k : Nat) (L : List Nat) (t : Nat) : bv (shL k L) (t + k) = bv L t := by
  unfold bv; rw [cntLt_shL]

theorem bv_shL_low (k : Nat) (L : List Nat) (t : Nat) (h : t ≤ k) : bv (shL k L) t = false := by
  unfold bv; rw [cntLt_shL_low k L t h]; rfl

/-- **A wire of delay `w` from a list node**: the pin is the driver's list shifted by `w - 1`. -/
theorem wire_map (L : List Nat) {w : Nat} (hw : 1 ≤ w) :
    Wire w w (cL L) (bv (shL (w - 1) L)) where
  H_WIN := CElemTiming.transport_winDelay (Nat.le_refl w) (Nat.le_refl w) (fun t => by
    show bv (shL (w - 1) L) (t + w) = bv L (t + 1)
    rw [show t + w = (t + 1) + (w - 1) by omega, bv_shL])
  H_NO_REVERT := noRevertI_shift (fun t ht => by
    show bv (shL (w - 1) L) t = bv L (t - w + 1)
    rw [show t = (t - w + 1) + (w - 1) by omega, bv_shL]
    congr 1; omega)
  H_POS := hw
  H_PWR := fun t ht => bv_shL_low (w - 1) L t (by omega)

/-- A single-point window: `nt` at `[w, w]` from `c` is `nt` at `[1, 1]` from `c + w - 1`. -/
theorem nt_ww (O : Nat → Bool) {w : Nat} (hw : 1 ≤ w) (c : Nat) (v : Bool) :
    nt O w w c v = nt O 1 1 (c + (w - 1)) v := by
  unfold WinFifoCausal.nt
  rw [show c + (w - 1) + 1 = c + w by omega, show c + w + 1 = c + (w - 1) + 1 + 1 by omega]

theorem getD_shL (k : Nat) (L : List Nat) {j : Nat} (hj : j < L.length) :
    (shL k L).getD j 1 = L.getD j 1 + k := by
  simp [shL, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hj,
    List.getElem?_eq_getElem (show j < (L.map (· + k)).length by simpa using hj)]

/-- **A pin's edges from its event list**, for a pin that is a wire of delay `w` from a
driver whose edge function is the driver's list at existing edges. -/
theorem gE_map {ι : Type} {τ : ι → Nat → Nat} {p : GPin ι} {Ld : List Nat} {w : Nat}
    (hw : 1 ≤ w) (hP : p.P = bv (shL (w - 1) Ld)) (hl : p.wl = w) (hh : p.wh = w)
    {j : Nat} (hj : j < Ld.length) (hτ : τ p.drv j = Ld.getD j 1) :
    gE τ p j = ε (bv (shL (w - 1) Ld)) 1 1 (fun j => (shL (w - 1) Ld).getD j 1) j := by
  unfold gE ε
  rw [hP, hl, hh, hτ, nt_ww _ hw]
  show _ = nt _ 1 1 ((shL (w - 1) Ld).getD j 1) _
  rw [getD_shL _ _ hj]

/-! ## 2. The cell checkers with bound drivers (Bfin3's, generalised) -/

open Formal.Cells.FiniteNetWit2
open Formal.Cells.FiniteNet
open Formal.Cells.AssumeGuaranteeEnds (lmax cmax GC2 GC3 GC4 sN)
open Formal.Cells.LutFbBridge2 (CelLaw CelG gc)
open Formal.Cells.AssumeGuaranteeMuxOr (oe cnt cnt_mono)
open Formal.Cells.FiniteRunsWit (bnd)
open Formal.Net.Ops.Gen (genF steerF)
open Formal.Gen Formal.Gen.Cells

theorem celB_spec' {ι : Type} {k : Nat} {G : (Fin k → Bool) → Bool → Bool → Bool}
    {Gf : (Fin k → Bool) → Bool → Bool} (hG : ∀ p q r, G p q r = (!r && Gf p q)) (hL : CelLaw G)
    {D : GD ι} {L : ι → Nat → Prop} {c : ι} {pv : Fin k → GPin ι} {pl : Fin k → List Nat}
    {Ln : List Nat} (hchk : celB Gf pl Ln = true)
    (hO : D.O c = cL Ln) (hq : D.qp c = bv Ln) (hlo : D.lo c = 1) (hhi : D.hi c = 1)
    (hfl : D.fl c = 1) (hfh : D.fh c = 1) (hR : D.R = 2) (hrst : D.rst = rst2)
    (hpins : D.pins c = (List.finRange k).map pv)
    (hP : ∀ i, (pv i).P = bv (pl i))
    (hgE : ∀ i j, j < (pl i).length → gE D.τ (pv i) j = ε (bv (pl i)) 1 1 (fun j => (pl i).getD j 1) j)
    (hLd : ∀ i, L (pv i).drv = fun j => j < (pl i).length) (hLc : L c = fun j => j < Ln.length)
    (hτL : ∀ j, j < Ln.length → D.τ c j = Ln.getD j 1)
    (htm : (List.range Ln.length).all (fun j => Ln.getD j 1 == celT pl Ln j) = true) :
    FCelSpec G D L c pv 1 := by
  simp only [celB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq,
    beq_iff_eq, Bool.not_eq_true'] at hchk
  obtain ⟨⟨⟨⟨⟨⟨hbn, hpl⟩, ⟨i0, _, hi0⟩⟩, ⟨i1, _, h1p⟩⟩, hpw⟩, hlut⟩, hsnd⟩ := hchk
  have hbp : ∀ i, bnd (pl i) = true := fun i => (hpl i (List.mem_finRange i)).1.1
  have hsp : ∀ i, sortedB (pl i) = true := fun i => (hpl i (List.mem_finRange i)).1.2
  have hlp : ∀ i, Ln.length ≤ (pl i).length := fun i => (hpl i (List.mem_finRange i)).2
  have lutA : ∀ t, celQ Gf pl Ln t = true := all_t NB (List.all_eq_true.2 hlut) (fun t ht => by
    unfold celQ
    have e : (fun i => bv (pl i) t) = (fun i => bv (pl i) NB) :=
      funext fun i => bv_tail (hbp i) t ht
    rw [e, bv_tail hbn (t + 2) (by omega), bv_tail hbn t ht, bv_tail hbn (NB + 2) (by omega)]
    have hNB : NB = 768 := rfl
    rw [show decide (t < 2) = false from decide_eq_false (by omega),
      show decide (NB < 2) = false from decide_eq_false (by omega)])
  have hstep : ∀ t, D.O c (t + 1) = G (fun i => (pv i).P t) (D.qp c t) (D.rst t) := by
    intro t
    have := lutA t
    unfold celQ at this
    rw [hO, hq, hrst, hG]
    simp only [beq_iff_eq] at this
    simp only [cL, hP, rst2]
    exact this
  have hcm : ∀ j, j < Ln.length → cmax (fun i => gE D.τ (pv i)) j = celE pl j := by
    intro j hj
    exact lmax_congr j _ (fun i _ => by
      rw [hgE i j (by have := hlp i; omega)]; exact eps_list (hsp i) j (by have := hlp i; omega))
  have hτ : ∀ j, j < Ln.length →
      D.τ c j = nt (D.O c) (D.lo c) (D.hi c) (cmax (fun i => gE D.τ (pv i)) j) (Vph j) := by
    intro j hj
    have e := List.all_eq_true.1 htm j (List.mem_range.2 hj)
    simp only [beq_iff_eq] at e
    rw [hτL j hj, e, hcm j hj, hO, hlo, hhi, nt11]; rfl
  refine { H_PINS := hpins, H_LAW := hL, H_CEL := ?_, H_PWR := ?_, H_TIMES := fun j hj => hτ j (by rw [hLc] at hj; exact hj),
           H_CNT := fun j => ?_, H_RST_EARLY := fun j hj => ?_, H_SND := fun i j hj hl => ?_,
           H_RST_LONG := ?_, H_LAT := ?_ }
  · have sw := step_win hstep
    rw [hlo, hhi, hfl, hfh]
    exact ⟨sw.1, sw.2, by rw [hO, hq]; exact fb_shift Ln, Nat.le_refl 1⟩
  · intro t ht; rw [hhi] at ht
    have : t = 0 := by omega
    subst this; rw [hO]; exact hpw
  · rw [hLc]; simp only [hLd]
    exact ⟨fun h i => by have := hlp i; omega, fun h => by have := h i0; omega⟩
  · rw [hR]
    have hj' : j < Ln.length := by rw [hLc] at hj; exact hj
    have := AssumeGuaranteeEnds.cmax_arr (fun i => gE D.τ (pv i)) i1 j
    have h2 := eps_ge (bv (pl i1)) (fun j => (pl i1).getD j 1) j
    have h3 := getD_ge1 (hsp i1) h1p j
    rw [← hgE i1 j (by have := hlp i1; omega)] at h2
    omega
  · rw [hLc] at hj; rw [hLd] at hl
    rw [hτ j hj, hcm j hj, hO, hlo, hhi, nt11, hgE i (j + 1) hl, eps_list (hsp i) (j + 1) hl]
    have := List.all_eq_true.1 (hsnd j (List.mem_range.2 hj)) i (List.mem_finRange i)
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
      at this
    rcases this with h | h
    · exact absurd hl h
    · unfold celT at h; exact h
  · rw [hhi, hfh, hR]; decide
  · rw [hhi, hfh, hlo]; decide

theorem stB_spec' {ι : Type} {b : Bool} {r : List Nat} {s : Nat → Bool} {tab : List Bool}
    {Ln : List Nat} (hchk : stB b r s tab Ln = true) (hs : ∀ t, NB ≤ t → s t = s NB)
    {D : GD ι} {L : ι → Nat → Prop} {c : ι} {rp : GPin ι}
    (hO : D.O c = cL Ln) (hlo : D.lo c = 1) (hhi : D.hi c = 1)
    (hpins : D.pins c = [rp]) (hP : rp.P = bv r)
    (hgE : ∀ j, j < r.length → gE D.τ rp j = ε (bv r) 1 1 (fun j => r.getD j 1) j)
    (hLd : L rp.drv = fun j => j < r.length) (hLc : L c = fun j => j < Ln.length)
    (hτL : ∀ j, j < Ln.length → D.τ c j = Ln.getD j 1)
    (htm : (List.range Ln.length).all (fun j => Ln.getD j 1 ==
      (if cL Ln (r.getD (sN (κT tab b) j) 1 + 1 + 1) = Vph j then r.getD (sN (κT tab b) j) 1 + 1 + 1
       else r.getD (sN (κT tab b) j) 1 + 1 + 2)) = true) :
    FSteerSpec D L c rp b s (σT tab) (κT tab b) := by
  simp only [stB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hbr, hbn⟩, hsr⟩, htab⟩, htl⟩, hpw⟩, hlut⟩, hsel⟩, hcnt⟩, hcnt2⟩ := hchk
  have hNB : NB = 768 := rfl
  have lutA : ∀ t, stQ b r s Ln t = true := all_t NB (List.all_eq_true.2 hlut) (fun t ht => by
    unfold stQ
    rw [bv_tail hbn (t + 2) (by omega), bv_tail hbr t ht, hs t ht, bv_tail hbn (NB + 2) (by omega)])
  have hstep : ∀ t, D.O c (t + 1) = steerF b (rp.P t, s t) := by
    intro t
    have := lutA t
    unfold stQ at this
    simp only [beq_iff_eq] at this
    rw [hO, hP, LutFbBridge2.steerF_gate]; exact this
  have sw := step_win hstep
  have hτ : ∀ j, j < Ln.length →
      D.τ c j = nt (D.O c) (D.lo c) (D.hi c) (gc (κT tab b) (gE D.τ rp) j) (Vph j) := by
    intro j hj
    have hi := hcnt j (List.mem_range.2 hj)
    have e := List.all_eq_true.1 htm j (List.mem_range.2 hj)
    simp only [beq_iff_eq] at e
    rw [hτL j hj, e, AssumeGuaranteeEnds.gc_sN, hgE _ hi, eps_list hsr _ hi, hO, hlo, hhi, nt11]
  refine { H_PINS := hpins, H_LUT_WIN := ?_, H_NO_REVERT := ?_, H_PWR := ?_, H_TIMES := fun j hj => hτ j (by rw [hLc] at hj; exact hj),
           H_CNT := fun j => ?_, H_DOWN := fun j h => ?_, H_INC := fun j h => ?_,
           H_SEL_STABLE := fun n t h1 h2 h3 => ?_, H_KAPPA := κT_inc htab b,
           H_KAPPA_B := κT_b htab b, H_KAPPA_ALL := κT_all htab b, H_FLOOR := fun j _ => ?_ }
  · rw [hlo, hhi]; exact sw.1
  · rw [hlo, hhi]; exact sw.2
  · intro t ht; rw [hhi] at ht
    have : t = 0 := by omega
    subst this; rw [hO]; exact hpw
  · rw [hLc, hLd]
    show j < Ln.length ↔ sN (κT tab b) j < r.length
    constructor
    · intro h; exact hcnt j (List.mem_range.2 h)
    · intro h
      apply Classical.byContradiction; intro hn
      have := sN_mono (κT_inc htab b) (show Ln.length ≤ j by omega); omega
  · rw [hLd] at h ⊢; show j < r.length; have : j + 1 < r.length := h; omega
  · rw [hLd] at h; have h' : j + 1 < r.length := h
    rw [hgE j (by omega), hgE (j + 1) h', eps_list hsr j (by omega), eps_list hsr (j + 1) h']
    have := FiniteNetWit.sorted_succ r hsr j 1 h'; omega
  · rw [hLd] at h1 h3; have h1' : 2 * n < r.length := h1
    rw [hgE _ h1', eps_list hsr _ h1'] at h2
    have hn : n < (r.length + 1) / 2 := by omega
    have hσ : σT tab n = tab.getD n false := by unfold σT; rw [if_pos (by omega)]
    rw [hσ]
    have hw : ∀ u, u ≤ NB → r.getD (2 * n) 1 + 1 ≤ u → (2 * n + 1 < r.length → u < r.getD (2 * n + 1) 1 + 1) →
        s u = tab.getD n false := by
      intro u hu a1 a2
      have := hsel n (List.mem_range.2 hn) u (List.mem_range.2 (by omega))
      unfold selQ at this
      rw [decide_eq_true a1] at this
      by_cases hB : 2 * n + 1 < r.length
      · rw [decide_eq_true hB, decide_eq_true (a2 hB)] at this
        simpa using this
      · rw [decide_eq_false hB] at this
        simpa using this
    have h3' : 2 * n + 1 < r.length → t < r.getD (2 * n + 1) 1 + 1 := fun h => by
      have := h3 h; rwa [hgE _ h, eps_list hsr _ h] at this
    by_cases ht : t ≤ NB
    · exact hw t ht h2 h3'
    · have hlast : ¬ 2 * n + 1 < r.length := fun h => by
        have := h3' h; have := bnd_getD hbr h; omega
      rw [hs t (by omega)]
      exact hw NB (Nat.le_refl _) (by have := bnd_getD hbr h1'; omega) (fun h => absurd h hlast)
  · rw [hhi, hlo]; omega

theorem orB_spec' {ι : Type} {tab : List Bool} {a0 a1 Ln : List Nat}
    (hchk : orB tab a0 a1 Ln = true) {F : Bool → Bool → Bool} (hF : ∀ x y, F x y = (y || x))
    {D : GD ι} {L : ι → Nat → Prop} {c : ι} {ap : Bool → GPin ι}
    (hO : D.O c = cL Ln) (hlo : D.lo c = 1) (hhi : D.hi c = 1)
    (hpins : D.pins c = [ap false, ap true]) (hP : ∀ b, (ap b).P = bv (lstB a0 a1 b))
    (hgE : ∀ b j, j < (lstB a0 a1 b).length →
      gE D.τ (ap b) j = ε (bv (lstB a0 a1 b)) 1 1 (fun j => (lstB a0 a1 b).getD j 1) j)
    (hLd : ∀ b, L (ap b).drv = fun j => j < (lstB a0 a1 b).length)
    (hLc : L c = fun j => j < Ln.length)
    (hτL : ∀ j, j < Ln.length → D.τ c j = Ln.getD j 1)
    (htm : (List.range Ln.length).all (fun k => Ln.getD k 1 ==
      (if cL Ln (orE tab a0 a1 k + 1) = Vph k then orE tab a0 a1 k + 1 else orE tab a0 a1 k + 2))
      = true) :
    FOrSpec D L c F ap (σT tab) (κT tab) := by
  simp only [orB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', beq_iff_eq] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hb0, hb1⟩, hbn⟩, hs0⟩, hs1⟩, htab⟩, hpw⟩, hlut⟩, hl2⟩, hc0⟩, hc1⟩, hcnt⟩,
    hord⟩ := hchk
  have hNB : NB = 768 := rfl
  have hbB : ∀ b, bnd (lstB a0 a1 b) = true := fun b => by cases b; exact hb0; exact hb1
  have hsB : ∀ b, sortedB (lstB a0 a1 b) = true := fun b => by cases b; exact hs0; exact hs1
  have hcB : ∀ b, (lstB a0 a1 b).length ≤ 2 * cnt (σT tab) b tab.length := fun b => by
    cases b; exact hc0; exact hc1
  have lutA : ∀ t, orQ a0 a1 Ln t = true := all_t NB (List.all_eq_true.2 hlut) (fun t ht => by
    unfold orQ
    rw [bv_tail hbn (t + 2) (by omega), bv_tail hb0 t ht, bv_tail hb1 t ht,
      bv_tail hbn (NB + 2) (by omega)])
  have hstep : ∀ t, D.O c (t + 1) = F ((ap false).P t) ((ap true).P t) := by
    intro t
    have := lutA t
    unfold orQ at this
    simp only [beq_iff_eq] at this
    rw [hO, hP, hP, hF]; exact this
  have sw := step_win hstep
  -- the edge set of the merged sequence
  have lor : ∀ k, Lor (σT tab) (fun b => L (ap b).drv) k ↔ orI tab k < (lstB a0 a1 (σT tab (k / 2))).length := by
    intro k; unfold Lor; show L (ap _).drv _ ↔ _; rw [hLd]; rfl
  have hcnt' : ∀ k, (Lor (σT tab) (fun b => L (ap b).drv) k ↔ k < Ln.length) := by
    intro k
    rw [lor]
    by_cases hk : k < 2 * tab.length
    · have := hcnt k (List.mem_range.2 hk)
      constructor
      · intro h; exact of_decide_eq_true (this ▸ decide_eq_true h)
      · intro h; exact of_decide_eq_true (this.symm ▸ decide_eq_true h)
    · constructor
      · intro h
        have := cnt_mono (σT tab) (σT tab (k / 2)) (show tab.length ≤ k / 2 by omega)
        have := hcB (σT tab (k / 2))
        unfold orI at h; omega
      · intro h; omega
  have hoe : ∀ k, k < Ln.length → oe (σT tab) (fun b => gE D.τ (ap b)) k = orE tab a0 a1 k := by
    intro k hk
    have hl := (lor k).1 ((hcnt' k).2 hk)
    show gE D.τ (ap (σT tab (k / 2))) (orI tab k) = _
    rw [hgE _ _ hl, eps_list (hsB _) _ hl]; rfl
  have hτ : ∀ k, k < Ln.length → D.τ c k =
      nt (D.O c) (D.lo c) (D.hi c) (oe (σT tab) (fun b => gE D.τ (ap b)) k) (Vph k) := by
    intro k hk
    have e := List.all_eq_true.1 htm k (List.mem_range.2 hk)
    simp only [beq_iff_eq] at e
    rw [hτL k hk, e, hoe k hk, hO, hlo, hhi, nt11]
  refine { H_PINS := hpins, H_GATE := hF, H_LUT_WIN := ?_, H_NO_REVERT := ?_, H_PWR := ?_,
           H_TIMES := fun j hj => hτ j (by rw [hLc] at hj; exact hj), H_CNT := fun k => ?_, H_KAPPA := κT_inc htab,
           H_KAPPA_B := κT_b htab, H_KAPPA_ALL := κT_all htab, H_DOWN := fun k h => ?_,
           H_ORD := fun k h => ?_, H_FLOOR := fun k _ => ?_ }
  · rw [hlo, hhi]; exact sw.1
  · rw [hlo, hhi]; exact sw.2
  · intro t ht; rw [hhi] at ht
    have : t = 0 := by omega
    subst this; rw [hO]; exact hpw
  · rw [hLc, hcnt']
  · rw [hcnt'] at h ⊢; omega
  · rw [hcnt'] at h
    rw [hoe k (by omega), hoe (k + 1) h]
    exact hord k (List.mem_range.2 (by omega))
  · rw [hhi, hlo]; omega

open Formal.Cells.AssumeGuaranteeEndsCap (LinkOut)
open Formal.Cells.WinFifoCausal (Stage Timing1 cph τs)
open Formal.Cells.FiniteRunsWit (linkB sndQ rcvQ ρL αL)
open Formal.Net.CapNet.Wit (CD)

theorem linkB_spec' {x y : CD} (h : linkB x y = true) {ι : Type} {D : GD ι} {L : ι → Nat → Prop}
    {c : ι} {rp ap : GPin ι}
    (hO : D.O c = cL y.rq) (hq : D.qp c = bv y.rq) (hlo : D.lo c = 1) (hhi : D.hi c = 1)
    (hfl : D.fl c = 1) (hfh : D.fh c = 1) (hR : D.R = 2) (hrst : D.rst = rst2)
    (hpins : D.pins c = [rp, ap])
    (hrP : rp.P = bv x.rq)
    (hgr : ∀ j, j < x.rq.length → gE D.τ rp j = ε (bv x.rq) 1 1 (fun j => x.rq.getD j 1) j)
    (hRE : ∀ j, D.R ≤ gE D.τ rp j)
    (haP : ap.P = bv y.ak)
    (hga : ∀ j, j < y.ak.length → gE D.τ ap j = ε (bv y.ak) 1 1 (fun j => y.ak.getD j 1) j)
    (hrL : L rp.drv = fun j => j < x.rq.length) (haL : L ap.drv = fun j => j < y.ak.length)
    (hLc : L c = fun j => j < min x.rq.length (y.ak.length + 1))
    (hτL : ∀ j, j < min x.rq.length (y.ak.length + 1) → D.τ c j = y.rq.getD j 1)
    (htm : (List.range (min x.rq.length (y.ak.length + 1))).all
      (fun j => y.rq.getD j 1 == FiniteNetWit.τ1 x y j) = true) :
    FLinkSpec D L c rp ap 3 3 ∧ LinkOut D c x.ch y.ch 3 3 := by
  obtain ⟨hak, sx, sy, c0, r0, St, hsnd, hrcv, d1, d2⟩ := FiniteNetWit.linkB_facts h
  have hτ1 : ∀ j, j < min x.rq.length (y.ak.length + 1) → D.τ c j = FiniteNetWit.τ1 x y j := by
    intro j hj
    have e := List.all_eq_true.1 htm j (List.mem_range.2 hj)
    simp only [beq_iff_eq] at e
    rw [hτL j hj, e]
  have hτ : ∀ j, j < min x.rq.length (y.ak.length + 1) →
      D.τ c j = τs (D.O c) (D.lo c) (D.hi c) (gE D.τ rp) (ash D.R (gE D.τ ap)) j := by
    intro j hj
    rw [hτ1 j hj]
    unfold FiniteNetWit.τ1 τs cph FiniteNetWit.ρc FiniteNetWit.αc
    rw [hO, hlo, hhi, hgr j (by omega)]
    congr 2
    cases j with
    | zero => show 2 = D.R; exact hR.symm
    | succ k => show _ = gE D.τ ap k; rw [hga k (by omega)]; rfl
  refine ⟨{ H_PINS := hpins, H_STAGE := ?_, H_PWR := ?_, H_TIMES := fun j hj => hτ j (by rw [hLc] at hj; exact hj), H_CNT := fun j => ?_,
            H_RST_EARLY := fun j => ?_, H_SND := fun j h1 h2 => ?_, H_RCV := fun j h1 h2 => ?_,
            H_T := ?_ }, ?_⟩
  · rw [hrP, haP, hrst, hO, hq, hlo, hhi, hfl, hfh]; exact St
  · intro t ht; rw [hhi] at ht
    have : t = 0 := by omega
    subst this; rw [hO]; exact c0
  · rw [hLc, hrL, haL]; exact (lnL_fin _ _ j).symm
  · exact hRE j
  · rw [hLc] at h1; rw [hrL] at h2
    have hl : j < min x.rq.length (y.ak.length + 1) := h1
    have hr : j + 1 < x.rq.length := h2
    have q := hsnd j (by omega)
    simp only [sndQ, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, Bool.and_eq_true, beq_iff_eq] at q
    rcases q with (q | q) | ⟨q1, q2⟩
    · exact absurd hr q
    · exact absurd (show j ≤ y.ak.length by omega) q
    · obtain ⟨e1, _⟩ := FiniteNetWit.link_edges h j (by omega) (by omega) q1
      rw [hτ1 j hl, e1, hgr (j + 1) hr, eps_list sx (j + 1) hr]
      exact q2
  · rw [hLc] at h1; rw [haL] at h2
    have hl : j < min x.rq.length (y.ak.length + 1) := h1
    have ha : j < y.ak.length := h2
    have q := hrcv j ha
    simp only [rcvQ, decide_eq_true_eq, Bool.or_eq_true, Bool.not_eq_true',
      decide_eq_false_iff_not, Bool.and_eq_true, beq_iff_eq] at q
    rcases q with (q | q) | ⟨q1, q2⟩
    · exact absurd ha q
    · exact absurd (show j < x.rq.length by omega) q
    · obtain ⟨e1, _⟩ := FiniteNetWit.link_edges h j (by omega) (by omega) q1
      rw [hτ1 j hl, e1, hga j ha, eps_list sy j ha]
      rw [FiniteRunsWit.αL_succ, FiniteNetWit.getD_irrel y.ak j 0 1 ha] at q2; exact q2
  · rw [hlo, hhi, hfh, hR]; exact ⟨by decide, by decide, by decide⟩
  · refine ⟨1, 1, 1, 1, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · show Wire 1 1 (D.O c) (bv x.ak); rw [hO, hak]; exact wire_shift y.rq
    · show Wire 1 1 (D.O c) (bv y.rq); rw [hO]; exact wire_shift y.rq
    · rw [hR]; decide
    · rw [hR]; decide
    · rw [hhi, hlo]; decide
    · rw [hhi, hlo]; decide
    · intro t ht; rw [hO] at ht; exact d1 t ht
    · intro t ht; rw [hO] at ht; exact d2 t ht

end Formal.Cells.BWit
