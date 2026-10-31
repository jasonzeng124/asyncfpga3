import Formal.Cells.FiniteNetMixed
import Formal.Cells.FiniteNetWit

/-!
# Probe Bfin3 (shard B): kernel checkers for the gate-modelled cells of `FGcdNetOK`

Note: `formal/notes/B-finite-net-wit2.md`. Boolean checkers, with proved soundness, for the
cells that `FiniteNetMixed.FGcdNetOK` gate-models besides the links (Bfin's `linkB`): an
`n`-pin C-element (`celB`, the REAL `bd_c2`/`bd_ctree` N = 3/`bd_c4` LUTs via `c2_gen`,
`c3_gen`, `c4_gen`), a steer branch (`stB`, the REAL `bd_steer` `u`) and the steer
acknowledge OR (`orB`, the REAL `bd_steer` `uack`), all at unit LUT delay with unit wires,
on event-list traces (`FiniteRunsWit.cL`/`bv`). A finite token table is extended to a total
token enumeration (`σT`, `κT`: the table, then alternating tokens past its end).

## Assumed / proved / NOT covered

**Proved:** `nt11` (a unit window's edge in closed form), `step_win` (a one-tick transport
is `Win 1 1` with H_NO_REVERT), `σT`/`κT` meet H_KAPPA, H_KAPPA_B, H_KAPPA_ALL from a
decided table check (`tabOK`), and the soundness lemmas `celB_spec`, `stB_spec`, `orB_spec`:
a passing checker gives the fields of `FCelSpec`, `FSteerSpec`, `FOrSpec` on any `GD` whose
cell and pin traces are the checked event lists.

**Assumed:** nothing (definitions and lemmas). **NOT covered:** the data and the network:
`FiniteNetWit2Data`, `FiniteNetWit2`. Core Lean only.
-/

namespace Formal.Cells.FiniteNetWit2
open Formal.Cells
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo nt_eq lfind_eq noRevertI_shift)
open Formal.Cells.PipeTimed (Vph lfind lfind_le lfind_spec lfind_min)
open Formal.Cells.LutFbBridge2Env (Wire ε ash)
open Formal.Cells.FiniteRunsWit (sortedB bv_phase bv_low bv_tail all_t cL rst2 wire_shift NB)
open Formal.Net.CapNet.Wit (bv cntLt bv_zero)

/-! ## 1. Small facts -/

theorem nt11 (O : Nat → Bool) (c : Nat) (v : Bool) :
    nt O 1 1 c v = if O (c + 1) = v then c + 1 else c + 2 := by
  by_cases h : O (c + 1) = v
  · rw [if_pos h]; exact nt_eq O (Nat.le_refl 1) h
  · rw [if_neg h]
    have hle := lfind_le (fun t => decide (c + 1 ≤ t) && (O t == v)) (c + 1 + 1)
    rcases Nat.lt_or_ge (lfind (fun t => decide (c + 1 ≤ t) && (O t == v)) (c + 1 + 1))
      (c + 1 + 1) with hl | hl
    · have hs := lfind_spec _ _ hl
      simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hs
      have : lfind (fun t => decide (c + 1 ≤ t) && (O t == v)) (c + 1 + 1) = c + 1 := by omega
      rw [this] at hs; exact absurd hs.2 h
    · show lfind _ _ = _; omega

theorem step_win {F O : Nat → Bool} (h : ∀ t, O (t + 1) = F t) : Win 1 1 F O ∧ NoRevertI 1 1 F O :=
  ⟨CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1) h,
    noRevertI_shift (fun t ht => by have := h (t - 1); rw [Nat.sub_add_cancel ht] at this; exact this)⟩

/-- A node read off an event list is the list's pin one tick earlier; its feedback pin
(the list itself, one wire tick) is a `WinDelay 1 1`. -/
theorem fb_shift (L : List Nat) : CElemTiming.WinDelay 1 1 (cL L) (bv L) :=
  CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1) (fun _ => rfl)

theorem getD_ge1 {L : List Nat} (hs : sortedB L = true) (h0 : 1 ≤ L.getD 0 1) (j : Nat) :
    1 ≤ L.getD j 1 := FiniteNetWit.sorted_ge1 L hs h0 j

/-- The pin edge of an event-list pin driven by its own node (`cL L` through a unit wire). -/
theorem eps_list {L : List Nat} (hs : sortedB L = true) (j : Nat) (hj : j < L.length) :
    ε (bv L) 1 1 (fun j => L.getD j 1) j = L.getD j 1 + 1 := FiniteNetWit.eps_bv hs j hj

theorem eps_ge (P : Nat → Bool) (τ : Nat → Nat) (j : Nat) : τ j + 1 ≤ ε P 1 1 τ j :=
  nt_lo P (τ j) (Vph j) (Nat.le_refl 1)

/-! ## 2. Token tables -/

/-- The token selects: the table, then alternating past its end. -/
def σT (tab : List Bool) (n : Nat) : Bool := if n < tab.length then tab.getD n false else n % 2 == 1

/-- The tokens of the table steered to `b`. -/
def idxT (tab : List Bool) (b : Bool) : List Nat :=
  (List.range tab.length).filter (fun n => tab.getD n false == b)

/-- The `m`-th token steered to `b`. -/
def κT (tab : List Bool) (b : Bool) (m : Nat) : Nat :=
  if m < (idxT tab b).length then (idxT tab b).getD m 0
  else tab.length + 2 * (m - (idxT tab b).length) + (if b then 1 else 0)

/-- The table check: even length, both index lists strictly increasing. -/
def tabOK (tab : List Bool) : Bool :=
  tab.length % 2 == 0 && sortedB (idxT tab false) && sortedB (idxT tab true)

theorem idx_mem {tab : List Bool} {b : Bool} {n : Nat} :
    n ∈ idxT tab b ↔ n < tab.length ∧ tab.getD n false = b := by
  unfold idxT; simp [List.mem_filter, List.mem_range]

theorem idx_get {tab : List Bool} {b : Bool} {m : Nat} (h : m < (idxT tab b).length) :
    (idxT tab b).getD m 0 ∈ idxT tab b := FiniteRunsWit.getD_mem' _ m 0 h

section tab
variable {tab : List Bool} (h : tabOK tab = true)
include h

theorem tab_even : tab.length % 2 = 0 := by
  simp only [tabOK, Bool.and_eq_true, beq_iff_eq] at h; exact h.1.1

theorem tab_sorted (b : Bool) : sortedB (idxT tab b) = true := by
  simp only [tabOK, Bool.and_eq_true] at h
  cases b
  · exact h.1.2
  · exact h.2

theorem κT_inc (b : Bool) (m : Nat) : κT tab b m < κT tab b (m + 1) := by
  have he := tab_even h
  unfold κT
  by_cases h1 : m + 1 < (idxT tab b).length
  · rw [if_pos (by omega), if_pos h1]
    exact FiniteNetWit.sorted_succ _ (tab_sorted h b) m 0 h1
  · rw [if_neg h1]
    by_cases h2 : m < (idxT tab b).length
    · rw [if_pos h2]
      have := (idx_mem.1 (idx_get h2)).1
      omega
    · rw [if_neg h2]; split <;> omega

theorem κT_b (b : Bool) (m : Nat) : σT tab (κT tab b m) = b := by
  have he := tab_even h
  unfold κT
  by_cases h1 : m < (idxT tab b).length
  · rw [if_pos h1]
    obtain ⟨a1, a2⟩ := idx_mem.1 (idx_get h1)
    unfold σT; rw [if_pos a1]; exact a2
  · rw [if_neg h1]
    unfold σT
    rw [if_neg (by omega)]
    cases b
    · simp only [Bool.false_eq_true, ite_false]
      simp; omega
    · simp only [ite_true]; simp; omega

theorem κT_all (b : Bool) (n : Nat) (hb : σT tab n = b) : ∃ m, κT tab b m = n := by
  have he := tab_even h
  unfold σT at hb
  by_cases hn : n < tab.length
  · rw [if_pos hn] at hb
    obtain ⟨m, hm, e⟩ := List.mem_iff_getElem.1 (idx_mem.2 ⟨hn, hb⟩)
    refine ⟨m, ?_⟩
    unfold κT; rw [if_pos hm, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hm]
    simpa using e
  · rw [if_neg hn] at hb
    refine ⟨(idxT tab b).length + (n - tab.length) / 2, ?_⟩
    unfold κT
    rw [if_neg (by omega)]
    have : (idxT tab b).length + (n - tab.length) / 2 - (idxT tab b).length =
      (n - tab.length) / 2 := by omega
    rw [this]
    cases b
    · simp at hb; simp only [Bool.false_eq_true, ite_false]; omega
    · simp at hb; simp only [ite_true]; omega

end tab

/-! ## 3. Lists of pins -/

open Formal.Cells.AssumeGuaranteeEnds (lmax cmax)

theorem lmax_congr {κ : Type} {ρ ρ' : κ → Nat → Nat} (j : Nat) :
    ∀ (l : List κ), (∀ i ∈ l, ρ i j = ρ' i j) → lmax ρ j l = lmax ρ' j l
  | [], _ => rfl
  | i :: l, h => by
    unfold lmax
    rw [h i (List.mem_cons_self ..), lmax_congr j l (fun i' hi => h i' (List.mem_cons_of_mem _ hi))]

theorem lmax_map {κ κ' : Type} (ρ : κ' → Nat → Nat) (f : κ → κ') (j : Nat) :
    ∀ (l : List κ), lmax (fun i => ρ (f i)) j l = lmax ρ j (l.map f)
  | [] => rfl
  | i :: l => by unfold lmax; rw [lmax_map ρ f j l]; rfl

theorem finRange_getD {α : Type} (l : List α) (d : α) :
    (List.finRange l.length).map (fun i => l.getD i.val d) = l := by
  apply List.ext_getElem (by simp)
  intro n h1 h2
  simp [List.getElem_finRange, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h2]


theorem finRange_getD' {α : Type} (l : List α) (d : α) (n : Nat) (h : l.length = n) :
    (List.finRange n).map (fun i => l.getD i.val d) = l := by
  subst h; exact finRange_getD l d

/-! ## 4. The `n`-pin C-element checker -/

open Formal.Cells.FiniteNet (FCelSpec FSteerSpec FOrSpec Lor)
open Formal.Cells.AssumeGuaranteeEnds (GPin gE sN)
open Formal.Cells.AssumeGuaranteeEndsNet (GD)
open Formal.Cells.LutFbBridge2 (CelLaw CelG gc)
open Formal.Cells.FiniteRunsWit (bnd)
open Formal.Net.Ops.Gen (genF steerF)
open Formal.Gen Formal.Gen.Cells

/-- The LUT at tick `t` (`Gf` the C-element without its reset pin). -/
def celQ {k : Nat} (Gf : (Fin k → Bool) → Bool → Bool) (pl : Fin k → List Nat) (Ln : List Nat)
    (t : Nat) : Bool :=
  bv Ln (t + 2) == (!decide (t < 2) && Gf (fun i => bv (pl i) t) (bv Ln t))

/-- The last pin arrival of phase `j`. -/
def celE {k : Nat} (pl : Fin k → List Nat) (j : Nat) : Nat :=
  lmax (fun i j => (pl i).getD j 1 + 1) j (List.finRange k)

/-- The node's edge of phase `j` (`nt11`). -/
def celT {k : Nat} (pl : Fin k → List Nat) (Ln : List Nat) (j : Nat) : Nat :=
  if cL Ln (celE pl j + 1) = Vph j then celE pl j + 1 else celE pl j + 2

/-- H_SND at phase `j`, `E = 1`. -/
def celS {k : Nat} (pl : Fin k → List Nat) (Ln : List Nat) (j : Nat) : Bool :=
  (List.finRange k).all fun i =>
    !decide (j + 1 < (pl i).length) || decide (celT pl Ln j + 1 ≤ (pl i).getD (j + 1) 1 + 1)

/-- **The C-element checker**: pins `bv (pl i)`, node `cL Ln`, feedback `bv Ln`. -/
def celB {k : Nat} (Gf : (Fin k → Bool) → Bool → Bool) (pl : Fin k → List Nat)
    (Ln : List Nat) : Bool :=
  bnd Ln && (List.finRange k).all (fun i => bnd (pl i) && sortedB (pl i) &&
    decide (Ln.length ≤ (pl i).length)) &&
  (List.finRange k).any (fun i => (pl i).length == Ln.length) &&
  (List.finRange k).any (fun i => decide (1 ≤ (pl i).getD 0 1)) && !bv Ln 1 &&
  (List.range (NB + 1)).all (celQ Gf pl Ln) && (List.range Ln.length).all (celS pl Ln)

theorem gE_list {ι : Type} {τ : ι → Nat → Nat} {p : GPin ι} {l : List Nat}
    (hP : p.P = bv l) (hl : p.wl = 1) (hh : p.wh = 1) (hτ : τ p.drv = fun j => l.getD j 1) (j : Nat) :
    gE τ p j = ε (bv l) 1 1 (fun j => l.getD j 1) j := by
  unfold gE; rw [hP, hl, hh, hτ]

theorem celB_spec {ι : Type} {k : Nat} {G : (Fin k → Bool) → Bool → Bool → Bool}
    {Gf : (Fin k → Bool) → Bool → Bool} (hG : ∀ p q r, G p q r = (!r && Gf p q)) (hL : CelLaw G)
    {D : GD ι} {L : ι → Nat → Prop} {c : ι} {pv : Fin k → GPin ι} {pl : Fin k → List Nat}
    {Ln : List Nat} (hchk : celB Gf pl Ln = true)
    (hO : D.O c = cL Ln) (hq : D.qp c = bv Ln) (hlo : D.lo c = 1) (hhi : D.hi c = 1)
    (hfl : D.fl c = 1) (hfh : D.fh c = 1) (hR : D.R = 2) (hrst : D.rst = rst2)
    (hpins : D.pins c = (List.finRange k).map pv)
    (hP : ∀ i, (pv i).P = bv (pl i)) (hwl : ∀ i, (pv i).wl = 1) (hwh : ∀ i, (pv i).wh = 1)
    (hτd : ∀ i, D.τ (pv i).drv = fun j => (pl i).getD j 1)
    (hLd : ∀ i, L (pv i).drv = fun j => j < (pl i).length) (hLc : L c = fun j => j < Ln.length)
    (hτ : ∀ j, D.τ c j = nt (D.O c) (D.lo c) (D.hi c) (cmax (fun i => gE D.τ (pv i)) j) (Vph j)) :
    FCelSpec G D L c pv 1 := by
  simp only [celB, Bool.and_eq_true, List.all_eq_true, List.any_eq_true, decide_eq_true_eq,
    beq_iff_eq, Bool.not_eq_true'] at hchk
  obtain ⟨⟨⟨⟨⟨⟨hbn, hpl⟩, ⟨i0, _, hi0⟩⟩, ⟨i1, _, h1p⟩⟩, hpw⟩, hlut⟩, hsnd⟩ := hchk
  have hbp : ∀ i, bnd (pl i) = true := fun i => (hpl i (List.mem_finRange i)).1.1
  have hsp : ∀ i, sortedB (pl i) = true := fun i => (hpl i (List.mem_finRange i)).1.2
  have hlp : ∀ i, Ln.length ≤ (pl i).length := fun i => (hpl i (List.mem_finRange i)).2
  have hgE : ∀ i j, gE D.τ (pv i) j = ε (bv (pl i)) 1 1 (fun j => (pl i).getD j 1) j :=
    fun i j => gE_list (hP i) (hwl i) (hwh i) (hτd i) j
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
      rw [hgE]; exact eps_list (hsp i) j (by have := hlp i; omega))
  refine { H_PINS := hpins, H_LAW := hL, H_CEL := ?_, H_PWR := ?_, H_TIMES := fun j _ => hτ j,
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
    have := AssumeGuaranteeEnds.cmax_arr (fun i => gE D.τ (pv i)) i1 j
    have h2 := eps_ge (bv (pl i1)) (fun j => (pl i1).getD j 1) j
    have h3 := getD_ge1 (hsp i1) h1p j
    rw [← hgE] at h2
    omega
  · rw [hLc] at hj; rw [hLd] at hl
    rw [hτ, hcm j hj, hO, hlo, hhi, nt11, hgE, eps_list (hsp i) (j + 1) hl]
    have := List.all_eq_true.1 (hsnd j (List.mem_range.2 hj)) i (List.mem_finRange i)
    simp only [Bool.or_eq_true, Bool.not_eq_true', decide_eq_false_iff_not, decide_eq_true_eq]
      at this
    rcases this with h | h
    · exact absurd hl h
    · unfold celT at h; exact h
  · rw [hhi, hfh, hR]; decide
  · rw [hhi, hfh, hlo]; decide


/-! ## 5. The steer branch checker -/

theorem sN_step {κ : Nat → Nat} (hκ : ∀ m, κ m < κ (m + 1)) (j : Nat) : sN κ j < sN κ (j + 1) := by
  obtain ⟨m, rfl | rfl⟩ : ∃ m, j = 2 * m ∨ j = 2 * m + 1 := ⟨j / 2, by omega⟩
  · rw [AssumeGuaranteeEnds.sN_even, AssumeGuaranteeEnds.sN_odd]; omega
  · rw [AssumeGuaranteeEnds.sN_odd, show 2 * m + 1 + 1 = 2 * (m + 1) by omega,
      AssumeGuaranteeEnds.sN_even]
    have := hκ m; omega

theorem sN_mono {κ : Nat → Nat} (hκ : ∀ m, κ m < κ (m + 1)) {j j' : Nat} (h : j ≤ j') :
    sN κ j ≤ sN κ j' := by
  induction j' with
  | zero => have : j = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j' ih =>
    rcases Nat.lt_or_ge j (j' + 1) with h' | h'
    · have := ih (by omega); have := sN_step hκ j'; omega
    · have : j = j' + 1 := by omega
      subst this; exact Nat.le_refl _

theorem bnd_getD {L : List Nat} (h : bnd L = true) {j : Nat} (hj : j < L.length) :
    L.getD j 1 < NB := by
  have := List.all_eq_true.1 h _ (FiniteRunsWit.getD_mem' L j 1 hj)
  simpa using this

/-- The steer LUT at tick `t`. -/
def stQ (b : Bool) (r : List Nat) (s : Nat → Bool) (Ln : List Nat) (t : Nat) : Bool :=
  bv Ln (t + 2) == (bv r t && (s t == b))

/-- While token `n`'s request is high, the select is the table's `n`-th entry. -/
def selQ (r : List Nat) (s : Nat → Bool) (tab : List Bool) (n t : Nat) : Bool :=
  !(decide (r.getD (2 * n) 1 + 1 ≤ t) &&
    (!decide (2 * n + 1 < r.length) || decide (t < r.getD (2 * n + 1) 1 + 1))) ||
  (s t == tab.getD n false)

/-- **The steer branch checker**: request pin `bv r`, select `s`, node `cL Ln`, branch `b`. -/
def stB (b : Bool) (r : List Nat) (s : Nat → Bool) (tab : List Bool) (Ln : List Nat) : Bool :=
  bnd r && bnd Ln && sortedB r && tabOK tab && decide ((r.length + 1) / 2 ≤ tab.length) &&
  !bv Ln 1 && (List.range (NB + 1)).all (stQ b r s Ln) &&
  (List.range ((r.length + 1) / 2)).all (fun n => (List.range (NB + 1)).all (selQ r s tab n)) &&
  (List.range Ln.length).all (fun j => decide (sN (κT tab b) j < r.length)) &&
  !decide (sN (κT tab b) Ln.length < r.length)

theorem stB_spec {ι : Type} {b : Bool} {r : List Nat} {s : Nat → Bool} {tab : List Bool}
    {Ln : List Nat} (hchk : stB b r s tab Ln = true) (hs : ∀ t, NB ≤ t → s t = s NB)
    {D : GD ι} {L : ι → Nat → Prop} {c : ι} {rp : GPin ι}
    (hO : D.O c = cL Ln) (hlo : D.lo c = 1) (hhi : D.hi c = 1)
    (hpins : D.pins c = [rp]) (hP : rp.P = bv r) (hwl : rp.wl = 1) (hwh : rp.wh = 1)
    (hτd : D.τ rp.drv = fun j => r.getD j 1)
    (hLd : L rp.drv = fun j => j < r.length) (hLc : L c = fun j => j < Ln.length)
    (hτ : ∀ j, D.τ c j = nt (D.O c) (D.lo c) (D.hi c) (gc (κT tab b) (gE D.τ rp) j) (Vph j)) :
    FSteerSpec D L c rp b s (σT tab) (κT tab b) := by
  simp only [stB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', decide_eq_false_iff_not] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨hbr, hbn⟩, hsr⟩, htab⟩, htl⟩, hpw⟩, hlut⟩, hsel⟩, hcnt⟩, hcnt2⟩ := hchk
  have hgE : ∀ j, gE D.τ rp j = ε (bv r) 1 1 (fun j => r.getD j 1) j :=
    fun j => gE_list hP hwl hwh hτd j
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
  refine { H_PINS := hpins, H_LUT_WIN := ?_, H_NO_REVERT := ?_, H_PWR := ?_, H_TIMES := fun j _ => hτ j,
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
    rw [hgE, hgE, eps_list hsr j (by omega), eps_list hsr (j + 1) h']
    have := FiniteNetWit.sorted_succ r hsr j 1 h'; omega
  · rw [hLd] at h1 h3; have h1' : 2 * n < r.length := h1
    rw [hgE, eps_list hsr _ h1'] at h2
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
      have := h3 h; rwa [hgE, eps_list hsr _ h] at this
    by_cases ht : t ≤ NB
    · exact hw t ht h2 h3'
    · have hlast : ¬ 2 * n + 1 < r.length := fun h => by
        have := h3' h; have := bnd_getD hbr h; omega
      rw [hs t (by omega)]
      exact hw NB (Nat.le_refl _) (by have := bnd_getD hbr h1'; omega) (fun h => absurd h hlast)
  · rw [hhi, hlo]; omega


/-! ## 6. The acknowledge OR checker -/

open Formal.Cells.AssumeGuaranteeMuxOr (cnt cnt_mono oe)

def lstB (a0 a1 : List Nat) (b : Bool) : List Nat := if b then a1 else a0

/-- The OR LUT at tick `t`. -/
def orQ (a0 a1 Ln : List Nat) (t : Nat) : Bool := bv Ln (t + 2) == (bv a1 t || bv a0 t)

/-- Merged edge `k`: its branch's edge index. -/
def orI (tab : List Bool) (k : Nat) : Nat := 2 * cnt (σT tab) (σT tab (k / 2)) (k / 2) + k % 2

/-- Merged edge `k`: its time (the branch pin's edge). -/
def orE (tab : List Bool) (a0 a1 : List Nat) (k : Nat) : Nat :=
  (lstB a0 a1 (σT tab (k / 2))).getD (orI tab k) 1 + 1

/-- **The OR checker**: branch pins `bv a0` (`ap false`), `bv a1` (`ap true`), node `cL Ln`,
token table `tab` (the steer's input tokens). -/
def orB (tab : List Bool) (a0 a1 Ln : List Nat) : Bool :=
  bnd a0 && bnd a1 && bnd Ln && sortedB a0 && sortedB a1 && tabOK tab && !bv Ln 1 &&
  (List.range (NB + 1)).all (orQ a0 a1 Ln) &&
  decide (Ln.length ≤ 2 * tab.length) &&
  decide (a0.length ≤ 2 * cnt (σT tab) false tab.length) &&
  decide (a1.length ≤ 2 * cnt (σT tab) true tab.length) &&
  (List.range (2 * tab.length)).all (fun k =>
    decide (k < Ln.length) == decide (orI tab k < (lstB a0 a1 (σT tab (k / 2))).length)) &&
  (List.range (Ln.length - 1)).all (fun k => decide (orE tab a0 a1 k < orE tab a0 a1 (k + 1)))

theorem orB_spec {ι : Type} {tab : List Bool} {a0 a1 Ln : List Nat}
    (hchk : orB tab a0 a1 Ln = true) {F : Bool → Bool → Bool} (hF : ∀ x y, F x y = (y || x))
    {D : GD ι} {L : ι → Nat → Prop} {c : ι} {ap : Bool → GPin ι}
    (hO : D.O c = cL Ln) (hlo : D.lo c = 1) (hhi : D.hi c = 1)
    (hpins : D.pins c = [ap false, ap true]) (hP : ∀ b, (ap b).P = bv (lstB a0 a1 b))
    (hwl : ∀ b, (ap b).wl = 1) (hwh : ∀ b, (ap b).wh = 1)
    (hτd : ∀ b, D.τ (ap b).drv = fun j => (lstB a0 a1 b).getD j 1)
    (hLd : ∀ b, L (ap b).drv = fun j => j < (lstB a0 a1 b).length)
    (hLc : L c = fun j => j < Ln.length)
    (hτ : ∀ k, D.τ c k = nt (D.O c) (D.lo c) (D.hi c) (oe (σT tab) (fun b => gE D.τ (ap b)) k)
      (Vph k)) :
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
  have hgE : ∀ b j, gE D.τ (ap b) j = ε (bv (lstB a0 a1 b)) 1 1 (fun j => (lstB a0 a1 b).getD j 1) j :=
    fun b j => gE_list (hP b) (hwl b) (hwh b) (hτd b) j
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
    rw [hgE, eps_list (hsB _) _ hl]; rfl
  refine { H_PINS := hpins, H_GATE := hF, H_LUT_WIN := ?_, H_NO_REVERT := ?_, H_PWR := ?_,
           H_TIMES := fun j _ => hτ j, H_CNT := fun k => ?_, H_KAPPA := κT_inc htab,
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


/-! ## 7. The link, from Bfin's checker -/

open Formal.Cells.FiniteNet (FLinkSpec LnL lnL_fin)
open Formal.Cells.AssumeGuaranteeEndsCap (LinkOut)
open Formal.Cells.WinFifoCausal (Stage Timing1 cph τs)
open Formal.Cells.FiniteRunsWit (linkB sndQ rcvQ ρL αL)
open Formal.Net.CapNet.Wit (CD)

theorem linkB_spec {x y : CD} (h : linkB x y = true) {ι : Type} {D : GD ι} {L : ι → Nat → Prop}
    {c : ι} {rp ap : GPin ι}
    (hO : D.O c = cL y.rq) (hq : D.qp c = bv y.rq) (hlo : D.lo c = 1) (hhi : D.hi c = 1)
    (hfl : D.fl c = 1) (hfh : D.fh c = 1) (hR : D.R = 2) (hrst : D.rst = rst2)
    (hpins : D.pins c = [rp, ap])
    (hrP : rp.P = bv x.rq) (hrl : rp.wl = 1) (hrh : rp.wh = 1)
    (hrτ : D.τ rp.drv = fun j => x.rq.getD j 1)
    (haP : ap.P = bv y.ak) (hal : ap.wl = 1) (hah : ap.wh = 1)
    (haτ : D.τ ap.drv = fun j => y.ak.getD j 1)
    (hrL : L rp.drv = fun j => j < x.rq.length) (haL : L ap.drv = fun j => j < y.ak.length)
    (hLc : L c = fun j => j < min x.rq.length (y.ak.length + 1))
    (hτ : ∀ j, D.τ c j = τs (D.O c) (D.lo c) (D.hi c) (gE D.τ rp) (ash D.R (gE D.τ ap)) j) :
    FLinkSpec D L c rp ap 3 3 ∧ LinkOut D c x.ch y.ch 3 3 := by
  obtain ⟨hak, sx, sy, c0, r0, St, hsnd, hrcv, d1, d2⟩ := FiniteNetWit.linkB_facts h
  have hgr : gE D.τ rp = FiniteNetWit.ρc x := funext fun j => gE_list hrP hrl hrh hrτ j
  have hga : ash D.R (gE D.τ ap) = FiniteNetWit.αc y := by
    rw [hR]; exact congrArg (ash 2) (funext fun j => gE_list haP hal hah haτ j)
  have hτ1 : ∀ j, D.τ c j = FiniteNetWit.τ1 x y j := fun j => by
    rw [hτ, hgr, hga, hO, hlo, hhi]; rfl
  refine ⟨{ H_PINS := hpins, H_STAGE := ?_, H_PWR := ?_, H_TIMES := fun j _ => hτ j, H_CNT := fun j => ?_,
            H_RST_EARLY := fun j => ?_, H_SND := fun j h1 h2 => ?_, H_RCV := fun j h1 h2 => ?_,
            H_T := ?_ }, ?_⟩
  · rw [hrP, haP, hrst, hO, hq, hlo, hhi, hfl, hfh]; exact St
  · intro t ht; rw [hhi] at ht
    have : t = 0 := by omega
    subst this; rw [hO]; exact c0
  · rw [hLc, hrL, haL]; exact (lnL_fin _ _ j).symm
  · rw [hR, hgr]
    have := eps_ge (bv x.rq) (FiniteNetWit.τ0 x) j
    have := getD_ge1 sx r0 j
    show 2 ≤ ε (bv x.rq) 1 1 (FiniteNetWit.τ0 x) j
    unfold FiniteNetWit.τ0 at *; omega
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
      rw [hτ1, e1, hgr]
      show _ ≤ ε (bv x.rq) 1 1 (FiniteNetWit.τ0 x) (j + 1)
      rw [show FiniteNetWit.τ0 x = fun j => x.rq.getD j 1 from rfl, eps_list sx (j + 1) hr]
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
      rw [hτ1, e1, gE_list haP hal hah haτ, eps_list sy j ha]
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

end Formal.Cells.FiniteNetWit2
