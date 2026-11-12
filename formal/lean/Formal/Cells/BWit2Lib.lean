import Formal.Cells.BWitLib
import Formal.Cells.AssumeGuaranteeMuxNFin

/-!
# Probe Bwit2 (shard B): checkers for `bd_mux`'s cells on event lists

Boolean checkers with proved soundness, in the style of `BWitLib` (pins at existing edges,
edge times checked as data), for the three `bd_mux` cell kinds that Bmn specifies:
* `bufB` / `bufB_spec`: a feedback-free 1-pin buffer (`udly` stages) → `FBufSpec`;
* `mjB` / `mjB_spec`: a mux join `uj0`/`uj1` (C-element `G2` of the data request and the
  gated control `ctl_req ∧ (s == b)`, the control read at its κ-indexed edges) → `FMuxJSpec`;
* `maB` / `maB_spec`: a mux acknowledge `uxa`/`uya` (C-element `G2` of the join and `z_ack`,
  `z_ack` read at its κ-indexed edges) → `FMuxASpec`.
All at unit LUT delay, unit feedback wire, `R = 2`. **Assumed:** nothing (definitions and
lemmas). Core Lean only.
-/

namespace Formal.Cells.BWit2
open Formal.Cells
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo nt_eq)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.LutFbBridge2Env (Wire ε ash)
open Formal.Cells.FiniteRunsWit (sortedB bv_phase bv_low bv_tail all_t cL rst2 NB bnd)
open Formal.Net.CapNet.Wit (bv cntLt bv_zero)
open Formal.Cells.AssumeGuaranteeEnds (GPin gE sN)
open Formal.Cells.AssumeGuaranteeEndsNet (GD)
open Formal.Cells.LutFbBridge2 (CelG gc G2 pv2 gate)
open Formal.Cells.FiniteNetWit2 (step_win fb_shift nt11 eps_list getD_ge1 σT κT tabOK κT_inc κT_b
  κT_all sN_mono bnd_getD selQ)
open Formal.Cells.AssumeGuaranteeMuxNFin (FMuxJSpec FMuxASpec FBufSpec)
open Formal.Net.Ops.Gen (cel2)

/-! ## 1. The buffer -/

def bufT (r Ln : List Nat) (j : Nat) : Nat :=
  if cL Ln (r.getD j 1 + 1 + 1) = Vph j then r.getD j 1 + 1 + 1 else r.getD j 1 + 1 + 2

/-- **The buffer checker**: pin `bv r`, node `cL Ln` = the pin one tick later. -/
def bufB (r Ln : List Nat) : Bool :=
  bnd r && bnd Ln && sortedB r && !bv Ln 1 && (Ln.length == r.length) &&
  (List.range (NB + 1)).all (fun t => bv Ln (t + 2) == bv r t) &&
  (List.range Ln.length).all (fun j => Ln.getD j 1 == bufT r Ln j)

theorem bufB_spec {r Ln : List Nat} (hchk : bufB r Ln = true) {ι : Type} {D : GD ι}
    {L : ι → Nat → Prop} {c : ι} {p : GPin ι}
    (hO : D.O c = cL Ln) (hlo : D.lo c = 1) (hhi : D.hi c = 1)
    (hpins : D.pins c = [p]) (hP : p.P = bv r)
    (hgE : ∀ j, j < r.length → gE D.τ p j = ε (bv r) 1 1 (fun j => r.getD j 1) j)
    (hLd : L p.drv = fun j => j < r.length) (hLc : L c = fun j => j < Ln.length)
    (hτL : ∀ j, j < Ln.length → D.τ c j = Ln.getD j 1) :
    FBufSpec D L c p := by
  simp only [bufB, Bool.and_eq_true, List.all_eq_true, beq_iff_eq, Bool.not_eq_true'] at hchk
  obtain ⟨⟨⟨⟨⟨⟨hbr, hbn⟩, hsr⟩, hpw⟩, hlen⟩, hlut⟩, htm⟩ := hchk
  have lutA : ∀ t, (bv Ln (t + 2) == bv r t) = true := all_t NB
    (List.all_eq_true.2 fun t ht => by simpa using hlut t ht) (fun t ht => by
      rw [bv_tail hbn (t + 2) (by omega), bv_tail hbr t ht, bv_tail hbn (NB + 2) (by omega)])
  have hstep : ∀ t, D.O c (t + 1) = p.P t := by
    intro t; have := lutA t; simp only [beq_iff_eq] at this
    rw [hO, hP]; exact this
  have sw := step_win hstep
  refine { H_PINS := hpins, H_LUT_WIN := ?_, H_NO_REVERT := ?_, H_PWR := ?_,
           H_TIMES := fun j hj => ?_, H_CNT := fun j => ?_, H_FLOOR := fun j _ => ?_ }
  · rw [hlo, hhi]; exact sw.1
  · rw [hlo, hhi]; exact sw.2
  · intro t ht; rw [hhi] at ht
    have : t = 0 := by omega
    subst this; rw [hO]; exact hpw
  · rw [hLc] at hj
    have hj' : j < r.length := by omega
    have e := htm j (List.mem_range.2 hj)
    rw [hτL j hj, e, hgE j hj', eps_list hsr j hj', hO, hlo, hhi, nt11]; rfl
  · rw [hLc, hLd]; show j < Ln.length ↔ j < r.length; omega
  · rw [hhi, hlo]; omega

/-! ## 2. Two-input C-elements with a κ-indexed second pin -/

/-- The LUT at tick `t` (feedback = the node's own list, reset `rst2`); `g` gates the second
input (the mux join's select gate, or the identity). -/
def cjQ (g : Nat → Bool → Bool) (a cl Ln : List Nat) (t : Nat) : Bool :=
  bv Ln (t + 2) == (!decide (t < 2) && cel2 (bv a t) (g t (bv cl t)) (bv Ln t))

/-- Last pin arrival of phase `j` (`a` at `j`, `cl` at its κ-edge `sN κ j`). -/
def cjA (κ : Nat → Nat) (a cl : List Nat) (j : Nat) : Nat :=
  max (a.getD j 1 + 1) (cl.getD (sN κ j) 1 + 1)

def cjT (κ : Nat → Nat) (a cl Ln : List Nat) (j : Nat) : Nat :=
  if cL Ln (cjA κ a cl j + 1) = Vph j then cjA κ a cl j + 1 else cjA κ a cl j + 2

/-- The edge-set and edge-time checks shared by the join and the acknowledge. -/
def cjCnt (κ : Nat → Nat) (a cl Ln : List Nat) : Bool :=
  (List.range Ln.length).all (fun j => decide (j < a.length) && decide (sN κ j < cl.length)) &&
  (decide (a.length ≤ Ln.length) || !decide (sN κ Ln.length < cl.length)) &&
  (List.range Ln.length).all (fun j => Ln.getD j 1 == cjT κ a cl Ln j)

theorem cnt_iff {κ : Nat → Nat} (hκ : ∀ m, κ m < κ (m + 1)) {a cl Ln : List Nat}
    (h1 : ∀ j, j < Ln.length → j < a.length ∧ sN κ j < cl.length)
    (h2 : a.length ≤ Ln.length ∨ ¬ sN κ Ln.length < cl.length) (j : Nat) :
    j < Ln.length ↔ j < a.length ∧ sN κ j < cl.length := by
  constructor
  · exact h1 j
  · intro ⟨ha, hc⟩
    apply Classical.byContradiction; intro hn
    rcases h2 with h2 | h2
    · omega
    · have := sN_mono hκ (show Ln.length ≤ j by omega); omega

/-- **The mux join checker** (`uj0`, `b = false`; `uj1`, `b = true`): data request pin
`bv a`, control pin `bv cl`, select `s`, node `cL Ln`, token table `tab`. -/
def mjB (b : Bool) (a cl : List Nat) (s : Nat → Bool) (tab : List Bool) (Ln : List Nat) : Bool :=
  bnd a && bnd cl && bnd Ln && sortedB a && sortedB cl && tabOK tab && !bv Ln 1 &&
  decide (1 ≤ a.getD 0 1) &&
  (List.range (NB + 1)).all (cjQ (fun t v => v && (s t == b)) a cl Ln) &&
  cjCnt (κT tab b) a cl Ln &&
  (List.range Ln.length).all (fun j =>
    (!decide (j + 1 < a.length) || decide (Ln.getD j 1 + 1 ≤ a.getD (j + 1) 1 + 1)) &&
    (!decide (sN (κT tab b) (j + 1) < cl.length) ||
      decide (Ln.getD j 1 + 1 ≤ cl.getD (sN (κT tab b) (j + 1)) 1 + 1))) &&
  decide ((cl.length + 1) / 2 ≤ tab.length) &&
  (List.range ((cl.length + 1) / 2)).all (fun n => (List.range (NB + 1)).all (selQ cl s tab n))

theorem mjB_spec {b : Bool} {a cl : List Nat} {s : Nat → Bool} {tab : List Bool} {Ln : List Nat}
    (hchk : mjB b a cl s tab Ln = true) (hs : ∀ t, NB ≤ t → s t = s NB)
    {ι : Type} {D : GD ι} {L : ι → Nat → Prop} {c : ι} {xp cp : GPin ι}
    (hO : D.O c = cL Ln) (hq : D.qp c = bv Ln) (hlo : D.lo c = 1) (hhi : D.hi c = 1)
    (hfl : D.fl c = 1) (hfh : D.fh c = 1) (hR : D.R = 2) (hrst : D.rst = rst2)
    (hpins : D.pins c = [xp, cp]) (hxP : xp.P = bv a) (hcP : cp.P = bv cl)
    (hgx : ∀ j, j < a.length → gE D.τ xp j = ε (bv a) 1 1 (fun j => a.getD j 1) j)
    (hgc : ∀ j, j < cl.length → gE D.τ cp j = ε (bv cl) 1 1 (fun j => cl.getD j 1) j)
    (hLx : L xp.drv = fun j => j < a.length) (hLcp : L cp.drv = fun j => j < cl.length)
    (hLc : L c = fun j => j < Ln.length)
    (hτL : ∀ j, j < Ln.length → D.τ c j = Ln.getD j 1) :
    FMuxJSpec D L c xp cp b s (σT tab) (κT tab b) 1 := by
  simp only [mjB, cjCnt, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', beq_iff_eq, Bool.or_eq_true, decide_eq_false_iff_not] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hba, hbc⟩, hbn⟩, hsa⟩, hsc⟩, htab⟩, hpw⟩, ha0⟩, hlut⟩, ⟨⟨hc1, hc2⟩, htm⟩⟩,
    hsnd⟩, htl⟩, hsel⟩ := hchk
  have hNB : NB = 768 := rfl
  have hκ := κT_inc htab b
  have lutA : ∀ t, cjQ (fun t v => v && (s t == b)) a cl Ln t = true := all_t NB
    (List.all_eq_true.2 hlut) (fun t ht => by
      unfold cjQ
      dsimp only
      rw [bv_tail hbn (t + 2) (by omega), bv_tail hba t ht, bv_tail hbc t ht, hs t ht,
        bv_tail hbn t ht, bv_tail hbn (NB + 2) (by omega)]
      rw [show decide (t < 2) = false from decide_eq_false (by omega),
        show decide (NB < 2) = false from decide_eq_false (by omega)])
  have hstep : ∀ t, D.O c (t + 1) = G2 (pv2 xp.P (gate b cp.P s) t) (D.qp c t) (D.rst t) := by
    intro t
    have := lutA t
    unfold cjQ at this
    simp only [beq_iff_eq] at this
    rw [hO, hq, hrst, hxP, hcP]
    simp only [cL, G2, pv2, gate, rst2]
    exact this
  have sw := step_win hstep
  have hc1' : ∀ j, j < Ln.length → j < a.length ∧ sN (κT tab b) j < cl.length := fun j hj => by
    have := hc1 j (List.mem_range.2 hj); exact ⟨this.1, this.2⟩
  have hcnt := cnt_iff hκ hc1' (by rcases hc2 with h | h; exact Or.inl h; exact Or.inr h)
  have harr : ∀ j, j < Ln.length →
      max (gE D.τ xp j) (gc (κT tab b) (gE D.τ cp) j) = cjA (κT tab b) a cl j := by
    intro j hj
    obtain ⟨h1, h2⟩ := hc1' j hj
    unfold cjA
    rw [AssumeGuaranteeEnds.gc_sN, hgx j h1, hgc _ h2, eps_list hsa j h1, eps_list hsc _ h2]
  have hτ : ∀ j, j < Ln.length → D.τ c j =
      nt (D.O c) (D.lo c) (D.hi c) (max (gE D.τ xp j) (gc (κT tab b) (gE D.τ cp) j)) (Vph j) := by
    intro j hj
    have e := htm j (List.mem_range.2 hj)
    rw [hτL j hj, e, harr j hj, hO, hlo, hhi, nt11]; rfl
  refine { H_PINS := hpins, H_CEL := ?_, H_PWR := ?_,
           H_TIMES := fun j hj => hτ j (by rw [hLc] at hj; exact hj),
           H_CNT := fun j => ?_, H_DOWNC := fun j h => ?_, H_INCC := fun j h => ?_,
           H_SEL_STABLE := fun n t h1 h2 h3 => ?_, H_KAPPA := hκ, H_KAPPA_B := κT_b htab b,
           H_KAPPA_ALL := κT_all htab b, H_RST_EARLY := fun j hj => ?_,
           H_SND := fun j hj => ⟨fun hl => ?_, fun hl => ?_⟩, H_RST_LONG := ?_, H_LAT := ?_ }
  · rw [hlo, hhi, hfl, hfh]
    exact ⟨sw.1, sw.2, by rw [hO, hq]; exact fb_shift Ln, Nat.le_refl 1⟩
  · intro t ht; rw [hhi] at ht
    have : t = 0 := by omega
    subst this; rw [hO]; exact hpw
  · rw [hLc, hLx, hLcp]; exact hcnt j
  · rw [hLcp] at h ⊢; show j < cl.length; have : j + 1 < cl.length := h; omega
  · rw [hLcp] at h; have h' : j + 1 < cl.length := h
    rw [hgc j (by omega), hgc (j + 1) h', eps_list hsc j (by omega), eps_list hsc (j + 1) h']
    have := FiniteNetWit.sorted_succ cl hsc j 1 h'; omega
  · rw [hLcp] at h1 h3; have h1' : 2 * n < cl.length := h1
    rw [hgc _ h1', eps_list hsc _ h1'] at h2
    have hn : n < (cl.length + 1) / 2 := by omega
    have hσ : σT tab n = tab.getD n false := by unfold σT; rw [if_pos (by omega)]
    rw [hσ]
    have hw : ∀ u, u ≤ NB → cl.getD (2 * n) 1 + 1 ≤ u →
        (2 * n + 1 < cl.length → u < cl.getD (2 * n + 1) 1 + 1) → s u = tab.getD n false := by
      intro u hu a1 a2
      have := hsel n (List.mem_range.2 hn) u (List.mem_range.2 (by omega))
      unfold selQ at this
      rw [decide_eq_true a1] at this
      by_cases hB : 2 * n + 1 < cl.length
      · rw [decide_eq_true hB, decide_eq_true (a2 hB)] at this
        simpa using this
      · rw [decide_eq_false hB] at this
        simpa using this
    have h3' : 2 * n + 1 < cl.length → t < cl.getD (2 * n + 1) 1 + 1 := fun h => by
      have := h3 h; rwa [hgc _ h, eps_list hsc _ h] at this
    by_cases ht : t ≤ NB
    · exact hw t ht h2 h3'
    · have hlast : ¬ 2 * n + 1 < cl.length := fun h => by
        have := h3' h; have := bnd_getD hbc h; omega
      rw [hs t (by omega)]
      exact hw NB (Nat.le_refl _) (by have := bnd_getD hbc h1'; omega) (fun h => absurd h hlast)
  · rw [hLc] at hj
    rw [hR, harr j hj]
    have := getD_ge1 hsa ha0 j
    unfold cjA; omega
  · rw [hLc] at hj; rw [hLx] at hl
    have hl' : j + 1 < a.length := hl
    have q := (hsnd j (List.mem_range.2 hj)).1
    rcases q with q | q
    · exact absurd hl' q
    · rw [hτL j hj, hgx _ hl', eps_list hsa _ hl']; exact q
  · rw [hLc] at hj; rw [hLcp] at hl
    have hl' : sN (κT tab b) (j + 1) < cl.length := hl
    have q := (hsnd j (List.mem_range.2 hj)).2
    rcases q with q | q
    · exact absurd hl' q
    · rw [hτL j hj, AssumeGuaranteeEnds.gc_sN, hgc _ hl', eps_list hsc _ hl']; exact q
  · rw [hhi, hfh, hR]; decide
  · rw [hhi, hfh, hlo]; exact Nat.le_refl _

/-- **The mux acknowledge checker** (`uxa`, `b = false`; `uya`, `b = true`): join pin `bv a`,
`z_ack` pin `bv zl`, node `cL Ln`, token table `tab` (the control's tokens). -/
def maB (b : Bool) (a zl : List Nat) (tab : List Bool) (Ln : List Nat) : Bool :=
  bnd a && bnd zl && bnd Ln && sortedB a && sortedB zl && tabOK tab && !bv Ln 1 &&
  decide (1 ≤ a.getD 0 1) &&
  (List.range (NB + 1)).all (cjQ (fun _ v => v) a zl Ln) &&
  cjCnt (κT tab b) a zl Ln &&
  (List.range Ln.length).all (fun j =>
    (!decide (j + 1 < a.length) || decide (Ln.getD j 1 + 1 ≤ a.getD (j + 1) 1 + 1)) &&
    (!decide (sN (κT tab b) j + 1 < zl.length) ||
      decide (Ln.getD j 1 + 1 ≤ zl.getD (sN (κT tab b) j + 1) 1 + 1))) &&
  (List.range ((a.length + 1) / 2)).all (fun m =>
    !decide (0 < κT tab b m) || !decide (2 * m < a.length) ||
    (decide (2 * κT tab b m - 1 < zl.length) &&
      decide (zl.getD (2 * κT tab b m - 1) 1 + 1 ≤ a.getD (2 * m) 1 + 1)))

theorem maB_spec {b : Bool} {a zl : List Nat} {tab : List Bool} {Ln : List Nat}
    (hchk : maB b a zl tab Ln = true)
    {ι : Type} {D : GD ι} {L : ι → Nat → Prop} {c : ι} {ap zp : GPin ι}
    (hO : D.O c = cL Ln) (hq : D.qp c = bv Ln) (hlo : D.lo c = 1) (hhi : D.hi c = 1)
    (hfl : D.fl c = 1) (hfh : D.fh c = 1) (hR : D.R = 2) (hrst : D.rst = rst2)
    (hpins : D.pins c = [ap, zp]) (haP : ap.P = bv a) (hzP : zp.P = bv zl)
    (hga : ∀ j, j < a.length → gE D.τ ap j = ε (bv a) 1 1 (fun j => a.getD j 1) j)
    (hgz : ∀ j, j < zl.length → gE D.τ zp j = ε (bv zl) 1 1 (fun j => zl.getD j 1) j)
    (hLa : L ap.drv = fun j => j < a.length) (hLz : L zp.drv = fun j => j < zl.length)
    (hLc : L c = fun j => j < Ln.length)
    (hτL : ∀ j, j < Ln.length → D.τ c j = Ln.getD j 1) :
    FMuxASpec D L c ap zp (κT tab b) 1 := by
  simp only [maB, cjCnt, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq,
    Bool.not_eq_true', beq_iff_eq, Bool.or_eq_true, decide_eq_false_iff_not] at hchk
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨hba, hbz⟩, hbn⟩, hsa⟩, hsz⟩, htab⟩, hpw⟩, ha0⟩, hlut⟩, ⟨⟨hc1, hc2⟩, htm⟩⟩,
    hsnd⟩, hzf⟩ := hchk
  have hNB : NB = 768 := rfl
  have hκ := κT_inc htab b
  have lutA : ∀ t, cjQ (fun _ v => v) a zl Ln t = true := all_t NB
    (List.all_eq_true.2 hlut) (fun t ht => by
      unfold cjQ
      rw [bv_tail hbn (t + 2) (by omega), bv_tail hba t ht, bv_tail hbz t ht,
        bv_tail hbn t ht, bv_tail hbn (NB + 2) (by omega)]
      rw [show decide (t < 2) = false from decide_eq_false (by omega),
        show decide (NB < 2) = false from decide_eq_false (by omega)])
  have hstep : ∀ t, D.O c (t + 1) = G2 (pv2 ap.P zp.P t) (D.qp c t) (D.rst t) := by
    intro t
    have := lutA t
    unfold cjQ at this
    simp only [beq_iff_eq] at this
    rw [hO, hq, hrst, haP, hzP]
    simp only [cL, G2, pv2, rst2]
    exact this
  have sw := step_win hstep
  have hc1' : ∀ j, j < Ln.length → j < a.length ∧ sN (κT tab b) j < zl.length := fun j hj => by
    have := hc1 j (List.mem_range.2 hj); exact ⟨this.1, this.2⟩
  have hcnt := cnt_iff hκ hc1' (by rcases hc2 with h | h; exact Or.inl h; exact Or.inr h)
  have harr : ∀ j, j < Ln.length →
      max (gE D.τ ap j) (gc (κT tab b) (gE D.τ zp) j) = cjA (κT tab b) a zl j := by
    intro j hj
    obtain ⟨h1, h2⟩ := hc1' j hj
    unfold cjA
    rw [AssumeGuaranteeEnds.gc_sN, hga j h1, hgz _ h2, eps_list hsa j h1, eps_list hsz _ h2]
  have hτ : ∀ j, j < Ln.length → D.τ c j =
      nt (D.O c) (D.lo c) (D.hi c) (max (gE D.τ ap j) (gc (κT tab b) (gE D.τ zp) j)) (Vph j) := by
    intro j hj
    have e := htm j (List.mem_range.2 hj)
    rw [hτL j hj, e, harr j hj, hO, hlo, hhi, nt11]; rfl
  refine { H_PINS := hpins, H_CEL := ?_, H_PWR := ?_,
           H_TIMES := fun j hj => hτ j (by rw [hLc] at hj; exact hj),
           H_CNT := fun j => ?_, H_DOWNZ := fun j h => ?_, H_INCZ := fun j h => ?_,
           H_RST_EARLY := fun j hj => ?_, H_SNDJ := fun j hj hl => ?_,
           H_SNDZ := fun j hj hl => ?_, H_ZFALL := fun m hm hl => ?_, H_RST_LONG := ?_,
           H_LAT := ?_ }
  · rw [hlo, hhi, hfl, hfh]
    exact ⟨sw.1, sw.2, by rw [hO, hq]; exact fb_shift Ln, Nat.le_refl 1⟩
  · intro t ht; rw [hhi] at ht
    have : t = 0 := by omega
    subst this; rw [hO]; exact hpw
  · rw [hLc, hLa, hLz]; exact hcnt j
  · rw [hLz] at h ⊢; show j < zl.length; have : j + 1 < zl.length := h; omega
  · rw [hLz] at h; have h' : j + 1 < zl.length := h
    rw [hgz j (by omega), hgz (j + 1) h', eps_list hsz j (by omega), eps_list hsz (j + 1) h']
    have := FiniteNetWit.sorted_succ zl hsz j 1 h'; omega
  · rw [hLc] at hj
    rw [hR, harr j hj]
    have := getD_ge1 hsa ha0 j
    unfold cjA; omega
  · rw [hLc] at hj; rw [hLa] at hl
    have hl' : j + 1 < a.length := hl
    have q := (hsnd j (List.mem_range.2 hj)).1
    rcases q with q | q
    · exact absurd hl' q
    · rw [hτL j hj, hga _ hl', eps_list hsa _ hl']; exact q
  · rw [hLc] at hj; rw [hLz] at hl
    have hl' : sN (κT tab b) j + 1 < zl.length := hl
    have q := (hsnd j (List.mem_range.2 hj)).2
    rcases q with q | q
    · exact absurd hl' q
    · rw [hτL j hj, hgz _ hl', eps_list hsz _ hl']; exact q
  · rw [hLa] at hl; have hl' : 2 * m < a.length := hl
    have q := hzf m (List.mem_range.2 (by omega))
    rcases q with (q | q) | ⟨q1, q2⟩
    · exact absurd hm q
    · exact absurd hl' q
    · refine ⟨by rw [hLz]; exact q1, ?_⟩
      rw [hgz _ q1, hga _ hl', eps_list hsz _ q1, eps_list hsa _ hl']; exact q2
  · rw [hhi, hfh, hR]; decide
  · rw [hhi, hfh, hlo]; exact Nat.le_refl _

end Formal.Cells.BWit2
