import Formal.Cells.ResetGcdVec
import Formal.Cells.LibEndMemMlink
open Formal.Core.LutList

/-!
# Probe Bfw (shard B): gcd_hw's per-cell reset model derived from the network run, and the first-wave cells

Notes: `formal/notes/B-reset-gcd-vec2.md`. Follows `ResetGcdVec` (probe Brst),
`ResetGcd` (Rst2) and `ResetGcdWave` (Rst3); all read-only here.

Results (namespace `Formal.Cells.ResetGcdVec2`):
* **Part 1: `CellRun` from the GMW network `Run`.** `cellRun_of_run`: in any
  run of `gNet` (7f's GMW `Run` with `Bounded D W`), every rst-reading LUT
  loop with distinct pin nodes (all 414, `pinsOK`, decided) has a
  `ResetGcdVec.CellRun` whose root is the LUT value the cell sees
  (`Run.exc`), with `Dhi = W + D + 1`. `H_TREE` is exact (`lutK` of the
  definite reads), `H_FB_WIN` is derived from `Bounded` (`exc_lag`: the
  output always equals the LUT value of one of the last `D + 1` steps), and
  `H_RST_HIGH` / `H_DATA_STATIC` are derived from facts about the reads.
  `gcd_reset_vec_net`: with a clean rst from power-up (Rst3's
  `gcd_clean_release` hypotheses) every one of those facts holds, and
  `H_RST_LONG` at the hold cells follows from Rst2's `H_HOLD_LONG`: the
  per-cell model, and `ResetGcdVec.gcd_reset_vec`'s conclusion, are
  consequences of the network model with NO per-cell timing assumption.
* **Part 2: the 21 first-wave cells.** `vec2_census` (decided): at the
  first-wave vector `rhoA` (every wave node of Rst3 `x`) the 414 loops split
  into 194 forced, 203 hold, 10 leave (the frontier) and 7 moving (cells of
  the wave itself). The 203 are Brst's 195 minus the 3 moving joins, plus 11
  cells (`newHoldL`) that are FORCED at the reset vector and become HOLD
  once their first-wave data pin rises. `forcedA_clean`, `holdA_clean`,
  `gcd_reset_vec2`: every non-moving cell stays at its reset value through
  the whole first wave (not only up to its data pins' first move), with the
  width condition `T1 + Dhi ≤ s` at the 192 old hold cells and
  `T1 + Dhi ≤ max s Tw` at the 11 new ones (`newHold_exact`: exact at the
  moved vector). `wave_early` + `wave_cells_order`: a wave node `w` is at
  its reset value through step `F + wR w - 1` (`F`: rst last 1), so the data
  pins of each of the 21 cells are at the reset vector through
  `F + dminP n` (32 for the three steer joins, 1 for the cells reading a
  frontier controller), while their rst pin reads 0 from `F + W + 1`: if
  `W < dminP n` the cell is released for good before its data can move.
  `counter_uori2` (`W = dminP = 1`) and `counter_br9` (`W = dminP = 32`):
  bounded runs meeting every hypothesis in which the cell's rst pin reads 1
  at every step before its first-wave data pin first reads the moved value.
* `nonvac_net`: a unit-delay run of `gNet` meets every hypothesis of the
  network instance.

Core Lean; every certificate is checked with `decide +kernel`.
-/

namespace Formal.Cells.ResetGcdVec2
open Formal.Cells Formal.Cells.TernarySound Formal.Cells.ResetContract Formal.Cells.ResetGcd
open Formal.Cells.ResetGcdVec

/-! ## Vector-parametric classes -/

def forcBV (σ : Nat → K3) (init : Nat) (pins : List Src) (n : Nat) (b : Bool) : Bool :=
  ks.all fun r => ks.all fun k => decide (cellF init pins n σ r k = K3.ofBool b)
def holdBV (σ : Nat → K3) (init : Nat) (pins : List Src) (n : Nat) (b : Bool) : Bool :=
  ks.all fun r => decide (cellF init pins n σ r (K3.ofBool b) = K3.ofBool b)
def leaveBV (σ : Nat → K3) (init : Nat) (pins : List Src) (n : Nat) (b : Bool) : Bool :=
  ks.all fun k => decide (cellF init pins n σ .f k = K3.ofBool (!b))

theorem forcB_eq : forcB = forcBV rho := rfl
theorem holdB_eq : holdB = holdBV rho := rfl

theorem holdV_at {σ : Nat → K3} {init : Nat} {pins : List Src} {n : Nat} {b : Bool}
    (hh : holdBV σ init pins n b = true) {e : Nat → K3} (he : ∀ i, i ≠ 0 → i ≠ n → le (e i) (σ i))
    (r : K3) : cellF init pins n e r (K3.ofBool b) = K3.ofBool b := by
  have h1 := cellF_le (init := init) (pins := pins) (r := r) (q := K3.ofBool b) he
  have h2 : cellF init pins n σ r (K3.ofBool b) = K3.ofBool b := of_decide_eq_true (ks_all hh r)
  rw [h2] at h1
  exact le_ofBool_eq h1

theorem forcedV_at {σ : Nat → K3} {init : Nat} {pins : List Src} {n : Nat} {b : Bool}
    (hF : forcBV σ init pins n b = true) {e : Nat → K3} (he : ∀ i, i ≠ 0 → i ≠ n → le (e i) (σ i))
    (r k : K3) : cellF init pins n e r k = K3.ofBool b := by
  have h1 := cellF_le (init := init) (pins := pins) (r := r) (q := k) he
  have h2 : cellF init pins n σ r k = K3.ofBool b :=
    of_decide_eq_true (ks_all (ks_all (f := fun r => ks.all fun k =>
      decide (cellF init pins n σ r k = K3.ofBool b)) hF r) k)
  rw [h2] at h1
  exact le_ofBool_eq h1

/-- The first-wave vector: as `rho`, but every node of Rst3's wave
certificate (`wR ≠ 0`: rst and the 108 nodes that move in the first wave)
is `x`. -/
def rhoA (i : Nat) : K3 := if ResetGcdWave.wR i ≠ 0 then .x else rho i
/-- The end-of-wave vector, data nets at 1 (exactness only): control nets
at their end-of-wave value `sigB`. -/
def rhoA1 (i : Nat) : K3 := if gCtl i then K3.ofBool (ResetGcdWave.sigB i) else .t

theorem le_rho_rhoA (i : Nat) : le (rho i) (rhoA i) := by
  unfold rhoA
  by_cases h : ResetGcdWave.wR i ≠ 0
  · rw [ite_eq_left h]; exact Or.inr rfl
  · rw [ite_eq_right h]; exact le_refl _

/-! ## The two-phase cell model and its release theorems -/

/-- `CellRun` plus a second data phase: on `[s, Tz)` the data pins are
Kleene-below the first-wave vector `rhoA` (the reset vector with every wave
node `x`). `Tw ≤ Tz` is not needed. -/
structure CellRunW (init : Nat) (pins : List Src) (n : Nat) (T1 s Tw Tz Dhi : Nat)
    (e : Nat → Nat → K3) (r qp G : Nat → K3) : Prop where
  base : CellRun init pins n T1 s Tw Dhi e r qp G
  /-- H_DATA_WAVE: on `[s, Tz)` every data pin reads below `rhoA`. -/
  H_DATA_WAVE : ∀ t, s ≤ t → t < Tz → ∀ i, i ≠ 0 → i ≠ n → le (e t i) (rhoA i)

/-- **Forced at the first-wave vector**: no width condition, the root is the
reset value on `[T1, Tz)`. -/
theorem forcedA_clean {init : Nat} {pins : List Src} {n T1 s Tw Tz Dhi : Nat} {b : Bool}
    {e : Nat → Nat → K3} {r qp G : Nat → K3}
    (hf : followB init pins n b = true) (hF : forcBV rhoA init pins n b = true)
    (C : CellRunW init pins n T1 s Tw Tz Dhi e r qp G) :
    ∀ t, T1 ≤ t → t < Tz → G t = K3.ofBool b := by
  intro t h1 h2
  rw [C.base.H_TREE]
  by_cases hs : t < s
  · rw [C.base.H_RST_HIGH t h1 hs]; exact follow_any hf _ _
  · exact forcedV_at hF (C.H_DATA_WAVE t (by omega) h2) _ _

/-- **Hold at the first-wave vector.** The root is the reset value on
`[T1, Tz)` if the width condition holds at the release (`T1 + Dhi ≤ s`), or,
for a cell forced at the reset vector, at the first data move
(`T1 + Dhi ≤ Tw`): `H_RST_LONG2`. -/
theorem holdA_clean {init : Nat} {pins : List Src} {n T1 s Tw Tz Dhi : Nat} {b : Bool}
    {e : Nat → Nat → K3} {r qp G : Nat → K3}
    (hf : followB init pins n b = true) (hH : holdBV rhoA init pins n b = true)
    (C : CellRunW init pins n T1 s Tw Tz Dhi e r qp G)
    (H_RST_LONG2 : T1 + Dhi ≤ s ∨ (forcB init pins n b = true ∧ T1 + Dhi ≤ Tw)) :
    ∀ t, T1 ≤ t → t < Tz → G t = K3.ofBool b := by
  have key : ∀ m t, t < m → T1 ≤ t → t < Tz → G t = K3.ofBool b := by
    intro m
    induction m with
    | zero => intro t h; omega
    | succ m ih =>
      intro t ht h1 h2
      rw [C.base.H_TREE]
      by_cases hs : t < s
      · rw [C.base.H_RST_HIGH t h1 hs]; exact follow_any hf _ _
      · have hfar : T1 + Dhi ≤ t ∨ (forcB init pins n b = true ∧ t < Tw) := by
          rcases H_RST_LONG2 with h | ⟨hF, h⟩
          · left; omega
          · by_cases htw : t < Tw
            · right; exact ⟨hF, htw⟩
            · left; omega
        rcases hfar with hfar | ⟨hF, htw⟩
        · obtain ⟨d, hd1, hd2, hd3, hq⟩ := C.base.H_FB_WIN t (by omega)
          rw [hq, ih (t - d) (by omega) (by omega) (by omega)]
          exact holdV_at hH (C.H_DATA_WAVE t (by omega) h2) _
        · exact forced_at hF (C.base.H_DATA_STATIC t (by omega) htw) _ _
  exact fun t => key (t + 1) t (by omega)


/-! ## Part 1: `CellRun` from the GMW network run -/

/-- The output of a GMW gate always equals the LUT value it saw at one of the
last `D + 1` steps (`Bounded`'s gate bound, with `Run`'s hold-or-update
rule). -/
theorem switch_back (v : Nat → Nat → Bool) (j : Nat) :
    ∀ m i, i < m → v i j ≠ v m j →
      ∃ q, i ≤ q ∧ q < m ∧ v (q + 1) j ≠ v q j ∧ v (q + 1) j = v m j := by
  intro m
  induction m with
  | zero => intro i h; omega
  | succ m ih =>
    intro i hi hne
    by_cases hm : v m j = v (m + 1) j
    · have him : i < m := by
        rcases Nat.lt_or_ge i m with h | h
        · exact h
        · exfalso; apply hne; rw [show i = m by omega, hm]
      obtain ⟨q, h1, h2, h3, h4⟩ := ih i him (by rw [hm]; exact hne)
      exact ⟨q, h1, by omega, h3, by rw [h4, hm]⟩
    · exact ⟨m, by omega, by omega, fun h => hm h.symm, rfl⟩

theorem exc_lag {N : Circ} {v : Nat → Nat → Bool} (R : Run N v) {D W : Nat}
    (hB : Bounded N v R D W) {j init : Nat} {pins : List Src} (hj : N.node j = .gate init pins)
    (m : Nat) (hm : D + 1 ≤ m) :
    ∃ m', m - (D + 1) ≤ m' ∧ m' < m ∧ R.exc init pins m' j = v m j := by
  apply Classical.byContradiction
  intro hno
  have hall : ∀ i, m - (D + 1) ≤ i → i ≤ m - (D + 1) + D → R.exc init pins i j = !(v m j) := by
    intro i h1 h2
    have : R.exc init pins i j ≠ v m j := fun h => hno ⟨i, h1, by omega, h⟩
    cases h : R.exc init pins i j <;> cases hv : v m j <;> simp_all
  obtain ⟨i, hi1, hi2, hvi⟩ := hB.gate (m - (D + 1)) j init pins (!(v m j)) hj hall
  have him : i < m := by
    rcases Nat.lt_or_ge i m with h | h
    · exact h
    · exfalso; rw [show i = m by omega] at hvi
      cases hv : v m j <;> rw [hv] at hvi <;> cases hvi
  obtain ⟨q, hq1, hq2, hq3, hq4⟩ := switch_back v j m i him (by
    rw [hvi]; cases v m j <;> decide)
  rcases R.gate q j init pins hj with h | h
  · exact hq3 h
  · apply hno
    exact ⟨q, by omega, hq2, by rw [← hq4, h]; rfl⟩

/-- Every pin that reads a node is the first pin reading it (the cell's
pin nodes are distinct, so a node value is one read). -/
def pinsOK (pins : List Src) : Bool :=
  (List.range pins.length).all fun j => match pins[j]? with
    | some (.node i) => pins.idxOf (.node i) == j
    | _ => true

theorem pinsOK_idx {pins : List Src} (h : pinsOK pins = true) {j i : Nat}
    (hj : pins[j]? = some (.node i)) : pins.idxOf (.node i) = j := by
  have hlt : j < pins.length := by
    rcases Nat.lt_or_ge j pins.length with h' | h'
    · exact h'
    · rw [List.getElem?_eq_none h'] at hj; cases hj
  have := List.all_eq_true.1 h j (List.mem_range.2 hlt)
  rw [hj] at this
  simpa using this

theorem map_srcK_eq (f : Nat → K3) (rv : Nat → Nat → Bool) :
    ∀ (L : List Src) (p0 : Nat), (∀ j i, L[j]? = some (.node i) → f i = K3.ofBool (rv (p0 + j) i)) →
      L.map (srcK f) = (pinsB rv L p0).map K3.ofBool := by
  intro L
  induction L with
  | nil => intro _ _; rfl
  | cons a as ih =>
    intro p0 h
    simp only [List.map_cons, pinsB]
    congr 1
    · cases a with
      | node i => have := h 0 i rfl; simpa [srcK, srcB] using this
      | const b => rfl
    · apply ih (p0 + 1)
      intro j i hj
      have := h (j + 1) i (by simpa using hj)
      rw [this]; congr 2; omega

section derive
variable {v : Nat → Nat → Bool} (Rn : Run gNet v)

/-- What pin `pins.idxOf (node i)` of gate `n` reads of node `i` at step `k`. -/
def rdv (pins : List Src) (n k i : Nat) : Bool := v (Rn.rd k n (pins.idxOf (.node i))) i
/-- The data reads as a `CellRun` data valuation (nodes not on a pin: `rho`). -/
def eG (pins : List Src) (n k i : Nat) : K3 :=
  if pins.contains (.node i) then K3.ofBool (rdv Rn pins n k i) else rho i
def rG (pins : List Src) (n k : Nat) : K3 := K3.ofBool (rdv Rn pins n k 0)
def qG (pins : List Src) (n k : Nat) : K3 := K3.ofBool (rdv Rn pins n k n)
/-- The root of the derived cell model: the LUT value gate `n` sees. -/
def GG (init : Nat) (pins : List Src) (n k : Nat) : K3 := K3.ofBool (Rn.exc init pins k n)

theorem tree_eq {n init : Nat} {pins : List Src} (hok : pinsOK pins = true) (k : Nat) :
    GG Rn init pins n k = cellF init pins n (eG Rn pins n k) (rG Rn pins n k) (qG Rn pins n k) := by
  unfold GG cellF Run.exc
  rw [map_srcK_eq _ (fun p i => v (Rn.rd k n p) i) pins 0, LibEndMemMlink.lutK_ofBool]
  intro j i hj
  have hidx := pinsOK_idx hok hj
  have hmem : pins.contains (.node i) = true :=
    List.contains_iff_mem.2 (List.mem_of_getElem? hj)
  unfold cin
  by_cases h0 : i = 0
  · subst h0; simp only [ite_true, rG, rdv, hidx, Nat.zero_add]
  · by_cases hn : i = n
    · subst hn; simp only [h0, ite_false, ite_true, qG, rdv, hidx, Nat.zero_add]
    · simp only [h0, hn, ite_false, eG, hmem, ite_true, rdv, hidx, Nat.zero_add]

/-- **`CellRun` from the network run.** In any bounded GMW run of `gNet`,
an rst-reading loop `n` with distinct pin nodes has a `CellRun` with root
`GG` (the LUT value it sees), feedback window `Dhi = W + D + 1`, provided
- `hs`: the release `s` is at least `W + D + 1` (so the window lies inside
  the run);
- `H_RST_PIN`: its rst pin reads 1 at every step of `[T1, s)`;
- `H_READ_STATIC`: on `[s, Tw)` every control data pin reads its reset value. -/
theorem cellRun_of_run {D W : Nat} (hB : Bounded gNet v Rn D W) {n init : Nat} {pins : List Src}
    (hg : gNode n = .gate init pins) (hok : pinsOK pins = true) {T1 s Tw : Nat}
    (hs : W + D + 1 ≤ s)
    (H_RST_PIN : ∀ t, T1 ≤ t → t < s → rdv Rn pins n t 0 = true)
    (H_READ_STATIC : ∀ t, s ≤ t → t < Tw → ∀ i, i ≠ 0 → i ≠ n → gCtl i = true →
      pins.contains (.node i) = true → rdv Rn pins n t i = gR i) :
    CellRun init pins n T1 s Tw (W + D + 1) (eG Rn pins n) (rG Rn pins n) (qG Rn pins n)
      (GG Rn init pins n) where
  H_TREE t := tree_eq Rn hok t
  H_FB_WIN t ht := by
    have hg' : gNet.node n = .gate init pins := hg
    have hw := hB.wire t n (pins.idxOf (.node n))
    have hle := Rn.rd_le t n (pins.idxOf (.node n))
    obtain ⟨m', h1, h2, h3⟩ := exc_lag Rn hB hg' (Rn.rd t n (pins.idxOf (.node n))) (by omega)
    refine ⟨t - m', by omega, by omega, by omega, ?_⟩
    unfold qG GG rdv
    rw [show t - (t - m') = m' by omega, h3]
  H_RST_HIGH t h1 h2 := by unfold rG; rw [H_RST_PIN t h1 h2]; rfl
  H_DATA_STATIC t h1 h2 i h0 hn := by
    unfold eG rho
    cases hc : pins.contains (.node i)
    · exact le_refl _
    · simp only [ite_true]
      cases hci : gCtl i
      · exact Or.inr rfl
      · simp only [ite_true]; rw [H_READ_STATIC t h1 h2 i h0 hn hci hc]; exact le_refl _

/-- The same with the first-wave phase: on `[s, Tz)` every control data pin
that is not a wave node reads its reset value. -/
theorem cellRunW_of_run {D W : Nat} (hB : Bounded gNet v Rn D W) {n init : Nat}
    {pins : List Src} (hg : gNode n = .gate init pins) (hok : pinsOK pins = true)
    {T1 s Tw Tz : Nat} (hs : W + D + 1 ≤ s)
    (H_RST_PIN : ∀ t, T1 ≤ t → t < s → rdv Rn pins n t 0 = true)
    (H_READ_STATIC : ∀ t, s ≤ t → t < Tw → ∀ i, i ≠ 0 → i ≠ n → gCtl i = true →
      pins.contains (.node i) = true → rdv Rn pins n t i = gR i)
    (H_READ_WAVE : ∀ t, s ≤ t → t < Tz → ∀ i, i ≠ 0 → i ≠ n → gCtl i = true →
      ResetGcdWave.wR i = 0 → pins.contains (.node i) = true → rdv Rn pins n t i = gR i) :
    CellRunW init pins n T1 s Tw Tz (W + D + 1) (eG Rn pins n) (rG Rn pins n) (qG Rn pins n)
      (GG Rn init pins n) where
  base := cellRun_of_run Rn hB hg hok hs H_RST_PIN H_READ_STATIC
  H_DATA_WAVE t h1 h2 i h0 hn := by
    unfold eG rhoA
    by_cases hw : ResetGcdWave.wR i ≠ 0
    · rw [ite_eq_left hw]; exact Or.inr rfl
    · rw [ite_eq_right hw]
      unfold rho
      cases hc : pins.contains (.node i)
      · exact le_refl _
      · simp only [ite_true]
        cases hci : gCtl i
        · exact Or.inr rfl
        · simp only [ite_true]
          rw [H_READ_WAVE t h1 h2 i h0 hn hci (by omega) hc]; exact le_refl _

end derive

/-! ## Part 2: the census at the first-wave vector -/

/-- Class at the first-wave vector `rhoA`: 0 not an rst reader, 1 hold,
2 forced, 3 leave, 4 combinational, 5 none (a cell that itself moves in the
first wave). -/
def vclsA (n : Nat) : Nat :=
  match gNode n with
  | .input => 0
  | .gate init pins =>
    if !(pins.contains (p 0)) then 0
    else if !(pins.contains (p n)) then 4
    else if forcBV rhoA init pins n (gR n) then 2
    else if holdBV rhoA init pins n (gR n) then 1
    else if leaveBV rhoA init pins n (gR n) then 3 else 5

/-- The 11 cells forced at the reset vector and hold at the first-wave
vector: `ufork1`, `ufork10`, `ushrsi0.ujoin`, `ushrsi1.ujoin`,
`uaddi0.ujoin`, `ufork18`, `ushrsi2.ujoin`, `ufork23`, `ushrsi3.ujoin`,
`ufork38`, `ushrsi4.ujoin`. -/
def newHoldL : List Nat := [66, 309, 311, 346, 381, 628, 718, 847, 937, 1400, 1491]
/-- The 7 rst-reading loops that are themselves first-wave nodes:
`ucond_br9_j`, `ucond_br10_j`, `ucond_br11_j` (B34), `ufork11`, `ufork19`,
`ufork24`, `ufork39` (B4). -/
def movL : List Nat := [99, 103, 107, 310, 629, 848, 1401]

/-- CElemStrict2's reset race facts at the end-of-wave vector `rhoA1`. -/
def exactBA (init : Nat) (pins : List Src) (n : Nat) (b : Bool) : Bool :=
  CElemStrict2.rstB (cellF init pins n rhoA1) (K3.ofBool (!b)) b &&
    CElemStrict2.rstB (cellF init pins n rhoA1) .x b

/-- The least `wR - 1` over the cell's first-wave data pins (1000 if none). -/
def dminP (n : Nat) : List Src → Nat
  | [] => 1000
  | .node i :: ps =>
    if i ≠ 0 ∧ i ≠ n ∧ ResetGcdWave.wR i ≠ 0 then min (ResetGcdWave.wR i - 1) (dminP n ps)
    else dminP n ps
  | .const _ :: ps => dminP n ps

theorem dminP_le (n : Nat) : ∀ (ps : List Src) (i : Nat), Src.node i ∈ ps → i ≠ 0 → i ≠ n →
    ResetGcdWave.wR i ≠ 0 → dminP n ps ≤ ResetGcdWave.wR i - 1 := by
  intro ps
  induction ps with
  | nil => intro i h; cases h
  | cons a ps ih =>
    intro i hm h0 hn hw
    rcases List.mem_cons.1 hm with h | h
    · subst h; simp only [dminP]; rw [ite_eq_left ⟨h0, hn, hw⟩]; exact Nat.min_le_left _ _
    · cases a with
      | node j =>
        simp only [dminP]
        by_cases hj : j ≠ 0 ∧ j ≠ n ∧ ResetGcdWave.wR j ≠ 0
        · rw [ite_eq_left hj]; exact Nat.le_trans (Nat.min_le_right _ _) (ih i h h0 hn hw)
        · rw [ite_eq_right hj]; exact ih i h h0 hn hw
      | const b => exact ih i h h0 hn hw

theorem waveIn_of {n init : Nat} {pins : List Src} (hg : gNode n = .gate init pins) {i : Nat}
    (hm : Src.node i ∈ pins) (h0 : i ≠ 0) (hn : i ≠ n) (hw : ResetGcdWave.wR i ≠ 0) :
    waveIn n = true := by
  simp only [waveIn, hg, List.any_eq_true]
  exact ⟨.node i, hm, by simp [h0, hn, hw]⟩

/-- Everything checked per node. -/
def vecA (n : Nat) : Bool :=
  match gNode n with
  | .input => !newHoldL.contains n && !movL.contains n
  | .gate init pins =>
    if pins.contains (p 0) && pins.contains (p n) then
      pinsOK pins &&
        ((vclsA n == 1) == ((holdL.contains n && !movL.contains n) || newHoldL.contains n)) &&
        ((vclsA n == 3) == frontierL.contains n) && ((vclsA n == 5) == movL.contains n) &&
        (!newHoldL.contains n || (forcB init pins n (gR n) && exactBA init pins n (gR n)))
    else !newHoldL.contains n && !movL.contains n

def chunkA (lo k : Nat) : Bool := (List.range' lo k).all vecA

theorem chunkA_mem {lo k : Nat} (h : chunkA lo k = true) {n : Nat} (h1 : lo ≤ n)
    (h2 : n < lo + k) : vecA n = true :=
  List.all_eq_true.1 h n (List.mem_range'_1.2 ⟨h1, h2⟩)

theorem ca0 : chunkA 0 400 = true := by decide +kernel
theorem ca1 : chunkA 400 400 = true := by decide +kernel
theorem ca2 : chunkA 800 400 = true := by decide +kernel
theorem ca3 : chunkA 1200 400 = true := by decide +kernel
theorem ca4 : chunkA 1600 400 = true := by decide +kernel
theorem ca5 : chunkA 2000 400 = true := by decide +kernel
theorem ca6 : chunkA 2400 400 = true := by decide +kernel
theorem ca7 : chunkA 2800 400 = true := by decide +kernel
theorem ca8 : chunkA 3200 122 = true := by decide +kernel

theorem all_vecA (n : Nat) (h : n < gM) : vecA n = true := by
  have hM : gM = 3322 := rfl
  by_cases h0 : n < 400
  · exact chunkA_mem ca0 (by omega) (by omega)
  by_cases h1 : n < 800
  · exact chunkA_mem ca1 (by omega) (by omega)
  by_cases h2 : n < 1200
  · exact chunkA_mem ca2 (by omega) (by omega)
  by_cases h3 : n < 1600
  · exact chunkA_mem ca3 (by omega) (by omega)
  by_cases h4 : n < 2000
  · exact chunkA_mem ca4 (by omega) (by omega)
  by_cases h5 : n < 2400
  · exact chunkA_mem ca5 (by omega) (by omega)
  by_cases h6 : n < 2800
  · exact chunkA_mem ca6 (by omega) (by omega)
  by_cases h7 : n < 3200
  · exact chunkA_mem ca7 (by omega) (by omega)
  exact chunkA_mem ca8 (by omega) (by omega)

/-- The per-node facts for an rst-reading loop, unpacked. -/
theorem vecA_facts {n init : Nat} {pins : List Src} (hg : gNode n = .gate init pins)
    (h0 : pins.contains (p 0) = true) (hs : pins.contains (p n) = true) :
    pinsOK pins = true ∧
      (vclsA n = 1 ↔ (n ∈ holdL ∧ n ∉ movL) ∨ n ∈ newHoldL) ∧
      (vclsA n = 3 ↔ n ∈ frontierL) ∧ (vclsA n = 5 ↔ n ∈ movL) ∧
      (n ∈ newHoldL → forcB init pins n (gR n) = true ∧ exactBA init pins n (gR n) = true) := by
  have h := all_vecA n (gate_lt hg)
  simp only [vecA, hg, h0, hs, Bool.and_self, ite_true, Bool.and_eq_true] at h
  obtain ⟨⟨⟨⟨hok, h1⟩, h3⟩, h5⟩, hn⟩ := h
  refine ⟨hok, ?_, ?_, ?_, ?_⟩
  · have := h1; simp only [beq_iff_eq] at this
    rw [← List.contains_iff_mem, ← List.contains_iff_mem, ← List.contains_iff_mem]
    cases hv : decide (vclsA n = 1) <;> cases a : holdL.contains n <;>
      cases b : movL.contains n <;> cases c : newHoldL.contains n <;> simp_all
  · rw [← List.contains_iff_mem]
    cases hv : decide (vclsA n = 3) <;> cases a : frontierL.contains n <;> simp_all
  · rw [← List.contains_iff_mem]
    cases hv : decide (vclsA n = 5) <;> cases a : movL.contains n <;> simp_all
  · intro hm
    have hc : newHoldL.contains n = true := List.contains_iff_mem.2 hm
    simp only [hc, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hn
    exact hn

/-- The 21 rst-reading loops with a first-wave data pin, and their `dminP`. -/
def wcL : List Nat := [66, 99, 103, 107, 309, 310, 311, 346, 381, 628, 629, 630, 718, 847, 848,
  849, 937, 1400, 1401, 1402, 1491]
def pinsOf (n : Nat) : List Src := match gNode n with | .gate _ pins => pins | .input => []

/-- **The census at the first-wave vector.** Of the 414 rst-reading loops:
203 hold, 194 forced, 10 leave (the frontier), 7 moving. The 21 loops with a
first-wave data pin are `wcL`, with least `wR - 1` over those pins
(`dminP`): 2 for `ufork1`, 32 for the three steer joins, 3 for the
`ufork10/18/23/38` (they read a moving fork), 2 for the moving forks, 1 for
every cell that reads a frontier link controller. -/
theorem vec2_census :
    [1, 2, 3, 5].map (fun c => rstL.countP (fun n => vclsA n == c)) = [203, 194, 10, 7] ∧
    rstL.filter (fun n => vclsA n != 4 && waveIn n) = wcL ∧
    wcL.map (fun n => dminP n (pinsOf n)) =
      [2, 32, 32, 32, 3, 2, 1, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1, 3, 2, 1, 1] ∧
    newHoldL.all (fun n => vcls n == 2) = true ∧ movL.all (fun n => holdL.contains n || vcls n == 2) = true := by
  decide +kernel

/-! ## A first-wave node cannot move early -/

/-- The early-hold state for a node of wave rank `r`: rst at 1 if `r ≤ 2`,
a wave node `i` at its reset value if `r ≤ wR i + 1`, every other control
node at its reset value, everything else `x`. -/
def eSt (r i : Nat) : K3 :=
  if i = 0 then (if r ≤ 2 then .t else .x)
  else if ResetGcdWave.wR i ≠ 0 then (if r ≤ ResetGcdWave.wR i + 1 then K3.ofBool (gR i) else .x)
  else if gCtl i then K3.ofBool (gR i) else .x

def earlyOK : Bool := ResetGcdWave.wL.all fun q => q.1 == 0 ||
  match gNode q.1 with
  | .gate init pins =>
    decide (lutK init (pins.map (srcK (eSt (ResetGcdWave.wR q.1)))) = K3.ofBool (gR q.1))
  | .input => false

theorem earlyOK_true : earlyOK = true := by decide +kernel

theorem early_node {w : Nat} (hw : ResetGcdWave.wR w ≠ 0) (h0 : w ≠ 0) :
    ∃ init pins, gNode w = .gate init pins ∧
      lutK init (pins.map (srcK (eSt (ResetGcdWave.wR w)))) = K3.ofBool (gR w) := by
  obtain ⟨q, hq, he, _, _⟩ := ResetGcdWave.wq hw
  have h := List.all_eq_true.1 earlyOK_true q hq
  rw [he] at h
  have h0' : (w == 0) = false := by simp [h0]
  rw [h0', Bool.false_or] at h
  cases hn : gNode w with
  | input => rw [hn] at h; cases h
  | gate init pins => rw [hn] at h; exact ⟨init, pins, rfl, of_decide_eq_true h⟩

/-- **Early hold.** In a run with wires at most `W` old, with every control
node at its reset value on `[S - W, S]`, the rst source 1 on `[S - W, F]`,
and every control node outside the wave certificate at its reset value on
`[S - W, T]`: a wave node `w` is at its reset value at every step
`k ≤ min T (F + wR w - 1)`. (`wR w - 1` steps after rst is last 1: the
frontier controllers at `F + 1`, `ucmpi0.udly.g[29]` at `F + 32`.) -/
theorem wave_early {v : Nat → Nat → Bool} (Rn : Run gNet v) {W : Nat}
    (H_WIRE_BOUND : ∀ k j p, k ≤ Rn.rd k j p + W) (S F T : Nat)
    (H_SETTLED : ∀ k n, k ≤ S → S ≤ k + W → gCtl n = true → n ≠ 0 → v k n = gR n)
    (H_RST_HIGH : ∀ k, S ≤ k + W → k ≤ F → v k 0 = true)
    (H_NW_QUIET : ∀ k i, S ≤ k + W → k ≤ T → gCtl i = true → ResetGcdWave.wR i = 0 → i ≠ 0 →
      v k i = gR i) :
    ∀ k w, S ≤ k + W → k ≤ T → ResetGcdWave.wR w ≠ 0 → w ≠ 0 →
      k + 1 ≤ F + ResetGcdWave.wR w → v k w = gR w := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro w h1 h2 hw h0 h3
    have hc := (ResetGcdWave.wq_shape hw).2.2.1
    by_cases hk : k ≤ S
    · exact H_SETTLED k w hk h1 hc h0
    obtain ⟨j, rfl⟩ : ∃ j, k = j + 1 := ⟨k - 1, by omega⟩
    obtain ⟨init, pins, hg, hchk⟩ := early_node hw h0
    have hg' : gNet.node w = .gate init pins := hg
    rcases Rn.gate j w init pins hg' with h | h
    · rw [h]; exact ih j (by omega) w (by omega) (by omega) hw h0 (by omega)
    · rw [h]
      have hs := lutK_sound init (pins_forall2 (eSt (ResetGcdWave.wR w))
        (fun p i => v (Rn.rd j w p) i) ?_ pins 0)
      · rw [hchk] at hs; exact (admits_ofBool_iff _ _).1 hs
      intro q i
      have r1 := Rn.rd_le j w q
      have r2 := H_WIRE_BOUND j w q
      unfold eSt
      by_cases hi : i = 0
      · subst hi; rw [ite_eq_left rfl]
        by_cases hr : ResetGcdWave.wR w ≤ 2
        · rw [ite_eq_left hr, H_RST_HIGH _ (by omega) (by omega)]; rfl
        · rw [ite_eq_right hr]; rfl
      · rw [ite_eq_right hi]
        by_cases hwi : ResetGcdWave.wR i ≠ 0
        · rw [ite_eq_left hwi]
          by_cases hr : ResetGcdWave.wR w ≤ ResetGcdWave.wR i + 1
          · rw [ite_eq_left hr, ih _ (by omega) i (by omega) (by omega) hwi hi (by omega)]
            exact admits_ofBool _
          · rw [ite_eq_right hr]; rfl
        · rw [ite_eq_right hwi]
          cases hci : gCtl i
          · rfl
          · rw [ite_eq_left rfl, H_NW_QUIET _ i (by omega) (by omega) hci (by omega) hi]
            exact admits_ofBool _

/-! ## The network instance: clean release from power-up -/

theorem hold_ge (D W : Nat) : W + D + 1 ≤ (maxRank + 2) * (D + W + 1) := by
  have : (1 : Nat) ≤ maxRank + 2 := by decide
  calc W + D + 1 = 1 * (D + W + 1) := by omega
    _ ≤ (maxRank + 2) * (D + W + 1) := Nat.mul_le_mul_right _ this

/-- No frontier controller reads a first-wave node. -/
theorem frontier_noWave : frontierL.all (fun n => !waveIn n) = true := by decide +kernel

section net
variable {v : Nat → Nat → Bool} (Rn : Run gNet v)

/-- The per-cell data horizon: the end of the segment, or for a cell with a
first-wave data pin, `F + dminP` (its wave pins cannot have moved before). -/
def twOf (F E n : Nat) (pins : List Src) : Nat :=
  if waveIn n then min (E + 1) (F + 1 + dminP n pins) else E + 1

/-- What the clean-release hypotheses give at every rst-reading loop: its
two-phase cell model, with `T1 = W + 1`, `s = F + 1`, `Tw = twOf`,
`Tz = E + 1`, `Dhi = W + D + 1`. -/
theorem cellRunW_clean {D W : Nat} (hB : Bounded gNet v Rn D W) (F E : Nat)
    (H_RST_CLEAN : ∀ k, 0 < k → k ≤ F → TernaryPhases.InputsIn gNet v gA k)
    (H_HOLD_LONG : (maxRank + 2) * (D + W + 1) + W ≤ F)
    (H_RST_LOW : ∀ k, F < k → k ≤ E → v k 0 = false)
    (H_STEER_HOLD : ∀ k z, z ∈ ResetGcdWave.zL → F + 34 < k → k ≤ E → v k z = false)
    {n init : Nat} {pins : List Src} (hg : gNode n = .gate init pins) (hok : pinsOK pins = true) :
    CellRunW init pins n (W + 1) (F + 1) (twOf F E n pins) (E + 1) (W + D + 1)
      (eG Rn pins n) (rG Rn pins n) (qG Rn pins n) (GG Rn init pins n) := by
  have hpos : 0 < (maxRank + 2) * (D + W + 1) := Nat.mul_pos (by decide) (by omega)
  have hge := hold_ge D W
  have hset : ∀ k m, (maxRank + 2) * (D + W + 1) ≤ k → k ≤ F → gCtl m = true → v k m = gR m :=
    fun k m h1 h2 hc => gcd_reset_binary Rn hB F H_RST_CLEAN m hc k h1 h2
  have hsrc : ∀ k, 0 < k → k ≤ F → v k 0 = true := fun k h1 h2 =>
    (admits_ofBool_iff true _).1 (H_RST_CLEAN k h1 h2 0 (by show gNode 0 = .input; rfl))
  have hA := (ResetGcdWave.gcd_clean_release Rn hB F E H_RST_CLEAN H_HOLD_LONG H_RST_LOW
    H_STEER_HOLD).1
  have hNW : ∀ k i, F ≤ k + W → k ≤ E → gCtl i = true → ResetGcdWave.wR i = 0 →
      v k i = gR i := by
    intro k i h1 h2 hc hw
    have := hA k h1 h2 i
    simp only [ResetGcdWave.sA, hw, hc, ne_eq, not_true_eq_false, ite_false, ite_true] at this
    exact (admits_ofBool_iff _ _).1 this
  have hE := wave_early Rn hB.wire F F E
    (fun k m h1 h2 hc _ => hset k m (by omega) h1 hc)
    (fun k h1 h2 => hsrc k (by omega) h2)
    (fun k i h1 h2 hc hw _ => hNW k i h1 h2 hc hw)
  apply cellRunW_of_run Rn hB hg hok (by omega)
  · intro t h1 h2
    have := Rn.rd_le t n (pins.idxOf (.node 0)); have := hB.wire t n (pins.idxOf (.node 0))
    exact hsrc _ (by omega) (by omega)
  · intro t h1 h2 i h0 hn hc hm
    have r1 := Rn.rd_le t n (pins.idxOf (.node i)); have r2 := hB.wire t n (pins.idxOf (.node i))
    have hte : t ≤ E := by unfold twOf at h2; split at h2 <;> omega
    unfold rdv
    by_cases hw : ResetGcdWave.wR i = 0
    · exact hNW _ i (by omega) (by omega) hc hw
    · have hmem : Src.node i ∈ pins := List.contains_iff_mem.1 hm
      have hwi := waveIn_of hg hmem h0 hn hw
      have hd := dminP_le n pins i hmem h0 hn hw
      simp only [twOf, hwi, ite_true] at h2
      exact hE _ i (by omega) (by omega) hw h0 (by omega)
  · intro t h1 h2 i h0 hn hc hw _
    have r1 := Rn.rd_le t n (pins.idxOf (.node i)); have r2 := hB.wire t n (pins.idxOf (.node i))
    exact hNW _ i (by omega) (by omega) hc hw

theorem ofBool_inj {a b : Bool} (h : K3.ofBool a = K3.ofBool b) : a = b := by
  cases a <;> cases b <;> first | rfl | cases h

/-- **gcd_hw's reset loops from the network model, no per-cell assumption.**
Every bounded GMW run of `gNet` from ANY power-up state with a clean rst
(1 on `(0, F]`, `F ≥ 23(D+W+1) + W`, 0 on `(F, E]`), data arbitrary, and
`E` before the first loop request (steers 0 on `(F + 34, E]`; before that
it is a theorem). For every one of the 414 rst-reading LUT loops `n`, the
LUT value it sees (`Run.exc`):
* is its reset value at every step of `[W + 1, E]`, if `n` is neither a
  frontier controller nor one of the 7 moving cells (397 cells; this covers
  the 14 non-moving first-wave cells through the WHOLE first wave);
* is its reset value on `[W + 1, min E (F + dminP n)]` for the 7 moving cells
  (`F + 32` for the three steer joins);
* for the 10 frontier controllers: its reset value on `[W + 1, F]` and the
  other value at every step of `(F, E]` at which its rst pin reads 0.
`H_RST_LONG` is not assumed anywhere: it follows from `H_HOLD_LONG`. -/
theorem gcd_reset_vec_net {D W : Nat} (hB : Bounded gNet v Rn D W) (F E : Nat)
    (H_RST_CLEAN : ∀ k, 0 < k → k ≤ F → TernaryPhases.InputsIn gNet v gA k)
    (H_HOLD_LONG : (maxRank + 2) * (D + W + 1) + W ≤ F)
    (H_RST_LOW : ∀ k, F < k → k ≤ E → v k 0 = false)
    (H_STEER_HOLD : ∀ k z, z ∈ ResetGcdWave.zL → F + 34 < k → k ≤ E → v k z = false) :
    ∀ n init pins, gNode n = .gate init pins → pins.contains (p 0) = true →
      pins.contains (p n) = true →
      (n ∉ frontierL → n ∉ movL → ∀ t, W + 1 ≤ t → t ≤ E → Rn.exc init pins t n = gR n) ∧
      (n ∈ movL → ∀ t, W + 1 ≤ t → t ≤ E → t ≤ F + dminP n pins →
        Rn.exc init pins t n = gR n) ∧
      (n ∈ frontierL → (∀ t, W + 1 ≤ t → t ≤ F → Rn.exc init pins t n = gR n) ∧
        ∀ t, F < t → t ≤ E → rdv Rn pins n t 0 = false → Rn.exc init pins t n = !gR n) := by
  intro n init pins hg h0 hs
  obtain ⟨hok, hA1, hA3, hA5, _⟩ := vecA_facts hg h0 hs
  obtain ⟨_, hf, h5, hhold, hlv, _⟩ := vec_facts hg h0 hs
  have C := cellRunW_clean Rn hB F E H_RST_CLEAN H_HOLD_LONG H_RST_LOW H_STEER_HOLD hg hok
  have hpos : 0 < (maxRank + 2) * (D + W + 1) := Nat.mul_pos (by decide) (by omega)
  have hlong : W + 1 + (W + D + 1) ≤ F + 1 := by have := hold_ge D W; omega
  have hvA : vclsA n = (if forcBV rhoA init pins n (gR n) then 2
      else if holdBV rhoA init pins n (gR n) then 1
      else if leaveBV rhoA init pins n (gR n) then 3 else 5) := by
    simp only [vclsA, hg, h0, hs, Bool.not_true]; rfl
  have hv : vcls n = (if forcB init pins n (gR n) then 2
      else if holdB init pins n (gR n) then 1
      else if leaveB init pins n (gR n) then 3 else 5) := by
    simp only [vcls, hg, h0, hs, Bool.not_true]; rfl
  have conv : ∀ t, GG Rn init pins n t = K3.ofBool (gR n) → Rn.exc init pins t n = gR n :=
    fun t h => ofBool_inj h
  refine ⟨fun hnf hnm t h1 h2 => conv t ?_, fun hm t h1 h2 h3 => conv t ?_, fun hfr => ⟨?_, ?_⟩⟩
  · -- non-moving, non-frontier: forced or hold at rhoA
    by_cases hF : forcBV rhoA init pins n (gR n) = true
    · exact forcedA_clean hf hF C t h1 (by omega)
    · by_cases hH : holdBV rhoA init pins n (gR n) = true
      · exact holdA_clean hf hH C (Or.inl hlong) t h1 (by omega)
      · exfalso
        by_cases hL : leaveBV rhoA init pins n (gR n) = true
        · exact hnf (hA3.1 (by rw [hvA]; simp [hF, hH, hL]))
        · exact hnm (hA5.1 (by rw [hvA]; simp [hF, hH, hL]))
  · -- moving: hold or forced at rho, up to twOf
    have htw : t < twOf F E n pins := by
      unfold twOf; split <;> omega
    by_cases hF : forcB init pins n (gR n) = true
    · exact forced_clean' hf hF C.base t h1 htw
    · by_cases hH : holdB init pins n (gR n) = true
      · exact hold_clean hf hH C.base hlong t h1 htw
      · exfalso
        have hnf : n ∉ frontierL := fun h => by
          have := hA3.2 h; have := hA5.2 hm; omega
        by_cases hL : leaveB init pins n (gR n) = true
        · exact hnf (hlv.1 (by rw [hv]; simp [hF, hH, hL]))
        · exact h5 (by rw [hv]; simp [hF, hH, hL])
  · intro t h1 h2
    have hL : leaveB init pins n (gR n) = true := by
      have h3 := hlv.2 hfr
      cases hF : forcB init pins n (gR n) <;> cases hH : holdB init pins n (gR n) <;>
        cases hL : leaveB init pins n (gR n) <;> simp_all
    exact conv t ((leave_clean hf hL C.base).1 t h1 (by omega))
  · intro t h1 h2 hr
    have hL : leaveB init pins n (gR n) = true := by
      have h3 := hlv.2 hfr
      cases hF : forcB init pins n (gR n) <;> cases hH : holdB init pins n (gR n) <;>
        cases hL : leaveB init pins n (gR n) <;> simp_all
    have hnw : waveIn n = false := by
      have := List.all_eq_true.1 frontier_noWave n hfr
      simpa using this
    have htw : t < twOf F E n pins := by
      simp only [twOf, hnw, Bool.false_eq_true, ite_false]; omega
    have := (leave_clean hf hL C.base).2 t (by omega) htw (by unfold rG; rw [hr]; rfl)
    exact ofBool_inj this

end net

/-! ## `ResetGcdVec.gcd_reset_vec`, instantiated from the network -/

section netvec
variable {v : Nat → Nat → Bool} (Rn : Run gNet v)

def eN (n : Nat) : Nat → Nat → K3 := match gNode n with
  | .gate _ pins => eG Rn pins n | .input => fun _ _ => .x
def rN (n : Nat) : Nat → K3 := match gNode n with
  | .gate _ pins => rG Rn pins n | .input => fun _ => .x
def qN (n : Nat) : Nat → K3 := match gNode n with
  | .gate _ pins => qG Rn pins n | .input => fun _ => .x
def GN (n : Nat) : Nat → K3 := match gNode n with
  | .gate init pins => GG Rn init pins n | .input => fun _ => .x
def twN (F E n : Nat) : Nat := match gNode n with
  | .gate _ pins => twOf F E n pins | .input => 0

/-- **Brst's composition holds in the network model.** Under the clean-release
hypotheses, `ResetGcdVec.gcd_reset_vec` applies with every `H_CELL`
discharged by `cellRunW_clean` and every `H_RST_LONG` by `H_HOLD_LONG`
(`T1 = W + 1`, `s = F + 1`, `Dhi = W + D + 1`, `Tw = twOf`). -/
theorem gcd_reset_vec_of_net {D W : Nat} (hB : Bounded gNet v Rn D W) (F E : Nat)
    (H_RST_CLEAN : ∀ k, 0 < k → k ≤ F → TernaryPhases.InputsIn gNet v gA k)
    (H_HOLD_LONG : (maxRank + 2) * (D + W + 1) + W ≤ F)
    (H_RST_LOW : ∀ k, F < k → k ≤ E → v k 0 = false)
    (H_STEER_HOLD : ∀ k z, z ∈ ResetGcdWave.zL → F + 34 < k → k ≤ E → v k z = false) :
    ∀ n init pins, gNode n = .gate init pins → pins.contains (p 0) = true →
      pins.contains (p n) = true →
      (∀ t, W + 1 ≤ t → t < F + 1 → GN Rn n t = K3.ofBool (gR n)) ∧
      (n ∉ frontierL → ∀ t, W + 1 ≤ t → t < twN F E n → GN Rn n t = K3.ofBool (gR n)) ∧
      (n ∈ frontierL → ∀ t, F + 1 ≤ t → t < twN F E n → rN Rn n t = .f →
        GN Rn n t = K3.ofBool (!gR n)) := by
  apply gcd_reset_vec (T1 := fun _ => W + 1) (s := fun _ => F + 1) (Dhi := fun _ => W + D + 1)
    (Tw := twN F E) (e := eN Rn) (r := rN Rn) (qp := qN Rn) (G := GN Rn)
  · intro n init pins hg h0 hs
    have hok := (vecA_facts hg h0 hs).1
    have C := (cellRunW_clean Rn hB F E H_RST_CLEAN H_HOLD_LONG H_RST_LOW H_STEER_HOLD hg hok).base
    simp only [eN, rN, qN, GN, twN, hg]
    exact C
  · intro n _
    have := hold_ge D W; omega

end netvec

/-! ## The 21 first-wave cells -/

/-- **The 11 new hold cells: the width condition is exact at the moved
vector.** If a cell of `newHoldL` is released after its first-wave data pin
has risen (vector `rhoA1`), CElemStrict2's `reset_width_iff` holds for its
real LUT there: every behaviour is safe iff `Dhi + wa ≤ P`. -/
theorem newHold_exact {n init : Nat} {pins : List Src} (hg : gNode n = .gate init pins)
    (h0 : pins.contains (p 0) = true) (hs : pins.contains (p n) = true) (hn : n ∈ newHoldL) :
    ∀ v ∈ [K3.ofBool (!gR n), K3.x],
      CElemStrict2.FactsK (cellF init pins n rhoA1) K3.f K3.x K3.t K3.x K3.f v (gR n) ∧
      ∀ {tb wb wa Dlo Dhi P : Nat}, 1 ≤ Dlo → Dlo ≤ Dhi → wa ≤ P →
        (CElemStrict2.SafeBoxK (cellF init pins n rhoA1) K3.f K3.x K3.t K3.x K3.f v (gR n)
          tb wb wa Dlo Dhi (tb + wb + P - wa) ↔ Dhi + wa ≤ P) := by
  have hE := ((vecA_facts hg h0 hs).2.2.2.2 hn).2
  simp only [exactBA, Bool.and_eq_true] at hE
  intro v hv
  have H : CElemStrict2.FactsK (cellF init pins n rhoA1) K3.f K3.x K3.t K3.x K3.f v (gR n) := by
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hv
    rcases hv with rfl | rfl
    · exact CElemStrict2.factsK_of_B hE.1
    · exact CElemStrict2.factsK_of_B hE.2
  exact ⟨H, fun h1 h2 h3 => CElemStrict2.reset_width_iff H h1 h2 h3⟩

/-- **The per-cell composition over the whole first wave.** Every rst-reading
loop with a two-phase run `CellRunW` (its own `T1 s Tw Tz Dhi`):
* the 194 cells forced at `rhoA`: reset value on `[T1, Tz)`, no width
  condition;
* the 203 cells hold at `rhoA`: reset value on `[T1, Tz)` under
  `H_RST_LONG2` (`T1 + Dhi ≤ s`, or for the 11 `newHoldL` cells, forced at
  the reset vector, `T1 + Dhi ≤ Tw`);
* the 7 moving cells: reset value on `[T1, Tw)`, with `H_RST_LONG` at the
  three hold joins;
* the 10 frontier controllers: as in `gcd_reset_vec`. -/
theorem gcd_reset_vec2 {T1 s Tw Tz Dhi : Nat → Nat} {e : Nat → Nat → Nat → K3}
    {r qp G : Nat → Nat → K3}
    (H_CELL : ∀ n init pins, gNode n = .gate init pins → pins.contains (p 0) = true →
      pins.contains (p n) = true →
      CellRunW init pins n (T1 n) (s n) (Tw n) (Tz n) (Dhi n) (e n) (r n) (qp n) (G n))
    (H_RST_LONG2 : ∀ n, vclsA n = 1 →
      T1 n + Dhi n ≤ s n ∨ (n ∈ newHoldL ∧ T1 n + Dhi n ≤ Tw n))
    (H_RST_LONG : ∀ n, n ∈ movL → n ∈ holdL → T1 n + Dhi n ≤ s n) :
    ∀ n init pins, gNode n = .gate init pins → pins.contains (p 0) = true →
      pins.contains (p n) = true →
      (n ∉ frontierL → n ∉ movL → ∀ t, T1 n ≤ t → t < Tz n → G n t = K3.ofBool (gR n)) ∧
      (n ∈ movL → ∀ t, T1 n ≤ t → t < Tw n → G n t = K3.ofBool (gR n)) ∧
      (n ∈ frontierL → ∀ t, s n ≤ t → t < Tw n → r n t = .f →
        G n t = K3.ofBool (!gR n)) := by
  intro n init pins hg h0 hs
  have C := H_CELL n init pins hg h0 hs
  obtain ⟨_, hA1, hA3, hA5, hnew⟩ := vecA_facts hg h0 hs
  obtain ⟨_, hf, h5, hhold, hlv, _⟩ := vec_facts hg h0 hs
  have hvA : vclsA n = (if forcBV rhoA init pins n (gR n) then 2
      else if holdBV rhoA init pins n (gR n) then 1
      else if leaveBV rhoA init pins n (gR n) then 3 else 5) := by
    simp only [vclsA, hg, h0, hs, Bool.not_true]; rfl
  have hv : vcls n = (if forcB init pins n (gR n) then 2
      else if holdB init pins n (gR n) then 1
      else if leaveB init pins n (gR n) then 3 else 5) := by
    simp only [vcls, hg, h0, hs, Bool.not_true]; rfl
  have hL : n ∈ frontierL → leaveB init pins n (gR n) = true := fun hfr => by
    have h3 := hlv.2 hfr
    cases hF : forcB init pins n (gR n) <;> cases hH : holdB init pins n (gR n) <;>
      cases hL : leaveB init pins n (gR n) <;> simp_all
  refine ⟨fun hnf hnm => ?_, fun hm => ?_, fun hfr => (leave_clean hf (hL hfr) C.base).2⟩
  · by_cases hF : forcBV rhoA init pins n (gR n) = true
    · exact forcedA_clean hf hF C
    · by_cases hH : holdBV rhoA init pins n (gR n) = true
      · have h1 : vclsA n = 1 := by rw [hvA]; simp [hF, hH]
        apply holdA_clean hf hH C
        rcases H_RST_LONG2 n h1 with h | ⟨hn, h⟩
        · exact Or.inl h
        · exact Or.inr ⟨(hnew hn).1, h⟩
      · exfalso
        by_cases hL' : leaveBV rhoA init pins n (gR n) = true
        · exact hnf (hA3.1 (by rw [hvA]; simp [hF, hH, hL']))
        · exact hnm (hA5.1 (by rw [hvA]; simp [hF, hH, hL']))
  · by_cases hF : forcB init pins n (gR n) = true
    · exact forced_clean' hf hF C.base
    · by_cases hH : holdB init pins n (gR n) = true
      · have h1 : vcls n = 1 := by rw [hv]; simp [hF, hH]
        exact hold_clean hf hH C.base (H_RST_LONG n hm (hhold.1 h1))
      · exfalso
        have hnf : n ∉ frontierL := fun h => by
          have := hA3.2 h; have := hA5.2 hm; omega
        by_cases hL' : leaveB init pins n (gR n) = true
        · exact hnf (hlv.1 (by rw [hv]; simp [hF, hH, hL']))
        · exact h5 (by rw [hv]; simp [hF, hH, hL'])

/-- **When the 21 first-wave cells are released, relative to their data.**
Every bounded run in Rst3's first-wave segment (control at reset on
`[S - W, S]`, the rst source 1 on `[S - W, F]` and 0 on `(F, E]`, steers 0 on
`(S, E]`): for every rst-reading loop `n` with pins `pins`,
* every control data pin reads its reset value at every step
  `t ∈ [S, min E (F + dminP n pins)]`;
* its rst pin reads 0 at every step of `(F + W, E]`.
So if `W < dminP n pins` the cell's rst pin is 0 for good before any of its
data pins can read a moved value (`dminP` is 32 for the three steer joins,
2 or 3 for the forks, 1 for the cells that read a frontier controller:
`vec2_census`). `counter_uori2` and `counter_br9` show the bound is exact for
`uori2.ujoin` and `ucond_br9_j`. -/
theorem wave_cells_order {v : Nat → Nat → Bool} (Rn : Run gNet v) {D W : Nat}
    (hB : Bounded gNet v Rn D W) (S F E : Nat) (hSF : S ≤ F)
    (H_SETTLED : ∀ k n, k ≤ S → S ≤ k + W → gCtl n = true → n ≠ 0 → v k n = gR n)
    (H_RST_HIGH : ∀ k, S ≤ k + W → k ≤ F → v k 0 = true)
    (H_RST_LOW : ∀ k, F < k → k ≤ E → v k 0 = false)
    (H_STEER_HOLD : ∀ k z, z ∈ ResetGcdWave.zL → S < k → k ≤ E → v k z = false)
    (n : Nat) (pins : List Src) :
    (∀ t, S ≤ t → t ≤ E → t ≤ F + dminP n pins → ∀ i, i ≠ 0 → i ≠ n → gCtl i = true →
      Src.node i ∈ pins → rdv Rn pins n t i = gR i) ∧
    (∀ t, F + W < t → t ≤ E → rdv Rn pins n t 0 = false) := by
  have hNW : ∀ k i, S ≤ k + W → k ≤ E → gCtl i = true → ResetGcdWave.wR i = 0 → i ≠ 0 →
      v k i = gR i := by
    intro k i h1 h2 hc hw h0
    by_cases hk : k ≤ S
    · exact H_SETTLED k i hk h1 hc h0
    · exact ResetGcdWave.gcd_wave_only Rn hB S F E hSF H_SETTLED
        (fun k h1 h2 => H_RST_LOW k h1 h2) H_STEER_HOLD k i (by omega) h2 hc hw
  have hE := wave_early Rn hB.wire S F E H_SETTLED H_RST_HIGH hNW
  refine ⟨fun t h1 h2 h3 i h0 hn hc hm => ?_, fun t h1 h2 =>
    ResetGcdWave.rst_reads_low Rn hB F E H_RST_LOW t n _ h1 h2⟩
  have r1 := Rn.rd_le t n (pins.idxOf (.node i)); have r2 := hB.wire t n (pins.idxOf (.node i))
  unfold rdv
  by_cases hw : ResetGcdWave.wR i = 0
  · exact hNW _ i (by omega) (by omega) hc hw h0
  · have hd := dminP_le n pins i hm h0 hn hw
    exact hE _ i (by omega) (by omega) hw h0 (by omega)

/-! ## Exactness of `W < dminP`: counter-runs -/

section counter
variable (cs : List Nat) (nT pr W F T0 : Nat)

/-- The prefix of the counter-run: rst falls after `F`; chain node `cs[i]`
rises at step `F + 2 + i` (one step per gate after rst was last 1); every
other node holds its reset value (allowed: gates may be slow, `D = T0`). -/
def pre (k i : Nat) : Bool :=
  if i = 0 then decide (k ≤ F)
  else if cs.contains i then decide (F + 2 + cs.idxOf i ≤ k) else gR i
def inpC (m i : Nat) : Bool := pre cs F (m + T0) i
/-- The counter-run: the prefix up to `T0`, then the unit-delay simulation. -/
def cv (k i : Nat) : Bool :=
  if k ≤ T0 then pre cs F k i else simB gNet (inpC cs F T0) (pre cs F T0) (k - T0) i
/-- Read times: unit, except that pin `pr` of cell `nT` (its rst pin) is `W`
steps old on `[W, T0)`. -/
def crd (k j q : Nat) : Nat := if j = nT ∧ q = pr ∧ W ≤ k ∧ k < T0 then k - W else k

/-- The chain certificate: at its switch step each chain node's LUT value is 1. -/
def updOK : Bool := cs.all fun j => match gNode j with
  | .gate init pins =>
    lutB init (pinsB (fun q i => cv cs F T0 (crd nT pr W T0 (F + 1 + cs.idxOf j) j q) i) pins 0)
  | .input => false

theorem cv_ge {k : Nat} (h : T0 ≤ k) (i : Nat) :
    cv cs F T0 k i = simB gNet (inpC cs F T0) (pre cs F T0) (k - T0) i := by
  unfold cv
  by_cases hk : k ≤ T0
  · rw [ite_eq_left hk, show k - T0 = 0 by omega, show k = T0 by omega]; rfl
  · rw [ite_eq_right hk]

theorem cv_step {k j init : Nat} {pins : List Src} (h : T0 ≤ k) (hj : gNode j = .gate init pins) :
    cv cs F T0 (k + 1) j =
      lutB init (pinsB (fun q i => cv cs F T0 (crd nT pr W T0 k j q) i) pins 0) := by
  rw [cv_ge cs F T0 (by omega), show k + 1 - T0 = (k - T0) + 1 by omega]
  have hj' : gNet.node j = .gate init pins := hj
  have e1 : (fun q i => cv cs F T0 (crd nT pr W T0 k j q) i) =
      (fun _ i => simB gNet (inpC cs F T0) (pre cs F T0) (k - T0) i) := by
    funext q i
    have : crd nT pr W T0 k j q = k := by unfold crd; rw [ite_eq_right (by omega)]
    rw [this, cv_ge cs F T0 h]
  rw [e1]
  show (match gNet.node j with
    | .input => inpC cs F T0 (k - T0 + 1) j
    | .gate init pins => lutB init (pinsB (fun _ i => simB gNet (inpC cs F T0) (pre cs F T0)
        (k - T0) i) pins 0)) = _
  rw [hj']

def cRun (h : updOK cs nT pr W F T0 = true) : Run gNet (cv cs F T0) where
  rd := crd nT pr W T0
  rd_le k j q := by unfold crd; split <;> omega
  gate k j init pins hj := by
    have hj' : gNode j = .gate init pins := hj
    by_cases hk : k < T0
    · have hj0 : j ≠ 0 := by intro h0; subst h0; cases hj'
      have e1 : cv cs F T0 (k + 1) j = pre cs F (k + 1) j := by
        unfold cv; rw [ite_eq_left (by omega)]
      have e2 : cv cs F T0 k j = pre cs F k j := by unfold cv; rw [ite_eq_left (by omega)]
      rw [e1, e2]
      unfold pre
      rw [ite_eq_right hj0, ite_eq_right hj0]
      by_cases hc : cs.contains j = true
      · rw [ite_eq_left hc, ite_eq_left hc]
        by_cases hsw : k + 1 = F + 2 + cs.idxOf j
        · right
          have hu := List.all_eq_true.1 h j (List.contains_iff_mem.1 hc)
          rw [hj'] at hu
          rw [show k = F + 1 + cs.idxOf j by omega]
          simp only [show F + 2 + cs.idxOf j ≤ F + 1 + cs.idxOf j + 1 by omega, decide_true]
          exact hu.symm
        · left
          by_cases h1 : F + 2 + cs.idxOf j ≤ k
          · simp [h1, show F + 2 + cs.idxOf j ≤ k + 1 by omega]
          · simp [h1, show ¬ F + 2 + cs.idxOf j ≤ k + 1 by omega]
      · rw [ite_eq_right hc, ite_eq_right hc]; left; rfl
    · right; exact cv_step cs nT pr W F T0 (by omega) hj'

theorem cBounded (h : updOK cs nT pr W F T0 = true) :
    Bounded gNet (cv cs F T0) (cRun cs nT pr W F T0 h) T0 W where
  wire k j q := by show k ≤ crd nT pr W T0 k j q + W; unfold crd; split <;> omega
  gate k j init pins b hj hexc := by
    have hj' : gNode j = .gate init pins := hj
    by_cases hk : T0 ≤ k
    · refine ⟨k + 1, by omega, by omega, ?_⟩
      rw [cv_step cs nT pr W F T0 hk hj', ← hexc k (Nat.le_refl _) (by omega)]; rfl
    · refine ⟨T0 + 1, by omega, by omega, ?_⟩
      rw [cv_step cs nT pr W F T0 (Nat.le_refl _) hj', ← hexc T0 (by omega) (by omega)]; rfl

theorem c_settled (hc : cs.all (fun j => !gR j) = true) {S : Nat} (hS : S < F + 2) (hST : S ≤ T0) :
    ∀ k n, k ≤ S → S ≤ k + W → gCtl n = true → n ≠ 0 → cv cs F T0 k n = gR n := by
  intro k n h1 _ _ h0
  by_cases hk : k ≤ T0
  · unfold cv pre; rw [ite_eq_left hk, ite_eq_right h0]
    by_cases hm : cs.contains n = true
    · rw [ite_eq_left hm]
      have := List.all_eq_true.1 hc n (List.contains_iff_mem.1 hm)
      simp only [Bool.not_eq_true'] at this
      rw [this]; simp; omega
    · rw [ite_eq_right hm]
  · omega

theorem c_rst : ∀ k, k ≤ T0 → cv cs F T0 k 0 = decide (k ≤ F) := by
  intro k hk; unfold cv pre; rw [ite_eq_left hk, ite_eq_left rfl]

theorem c_steer (hz : ResetGcdWave.zL.all (fun z => !cs.contains z && z != 0 && !gR z) = true) :
    ∀ k z, z ∈ ResetGcdWave.zL → k ≤ T0 → cv cs F T0 k z = false := by
  intro k z hzm hk
  have := List.all_eq_true.1 hz z hzm
  simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at this
  obtain ⟨⟨h1, h2⟩, h3⟩ := this
  unfold cv pre; rw [ite_eq_left hk, ite_eq_right h2, h1]; simpa using h3

end counter

def pins630 : List Src := [p 2357, p 2439, p 2364, p 627, p 630, p 0]
theorem node630 : gNode 630 = .gate I_c4 pins630 := rfl

theorem upd630 : updOK [2439] 630 5 1 2 4 = true := by decide +kernel

/-- **Exactness of `W < dminP` at `uori2.ujoin`** (node 630, bd_c4, reads
the frontier controller `ulink_n68__1`, `dminP = 1`). A bounded run
(`D = 4`, `W = 1`) meeting every hypothesis of `wave_cells_order` (control
at reset on `[1, 2]`, rst 1 up to `F = 2` and 0 on `(2, 4]`, steers 0) in
which the cell's rst pin reads 1 at EVERY step before step 4, while at step
4 its pin on `ulink_n68__1` already reads the moved value 1: the data pin
moves no later than the cell's release. With `W = dminP = 1` the cell is
not released before its data. -/
theorem counter_uori2 :
    ∃ (v : Nat → Nat → Bool) (Rn : Run gNet v), Bounded gNet v Rn 4 1 ∧
      (∀ k n, k ≤ 2 → 2 ≤ k + 1 → gCtl n = true → n ≠ 0 → v k n = gR n) ∧
      (∀ k, 2 ≤ k + 1 → k ≤ 2 → v k 0 = true) ∧ (∀ k, 2 < k → k ≤ 4 → v k 0 = false) ∧
      (∀ k z, z ∈ ResetGcdWave.zL → 2 < k → k ≤ 4 → v k z = false) ∧
      dminP 630 pins630 = 1 ∧
      (∀ t, t < 4 → rdv Rn pins630 630 t 0 = true) ∧
      rdv Rn pins630 630 4 2439 = true ∧ gR 2439 = false := by
  refine ⟨_, cRun [2439] 630 5 1 2 4 upd630, cBounded _ _ _ _ _ _ upd630,
    c_settled _ _ _ _ (by decide +kernel) (by omega) (by omega), ?_, ?_,
    fun k z hz _ hk => c_steer _ _ _ (by decide +kernel) k z hz hk, by decide +kernel, ?_, ?_,
    by decide +kernel⟩
  · intro k _ hk; rw [c_rst _ _ _ k (by omega)]; simp [hk]
  · intro k h1 hk; rw [c_rst _ _ _ k hk]; simp; omega
  · decide +kernel
  · decide +kernel

def pins99 : List Src := [p 3275, p 97, p 99, p 0, k0, k0]
theorem node99 : gNode 99 = .gate I_c2 pins99 := rfl

theorem upd99 : updOK ResetGcdWave.basePath 99 3 32 32 65 = true := by decide +kernel

/-- **Exactness of `W < dminP` at the steer join `ucond_br9_j`** (node 99,
`dminP = 32`: it reads `ucmpi0.udly.g[29]`). A bounded run (`D = 65`,
`W = 32`) meeting every hypothesis of `wave_cells_order` (control at reset
on `[0, 32]`, rst 1 up to `F = 32`, 0 on `(32, 65]`, steers 0) in which the
request crosses `ulink_n1__1`, `ucmpi0.uor` and the 30-element delay at one
step per LUT, and the join's rst pin reads 1 at every step before 65, while
at step 65 its pin on `g[29]` reads the moved value 1. -/
theorem counter_br9 :
    ∃ (v : Nat → Nat → Bool) (Rn : Run gNet v), Bounded gNet v Rn 65 32 ∧
      (∀ k n, k ≤ 32 → 32 ≤ k + 32 → gCtl n = true → n ≠ 0 → v k n = gR n) ∧
      (∀ k, 32 ≤ k + 32 → k ≤ 32 → v k 0 = true) ∧ (∀ k, 32 < k → k ≤ 65 → v k 0 = false) ∧
      (∀ k z, z ∈ ResetGcdWave.zL → 32 < k → k ≤ 65 → v k z = false) ∧
      dminP 99 pins99 = 32 ∧
      (∀ t, t < 65 → rdv Rn pins99 99 t 0 = true) ∧
      rdv Rn pins99 99 65 97 = true ∧ gR 97 = false := by
  refine ⟨_, cRun _ 99 3 32 32 65 upd99, cBounded _ _ _ _ _ _ upd99,
    c_settled _ _ _ _ (by decide +kernel) (by omega) (by omega), ?_, ?_,
    fun k z hz _ hk => c_steer _ _ _ (by decide +kernel) k z hz hk, by decide +kernel, ?_, ?_,
    by decide +kernel⟩
  · intro k _ hk; rw [c_rst _ _ _ k (by omega)]; simp [hk]
  · intro k h1 hk; rw [c_rst _ _ _ k hk]; simp; omega
  · decide +kernel
  · decide +kernel

/-! ## Non-vacuity of the network instance -/

/-- The rst waveform of the witness: 1 up to step 23, then 0; data 0. -/
def inpW (k i : Nat) : Bool := if i = 0 then decide (k ≤ 23) else false

/-- **Non-vacuity of `cellRunW_clean`, `gcd_reset_vec_net` and
`gcd_reset_vec_of_net`.** The unit-delay simulation of `gNet` from the
all-0 power-up state (any other works too), with rst 1 on `(0, 23]` and 0
on `(23, 57]`, meets every hypothesis with `D = W = 0`, `F = 23`, `E = 57`
(`H_HOLD_LONG`: `23 * 1 + 0 ≤ 23`; `H_STEER_HOLD` is vacuous on
`(57, 57]`). -/
theorem nonvac_net :
    ∃ (v : Nat → Nat → Bool) (Rn : Run gNet v), Bounded gNet v Rn 0 0 ∧
      (∀ k, 0 < k → k ≤ 23 → TernaryPhases.InputsIn gNet v gA k) ∧
      (maxRank + 2) * (0 + 0 + 1) + 0 ≤ 23 ∧
      (∀ k, 23 < k → k ≤ 57 → v k 0 = false) ∧
      (∀ k z, z ∈ ResetGcdWave.zL → 23 + 34 < k → k ≤ 57 → v k z = false) := by
  refine ⟨_, unitRun gNet inpW (fun _ => false), unitDelay_run gNet inpW (fun _ => false),
    ?_, by decide, ?_, fun _ _ _ h1 h2 => by omega⟩
  · intro k h1 h2 n hn
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    show K3.admits (gA n) (match gNet.node n with
      | .input => inpW (k' + 1) n
      | .gate init pins => lutB init (pinsB (fun _ i => simB gNet inpW (fun _ => false) k' i)
          pins 0)) = true
    rw [hn]
    unfold gA inpW
    by_cases h0 : n = 0
    · subst h0; simp only [ite_true]; rw [show decide (k' + 1 ≤ 23) = true by simp; omega]; rfl
    · simp only [h0, ite_false]; rfl
  · intro k h1 h2
    obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
    show (match gNet.node 0 with
      | .input => inpW (k' + 1) 0
      | .gate init pins => lutB init (pinsB (fun _ i => simB gNet inpW (fun _ => false) k' i)
          pins 0)) = false
    rw [show gNet.node 0 = .input from rfl]
    unfold inpW; simp only [ite_true]; simp; omega

end Formal.Cells.ResetGcdVec2
