import Formal.Cells.AssumeGuaranteeMuxNNet
import Formal.Cells.AssumeGuaranteeMuxNFinWit
import Formal.Cells.AMergeGates
open Formal.Core.LutList

/-!
# Probe Bor3 (shard B): the n-branch truncated OR; the muxn's `|j` gate-modelled

Note: `formal/notes/B-finite-or-n.md`. Bfin2's `FiniteNet.tor_ex` carries a 2-input OR (the
steer `uack`, the mux `uor`) in the time-indexed rule; `AssumeGuaranteeMuxNNet.
gcd_hw_safe_fin_net3` left a contract on `bdc_muxn`'s `|j`, the 3-input OR of the three
join outputs that feeds `uor` and gates the FASTFALL line. This file generalises `tor_ex`
to any number of branches and removes that contract.

## Assumed / proved / NOT covered

**Proved:**
* `tor_exN`: the OR of branches indexed by ANY type `β` (one branch active per token: token
  `n` is carried by branch `σ n`, `κ b` enumerates branch `b`'s tokens), truncated: branches
  clean on `[0, T)` ⇒ the OR clean on `[0, T)` with the merged edges `oeN` (token `n`'s
  edges on its branch, counted by `cntN`) and edge set `LorN`. The OR is given by its
  truth (`H_OR`: `x t` iff some branch is high), so every LUT computing an OR is covered.
  Hypotheses beyond the per-branch enumerations: H_DOWN_N and H_ORD_N, the same shape as
  Bfin2's (merged edges exist in order and increase). `tor_ex_of_N`: Bfin2's 2-branch
  statement is the instance `β = Bool` (`cntN_bool`, `oeN_bool`, `lorN_bool`).
* `or3_real`, `or3_any_order`, `or3_init_unique` (kernel `decide`): the `|j` LUT3, INIT
  `8'hFE` on `[j2, j1, j0]` (`AMergeGates.or3`, from the yosys run recorded in
  `notes/B-amerge.md`, H_YOSYS_MAP), is `j0 ∨ j1 ∨ j2`; it is the OR for EVERY pin order,
  and `8'hFE` is the ONLY LUT3 INIT computing the 3-OR, so the RTL's `|j` (a reduction OR
  of 3 nets, `bdc/emit.py` `emit_muxn`) forces this INIT whenever yosys maps it to one
  LUT3 on those three nets. `tor3`: the REAL `|j` LUT, truncated (`Win` + H_NO_REVERT).
* `FOr3Spec`, `for3_spec_cell`: the cell spec for the time-indexed network rule.
* `muxn_count` (kernel census): gcd_hw has exactly one `muxn`. `gcd_hw_safe_fin_net3'`:
  `gcd_hw_safe_fin_net3` with the muxn's `|j` gate-modelled (`FGcdNetOK3'`, `FTied3'`);
  contracts remain on the 3 sources and the cells of the 9 amerges only
  (`op_classes_fin3`; join1/sink have no cell).
* `Wit3.or3_witness`: a finite run, 4 tokens with codes `0, 1, 2, 0` (all three branches
  fire, branch 0 twice), the REAL `|j` INIT with a delay window `[2, 3]` (actual delay 2):
  every hypothesis of `tor3` holds and the OR node is clean at every `T`, with 8 edges at
  `6, 10, …, 28`, then quiet. `Wit3.for3_spec_witness`: a 4-cell `GD` (three drivers
  whose edges are one tick before their pins', pin windows `[1, 1]`, and the `|j` cell)
  meets every field of `FOr3Spec` (the `Wire` relation of `FNetW` is not part of the spec
  and is not checked there).

**Assumed (named):** B's `Win` + H_NO_REVERT gate model and H_PWR for the `|j` LUT;
H_YOSYS_MAP (yosys maps `|j` to ONE LUT3 on `j[0..2]`; the INIT then follows); the token
enumerations per branch (as Bfin2: `σ` is an infinite select sequence; a finite run has
finitely many EXISTING edges); H_DOWN_N, H_ORD_N, H_FLOOR (edge-time inequalities).

**NOT covered:** H_ORD_N is not derived from delay constants (it is the n-branch form of
Bfin2's H_ORD); no joint witness of `FGcdNetOK3'` (each spec witnessed separately); the
sources and amerges stay contracts here. Core Lean only.
-/

namespace Formal.Cells.FiniteOrN
open Formal.Cells
open Formal.Cells.FiniteNet
open Formal.Cells.WinFifo (Win)
open Formal.Cells.WinFifoCausal (NoRevertI nt noRevertI_shift)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.FiniteRuns (fe)
open Formal.Cells.AssumeGuaranteeMuxOr (cnt cnt_succ_eq cnt_succ_ne cnt_mono cnt_kappa oe)

/-! ## 1. Token counts and merged edges over any branch type -/

section defs
variable {β : Type} [DecidableEq β]

/-- Token `n` is on branch `b`. -/
def ind (σ : Nat → β) (b : β) (n : Nat) : Bool := decide (σ n = b)

/-- The number of tokens before `n` carried by branch `b`. -/
def cntN (σ : Nat → β) (b : β) (n : Nat) : Nat := cnt (ind σ b) true n

/-- **The merged edges** of the n-branch OR: edge `2n + r` is edge `r` of token `n` on its
branch `σ n` (Bfin2's `oe` for any branch type). -/
def oeN (σ : Nat → β) (α : β → Nat → Nat) (k : Nat) : Nat :=
  α (σ (k / 2)) (2 * cntN σ (σ (k / 2)) (k / 2) + k % 2)

/-- The OR's merged edge `k` exists iff its token's edge exists on the token's branch. -/
def LorN (σ : Nat → β) (La : β → Nat → Prop) (k : Nat) : Prop :=
  La (σ (k / 2)) (2 * cntN σ (σ (k / 2)) (k / 2) + k % 2)

theorem cntN_succ_eq {σ : Nat → β} {b : β} {n : Nat} (h : σ n = b) :
    cntN σ b (n + 1) = cntN σ b n + 1 := cnt_succ_eq (by simp [ind, h])

theorem cntN_mono (σ : Nat → β) (b : β) {n n' : Nat} (h : n ≤ n') : cntN σ b n ≤ cntN σ b n' :=
  cnt_mono _ _ h

theorem cntN_kappa {σ : Nat → β} {b : β} {κ : Nat → Nat} (hκ : ∀ m, κ m < κ (m + 1))
    (hκb : ∀ m, σ (κ m) = b) (hκall : ∀ n, σ n = b → ∃ m, κ m = n) (m : Nat) :
    cntN σ b (κ m) = m :=
  cnt_kappa hκ (fun m => by simp [ind, hκb m]) (fun n h => hκall n (by simpa [ind] using h)) m

theorem oeN_even (σ : Nat → β) (α : β → Nat → Nat) (n : Nat) :
    oeN σ α (2 * n) = α (σ n) (2 * cntN σ (σ n) n) := by
  unfold oeN; rw [show 2 * n / 2 = n by omega, show 2 * n % 2 = 0 by omega]; rfl
theorem oeN_odd (σ : Nat → β) (α : β → Nat → Nat) (n : Nat) :
    oeN σ α (2 * n + 1) = α (σ n) (2 * cntN σ (σ n) n + 1) := by
  unfold oeN; rw [show (2 * n + 1) / 2 = n by omega, show (2 * n + 1) % 2 = 1 by omega]
theorem lorN_even {σ : Nat → β} {La : β → Nat → Prop} (n : Nat) :
    LorN σ La (2 * n) ↔ La (σ n) (2 * cntN σ (σ n) n) := by
  unfold LorN; rw [show 2 * n / 2 = n by omega, show 2 * n % 2 = 0 by omega]; simp
theorem lorN_odd {σ : Nat → β} {La : β → Nat → Prop} (n : Nat) :
    LorN σ La (2 * n + 1) ↔ La (σ n) (2 * cntN σ (σ n) n + 1) := by
  unfold LorN; rw [show (2 * n + 1) / 2 = n by omega, show (2 * n + 1) % 2 = 1 by omega]

end defs

/-! ## 2. The n-branch OR, truncated -/

section orn
variable {β : Type} [DecidableEq β] {σ : Nat → β} {a : β → Nat → Bool} {α : β → Nat → Nat}
  {La : β → Nat → Prop} {κ : β → Nat → Nat} {T : Nat} {x : Nat → Bool}

/-- **The OR of any number of branches, truncated.** The branches `a b` are clean on
`[0, T)` (edges `α b`, sets `La b`); token `n` is carried by branch `σ n` and `κ b`
enumerates branch `b`'s tokens; H_DOWN_N / H_ORD_N: the merged edges `oeN` exist in order
and increase (the branches interleave in token order). `x` is the OR on `[0, T)` (`H_OR`).
Then `x` is clean on `[0, T)` with edges `oeN` and edge set `LorN`. -/
theorem tor_exN
    (hκ : ∀ b m, κ b m < κ b (m + 1)) (hκb : ∀ b m, σ (κ b m) = b)
    (hκall : ∀ b n, σ n = b → ∃ m, κ b m = n)
    (H_DOWN_N : ∀ k, LorN σ La (k + 1) → LorN σ La k)
    (H_ORD_N : ∀ k, LorN σ La (k + 1) → oeN σ α k < oeN σ α (k + 1))
    (H_OR : ∀ t, t < T → (x t = true ↔ ∃ b, a b t = true))
    (ha : ∀ b, GPhT (a b) (α b) (La b) T) :
    GPhT x (oeN σ α) (LorN σ La) T := by
  have om := mono_ex H_DOWN_N H_ORD_N
  have dn := down_ex H_DOWN_N
  have ck : ∀ b m, cntN σ b (κ b m) = m := fun b => cntN_kappa (hκ b) (hκb b) (hκall b)
  have ea : ∀ b m r, r < 2 → α b (2 * m + r) = oeN σ α (2 * κ b m + r) := by
    intro b m r hr
    unfold oeN
    rw [show (2 * κ b m + r) / 2 = κ b m by omega, show (2 * κ b m + r) % 2 = r by omega,
      hκb b m, ck b m]
  have la : ∀ b m r, r < 2 → (La b (2 * m + r) ↔ LorN σ La (2 * κ b m + r)) := by
    intro b m r hr
    unfold LorN
    rw [show (2 * κ b m + r) / 2 = κ b m by omega, show (2 * κ b m + r) % 2 = r by omega,
      hκb b m, ck b m]
  have before : ∀ b m n, m < cntN σ b n → κ b m < n := by
    intro b m n h
    apply Classical.byContradiction; intro hc
    have := cntN_mono σ b (show n ≤ κ b m by omega); rw [ck] at this; omega
  have after : ∀ b m n, cntN σ b n ≤ m → n ≤ κ b m := by
    intro b m n h
    apply Classical.byContradiction; intro hc
    have := cntN_mono σ b (show κ b m + 1 ≤ n by omega)
    rw [cntN_succ_eq (hκb b m), ck] at this; omega
  -- a branch is low between its tokens
  have low : ∀ b t, t < T → ∀ n, (∀ m, n ≤ κ b m → σ (κ b m) = b →
      (La b (2 * m) → t < α b (2 * m))) →
      (∀ m, κ b m < n → La b (2 * m + 1) ∧ α b (2 * m + 1) ≤ t) →
      a b t = false := by
    intro b t ht n hA hB
    by_cases hc : cntN σ b n = 0
    · refine (ha b).pre t ht ?_
      by_cases h0 : La b 0
      · exact Or.inr (by
          have := hA 0 (after b 0 n (by omega)) (hκb b 0) (by simpa using h0)
          simpa using this)
      · exact Or.inl h0
    · obtain ⟨d, hd⟩ : ∃ d, cntN σ b n = d + 1 := ⟨cntN σ b n - 1, by omega⟩
      obtain ⟨l1, l2⟩ := hB d (before b d n (by omega))
      have := (ha b).ph (2 * d + 1) t ht l1 l2 (fun h => by
        have := hA (d + 1) (after b (d + 1) n (by omega)) (hκb b _)
          (by rw [show 2 * (d + 1) = 2 * d + 1 + 1 by omega]; exact h)
        rw [show 2 * (d + 1) = 2 * d + 1 + 1 by omega] at this; exact this)
      rw [this]; exact PipeTimed.Vph_odd d
  have allLow : ∀ t, t < T → (∀ b, a b t = false) → x t = false := by
    intro t ht hb
    cases hxt : x t
    · rfl
    · obtain ⟨b, hb'⟩ := (H_OR t ht).1 hxt
      rw [hb b] at hb'; cases hb'
  refine ⟨fun t ht h => ?_, fun k t ht hk h1 h2 => ?_⟩
  · -- before the first merged edge every branch is low
    refine allLow t ht (fun b => low b t ht 0 (fun m _ _ hl => by
        have l := (la b m 0 (by omega)).1 (by simpa using hl)
        have l0 := dn 0 _ (Nat.zero_le _) l
        rcases h with h | h
        · exact absurd l0 h
        · rw [show 2 * m = 2 * m + 0 by omega, ea b m 0 (by omega)]
          have := om 0 _ (Nat.zero_le _) l; omega)
      (fun m h => absurd h (Nat.not_lt_zero _)))
  · obtain ⟨n, rfl | rfl⟩ : ∃ n, k = 2 * n ∨ k = 2 * n + 1 := ⟨k / 2, by omega⟩
    · -- high phase of token `n`: its branch is high
      have hl := (lorN_even (σ := σ) (La := La) n).1 hk
      have e1 := oeN_even σ α n
      have hv : a (σ n) t = true := by
        rw [(ha (σ n)).ph (2 * cntN σ (σ n) n) t ht hl (by omega) (fun h => by
          have := h2 ((lorN_odd n).2 h); rw [oeN_odd] at this; exact this)]
        exact PipeTimed.Vph_even _
      rw [PipeTimed.Vph_even]
      exact (H_OR t ht).2 ⟨σ n, hv⟩
    · -- low phase between tokens `n` and `n + 1`: every branch is low
      have hl := (lorN_odd (σ := σ) (La := La) n).1 hk
      have e1 := oeN_odd σ α n
      have upper : ∀ b m, n < κ b m → La b (2 * m) → t < α b (2 * m) := by
        intro b m hm hl'
        have l := (la b m 0 (by omega)).1 (by simpa using hl')
        have l2 := dn (2 * n + 1 + 1) _ (by omega) l
        have := h2 l2
        have := om (2 * n + 1 + 1) _ (by omega) l
        rw [show 2 * m = 2 * m + 0 by omega, ea b m 0 (by omega)]; omega
      have lower : ∀ b m, κ b m ≤ n → La b (2 * m + 1) ∧ α b (2 * m + 1) ≤ t := by
        intro b m hm
        have l := dn (2 * κ b m + 1) _ (by omega) hk
        refine ⟨(la b m 1 (by omega)).2 l, ?_⟩
        have := om (2 * κ b m + 1) _ (by omega) hk
        rw [ea b m 1 (by omega)]; omega
      rw [PipeTimed.Vph_odd]
      exact allLow t ht (fun b => low b t ht (n + 1) (fun m hm _ hl' => upper b m (by omega) hl')
        (fun m hm => lower b m (by omega)))

end orn

/-! ## 3. Bfin2's 2-branch OR is the instance `β = Bool` -/

theorem cntN_bool (σ : Nat → Bool) (b : Bool) : ∀ n, cntN σ b n = cnt σ b n
  | 0 => rfl
  | n + 1 => by
    by_cases h : σ n = b
    · rw [cntN_succ_eq h, cnt_succ_eq h, cntN_bool σ b n]
    · have e : cntN σ b (n + 1) = cntN σ b n :=
        cnt_succ_ne (σ := ind σ b) (b := true) (by simp [ind, h])
      rw [cnt_succ_ne h, e, cntN_bool σ b n]

theorem oeN_bool (σ : Nat → Bool) (α : Bool → Nat → Nat) : oeN σ α = oe σ α := by
  funext k; unfold oeN oe; rw [cntN_bool]

theorem lorN_bool (σ : Nat → Bool) (La : Bool → Nat → Prop) : LorN σ La = Lor σ La := by
  funext k; unfold LorN Lor; rw [cntN_bool]

/-- **`tor_ex` recovered from `tor_exN`** (the generalisation loses nothing). -/
theorem tor_ex_of_N {σ : Nat → Bool} {a : Bool → Nat → Bool} {α : Bool → Nat → Nat}
    {La : Bool → Nat → Prop} {κ : Bool → Nat → Nat} {T : Nat}
    (hκ : ∀ b m, κ b m < κ b (m + 1)) (hκb : ∀ b m, σ (κ b m) = b)
    (hκall : ∀ b n, σ n = b → ∃ m, κ b m = n)
    (H_DOWN : ∀ k, Lor σ La (k + 1) → Lor σ La k)
    (H_ORD : ∀ k, Lor σ La (k + 1) → oe σ α k < oe σ α (k + 1))
    (ha : ∀ b, GPhT (a b) (α b) (La b) T) :
    GPhT (fun t => a true t || a false t) (oe σ α) (Lor σ La) T := by
  rw [← oeN_bool, ← lorN_bool]
  rw [← oeN_bool, ← lorN_bool] at H_ORD
  rw [← lorN_bool] at H_DOWN
  refine tor_exN hκ hκb hκall H_DOWN H_ORD (fun t _ => ?_) ha
  constructor
  · intro h
    cases h1 : a true t
    · rw [h1] at h; exact ⟨false, by simpa using h⟩
    · exact ⟨true, h1⟩
  · rintro ⟨b, hb⟩
    cases b
    · rw [hb]; cases a true t <;> rfl
    · rw [hb]; rfl

/-! ## 4. The REAL `|j` LUT3 of `bdc_muxn` -/

open Formal.Cells.AMergeGates (or3 OR3)

/-- **`|j` = LUT3 `8'hFE` on `[j2, j1, j0]` is the 3-input OR** (kernel `decide`). -/
theorem or3_real : ∀ j0 j1 j2 : Bool, or3 j0 j1 j2 = (j0 || j1 || j2) := by decide +kernel

/-- `8'hFE` is the OR for EVERY assignment of the three nets to `I0..I2`: the pin order
recorded by H_YOSYS_MAP does not matter. -/
theorem or3_any_order : ∀ a b c : Bool, lutB OR3 [a, b, c] = (a || b || c) := by decide +kernel

/-- **The INIT is forced**: `8'hFE` is the only LUT3 INIT computing the 3-input OR. So the
RTL's reduction OR `|j` (`emit_muxn`) fixes the INIT once yosys maps it to one LUT3 on
`j[0..2]` (that mapping is H_YOSYS_MAP's content). -/
theorem or3_init_unique :
    ∀ i : Fin 256, (∀ a b c : Bool, lutB i.val [a, b, c] = (a || b || c)) ↔ i.val = OR3 := by
  decide +kernel

theorem fin3_cases (b : Fin 3) : b = 0 ∨ b = 1 ∨ b = 2 := by
  match b with
  | ⟨0, _⟩ => exact Or.inl rfl
  | ⟨1, _⟩ => exact Or.inr (Or.inl rfl)
  | ⟨2, _⟩ => exact Or.inr (Or.inr rfl)

theorem or3_iff (a : Fin 3 → Bool) : or3 (a 0) (a 1) (a 2) = true ↔ ∃ b, a b = true := by
  rw [or3_real]
  constructor
  · intro h
    cases h0 : a 0
    · cases h1 : a 1
      · rw [h0, h1] at h; exact ⟨2, by simpa using h⟩
      · exact ⟨1, h1⟩
    · exact ⟨0, h0⟩
  · rintro ⟨b, hb⟩
    rcases fin3_cases b with rfl | rfl | rfl
    · rw [hb]; rfl
    · rw [hb]; cases a 0 <;> rfl
    · rw [hb]; cases a 0 <;> cases a 1 <;> rfl

/-- **The REAL `|j` of `bdc_muxn3_32`, truncated**: branch `b` is the join `j[b]`; token `n`
of the control is decoded to branch `σ n` (`κ b`: the tokens with code `b`). -/
theorem tor3 {σ : Nat → Fin 3} {a : Fin 3 → Nat → Bool} {α : Fin 3 → Nat → Nat}
    {La : Fin 3 → Nat → Prop} {κ : Fin 3 → Nat → Nat} {O : Nat → Bool} {lo hi T : Nat}
    (H_LUT_WIN : Win lo hi (fun t => or3 (a 0 t) (a 1 t) (a 2 t)) O)
    (H_NO_REVERT : NoRevertI lo hi (fun t => or3 (a 0 t) (a 1 t) (a 2 t)) O)
    (H_PWR : ∀ t, t < hi → O t = false)
    (H_FLOOR : ∀ k, LorN σ La k → hi ≤ oeN σ α k + lo)
    (hκ : ∀ b m, κ b m < κ b (m + 1)) (hκb : ∀ b m, σ (κ b m) = b)
    (hκall : ∀ b n, σ n = b → ∃ m, κ b m = n)
    (H_DOWN_N : ∀ k, LorN σ La (k + 1) → LorN σ La k)
    (H_ORD_N : ∀ k, LorN σ La (k + 1) → oeN σ α k < oeN σ α (k + 1))
    (ha : ∀ b, GPhT (a b) (α b) (La b) T) :
    GPhT O (fe O lo hi (oeN σ α)) (LorN σ La) (T + lo) :=
  tnode H_LUT_WIN H_NO_REVERT
    (tor_exN hκ hκb hκall H_DOWN_N H_ORD_N (fun t _ => or3_iff (fun b => a b t)) ha)
    H_FLOOR H_PWR

/-! ## 5. The cell spec -/

section spec
open Formal.Cells.AssumeGuaranteeEnds (GPin gE)
open Formal.Cells.AssumeGuaranteeEndsNet (GD)
variable {ι : Type}

/-- **The `|j` cell spec** (time-indexed rule): pins `[j2, j1, j0]` as yosys mapped them;
the REAL INIT; B's `Win` + H_NO_REVERT gate model; edges `fe` of the merged pin edges; edge
set `LorN`; the control's decoded select `σ`, enumerations `κ`, H_DOWN_N, H_ORD_N, floor. -/
structure FOr3Spec (D : GD ι) (L : ι → Nat → Prop) (c : ι) (ap : Fin 3 → GPin ι)
    (σ : Nat → Fin 3) (κ : Fin 3 → Nat → Nat) : Prop where
  H_PINS : D.pins c = [ap 2, ap 1, ap 0]
  H_LUT_WIN : Win (D.lo c) (D.hi c) (fun t => or3 ((ap 0).P t) ((ap 1).P t) ((ap 2).P t)) (D.O c)
  H_NO_REVERT : NoRevertI (D.lo c) (D.hi c)
    (fun t => or3 ((ap 0).P t) ((ap 1).P t) ((ap 2).P t)) (D.O c)
  H_PWR : ∀ t, t < D.hi c → D.O c t = false
  H_TIMES : ∀ k, D.τ c k = nt (D.O c) (D.lo c) (D.hi c) (oeN σ (fun b => gE D.τ (ap b)) k) (Vph k)
  H_CNT : ∀ k, L c k ↔ LorN σ (fun b => L (ap b).drv) k
  H_KAPPA : ∀ b m, κ b m < κ b (m + 1)
  H_KAPPA_B : ∀ b m, σ (κ b m) = b
  H_KAPPA_ALL : ∀ b n, σ n = b → ∃ m, κ b m = n
  H_DOWN_N : ∀ k, LorN σ (fun b => L (ap b).drv) (k + 1) → LorN σ (fun b => L (ap b).drv) k
  H_ORD_N : ∀ k, LorN σ (fun b => L (ap b).drv) (k + 1) →
    oeN σ (fun b => gE D.τ (ap b)) k < oeN σ (fun b => gE D.τ (ap b)) (k + 1)
  H_FLOOR : ∀ k, L c k → D.hi c ≤ oeN σ (fun b => gE D.τ (ap b)) k + D.lo c

/-- **The `|j` spec gives the truncated contract** `FCellOK`. -/
theorem for3_spec_cell {D : GD ι} {L : ι → Nat → Prop} {c : ι} {ap : Fin 3 → GPin ι}
    {σ : Nat → Fin 3} {κ : Fin 3 → Nat → Nat} (S : FOr3Spec D L c ap σ κ) : FCellOK D L c := by
  intro T hA
  have hτ : D.τ c = fe (D.O c) (D.lo c) (D.hi c) (oeN σ (fun b => gE D.τ (ap b))) :=
    funext S.H_TIMES
  have hL : L c = LorN σ (fun b => L (ap b).drv) := funext fun j => propext (S.H_CNT j)
  rw [hτ, hL]
  refine tor3 (a := fun b => (ap b).P) S.H_LUT_WIN S.H_NO_REVERT S.H_PWR
    (fun k hk => S.H_FLOOR k (by rw [hL]; exact hk)) S.H_KAPPA S.H_KAPPA_B S.H_KAPPA_ALL
    S.H_DOWN_N S.H_ORD_N (fun b => hA (ap b) ?_)
  rw [S.H_PINS]
  rcases fin3_cases b with rfl | rfl | rfl <;> simp

end spec

/-! ## 6. gcd_hw with the muxn's `|j` gate-modelled -/

section gcd
open Formal.Cells.AssumeGuaranteeEnds (GPin gE GC2)
open Formal.Cells.AssumeGuaranteeEndsNet
open Formal.Cells.AssumeGuaranteeMuxNet
open Formal.Cells.AssumeGuaranteeMuxNFin
open Formal.Cells.AssumeGuaranteeMuxNNet
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe
open Formal.Cells.LutFbBridge2Env (isLink)
open Formal.Cells.AssumeGuaranteeCap (kname census)
open Formal.Cells.AssumeGuaranteeEndsCap (tiedOp forkOuts joinIns steerIn d0 LinkOut)
open Formal.Net.Ops.Gen (genF)
open Formal.Gen Formal.Gen.Cells

/-- **gcd_hw has exactly one `muxn`** (kernel census), so one `|j` cell. -/
theorem muxn_count :
    census (((List.finRange NO).filter (fun o => isMuxNK (opAt o))).map (fun o => kname (opAt o)))
      = [("muxn", 1)] := by
  decide +kernel

/-- `FGcdNet3` plus the muxn's `|j` cell `nor`. -/
structure FGcdNet3' extends FGcdNet3 where
  nor : Fin NO → ι

def FTied3' (N : FGcdNet3') (c : N.ι) : Prop :=
  FTied3 N.toFGcdNet3 c ∨ ∃ o cc x0 x1 x2 z nw, opAt o = .muxn cc x0 x1 x2 z nw ∧ c = N.nor o

/-- **The hypotheses**: `FGcdNetOK3`'s fields verbatim, plus the `|j` spec (`H_FNOR`, its
pins the three joins); a truncated contract only on the cells not in `FTied3'`. -/
structure FGcdNetOK3' (ch : Fin NC → Chan) (N : FGcdNet3') (L : N.ι → Nat → Prop)
    (n : N.ι → Nat) : Prop where
  NW : FNetW N.D L
  H_FIN : ∀ c j, L c j ↔ j < n c
  H_LINK : ∀ o i o', opAt o = .link i o' → ∃ rp ap Es Ea, FLinkSpec N.D L (N.lk o) rp ap Es Ea ∧
    rp.P = (ch i).req ∧ ap.P = (ch o').ack ∧ LinkOut N.D (N.lk o) (ch i) (ch o') Es Ea
  H_FORK : ∀ o os, forkOuts (opAt o) = some os → 2 ≤ os.length → os.length ≤ 4 →
    FCelTie N.D L (N.fa o) os (fun c => (ch c).ack)
  H_JOIN : ∀ o ins, joinIns (opAt o) = some ins → ins.length = 2 →
    FCelTie N.D L (N.jr o) ins (fun c => (ch c).req)
  H_STEER : ∀ o j, steerIn (opAt o) = some j → ∀ b, ∃ rp s σ κ,
    FSteerSpec N.D L (N.sb o b) rp b s σ κ ∧ rp.P = (ch j).req
  H_SOR : ∀ o j, steerIn (opAt o) = some j → ∃ ap σ κ,
    FOrSpec N.D L (N.ao o) (fun a0 a1 => genF bd_steer "uack" .O ["ack0", "ack1"] [a0, a1])
      ap σ κ
  H_FMUXJ : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ b, ∃ xp cp s σ κ E,
    FMuxJSpec N.D L (N.mj o b) xp cp b s σ κ E ∧ xp.P = (ch (if b then y else x)).req ∧
    cp.P = (ch cc).req
  H_FMUXA : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ b, ∃ ap zp κ E,
    FMuxASpec N.D L (N.ma o b) ap zp κ E ∧ ap.drv = N.mj o b ∧ zp.P = (ch z).ack
  H_FMUXD : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ i, ∃ p, FBufSpec N.D L (N.md o i) p
  H_FMUXO : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∃ ap σ κ,
    FOrSpec N.D L (N.mo o) (fun a0 a1 => genF bd_mux_W2 "uor" .O ["j0", "j1"] [a0, a1]) ap σ κ
  H_FNDEC : ∀ o cc x0 x1 x2 z nw, opAt o = .muxn cc x0 x1 x2 z nw → ∀ k : Fin 3,
    ∃ cp s0 s1 σ κ, FDecSpec N.D L (N.nd o k) cp k.val s0 s1 σ κ ∧ cp.P = (ch cc).req
  H_FNJ : ∀ o cc x0 x1 x2 z nw, opAt o = .muxn cc x0 x1 x2 z nw → ∀ k : Fin 3,
    ∃ (pv : Fin 2 → GPin N.ι) (E : Nat), FCelSpec GC2 N.D L (N.nj o k) pv E ∧
      (pv 0).P = (ch (mx x0 x1 x2 k)).req ∧ (pv 1).drv = N.nd o k
  H_FNA : ∀ o cc x0 x1 x2 z nw, opAt o = .muxn cc x0 x1 x2 z nw → ∀ k : Fin 3,
    ∃ ap zp κ E, FMuxASpec N.D L (N.na o k) ap zp κ E ∧ ap.drv = N.nj o k ∧ zp.P = (ch z).ack
  H_FNBUF : ∀ o cc x0 x1 x2 z nw, opAt o = .muxn cc x0 x1 x2 z nw → ∀ i : Fin 13, i.val < 2 →
    ∃ p, FBufSpec N.D L (N.nl o i) p
  H_FNAND : ∀ o cc x0 x1 x2 z nw, opAt o = .muxn cc x0 x1 x2 z nw → ∀ i : Fin 13, 2 ≤ i.val →
    ∃ ap gp, FAndSpec N.D L (N.nl o i) ap gp
  H_FTREE5 : ∀ o os, forkOuts (opAt o) = some os → os.length = 5 → ∃ pin lv E,
    FTree5 N.D L (N.tr o 0) (N.tr o 1) pin lv E ∧
      ∀ i : Fin 5, (lv i).P = (ch (os.getD i.val d0)).ack
  H_FTREE6 : ∀ o os, forkOuts (opAt o) = some os → os.length = 6 → ∃ pa pb lv E,
    FTree6 N.D L (N.tr o 0) (N.tr o 1) (N.tr o 2) pa pb lv E ∧
      ∀ i : Fin 6, (lv i).P = (ch (os.getD i.val d0)).ack
  H_FNOR : ∀ o cc x0 x1 x2 z nw, opAt o = .muxn cc x0 x1 x2 z nw → ∃ ap σ κ,
    FOr3Spec N.D L (N.nor o) ap σ κ ∧ ∀ k : Fin 3, (ap k).drv = N.nj o k
  H_REST : ∀ c, ¬ FTied3' N c → FCellOK N.D L c

/-- The `|j` spec gives its cell a truncated contract, so `FGcdNetOK3'` contains
`FGcdNetOK3`. -/
theorem FGcdNetOK3'.toOK3 {ch : Fin NC → Chan} {N : FGcdNet3'} {L : N.ι → Nat → Prop}
    {n : N.ι → Nat} (H : FGcdNetOK3' ch N L n) : FGcdNetOK3 ch N.toFGcdNet3 L n := by
  refine ⟨H.NW, H.H_FIN, H.H_LINK, H.H_FORK, H.H_JOIN, H.H_STEER, H.H_SOR, H.H_FMUXJ, H.H_FMUXA,
    H.H_FMUXD, H.H_FMUXO, H.H_FNDEC, H.H_FNJ, H.H_FNA, H.H_FNBUF, H.H_FNAND, H.H_FTREE5,
    H.H_FTREE6, fun c hc => ?_⟩
  by_cases h : ∃ o cc x0 x1 x2 z nw, opAt o = .muxn cc x0 x1 x2 z nw ∧ c = N.nor o
  · obtain ⟨o, cc, x0, x1, x2, z, nw, ho, rfl⟩ := h
    obtain ⟨ap, σ, κ, S, _⟩ := H.H_FNOR o cc x0 x1 x2 z nw ho
    exact for3_spec_cell S
  · exact H.H_REST c (fun h' => h'.elim hc h)

/-- **End to end, runs that stop, the muxn's `|j` gate-modelled.** C's gcd_hw circuit
safety with every link's `H_CELLS` discharged by ONE gate-level network (`FGcdNetOK3'`,
finite edge counts) in which every cell carries B's gate model except (truncated
contracts) the 3 sources and the cells of the 9 amerges. Still assumed: the edge-time
bounds of `FGcdNetOK3'` (now including the `|j`'s H_ORD_N), C's `H_CELLS` of the other 192
operators, H_BUNDLE, H_CM_FORCED.
CAVEAT (SelfAuditB9; audit P12b, 2026-10-31): the hypothesis does NOT bind the pin
drivers (`GPin.drv`) or the cell set to gcd_hw's netlist. A pinless cell's contract is
the bare claim that its node is clean (`fcellOK_nil_iff`), and a link fed by two such
cells gets its environment from them alone (`flink_env1_local`). So this theorem does not
enforce that any link's environment comes from the gate models named above; "gate-
modelled" describes the intended elaboration only. C's `H_CELLS` for the 192 non-link
operators stays a hypothesis (`H_OTHER`): B's gate models are used only to derive link
environments, never to discharge an operator contract. Driver-bound form: `FiniteNetBound`. -/
theorem gcd_hw_safe_fin_net3' (a b : Nat) (ch : Fin NC → Chan) (N : FGcdNet3')
    (L : N.ι → Nat → Prop) (n : N.ι → Nat) (H : FGcdNetOK3' ch N L n)
    (H_OTHER : ∀ o : Fin NO, isLink (opAt o) = false → Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_CM_FORCED : ∃ y, Good a b y ∧ ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) :=
  gcd_hw_safe_fin_net3 a b ch N.toFGcdNet3 L n H.toOK3 H_OTHER H_BUNDLE H_CM_FORCED

end gcd

/-! ## 7. Non-vacuity: a finite 3-way run through the REAL `|j`, delay window `[2, 3]` -/

namespace Wit3
open Formal.Cells.FiniteRunsWit (sortedB cL)
open Formal.Cells.FiniteNetWit (cL_gph)
open Formal.Cells.AssumeGuaranteeMuxNFin.Wit (cL_tail)

/-- Token `n` has code `n mod 3`: codes `0, 1, 2, 0, …` (the run uses tokens 0..3). -/
def σw (n : Nat) : Fin 3 := ⟨n % 3, Nat.mod_lt _ (by decide)⟩
def κw (b : Fin 3) (m : Nat) : Nat := 3 * m + b.val
/-- Join `j[0]` high on `[4, 8)` and `[22, 26)` (tokens 0 and 3), `j[1]` on `[10, 14)`
(token 1), `j[2]` on `[16, 20)` (token 2); then quiet forever. -/
def L0 : List Nat := [4, 8, 22, 26]
def L1 : List Nat := [10, 14]
def L2 : List Nat := [16, 20]
def Al (b : Fin 3) : List Nat := if b.val = 0 then L0 else if b.val = 1 then L1 else L2
def aw (b : Fin 3) : Nat → Bool := cL (Al b)
def αw (b : Fin 3) (j : Nat) : Nat := (Al b).getD j 1
def Law (b : Fin 3) (j : Nat) : Prop := j < (Al b).length
/-- The `|j` node: the OR delayed by 2 (inside the window `[2, 3]`). -/
def OLw : List Nat := [6, 10, 12, 16, 18, 22, 24, 28]
def Ow : Nat → Bool := cL OLw

theorem c6 : ∀ b : Fin 3, cntN σw b 6 = 2 := by decide
theorem al_len : ∀ b : Fin 3, (Al b).length ≤ 4 := by decide
theorem al_sorted : ∀ b : Fin 3, sortedB (Al b) = true := by decide

theorem lorN_w (k : Nat) : LorN σw Law k ↔ k < 8 := by
  show 2 * cntN σw (σw (k / 2)) (k / 2) + k % 2 < (Al (σw (k / 2))).length ↔ k < 8
  by_cases hk : k < 12
  · have key : ∀ k, k < 12 → (2 * cntN σw (σw (k / 2)) (k / 2) + k % 2 <
        (Al (σw (k / 2))).length ↔ k < 8) := by decide
    exact key k hk
  · have h1 := cntN_mono σw (σw (k / 2)) (show 6 ≤ k / 2 by omega)
    have h2 := c6 (σw (k / 2))
    have h3 := al_len (σw (k / 2))
    omega

theorem oe_w : ∀ k, k < 8 → oeN σw αw k = [4, 8, 10, 14, 16, 20, 22, 26].getD k 0 := by decide

theorem aw_ph (b : Fin 3) (T : Nat) : GPhT (aw b) (αw b) (Law b) T :=
  cL_gph (al_sorted b) T

theorem stepO : ∀ t, 2 ≤ t → Ow t = or3 (aw 0 (t - 2)) (aw 1 (t - 2)) (aw 2 (t - 2)) := by
  have small : ∀ t, t < 40 → 2 ≤ t → Ow t = or3 (aw 0 (t - 2)) (aw 1 (t - 2)) (aw 2 (t - 2)) := by
    decide
  intro t ht
  by_cases h : t < 40
  · exact small t h ht
  · show cL OLw t = or3 (cL L0 (t - 2)) (cL L1 (t - 2)) (cL L2 (t - 2))
    rw [cL_tail OLw 30 t (by decide) (by omega), cL_tail L0 30 (t - 2) (by decide) (by omega),
      cL_tail L1 30 (t - 2) (by decide) (by omega), cL_tail L2 30 (t - 2) (by decide) (by omega)]
    decide

theorem hκw : ∀ b m, κw b m < κw b (m + 1) := fun b m => by unfold κw; omega
theorem hκbw : ∀ b m, σw (κw b m) = b := fun b m => by
  have := b.isLt
  apply Fin.ext; show (3 * m + b.val) % 3 = b.val; omega
theorem hκallw : ∀ b n, σw n = b → ∃ m, κw b m = n := fun b n h => by
  have h' : n % 3 = b.val := congrArg Fin.val h
  exact ⟨n / 3, by unfold κw; omega⟩

theorem winw : Win 2 3 (fun t => or3 (aw 0 t) (aw 1 t) (aw 2 t)) Ow :=
  fun t ht => ⟨t - 2, by omega, by omega, stepO t (by omega)⟩
theorem norevw : NoRevertI 2 3 (fun t => or3 (aw 0 t) (aw 1 t) (aw 2 t)) Ow :=
  noRevertI_shift (fun t ht => stepO t ht)
theorem pwrw : ∀ t, t < 3 → Ow t = false := by decide

/-- **`tor3` has a witness on a finite run with all three branches**: 4 control tokens
with codes `0, 1, 2, 0` (branch 0 carries two), the REAL `|j` INIT, LUT delay window
`[2, 3]` (actual 2). Every hypothesis of `tor3` holds (enumerations, H_DOWN_N, H_ORD_N on
the 8 merged edges `4, 8, …, 26`, gate model, H_PWR, floor); the node is clean at every `T`
with its 8 edges at `6, 10, 12, 16, 18, 22, 24, 28` and is low forever after `28`. -/
theorem or3_witness :
    (∀ b m, κw b m < κw b (m + 1)) ∧ (∀ b m, σw (κw b m) = b) ∧
    (∀ b n, σw n = b → ∃ m, κw b m = n) ∧
    (∀ k, LorN σw Law (k + 1) → LorN σw Law k) ∧
    (∀ k, LorN σw Law (k + 1) → oeN σw αw k < oeN σw αw (k + 1)) ∧
    Win 2 3 (fun t => or3 (aw 0 t) (aw 1 t) (aw 2 t)) Ow ∧
    NoRevertI 2 3 (fun t => or3 (aw 0 t) (aw 1 t) (aw 2 t)) Ow ∧
    (∀ t, t < 3 → Ow t = false) ∧
    (∀ k, LorN σw Law k → 3 ≤ oeN σw αw k + 2) ∧
    (∀ b T, GPhT (aw b) (αw b) (Law b) T) ∧
    (∀ T, GPhT Ow (fe Ow 2 3 (oeN σw αw)) (LorN σw Law) T) ∧
    (∀ k, k < 8 → fe Ow 2 3 (oeN σw αw) k = OLw.getD k 0) ∧
    (∀ b : Fin 3, ∃ n, n < 4 ∧ σw n = b ∧ LorN σw Law (2 * n + 1)) ∧
    (∀ t, 28 ≤ t → Ow t = false) := by
  have hD : ∀ k, LorN σw Law (k + 1) → LorN σw Law k := fun k h => by
    rw [lorN_w] at h ⊢; omega
  have hO : ∀ k, LorN σw Law (k + 1) → oeN σw αw k < oeN σw αw (k + 1) := by
    have key : ∀ k, k < 7 → [4, 8, 10, 14, 16, 20, 22, 26].getD k 0 <
        [4, 8, 10, 14, 16, 20, 22, 26].getD (k + 1) 0 := by decide
    intro k h; rw [lorN_w] at h; rw [oe_w k (by omega), oe_w (k + 1) h]; exact key k (by omega)
  have hF : ∀ k, LorN σw Law k → 3 ≤ oeN σw αw k + 2 := by
    have key : ∀ k, k < 8 → 3 ≤ [4, 8, 10, 14, 16, 20, 22, 26].getD k 0 + 2 := by decide
    intro k h; rw [lorN_w] at h; rw [oe_w k h]; exact key k h
  have hT : ∀ T, GPhT Ow (fe Ow 2 3 (oeN σw αw)) (LorN σw Law) (T + 2) := fun T =>
    tor3 winw norevw pwrw hF hκw hκbw hκallw hD hO (fun b => aw_ph b T)
  refine ⟨hκw, hκbw, hκallw, hD, hO, winw, norevw, pwrw, hF, aw_ph,
    fun T => gphT_mono (hT T) (Nat.le_add_right T 2), fun k hk => ?_, fun b => ?_, fun t ht => ?_⟩
  · have key : ∀ k, k < 8 → nt Ow 2 3 ([4, 8, 10, 14, 16, 20, 22, 26].getD k 0) (Vph k) =
        OLw.getD k 0 := by decide
    show nt Ow 2 3 (oeN σw αw k) (Vph k) = _
    rw [oe_w k hk]; exact key k hk
  · rcases fin3_cases b with rfl | rfl | rfl
    · exact ⟨3, by decide, by decide, (lorN_w _).2 (by decide)⟩
    · exact ⟨1, by decide, by decide, (lorN_w _).2 (by decide)⟩
    · exact ⟨2, by decide, by decide, (lorN_w _).2 (by decide)⟩
  · show cL OLw t = false
    by_cases h : t = 28
    · subst h; decide
    · rw [cL_tail OLw 29 t (by decide) (by omega)]; decide

/-! ### The cell spec on a 4-cell network -/

section specwit
open Formal.Cells.AssumeGuaranteeEnds (GPin gE)
open Formal.Cells.AssumeGuaranteeEndsNet (GD)
open Formal.Cells.LutFbBridge2Env (ε)

/-- Driver `b` (the join `j[b]`) switches one tick before its pin (a wire of `[1, 1]`). -/
def drvL (b : Fin 3) : List Nat := (Al b).map (· - 1)
def τd (b : Fin 3) (j : Nat) : Nat := (drvL b).getD j 0
def apw (b : Fin 3) : GPin (Fin 4) := ⟨b.castSucc, aw b, 1, 1, fun _ => 0⟩
def oeG (k : Nat) : Nat := oeN σw (fun b => ε (aw b) 1 1 (τd b)) k

/-- Cells `0, 1, 2`: the three joins (no pins here); cell `3`: the `|j` LUT. -/
def Dw : GD (Fin 4) where
  O c := if h : c.val < 3 then cL (drvL ⟨c.val, h⟩) else Ow
  τ c := if h : c.val < 3 then τd ⟨c.val, h⟩ else fun k => nt Ow 2 3 (oeG k) (Vph k)
  lo c := if c.val < 3 then 1 else 2
  hi c := if c.val < 3 then 1 else 3
  fl _ := 0
  fh _ := 0
  qp _ := fun _ => false
  rst _ := false
  R := 0
  pins c := if c.val < 3 then [] else [apw 2, apw 1, apw 0]

def Lw (c : Fin 4) (j : Nat) : Prop := if h : c.val < 3 then Law ⟨c.val, h⟩ j else j < 8

theorem ge_w (b : Fin 3) : gE Dw.τ (apw b) = ε (aw b) 1 1 (τd b) := by
  rcases fin3_cases b with rfl | rfl | rfl <;> rfl

theorem oeG_eq : oeN σw (fun b => gE Dw.τ (apw b)) = oeG := by
  funext k; unfold oeG; congr 1; funext b; exact ge_w b

theorem lw_pins : (fun b => Lw (apw b).drv) = Law := by
  funext b; rcases fin3_cases b with rfl | rfl | rfl <;> rfl

theorem oeG_val : ∀ k, k < 8 → oeG k = [4, 8, 10, 14, 16, 20, 22, 26].getD k 0 := by decide

/-- **`FOr3Spec` is jointly satisfiable**: on the 4-cell network `Dw` (wires `[1, 1]`, the
REAL `|j` INIT with window `[2, 3]`, the 4-token 3-way run of `or3_witness`) every field
holds, so the cell has its truncated contract. Pin windows are `[1, 1]` with the drivers'
edges one tick earlier; `FNetW` (wires, floors) is not part of `FOr3Spec` and not checked. -/
theorem for3_spec_witness : FOr3Spec Dw Lw 3 apw σw κw ∧ FCellOK Dw Lw 3 := by
  have S : FOr3Spec Dw Lw 3 apw σw κw := by
    obtain ⟨_, _, _, hD, _, _, _, _, _, _, _, _, _, _⟩ := or3_witness
    refine ⟨rfl, winw, norevw, pwrw, fun k => ?_, fun k => ?_, hκw, hκbw, hκallw, ?_, ?_, ?_⟩
    · show nt Ow 2 3 (oeG k) (Vph k) = _
      rw [oeG_eq]; rfl
    · rw [lw_pins, lorN_w]; exact Iff.rfl
    · rw [lw_pins]; exact hD
    · rw [lw_pins, oeG_eq]
      have key : ∀ k, k < 7 → [4, 8, 10, 14, 16, 20, 22, 26].getD k 0 <
          [4, 8, 10, 14, 16, 20, 22, 26].getD (k + 1) 0 := by decide
      intro k h; rw [lorN_w] at h; rw [oeG_val k (by omega), oeG_val (k + 1) h]
      exact key k (by omega)
    · rw [oeG_eq]
      have key : ∀ k, k < 8 → 3 ≤ [4, 8, 10, 14, 16, 20, 22, 26].getD k 0 + 2 := by decide
      intro k h; have h' : k < 8 := h; rw [oeG_val k h']; exact key k h'
  exact ⟨S, for3_spec_cell S⟩

end specwit

end Wit3

end Formal.Cells.FiniteOrN
