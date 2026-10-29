import Formal.Cells.AssumeGuaranteeMux

/-!
# Probe Bmux2 (shard B): the acknowledge / request ORs (`bd_steer` `uack`, `bd_mux` `uor`)

A steer's acknowledge is `ack₀ ∨ ack₁`; a mux's request is `delay(j₀ ∨ j₁)`. Each input
token is carried by ONE branch (`σ n`). This file gives the OR's segment lemma, derives the
interleaving it needs from causality and the select enumeration, and shows that the lemma
cannot be consumed by Bseg's end-ordered segment rule.

## Assumed / proved / NOT covered

**Proved:**
* `cnt` (tokens before `n` on branch `b`) with `cnt_kappa`/`kappa_cnt`: the count agrees
  with the steer's own select enumeration `κ_b`.
* `or_exc_segK`: segment `k` of `a₁ ∨ a₀` (merged edges `oe`: token `n`'s edges on its own
  branch) from the branch segments `sx σ b k` and the BRACKETS (`Brk`) of the tokens
  `≤ k/2`. A high segment reads only the active branch. `uack_segK`, `uor_segK`: the node
  segment for the REAL LUTs (`uack_gate`, `uor_gate`), via `lutnf_segK`.
* `brk_of_causal`: the brackets from two edge-time facts, `C1` (a branch acknowledge
  rises for token `n` only after the input request rose for token `n`) and `C2` (the input
  request rises for token `n+1` only after the active branch's acknowledge fell for token
  `n`), when the idle branch gets a later token (`H_LATER`). `c1_of_kappa`: `C1` from the
  per-branch path inequality `gc κ_b γ j ≤ α_b j` (the steer branch's gated request phase
  starts, i.e. H_SEL_STABLE + `κ_b`; the path through the branch, its consumer and wires
  is a chain of H_WAITs).
* `Wit.uack_witness`: all hypotheses of `uack_segK` and `brk_of_causal` on an alternating
  run, every node segment. `Wit.or_not_causal`: on that run, the low segment `k = 2` reads
  the idle branch's segment that ends at `20`, after the OR's node edge `13` (no `nb`
  including it meets H_WAIT), and a trace that agrees with the idle branch on all earlier
  segments, keeps every edge (so every bracket), but pulses high, makes segment 2 fail.

**Assumed (named):** `Win` + H_NO_REVERT, H_PWR, H_SPACE (on `oe`); branch acknowledge
edges strictly increasing; the brackets, or `C1`, `C2`, `H_LATER`.

**NOT covered:** the OR is NOT closed in a network: its low segments need a PREFIX (up to
the OR's edge) of a segment of the idle branch that ends later, so `net_closed_gen`
cannot carry it with any dependency bound; a time-indexed rule with prefix guarantees
for every cell class would be needed (not done). Without a later token on the idle branch
(finite runs) the second half of the bracket is an inequality on an edge of an event that
never happens, and is not derivable. Core Lean only.
-/

namespace Formal.Cells.AssumeGuaranteeMuxOr
open Formal.Cells
open Formal.Cells.AssumeGuaranteeLinks (SegK)
open Formal.Cells.AssumeGuaranteeEnds (lutnf_segK)
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt cW vW)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.LutFbBridge2 (gc gc_even gc_odd mono_of_succ)
open Formal.Net.Ops.Gen (genF steer_gate)
open Formal.Gen Formal.Gen.Cells

/-! ## 1. Token counts per branch -/

/-- The number of tokens before token `n` steered to branch `b`. -/
def cnt (σ : Nat → Bool) (b : Bool) : Nat → Nat
  | 0 => 0
  | n + 1 => cnt σ b n + (if σ n = b then 1 else 0)

theorem cnt_succ_eq {σ : Nat → Bool} {b : Bool} {n : Nat} (h : σ n = b) :
    cnt σ b (n + 1) = cnt σ b n + 1 := by simp [cnt, h]

theorem cnt_succ_ne {σ : Nat → Bool} {b : Bool} {n : Nat} (h : σ n ≠ b) :
    cnt σ b (n + 1) = cnt σ b n := by simp [cnt, h]

theorem cnt_mono (σ : Nat → Bool) (b : Bool) {n n' : Nat} (h : n ≤ n') : cnt σ b n ≤ cnt σ b n' := by
  induction n' with
  | zero => have : n = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ n' ih =>
    rcases Nat.lt_or_ge n (n' + 1) with h' | h'
    · exact Nat.le_trans (ih (by omega)) (Nat.le_add_right _ _)
    · have : n = n' + 1 := by omega
      subst this; exact Nat.le_refl _

/-- A positive count has a last counted token. -/
theorem cnt_pred (σ : Nat → Bool) (b : Bool) :
    ∀ n d, cnt σ b n = d + 1 → ∃ n', n' < n ∧ σ n' = b ∧ cnt σ b n' = d
  | 0, d, h => by simp [cnt] at h
  | n + 1, d, h => by
    by_cases hs : σ n = b
    · rw [cnt_succ_eq hs] at h; exact ⟨n, by omega, hs, by omega⟩
    · rw [cnt_succ_ne hs] at h
      obtain ⟨n', h1, h2, h3⟩ := cnt_pred σ b n d h
      exact ⟨n', by omega, h2, h3⟩

/-- No `b` token in `[a, a')`: the count does not change. -/
theorem cnt_const (σ : Nat → Bool) (b : Bool) (a : Nat) :
    ∀ a', a ≤ a' → (∀ i, a ≤ i → i < a' → σ i ≠ b) → cnt σ b a' = cnt σ b a
  | 0, h, _ => by have : a = 0 := by omega
                  subst this; rfl
  | a' + 1, h, hn => by
    rcases Nat.lt_or_ge a (a' + 1) with h' | h'
    · rw [cnt_succ_ne (hn a' (by omega) (by omega))]
      exact cnt_const σ b a a' (by omega) (fun i h1 h2 => hn i h1 (by omega))
    · have : a = a' + 1 := by omega
      subst this; rfl

/-- The first `b` token after `n`, if there is any. -/
theorem first_after (σ : Nat → Bool) (b : Bool) (n : Nat) :
    ∀ n'', n < n'' → σ n'' = b →
      ∃ n₁, n < n₁ ∧ n₁ ≤ n'' ∧ σ n₁ = b ∧ ∀ i, n < i → i < n₁ → σ i ≠ b := by
  intro n''
  induction n'' using Nat.strongRecOn with
  | _ n'' ih =>
    intro h hb
    by_cases hex : ∃ i, n < i ∧ i < n'' ∧ σ i = b
    · obtain ⟨i, h1, h2, h3⟩ := hex
      obtain ⟨n₁, a1, a2, a3, a4⟩ := ih i h2 h1 h3
      exact ⟨n₁, a1, by omega, a3, a4⟩
    · exact ⟨n'', h, Nat.le_refl _, hb, fun i h1 h2 h3 => hex ⟨i, h1, h2, h3⟩⟩

/-- **The select enumeration and the count agree**: if `κ` enumerates (strictly increasing)
exactly the tokens with `σ n = b`, then `κ m` is branch `b`'s `m`-th token. -/
theorem cnt_kappa {σ : Nat → Bool} {b : Bool} {κ : Nat → Nat} (hκ : ∀ m, κ m < κ (m + 1))
    (hκb : ∀ m, σ (κ m) = b) (hκall : ∀ n, σ n = b → ∃ m, κ m = n) :
    ∀ m, cnt σ b (κ m) = m := by
  have km := mono_of_succ hκ
  have kinj : ∀ m m', κ m < κ m' → m < m' := by
    intro m m' h; apply Classical.byContradiction; intro hc
    have := km m' m (by omega); omega
  intro m
  induction m with
  | zero =>
    rw [cnt_const σ b 0 (κ 0) (Nat.zero_le _) (fun i _ hi hb => by
      obtain ⟨m', rfl⟩ := hκall i hb; have := kinj _ _ hi; omega)]; rfl
  | succ m ih =>
    rw [cnt_const σ b (κ m + 1) (κ (m + 1)) (by have := hκ m; omega) (fun i h1 h2 hb => by
      obtain ⟨m', rfl⟩ := hκall i hb
      have := kinj _ _ h2; have := kinj m m' (by omega); omega),
      cnt_succ_eq (hκb m), ih]

theorem kappa_cnt {σ : Nat → Bool} {b : Bool} {κ : Nat → Nat} (hκ : ∀ m, κ m < κ (m + 1))
    (hκb : ∀ m, σ (κ m) = b) (hκall : ∀ n, σ n = b → ∃ m, κ m = n) {n : Nat} (h : σ n = b) :
    κ (cnt σ b n) = n := by
  obtain ⟨m, rfl⟩ := hκall n h; rw [cnt_kappa hκ hκb hκall m]

/-! ## 2. The acknowledge OR, one segment -/

/-- **The OR's excitation edges**: token `n`'s edges on its own branch `σ n`. -/
def oe (σ : Nat → Bool) (α : Bool → Nat → Nat) (k : Nat) : Nat :=
  α (σ (k / 2)) (2 * cnt σ (σ (k / 2)) (k / 2) + k % 2)

/-- **The branch segment read by the OR's segment `k`.** -/
def sx (σ : Nat → Bool) (b : Bool) (k : Nat) : Nat :=
  2 * cnt σ b (k / 2) + (if k % 2 = 1 ∧ σ (k / 2) = b then 1 else 0)

/-- **The bracket of token `n`** (an inequality between the two branches' edges): the idle
branch's last fall comes before token `n`'s acknowledge rises, and its next rise after
token `n`'s acknowledge falls. -/
def Brk (σ : Nat → Bool) (α : Bool → Nat → Nat) (n : Nat) : Prop :=
  cW (α (!σ n)) (2 * cnt σ (!σ n) n) ≤ α (σ n) (2 * cnt σ (σ n) n) ∧
  α (σ n) (2 * cnt σ (σ n) n + 1) ≤ α (!σ n) (2 * cnt σ (!σ n) n)

theorem oe_even (σ : Nat → Bool) (α : Bool → Nat → Nat) (n : Nat) :
    oe σ α (2 * n) = α (σ n) (2 * cnt σ (σ n) n) := by
  unfold oe; rw [show 2 * n / 2 = n by omega, show 2 * n % 2 = 0 by omega]; rfl
theorem oe_odd (σ : Nat → Bool) (α : Bool → Nat → Nat) (n : Nat) :
    oe σ α (2 * n + 1) = α (σ n) (2 * cnt σ (σ n) n + 1) := by
  unfold oe; rw [show (2 * n + 1) / 2 = n by omega, show (2 * n + 1) % 2 = 1 by omega]
theorem sx_even (σ : Nat → Bool) (b : Bool) (n : Nat) : sx σ b (2 * n) = 2 * cnt σ b n := by
  unfold sx; rw [show 2 * n / 2 = n by omega, show 2 * n % 2 = 0 by omega]; simp
theorem sx_odd (σ : Nat → Bool) (n : Nat) : sx σ (σ n) (2 * n + 1) = 2 * cnt σ (σ n) n + 1 := by
  unfold sx; rw [show (2 * n + 1) / 2 = n by omega, show (2 * n + 1) % 2 = 1 by omega]; simp

theorem vW_even (d : Nat) : vW (2 * d) = false := by
  cases d with
  | zero => rfl
  | succ d => show Vph (2 * d + 1) = false; exact PipeTimed.Vph_odd d

theorem or_split (a : Bool → Nat → Bool) (b : Bool) (t : Nat) :
    (a true t || a false t) = (a b t || a (!b) t) := by
  cases b <;> simp [Bool.or_comm]

/-- **The acknowledge OR's excitation, one segment.** The two branch acknowledge pins
`a b` (edges `α b`, strictly increasing), the select sequence `σ` (token `n` is steered to
branch `σ n`; at most one branch per token), the brackets of the tokens `≤ k/2` (edge-time
inequalities, see `brk_of_causal`), and the branch segments `sx σ b k`: then segment `k`
of `a₁ ∨ a₀` with the merged edges `oe`. A HIGH segment (`k` odd) reads only the active
branch; a LOW segment reads both, and the branch that does NOT carry token `k/2` is read at
a segment that ends at its NEXT rise (see `or_not_causal`). -/
theorem or_exc_segK {σ : Nat → Bool} {a : Bool → Nat → Bool} {α : Bool → Nat → Nat}
    (hα : ∀ b j, α b j < α b (j + 1)) (k : Nat)
    (hbr : ∀ n, n ≤ k / 2 → Brk σ α n)
    (hseg : ∀ b, SegK (a b) (α b) (sx σ b k)) :
    SegK (fun t => a true t || a false t) (oe σ α) k := by
  match k with
  | 0 =>
    intro t _ ht
    have e0 : oe σ α 0 = α (σ 0) 0 := by unfold oe; simp [cnt]
    have sx0 : ∀ b, sx σ b 0 = 0 := fun b => by unfold sx; simp [cnt]
    have b0 : α (σ 0) 1 ≤ α (!σ 0) 0 := by
      have := (hbr 0 (Nat.zero_le _)).2; simpa [cnt] using this
    have m0 : α (σ 0) 0 < α (σ 0) 1 := hα (σ 0) 0
    have hs0 := hseg (σ 0); rw [sx0] at hs0
    have hs1 := hseg (!σ 0); rw [sx0] at hs1
    have ht' : t < α (σ 0) 0 := by rw [← e0]; exact ht
    have h1 : a (σ 0) t = false := hs0 t (Nat.zero_le _) ht'
    have h2 : a (!σ 0) t = false := hs1 t (Nat.zero_le _) (by omega)
    show (a true t || a false t) = false
    rw [or_split a (σ 0), h1, h2]; rfl
  | j + 1 =>
    obtain ⟨n, rfl | rfl⟩ : ∃ n, j = 2 * n ∨ j = 2 * n + 1 := ⟨j / 2, by omega⟩
    · -- high phase of token `n`: only the active branch is read
      intro t h1 h2
      have h1' : α (σ n) (2 * cnt σ (σ n) n) ≤ t := by
        have e := oe_even σ α n
        have : cW (oe σ α) (2 * n + 1) = oe σ α (2 * n) := rfl
        omega
      have h2' : t < α (σ n) (2 * cnt σ (σ n) n + 1) := by
        have e := oe_odd σ α n; omega
      have hs := hseg (σ n)
      rw [sx_odd] at hs
      have hv : a (σ n) t = Vph (2 * cnt σ (σ n) n) := hs t h1' h2'
      show (a true t || a false t) = Vph (2 * n)
      rw [or_split a (σ n), hv, PipeTimed.Vph_even, PipeTimed.Vph_even]; rfl
    · -- low phase between tokens `n` and `n + 1`: both branches are read
      intro t h1 h2
      have hk2 : (2 * n + 1 + 1) / 2 = n + 1 := by omega
      have br0 := hbr n (by omega)
      have br1 := hbr (n + 1) (by omega)
      have h1' : α (σ n) (2 * cnt σ (σ n) n + 1) ≤ t := by
        have e := oe_odd σ α n
        have : cW (oe σ α) (2 * n + 1 + 1) = oe σ α (2 * n + 1) := rfl
        omega
      have h2' : t < oe σ α (2 * (n + 1)) := by
        rw [show 2 * (n + 1) = 2 * n + 1 + 1 by omega]; exact h2
      rw [oe_even] at h2'
      have sxe : ∀ b, sx σ b (2 * n + 1 + 1) = 2 * cnt σ b (n + 1) := fun b => by
        rw [show 2 * n + 1 + 1 = 2 * (n + 1) by omega, sx_even]
      have hs := hseg (σ n); rw [sxe, cnt_succ_eq rfl] at hs
      have hsn := hseg (!σ n)
      rw [sxe, cnt_succ_ne (by cases σ n <;> simp)] at hsn
      have c1 := cnt_succ_eq (σ := σ) (n := n) rfl
      have c2 := cnt_succ_ne (σ := σ) (b := !σ n) (n := n) (by cases σ n <;> simp)
      have mb := hα (σ n) (2 * cnt σ (σ n) n)
      have mb2 := hα (σ n) (2 * cnt σ (σ n) n + 1)
      obtain ⟨b1, _⟩ := br0
      -- the token-`n+1` edge is below both branches' next segment ends
      have bnd : α (σ (n + 1)) (2 * cnt σ (σ (n + 1)) (n + 1)) ≤
          α (σ n) (2 * (cnt σ (σ n) n + 1)) ∧
          α (σ (n + 1)) (2 * cnt σ (σ (n + 1)) (n + 1)) ≤ α (!σ n) (2 * cnt σ (!σ n) n) := by
        obtain ⟨_, b3⟩ := br1
        by_cases hb : σ (n + 1) = σ n
        · rw [hb] at b3 ⊢
          rw [c1] at b3 ⊢; rw [c2] at b3
          have := hα (σ n) (2 * (cnt σ (σ n) n + 1))
          exact ⟨Nat.le_refl _, by omega⟩
        · have hb' : σ (n + 1) = !σ n := by cases h : σ (n + 1) <;> cases h' : σ n <;> simp_all
          rw [hb'] at b3 ⊢
          rw [c2] at b3 ⊢; rw [Bool.not_not, c1] at b3
          have := hα (!σ n) (2 * cnt σ (!σ n) n)
          exact ⟨by omega, Nat.le_refl _⟩
      have va : a (σ n) t = false := by
        rw [hs t h1' (by omega)]
        show Vph (2 * cnt σ (σ n) n + 1) = false
        exact PipeTimed.Vph_odd _
      have vb : a (!σ n) t = false := by
        rw [hsn t (by omega) (by omega)]; exact vW_even _
      show (a true t || a false t) = Vph (2 * n + 1)
      rw [or_split a (σ n), va, vb, PipeTimed.Vph_odd]; rfl

/-- The REAL `bd_steer` `uack` (LUT2 OR of `ack0`, `ack1`) and `bd_mux` `uor` (LUT2 OR of
`j0`, `j1`) are `a₁ ∨ a₀`. -/
theorem uack_gate (a0 a1 : Bool) :
    genF bd_steer "uack" .O ["ack0", "ack1"] [a0, a1] = (a1 || a0) :=
  (steer_gate false false a0 a1).2.2

theorem uor_gate : ∀ j0 j1 : Bool, genF bd_mux_W2 "uor" .O ["j0", "j1"] [j0, j1] = (j1 || j0) := by
  decide +kernel

/-- **The REAL steer acknowledge OR, one node segment** (`uack`, `Win` + H_NO_REVERT on its
generated excitation, H_PWR, excitation spacing `H_SPACE` on `oe`). -/
theorem uack_segK {σ : Nat → Bool} {a : Bool → Nat → Bool} {α : Bool → Nat → Nat}
    {O : Nat → Bool} {lo hi : Nat}
    (H_LUT_WIN : Win lo hi (fun t => genF bd_steer "uack" .O ["ack0", "ack1"]
      [a false t, a true t]) O)
    (H_NO_REVERT : NoRevertI lo hi (fun t => genF bd_steer "uack" .O ["ack0", "ack1"]
      [a false t, a true t]) O)
    (H_PWR : ∀ t, t < hi → O t = false)
    (H_SPACE : hi ≤ oe σ α 0 ∧ ∀ j, oe σ α j + hi < oe σ α (j + 1) + lo)
    (hα : ∀ b j, α b j < α b (j + 1)) (k : Nat)
    (hbr : ∀ n, n ≤ k / 2 → Brk σ α n)
    (hseg : ∀ b, SegK (a b) (α b) (sx σ b k)) :
    SegK O (fun j => nt O lo hi (oe σ α j) (Vph j)) k := by
  have ex : (fun t => genF bd_steer "uack" .O ["ack0", "ack1"] [a false t, a true t]) =
      fun t => a true t || a false t := funext fun t => uack_gate _ _
  rw [ex] at H_LUT_WIN H_NO_REVERT
  exact lutnf_segK H_LUT_WIN H_NO_REVERT H_PWR H_SPACE k (or_exc_segK hα k hbr hseg)

/-- **The REAL mux request OR `uor`, one node segment** (`j0`/`j1` as branches `false`/
`true`; the mux's `σ` is its control's select sequence). -/
theorem uor_segK {σ : Nat → Bool} {a : Bool → Nat → Bool} {α : Bool → Nat → Nat}
    {O : Nat → Bool} {lo hi : Nat}
    (H_LUT_WIN : Win lo hi (fun t => genF bd_mux_W2 "uor" .O ["j0", "j1"] [a false t, a true t]) O)
    (H_NO_REVERT : NoRevertI lo hi (fun t => genF bd_mux_W2 "uor" .O ["j0", "j1"]
      [a false t, a true t]) O)
    (H_PWR : ∀ t, t < hi → O t = false)
    (H_SPACE : hi ≤ oe σ α 0 ∧ ∀ j, oe σ α j + hi < oe σ α (j + 1) + lo)
    (hα : ∀ b j, α b j < α b (j + 1)) (k : Nat)
    (hbr : ∀ n, n ≤ k / 2 → Brk σ α n)
    (hseg : ∀ b, SegK (a b) (α b) (sx σ b k)) :
    SegK O (fun j => nt O lo hi (oe σ α j) (Vph j)) k := by
  have ex : (fun t => genF bd_mux_W2 "uor" .O ["j0", "j1"] [a false t, a true t]) =
      fun t => a true t || a false t := funext fun t => uor_gate _ _
  rw [ex] at H_LUT_WIN H_NO_REVERT
  exact lutnf_segK H_LUT_WIN H_NO_REVERT H_PWR H_SPACE k (or_exc_segK hα k hbr hseg)

/-! ## 3. The brackets from causality and the select enumeration -/

/-- **The brackets, derived.** Edge-time facts: `C1` (a branch acknowledge rises for token
`n` only after the input request rose for token `n`) and `C2` (the input request rises for
token `n + 1` only after the active branch's acknowledge fell for token `n`), the input
request's edges non-decreasing. Then the bracket of token `n` holds, provided the idle
branch receives a later token (`H_LATER`; without one, the idle branch's "next rise" is an
edge of an event that never happens and the second half is not derivable). -/
theorem brk_of_causal {σ : Nat → Bool} {α : Bool → Nat → Nat} {γ : Nat → Nat}
    (hγ : ∀ i j, i ≤ j → γ i ≤ γ j)
    (C1 : ∀ n, γ (2 * n) ≤ α (σ n) (2 * cnt σ (σ n) n))
    (C2 : ∀ n, α (σ n) (2 * cnt σ (σ n) n + 1) ≤ γ (2 * n + 2)) (n : Nat)
    (H_LATER : ∃ n'', n < n'' ∧ σ n'' = !σ n) : Brk σ α n := by
  refine ⟨?_, ?_⟩
  · rcases h : cnt σ (!σ n) n with _ | d
    · exact Nat.zero_le _
    · obtain ⟨n', h1, h2, h3⟩ := cnt_pred σ (!σ n) n d h
      have c2 := C2 n'
      rw [h2, h3] at c2
      have := hγ (2 * n' + 2) (2 * n) (by omega)
      have := C1 n
      show α (!σ n) (2 * d + 1) ≤ _
      omega
  · obtain ⟨n'', h1, h2⟩ := H_LATER
    obtain ⟨n₁, a1, _, a3, a4⟩ := first_after σ (!σ n) n n'' h1 h2
    have e : cnt σ (!σ n) n₁ = cnt σ (!σ n) n := by
      rw [cnt_const σ (!σ n) (n + 1) n₁ (by omega) (fun i u v => a4 i (by omega) v),
        cnt_succ_ne (by cases σ n <;> simp)]
    have c1 := C1 n₁
    rw [a3, e] at c1
    have := hγ (2 * n + 2) (2 * n₁) (by omega)
    have := C2 n
    omega

/-- **`C1` from the steer's own select enumeration**: if each branch acknowledge's edge `j`
comes after the branch's gated-request phase start `gc κ_b γ j` (a chain of H_WAITs: the
steer branch, its wire, the consumer, its wire), and `κ_b` enumerates exactly the tokens
with `σ n = b` (H_SEL_STABLE gives the gated request these phases, `gated_segK`), then
`C1` holds in the count form. -/
theorem c1_of_kappa {σ : Nat → Bool} {α : Bool → Nat → Nat} {γ : Nat → Nat}
    {κ : Bool → Nat → Nat} (hκ : ∀ b m, κ b m < κ b (m + 1)) (hκb : ∀ b m, σ (κ b m) = b)
    (hκall : ∀ b n, σ n = b → ∃ m, κ b m = n)
    (hpath : ∀ b j, gc (κ b) γ j ≤ α b j) (n : Nat) :
    γ (2 * n) ≤ α (σ n) (2 * cnt σ (σ n) n) := by
  have := hpath (σ n) (2 * cnt σ (σ n) n)
  rw [gc_even, kappa_cnt (hκ (σ n)) (hκb (σ n)) (hκall (σ n)) rfl] at this
  exact this

/-! ## 4. Non-vacuity, and why the low segment is not causal -/

namespace Wit
open Formal.Cells.AssumeGuaranteeMux.Wit (pw16 e16 pw8 e8 pw16_segK e16_inc)
open Formal.Cells.WinFifoCausal (noRevertI_shift)

/-- Alternating select: token `n` goes to branch `n` odd. Branch `false` acknowledges the
even tokens on `[16m+4, 16m+8)`, branch `true` the odd ones on `[16m+12, 16m+16)`. -/
def σw (n : Nat) : Bool := n % 2 == 1
def aw : Bool → Nat → Bool
  | false => pw16 4
  | true => pw16 12
def αw : Bool → Nat → Nat
  | false => e16 4
  | true => e16 12
/-- The steer's input request edges (token `n` on `[8n, 8n+4)`). -/
def γw (k : Nat) : Nat := 4 * k
/-- The real `uack` LUT as a 1-tick transport copy of its excitation. -/
def Ow (t : Nat) : Bool := if t = 0 then false else (aw true (t - 1) || aw false (t - 1))

theorem σw_e {n : Nat} (h : n % 2 = 0) : σw n = false := by simp [σw, h]
theorem σw_o {n : Nat} (h : n % 2 = 1) : σw n = true := by simp [σw, h]

theorem cnt_w : ∀ n, cnt σw false n = (n + 1) / 2 ∧ cnt σw true n = n / 2
  | 0 => ⟨rfl, rfl⟩
  | n + 1 => by
    obtain ⟨h0, h1⟩ := cnt_w n
    rcases Nat.mod_two_eq_zero_or_one n with h | h
    · rw [cnt_succ_eq (σw_e h), cnt_succ_ne (by rw [σw_e h]; simp), h0, h1]; omega
    · rw [cnt_succ_ne (by rw [σw_o h]; simp), cnt_succ_eq (σw_o h), h0, h1]; omega

/-- Token `n`'s acknowledge edges on its own branch: `[8n+4, 8n+8)`. -/
theorem αw_tok (n r : Nat) (hr : r < 2) :
    αw (σw n) (2 * cnt σw (σw n) n + r) = 8 * n + 4 + 4 * r := by
  obtain ⟨h0, h1⟩ := cnt_w n
  rcases Nat.mod_two_eq_zero_or_one n with h | h
  · rw [σw_e h, h0]; show e16 4 _ = _; unfold e16; omega
  · rw [σw_o h, h1]; show e16 12 _ = _; unfold e16; omega

theorem oe_w (k : Nat) : oe σw αw k = 4 * k + 4 := by
  unfold oe; rw [αw_tok (k / 2) (k % 2) (by omega)]; omega

theorem brk_w (n : Nat) : Brk σw αw n :=
  brk_of_causal (γ := γw) (fun i j h => by unfold γw; omega)
    (fun n => by have := αw_tok n 0 (by omega); simp only [Nat.add_zero] at this; rw [this]
                 unfold γw; omega)
    (fun n => by rw [αw_tok n 1 (by omega)]; unfold γw; omega) n
    ⟨n + 1, by omega, by
      rcases Nat.mod_two_eq_zero_or_one n with h | h
      · rw [σw_e h, σw_o (by omega)]; rfl
      · rw [σw_o h, σw_e (by omega)]; rfl⟩

theorem αw_inc (b : Bool) (j : Nat) : αw b j < αw b (j + 1) := by
  cases b
  · exact e16_inc 4 j
  · exact e16_inc 12 j

theorem segw (b : Bool) (k : Nat) : SegK (aw b) (αw b) k := by
  cases b
  · exact pw16_segK 4 k
  · exact pw16_segK 12 k

/-- **Non-vacuity of `uack_segK` and `brk_of_causal`** (the REAL `bd_steer` `uack`, band
`[1, 1]`; alternating select, so every low segment has an idle branch): the brackets are
DERIVED from `C1`/`C2` on the input request edges `4k`, every hypothesis holds, and every
node segment follows. -/
theorem uack_witness :
    Win 1 1 (fun t => genF bd_steer "uack" .O ["ack0", "ack1"] [aw false t, aw true t]) Ow ∧
    (∀ n, Brk σw αw n) ∧
    (∀ k, SegK Ow (fun j => nt Ow 1 1 (oe σw αw j) (Vph j)) k) := by
  have hx : ∀ t, 1 ≤ t →
      Ow t = genF bd_steer "uack" .O ["ack0", "ack1"] [aw false (t - 1), aw true (t - 1)] := by
    intro t ht; rw [uack_gate]; unfold Ow; simp [show t ≠ 0 by omega]
  have hW : Win 1 1 (fun t => genF bd_steer "uack" .O ["ack0", "ack1"] [aw false t, aw true t])
      Ow := fun t ht => ⟨t - 1, by omega, by omega, hx t ht⟩
  have hN : NoRevertI 1 1 (fun t => genF bd_steer "uack" .O ["ack0", "ack1"]
      [aw false t, aw true t]) Ow := noRevertI_shift hx
  exact ⟨hW, brk_w, fun k => uack_segK hW hN (fun t h => by unfold Ow; simp [show t = 0 by omega])
    ⟨by rw [oe_w]; omega, fun j => by rw [oe_w, oe_w]; omega⟩ αw_inc k
    (fun n _ => brk_w n) (fun b => segw b _)⟩

/-- **The low segment of the OR is not strictly causal, in either direction** (on the
witness run, OR segment `k = 2`: between token 0 on branch `false` and token 1 on branch
`true`; branch `false` is idle):

* the branch segment the lemma reads (`sx σw false 2 = 2`) ends at the idle branch's NEXT
  rise, `20`, after the OR's own node edge `13`: no dependency bound `nb` that includes it
  meets `net_closed_gen`'s H_WAIT (`gE + lo ≤ τ`);
* dropping it does not work: a trace `a0g` that agrees with branch `false` on all EARLIER
  segments (`< 2`), with branch `true` untouched and the same edges (so every bracket
  holds), but pulses high on `[9, 11)`, gives an OR excitation that is NOT clean on
  segment 2 (high at `t = 9`).

So the OR's low segments are not a function of segments that end before the OR's edge:
the end-ordered segment induction (`net_closed_gen`) cannot discharge the OR with any `nb`.
The idle branch's lowness is a PREFIX fact (up to the OR's edge) of a segment that ends
later; a time-indexed rule with prefix guarantees would be needed (not done). -/
theorem or_not_causal :
    sx σw false 2 = 2 ∧ αw false (sx σw false 2) = 20 ∧
    nt Ow 1 1 (oe σw αw 2) (Vph 2) = 13 ∧
    let a0g : Nat → Bool := fun t => aw false t || decide (9 ≤ t ∧ t < 11)
    (∀ k', k' < 2 → SegK a0g (αw false) k') ∧ (∀ k', SegK (aw true) (αw true) k') ∧
    (∀ n, Brk σw αw n) ∧ ¬ SegK (fun t => aw true t || a0g t) (oe σw αw) 2 := by
  refine ⟨by decide, by decide, by decide, ?_, fun k' => segw true k', brk_w, ?_⟩
  · intro k' hk' t h1 h2
    have e : decide (9 ≤ t ∧ t < 11) = false := by
      simp only [decide_eq_false_iff_not]
      have : αw false k' ≤ 8 := by
        show e16 4 k' ≤ 8; unfold e16; omega
      omega
    show (aw false t || decide (9 ≤ t ∧ t < 11)) = _
    rw [e, Bool.or_false]; exact segw false k' t h1 h2
  · intro h
    have := h 9 (by rw [show cW (oe σw αw) 2 = oe σw αw 1 from rfl, oe_w]; omega)
      (by rw [oe_w]; omega)
    revert this; decide

end Wit

end Formal.Cells.AssumeGuaranteeMuxOr
