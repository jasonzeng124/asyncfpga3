import Formal.Cells.ResetCapstone
import Formal.Cells.ResetWitness2Data
open Formal.Core.LutList

/-!
# Probe Bwit (shard B): a moving, varied-delay witness for gcd_hw's reset theorems

Notes: `formal/notes/B-reset-witness2.md`. Follows self-audit 4 (`SelfAuditB7.wv_frozen`):
the `D = 40` witness `ResetCapstoneWit.wRun` never moves before `E` (power-up = reset state,
every gate held), and the moving witnesses of Bsa3 have `D = W = 0`. Here one run has both.

`wv` is a GMW run (`wRun`) of the real `gNet` (all 3322 nodes, real INITs) with

    D = 2, W = 1, F = 93 (= 23·(D+W+1) + W: H_HOLD_LONG tight), E = 158.

* power-up: a pseudo-random state (`P0`, generated): 1593 of the 3257 non-rst control nodes
  are NOT at their reset value at step 0 (`pw_wrong`);
* rst 1 on `(0, F]`, 0 after (0 at power-up); every data net toggles (`datW`) the whole time;
* gate `j` takes its current LUT value exactly at the steps `k` with `k % per j = 0`,
  `per j = 1 + j % 3 ∈ {1, 2, 3}`, and holds otherwise; pin `q` of gate `j` reads its source
  `lag j q = (j + q) % 2 ∈ {0, 1}` steps late. So gate delays 1, 2 and 3 (= D + 1) and wire
  lags 0 and 1 (= W) all occur.

The run is defined for all steps by recursion (`hist`); `wRun` / `wBounded` are proved for
every step, with no computation. The values used below are computed by kernel `decide`:
* early: `wv 0 .. 2` at a few nodes, directly from the recursion;
* late (`[F - 1, E]`): `late_at` (`late_aux`), by induction over the 65 steps, with a per-step check on the
  108 wave nodes and the 6 steers only (`stepAt`, decided); every other control node is
  carried by Rst3's `gcd_wave_only` (its H_STEER_HOLD is discharged step by step from the
  previous steps), so the other 3143 control nodes are never simulated.

## Assumed / proved / NOT covered

**Assumed:** nothing beyond the imported files. The data file is untrusted and checked.

**Proved:**
* `wRun`, `wBounded`: `wv` is a GMW run of `gNet`, `Bounded 2 1`.
* `nonvac_net3`: every hypothesis of Bfw's `gcd_reset_vec_net` / `cellRunW_clean` and Rst3's
  `gcd_clean_release` (H_RST_CLEAN, H_HOLD_LONG tight, H_RST_LOW, H_STEER_HOLD on the 31-step
  window `(F + 34, E]`) holds; the theorems are applied to it (examples).
* `w_steer_tight`: H_STEER_HOLD cannot be extended: steer output 100 (`ucond_br9.O5`) is 1 at
  `E + 1`, so `E = 158` is the last admissible end.
* `reset_capstone_nonvac2`: every hypothesis of `ResetCapstone.gcd_hw_safe_after_reset`
  jointly, with this run (`D = 2`, `W = 1`, rst held to 93, `T0 = 92`).
* Non-degeneracy: `pw_wrong` (1593 wrong control nodes at power-up); `link_moves` (link
  controller `ulink_n68__1.ctl` (2439) is 1 at steps 0 and 1, falls to its reset value 0 at
  step 2, is 0 on `[92, 94]` and rises again at 95, after release); `delays_vary` (three
  gates of the matched delay `ucmpi0.udly`, after release, see their LUT value change and
  follow after 1, 2 and 3 steps respectively); `per_vary`, `lag_vary`.

**NOT covered:** the C side of the joint witness is unchanged (`frzC chW`: C's family frozen
from `T0`, and the degenerate map `μW`, `SelfAuditB7.μW_not_wiring`); B's run and C's family
are still different models joined only by H_MAP at `T0`. The delay model is one family
(periodic sampling per gate, constant lag per pin), not every GMW run; nothing about the board.
-/

namespace Formal.Cells.ResetWitness2
open Formal.Cells Formal.Cells.TernarySound Formal.Cells.ResetContract Formal.Cells.ResetGcd

/-! ## The run -/

def F : Nat := 93
def E : Nat := 158

/-- Gate `j` samples its LUT value every `per j` steps. -/
def per (j : Nat) : Nat := 1 + j % 3
def fires (j k : Nat) : Bool := k % per j == 0
/-- Pin `q` of gate `j` is `lag j q` steps old. -/
def lag (j q : Nat) : Nat := (j + q) % 2
/-- rst: 0 at power-up, 1 on `(0, F]`, 0 after. -/
def rstW (k : Nat) : Bool := decide (0 < k ∧ k ≤ F)
/-- Data nets toggle all the time. -/
def datW (k i : Nat) : Bool := (k / 4 + i) % 3 == 0
def inp (k i : Nat) : Bool := if i = 0 then rstW k else if i < 65 then datW k i else false
/-- The power-up state. -/
def v0 (i : Nat) : Bool := P0.testBit i

/-- One step: node `n` at `k + 1` from the states `c` (step `k`) and `p` (step `k - 1`). -/
def stepF (c p : Nat → Bool) (k n : Nat) : Bool :=
  match gNode n with
  | .input => inp (k + 1) n
  | .gate init pins =>
    if fires n k then lutB init (pinsB (fun q i => if lag n q = 0 then c i else p i) pins 0)
    else c n

/-- (state at `k`, state at `k - 1`). -/
def hist : Nat → (Nat → Bool) × (Nat → Bool)
  | 0 => (v0, v0)
  | k + 1 => (stepF (hist k).1 (hist k).2 k, (hist k).1)

def wv (k i : Nat) : Bool := (hist k).1 i

theorem hist_snd (k : Nat) : (hist k).2 = wv (k - 1) := by
  cases k with
  | zero => rfl
  | succ k => rfl

theorem wv_succ (k n : Nat) : wv (k + 1) n = stepF (wv k) (wv (k - 1)) k n := by
  show stepF (hist k).1 (hist k).2 k n = _
  rw [hist_snd]; rfl

theorem lag_lt (j q : Nat) : lag j q < 2 := Nat.mod_lt _ (by decide)

theorem pins_lag (k n : Nat) :
    (fun q i => if lag n q = 0 then wv k i else wv (k - 1) i) = (fun q i => wv (k - lag n q) i) := by
  funext q i
  have := lag_lt n q
  by_cases h : lag n q = 0
  · rw [ite_eq_left h, h, Nat.sub_zero]
  · rw [ite_eq_right h, show lag n q = 1 by omega]

theorem wv_gate {k n init : Nat} {pins : List Src} (hn : gNode n = .gate init pins) :
    wv (k + 1) n = if fires n k then lutB init (pinsB (fun q i => wv (k - lag n q) i) pins 0)
      else wv k n := by
  rw [wv_succ, ← pins_lag]; unfold stepF; rw [hn]

theorem wv_input {k n : Nat} (hk : 0 < k) (hn : gNode n = .input) : wv k n = inp k n := by
  obtain ⟨k', rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [wv_succ]; unfold stepF; rw [hn]

def wrd (k j q : Nat) : Nat := k - lag j q

/-- **The run** (GMW: every gate holds or takes its current LUT value, read through `wrd`). -/
def wRun : Run gNet wv where
  rd := wrd
  rd_le _ _ _ := Nat.sub_le _ _
  gate k j init pins h := by
    rw [wv_gate (n := j) h]
    by_cases hf : fires j k = true
    · right; rw [ite_eq_left hf]; rfl
    · left; rw [ite_eq_right hf]

theorem per_cases (j : Nat) : per j = 1 ∨ per j = 2 ∨ per j = 3 := by unfold per; omega

/-- Every gate samples at least once in any 3 consecutive steps. -/
theorem fire_in (j k : Nat) : ∃ i, k ≤ i ∧ i ≤ k + 2 ∧ fires j i = true := by
  have hf : ∀ i, i % per j = 0 → fires j i = true := by
    intro i h; unfold fires; rw [h]; rfl
  rcases per_cases j with h | h | h
  · exact ⟨k, Nat.le_refl _, by omega, hf k (by rw [h]; omega)⟩
  · by_cases hk : k % 2 = 0
    · exact ⟨k, Nat.le_refl _, by omega, hf k (by rw [h]; omega)⟩
    · exact ⟨k + 1, by omega, by omega, hf _ (by rw [h]; omega)⟩
  · by_cases hk : k % 3 = 0
    · exact ⟨k, Nat.le_refl _, by omega, hf k (by rw [h]; omega)⟩
    · by_cases hk1 : k % 3 = 2
      · exact ⟨k + 1, by omega, by omega, hf _ (by rw [h]; omega)⟩
      · exact ⟨k + 2, by omega, by omega, hf _ (by rw [h]; omega)⟩

/-- **Bounded `D = 2`, `W = 1`.** -/
theorem wBounded : Bounded gNet wv wRun 2 1 where
  wire k j q := by
    show k ≤ wrd k j q + 1
    unfold wrd; have := lag_lt j q; omega
  gate k j init pins b h hb := by
    obtain ⟨i, h1, h2, hf⟩ := fire_in j k
    refine ⟨i + 1, by omega, by omega, ?_⟩
    rw [wv_gate (n := j) h, ite_eq_left hf]
    exact hb i h1 (by omega)

/-! ## The reset hypotheses -/

theorem w_rst_clean : ∀ k, 0 < k → k ≤ F → TernaryPhases.InputsIn gNet wv gA k := by
  intro k h1 h2 n hn
  rw [wv_input h1 hn]
  unfold gA inp
  by_cases h0 : n = 0
  · subst h0
    rw [ite_eq_left rfl, ite_eq_left rfl, show rstW k = true from decide_eq_true ⟨h1, h2⟩]; rfl
  · rw [ite_eq_right h0, ite_eq_right h0]; rfl

theorem w_hold_long : (maxRank + 2) * (2 + 1 + 1) + 1 ≤ F := by decide

theorem w_rst_low : ∀ k, F < k → wv k 0 = false := by
  intro k h1
  rw [wv_input (by omega) rfl]
  unfold inp rstW; rw [ite_eq_left rfl]; exact decide_eq_false (by omega)

/-- Every control node is at its reset value on `[92, 93]` (Rst2). -/
theorem w_reset (n : Nat) (hc : gCtl n = true) : ∀ k, 92 ≤ k → k ≤ F → wv k n = gR n :=
  gcd_reset_binary wRun wBounded F w_rst_clean n hc

/-! ## After release: the wave, computed on its 108 nodes -/

/-- The data state at step `k` (`k ∈ [F - 1, E]`). -/
def lateAt (k : Nat) : Nat := lateL.getD (k - (F - 1)) 0

/-- The reduced state: rst and data from the waveform, wave nodes from `R`, every other
control node at its reset value. -/
def red (R k i : Nat) : Bool :=
  if i = 0 then inp k 0
  else if ResetGcdWave.wR i ≠ 0 then R.testBit i
  else if gCtl i then gR i else inp k i

def redAt (k i : Nat) : Bool := red (lateAt k) k i

def wavesL : List Nat := (ResetGcdWave.wL.map (·.1)).filter (· != 0)

/-- One step on the wave nodes and the 6 steers (which must stay 0). -/
def stepChk (Rp R Rn k : Nat) : Bool :=
  wavesL.all (fun w => stepF (red R k) (red Rp (k - 1)) k w == Rn.testBit w) &&
    ResetGcdWave.zL.all (fun z => !stepF (red R k) (red Rp (k - 1)) k z)

def stepAt (m : Nat) : Bool :=
  stepChk (lateL.getD m 0) (lateL.getD (m + 1) 0) (lateL.getD (m + 2) 0) (F + m)

theorem sa0 : (List.range' 0 11).all stepAt = true := by decide +kernel
theorem sa1 : (List.range' 11 11).all stepAt = true := by decide +kernel
theorem sa2 : (List.range' 22 11).all stepAt = true := by decide +kernel
theorem sa3 : (List.range' 33 11).all stepAt = true := by decide +kernel
theorem sa4 : (List.range' 44 11).all stepAt = true := by decide +kernel
theorem sa5 : (List.range' 55 10).all stepAt = true := by decide +kernel

theorem sa_mem {lo n : Nat} (h : (List.range' lo n).all stepAt = true) {m : Nat} (h1 : lo ≤ m)
    (h2 : m < lo + n) : stepAt m = true :=
  List.all_eq_true.1 h m (List.mem_range'_1.2 ⟨h1, h2⟩)

theorem stepAt_ok (m : Nat) (h : m < 65) : stepAt m = true := by
  rcases Nat.lt_or_ge m 11 with h0 | h0
  · exact sa_mem sa0 (by omega) (by omega)
  rcases Nat.lt_or_ge m 22 with h1 | h1
  · exact sa_mem sa1 (by omega) (by omega)
  rcases Nat.lt_or_ge m 33 with h2 | h2
  · exact sa_mem sa2 (by omega) (by omega)
  rcases Nat.lt_or_ge m 44 with h3 | h3
  · exact sa_mem sa3 (by omega) (by omega)
  rcases Nat.lt_or_ge m 55 with h4 | h4
  · exact sa_mem sa4 (by omega) (by omega)
  · exact sa_mem sa5 (by omega) (by omega)

/-- Static checks: the wave nodes are control nodes at their reset value in the data at
`F - 1` and `F`; the steers are non-wave control nodes with reset value 0; every non-control
node below `gM` is an input. -/
def baseChk : Bool := wavesL.all (fun w => gCtl w && ((lateL.getD 0 0).testBit w == gR w) &&
  ((lateL.getD 1 0).testBit w == gR w))
theorem base_ok : baseChk = true := by decide +kernel

def zChk : Bool := ResetGcdWave.zL.all (fun z => gCtl z && ResetGcdWave.wR z == 0 && !gR z && z != 0)
theorem z_ok : zChk = true := by decide +kernel

def isInp (i : Nat) : Bool := match gNode i with | .input => true | .gate _ _ => false
theorem inputs_ok : (List.range' 0 3322).all (fun i => gCtl i || isInp i) = true := by
  decide +kernel

theorem ctl_or_input (i : Nat) (h : gCtl i = false) : gNode i = .input := by
  by_cases hi : i < gM
  · have := List.all_eq_true.1 inputs_ok i (List.mem_range'_1.2 ⟨Nat.zero_le _, hi⟩)
    rw [h, Bool.false_or] at this
    unfold isInp at this
    split at this
    · assumption
    · cases this
  · unfold gNode; rw [ite_eq_right hi]

theorem mem_waves {i : Nat} (hw : ResetGcdWave.wR i ≠ 0) (h0 : i ≠ 0) : i ∈ wavesL := by
  obtain ⟨q, hq, hq1, _, _⟩ := ResetGcdWave.wq hw
  unfold wavesL
  refine List.mem_filter.2 ⟨List.mem_map.2 ⟨q, hq, hq1⟩, ?_⟩
  simpa using h0

theorem z_facts {z : Nat} (hz : z ∈ ResetGcdWave.zL) :
    gCtl z = true ∧ ResetGcdWave.wR z = 0 ∧ gR z = false ∧ z ≠ 0 := by
  have := List.all_eq_true.1 z_ok z hz
  simp only [Bool.and_eq_true, beq_iff_eq, Bool.not_eq_true', bne_iff_ne, ne_eq] at this
  exact ⟨this.1.1.1, this.1.1.2, this.1.2, this.2⟩

theorem lateAt_eq (m : Nat) : lateAt (F - 1 + m) = lateL.getD m 0 := by
  unfold lateAt; congr 1; omega

/-- Assembling a full state from its parts. -/
theorem state_of (j : Nat) (hj : 0 < j)
    (hctl : ∀ i, gCtl i = true → ResetGcdWave.wR i = 0 → i ≠ 0 → wv j i = gR i)
    (hwave : ∀ w ∈ wavesL, wv j w = (lateAt j).testBit w) : ∀ i, wv j i = redAt j i := by
  intro i
  unfold redAt red
  by_cases h0 : i = 0
  · subst h0; rw [ite_eq_left rfl]; exact wv_input hj rfl
  rw [ite_eq_right h0]
  by_cases hw : ResetGcdWave.wR i ≠ 0
  · rw [ite_eq_left hw]; exact hwave i (mem_waves hw h0)
  rw [ite_eq_right hw]
  cases hc : gCtl i
  · rw [ite_eq_right (by simp)]; exact wv_input hj (ctl_or_input i hc)
  · rw [ite_eq_left rfl]; exact hctl i hc (by omega) h0

theorem base_facts (w : Nat) (hw : w ∈ wavesL) :
    gCtl w = true ∧ (lateL.getD 0 0).testBit w = gR w ∧ (lateL.getD 1 0).testBit w = gR w := by
  have := List.all_eq_true.1 base_ok w hw
  simp only [Bool.and_eq_true, beq_iff_eq] at this
  exact ⟨this.1.1, this.1.2, this.2⟩

/-- **The late segment**: on `[F - 1, E]` the run is the reduced state built from `lateL`. -/
theorem late_aux : ∀ m, F + m ≤ E → ∀ j, F - 1 ≤ j → j ≤ F + m → ∀ i, wv j i = redAt j i := by
  intro m
  induction m with
  | zero =>
    intro _ j h1 h2
    have hF : F = 93 := rfl
    apply state_of j (by omega)
    · intro i hc _ _; exact w_reset i hc j (by omega) h2
    · intro w hw
      obtain ⟨hc, e0, e1⟩ := base_facts w hw
      rw [w_reset w hc j (by omega) h2]
      rcases (show j = F - 1 + 0 ∨ j = F - 1 + 1 by omega) with e | e
      · rw [e, lateAt_eq, e0]
      · rw [e, lateAt_eq, e1]
  | succ m ih =>
    intro hkE j h1 h2
    have hF : F = 93 := rfl
    have hE : E = 158 := rfl
    have IH := ih (by omega)
    generalize hk : F + m = k at IH hkE h2
    have hFk : F ≤ k := by omega
    rw [show F + (m + 1) = k + 1 by omega] at hkE h2
    by_cases hj : j ≤ k
    · exact IH j h1 hj
    have hjk : j = k + 1 := by omega
    subst hjk
    -- the step at `k`, on the reduced states
    have e1 : wv k = redAt k := funext (IH k (by omega) (Nat.le_refl _))
    have e2 : wv (k - 1) = redAt (k - 1) := funext (IH (k - 1) (by omega) (by omega))
    have hst : ∀ n, wv (k + 1) n = stepF (redAt k) (redAt (k - 1)) k n := by
      intro n; rw [wv_succ, e1, e2]
    have hsa := stepAt_ok (k - F) (by omega)
    have r0 : lateL.getD (k - F) 0 = lateAt (k - 1) := by rw [← lateAt_eq]; congr 1; omega
    have r1 : lateL.getD (k - F + 1) 0 = lateAt k := by rw [← lateAt_eq]; congr 1; omega
    have r2 : lateL.getD (k - F + 2) 0 = lateAt (k + 1) := by rw [← lateAt_eq]; congr 1; omega
    unfold stepAt stepChk at hsa
    rw [r0, r1, r2, show F + (k - F) = k by omega] at hsa
    simp only [Bool.and_eq_true] at hsa
    obtain ⟨hwv, hzs⟩ := hsa
    -- H_STEER_HOLD up to `k + 1`
    have hsteer : ∀ t z, z ∈ ResetGcdWave.zL → F < t → t ≤ k + 1 → wv t z = false := by
      intro t z hz _ ht2
      by_cases ht : t ≤ k
      · obtain ⟨hc, hw0, hg, hz0⟩ := z_facts hz
        rw [IH t (by omega) ht]
        unfold redAt red
        rw [ite_eq_right hz0, ite_eq_right (by simpa using hw0), ite_eq_left hc, hg]
      · rw [show t = k + 1 by omega, hst]
        have := List.all_eq_true.1 hzs z hz
        simp only [Bool.not_eq_true'] at this
        exact this
    have hsettled : ∀ t n, t ≤ F → F ≤ t + 1 → gCtl n = true → n ≠ 0 → wv t n = gR n :=
      fun t n h1 h2 hc _ => w_reset n hc t (by omega) h1
    have hquiet := ResetGcdWave.gcd_wave_only wRun wBounded F F (k + 1) (Nat.le_refl _) hsettled
      (fun t h1 _ => w_rst_low t h1) hsteer
    apply state_of (k + 1) (by omega)
    · intro i hc hw _; exact hquiet (k + 1) i (by omega) (Nat.le_refl _) hc hw
    · intro w hw
      rw [hst]
      have := List.all_eq_true.1 hwv w hw
      simp only [beq_iff_eq] at this
      exact this

theorem late_at (j : Nat) (h1 : F - 1 ≤ j) (h2 : j ≤ E) (i : Nat) : wv j i = redAt j i :=
  late_aux (E - F) (by decide) j h1 (by have : F = 93 := rfl; have : E = 158 := rfl; omega) i

/-- **H_STEER_HOLD**, in fact on all of `(F, E]`. -/
theorem w_steer_hold : ∀ k z, z ∈ ResetGcdWave.zL → F < k → k ≤ E → wv k z = false := by
  intro k z hz h1 h2
  obtain ⟨hc, hw0, hg, hz0⟩ := z_facts hz
  rw [late_at k (by omega) h2]
  unfold redAt red
  rw [ite_eq_right hz0, ite_eq_right (by simpa using hw0), ite_eq_left hc, hg]

/-- **H_STEER_HOLD is tight in this run**: steer output 100 (`ucond_br9.u.O5`) is 1 at
`E + 1`. -/
theorem w_steer_tight : wv (E + 1) 100 = true := by
  rw [wv_succ, funext (late_at E (by decide) (Nat.le_refl _)),
    funext (late_at (E - 1) (by decide) (by decide))]
  decide +kernel

/-! ## Non-vacuity, jointly -/

/-- **Non-degenerate non-vacuity** of Bfw's `cellRunW_clean` / `gcd_reset_vec_net` /
`gcd_reset_vec_of_net` and Rst3's `gcd_clean_release`: a bounded GMW run of the real `gNet`
with `D = 2`, `W = 1`, from a power-up state with 1593 wrong control nodes, with gate delays
1..3 and wire lags 0..1, meets H_RST_CLEAN, H_HOLD_LONG (tight), H_RST_LOW and H_STEER_HOLD,
the last on the 31-step window `(127, 158]`. -/
theorem nonvac_net3 :
    ∃ (v : Nat → Nat → Bool) (Rn : Run gNet v), Bounded gNet v Rn 2 1 ∧
      (∀ k, 0 < k → k ≤ 93 → TernaryPhases.InputsIn gNet v gA k) ∧
      (maxRank + 2) * (2 + 1 + 1) + 1 ≤ 93 ∧
      (∀ k, 93 < k → k ≤ 158 → v k 0 = false) ∧
      (∀ k z, z ∈ ResetGcdWave.zL → 93 + 34 < k → k ≤ 158 → v k z = false) ∧
      93 + 34 + 31 = 158 :=
  ⟨wv, wRun, wBounded, w_rst_clean, w_hold_long, fun k h1 _ => w_rst_low k h1,
    fun k z hz h1 h2 => w_steer_hold k z hz (by have : F = 93 := rfl; omega) h2, rfl⟩

/-- The network theorems apply to the witness (nothing per-cell supplied). -/
example : True := by
  have _h1 := ResetGcdVec2.gcd_reset_vec_net (Rn := wRun) wBounded F E w_rst_clean
    w_hold_long (fun k h1 _ => w_rst_low k h1)
    (fun k z hz h1 h2 => w_steer_hold k z hz (by have : F = 93 := rfl; omega) h2)
  have _h2 := ResetGcdWave.gcd_clean_release wRun wBounded F E w_rst_clean w_hold_long
    (fun k h1 _ => w_rst_low k h1)
    (fun k z hz h1 h2 => w_steer_hold k z hz (by have : F = 93 := rfl; omega) h2)
  trivial

open Formal.Net Formal.Net.Handshake Formal.Net.CapNet Formal.Net.CapNet.Gcd in
/-- **Joint non-vacuity of `ResetCapstone.gcd_hw_safe_after_reset`** (a = 12, b = 18) with
the moving run: `D = 2`, `W = 1`, rst held on `(0, 93]`, `T0 = T0of 2 1 = 92`, the map `μW`
and C's frozen family `frzC chW` (both unchanged from `reset_capstone_nonvac`). -/
theorem reset_capstone_nonvac2 :
    ∃ (v : Nat → Nat → Bool) (Rn : Run gNet v) (D W E : Nat) (r : Fin NC → Chan)
      (μ : ResetCapstone.ChanMap),
      2 ≤ D ∧ 1 ≤ W ∧ Bounded gNet v Rn D W ∧
      (∀ k, 0 < k → k ≤ E → TernaryPhases.InputsIn gNet v gA k) ∧
      ResetCapstone.T0of D W ≤ E ∧ ResetCapstone.MapOK μ ∧
      (∀ c, (r c).req (ResetCapstone.T0of D W) = v (ResetCapstone.T0of D W) (μ.μR c) ∧
        (r c).ack (ResetCapstone.T0of D W) = v (ResetCapstone.T0of D W) (μ.μA c)) ∧
      (∀ o : Fin NO, ResetCapstone.CellA r (ResetCapstone.T0of D W) (srcV 12 18) (opAt o)) ∧
      (∀ c, ResetCapstone.HeldA (r c) (ResetCapstone.T0of D W)) ∧
      (∀ t, ResetCapstone.T0of D W ≤ t → Handshake.riseB (r start).req t = false) := by
  refine ⟨wv, wRun, 2, 1, F, ResetCapstone.frzC Wit.chW, ResetCapstone.μW,
    by decide, by decide, wBounded, w_rst_clean, by decide, ResetCapstone.μW_ok, ?_, ?_, ?_, ?_⟩
  · intro c
    obtain ⟨a1, _, a3, _, _, _, a7, a8⟩ := ResetCapstone.μW_facts c
    refine ⟨?_, ?_⟩
    · rw [w_reset _ a1 _ (by decide) (by decide), a7]; rfl
    · rw [w_reset _ a3 _ (by decide) (by decide), a8]; rfl
  · intro o
    exact ResetCapstone.frozen_cellA _ _ _ _ (ResetCapstone.side_all o) (Wit.w_cells o)
  · intro c t _ _ _; rfl
  · intro t _; unfold Handshake.riseB; cases ResetCapstone.hot start <;> rfl

/-! ## Non-degeneracy -/

/-- The power-up state is not the reset state: 1593 of the non-rst control nodes are wrong. -/
theorem pw_wrong :
    ((List.range' 0 3322).filter (fun n => gCtl n && n != 0 && wv 0 n != gR n)).length = 1593 := by
  decide +kernel

/-- **A node that moves**: the link controller `ulink_n68__1.ctl` (node 2439, a `bd_c2n`,
reset value 0) is 1 at power-up and still 1 at step 1, falls to 0 at step 2 (rst held), is at
its reset value 0 on `[92, 94]`, and rises again at step 95 after release (it is on Rst2's
frontier). -/
theorem link_moves :
    gR 2439 = false ∧ wv 0 2439 = true ∧ wv 1 2439 = true ∧ wv 2 2439 = false ∧
      (∀ k, 92 ≤ k → k ≤ 94 → wv k 2439 = false) ∧ wv 95 2439 = true := by
  have hc : gCtl 2439 = true := by decide +kernel
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel, ?_, ?_⟩
  · intro k h1 h2
    rw [late_at k (by have : F = 93 := rfl; omega) (by have : E = 158 := rfl; omega)]
    have : k = 92 ∨ k = 93 ∨ k = 94 := by omega
    rcases this with rfl | rfl | rfl <;> decide +kernel
  · rw [late_at 95 (by decide) (by decide)]; decide +kernel

/-- The LUT value gate `j` sees at step `k`, on the reduced late states. -/
def excR (k j : Nat) : Bool :=
  match gNode j with
  | .input => false
  | .gate init pins => lutB init (pinsB (fun q i => redAt (k - lag j q) i) pins 0)

theorem exc_late {k j init : Nat} {pins : List Src} (hj : gNode j = .gate init pins)
    (h1 : F ≤ k) (h2 : k ≤ E) : wRun.exc init pins k j = excR k j := by
  unfold excR Run.exc; rw [hj]
  show lutB init (pinsB (fun q i => wv (k - lag j q) i) pins 0) = _
  have : (fun q i => wv (k - lag j q) i) = (fun q i => redAt (k - lag j q) i) := by
    funext q i
    have := lag_lt j q
    exact late_at _ (by omega) (by omega) i
  rw [this]

/-- Gate `j` sees LUT value `b` on `[k, k + d)` while showing `!b`, and shows `b` at `k + d`:
it follows its excitation after exactly `d` steps. -/
def Resp (j k d : Nat) (b : Bool) : Prop :=
  ∃ init pins, gNode j = .gate init pins ∧
    (∀ i, k ≤ i → i < k + d → wRun.exc init pins i j = b ∧ wv i j = !b) ∧ wv (k + d) j = b

def respChk (j k d : Nat) (b : Bool) : Bool :=
  (List.range' k d).all (fun i => excR i j == b && redAt i j == !b) && redAt (k + d) j == b

theorem resp_of {j k d init : Nat} {pins : List Src} {b : Bool} (hj : gNode j = .gate init pins)
    (h1 : F ≤ k) (h2 : k + d ≤ E) (h : respChk j k d b = true) : Resp j k d b := by
  unfold respChk at h
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  refine ⟨init, pins, hj, fun i hi1 hi2 => ?_, ?_⟩
  · have := List.all_eq_true.1 h.1 i (List.mem_range'_1.2 ⟨hi1, hi2⟩)
    simp only [Bool.and_eq_true, beq_iff_eq] at this
    rw [exc_late hj (by omega) (by omega), late_at i (by omega) (by omega)]
    exact this
  · rw [late_at _ (by omega) h2]; exact h.2

/-- **Gate delays vary in the run** (after release, three consecutive elements of the matched
delay `ucmpi0.udly`): `g[1]` (node 69) follows its LUT value after
1 step, `g[3]` (node 71) after 2 steps, `g[6]` (node 74) after 3 = D + 1 steps. -/
theorem delays_vary : Resp 69 101 1 true ∧ Resp 71 104 2 true ∧ Resp 74 109 3 true :=
  ⟨resp_of rfl (by decide) (by decide) (by decide +kernel),
    resp_of rfl (by decide) (by decide) (by decide +kernel),
    resp_of rfl (by decide) (by decide) (by decide +kernel)⟩

theorem per_vary : per 69 = 1 ∧ per 67 = 2 ∧ per 71 = 3 := ⟨rfl, rfl, rfl⟩
theorem lag_vary : lag 69 0 = 1 ∧ lag 69 1 = 0 := ⟨rfl, rfl⟩

/-- **Summary of non-degeneracy**: `D > 0` and `W > 0`; some node is wrong at power-up and
moves at a step `t > 0`; two gates follow their excitation with different delays. -/
theorem nondegenerate :
    0 < 2 ∧ 0 < 1 ∧
    (∃ n t, 0 < t ∧ gCtl n = true ∧ wv 0 n ≠ gR n ∧ wv t n ≠ wv (t + 1) n ∧ wv (t + 1) n = gR n) ∧
    (∃ j1 j2 k1 k2 d1 d2 b1 b2, d1 ≠ d2 ∧ Resp j1 k1 d1 b1 ∧ Resp j2 k2 d2 b2) := by
  obtain ⟨hg, h0, h1, h2, _, _⟩ := link_moves
  refine ⟨by decide, by decide, ⟨2439, 1, by decide, by decide +kernel, ?_, ?_, ?_⟩,
    ⟨69, 74, 101, 109, 1, 3, true, true, by decide, delays_vary.1, delays_vary.2.2⟩⟩
  · rw [h0, hg]; decide
  · rw [h1, h2]; decide
  · rw [h2, hg]

end Formal.Cells.ResetWitness2
