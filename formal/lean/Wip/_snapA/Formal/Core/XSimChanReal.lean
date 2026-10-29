import Mathlib.Basic.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Algebra.Order.Archimedean.Real.Basic
import Formal.Core.XSimChan
import Formal.Core.Delay.Pure
import Formal.Core.Delay.Inertial

/-!
# Formal.Core.XSimChanReal — `XSim`/`xaudit` cells over continuous time: transport and inertial

Probe XSound2 (shard A). See `formal/notes/A-xsound2.md`.

`XSimChan.sound_cells` proves the X-window simulator sound in any time domain
`τ` with a cell map `c : τ → ℕ`, for every gate whose channel satisfies the
step-level property `ChanCells c lo hi`. Here `τ = ℝ` (seconds, ps, any unit),
cells have width `q > 0` (`CellMap q c`: cell `k ≥ 1` lies in `[k q, (k+1) q)`,
cell 0 in `(-∞, q)`; `⌊t/q⌋₊` is one, `cellMap_floor`), and the channels are
the `Core/Delay` ones:

* `Follows Lo Hi x y`: if `x` is constantly `v` on `[s - Hi, s - Lo]`, then
  `y s = v`. The continuous analogue of `XSim.WinCh`.
  - `chan_follows`: transport `DelayPure.Chan lo hi` follows with `[lo, hi]`;
  - `inertialRD_follows`: `InertialRD ρ Δ` (`0 ≤ ρ`) follows with `[Δ, Δ + ρ]`;
  - `boundedInertial_follows`: `BoundedInertial ρ L H` follows with `[L, H + ρ]`.
* `chanCells_of_follows`: a `Follows Lo Hi` channel is `ChanCells c lo hi` as
  soon as `lo * q ≤ Lo` and `Hi ≤ hi * q` (step band = ps band rounded
  outwards: `lo = ⌊Lo/q⌋`, `hi = ⌈Hi/q⌉`).
* `boundedInertial_chanCells`: sharper for inertial: `BoundedInertial ρ L H` is
  `ChanCells c lo hi` when `lo q ≤ L`, `H ≤ hi q` and the rejection window is
  no wider than the abstract window, `ρ ≤ (hi + 1 - lo) q`.
* `inertial_wide_not_chanCells`: and that side condition is necessary. For
  every `q > 0`, `1 ≤ lo ≤ hi` and `ρ > (hi + 1 - lo) q` there is an input and
  a `BoundedInertial ρ (lo q) (hi q)` output (the filtered pulse) that is NOT
  `ChanCells ⌊·/q⌋₊ lo hi`. `cex_real` is the end-to-end failure on a
  one-buffer network: the abstract simulation prints `1`, the inertial
  behaviour is `0`.
* `PhysChan q lo hi`: a gate channel that is transport with band `[L, H]` or
  bounded inertial with band `[L, H]` and window `ρ`, under the side conditions
  above. `physChan_chanCells` feeds `sound_cells`; `XSimChanTern.physChan_nodeChan`
  places it inside `TernaryChannels.NodeChan (lo q) (hi q)`, the class for which
  the untimed ternary analysis is sound (`TernaryChannels.rcausal_of_nodeChan`).
* `sound_real`: soundness of `XSim.val` for ℝ-time networks of `PhysChan`
  gates (`1 ≤ lo` on every gate, so every lower delay bound is `≥ q > 0`;
  `TernaryChannels.zero_delay_chan_unsound`/`zero_delay_inertial_unsound`
  show that lower bound 0 is genuinely unsound).
-/

namespace Formal.Core.XSimChanReal

open Formal.Core K3
open Formal.Core.XSim
open Formal.Core.XSimChan

/-! ## 1. Cells of width `q` -/

/-- `c` maps each instant to its cell: cell `k ≥ 1` lies in `[k q, (k+1) q)`,
cell 0 in `(-∞, q)`. -/
def CellMap (q : ℝ) (c : ℝ → ℕ) : Prop :=
  ∀ t, t < ((c t : ℝ) + 1) * q ∧ (1 ≤ c t → (c t : ℝ) * q ≤ t)

/-- `⌊t / q⌋₊` is a cell map of width `q`. -/
theorem cellMap_floor {q : ℝ} (hq : 0 < q) : CellMap q (fun t => ⌊t / q⌋₊) := by
  intro t
  refine ⟨?_, fun h1 => ?_⟩
  · have := Nat.lt_floor_add_one (t / q)
    calc t = t / q * q := (div_mul_cancel₀ t hq.ne').symm
      _ < _ := mul_lt_mul_of_pos_right this hq
  · have hpos : 0 ≤ t / q := by
      by_contra hn
      have := Nat.floor_of_nonpos (le_of_lt (lt_of_not_ge hn))
      omega
    have := Nat.floor_le hpos
    calc (⌊t / q⌋₊ : ℝ) * q ≤ t / q * q := mul_le_mul_of_nonneg_right this hq.le
      _ = t := div_mul_cancel₀ t hq.ne'

theorem cell_ge {q : ℝ} {c : ℝ → ℕ} (hc : CellMap q c) (hq : 0 < q) {m : ℕ} {τ : ℝ}
    (h : (m : ℝ) * q ≤ τ) : m ≤ c τ := by
  have h1 := (hc τ).1
  have : (m : ℝ) < (c τ : ℝ) + 1 := by
    by_contra hn
    have : ((c τ : ℝ) + 1) * q ≤ (m : ℝ) * q := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hq.le
    linarith
  exact_mod_cast Nat.lt_succ_iff.mp (by exact_mod_cast this)

theorem cell_le {q : ℝ} {c : ℝ → ℕ} (hc : CellMap q c) (hq : 0 < q) {m : ℕ} {τ : ℝ}
    (h : τ < ((m : ℝ) + 1) * q) : c τ ≤ m := by
  by_cases h0 : c τ = 0
  · omega
  have h2 := (hc τ).2 (by omega)
  have : (c τ : ℝ) < (m : ℝ) + 1 := by
    by_contra hn
    have : ((m : ℝ) + 1) * q ≤ (c τ : ℝ) * q := mul_le_mul_of_nonneg_right (le_of_not_gt hn) hq.le
    linarith
  exact Nat.lt_succ_iff.mp (by exact_mod_cast this)

/-- Every instant of the abstract window of cell `k` (cells `[k - hi, k - lo]`)
contains the real interval `[(k - hi) q, (k + 1 - lo) q)` (lower end `-∞` when
`k < hi`). -/
theorem in_window {q : ℝ} {c : ℝ → ℕ} (hc : CellMap q c) (hq : 0 < q) {k lo hi : ℕ} {τ : ℝ}
    (h1 : hi ≤ k → ((k : ℝ) - hi) * q ≤ τ) (h2 : τ < ((k : ℝ) + 1 - lo) * q) :
    k - hi ≤ c τ ∧ c τ ≤ k - lo := by
  refine ⟨?_, ?_⟩
  · by_cases hk : hi ≤ k
    · apply cell_ge hc hq
      rw [Nat.cast_sub hk]; exact h1 hk
    · omega
  · apply cell_le hc hq
    have : (k : ℝ) + 1 - lo ≤ ((k - lo : ℕ) : ℝ) + 1 := by
      by_cases hk : lo ≤ k
      · rw [Nat.cast_sub hk]; linarith
      · have : (k : ℝ) + 1 ≤ lo := by exact_mod_cast (by omega : k + 1 ≤ lo)
        have : (0 : ℝ) ≤ ((k - lo : ℕ) : ℝ) := Nat.cast_nonneg _
        linarith
    calc τ < ((k : ℝ) + 1 - lo) * q := h2
      _ ≤ _ := mul_le_mul_of_nonneg_right this hq.le

/-! ## 2. Window-determined channels -/

/-- **Continuous window channel**: if the input is constantly `v` on
`[s - Hi, s - Lo]`, the output at `s` is `v`. -/
def Follows (Lo Hi : ℝ) (x y : ℝ → Bool) : Prop :=
  ∀ s v, (∀ τ, s - Hi ≤ τ → τ ≤ s - Lo → x τ = v) → y s = v

theorem follows_mono {Lo Hi Lo' Hi' : ℝ} {x y : ℝ → Bool} (h1 : Lo' ≤ Lo) (h2 : Hi ≤ Hi')
    (h : Follows Lo Hi x y) : Follows Lo' Hi' x y :=
  fun s v hv => h s v (fun τ a b => hv τ (by linarith) (by linarith))

/-- Transport `[lo, hi]` follows its band. -/
theorem chan_follows {lo hi : ℝ} {x y : ℝ → Bool} (h : DelayPure.Chan lo hi x y) :
    Follows lo hi x y := by
  obtain ⟨r, hr⟩ := h
  intro s v hv
  rw [hr s]
  exact hv _ (r.ge s) (r.le s)

/-- Inertial (window `ρ ≥ 0`, delay `Δ`) follows `[Δ, Δ + ρ]`: the rejection
window is added to the upper end. -/
theorem inertialRD_follows {ρ Δ : ℝ} (hρ : 0 ≤ ρ) {x y : ℝ → Bool}
    (h : DelayInertial.InertialRD ρ Δ x y) : Follows Δ (Δ + ρ) x y := by
  intro s v hv
  obtain ⟨τ, hτ, _, hb, hmax⟩ := h (s - Δ)
  have hb' : y s = x τ := by have := hb; simp only [sub_add_cancel] at this; exact this
  rw [hb']
  by_cases ha : s - Δ - ρ ≤ τ
  · exact hv τ (by linarith) hτ
  · have hlt : τ < s - Δ - ρ := lt_of_not_ge ha
    have hst : DelayInertial.Stable x (s - Δ - ρ) ρ := fun w h1 h2 => by
      rw [hv w (by linarith) (by linarith), hv _ (by linarith) (by linarith)]
    rw [← hmax _ hlt (by linarith) hst]
    exact hv _ (by linarith) (by linarith)

theorem boundedInertial_follows {ρ L H : ℝ} (hρ : 0 ≤ ρ) {x y : ℝ → Bool}
    (h : DelayInertial.BoundedInertial ρ L H x y) : Follows L (H + ρ) x y := by
  obtain ⟨Δ, h1, h2, h⟩ := h
  exact follows_mono h1 (by linarith) (inertialRD_follows hρ h)

/-- **A `Follows` channel is a `ChanCells` channel** for the outward-rounded
step band. -/
theorem chanCells_of_follows {q : ℝ} {c : ℝ → ℕ} (hc : CellMap q c) (hq : 0 < q)
    {lo hi : ℕ} {Lo Hi : ℝ} (hlo : (lo : ℝ) * q ≤ Lo) (hhi : Hi ≤ (hi : ℝ) * q)
    {x y : ℝ → Bool} (h : Follows Lo Hi x y) : ChanCells c lo hi x y := by
  intro k hk v he t ht
  have hkt := (hc t).2 (by omega)
  have hkt2 := (hc t).1
  rw [ht] at hkt hkt2
  apply h t v
  intro τ h1 h2
  have e1 : ((k : ℝ) - hi) * q = k * q - hi * q := by ring
  have e2 : ((k : ℝ) + 1 - lo) * q = (k + 1) * q - lo * q := by ring
  have w1 : hi ≤ k → ((k : ℝ) - hi) * q ≤ τ := fun _ => by linarith
  have w2 : τ < ((k : ℝ) + 1 - lo) * q := by linarith
  exact he τ (in_window hc hq w1 w2).1 (in_window hc hq w1 w2).2

/-- **Inertial, sharp form**: band `[L, H]` rounded outwards, and the rejection
window no wider than the abstract window `(hi + 1 - lo)` cells. -/
theorem boundedInertial_chanCells {q : ℝ} {c : ℝ → ℕ} (hc : CellMap q c) (hq : 0 < q)
    {lo hi : ℕ} {ρ L H : ℝ} (hlo : (lo : ℝ) * q ≤ L) (hhi : H ≤ (hi : ℝ) * q)
    (hρ : ρ ≤ ((hi : ℝ) + 1 - lo) * q)
    {x y : ℝ → Bool} (h : DelayInertial.BoundedInertial ρ L H x y) : ChanCells c lo hi x y := by
  obtain ⟨Δ, hΔ1, hΔ2, h⟩ := h
  intro k hk v he t ht
  have hkt := (hc t).2 (by omega)
  have hkt2 := (hc t).1
  rw [ht] at hkt hkt2
  obtain ⟨τ, hτ, _, hb, hmax⟩ := h (t - Δ)
  have hb' : y t = x τ := by have := hb; simp only [sub_add_cancel] at this; exact this
  rw [hb']
  -- every instant in `[(k - hi) q, (k + 1 - lo) q)` (or below it, if `k < hi`) is `v`
  have e1 : ((k : ℝ) - hi) * q = k * q - hi * q := by ring
  have e2 : ((k : ℝ) + 1 - lo) * q = (k + 1) * q - lo * q := by ring
  have e3 : ((hi : ℝ) + 1 - lo) * q = hi * q + q - lo * q := by ring
  have hB : t - Δ < ((k : ℝ) + 1 - lo) * q := by linarith
  have hin : ∀ w, (hi ≤ k → ((k : ℝ) - hi) * q ≤ w) → w < ((k : ℝ) + 1 - lo) * q → x w = v :=
    fun w h1 h2 => he w (in_window hc hq h1 h2).1 (in_window hc hq h1 h2).2
  by_cases hik : hi ≤ k
  · by_cases ha : ((k : ℝ) - hi) * q ≤ τ
    · exact hin τ (fun _ => ha) (by linarith)
    · have hA : ((k : ℝ) - hi) * q ≤ t - Δ := by linarith
      have hlt : τ < ((k : ℝ) - hi) * q := lt_of_not_ge ha
      have hAρ : ((k : ℝ) - hi) * q + ρ ≤ ((k : ℝ) + 1 - lo) * q := by linarith
      have hst : DelayInertial.Stable x (((k : ℝ) - hi) * q) ρ := fun w h1 h2 => by
        rw [hin w (fun _ => h1) (by linarith), hin _ (fun _ => le_rfl) (by linarith)]
      rw [← hmax _ hlt hA hst]
      exact hin _ (fun _ => le_rfl) (by linarith)
  · exact hin τ (fun h => absurd h hik) (by linarith)

/-! ## 3. The side condition is necessary: a wide rejection window is not covered -/

/-- **Inertial with a rejection window wider than the abstract window is NOT a
`ChanCells` channel.** The input is `1` exactly on the instants of the window
cells `[1, hi + 1 - lo]` of cell `k = hi + 1`; the inertial channel filters
this pulse (it is shorter than `ρ`) and outputs `0` throughout. -/
theorem inertial_wide_not_chanCells {q ρ : ℝ} (hq : 0 < q) {lo hi : ℕ} (hlo : 1 ≤ lo)
    (hlh : lo ≤ hi) (hρ : ((hi : ℝ) + 1 - lo) * q < ρ) :
    ∃ x y : ℝ → Bool, DelayInertial.BoundedInertial ρ (lo * q) (hi * q) x y ∧
      ¬ ChanCells (fun t => ⌊t / q⌋₊) lo hi x y := by
  have hlh' : (lo : ℝ) ≤ hi := by exact_mod_cast hlh
  have hρ0 : 0 < ρ := by
    have : (0 : ℝ) < ((hi : ℝ) + 1 - lo) * q := mul_pos (by linarith) hq
    linarith
  refine ⟨DelayInertial.pulse false q (((hi : ℝ) + 1 - lo) * q), fun _ => false,
    ⟨lo * q, le_rfl, mul_le_mul_of_nonneg_right hlh' hq.le,
      DelayInertial.filt_pulse_short hρ0 hρ⟩, fun h => ?_⟩
  have hc := cellMap_floor hq
  have hk : ⌊((hi + 1 : ℕ) : ℝ) * q / q⌋₊ = hi + 1 := by
    rw [mul_div_cancel_right₀ _ hq.ne']; exact Nat.floor_natCast _
  have := h (hi + 1) (by omega) true (fun s h1 h2 => ?_) _ hk
  · simp at this
  · -- an instant of a window cell lies in `[q, (hi + 2 - lo) q)`
    simp only at h1 h2
    have hs1 : 1 ≤ ⌊s / q⌋₊ := by omega
    have hA := (hc s).2 hs1
    have hB := (hc s).1
    have h1' : (1 : ℝ) ≤ (⌊s / q⌋₊ : ℝ) := by exact_mod_cast hs1
    have h2' : (⌊s / q⌋₊ : ℝ) ≤ (hi : ℝ) + 1 - lo := by
      have : ⌊s / q⌋₊ + lo ≤ hi + 1 := by omega
      have : ((⌊s / q⌋₊ + lo : ℕ) : ℝ) ≤ ((hi + 1 : ℕ) : ℝ) := by exact_mod_cast this
      push_cast at this; linarith
    have hq1 : q ≤ (⌊s / q⌋₊ : ℝ) * q := by simpa using mul_le_mul_of_nonneg_right h1' hq.le
    have hq2 : ((⌊s / q⌋₊ : ℝ) + 1) * q ≤ ((hi : ℝ) + 1 - lo + 1) * q :=
      mul_le_mul_of_nonneg_right (by linarith) hq.le
    have e4 : ((hi : ℝ) + 1 - lo + 1) * q = q + ((hi : ℝ) + 1 - lo) * q := by ring
    exact DelayInertial.pulse_in (by linarith) (by linarith)

/-! ## 4. Physical gate channels and soundness over `ℝ` -/

/-- **A physical gate channel at cell width `q` with step band `[lo, hi]`**:
transport with a ps band `[L, H]` inside `[lo q, hi q]`, or bounded inertial
with such a band and a rejection window `ρ ≤ (hi + 1 - lo) q`. -/
def PhysChan (q : ℝ) (lo hi : ℕ) (e o : ℝ → Bool) : Prop :=
  (∃ L H, (lo : ℝ) * q ≤ L ∧ H ≤ (hi : ℝ) * q ∧ DelayPure.Chan L H e o) ∨
  (∃ ρ L H, (lo : ℝ) * q ≤ L ∧ H ≤ (hi : ℝ) * q ∧ ρ ≤ ((hi : ℝ) + 1 - lo) * q ∧
    DelayInertial.BoundedInertial ρ L H e o)

theorem physChan_chanCells {q : ℝ} {c : ℝ → ℕ} (hc : CellMap q c) (hq : 0 < q) {lo hi : ℕ}
    {e o : ℝ → Bool} (h : PhysChan q lo hi e o) : ChanCells c lo hi e o := by
  rcases h with ⟨L, H, h1, h2, h⟩ | ⟨ρ, L, H, h1, h2, h3, h⟩
  · exact chanCells_of_follows hc hq h1 h2 (chan_follows h)
  · exact boundedInertial_chanCells hc hq h1 h2 h3 h

/-- `1 ≤ lo` makes every lower delay bound at least one cell, `q > 0`. -/
theorem physChan_lower_pos {q : ℝ} (hq : 0 < q) {lo : ℕ} (hlo : 1 ≤ lo) : 0 < (lo : ℝ) * q :=
  mul_pos (by exact_mod_cast hlo) hq

/-- **Soundness of `XSim` for ℝ-time networks of transport / inertial gates.**
Every gate: zero-delay Boolean LUT function, then a `PhysChan q lo hi`
channel, with `1 ≤ lo`. Inputs covered cell-wise, all-X power-up. Then the
abstract value at the cell of `t` covers the concrete value at `t`, for every
instant `t` and wire `w`. Cycles allowed. -/
theorem sound_real {n : ℕ} (gs : List (LGate n)) (u : Fin n → ℕ → K3) {q : ℝ} (hq : 0 < q)
    (c : ℝ → ℕ) (hc : CellMap q c) (hlo : ∀ g ∈ gs, 1 ≤ g.lo) (x : Fin n → ℝ → Bool)
    (hsat : ∀ g ∈ gs, PhysChan q g.lo g.hi (excT g x) (x g.out))
    (hin : ∀ w, Undriven gs w → ∀ t, u w (c t) ⊑ ofBool (x w t)) :
    ∀ t w, val gs u (fun _ => X) (c t) w ⊑ ofBool (x w t) :=
  sound_cells gs u _ c hlo x (fun g hg => physChan_chanCells hc hq (hsat g hg)) hin
    (h0_X gs x c)

/-! ## 5. End to end: one buffer, a wide inertial window, the simulator is wrong -/

namespace Cex

/-- One routed buffer `0 → 1`, step band `[1, 1]`. -/
def g : LGate 2 :=
  { k := 1, lut := Init.delay_buf, ins := fun _ => 0, out := 1, lo := 1, hi := 1 }

def net : List (LGate 2) := [g]

/-- Abstract input: `1` at step 1 only (cells of width `q = 1`). -/
def u : Fin 2 → ℕ → K3 := fun _ k => ofBool (k == 1)

/-- Concrete input: `1` on `[1, 2)`; output: the inertial filter's `0`. -/
noncomputable def x : Fin 2 → ℝ → Bool := fun w =>
  if w = 0 then DelayInertial.pulse false 1 1 else fun _ => false

theorem val_2 : val net u (fun _ => X) 2 1 = one := by decide

/-- **The simulator prints `1` at cell 2 of the output; the behaviour with an
inertial buffer (delay 1, rejection window `3/2 > 1` cell) is `0` there.**
Every other hypothesis of `sound_real` holds (inputs exactly covered with
`c = ⌊·⌋₊`, `lo = 1`, the buffer's channel has delay band `[1, 1]` = `[lo q, hi q]`). -/
theorem cex_real :
    DelayInertial.BoundedInertial (3 / 2) 1 1 (excT g x) (x g.out) ∧
    (∀ t : ℝ, u 0 ⌊t / 1⌋₊ = ofBool (x 0 t)) ∧
    ¬ (val net u (fun _ => X) ⌊(2 : ℝ) / 1⌋₊ 1 ⊑ ofBool (x 1 2)) := by
  have hexc : excT g x = DelayInertial.pulse false 1 1 := by
    funext t
    show Init.delay_buf.eval (fun _ => DelayInertial.pulse false 1 1 t) = _
    generalize DelayInertial.pulse false 1 1 t = b
    cases b <;> rfl
  have hout : x g.out = fun _ => false := rfl
  refine ⟨?_, fun t => ?_, ?_⟩
  · rw [hexc, hout]
    exact ⟨1, le_rfl, le_rfl, DelayInertial.filt_pulse_short (by norm_num) (by norm_num)⟩
  · show ofBool (⌊t / 1⌋₊ == 1) = ofBool (DelayInertial.pulse false 1 1 t)
    rw [div_one]
    congr 1
    unfold DelayInertial.pulse
    by_cases h : (1 : ℝ) ≤ t ∧ t < 1 + 1
    · have : ⌊t⌋₊ = 1 := by
        rw [Nat.floor_eq_iff (by linarith)]; push_cast; exact ⟨h.1, by linarith [h.2]⟩
      rw [if_pos h, this]; rfl
    · rw [if_neg h]
      have : ⌊t⌋₊ ≠ 1 := by
        intro hf
        rw [Nat.floor_eq_iff' (by norm_num)] at hf
        push_cast at hf; exact h ⟨hf.1, by linarith [hf.2]⟩
      simp [this]
  · have h2 : ⌊(2 : ℝ) / 1⌋₊ = 2 := by
      rw [div_one]; exact_mod_cast Nat.floor_natCast (R := ℝ) 2
    have hx : x 1 2 = false := rfl
    rw [h2, val_2, hx]
    decide

end Cex

end Formal.Core.XSimChanReal
