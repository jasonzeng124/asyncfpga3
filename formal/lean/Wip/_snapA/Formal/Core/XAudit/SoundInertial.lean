import Formal.Core.XAudit.Parse
import Formal.Core.XAudit.SoundSteps
import Formal.Core.XAudit.SoundPhys

/-!
# Formal.Core.XAudit.SoundInertial — xaudit's `--inertial` verdicts are sound

Probe XInert (shard A). See `formal/notes/A-xinert.md`.

`xaudit --inertial widen|check` gives each gate a rejection window `ρ` (ps) and
simulates the design `Parse.widenD u m ps`, in which gate `g` with window `ρ`
has `hi := Parse.widenHi u g.lo g.hi ρ = max hi (lo + ⌈ρ/u⌉ - 1)` (`lo`,
INIT, pins, output unchanged). `check` refuses to run unless no gate is widened.

Proved here:

* `widenHi_window`: `ρ ≤ (widenHi u lo hi ρ + 1 - lo) · u`, so the widened band
  meets the side condition of `XSimChanReal.boundedInertial_chanCells`;
  `widenHi_ge`: `hi ≤ widenHi …`;
* `physChan_widen`: a gate whose physical channel is transport, or bounded
  inertial with some window `ρ' ≤ ρ`, with a ps band `[L, H]` inside the
  ORIGINAL step band (`lo u ≤ L`, `H ≤ hi u`; `GateOK`), is a
  `XSimChanReal.PhysChan u lo (widenHi u lo hi ρ)` channel;
* `satPhys_widenD`: every gate `GateOK` ⇒ `SoundPhys.SatPhys (widenD u m ps) u x`;
  and so the executable's verdicts on the widened design hold in continuous
  time: `valF_sound_inertial`, `noXF_sound_inertial`, `constF_sound_inertial`,
  `settledF_inertial` (instances of `SoundPhys`);
* `gateOK_of_toSteps`: the parser's rounding gives `GateOK` from a ps band
  `[L, H]` with `u ≤ L` (not a "raised" arc); `gateOK_verilog`: a Verilog-style
  inertial gate (`DelayInertial.Inertial Δ`, reject limit = its delay
  `Δ ∈ [L, H]`) is `GateOK` with `ρ = H` (the executable's `"delay"` window);
* `widenHi_eq_of_window` / `widened_wide`: a gate is widened iff
  `(hi + 1 - lo) · u < ρ` — exactly the case in which
  `XSimChanReal.inertial_wide_not_chanCells` shows the unwidened band is NOT
  sound; so `check`'s refusals are necessary, and a `check` run that is not
  refused simulates the unchanged design (`widenD_eq_of_window`);
* `widenD_zero`: with every `ρ = 0` the widened design IS the parsed design.

Assumed: `GateOK` per gate (a measurement/model hypothesis: which channel the
gate is, its band and its window), the hypotheses of `SoundPhys` (inputs
covered cell-wise; `Design.WF` of the simulated design, which the executable
checks). The parser and `Parse.applyInertial` (which reconstructs each gate's
ps band and window from the band file) are TRUSTED code; `applyInertial`
re-rounds each reconstructed band and refuses on any mismatch with the parsed
step band. NOT covered: pads (always transport, band in steps), "raised" arcs
(`L < u`), involution channels, analog effects.
-/

namespace Formal.Core.XAudit.SoundInertial

open Formal.Core K3
open Formal.Core.XSim
open Formal.Core.XSimChan
open Formal.Core.XSimChanReal
open Formal.Core.XAudit
open Formal.Core.XAudit.Fast
open Formal.Core.XAudit.SoundCells
open Formal.Core.XAudit.SoundPhys
open Formal.Core.XAudit.Parse

/-! ## 0. Inverted bands are rejected (`Parse.checkedSteps`, used by `Parse.bandFor`) -/

/-- An accepted band is not inverted, and is rounded by `toSteps`. -/
theorem checkedSteps_ok {u : ℕ} {b : ℕ × ℕ} {r : ℕ × ℕ × Bool}
    (h : checkedSteps u b = .ok r) : b.1 ≤ b.2 ∧ r = toSteps u b := by
  unfold checkedSteps at h
  by_cases hb : b.2 < b.1
  · rw [if_pos hb] at h; cases h
  · rw [if_neg hb] at h; cases h; exact ⟨Nat.le_of_not_lt hb, rfl⟩

/-- An inverted band (`lo > hi`) is rejected. -/
theorem checkedSteps_inverted {u : ℕ} {b : ℕ × ℕ} (h : b.2 < b.1) :
    ∃ e, checkedSteps u b = .error e := by
  unfold checkedSteps; rw [if_pos h]; exact ⟨_, rfl⟩

/-- For a non-inverted band the step `hi` is `⌈H/u⌉` (at least 1): the `max` with
`lo` in `toSteps` never narrows it. -/
theorem toSteps_hi_ceil {u L H : ℕ} (hu : 0 < u) (hLH : L ≤ H) :
    (toSteps u (L, H)).2.1 = max 1 ((H + u - 1) / u) := by
  rw [SoundSteps.toSteps_snd]
  have : L / u ≤ (H + u - 1) / u := Nat.div_le_div_right (by omega)
  generalize L / u = a at this ⊢
  generalize (H + u - 1) / u = c at this ⊢
  omega

/-- An accepted band with `u ≤ L` (not raised): its ps band lies inside the step
band, `lo·u ≤ L ≤ H ≤ hi·u`, and `1 ≤ lo ≤ hi`. -/
theorem checkedSteps_inside {u : ℕ} (hu : 0 < u) {L H : ℕ} {r : ℕ × ℕ × Bool}
    (h : checkedSteps u (L, H) = .ok r) (hL : u ≤ L) :
    r.1 * u ≤ L ∧ L ≤ H ∧ H ≤ r.2.1 * u ∧ 1 ≤ r.1 ∧ r.1 ≤ r.2.1 := by
  obtain ⟨hLH, rfl⟩ := checkedSteps_ok h
  exact ⟨SoundSteps.toSteps_lo_le hu hL, hLH, SoundSteps.toSteps_hi_ge hu,
    SoundSteps.toSteps_lo_pos u L H, SoundSteps.toSteps_lo_le_hi u L H⟩

/-! ## 1. The widening, in ℕ -/

theorem widenHi_ge (u lo hi ρ : ℕ) : hi ≤ widenHi u lo hi ρ := Nat.le_max_left _ _

theorem widenHi_lo (u lo hi ρ : ℕ) : lo ≤ widenHi u lo hi ρ + 1 := by
  have h : lo + (ρ + u - 1) / u - 1 ≤ widenHi u lo hi ρ := Nat.le_max_right _ _
  generalize (ρ + u - 1) / u = c at h
  generalize widenHi u lo hi ρ = w at h ⊢
  omega

theorem widenHi_window {u : ℕ} (hu : 0 < u) (lo hi ρ : ℕ) :
    ρ ≤ (widenHi u lo hi ρ + 1 - lo) * u := by
  have h1 := SoundSteps.ceil_mul_ge (H := ρ) hu
  have h2 : lo + (ρ + u - 1) / u - 1 ≤ widenHi u lo hi ρ := Nat.le_max_right _ _
  have h3 : (ρ + u - 1) / u ≤ widenHi u lo hi ρ + 1 - lo := by omega
  exact Nat.le_trans h1 (Nat.mul_le_mul_right _ h3)

/-- A gate whose window already fits is not widened. -/
theorem widenHi_eq_of_window {u lo hi ρ : ℕ} (hu : 0 < u) (hlh : lo ≤ hi)
    (h : ρ ≤ (hi + 1 - lo) * u) : widenHi u lo hi ρ = hi := by
  have hc : (ρ + u - 1) / u < hi + 1 - lo + 1 := by
    rw [Nat.div_lt_iff_lt_mul hu]
    rw [Nat.add_mul, Nat.one_mul]
    omega
  unfold widenHi
  omega

/-- A window of at most one step never widens a well-formed gate. -/
theorem widenHi_eq_of_le_unit {u lo hi ρ : ℕ} (hu : 0 < u) (hlh : lo ≤ hi) (h : ρ ≤ u) :
    widenHi u lo hi ρ = hi :=
  widenHi_eq_of_window hu hlh (Nat.le_trans h (by
    have : 1 ≤ hi + 1 - lo := by omega
    simpa using Nat.mul_le_mul_right u this))

/-- A widened gate has a window wider than its abstract window: the case of
`XSimChanReal.inertial_wide_not_chanCells`. -/
theorem widened_wide {u lo hi ρ : ℕ} (hu : 0 < u) (hlh : lo ≤ hi)
    (h : widenHi u lo hi ρ ≠ hi) : (hi + 1 - lo) * u < ρ := by
  rcases Nat.lt_or_ge ((hi + 1 - lo) * u) ρ with h' | h'
  · exact h'
  · exact absurd (widenHi_eq_of_window hu hlh h') h

theorem widenHi_zero {u : ℕ} (hu : 0 < u) {lo hi : ℕ} (hlh : lo ≤ hi + 1) :
    widenHi u lo hi 0 = hi := by
  have : (0 + u - 1) / u = 0 := (Nat.div_eq_zero_iff_lt hu).2 (by omega)
  unfold widenHi; rw [this]; omega

theorem widenGate_eq {u : ℕ} {g : GSpec} {ρ : ℕ} (h : widenHi u g.lo g.hi ρ = g.hi) :
    widenGate u g ρ = g := by
  unfold widenGate; rw [h]

/-- With every window `0`, the simulated design is the parsed design. -/
theorem widenD_zero {u : ℕ} (hu : 0 < u) (m : ℕ) (ps : List (GSpec × ℕ))
    (h : ∀ p ∈ ps, p.2 = 0 ∧ p.1.lo ≤ p.1.hi) :
    widenD u m ps = { m := m, gates := ps.map Prod.fst } := by
  unfold widenD
  congr 1
  apply List.map_congr_left
  intro p hp
  obtain ⟨h0, hlh⟩ := h p hp
  rw [h0]
  exact widenGate_eq (widenHi_zero hu (by omega))

/-- `check` mode: if no gate needs widening, the simulated design is the parsed one. -/
theorem widenD_eq_of_window {u : ℕ} (hu : 0 < u) (m : ℕ) (ps : List (GSpec × ℕ))
    (h : ∀ p ∈ ps, p.1.lo ≤ p.1.hi ∧ p.2 ≤ (p.1.hi + 1 - p.1.lo) * u) :
    widenD u m ps = { m := m, gates := ps.map Prod.fst } := by
  unfold widenD
  congr 1
  apply List.map_congr_left
  intro p hp
  obtain ⟨hlh, hw⟩ := h p hp
  exact widenGate_eq (widenHi_eq_of_window hu hlh hw)

/-! ## 2. The widening, in ℝ -/

theorem widenHi_window_real {u : ℕ} (hu : 0 < u) (lo hi ρ : ℕ) :
    (ρ : ℝ) ≤ ((widenHi u lo hi ρ : ℝ) + 1 - lo) * u := by
  have h := widenHi_window hu lo hi ρ
  have hle := widenHi_lo u lo hi ρ
  have e : (((widenHi u lo hi ρ + 1 - lo) * u : ℕ) : ℝ) = ((widenHi u lo hi ρ : ℝ) + 1 - lo) * u := by
    rw [Nat.cast_mul, Nat.cast_sub hle]; push_cast; ring
  rw [← e]; exact_mod_cast h

/-- **The physical gate hypothesis, in ps** (cell width `q`; for xaudit `q = unit_ps`):
a ps band `[L, H]` inside the gate's parsed step band, and a channel that is
transport in that band, or bounded inertial in that band with a rejection window
`ρ' ≤ ρ`. -/
def GateOK (q : ℝ) (lo hi : ℕ) (ρ : ℝ) (e o : ℝ → Bool) : Prop :=
  ∃ L H : ℝ, (lo : ℝ) * q ≤ L ∧ H ≤ (hi : ℝ) * q ∧
    (DelayPure.Chan L H e o ∨ ∃ ρ', ρ' ≤ ρ ∧ DelayInertial.BoundedInertial ρ' L H e o)

theorem physChan_widen {u lo hi ρ : ℕ} (hu : 0 < u) {e o : ℝ → Bool}
    (h : GateOK u lo hi ρ e o) : PhysChan u lo (widenHi u lo hi ρ) e o := by
  obtain ⟨L, H, h1, h2, h⟩ := h
  have hu' : (0 : ℝ) ≤ u := by exact_mod_cast Nat.zero_le u
  have hH : H ≤ (widenHi u lo hi ρ : ℝ) * u :=
    le_trans h2 (mul_le_mul_of_nonneg_right (by exact_mod_cast widenHi_ge u lo hi ρ) hu')
  rcases h with h | ⟨ρ', hρ', h⟩
  · exact Or.inl ⟨L, H, h1, hH, h⟩
  · exact Or.inr ⟨ρ', L, H, h1, hH, le_trans hρ' (widenHi_window_real hu lo hi ρ), h⟩

/-- The parser's rounding (`toSteps`, not raised: `u ≤ L`) gives `GateOK`. -/
theorem gateOK_of_toSteps {u L H : ℕ} (hu : 0 < u) (hL : u ≤ L) {ρ : ℝ} {e o : ℝ → Bool}
    (h : DelayPure.Chan L H e o ∨ ∃ ρ', ρ' ≤ ρ ∧ DelayInertial.BoundedInertial ρ' L H e o) :
    GateOK u (toSteps u (L, H)).1 (toSteps u (L, H)).2.1 ρ e o :=
  ⟨L, H, by exact_mod_cast SoundSteps.toSteps_lo_le (H := H) hu hL,
    by exact_mod_cast SoundSteps.toSteps_hi_ge (L := L) (H := H) hu, h⟩

/-- A Verilog-default inertial gate (reject limit = its delay `Δ ∈ [L, H]`) is
`GateOK` with window `H` (the executable's `"delay"`). -/
theorem gateOK_verilog {q : ℝ} {lo hi : ℕ} {L H Δ : ℝ} (h1 : (lo : ℝ) * q ≤ L)
    (h2 : H ≤ (hi : ℝ) * q) (hL : L ≤ Δ) (hH : Δ ≤ H) {e o : ℝ → Bool}
    (h : DelayInertial.Inertial Δ e o) : GateOK q lo hi H e o :=
  ⟨L, H, h1, h2, Or.inr ⟨Δ, hH, Δ, hL, hH, h⟩⟩

/-! ## 3. The design the executable simulates -/

/-- **Every gate `GateOK` (with the ORIGINAL step band and its window) ⇒ the
widened design satisfies `SatPhys`.** -/
theorem satPhys_widenD {u : ℕ} (hu : 0 < u) (m : ℕ) (ps : List (GSpec × ℕ))
    (x : Fin (widenD u m ps).n → ℝ → Bool)
    (h : ∀ p ∈ ps, GateOK u p.1.lo p.1.hi p.2 (excT (p.1.toLGate (widenD u m ps)) x)
      (x ((widenD u m ps).wire p.1.out))) :
    SatPhys (widenD u m ps) u x := by
  intro g hg
  simp only [widenD, List.mem_map] at hg
  obtain ⟨p, hp, rfl⟩ := hg
  exact physChan_widen hu (h p hp)

/-- Hypothesis bundle: every parsed gate is `GateOK` with its window. -/
def AllOK (u m : ℕ) (ps : List (GSpec × ℕ)) (x : Fin (widenD u m ps).n → ℝ → Bool) : Prop :=
  ∀ p ∈ ps, GateOK u p.1.lo p.1.hi p.2 (excT (p.1.toLGate (widenD u m ps)) x)
    (x ((widenD u m ps).wire p.1.out))

theorem valF_sound_inertial {u : ℕ} (hu : 0 < u) (m : ℕ) (ps : List (GSpec × ℕ))
    (hwf : (widenD u m ps).WF) (s : Fin (widenD u m ps).n → ℕ → K3) (T : ℕ)
    (x : Fin (widenD u m ps).n → ℝ → Bool) (hok : AllOK u m ps x)
    (hin : InputsCoveredT (widenD u m ps) s (fun t => ⌊t / (u : ℝ)⌋₊) x)
    (t : ℝ) (ht : ⌊t / (u : ℝ)⌋₊ ≤ T) (w : Fin (widenD u m ps).n) :
    valF (auditF (widenD u m ps) s T) ⌊t / (u : ℝ)⌋₊ w.val ⊑ ofBool (x w t) :=
  valF_sound_phys _ hwf s T (by exact_mod_cast hu) _ (cellMap_floor (by exact_mod_cast hu)) x
    (satPhys_widenD hu m ps x hok) hin t ht w

/-- **"No X at `w` on steps `[t1, t2]`" under `--inertial`**: at every instant of
those cells, every behaviour with transport / inertial gates as in `AllOK` has the
printed value. -/
theorem noXF_sound_inertial {u : ℕ} (hu : 0 < u) (m : ℕ) (ps : List (GSpec × ℕ))
    (hwf : (widenD u m ps).WF) (s : Fin (widenD u m ps).n → ℕ → K3) (T : ℕ)
    (w : Fin (widenD u m ps).n) (t1 t2 : ℕ) (ht2 : t2 ≤ T)
    (h : noXF (auditF (widenD u m ps) s T) w.val t1 t2 = true)
    (x : Fin (widenD u m ps).n → ℝ → Bool) (hok : AllOK u m ps x)
    (hin : InputsCoveredT (widenD u m ps) s (fun t => ⌊t / (u : ℝ)⌋₊) x) :
    ∀ t : ℝ, t1 ≤ ⌊t / (u : ℝ)⌋₊ → ⌊t / (u : ℝ)⌋₊ ≤ t2 →
      x w t = pick (valF (auditF (widenD u m ps) s T) ⌊t / (u : ℝ)⌋₊ w.val) :=
  noXF_sound_phys _ hwf s T w t1 t2 ht2 h (by exact_mod_cast hu) _
    (cellMap_floor (by exact_mod_cast hu)) x (satPhys_widenD hu m ps x hok) hin

theorem constF_sound_inertial {u : ℕ} (hu : 0 < u) (m : ℕ) (ps : List (GSpec × ℕ))
    (hwf : (widenD u m ps).WF) (s : Fin (widenD u m ps).n → ℕ → K3) (T : ℕ)
    (w : Fin (widenD u m ps).n) (t1 t2 : ℕ) (ht2 : t2 ≤ T) (v : Bool)
    (h : allEqF (auditF (widenD u m ps) s T) w.val t1 t2 v = true)
    (x : Fin (widenD u m ps).n → ℝ → Bool) (hok : AllOK u m ps x)
    (hin : InputsCoveredT (widenD u m ps) s (fun t => ⌊t / (u : ℝ)⌋₊) x) :
    ∀ t : ℝ, t1 ≤ ⌊t / (u : ℝ)⌋₊ → ⌊t / (u : ℝ)⌋₊ ≤ t2 → x w t = v :=
  constF_sound_phys _ hwf s T w t1 t2 ht2 v h (by exact_mod_cast hu) _
    (cellMap_floor (by exact_mod_cast hu)) x (satPhys_widenD hu m ps x hok) hin

/-- **Fixed point under `--inertial`**: every binary value of row `T` holds at
every instant `t ≥ T u`. -/
theorem settledF_inertial {u : ℕ} (hu : 0 < u) (m : ℕ) (ps : List (GSpec × ℕ))
    (hwf : (widenD u m ps).WF) (s : Fin (widenD u m ps).n → ℕ → K3) (T : ℕ) (hT : 1 ≤ T)
    (hs : ∀ w, Undriven (build (widenD u m ps)) w → ∀ t, T ≤ t → s w t = s w T)
    (hfix : rowsFixedF (auditF (widenD u m ps) s T) T (widenD u m ps).maxHi = true)
    (x : Fin (widenD u m ps).n → ℝ → Bool) (hok : AllOK u m ps x)
    (hin : InputsCoveredT (widenD u m ps) s (fun t => ⌊t / (u : ℝ)⌋₊) x)
    (w : Fin (widenD u m ps).n) (v : Bool)
    (hv : valF (auditF (widenD u m ps) s T) T w.val = ofBool v) :
    ∀ t : ℝ, (T : ℝ) * u ≤ t → x w t = v :=
  settledF_phys _ hwf s T hT hs hfix (by exact_mod_cast hu) x (satPhys_widenD hu m ps x hok)
    hin w v hv

end Formal.Core.XAudit.SoundInertial
