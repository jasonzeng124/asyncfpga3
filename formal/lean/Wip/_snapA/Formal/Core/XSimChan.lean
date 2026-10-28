import Formal.Core.XSim

/-!
# Formal.Core.XSimChan — `XSim` is sound in ANY time domain, cell by cell

Probe XSound2 (shard A). See `formal/notes/A-xsound2.md`.

`XSim.sound` is proved for discrete behaviours (`ℕ → Bool`) whose gates are
window channels (`WinCh`). The physical channels of `Core/Delay`
(`DelayPure.Chan`, `DelayInertial.InertialRD`/`BoundedInertial`) live on `ℝ`.
`TernaryChannels.sample_not_causal` shows that *sampling* an `ℝ` behaviour on a
grid is the wrong bridge (a runt between two grid points is lost). The right
statement is a **cell** reading of the abstract rows: abstract step `k` covers
EVERY instant of time cell `k`, not one sample.

This file is time-domain agnostic and Mathlib-free:

* the time domain is any type `τ`, with a cell map `c : τ → ℕ` (for `ℝ` and a
  step `q`: `c t = ⌊t/q⌋₊`, so cell 0 is `(-∞, q)` and cell `k ≥ 1` is
  `[k q, (k+1) q)`; see `XSimChanReal`);
* a gate is the zero-delay Boolean LUT function (`excT`, = `Lut.eval` of the pin
  values at the same instant) followed by a channel satisfying `ChanCells`:
  "if the excitation is constantly `v` on every instant of the cells
  `[k - hi, k - lo]`, the output is `v` on every instant of cell `k`" (`k ≥ 1`).

Results.

* `sound_cells`: if every gate has `1 ≤ lo` and satisfies `ChanCells`, the
  abstract inputs cover the concrete inputs cell-wise, and `a0` covers the
  driven wires on cell 0, then `val gs u a0 (c t) w ⊑ ofBool (x w t)` for every
  instant `t` and wire `w`. Cycles allowed (induction on the cell index).
* `binary_cells`: a binary abstract value at step `k` is the concrete value at
  every instant of cell `k`, in every behaviour.
* `chanCells_of_winCh`: for `τ = ℕ`, `c = id`, `WinCh` implies `ChanCells`, so
  `sound_cells` contains `XSim.sound`.
-/

namespace Formal.Core.XSimChan

open Formal.Core K3
open Formal.Core.XSim

section Gen
variable {τ : Type} {n : Nat}

/-- Zero-delay Boolean LUT function of the pin values, in any time domain. -/
def excT (g : LGate n) (x : Fin n → τ → Bool) : τ → Bool :=
  fun t => g.lut.eval (fun i => x (g.ins i) t)

/-- **Step-level channel property.** For every cell `k ≥ 1` and value `v`: if
the input `e` is `v` at every instant whose cell lies in `[k - hi, k - lo]`
(natural subtraction, so the window is truncated at cell 0, which holds all
the time before the first full step), then the output `o` is `v` at every
instant of cell `k`. -/
def ChanCells (c : τ → Nat) (lo hi : Nat) (e o : τ → Bool) : Prop :=
  ∀ k, 1 ≤ k → ∀ v : Bool,
    (∀ s, k - hi ≤ c s → c s ≤ k - lo → e s = v) → ∀ t, c t = k → o t = v

variable (gs : List (LGate n)) (u : Fin n → Nat → K3) (a0 : Fin n → K3)

/-- **Soundness, cell by cell, in any time domain.** -/
theorem sound_cells (c : τ → Nat) (hlo : ∀ g ∈ gs, 1 ≤ g.lo) (x : Fin n → τ → Bool)
    (hsat : ∀ g ∈ gs, ChanCells c g.lo g.hi (excT g x) (x g.out))
    (hin : ∀ w, Undriven gs w → ∀ t, u w (c t) ⊑ ofBool (x w t))
    (h0 : ∀ g ∈ gs, ∀ t, c t = 0 → a0 g.out ⊑ ofBool (x g.out t)) :
    ∀ t w, val gs u a0 (c t) w ⊑ ofBool (x w t) := by
  suffices H : ∀ K t, c t ≤ K → ∀ w, val gs u a0 (c t) w ⊑ ofBool (x w t) from
    fun t w => H (c t) t (Nat.le_refl _) w
  intro K
  induction K with
  | zero =>
      intro t ht w
      have hc0 : c t = 0 := by omega
      rw [hc0, val_zero]
      cases hd : driver gs w with
      | none => have := hin w (driver_none hd) t; rw [hc0] at this; exact this
      | some g =>
          obtain ⟨hg, rfl⟩ := driver_some hd
          exact h0 g hg t hc0
  | succ k ih =>
      intro t ht w
      by_cases hkt : c t ≤ k
      · exact ih t hkt w
      have hck : c t = k + 1 := by omega
      have hin' := hin
      rw [hck, val_succ]
      unfold cell
      cases hd : driver gs w with
      | none => have := hin' w (driver_none hd) t; rw [hck] at this; exact this
      | some g =>
          obtain ⟨hg, rfl⟩ := driver_some hd
          simp only
          have hlo1 := hlo g hg
          generalize hW : win g.lo g.hi (fun s => g.lut.keval
            (fun i => ((hist gs u a0 k).getD (k - s) []).getD (g.ins i).val X)) (k + 1) = W
          by_cases hWX : W = X
          · rw [hWX]; exact X_le _
          obtain ⟨v, rfl⟩ := ne_X_iff.mp hWX
          suffices hx : x g.out t = v by rw [hx]; exact le_refl _
          refine hsat g hg (k + 1) (by omega) v (fun s h1 h2 => ?_) t hck
          -- the window value is `v`, so every cell of the window has excitation `v`
          have hle := win_le (g := fun s => g.lut.keval
            (fun i => ((hist gs u a0 k).getD (k - s) []).getD (g.ins i).val X)) h1 h2
          rw [hW] at hle
          have hs : c s ≤ k := by omega
          rw [hist_getD gs u a0 k (c s) hs] at hle
          have hcov : g.lut.keval (fun i => (arow gs u a0 (c s)).getD (g.ins i).val X) ⊑
              ofBool (excT g x s) := by
            simp only [excT]
            rw [← Lut.keval_ofBoolVec]
            exact Lut.keval_mono _ (fun i => ih s hs (g.ins i))
          exact defined_eq hcov (ofBool_le_iff.mp hle)

/-- A binary abstract value at the cell of `t` is the concrete value at `t`. -/
theorem binary_cells (c : τ → Nat) (hlo : ∀ g ∈ gs, 1 ≤ g.lo) (x : Fin n → τ → Bool)
    (hsat : ∀ g ∈ gs, ChanCells c g.lo g.hi (excT g x) (x g.out))
    (hin : ∀ w, Undriven gs w → ∀ t, u w (c t) ⊑ ofBool (x w t))
    (h0 : ∀ g ∈ gs, ∀ t, c t = 0 → a0 g.out ⊑ ofBool (x g.out t))
    (t : τ) (w : Fin n) (v : Bool) (hv : val gs u a0 (c t) w = ofBool v) : x w t = v :=
  defined_eq (sound_cells gs u a0 c hlo x hsat hin h0 t w) hv

/-- Every abstract value covers the concrete one: from an all-`X` power-up
row the `h0` hypothesis is free. -/
theorem h0_X (x : Fin n → τ → Bool) (c : τ → Nat) :
    ∀ g ∈ gs, ∀ t, c t = 0 → (fun _ : Fin n => X) g.out ⊑ ofBool (x g.out t) :=
  fun _ _ _ _ => X_le _

end Gen

/-! ## The discrete case: `WinCh` is a `ChanCells` channel for `c = id` -/

theorem chanCells_of_winCh {lo hi : Nat} {e o : Nat → Bool} (h : WinCh lo hi e o) :
    ChanCells id lo hi e o := by
  intro k _ v he t ht
  obtain ⟨s, h1, h2, hs⟩ := h t
  subst ht
  rw [hs]; exact he s h1 h2

theorem excT_eq_exc {n : Nat} (g : LGate n) (x : Fin n → Nat → Bool) : excT g x = g.exc x := rfl

/-- `XSim.sound` again, as the instance `τ = ℕ`, `c = id` of `sound_cells`. -/
theorem sound_of_cells {n : Nat} (gs : List (LGate n)) (u : Fin n → Nat → K3) (a0 : Fin n → K3)
    (hlo : ∀ g ∈ gs, 1 ≤ g.lo) (x : Fin n → Nat → Bool) (hsat : ∀ g ∈ gs, g.relW x)
    (hin : ∀ w, Undriven gs w → ∀ t, u w t ⊑ ofBool (x w t))
    (h0 : ∀ g ∈ gs, a0 g.out ⊑ ofBool (x g.out 0)) :
    ∀ t w, val gs u a0 t w ⊑ ofBool (x w t) :=
  sound_cells gs u a0 id hlo x (fun g hg => chanCells_of_winCh (hsat g hg)) hin
    (fun g hg t ht => by simp only [id] at ht; subst ht; exact h0 g hg)

end Formal.Core.XSimChan
