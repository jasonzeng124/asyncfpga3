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
open Formal.Core.TraceDiscrete (Sig delay)

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


/-! ## Inertial channels: covered with a widened band, NOT with their edge delay

Discrete-time (Mathlib-free) instance of the inertial question. The Core
discrete inertial filter `TraceDiscrete.inertial r` (Verilog default inertial:
reject width = delay) copies the input once it has held for the last `r + 1`
samples; `delay d` after it gives a channel whose surviving edges all arrive
exactly `d + r` steps late (`dinertial_passes`).

* `dinertial_chanCells`: the channel `delay d ∘ inertial r` is a `ChanCells id`
  channel with the WIDENED band `[d, d + r]` (lower bound the pure part, upper
  bound edge delay; the rejection window is folded into the abstract window).
  So `sound_cells` covers it with that band.
* `InertialCex`: with the band equal to its edge delay `[d + r, d + r]` it is
  NOT covered: one buffer, a 1-step input pulse, `r = 2`, `d = 1`. The abstract
  simulation prints `1` at step 8 while the inertial behaviour is `0` there
  (`cex_unsound`). The rejection window (`r + 1 = 3` samples) is wider than the
  abstract window (`hi - lo + 1 = 1` step). Inertial filtering does NOT only
  remove transport behaviours: it holds an old value, which no transport
  channel with the same band can.
-/

section DInertial
open Formal.Core.TraceDiscrete (inertial stab stab_iff pulse inertial_filters inertial_passes)

theorem inertial_of_stab {r t : Nat} {e : Sig} (h : stab e r t = true) : inertial r e t = e t := by
  cases t with
  | zero => rfl
  | succ t => simp only [inertial, h, ite_true]

/-- **Inertial is covered with the widened band `[d, d + r]`.** -/
theorem dinertial_chanCells (d r : Nat) (e : Sig) :
    ChanCells id d (d + r) e (delay d (inertial r e)) := by
  intro k _ v he t ht
  simp only [id] at ht
  have hs : ∀ j, j ≤ r → e (t - d - j) = v := fun j hj => he _ (by simp only [id]; omega)
    (by simp only [id]; omega)
  have hst : stab e r (t - d) = true :=
    stab_iff.2 (fun j hj => by rw [hs j hj, ← hs 0 (Nat.zero_le _), Nat.sub_zero])
  show inertial r e (t - d) = v
  rw [inertial_of_stab hst, ← Nat.sub_zero (t - d)]
  exact hs 0 (Nat.zero_le _)

/-- Edges of pulses wider than `r` arrive exactly `d + r` steps late. -/
theorem dinertial_passes {d r p w : Nat} {a : Bool} (hp : 1 ≤ p) (hw : r < w) :
    ∀ t, delay d (inertial r (pulse a p w)) t = pulse a (p + r + d) w t := by
  intro t
  simp only [delay]
  rw [inertial_passes hp hw]
  simp only [pulse]
  repeat' split
  all_goals first | rfl | omega

end DInertial

namespace InertialCex
open Formal.Core.TraceDiscrete (inertial pulse inertial_filters)

/-- One routed buffer `0 → 1` whose band is the inertial edge delay `[3, 3]`. -/
def g : LGate 2 :=
  { k := 1, lut := Init.delay_buf, ins := fun _ => 0, out := 1, lo := 3, hi := 3 }

def net : List (LGate 2) := [g]

/-- The input: `1` at step 5 only. -/
def e : Sig := pulse false 5 1

def u : Fin 2 → Nat → K3 := fun _ t => ofBool (e t)

/-- The inertial behaviour: `d = 1`, `r = 2` (edge delay 3). -/
def x : Fin 2 → Nat → Bool := fun w => if w = 0 then e else delay 1 (inertial 2 e)

theorem excT_g : excT g x = e := by
  funext t
  show Init.delay_buf.eval (fun _ => e t) = e t
  cases h : e t <;> rfl

/-- The output is the inertial channel `delay 1 ∘ inertial 2` of the excitation. -/
theorem x_out : x g.out = delay 1 (inertial 2 (excT g x)) := by
  rw [excT_g]; rfl

/-- The pulse is filtered: the output is `0` at every step. -/
theorem x_out_zero (t : Nat) : x 1 t = false := by
  show delay 1 (inertial 2 e) t = false
  simp only [delay]
  exact inertial_filters (by decide) (by decide) _

/-- The abstract simulation prints `1` at step 8 for the output. -/
theorem val_8 : val net u (fun _ => X) 8 1 = one := by decide

/-- **Not covered.** The behaviour satisfies every other hypothesis of
`sound_cells` (`c = id`, `lo = 3 ≥ 1`, inputs exact, all-X power-up), its
gate is `delay 1 ∘ inertial 2`, which delays every surviving edge by exactly 3
(`dinertial_passes`), yet the abstract value `1` does not cover the concrete
`0`. So `ChanCells id 3 3` fails for it, and soundness fails. -/
theorem cex_unsound : ¬ (val net u (fun _ => X) 8 1 ⊑ ofBool (x 1 8)) := by
  rw [val_8, x_out_zero]; decide

theorem cex_not_chanCells : ¬ ChanCells id g.lo g.hi (excT g x) (x g.out) := by
  intro h
  have := h 8 (by decide) true (fun s h1 h2 => by
    rw [excT_g]; simp only [id, g] at h1 h2
    have : s = 5 := by omega
    subst this; rfl) 8 rfl
  rw [show g.out = 1 from rfl, x_out_zero] at this
  exact Bool.noConfusion this

end InertialCex

end Formal.Core.XSimChan
