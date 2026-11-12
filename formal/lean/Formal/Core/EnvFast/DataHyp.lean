import Formal.Core.EnvFast.Data
import Formal.Core.Substrate.Chan

/-!
# Formal.Core.EnvFast.DataHyp — the data exemption of `SoundD` without inertial filtering (X1)

Shard A, contradiction X1 of `formal/out/gcd_hw_hypotheses.md`. Notes:
`formal/notes/A-contradictions.md` §X1.

`EnvFast.Data.SoundD` exempts a DATA element (`DSpec.dout`) from the MIC and
persistence checks on every transition with the output window closed before
and after (`exempt`). A-envfast-2 justified the exemption in prose: "a runt
there has died out before the window opens". That is an inertial assumption,
and A-substrate forbids proofs that rely on filtering (`inertial_not_win`:
no `Win` channel filters). This file replaces the prose by an explicit
hypothesis stated over the substrate's `Win` channel, and proves what it buys.

## The hypotheses

* **H_ZERO_DELAY_FN** (A-substrate): a LUT is a zero-delay Boolean function of
  its pin values (`e`, the EXCITATION) followed by one channel. The channel is
  `Win lo hi e z` (non-FIFO, per-transition delay, no filtering).
* **H_SOUNDD_TRACE** (`InWin`): while the window `[to, tc]` is open the data
  element's excitation equals the value `v` that `SoundD`'s `Q` names (the
  selected input). This is the timed reading of `SoundD`'s in-window
  guarantee (`Q`: "not excited and equal to the selected input",
  `SoundD.lutOK_data_win`). It is a REFINEMENT hypothesis: `Env` has no timed
  semantics, so the step from the state graph to time is not proved here (it
  rests on Env's H_SETTLE and atomic firing; see A-env.md).
* **H_DATA_SETTLES** (`H_DATA_SETTLES`): every transition of the data
  element's excitation that happens while the window is closed has reached
  its final value `v` at least `hi` (the element's slowest delay) before the
  window opens: `e s = v` for `s ∈ [to - hi, to)`. Runts and glitches are
  allowed earlier, and the channel passes them on unfiltered; they end
  before `to`.

## Results

* **`window_data`**: `Win lo hi e z` + `InWin` + `H_DATA_SETTLES` (+ the
  window opening after power-up, `hi ≤ to`) ⇒ the data output is `v` at every
  step of the window. No inertial filtering is used: this is the
  transport/`Win`-level bundled-data property that the substrate asks for
  (the consumer's latch is transparent only inside the window and sees `v`).
* **`settles_needed`**: drop `H_DATA_SETTLES` and the conclusion fails for a
  fixed 1-step channel (a `Win 1 1` behaviour): a runt of the excitation
  ending one step before the window opens is on the output when it opens.
  A one-step runt is exactly what an inertial LUT would swallow and `Win`
  does not.
* **`settles_of_bundle`** (discharge): if every pin of the data element is a
  `Win (loP i) (hiP i)` copy of a driver that holds its final value from the
  launch `tL` (the sender's last data / select move) to the close, the window
  opens at least `R` after that launch (`tL + R ≤ to`, the request path's
  minimum delay through the matched delay), and the **bundling inequality**
  `hiP i + hi ≤ R` holds for every pin, then `H_DATA_SETTLES` holds. That
  inequality is `tighten.py` rule A (data cone max + data element max ≤
  request path min) with the data element's own delay inside the data side.
* **`window_data_of_bundle`**: the two together.
-/

namespace Formal.Core.EnvFast.DataHyp

open Formal.Core.Substrate (Sig Win)

/-- **H_SOUNDD_TRACE**: while the window `[to, tc]` is open, the data
element's excitation is the value `SoundD`'s `Q` names. -/
def InWin (e : Sig) (v : Bool) (to tc : Nat) : Prop := ∀ t, to ≤ t → t ≤ tc → e t = v

/-- **H_DATA_SETTLES**: the excitation's closed-window transitions have
reached the final value `v` at least `hi` steps before the window opens. -/
def H_DATA_SETTLES (hi : Nat) (e : Sig) (v : Bool) (to : Nat) : Prop :=
  ∀ s, to - hi ≤ s → s < to → e s = v

/-- **Data validity through a window channel, without filtering.** -/
theorem window_data {lo hi to tc : Nat} {v : Bool} {e z : Sig} (hz : Win lo hi e z)
    (hpow : hi ≤ to) (hin : InWin e v to tc) (hset : H_DATA_SETTLES hi e v to) :
    ∀ t, to ≤ t → t ≤ tc → z t = v := by
  intro t h1 h2
  obtain ⟨s, a1, a2, hs⟩ := hz t (by omega)
  rw [hs]
  by_cases hlt : s < to
  · exact hset s (by omega) hlt
  · exact hin s (by omega) (by omega)

/-- The counterexample's excitation: `v = true` from step 10 on (the window
opens at 10), with a runt (`false`) at step 9, just before it. -/
def cxE (t : Nat) : Bool := t != 9

/-- The counterexample's output: the excitation one step later (a fixed
1-step channel, a legal `Win 1 1` behaviour). -/
def cxZ (t : Nat) : Bool := cxE (t - 1)

theorem cx_win : Win 1 1 cxE cxZ := by
  intro t ht
  exact ⟨t - 1, by omega, by omega, rfl⟩

/-- **`H_DATA_SETTLES` is needed** (no channel filters): with everything
else of `window_data` in place (window `[10, 20]`), the output shows the
runt at the first step of the window. -/
theorem settles_needed :
    Win 1 1 cxE cxZ ∧ 1 ≤ 10 ∧ InWin cxE true 10 20 ∧ ¬ H_DATA_SETTLES 1 cxE true 10 ∧
      cxZ 10 ≠ true := by
  refine ⟨cx_win, by decide, ?_, ?_, by decide⟩
  · intro t h1 _; unfold cxE; simp; omega
  · intro h; have := h 9 (by decide) (by decide); revert this; decide

/-- **Discharge of `H_DATA_SETTLES` by the bundling inequality.** Pins
`x i` are `Win (loP i) (hiP i)` copies of drivers `d i` that hold their final
values `w i` from the launch `tL` to the close `tc`; the excitation is the
element's function `f` of its pins (H_ZERO_DELAY_FN); the window opens at
least `R` after the launch; and `hiP i + hi ≤ R` (rule A). -/
theorem settles_of_bundle {n : Nat} {f : (Fin n → Bool) → Bool} {x d : Fin n → Sig}
    {w : Fin n → Bool} {loP hiP : Fin n → Nat} {e : Sig} {hi tL R to tc : Nat}
    (he : ∀ t, e t = f (fun i => x i t))
    (hx : ∀ i, Win (loP i) (hiP i) (d i) (x i))
    (hd : ∀ i u, tL ≤ u → u ≤ tc → d i u = w i)
    (hopen : tL + R ≤ to) (hclose : to ≤ tc)
    (hbundle : ∀ i, hiP i + hi ≤ R) :
    H_DATA_SETTLES hi e (f w) to := by
  intro s h1 h2
  rw [he s]
  congr 1
  funext i
  have hb := hbundle i
  obtain ⟨s', a1, a2, hs⟩ := hx i s (by omega)
  rw [hs]
  exact hd i s' (by omega) (by omega)

/-- **The data path, end to end, without filtering**: `SoundD`'s
in-window guarantee (timed reading) + the bundling inequality ⇒ the data
element's output is the selected value throughout the window. -/
theorem window_data_of_bundle {n : Nat} {f : (Fin n → Bool) → Bool} {x d : Fin n → Sig}
    {w : Fin n → Bool} {loP hiP : Fin n → Nat} {e z : Sig} {lo hi tL R to tc : Nat}
    (he : ∀ t, e t = f (fun i => x i t))
    (hx : ∀ i, Win (loP i) (hiP i) (d i) (x i))
    (hd : ∀ i u, tL ≤ u → u ≤ tc → d i u = w i)
    (hopen : tL + R ≤ to) (hclose : to ≤ tc)
    (hbundle : ∀ i, hiP i + hi ≤ R)
    (hz : Win lo hi e z) (hpow : hi ≤ to) (hin : InWin e (f w) to tc) :
    ∀ t, to ≤ t → t ≤ tc → z t = f w :=
  window_data hz hpow hin (settles_of_bundle he hx hd hopen hclose hbundle)

end Formal.Core.EnvFast.DataHyp
