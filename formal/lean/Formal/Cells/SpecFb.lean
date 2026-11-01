import Formal.Target.Spec
import Mathlib.Tactic.Ring

/-!
# Formal.Cells.SpecFb — feedback LUTs (C-elements, latches, the arbiter's q) under the frozen Spec

Shard B, THE goal. Stated directly over `Formal.Target.Spec`'s `GateOK` (frozen 2026-11-01).
Notes: `formal/notes/B-specfb.md`.

## Problem, plainly
Every storage node of the target is a LUT whose output is one of its own inputs (a C-element,
a latch, the arbiter's state). THE goal allows a resolution assumption only for arbiters
(H_ARB). What does the Spec's gate relation alone say about such a node: when does it keep
its value, when does it switch cleanly, and can it misbehave?

## Results (for any gate `g`, any delay parameters, any corner)
The caller gives Nat bounds `lo i ≤ d ≤ hi i` implied by `Adm` on pin `i` (`Bands`), and
the index `j` of the feedback pin (`g.ins[j] = g.out`), with `1 ≤ lo j`.
* `fb_stays`: the output is `b` on the feedback window before `s`; on `[s, e]` every
  combination of pin values that the reads can see, with the feedback at `b`, gives `b`
  (the pins CONFIRM `b`). Then the output is `b` on `[s, e]`.
* `fb_forced`: on `[s, e]` every visible combination gives `c` whatever the feedback is
  (the pins FORCE `c`). Then the output is `c` on `[s, e]`.
* `fb_switch`: forced to `c` on `[s, e]` with `e + 1 ≥ s + hi j` (the forcing lasts at least
  the feedback arc's upper bound), then confirmed on `[e + 1, e']`: the output is `c` on
  all of `[s, e']`. A clean switch.
* `fb_runt_oscillates` (necessity): a `bd_c2` C-element (table `0xE8` on pins a, b, q),
  arcs exactly 1, 1 and 3 ps (g = 1, κ = 0, any corner), a = 1 throughout, b high for ONE
  ps: the set condition is forced for 1 ps < 3 ps, and the gate relation admits an output
  that oscillates for ever (high at 11, 14, 17, ...; `c2_osc_forever`), a GateOK behaviour.
  So in the Spec semantics every C-element can be left oscillating by a short forcing
  episode, and no hypothesis of THE goal resolves it (H_ARB is for arbiters only).

## What it means for THE theorem
The proof must derive, for every feedback LUT of the target, that each forcing episode at
the gate's pins lasts at least the feedback arc's upper bound (`fb_switch`'s side
condition), from the bands: an obligation per storage node that the checker must generate
(shard C). Where it cannot be shown, the counterexample is a runt that circulates
(`fb_runt_oscillates` is the cell-level shape).

## Not covered
Which combinations are visible is stated by quantifying over values the reads can see on
each pin's window (a sound over-approximation of the actual reads); the per-node
obligations on the target; inertial channels that would kill the runt (the Spec admits
transport, so it must be excluded by timing, not by physics).
-/

namespace Formal.Cells.SpecFb

open Formal.Target

/-- Nat bounds on every admissible read delay of each pin. -/
def Bands (p : DelayPar) (c : ℚ) (g : Gate) (lo hi : Nat → Nat) : Prop :=
  ∀ i, i < g.k → ∀ d, Adm p c (g.arcs.getD i default) d → lo i ≤ d ∧ d ≤ hi i

/-- `v` is a combination of pin values the reads can see at `t` (feedback pin `j` excluded). -/
def Visible (x : Beh) (g : Gate) (lo hi : Nat → Nat) (j t : Nat) (v : Nat → Bool) : Prop :=
  ∀ i, i < g.k → i ≠ j → ∃ u, u + lo i ≤ t ∧ t ≤ u + hi i ∧ v i = x (g.ins.getD i 0) u

/-- The read vector at `t` is visible. -/
theorem reads_visible {p : DelayPar} {c : ℚ} {g : Gate} {x : Beh} {lo hi : Nat → Nat}
    (hb : Bands p c g lo hi) (f : Nat → Nat → Nat) (t j : Nat)
    (hr : ∀ i, i < g.k → f i t ≤ t ∧ Adm p c (g.arcs.getD i default) (t - f i t)) :
    Visible x g lo hi j t (fun i => x (g.ins.getD i 0) (f i t)) := by
  intro i hi' _
  have h := hr i hi'
  have hd := hb i hi' _ h.2
  exact ⟨f i t, by omega, by omega, rfl⟩

/-- **Confirmed value stays.** -/
theorem fb_stays {p : DelayPar} {c : ℚ} {g : Gate} {x : Beh} (hg : GateOK p c g x)
    {lo hi : Nat → Nat} (hb : Bands p c g lo hi) {j : Nat} (hj : j < g.k)
    (hfb : g.ins.getD j 0 = g.out) (hlo : 1 ≤ lo j) {s e : Nat} (hs : g.start p ≤ s) {b : Bool}
    (hpre : ∀ t, s ≤ t + hi j → t < s → x g.out t = b)
    (hconf : ∀ t, s ≤ t → t ≤ e → ∀ v : Nat → Bool, v j = b → Visible x g lo hi j t v →
      g.init.testBit (addr g.k v) = b) :
    ∀ t, s ≤ t → t ≤ e → x g.out t = b := by
  obtain ⟨f, _, hf⟩ := hg
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro hst hte
    obtain ⟨hr, hy⟩ := hf t (by omega)
    have hj' := hr j hj
    have hd := hb j hj _ hj'.2
    have hfj : x g.out (f j t) = b := by
      by_cases hc : s ≤ f j t
      · exact ih (f j t) (by omega) hc (by omega)
      · exact hpre (f j t) (by omega) (by omega)
    rw [hy]
    apply hconf t hst hte
    · show x (g.ins.getD j 0) (f j t) = b
      rw [hfb]; exact hfj
    · exact reads_visible hb f t j hr

/-- **Forced value.** -/
theorem fb_forced {p : DelayPar} {c : ℚ} {g : Gate} {x : Beh} (hg : GateOK p c g x)
    {lo hi : Nat → Nat} (hb : Bands p c g lo hi) {j : Nat} {s e : Nat} (hs : g.start p ≤ s)
    {cv : Bool}
    (hforce : ∀ t, s ≤ t → t ≤ e → ∀ v : Nat → Bool, Visible x g lo hi j t v →
      g.init.testBit (addr g.k v) = cv) :
    ∀ t, s ≤ t → t ≤ e → x g.out t = cv := by
  obtain ⟨f, _, hf⟩ := hg
  intro t hst hte
  obtain ⟨hr, hy⟩ := hf t (by omega)
  rw [hy]
  exact hforce t hst hte _ (reads_visible hb f t j hr)

/-- **Clean switch**: forced for at least the feedback arc's upper bound, then confirmed. -/
theorem fb_switch {p : DelayPar} {c : ℚ} {g : Gate} {x : Beh} (hg : GateOK p c g x)
    {lo hi : Nat → Nat} (hb : Bands p c g lo hi) {j : Nat} (hj : j < g.k)
    (hfb : g.ins.getD j 0 = g.out) (hlo : 1 ≤ lo j) {s e e' : Nat} (hs : g.start p ≤ s)
    (hlong : s + hi j ≤ e + 1) {cv : Bool}
    (hforce : ∀ t, s ≤ t → t ≤ e → ∀ v : Nat → Bool, Visible x g lo hi j t v →
      g.init.testBit (addr g.k v) = cv)
    (hconf : ∀ t, e + 1 ≤ t → t ≤ e' → ∀ v : Nat → Bool, v j = cv → Visible x g lo hi j t v →
      g.init.testBit (addr g.k v) = cv) :
    ∀ t, s ≤ t → t ≤ e' → x g.out t = cv := by
  have h1 := fb_forced hg hb (j := j) hs hforce
  have h2 := fb_stays hg hb hj hfb hlo (s := e + 1) (e := e') (by omega) (b := cv)
    (fun t h3 h4 => h1 t (by omega) (by omega)) hconf
  intro t hst hte
  by_cases ht : t ≤ e
  · exact h1 t hst ht
  · exact h2 t (by omega) hte

/-! ## Necessity: a forcing episode shorter than the feedback arc can leave a C-element oscillating -/

/-- `bd_c2`'s table on pins a, b, q (rst and the tied pins folded away): majority. -/
def c2Init : Nat := 0xE8

/-- The C-element gate: pins nodes 0 (a), 1 (b), 2 (q, its own output); arcs exactly
1, 1 and 3 ps. -/
def c2Gate : Gate := ⟨"bd_c2", 3, c2Init, [0, 1, 2], [⟨1, 1, 1, 1⟩, ⟨1, 1, 1, 1⟩, ⟨3, 3, 3, 3⟩], 2⟩

def pex : DelayPar := ⟨1, 0⟩

/-- a = 1 always; b = 1 only at t = 10; q high at 11, 14, 17, ... for ever. -/
def oscBeh : Beh := fun n t =>
  if n = 0 then true else if n = 1 then decide (t = 10) else decide (11 ≤ t ∧ t % 3 = 2)

theorem c2_start : c2Gate.start pex = 3 := by
  simp [Gate.start, c2Gate, pex]; rfl

theorem adm_exact (c : ℚ) (n d : Nat) : Adm pex c ⟨n, n, n, n⟩ d ↔ d = n := by
  have e : ∀ m : ℚ, (1 - (0:ℚ)) * ((1 - c) * m + c * m) / 1 = m := fun m => by ring
  have e' : ∀ m : ℚ, (1 + (0:ℚ)) * ((1 - c) * m + c * m) * 1 = m := fun m => by ring
  simp only [Adm, pex, lerp, e, e']
  constructor
  · rintro ⟨h1, h2⟩
    exact_mod_cast le_antisymm h2 h1
  · rintro rfl
    exact ⟨le_refl _, le_refl _⟩

/-- The oscillating trace is a behaviour of the C-element gate at every corner. -/
theorem c2_osc_gateOK (c : ℚ) : GateOK pex c c2Gate oscBeh := by
  refine ⟨fun i t => if i = 2 then t - 3 else t - 1, ?_, ?_⟩
  · intro i _ a b hab
    show (if i = 2 then a - 3 else a - 1) ≤ (if i = 2 then b - 3 else b - 1)
    split <;> omega
  · intro t ht
    rw [c2_start] at ht
    refine ⟨fun i hi => ?_, ?_⟩
    · have hk : c2Gate.k = 3 := rfl
      rw [hk] at hi
      rcases i with _ | _ | _ | i
      · refine ⟨by simp, ?_⟩
        rw [show c2Gate.arcs.getD 0 default = ⟨1, 1, 1, 1⟩ from rfl, adm_exact]; simp; omega
      · refine ⟨by simp, ?_⟩
        rw [show c2Gate.arcs.getD 1 default = ⟨1, 1, 1, 1⟩ from rfl, adm_exact]; simp; omega
      · refine ⟨by simp, ?_⟩
        rw [show c2Gate.arcs.getD 2 default = ⟨3, 3, 3, 3⟩ from rfl, adm_exact]; simp; omega
      · omega
    · show oscBeh 2 t = c2Init.testBit (addr 3 fun i =>
          oscBeh ([0, 1, 2].getD i 0) (if i = 2 then t - 3 else t - 1))
      by_cases h : t < 30
      · have key : ∀ t, t < 30 → 3 ≤ t → oscBeh 2 t = c2Init.testBit (addr 3 fun i =>
            oscBeh ([0, 1, 2].getD i 0) (if i = 2 then t - 3 else t - 1)) := by decide
        exact key t h ht
      · simp only [oscBeh, addr, c2Init]
        have e1 : t - 1 ≠ 10 := by omega
        have e3 : (t - 3) % 3 = t % 3 := by omega
        by_cases h3 : t % 3 = 2 <;>
          simp [e1, e3, h3, show 11 ≤ t by omega, show 11 ≤ t - 3 by omega] <;> decide

/-- **It oscillates for ever**: high at every `t ≥ 11` with `t % 3 = 2`, low in between,
although `a` stays 1 and `b`'s only pulse ended at 11. -/
theorem c2_osc_forever : ∀ n, oscBeh 2 (11 + 3 * n) = true ∧ oscBeh 2 (12 + 3 * n) = false ∧
    oscBeh 0 (11 + 3 * n) = true ∧ oscBeh 1 (11 + 3 * n) = false := by
  intro n
  simp only [oscBeh]
  refine ⟨by simp, by simp, by simp, by simp; omega⟩

/-- **Necessity of `fb_switch`'s side condition.** The set condition (a = b = 1) is forced
for ONE ps (`t = 11` reads b at 10), shorter than the feedback arc (3 ps), and the C-element
gate admits a behaviour that never settles. -/
theorem fb_runt_oscillates :
    (∀ c : ℚ, GateOK pex c c2Gate oscBeh) ∧
    (∀ t, oscBeh 1 t = true ↔ t = 10) ∧ (∀ t, oscBeh 0 t = true) ∧
    (∀ T, ∃ t, T ≤ t ∧ oscBeh 2 t = true ∧ oscBeh 2 (t + 1) = false) := by
  refine ⟨c2_osc_gateOK, fun t => by simp [oscBeh], fun t => by simp [oscBeh], fun T => ?_⟩
  refine ⟨11 + 3 * T, by omega, (c2_osc_forever T).1, ?_⟩
  have := (c2_osc_forever T).2.1
  rwa [show 12 + 3 * T = 11 + 3 * T + 1 by omega] at this

end Formal.Cells.SpecFb
