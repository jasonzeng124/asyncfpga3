import Formal.Cells.Bundling

/-!
# Probe P3c: the exact per-stage FASTFALL flush and `bd_delay_gated`
(cell_constraints entries `bd_delay[FASTFALL].flush_per_stage`,
`bd_delay_gated.gate`)

`Bundling.slow_not_early` proves the FASTFALL line's rising edge cannot reach
`z` early under the UNIFORM hypothesis H_FLUSH `2*hi + thi ≤ (T - F) + tlo`
(one window for every hop, one for every tap). B-bundling.md states the exact
requirement per stage: the fall of stage `i` must reach stage `i+1`'s chain
pin before the tap's rise re-enables stage `i+1`:

    fall_i (latest, at stage i's OUTPUT) + hop_hi(i -> i+1) ≤ T + tap_lo(i+1).

This file proves that per-stage form sufficient, with PER-STAGE windows (every
routed hop and tap its own `[lo, hi]`), for a tap net that is either the line's
own input (`bd_delay #(.FASTFALL(1))`, `tap = s 0`) or a separate `gate` net
(`bd_delay_gated`, `tap = gate`). Same gate model as Bundling (window
channels, Kleene closure of the REAL INITs `2'h2` and `4'h8`).

* `FastLineP`: the per-stage structure (any side INIT with Bundling's three
  absorption/pass properties); `fastfall_lineP` instantiates `4'h8`.
* `fallBound`: the latest fall time of each stage OUTPUT, computed from the
  windows (`fallBound 1 = Fa + hi 0`, `fallBound (i+1) = min (Ft + thi i)
  (fallBound i + hi i)`: the tap or the chain, whichever is sooner).
* `slow_not_early_ps`: under **H_FLUSH_STAGE i** `fallBound i + hi i ≤ Tt +
  tlo i` for each side stage, every stage `i` holds the fast value on
  `[fallBound i, Ta + Lo i - 1]` (`Lo i` = sum of the min hops), so `z`
  cannot rise before `Ta + Lo N`.
* `slow_arrives_ps`: the rise arrives (per-stage windows).
* `fast_edge_ps`: the fall flushes in one tap hop.
* `flush_stage_of_uniform`: Bundling's uniform H_FLUSH implies every
  H_FLUSH_STAGE (so this theorem strictly generalises `slow_not_early`), and
  `flush_stage_strictly_weaker`: a numeric case where every per-stage
  condition holds and H_FLUSH fails.
* `ruleF_counter_violates_stage`: Bundling's `ff_counter_ruleF` (rule F's
  premise holds, the rise skips) violates H_FLUSH_STAGE 1: the per-stage form
  is the one that separates it.
* `bd_delay_gated`: `gated_line` instantiates the same structure with the
  taps on `gate`; `gated_not_early` / `gated_fast_edge` are the timed forms of
  `LibEndMemMlink.gated_gate_low` (Kleene only before).

Exactness: the per-stage condition is SUFFICIENT for every behaviour of the
window model; its necessity is shown on a witness (rule F's counter-trace),
not in general.
-/

namespace Formal.Cells.ConstraintsFastFall
open Formal.Cells
open Formal.Cells.Bundling

section P
variable (s : Nat → Sig) (tap : Sig) (N : Nat) (lo hi tlo thi : Nat → Nat) (init : Nat) (c : Bool)

/-- **A FAST line with per-stage windows.** `s 0` is the chain input `a`;
stage 0 is `LUT1 2'h2` reading `s 0` through `[lo 0, hi 0]`; stage `i ∈ [1, N)`
is a LUT2 (I0 = `s i` through `[lo i, hi i]`, the routed hop `i -> i+1` plus
the I0 arc; I1 = `tap` through `[tlo i, thi i]`, the tap's route to stage `i`
plus the I1 arc). H_HOP_BOUNDS per hop: per-hop SDF/prjxray min/max at one
corner; testable per hop by GLS or a ring oscillator built from the same
placement. -/
structure FastLineP : Prop where
  hlh : ∀ i, lo i ≤ hi i
  htlh : ∀ i, tlo i ≤ thi i
  g0 : Gate BUF [(s 0, lo 0, hi 0)] (s 1)
  gi : ∀ i, 1 ≤ i → i < N → Gate init [(s i, lo i, hi i), (tap, tlo i, thi i)] (s (i + 1))
  absorbTap : AbsorbTap init c
  absorbChain : AbsorbChain init c
  pass : Pass init c

/-- Sum of the minimum chain hops before stage `i`: the matched delay to
stage `i`. -/
def Lo : Nat → Nat
  | 0 => 0
  | i + 1 => Lo i + lo i

/-- Sum of the maximum chain hops before stage `i`. -/
def Hi : Nat → Nat
  | 0 => 0
  | i + 1 => Hi i + hi i

/-- Latest time stage `i`'s OUTPUT can still be away from the fast value,
given `a` at the fast value from `Fa` and the tap from `Ft`. -/
def fallBound (Fa Ft : Nat) : Nat → Nat
  | 0 => Fa
  | 1 => Fa + hi 0
  | i + 2 => min (Ft + thi (i + 1)) (fallBound Fa Ft (i + 1) + hi (i + 1))

end P

section Thm
variable {s : Nat → Sig} {tap : Sig} {N : Nat} {lo hi tlo thi : Nat → Nat} {init : Nat} {c : Bool}

/-- **Per-stage FASTFALL flush (sufficient).** `a = s 0` at the fast value
`c` on `[Fa, Ta - 1]`, the tap net at `c` on `[Ft, Tt - 1]`. If for every
side stage `i ∈ [1, N)`
  **H_FLUSH_STAGE i**: `fallBound i + hi i ≤ Tt + tlo i`
(the latest fall at stage `i`'s output plus the slowest hop into stage `i+1`
is no later than the earliest re-enabling by the tap), then every stage
`1 ≤ i ≤ N` holds `c` on `[fallBound i, Ta + Lo i - 1]`: the slow edge
cannot reach stage `i` before the matched `Ta + Lo i`. -/
theorem slow_not_early_ps (L : FastLineP s tap N lo hi tlo thi init c)
    (Fa Ta Ft Tt : Nat) (ha : StableOn (s 0) c Fa (Ta - 1)) (ht : StableOn tap c Ft (Tt - 1))
    (H_FLUSH_STAGE : ∀ i, 1 ≤ i → i < N → fallBound hi thi Fa Ft i + hi i ≤ Tt + tlo i) :
    ∀ i, 1 ≤ i → i ≤ N → StableOn (s i) c (fallBound hi thi Fa Ft i) (Ta + Lo lo i - 1) := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
    intro _ hiN t h1 h2
    by_cases hi0 : i = 0
    · subst hi0
      have hl := L.hlh 0
      simp only [fallBound, Lo] at h1 h2
      exact gate_buf L.g0 (win_of_stable hl ha (by omega) (by omega))
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hF := H_FLUSH_STAGE (j + 1) (by omega) (by omega)
      have hl := L.hlh (j + 1); have htl := L.htlh (j + 1)
      have hfb : fallBound hi thi Fa Ft (j + 2) =
          min (Ft + thi (j + 1)) (fallBound hi thi Fa Ft (j + 1) + hi (j + 1)) := rfl
      have hLo : Lo lo (j + 2) = Lo lo (j + 1) + lo (j + 1) := rfl
      rw [hfb] at h1; rw [hLo] at h2
      by_cases hc : fallBound hi thi Fa Ft (j + 1) + hi (j + 1) ≤ t
      · -- the chain pin reads stage j+1, which is at c over the whole window
        exact gate_side_chain (L.gi (j + 1) (by omega) (by omega)) L.absorbChain
          (win_of_stable hl (ih (by omega) (by omega)) hc (by omega))
      · -- before the chain has flushed: the tap holds the stage at c
        exact gate_side_tap (L.gi (j + 1) (by omega) (by omega)) L.absorbTap
          (win_of_stable htl ht (by omega) (by omega))

/-- **Slow edge arrives (per-stage windows).** `a` at `!c` on `[Ta, Ta']`, the
tap at `!c` on `[Tt, Tt']`: stage `i ≥ 1` holds `!c` from
`max (Ta + Hi i) (Tt + max thi)`-style bound `riseBound`, until
`min (Ta' + lo 0) (Tt' + min tlo)`-style bound. Stated with the bounds as
hypotheses-free recursions. -/
def riseBound (hi thi : Nat → Nat) (Ta Tt : Nat) : Nat → Nat
  | 0 => Ta
  | 1 => Ta + hi 0
  | i + 2 => max (riseBound hi thi Ta Tt (i + 1) + hi (i + 1)) (Tt + thi (i + 1))

def holdBound (lo tlo : Nat → Nat) (Ta' Tt' : Nat) : Nat → Nat
  | 0 => Ta'
  | 1 => Ta' + lo 0
  | i + 2 => min (holdBound lo tlo Ta' Tt' (i + 1) + lo (i + 1)) (Tt' + tlo (i + 1))

theorem slow_arrives_ps (L : FastLineP s tap N lo hi tlo thi init c)
    (Ta Ta' Tt Tt' : Nat) (ha : StableOn (s 0) (!c) Ta Ta') (ht : StableOn tap (!c) Tt Tt') :
    ∀ i, 1 ≤ i → i ≤ N →
      StableOn (s i) (!c) (riseBound hi thi Ta Tt i) (holdBound lo tlo Ta' Tt' i) := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
    intro _ hiN t h1 h2
    by_cases hi0 : i = 0
    · subst hi0
      have hl := L.hlh 0
      simp only [riseBound, holdBound] at h1 h2
      exact gate_buf L.g0 (win_of_stable hl ha (by omega) (by omega))
    · obtain ⟨j, rfl⟩ : ∃ j, i = j + 1 := ⟨i - 1, by omega⟩
      have hl := L.hlh (j + 1); have htl := L.htlh (j + 1)
      have e1 : riseBound hi thi Ta Tt (j + 2) =
          max (riseBound hi thi Ta Tt (j + 1) + hi (j + 1)) (Tt + thi (j + 1)) := rfl
      have e2 : holdBound lo tlo Ta' Tt' (j + 2) =
          min (holdBound lo tlo Ta' Tt' (j + 1) + lo (j + 1)) (Tt' + tlo (j + 1)) := rfl
      rw [e1] at h1; rw [e2] at h2
      exact gate_side_pass (L.gi (j + 1) (by omega) (by omega)) L.pass
        (win_of_stable hl (ih (by omega) (by omega)) (by omega) (by omega))
        (win_of_stable htl ht (by omega) (by omega))

/-- **Fast edge**: the tap at `c` on `[F, F']` puts `z = s N` at `c` on
`[F + thi (N-1), F' + tlo (N-1)]`: one tap hop, whatever the chain does. -/
theorem fast_edge_ps (L : FastLineP s tap N lo hi tlo thi init c) (hN : 2 ≤ N)
    (F F' : Nat) (ht : StableOn tap c F F') :
    StableOn (s N) c (F + thi (N - 1)) (F' + tlo (N - 1)) := by
  intro t h1 h2
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have htl := L.htlh M
  simp only [Nat.add_sub_cancel] at h1 h2
  exact gate_side_tap (L.gi M (by omega) (by omega)) L.absorbTap
    (win_of_stable htl ht (by omega) (by omega))

end Thm

/-! ## Instances: `bd_delay #(.FASTFALL(1))` and `bd_delay_gated` -/

/-- `bd_delay #(.FASTFALL(1))`: the real `4'h8` side stage, taps on `s 0`. -/
theorem fastfall_lineP (s : Nat → Sig) (N : Nat) (lo hi tlo thi : Nat → Nat)
    (hlh : ∀ i, lo i ≤ hi i) (htlh : ∀ i, tlo i ≤ thi i)
    (g0 : Gate BUF [(s 0, lo 0, hi 0)] (s 1))
    (gi : ∀ i, 1 ≤ i → i < N → Gate FF_SIDE [(s i, lo i, hi i), (s 0, tlo i, thi i)] (s (i + 1))) :
    FastLineP s (s 0) N lo hi tlo thi FF_SIDE false :=
  ⟨hlh, htlh, g0, gi, ff_absorbTap, ff_absorbChain, ff_pass⟩

/-- `bd_delay_gated`: the same LUTs (`2'h2` head, `4'h8` sides), taps on
`gate` (cells/rtl/bd_latch.v). -/
theorem gated_line (s : Nat → Sig) (gate : Sig) (N : Nat) (lo hi tlo thi : Nat → Nat)
    (hlh : ∀ i, lo i ≤ hi i) (htlh : ∀ i, tlo i ≤ thi i)
    (g0 : Gate BUF [(s 0, lo 0, hi 0)] (s 1))
    (gi : ∀ i, 1 ≤ i → i < N → Gate FF_SIDE [(s i, lo i, hi i), (gate, tlo i, thi i)] (s (i + 1))) :
    FastLineP s gate N lo hi tlo thi FF_SIDE false :=
  ⟨hlh, htlh, g0, gi, ff_absorbTap, ff_absorbChain, ff_pass⟩

/-- **`bd_delay_gated`, timed.** `gate` low on `[Fg, Tg - 1]`, `a = s 0` (the
buffered copy of `gate`, header contract **H_A_FOLLOWS_GATE**: `a` falls
after `gate` falls and rises after it rises) low on `[Fa, Ta - 1]`, and
H_FLUSH_STAGE with the gate's rise `Tg`: no stage rises before the matched
`Ta + Lo i`; `z` falls one gate-tap hop after `gate` (`gated_fast_edge`). -/
theorem gated_not_early (s : Nat → Sig) (gate : Sig) (N : Nat) (lo hi tlo thi : Nat → Nat)
    (L : FastLineP s gate N lo hi tlo thi FF_SIDE false)
    (Fa Ta Fg Tg : Nat) (ha : StableOn (s 0) false Fa (Ta - 1)) (hg : StableOn gate false Fg (Tg - 1))
    (H_FLUSH_STAGE : ∀ i, 1 ≤ i → i < N → fallBound hi thi Fa Fg i + hi i ≤ Tg + tlo i) :
    ∀ i, 1 ≤ i → i ≤ N → StableOn (s i) false (fallBound hi thi Fa Fg i) (Ta + Lo lo i - 1) :=
  slow_not_early_ps L Fa Ta Fg Tg ha hg H_FLUSH_STAGE

theorem gated_fast_edge (s : Nat → Sig) (gate : Sig) (N : Nat) (lo hi tlo thi : Nat → Nat)
    (L : FastLineP s gate N lo hi tlo thi FF_SIDE false) (hN : 2 ≤ N)
    (F F' : Nat) (hg : StableOn gate false F F') :
    StableOn (s N) false (F + thi (N - 1)) (F' + tlo (N - 1)) :=
  fast_edge_ps L hN F F' hg

/-- **The gate dip, timed** (the header's warning): `gate` low on `[F, F']`
while `a` stays HIGH puts `z` low on `[F + thi, F' + tlo]` (a request glitch
on a line that was high), for any `N ≥ 2`. Timed form of
`LibEndMemMlink.gated_dip_flushes`. -/
theorem gated_dip_glitch (s : Nat → Sig) (gate : Sig) (N : Nat) (lo hi tlo thi : Nat → Nat)
    (L : FastLineP s gate N lo hi tlo thi FF_SIDE false) (hN : 2 ≤ N)
    (F F' : Nat) (hg : StableOn gate false F F') (_ha : StableOn (s 0) true 0 F') :
    StableOn (s N) false (F + thi (N - 1)) (F' + tlo (N - 1)) :=
  fast_edge_ps L hN F F' hg

/-! ## Relation to the uniform H_FLUSH -/

theorem fallBound_le_uniform (hi thi : Nat) (Fa : Nat) :
    ∀ i, 1 ≤ i → fallBound (fun _ => hi) (fun _ => thi) Fa Fa i ≤ Fa + max hi thi := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
    intro _
    cases i with
    | zero => simp only [fallBound]; omega
    | succ j =>
      have : fallBound (fun _ => hi) (fun _ => thi) Fa Fa (j + 2) =
          min (Fa + thi) (fallBound (fun _ => hi) (fun _ => thi) Fa Fa (j + 1) + hi) := rfl
      rw [this]; omega

/-- **Uniform H_FLUSH implies every H_FLUSH_STAGE** (`bd_delay`, taps on
`s 0`, `Ft = Fa = F`, `Tt = Ta = T`): so `slow_not_early_ps` contains
`Bundling.slow_not_early`. -/
theorem flush_stage_of_uniform (hi tlo thi F T : Nat) (hFT : F < T)
    (H_FLUSH : 2 * hi + thi ≤ (T - F) + tlo) :
    ∀ i, 1 ≤ i → fallBound (fun _ => hi) (fun _ => thi) F F i + hi ≤ T + tlo := by
  intro i hi1
  have := fallBound_le_uniform hi thi F i hi1
  have : max hi thi ≤ hi + thi := by omega
  omega

/-- **Strictly weaker.** Chain `[1, 3]`, taps `[1, 1]`, low phase `[0, 4]`
(`F = 0`, `T = 5`), `N = 3`: H_FLUSH (`2*3 + 1 ≤ 5 + 1`) fails, every
H_FLUSH_STAGE holds (stage 1: `3 + 3 ≤ 6`; stage 2: `min 1 6 + 3 ≤ 6`). -/
theorem flush_stage_strictly_weaker :
    ¬ (2 * 3 + 1 ≤ (5 - 0) + 1) ∧
    (∀ i, 1 ≤ i → i < 3 → fallBound (fun _ => 3) (fun _ => 1) 0 0 i + 3 ≤ 5 + 1) := by
  refine ⟨by decide, ?_⟩
  intro i h1 h2
  have : i = 1 ∨ i = 2 := by omega
  rcases this with rfl | rfl <;> decide

/-- **Rule F's counter-trace violates H_FLUSH_STAGE 1.** In
`Bundling.ff_counter_ruleF` (chain `[1, 3]`, taps `[1, 1]`, `a` low on
`[10, 11]`, rise at 12) every stage output is low at 11 and 12 (rule F's
premise) and the rise still skips the chain; the per-stage condition fails at
stage 1: `fallBound 1 + hi = 13 + 3 > 12 + 1`. -/
theorem ruleF_counter_violates_stage :
    FastLine fgS 3 1 3 1 1 FF_SIDE false ∧ fgS 3 13 = true ∧ 13 < 12 + 3 * 1 ∧
    ¬ (fallBound (fun _ => 3) (fun _ => 1) 10 10 1 + 3 ≤ 12 + 1) :=
  ⟨ff_counter_ruleF.1, ff_counter_ruleF.2.2.2.2.1, by decide, by decide⟩

/-- A uniform `FastLine` is a `FastLineP` with constant windows. -/
theorem fastLineP_of_uniform {s : Nat → Sig} {N lo hi tlo thi init : Nat} {c : Bool}
    (L : FastLine s N lo hi tlo thi init c) :
    FastLineP s (s 0) N (fun _ => lo) (fun _ => hi) (fun _ => tlo) (fun _ => thi) init c :=
  ⟨fun _ => L.hlh, fun _ => L.htlh, L.g0, L.gi, L.absorbTap, L.absorbChain, L.pass⟩

end Formal.Cells.ConstraintsFastFall
