import Formal.Net.TimedBridge
import Mathlib.Algebra.Order.Floor.Semifield

/-!
# Formal.Cells.CornerSlice — one integer timed net for a whole interval of corners (shard B, 2026-11-10)

**Problem, plainly.** THE statement lets every behaviour pick its own process corner `c ∈ [0,1]`; the timed
occurrence-net model (`TimedOccX`, C's AO certificates) needs integer per-pin bounds `lo`/`hi`, and C's bridge
(`TimedBridge.GateFact`) asks `N.lo ≤ sumLoC p c` and `sumHiC p c ≤ N.hi` at the behaviour's own corner. The
certificate builders so far made one certificate at `c = 0` and one at `c = 1`; nothing covered the corners in
between. Can ONE integer net serve every corner of an interval `[c1, c2]`?

**Proved (for every sane `p`: 0 ≤ κ ≤ 1, 0 < g; and arcs ordered fmin ≤ smin, fmax ≤ smax, which Spec's `WF`
gives for every arc of the circuit):**
* `lerp_mono`, `loC_mono`, `hiC_mono`, `sumLoC_mono`, `sumHiC_mono`: the corner-`c` integer bounds of an arc,
  and their sums along a route, are non-decreasing in `c`.
* `gateFact_of_slice`: a gate whose net bounds are `lo ≤ sumLoC p c1` and `sumHiC p c2 ≤ hi` (the SLICE net)
  satisfies C's `GateFact` at every corner `c ∈ [c1, c2]` for which its `CGateOK` fact holds.
* `reads_of_slice`: hence (C's `reads_of_cgate`) the read hypotheses of `TBehX` hold, on the slice net, for
  every behaviour whose corner lies in the slice.
* `slice_cover`: a finite list of slice points `0 = s₀ ≤ s₁ ≤ … ≤ s_K = 1` covers `[0,1]`: every corner lies in
  some `[s_i, s_{i+1}]`.

So a per-pair certificate need only be checked (with integers, by `decide`) on K slice nets to cover every
corner. **Not shown here:** any instance; whether a certificate passes on a slice net (measured in
`formal/tools-B/slice/`, untrusted); the other `TBehX` fields (quiet start, environment, `lo ≥ 1`).
-/

namespace Formal.Cells.CornerSlice
open Formal.Target Formal.Timing.SpecSettle Formal.Timing.SpecChain Formal.Net.OccNet
  Formal.Net.OccNet.Timed Formal.Net.OccNet.Bridge

/-- An arc is corner-ordered: the slow corner is no faster than the fast one. -/
def ArcOrd (e : Arc) : Prop := e.fmin ≤ e.smin ∧ e.fmax ≤ e.smax

instance (e : Arc) : Decidable (ArcOrd e) := by unfold ArcOrd; infer_instance

theorem lerp_mono {a b : Nat} (hab : a ≤ b) {c1 c2 : ℚ} (hc : c1 ≤ c2) : lerp a b c1 ≤ lerp a b c2 := by
  unfold lerp
  have hab' : (a : ℚ) ≤ b := by exact_mod_cast hab
  have := mul_nonneg (sub_nonneg.2 hc) (sub_nonneg.2 hab')
  nlinarith

theorem loC_mono {p : DelayPar} (hp : Sane p) {e : Arc} (he : ArcOrd e) {c1 c2 : ℚ} (hc : c1 ≤ c2) :
    loC p c1 e ≤ loC p c2 e := by
  unfold loC
  obtain ⟨_, hk1, hg⟩ := hp
  have hl := lerp_mono he.1 hc
  have h1 : (1 - p.κ) * lerp e.fmin e.smin c1 / p.g ≤ (1 - p.κ) * lerp e.fmin e.smin c2 / p.g := by
    rw [div_eq_mul_inv, div_eq_mul_inv]
    apply mul_le_mul_of_nonneg_right _ (inv_nonneg.2 hg.le)
    exact mul_le_mul_of_nonneg_left hl (by linarith)
  exact Int.toNat_le_toNat (Int.ceil_le_ceil h1)

theorem hiC_mono {p : DelayPar} (hp : Sane p) {e : Arc} (he : ArcOrd e) {c1 c2 : ℚ} (hc : c1 ≤ c2) :
    hiC p c1 e ≤ hiC p c2 e := by
  unfold hiC
  obtain ⟨hk0, _, hg⟩ := hp
  have hl := lerp_mono he.2 hc
  have h1 : (1 + p.κ) * lerp e.fmax e.smax c1 * p.g ≤ (1 + p.κ) * lerp e.fmax e.smax c2 * p.g := by
    apply mul_le_mul_of_nonneg_right _ hg.le
    exact mul_le_mul_of_nonneg_left hl (by linarith)
  exact Int.toNat_le_toNat (Int.floor_le_floor h1)

theorem sumLoC_mono {p : DelayPar} (hp : Sane p) {c1 c2 : ℚ} (hc : c1 ≤ c2) :
    ∀ es : List Arc, (∀ e ∈ es, ArcOrd e) → sumLoC p c1 es ≤ sumLoC p c2 es
  | [], _ => by simp [sumLoC]
  | e :: es, h => by
    have h1 := loC_mono hp (h e (List.mem_cons_self ..)) hc
    have h2 := sumLoC_mono hp hc es (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    simp only [sumLoC, List.map_cons, List.sum_cons] at h2 ⊢
    omega

theorem sumHiC_mono {p : DelayPar} (hp : Sane p) {c1 c2 : ℚ} (hc : c1 ≤ c2) :
    ∀ es : List Arc, (∀ e ∈ es, ArcOrd e) → sumHiC p c1 es ≤ sumHiC p c2 es
  | [], _ => by simp [sumHiC]
  | e :: es, h => by
    have h1 := hiC_mono hp (h e (List.mem_cons_self ..)) hc
    have h2 := sumHiC_mono hp hc es (fun e' he' => h e' (List.mem_cons_of_mem _ he'))
    simp only [sumHiC, List.map_cons, List.sum_cons] at h2 ⊢
    omega

/-- What a slice net must satisfy at one gate, independent of the behaviour: the gate's pins, function and
corner-ordered routes, with the net's bounds taken at the slice ends `c1` (lower) and `c2` (upper). -/
structure SliceGate (p : DelayPar) (c1 c2 : ℚ) (N : TNet Nat) (v : Nat) (g : Gate) (src : Nat → Nat)
    (arcs : Nat → List Arc) : Prop where
  pins : N.pins v = (List.range g.k).map src
  nodup : (N.pins v).Nodup
  out : g.out = v
  fn : ∀ l, N.F v l = g.init.testBit (addr g.k fun i => l.getD i false)
  ord : ∀ i, i < g.k → ∀ e ∈ arcs i, ArcOrd e
  lo : ∀ i, i < g.k → N.lo v (src i) ≤ sumLoC p c1 (arcs i)
  hi : ∀ i, i < g.k → sumHiC p c2 (arcs i) ≤ N.hi v (src i)

/-- **One slice net serves every corner of its slice.** -/
theorem gateFact_of_slice {p : DelayPar} (hp : Sane p) {c1 c2 c : ℚ} (h1 : c1 ≤ c) (h2 : c ≤ c2)
    {N : TNet Nat} {x : Beh} {t0 v : Nat} {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc} {S : Nat}
    (hs : SliceGate p c1 c2 N v g src arcs) (hc : CGateOK p c g src arcs S x) (hS : S ≤ t0 + 1) :
    GateFact p c N x t0 v :=
  ⟨⟨g, src, arcs, S, hc, hS, hs.pins, hs.nodup, hs.out, hs.fn, fun i hi =>
    ⟨le_trans (hs.lo i hi) (sumLoC_mono hp h1 _ (hs.ord i hi)),
     le_trans (sumHiC_mono hp h2 _ (hs.ord i hi)) (hs.hi i hi)⟩⟩⟩

/-- **The read hypotheses of `TBehX` on a slice net**, for every behaviour whose corner lies in the slice: each
gate of the net comes with its slice facts (behaviour-independent) and its `CGateOK` fact at the behaviour's
corner (for THE target: `CViewPS.collapsed`). -/
theorem reads_of_slice {p : DelayPar} (hp : Sane p) {c1 c2 c : ℚ} (h1 : c1 ≤ c) (h2 : c ≤ c2)
    {N : TNet Nat} {x : Beh} {t0 H : Nat}
    (hF : ∀ v, N.gate v = true → ∃ (g : Gate) (src : Nat → Nat) (arcs : Nat → List Arc) (S : Nat),
      SliceGate p c1 c2 N v g src arcs ∧ CGateOK p c g src arcs S x ∧ S ≤ t0 + 1)
    (hH : ∀ v w, N.gate v = true → w ∈ N.pins v → N.hi v w ≤ H) :
    ∃ r : Nat → Nat → Nat → Nat,
      (∀ v w t, N.gate v = true → w ∈ N.pins v → t0 < t →
        N.lo v w ≤ t - r v w t ∧ t - r v w t ≤ N.hi v w ∧ r v w t ≤ t ∧ t0 ≤ r v w t + H) ∧
      (∀ v w t t', N.gate v = true → w ∈ N.pins v → t0 < t → t ≤ t' → r v w t ≤ r v w t') ∧
      (∀ v t, N.gate v = true → t0 < t → x v t = N.F v ((N.pins v).map fun w => x w (r v w t))) :=
  reads_of_cgate (fun v hv => by
    obtain ⟨g, src, arcs, S, hs, hc, hS⟩ := hF v hv
    exact gateFact_of_slice hp h1 h2 hs hc hS) hH

/-- **Finitely many slices cover every corner.** For slice points `a, b, s…` (consecutive pairs are the
slices), every `c` from the first point to the last lies in some consecutive pair. With first point 0 and last 1,
every corner of a behaviour is covered. -/
theorem slice_cover : ∀ (s : List ℚ) (a b c : ℚ), a ≤ c → c ≤ (b :: s).getLast (List.cons_ne_nil _ _) →
    ∃ i, ∃ lo hi, (a :: b :: s)[i]? = some lo ∧ (a :: b :: s)[i + 1]? = some hi ∧ lo ≤ c ∧ c ≤ hi
  | [], a, b, c, h1, h2 => ⟨0, a, b, rfl, rfl, h1, by simpa using h2⟩
  | d :: s, a, b, c, h1, h2 => by
    by_cases hb : c ≤ b
    · exact ⟨0, a, b, rfl, rfl, h1, hb⟩
    · have hlast : (b :: d :: s).getLast (List.cons_ne_nil _ _) = (d :: s).getLast (List.cons_ne_nil _ _) :=
        List.getLast_cons _
      obtain ⟨i, lo, hi, e1, e2, l1, l2⟩ :=
        slice_cover s b d c (le_of_lt (not_le.1 hb)) (by rw [← hlast]; exact h2)
      exact ⟨i + 1, lo, hi, by simpa using e1, by simpa using e2, l1, l2⟩

/-! ## Nat forms of the corner bounds (so that slice facts are checked by `decide` without ℚ)
For `p = ⟨gn/gd, kn/kd⟩` and `c = cn/cd`, the bound `loC` is a ceiling and `hiC` a floor of a Nat fraction. -/

theorem ceil_nat_div (A B : Nat) (hB : 0 < B) : ⌈((A : ℚ) / B)⌉₊ = (A + B - 1) / B := by
  have hBq : (0 : ℚ) < B := by exact_mod_cast hB
  apply le_antisymm
  · apply Nat.ceil_le.2
    rw [div_le_iff₀ hBq]
    have h1 : A ≤ (A + B - 1) / B * B := by
      have h := Nat.div_add_mod (A + B - 1) B
      have h2 := Nat.mod_lt (A + B - 1) hB
      have h3 : B * ((A + B - 1) / B) = (A + B - 1) / B * B := Nat.mul_comm _ _
      omega
    exact_mod_cast h1
  · have hk := Nat.le_ceil ((A : ℚ) / B)
    rw [div_le_iff₀ hBq] at hk
    have hk' : A ≤ ⌈((A : ℚ) / B)⌉₊ * B := by exact_mod_cast hk
    apply (Nat.div_le_iff_le_mul_add_pred hB).2
    have h3 : B * ⌈((A : ℚ) / B)⌉₊ = ⌈((A : ℚ) / B)⌉₊ * B := Nat.mul_comm _ _
    omega

/-- Lower corner bound as a Nat ceiling. -/
def loN (kn kd gn gd cn cd : Nat) (e : Arc) : Nat :=
  ((kd - kn) * ((cd - cn) * e.fmin + cn * e.smin) * gd + kd * cd * gn - 1) / (kd * cd * gn)

/-- Upper corner bound as a Nat floor. -/
def hiN (kn kd gn gd cn cd : Nat) (e : Arc) : Nat :=
  ((kd + kn) * ((cd - cn) * e.fmax + cn * e.smax) * gn) / (kd * cd * gd)

theorem loC_eq_loN {kn kd gn gd cn cd : Nat} (hk : kn ≤ kd) (hc : cn ≤ cd) (hkd : 0 < kd) (hgn : 0 < gn)
    (hgd : 0 < gd) (hcd : 0 < cd) (e : Arc) :
    loC ⟨(gn : ℚ) / gd, (kn : ℚ) / kd⟩ ((cn : ℚ) / cd) e = loN kn kd gn gd cn cd e := by
  unfold loC loN
  rw [Int.ceil_toNat, ← ceil_nat_div _ _ (by positivity)]
  congr 1
  unfold lerp
  push_cast [Nat.cast_sub hk, Nat.cast_sub hc]
  have : (kd : ℚ) ≠ 0 := by positivity
  have : (cd : ℚ) ≠ 0 := by positivity
  have : (gn : ℚ) ≠ 0 := by positivity
  have : (gd : ℚ) ≠ 0 := by positivity
  field_simp
  try ring

theorem hiC_eq_hiN {kn kd gn gd cn cd : Nat} (hc : cn ≤ cd) (hkd : 0 < kd)
    (hgd : 0 < gd) (hcd : 0 < cd) (e : Arc) :
    hiC ⟨(gn : ℚ) / gd, (kn : ℚ) / kd⟩ ((cn : ℚ) / cd) e = hiN kn kd gn gd cn cd e := by
  unfold hiC hiN
  rw [Int.floor_toNat, ← Nat.floor_div_eq_div (K := ℚ)]
  congr 1
  dsimp only
  unfold lerp
  push_cast [Nat.cast_sub hc]
  have : (kd : ℚ) ≠ 0 := by positivity
  have : (cd : ℚ) ≠ 0 := by positivity
  have : (gd : ℚ) ≠ 0 := by positivity
  field_simp
  try ring

theorem sumLoC_eq {kn kd gn gd cn cd : Nat} (hk : kn ≤ kd) (hc : cn ≤ cd) (hkd : 0 < kd) (hgn : 0 < gn)
    (hgd : 0 < gd) (hcd : 0 < cd) (es : List Arc) :
    sumLoC ⟨(gn : ℚ) / gd, (kn : ℚ) / kd⟩ ((cn : ℚ) / cd) es = (es.map (loN kn kd gn gd cn cd)).sum := by
  unfold sumLoC
  congr 1
  exact List.map_congr_left (fun e _ => loC_eq_loN hk hc hkd hgn hgd hcd e)

theorem sumHiC_eq {kn kd gn gd cn cd : Nat} (hc : cn ≤ cd) (hkd : 0 < kd)
    (hgd : 0 < gd) (hcd : 0 < cd) (es : List Arc) :
    sumHiC ⟨(gn : ℚ) / gd, (kn : ℚ) / kd⟩ ((cn : ℚ) / cd) es = (es.map (hiN kn kd gn gd cn cd)).sum := by
  unfold sumHiC
  congr 1
  exact List.map_congr_left (fun e _ => hiC_eq_hiN hc hkd hgd hcd e)

end Formal.Cells.CornerSlice
