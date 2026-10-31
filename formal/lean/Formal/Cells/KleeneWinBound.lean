import Formal.Cells.KleeneWin
open Formal.Core.LutList

/-!
# KleeneWinBound (probe Bwb): `+W` under H_W_BOUND, sufficient and needed, for every per-edge iff

Notes: `formal/notes/B-kleene-win-bound.md`. Follow-up of `KleeneWin` (probe Bxw) and
`SelfAuditB7.steer_win_bound` (bd_steer only). KleeneWin's per-edge iffs all have one shape:
a conjunction of race pairs `X + s ≤ Y` in binary-edge times, where `s = c(first) + a(after)`
is the exact window term of that pair. This file proves, once, for that shape
(`races_suff`, `races_need`), that

* `+W` is SUFFICIENT whenever every pair's term is at most `W` (H_W_BOUND), whatever the split;
* `+W` is NEEDED: on any pair whose term equals `W`, a binary-edge margin below `W` (e.g. `W - 1`)
  is unsafe (some behaviour in the box violates the spec: the counter-trace inside the iff);

and instantiates it for every KleeneWin cell.

## Assumed / proved / NOT covered

**Assumed:** exactly the hypotheses of the KleeneWin iffs (H_X_EDGE per edge, H_PIN_READ box,
H_KLEENE_LUT on the real INITs, H_RESET; for the C-element H_TREE, H_MUX_KLEENE, H_IN_PHASES and
H_FB_WIN), plus the bound under test, in one of three readings:
* **H_W_BOUND (pair)**, the JSON's reading: `c_e + a_l ≤ W` for every race pair `(e, l)`.
* **H_W_EDGE (width)**: every edge's window `[T - a_T, T + c_T)` has `0 ≤ a_T`, `0 ≤ c_T`,
  `a_T + c_T ≤ W` (the window contains its binary edge, width at most `W`).
* for the C-element, **H_FBW_BOUND**: the feedback pin's own window `wq ≤ Wq`.

**Proved:**
* `races_suff` / `races_need`: the generic lemma (any iff of the race-list shape).
* Pair reading, `+W` sufficient AND needed (per pair): `steer_win_bound'`/`steer_win_need_*`,
  `join_win_bound`/`join_win_need_*`, `muxn_win_bound`/`muxn_win_need_*`,
  `latch_win_bound`/`latch_win_need_*`.
* Width reading: `+2W` is sufficient (`*_edge_bound`) and needed (`join_edge_need`,
  `latch_edge_need`: split `c_e = a_l = W`); without `0 ≤ a_T, c_T` NO finite margin is
  sufficient, even with every width 0 (`join_width_unbounded`).
* C-element own-feedback race (any `Facts` cycle, H_FB_WIN): the exact term is
  `cf + wq + ar`, so the bound is **`+W + Wq`** under (pair, H_FBW_BOUND) and it is tight
  (`cel_env_win_bound`, `cel_env_win_need`); `+2W` is the special case `Wq = W`
  (`cel_env_win_bound_2W`); under the width reading it is `+2W + Wq` (`+3W` at `Wq = W`),
  also tight (`cel_env_edge_bound`, `cel_env_edge_need`). Per run: `cel_win_bound`; the
  explicit counter-run at margin `W + wq - 1` for every split, every loop delay and every
  `wq`, on any `Facts` cycle (`cel_win_ct`) and on the real bd_c2 INIT (`c2_win_ct`), with the
  clean run one tick later (`cel_win_clean_at`, `c2_win_clean`).
* Non-vacuity: `join_bound_pair_witness` (bound hypotheses satisfiable at `W = 2` with a
  non-uniform split, safe at margin `W`, unsafe at `W - 1` with the same widths bound),
  `latch_bound_pair_witness`, `muxn_bound_witness`, `steer_bound_pair_witness`,
  `c2_win_ct`/`c2_win_clean` (`W = 2`, `wq = 1`).

**NOT covered:** the value of `W`, `Wq` (unmeasured; board test XW-1 in B-kleene-win.md);
whether H_W_BOUND holds on the fabric; rows whose `+1` is NOT a KleeneWin iff (the reset rows
backed by `*_rst_dec`, which are not `Facts` cycles); that each C-element-backed JSON row IS an
instance of the `Facts` own-feedback race (that mapping is the row's existing `backing`, not
re-proved here); bdc_muxn's unselected joins; correlated corners; windows chosen per token by
the box adversary.
-/

namespace Formal.Cells.KleeneWinBound
open Formal.Cells
open Formal.Cells.KleeneWin
open Formal.Cells.KleeneBox (MuxSafeK StabK)
open Formal.Cells.CElemStrict (Facts Spec edge phase c2Cycle c2F c2_all)

/-! ## 1. The generic lemma -/

/-- One race pair in binary-edge times: `X` = the edge that must come first plus its read delay
(max), `Y` = the edge that must come after plus its read delay (min), `s` = the exact window
term `c(first) + a(after)`. -/
structure Race where
  X : Int
  s : Int
  Y : Int

def Race.ok (r : Race) : Prop := r.X + r.s ≤ r.Y

/-- Every race in the list holds (the right side of every KleeneWin iff). -/
def Races (l : List Race) : Prop := ∀ r ∈ l, r.ok

theorem races2 (a b : Race) : Races [a, b] ↔ a.ok ∧ b.ok := by simp [Races]
theorem races3 (a b c : Race) : Races [a, b, c] ↔ a.ok ∧ b.ok ∧ c.ok := by simp [Races]
theorem races4 (a b c d : Race) : Races [a, b, c, d] ↔ a.ok ∧ b.ok ∧ c.ok ∧ d.ok := by
  simp [Races]

/-- **Generic, sufficient.** If a safety property is exactly a list of races and every race's
window term is at most `W` (H_W_BOUND), then the binary-edge margins `+W` are sufficient. -/
theorem races_suff {P : Prop} {l : List Race} (h : P ↔ Races l) (W : Int)
    (H_W_BOUND : ∀ r ∈ l, r.s ≤ W) (hm : ∀ r ∈ l, r.X + W ≤ r.Y) : P :=
  h.2 fun r hr => by
    have := H_W_BOUND r hr; have := hm r hr
    unfold Race.ok; omega

/-- **Generic, needed.** If one race's window term equals `W`, a binary-edge margin below `W`
on that race (in particular `W - 1`) is unsafe. -/
theorem races_need {P : Prop} {l : List Race} (h : P ↔ Races l) {r : Race} (hr : r ∈ l) {W : Int}
    (hs : r.s = W) (hm : r.Y < r.X + W) : ¬ P := fun hp => by
  have := (h.1 hp) r hr
  unfold Race.ok at this; omega

/-! ## 2. `bd_steer` (completes `SelfAuditB7.steer_win_bound` with the necessity side) -/

section steer
variable (b v : Bool) (Rlo Rhi Slo Shi R F aR cR aF cF S0 cS0 S1 aS1 : Int)

def steerL : List Race := [⟨S0 + Shi, cS0 + aR, R + Rlo⟩, ⟨F + Rhi, cF + aS1, S1 + Slo⟩]

theorem steer_races (hR : Rlo ≤ Rhi) (hS : Slo ≤ Shi) (hRF : R - aR < F + cF) (hwR : 0 ≤ aR + cR)
    (hwF : 0 ≤ aF + cF) :
    SteerW b v Rlo Rhi Slo Shi R F aR cR aF cF S0 cS0 S1 aS1 ↔
      Races (steerL Rlo Rhi Slo Shi R F aR cF S0 cS0 S1 aS1) := by
  rw [steer_win_exact b v _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR hS hRF hwR hwF, steerL, races2]; rfl

/-- `+W` sufficient (same statement as `SelfAuditB7.steer_win_bound`, via the generic lemma). -/
theorem steer_win_bound' (W : Int) (hR : Rlo ≤ Rhi) (hS : Slo ≤ Shi) (hRF : R - aR < F + cF)
    (hwR : 0 ≤ aR + cR) (hwF : 0 ≤ aF + cF) (H_W_BOUND : cS0 + aR ≤ W ∧ cF + aS1 ≤ W)
    (h1 : S0 + Shi + W ≤ R + Rlo) (h2 : F + Rhi + W ≤ S1 + Slo) :
    SteerW b v Rlo Rhi Slo Shi R F aR cR aF cF S0 cS0 S1 aS1 :=
  races_suff (steer_races b v _ _ _ _ _ _ _ cR aF _ _ _ _ _ hR hS hRF hwR hwF) W
    (by simp [steerL]; omega) (by simp [steerL]; omega)

/-- `+W` needed on the setup pair: if `cS0 + aR = W`, a setup margin below `W` is unsafe. -/
theorem steer_win_need_setup (W : Int) (hR : Rlo ≤ Rhi) (hS : Slo ≤ Shi) (hRF : R - aR < F + cF)
    (hwR : 0 ≤ aR + cR) (hwF : 0 ≤ aF + cF) (hW : cS0 + aR = W) (hm : R + Rlo < S0 + Shi + W) :
    ¬ SteerW b v Rlo Rhi Slo Shi R F aR cR aF cF S0 cS0 S1 aS1 :=
  races_need (steer_races b v _ _ _ _ _ _ _ cR aF _ _ _ _ _ hR hS hRF hwR hwF)
    (r := ⟨S0 + Shi, cS0 + aR, R + Rlo⟩) (by simp [steerL]) hW hm

/-- `+W` needed on the hold pair. -/
theorem steer_win_need_hold (W : Int) (hR : Rlo ≤ Rhi) (hS : Slo ≤ Shi) (hRF : R - aR < F + cF)
    (hwR : 0 ≤ aR + cR) (hwF : 0 ≤ aF + cF) (hW : cF + aS1 = W) (hm : S1 + Slo < F + Rhi + W) :
    ¬ SteerW b v Rlo Rhi Slo Shi R F aR cR aF cF S0 cS0 S1 aS1 :=
  races_need (steer_races b v _ _ _ _ _ _ _ cR aF _ _ _ _ _ hR hS hRF hwR hwF)
    (r := ⟨F + Rhi, cF + aS1, S1 + Slo⟩) (by simp [steerL]) hW hm

end steer

/-- Non-vacuity and threshold (steer, `W = 2`): request rise window `(1, 0)`, select entry
`cS0 = 1`, so the setup pair's term is exactly 2; hold pair `(cF, aS1) = (0, 1)`. Binary setup
margin 2: safe; margin 1 (request one tick earlier): unsafe. -/
theorem steer_bound_pair_witness (b v : Bool) :
    SteerW b v 300 300 500 500 1002 3000 1 0 1 0 800 1 2802 1 ∧
    ¬ SteerW b v 300 300 500 500 1001 3000 1 0 1 0 800 1 2802 1 :=
  ⟨steer_win_bound' b v 300 300 500 500 1002 3000 1 0 1 0 800 1 2802 1 2 (by decide) (by decide)
      (by decide) (by decide) (by decide) ⟨by decide, by decide⟩ (by decide) (by decide),
   steer_win_need_setup b v 300 300 500 500 1001 3000 1 0 1 0 800 1 2802 1 2 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)⟩

/-! ## 3. `bd_mux` join -/

section join
variable (b v : Bool) (Rlo Rhi Clo Chi Slo Shi Qlo Qhi Cr Cf aCr cCr aCf cCf S0 cS0 S1 aS1 : Int)

def joinL : List Race := [⟨S0 + Shi, cS0 + aCr, Cr + Clo⟩, ⟨Cf + Chi, cCf + aS1, S1 + Slo⟩]

theorem join_races (hR : Rlo ≤ Rhi) (hC : Clo ≤ Chi) (hS : Slo ≤ Shi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (hCF : Cr - aCr < Cf + cCf) (hwR : 0 ≤ aCr + cCr) (hwF : 0 ≤ aCf + cCf) (hRst : 0 ≤ Cr - aCr + Clo) :
    JoinW b v Rlo Rhi Clo Chi Slo Shi Qlo Qhi Cr Cf aCr cCr aCf cCf S0 cS0 S1 aS1 ↔
      Races (joinL Clo Chi Slo Shi Cr Cf aCr cCf S0 cS0 S1 aS1) := by
  rw [join_win_exact b v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR hC hS hQ1 hQ hCF hwR hwF hRst, joinL,
    races2]; rfl

/-- **`+W` under H_W_BOUND, bd_mux join (sufficient).** -/
theorem join_win_bound (W : Int) (hR : Rlo ≤ Rhi) (hC : Clo ≤ Chi) (hS : Slo ≤ Shi) (hQ1 : 1 ≤ Qlo)
    (hQ : Qlo ≤ Qhi) (hCF : Cr - aCr < Cf + cCf) (hwR : 0 ≤ aCr + cCr) (hwF : 0 ≤ aCf + cCf)
    (hRst : 0 ≤ Cr - aCr + Clo) (H_W_BOUND : cS0 + aCr ≤ W ∧ cCf + aS1 ≤ W)
    (h1 : S0 + Shi + W ≤ Cr + Clo) (h2 : Cf + Chi + W ≤ S1 + Slo) :
    JoinW b v Rlo Rhi Clo Chi Slo Shi Qlo Qhi Cr Cf aCr cCr aCf cCf S0 cS0 S1 aS1 :=
  races_suff (join_races b v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR hC hS hQ1 hQ hCF hwR hwF hRst) W
    (by simp [joinL]; omega) (by simp [joinL]; omega)

/-- `+W` needed on the join's setup pair. -/
theorem join_win_need_setup (W : Int) (hR : Rlo ≤ Rhi) (hC : Clo ≤ Chi) (hS : Slo ≤ Shi)
    (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi) (hCF : Cr - aCr < Cf + cCf) (hwR : 0 ≤ aCr + cCr)
    (hwF : 0 ≤ aCf + cCf) (hRst : 0 ≤ Cr - aCr + Clo) (hW : cS0 + aCr = W)
    (hm : Cr + Clo < S0 + Shi + W) :
    ¬ JoinW b v Rlo Rhi Clo Chi Slo Shi Qlo Qhi Cr Cf aCr cCr aCf cCf S0 cS0 S1 aS1 :=
  races_need (join_races b v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR hC hS hQ1 hQ hCF hwR hwF hRst)
    (r := ⟨S0 + Shi, cS0 + aCr, Cr + Clo⟩) (by simp [joinL]) hW hm

/-- `+W` needed on the join's hold pair. -/
theorem join_win_need_hold (W : Int) (hR : Rlo ≤ Rhi) (hC : Clo ≤ Chi) (hS : Slo ≤ Shi)
    (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi) (hCF : Cr - aCr < Cf + cCf) (hwR : 0 ≤ aCr + cCr)
    (hwF : 0 ≤ aCf + cCf) (hRst : 0 ≤ Cr - aCr + Clo) (hW : cCf + aS1 = W)
    (hm : S1 + Slo < Cf + Chi + W) :
    ¬ JoinW b v Rlo Rhi Clo Chi Slo Shi Qlo Qhi Cr Cf aCr cCr aCf cCf S0 cS0 S1 aS1 :=
  races_need (join_races b v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hR hC hS hQ1 hQ hCF hwR hwF hRst)
    (r := ⟨Cf + Chi, cCf + aS1, S1 + Slo⟩) (by simp [joinL]) hW hm

/-- **Width reading (H_W_EDGE), bd_mux join: `+2W` sufficient.** Every edge's window contains
its binary edge (`0 ≤ a_T`, `0 ≤ c_T`) and has width at most `W`. -/
theorem join_edge_bound (W aS0 cS1 : Int) (hR : Rlo ≤ Rhi) (hC : Clo ≤ Chi) (hS : Slo ≤ Shi)
    (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi) (hCF : Cr < Cf) (hRst : 0 ≤ Cr - aCr + Clo)
    (H_W_EDGE : (0 ≤ aCr ∧ 0 ≤ cCr ∧ aCr + cCr ≤ W) ∧ (0 ≤ aCf ∧ 0 ≤ cCf ∧ aCf + cCf ≤ W) ∧
      (0 ≤ aS0 ∧ 0 ≤ cS0 ∧ aS0 + cS0 ≤ W) ∧ (0 ≤ aS1 ∧ 0 ≤ cS1 ∧ aS1 + cS1 ≤ W))
    (h1 : S0 + Shi + 2 * W ≤ Cr + Clo) (h2 : Cf + Chi + 2 * W ≤ S1 + Slo) :
    JoinW b v Rlo Rhi Clo Chi Slo Shi Qlo Qhi Cr Cf aCr cCr aCf cCf S0 cS0 S1 aS1 :=
  join_win_bound b v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (2 * W) hR hC hS hQ1 hQ (by omega) (by omega)
    (by omega) hRst (by omega) h1 h2

/-- Width reading, `+2W` needed: the split `cS0 = W`, `aCr = W` (each window of width `W`,
lying entirely after the select's entry edge and entirely before the request's rise) makes a
setup margin below `2W` unsafe. -/
theorem join_edge_need (W : Int) (hR : Rlo ≤ Rhi) (hC : Clo ≤ Chi) (hS : Slo ≤ Shi)
    (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi) (hW0 : 0 ≤ W) (hCF : Cr - W < Cf + cCf) (hwF : 0 ≤ aCf + cCf)
    (hRst : 0 ≤ Cr - W + Clo) (hm : Cr + Clo < S0 + Shi + 2 * W) :
    ¬ JoinW b v Rlo Rhi Clo Chi Slo Shi Qlo Qhi Cr Cf W 0 aCf cCf S0 W S1 aS1 :=
  join_win_need_setup b v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (2 * W) hR hC hS hQ1 hQ hCF (by omega)
    hwF hRst (by omega) hm

/-- **Width alone bounds nothing.** If a half may be negative (the window need not contain its
binary edge), then for EVERY margin `M` there is a split with every window of width 0 (the
select's entry window is the empty interval `M + 1` after its binary edge) under which binary
setup and hold margins of `M` are unsafe. -/
theorem join_width_unbounded (M : Int) :
    (850 - M) + 450 + M ≤ (1000 : Int) + 300 ∧ (3000 : Int) + 300 + M ≤ (4000 + M) + 450 ∧
    -(M + 1) + (M + 1) = 0 ∧
    ¬ JoinW b v 0 0 300 300 450 450 100 100 1000 3000 0 0 0 0 (850 - M) (M + 1) (4000 + M) 0 :=
  ⟨by omega, by omega, by omega,
   join_win_need_setup b v 0 0 300 300 450 450 100 100 1000 3000 0 0 0 0 (850 - M) (M + 1) (4000 + M) 0
    (M + 1) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by omega) (by omega)⟩

end join

/-- **Non-vacuity and threshold (join, `W = 2`).** Split: ctl_req rise `(0, 2)`, fall `(1, 1)`;
select entry `cS0 = 2`, exit `aS1 = 1`: the setup pair's term is `2 + 0 = 2 = W`, the hold pair's
`1 + 1 = 2 = W` (non-uniform halves). Setup margin exactly `W` (hold margin larger): safe;
setup margin `W - 1` (select one tick later): unsafe. That the box is inhabited by real-INIT
traces is KleeneWin's `join_witness_W` (other numbers), not re-proved here. -/
theorem join_bound_pair_witness (b v : Bool) :
    JoinW b v 0 0 300 300 450 450 100 100 1000 3000 0 2 1 1 848 2 4000 1 ∧
    ¬ JoinW b v 0 0 300 300 450 450 100 100 1000 3000 0 2 1 1 849 2 4000 1 :=
  ⟨join_win_bound b v 0 0 300 300 450 450 100 100 1000 3000 0 2 1 1 848 2 4000 1 2 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      ⟨by decide, by decide⟩ (by decide) (by decide),
   join_win_need_setup b v 0 0 300 300 450 450 100 100 1000 3000 0 2 1 1 849 2 4000 1 2 (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide)⟩

/-! ## 4. `bdc_muxn` selected join -/

section muxn
variable (k : Nat) (hk : k < 3)
  (Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Cr Cf aCr cCr aCf cCf A0 cA0 A1 aA1 B0 cB0 B1 aB1 : Int)

def muxnL : List Race :=
  [⟨A0 + Ahi, cA0 + aCr, Cr + Clo⟩, ⟨Cf + Chi, cCf + aA1, A1 + Alo⟩,
   ⟨B0 + Bhi, cB0 + aCr, Cr + Clo⟩, ⟨Cf + Chi, cCf + aB1, B1 + Blo⟩]

include hk in
theorem muxn_races (hRb : Rlo ≤ Rhi) (hDb : Dlo ≤ Dhi) (hCb : Clo ≤ Chi) (hAb : Alo ≤ Ahi)
    (hBb : Blo ≤ Bhi) (hQ1 : 1 ≤ Qlo) (hQb : Qlo ≤ Qhi) (hCF : Cr - aCr < Cf + cCf)
    (hwR : 0 ≤ aCr + cCr) (hwF : 0 ≤ aCf + cCf) (hRst : 0 ≤ Cr - aCr + Clo + Dlo) :
    MuxSafeK k Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi
      (A0 + cA0) (A1 - aA1) (B0 + cB0) (B1 - aB1) (ReqW Cr Cf aCr cCr aCf cCf) ↔
    Races (muxnL Clo Chi Alo Ahi Blo Bhi Cr Cf aCr cCf A0 cA0 A1 aA1 B0 cB0 B1 aB1) := by
  rw [muxn_win_exact k hk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hRb hDb hCb hAb hBb hQ1 hQb
    hCF hwR hwF hRst, muxnL, races4]; rfl

include hk in
/-- **`+W` under H_W_BOUND, bdc_muxn selected join (sufficient).** Four race pairs. -/
theorem muxn_win_bound (W : Int) (hRb : Rlo ≤ Rhi) (hDb : Dlo ≤ Dhi) (hCb : Clo ≤ Chi)
    (hAb : Alo ≤ Ahi) (hBb : Blo ≤ Bhi) (hQ1 : 1 ≤ Qlo) (hQb : Qlo ≤ Qhi) (hCF : Cr - aCr < Cf + cCf)
    (hwR : 0 ≤ aCr + cCr) (hwF : 0 ≤ aCf + cCf) (hRst : 0 ≤ Cr - aCr + Clo + Dlo)
    (H_W_BOUND : cA0 + aCr ≤ W ∧ cCf + aA1 ≤ W ∧ cB0 + aCr ≤ W ∧ cCf + aB1 ≤ W)
    (h1 : A0 + Ahi + W ≤ Cr + Clo) (h2 : Cf + Chi + W ≤ A1 + Alo)
    (h3 : B0 + Bhi + W ≤ Cr + Clo) (h4 : Cf + Chi + W ≤ B1 + Blo) :
    MuxSafeK k Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi
      (A0 + cA0) (A1 - aA1) (B0 + cB0) (B1 - aB1) (ReqW Cr Cf aCr cCr aCf cCf) :=
  races_suff (muxn_races k hk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hRb hDb hCb hAb hBb hQ1
    hQb hCF hwR hwF hRst) W (by simp [muxnL]; omega) (by simp [muxnL]; omega)

include hk in
/-- `+W` needed, index bit A setup pair (`cA0 + aCr = W`). The other three pairs are
`muxn_win_need` with the matching `r`; bit B is the same statement with `A ↔ B`. -/
theorem muxn_win_need (W : Int) (hRb : Rlo ≤ Rhi) (hDb : Dlo ≤ Dhi) (hCb : Clo ≤ Chi)
    (hAb : Alo ≤ Ahi) (hBb : Blo ≤ Bhi) (hQ1 : 1 ≤ Qlo) (hQb : Qlo ≤ Qhi) (hCF : Cr - aCr < Cf + cCf)
    (hwR : 0 ≤ aCr + cCr) (hwF : 0 ≤ aCf + cCf) (hRst : 0 ≤ Cr - aCr + Clo + Dlo)
    (r : Race) (hr : r ∈ muxnL Clo Chi Alo Ahi Blo Bhi Cr Cf aCr cCf A0 cA0 A1 aA1 B0 cB0 B1 aB1)
    (hW : r.s = W) (hm : r.Y < r.X + W) :
    ¬ MuxSafeK k Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi
      (A0 + cA0) (A1 - aA1) (B0 + cB0) (B1 - aB1) (ReqW Cr Cf aCr cCr aCf cCf) :=
  races_need (muxn_races k hk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hRb hDb hCb hAb hBb hQ1
    hQb hCF hwR hwF hRst) hr hW hm

end muxn

/-- Non-vacuity and threshold (muxn, decode index `k = 1`, `W = 2`): ctl_req rise `(1, 0)`, fall
`(0, 1)`; bit A entry `cA0 = 1`, exit `aA1 = 1`; bit B entry `cB0 = 0`, exit `aB1 = 0`: race
terms `2, 2, 1, 1`. Binary margins at least `W` (bit A setup exactly `W`): safe; bit A setup
margin `W - 1`: unsafe. -/
theorem muxn_bound_witness :
    MuxSafeK 1 0 0 50 50 300 300 450 450 450 450 100 100 (849 + 1) (4000 - 1) (840 + 0) (4000 - 0)
      (ReqW 1001 3000 1 0 0 1) ∧
    ¬ MuxSafeK 1 0 0 50 50 300 300 450 450 450 450 100 100 (850 + 1) (4000 - 1) (840 + 0) (4000 - 0)
      (ReqW 1001 3000 1 0 0 1) :=
  ⟨muxn_win_bound 1 (by decide) 0 0 50 50 300 300 450 450 450 450 100 100 1001 3000 1 0 0 1 849 1 4000 1
      840 0 4000 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide, by decide⟩
      (by decide) (by decide) (by decide) (by decide),
   muxn_win_need 1 (by decide) 0 0 50 50 300 300 450 450 450 450 100 100 1001 3000 1 0 0 1 850 1 4000 1
      840 0 4000 0 2 (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) ⟨850 + 450, 1 + 1, 1001 + 300⟩
      (by simp [muxnL]) (by decide) (by decide)⟩

/-! ## 5. `bd_latch` -/

section latch
variable (v : Bool) (Ton cOn Toff aOff cOff Td cD Tnew aN Dlo Dhi Elo Ehi Qlo Qhi : Int)

def latchL : List Race :=
  [⟨Ton + Ehi + Qhi, cOn + aOff, Toff + Elo⟩, ⟨Td + Dhi + Qhi, cD + aOff, Toff + Elo⟩,
   ⟨Toff + Ehi, cOff + aN, Tnew + Dlo⟩]

theorem latch_races (hD : Dlo ≤ Dhi) (hE : Elo ≤ Ehi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (hAB : Ton + cOn ≤ Toff - aOff) (hwOff : 0 ≤ aOff + cOff) (H_T0 : 0 ≤ Ton + cOn + Elo) :
    LibGapLatch.SafeBox v (Ton + cOn) (Toff - aOff) (Toff + cOff) (Td + cD) (Tnew - aN)
        Dlo Dhi Elo Ehi Qlo Qhi ↔
      Races (latchL Ton cOn Toff aOff cOff Td cD Tnew aN Dlo Dhi Elo Ehi Qhi) := by
  rw [latch_win_exact v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hD hE hQ1 hQ hAB hwOff H_T0, latchL, races3]; rfl

/-- **`+W` under H_W_BOUND, bd_latch (setup_pulse, setup_data, hold; sufficient).** -/
theorem latch_win_bound (W : Int) (hD : Dlo ≤ Dhi) (hE : Elo ≤ Ehi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (hAB : Ton + cOn ≤ Toff - aOff) (hwOff : 0 ≤ aOff + cOff) (H_T0 : 0 ≤ Ton + cOn + Elo)
    (H_W_BOUND : cOn + aOff ≤ W ∧ cD + aOff ≤ W ∧ cOff + aN ≤ W)
    (h_pulse : Ton + Ehi + Qhi + W ≤ Toff + Elo) (h_data : Td + Dhi + Qhi + W ≤ Toff + Elo)
    (h_hold : Toff + Ehi + W ≤ Tnew + Dlo) :
    LibGapLatch.SafeBox v (Ton + cOn) (Toff - aOff) (Toff + cOff) (Td + cD) (Tnew - aN)
        Dlo Dhi Elo Ehi Qlo Qhi :=
  races_suff (latch_races v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hD hE hQ1 hQ hAB hwOff H_T0) W
    (by simp [latchL]; omega) (by simp [latchL]; omega)

theorem latch_win_need_pulse (W : Int) (hD : Dlo ≤ Dhi) (hE : Elo ≤ Ehi) (hQ1 : 1 ≤ Qlo)
    (hQ : Qlo ≤ Qhi) (hAB : Ton + cOn ≤ Toff - aOff) (hwOff : 0 ≤ aOff + cOff)
    (H_T0 : 0 ≤ Ton + cOn + Elo) (hW : cOn + aOff = W) (hm : Toff + Elo < Ton + Ehi + Qhi + W) :
    ¬ LibGapLatch.SafeBox v (Ton + cOn) (Toff - aOff) (Toff + cOff) (Td + cD) (Tnew - aN)
        Dlo Dhi Elo Ehi Qlo Qhi :=
  races_need (latch_races v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hD hE hQ1 hQ hAB hwOff H_T0)
    (r := ⟨Ton + Ehi + Qhi, cOn + aOff, Toff + Elo⟩) (by simp [latchL]) hW hm

theorem latch_win_need_data (W : Int) (hD : Dlo ≤ Dhi) (hE : Elo ≤ Ehi) (hQ1 : 1 ≤ Qlo)
    (hQ : Qlo ≤ Qhi) (hAB : Ton + cOn ≤ Toff - aOff) (hwOff : 0 ≤ aOff + cOff)
    (H_T0 : 0 ≤ Ton + cOn + Elo) (hW : cD + aOff = W) (hm : Toff + Elo < Td + Dhi + Qhi + W) :
    ¬ LibGapLatch.SafeBox v (Ton + cOn) (Toff - aOff) (Toff + cOff) (Td + cD) (Tnew - aN)
        Dlo Dhi Elo Ehi Qlo Qhi :=
  races_need (latch_races v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hD hE hQ1 hQ hAB hwOff H_T0)
    (r := ⟨Td + Dhi + Qhi, cD + aOff, Toff + Elo⟩) (by simp [latchL]) hW hm

theorem latch_win_need_hold (W : Int) (hD : Dlo ≤ Dhi) (hE : Elo ≤ Ehi) (hQ1 : 1 ≤ Qlo)
    (hQ : Qlo ≤ Qhi) (hAB : Ton + cOn ≤ Toff - aOff) (hwOff : 0 ≤ aOff + cOff)
    (H_T0 : 0 ≤ Ton + cOn + Elo) (hW : cOff + aN = W) (hm : Tnew + Dlo < Toff + Ehi + W) :
    ¬ LibGapLatch.SafeBox v (Ton + cOn) (Toff - aOff) (Toff + cOff) (Td + cD) (Tnew - aN)
        Dlo Dhi Elo Ehi Qlo Qhi :=
  races_need (latch_races v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hD hE hQ1 hQ hAB hwOff H_T0)
    (r := ⟨Toff + Ehi, cOff + aN, Tnew + Dlo⟩) (by simp [latchL]) hW hm

/-- Width reading, bd_latch: `+2W` sufficient when every half is in `[0, W]` (each window
contains its binary edge and has width at most `W`). -/
theorem latch_edge_bound (W : Int) (hD : Dlo ≤ Dhi) (hE : Elo ≤ Ehi) (hQ1 : 1 ≤ Qlo)
    (hQ : Qlo ≤ Qhi) (hAB : Ton + cOn ≤ Toff - aOff) (H_T0 : 0 ≤ Ton + cOn + Elo)
    (H_W_EDGE : (0 ≤ cOn ∧ cOn ≤ W) ∧ (0 ≤ aOff ∧ 0 ≤ cOff ∧ aOff + cOff ≤ W) ∧ (0 ≤ cD ∧ cD ≤ W) ∧
      (0 ≤ aN ∧ aN ≤ W))
    (h_pulse : Ton + Ehi + Qhi + 2 * W ≤ Toff + Elo) (h_data : Td + Dhi + Qhi + 2 * W ≤ Toff + Elo)
    (h_hold : Toff + Ehi + 2 * W ≤ Tnew + Dlo) :
    LibGapLatch.SafeBox v (Ton + cOn) (Toff - aOff) (Toff + cOff) (Td + cD) (Tnew - aN)
        Dlo Dhi Elo Ehi Qlo Qhi :=
  latch_win_bound v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (2 * W) hD hE hQ1 hQ hAB (by omega) H_T0 (by omega)
    h_pulse h_data h_hold

/-- Width reading, `+2W` needed on the hold: `cOff = W` (the enable's fall window after its
binary edge) and `aN = W` (the next data's window before its binary edge). -/
theorem latch_edge_need (W : Int) (hD : Dlo ≤ Dhi) (hE : Elo ≤ Ehi) (hQ1 : 1 ≤ Qlo)
    (hQ : Qlo ≤ Qhi) (hW0 : 0 ≤ W) (hAB : Ton + cOn ≤ Toff) (H_T0 : 0 ≤ Ton + cOn + Elo)
    (hm : Tnew + Dlo < Toff + Ehi + 2 * W) :
    ¬ LibGapLatch.SafeBox v (Ton + cOn) (Toff - 0) (Toff + W) (Td + cD) (Tnew - W)
        Dlo Dhi Elo Ehi Qlo Qhi :=
  latch_win_need_hold v _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (2 * W) hD hE hQ1 hQ (by omega) (by omega) H_T0
    (by omega) hm

end latch

/-- Non-vacuity and threshold (latch, `W = 3`): KleeneWin's witness split (`cOn = 1`,
`aOff = 1`, `cOff = 0`, `cD = 2`, `aN = 2`): terms `2, 3, 2`, all `≤ W = 3`; with
`Ton = 1997`, `Td = 996`, `Tnew = 3804` the binary margins are at least `W` (hold exactly `W`):
safe. With the hold term raised to `W` (`cOff = 1`) and the next data one tick earlier
(`Tnew = 3803`, hold margin `W - 1`): unsafe. -/
theorem latch_bound_pair_witness :
    LibGapLatch.SafeBox true (1997 + 1) (3301 - 1) (3301 + 0) (996 + 2) (3804 - 2) 300 700 400 800 300 900 ∧
    ¬ LibGapLatch.SafeBox true (1997 + 1) (3301 - 1) (3301 + 1) (996 + 2) (3803 - 2) 300 700 400 800 300 900 :=
  ⟨latch_win_bound true 1997 1 3301 1 0 996 2 3804 2 300 700 400 800 300 900 3 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) ⟨by decide, by decide, by decide⟩
      (by decide) (by decide) (by decide),
   latch_win_need_hold true 1997 1 3301 1 1 996 2 3803 2 300 700 400 800 300 900 3 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)⟩

/-! ## 6. The C-element own-feedback race (any `Facts` cycle), feedback window H_FB_WIN

Nat time (as in CElemStrict / KleeneWin section 6). The exact term is `cf + wq + ar`: the
follow pin's trailing half, the feedback pin's own window, the release pin's leading half.
The race PAIR is (follow, release); `wq` is not a pair term. -/

section cel
variable {ι : Type} {F : ι → K3 → K3} {I0 IX I1 RX R1 : ι} {v n : Bool}

/-- **Per run, sufficient.** H_W_BOUND on the pair (`cf + ar ≤ W`): the binary-edge race
`Tf + D + W + wq ≤ Tr` gives one clean edge. -/
theorem cel_win_bound {Tf af cf Tr ar cr D wq W : Nat} {i : Nat → ι} {qp G : Nat → K3}
    (L : LoopW F I0 IX I1 RX R1 v (Tf - af) (af + cf) (Tr - ar) (ar + cr) D wq i qp G)
    (H : Facts F I0 IX I1 RX R1 v n) (hD : 1 ≤ D) (haf : af ≤ Tf) (har : ar ≤ Tr)
    (H_W_BOUND : cf + ar ≤ W) (hm : Tf + D + W + wq ≤ Tr) : Spec v n (Tf - af) (af + cf) G :=
  cleanW L H hD (by omega)

/-- **Box, sufficient: `+W + Wq`.** In B's terms: `dlmax + dwmax + W + Wq ≤ dlmin + E`, with
`cf + ar ≤ W` (pair) and the feedback window `wq ≤ Wq` (in `SafeBoxW`). -/
theorem cel_env_win_bound (H : Facts F I0 IX I1 RX R1 v n)
    {Tf af cf ar cr Dlo dlmin dlmax dwmax E Wq W : Nat}
    (hlo : 1 ≤ Dlo) (hbox : Dlo ≤ dlmax + dwmax) (haf : af ≤ Tf) (H_W_BOUND : cf + ar ≤ W)
    (hm : dlmax + dwmax + W + Wq ≤ dlmin + E) :
    SafeBoxW F I0 IX I1 RX R1 v n (Tf - af) (af + cf) (ar + cr) Dlo (dlmax + dwmax) Wq
      (Tf + dlmin + E - ar) :=
  (cel_env_win_iff H hlo hbox haf (by omega)).2 (by omega)

/-- **Box, needed: `+W + Wq` is tight.** For any split with `cf + ar = W` and any `Wq`, a
binary-edge margin below `W + Wq` is unsafe (the counter-run at `D = dlmax + dwmax`,
`wq = Wq` inside `box_iffW`). -/
theorem cel_env_win_need (H : Facts F I0 IX I1 RX R1 v n)
    {Tf af cf ar cr Dlo dlmin dlmax dwmax E Wq W : Nat}
    (hlo : 1 ≤ Dlo) (hbox : Dlo ≤ dlmax + dwmax) (haf : af ≤ Tf) (hord : cf + ar ≤ dlmin + E)
    (hW : cf + ar = W) (hm : dlmin + E < dlmax + dwmax + W + Wq) :
    ¬ SafeBoxW F I0 IX I1 RX R1 v n (Tf - af) (af + cf) (ar + cr) Dlo (dlmax + dwmax) Wq
      (Tf + dlmin + E - ar) := fun h => by
  have := (cel_env_win_iff H hlo hbox haf hord).1 h
  omega

/-- `+2W`: the case where H_W_BOUND also bounds the feedback pin's window (`Wq = W`). -/
theorem cel_env_win_bound_2W (H : Facts F I0 IX I1 RX R1 v n)
    {Tf af cf ar cr Dlo dlmin dlmax dwmax E W : Nat}
    (hlo : 1 ≤ Dlo) (hbox : Dlo ≤ dlmax + dwmax) (haf : af ≤ Tf) (H_W_BOUND : cf + ar ≤ W)
    (hm : dlmax + dwmax + 2 * W ≤ dlmin + E) :
    SafeBoxW F I0 IX I1 RX R1 v n (Tf - af) (af + cf) (ar + cr) Dlo (dlmax + dwmax) W
      (Tf + dlmin + E - ar) :=
  cel_env_win_bound H hlo hbox haf H_W_BOUND (by omega)

/-- Width reading (every window of width `≤ W`; halves are Nat, so non-negative): the pair
term `cf + ar` can reach `2W`, so the bound is `+2W + Wq` (`+3W` at `Wq = W`). Sufficient. -/
theorem cel_env_edge_bound (H : Facts F I0 IX I1 RX R1 v n)
    {Tf af cf ar cr Dlo dlmin dlmax dwmax E Wq W : Nat}
    (hlo : 1 ≤ Dlo) (hbox : Dlo ≤ dlmax + dwmax) (haf : af ≤ Tf)
    (H_W_EDGE : af + cf ≤ W ∧ ar + cr ≤ W) (hm : dlmax + dwmax + 2 * W + Wq ≤ dlmin + E) :
    SafeBoxW F I0 IX I1 RX R1 v n (Tf - af) (af + cf) (ar + cr) Dlo (dlmax + dwmax) Wq
      (Tf + dlmin + E - ar) :=
  cel_env_win_bound H hlo hbox haf (W := 2 * W) (by omega) (by omega)

/-- Width reading, needed: the split `af = 0, cf = W` (follow window after its edge),
`ar = W, cr = 0` (release window before its edge) makes any margin below `2W + Wq` unsafe. -/
theorem cel_env_edge_need (H : Facts F I0 IX I1 RX R1 v n)
    {Tf Dlo dlmin dlmax dwmax E Wq W : Nat}
    (hlo : 1 ≤ Dlo) (hbox : Dlo ≤ dlmax + dwmax) (hord : 2 * W ≤ dlmin + E)
    (hm : dlmin + E < dlmax + dwmax + 2 * W + Wq) :
    ¬ SafeBoxW F I0 IX I1 RX R1 v n (Tf - 0) (0 + W) (W + 0) Dlo (dlmax + dwmax) Wq
      (Tf + dlmin + E - W) :=
  cel_env_win_need H (af := 0) (cf := W) (ar := W) (cr := 0) hlo hbox (Nat.zero_le _) (by omega)
    (W := 2 * W) (by omega) hm

/-- **Explicit counter-run, every split, every loop delay, every feedback window** (any `Facts`
cycle). The simulated loop (`simGW`, loop delay `D = d + 1`, feedback window `wq`) with the
follow pin's binary edge `Tf` (window `[Tf - af, Tf + cf)`) and the release pin's X window
starting at `s = Tf + cf + d + wq` (binary edge `Tr = s + ar`): the binary-edge margin is
`Tr - Tf - D = cf + ar + wq - 1`, one tick short of `W + wq` with `W = cf + ar`, and the root at
`s` is not `n` where the spec says `n`. -/
theorem cel_win_ct (H : Facts F I0 IX I1 RX R1 v n) (Tf af cf ar cr d wq : Nat) (haf : af ≤ Tf) :
    simGW F (phase I0 IX I1 RX R1 (Tf - af) (af + cf) (Tf + cf + d + wq) (ar + cr)) v d wq
        (Tf + cf + d + wq) ≠ K3.ofBool n ∧
      edge v n (Tf - af) (af + cf) (Tf + cf + d + wq) = K3.ofBool n ∧
      (Tf + cf + d + wq + ar) + 1 = Tf + (d + 1) + (cf + ar) + wq :=
  have hz := hazardW (sim_loopW F (phase I0 IX I1 RX R1 (Tf - af) (af + cf) (Tf + cf + d + wq) (ar + cr))
    v d wq (fun _ => rfl)) H (by omega) (by omega) (by omega)
  ⟨hz.1, hz.2, by omega⟩

/-- The clean side one tick later (margin exactly `W + wq`): the simulated loop is the spec. -/
theorem cel_win_clean_at (H : Facts F I0 IX I1 RX R1 v n) (Tf af cf ar cr d wq : Nat) (haf : af ≤ Tf) :
    Spec v n (Tf - af) (af + cf)
      (simGW F (phase I0 IX I1 RX R1 (Tf - af) (af + cf) (Tf + cf + d + wq + 1) (ar + cr)) v d wq) :=
  cleanW (sim_loopW F (phase I0 IX I1 RX R1 (Tf - af) (af + cf) (Tf + cf + d + wq + 1) (ar + cr))
    v d wq (fun _ => rfl)) H (by omega) (by omega)

end cel

/-- **The real bd_c2 INIT (rising, follow b, release a), `W = 2`, `wq = 1`**, non-uniform split
follow `(af, cf) = (0, 1)`, release `(ar, cr) = (1, 0)`, loop delay `D = 420`: release binary
edge at `Tr = 423` (margin `Tr - Tf - D = 3 = W + wq`): clean; at `Tr = 422` (margin 2): the
root at the release window's start `421` is not 1 where the spec is 1. -/
theorem c2_win_ct :
    let c := c2Cycle false false true
    simGW c2F (phase c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 (0 - 0) (0 + 1) (0 + 1 + 419 + 1) (1 + 0))
        false 419 1 (0 + 1 + 419 + 1) ≠ K3.ofBool true ∧
      edge false true (0 - 0) (0 + 1) (0 + 1 + 419 + 1) = K3.ofBool true := by
  intro c
  have h := cel_win_ct (c2_all false false true) 0 0 1 1 0 419 1 (Nat.le_refl _)
  exact ⟨h.1, h.2.1⟩

theorem c2_win_clean :
    let c := c2Cycle false false true
    Spec false true (0 - 0) (0 + 1)
      (simGW c2F (phase c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 (0 - 0) (0 + 1) (0 + 1 + 419 + 1 + 1) (1 + 0))
        false 419 1) := by
  intro c
  exact cel_win_clean_at (c2_all false false true) 0 0 1 1 0 419 1 (Nat.le_refl _)

end Formal.Cells.KleeneWinBound
