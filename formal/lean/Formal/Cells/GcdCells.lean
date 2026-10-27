import Formal.Cells.PipeTimed

/-!
# Probe Bg2: timing of `bd_delay_gated` (cell_constraints `bd_delay_gated.gate`, row D5)

`bd_delay_gated` is the matched delay of every generated cell bdc emits:
in the gcd_hw kernel all 20 fused compute units (`bdc_fused_*`), the 8
arbitrated control merges (`bdc_amerge2_0` x7, `bdc_amerge3_0`) and the 3-way
mux (`bdc_muxn3_32`): 29 instances, N = 12..94
(`formal/notes/B-gcd-cells.md`). Until now it had a Kleene fact only
(`LibEndMemMlink.gated_gate_low`) and no timing theorem.

## The cell (cells/rtl/bd_latch.v), as instantiated by bdc

    gate  = the cell's join / arbiter node (`joined`, `r0`, `|j`)
    s[0]  = a = uor(gate)                 LUT1 buffer, the `uor` anchor
    s[1]  = g[0](s[0])                    LUT1 buffer
    s[i+1]= g[i](s[i], gate)  (1 <= i < N) LUT2 INIT 8: s[i] AND gate
    z     = s[N]

## Model

Each pin is read through its own FIFO read map (`PipeTimed.Ret`, the per-pin
model of `FifoFidelity.PinLut`, with the LUT's output stage folded into each
pin's map, `Ret.comp`): `r0` gate -> `uor` -> s[0]; `r1` s[0] -> s[1];
`p i` s[i] -> s[i+1] (chain pin) and `q i` gate -> s[i+1] (tap pin), i >= 1.
The relations are assumed at every instant (`Gated`).

## Results

* `no_early` (**the matched delay survives a reuse**): the gate low on
  `[F, T)`. If every stage's stale value is gone from its chain pin before the
  new gate rise reaches the tap pin of the same LUT (**H_GFLUSH i**,
  `(p i).fst (V i) <= (q i).fst T`), then from `V i` on, stage `i` is high only
  at or after `T + L i`, `L` the sum of the chain's LOWER bounds from the
  gate. So the request `z` cannot rise earlier than the full matched length
  after the gate rose, whatever the previous token left in the chain.
* `fast_fall`: `V (i+1) = (q i).fst F <= F + (q i).hi`: from one tap read
  after the gate fell, the output is low (until `T + L N`). This is the
  point of the cell (`bd_latch.v`: "z falls one LUT after the node").
* `rises` / `rise_by`: the gate high on `[T, F2)`: stage `i` is high on
  `[A i, B i)`, and `A i <= T + H i` (sum of the UPPER bounds, the tap paths
  included). No extra hypothesis: the rise needs none.
* `flush_needed`: without H_GFLUSH 1 the claim is false: N = 2, a short gate
  dip that the two ungated buffers (`uor`, `g[0]`) have not yet carried to
  `g[1]`'s chain pin when the gate rises again gives `z` high 6 ticks before
  `T + L 2` (an early request: the data it bundles may not be valid).

H_GFLUSH, in delays: stage 1 (`uor`, `g[0]` ungated):
`F + r0.hi + r1.hi + (p 1).hi <= T + (q 1).lo` suffices
(`gflush1_of_lat`): the gate's LOW phase at the cell must outlast the two
ungated hops plus the chain wire into `g[1]`, minus the fastest tap wire.
Stage `i >= 2`: `F + (q (i-1)).hi + (p i).hi <= T + (q i).lo`
(`gflush_of_lat`). tighten.py rule F (`audit_fastfall`, which covers
bd_delay_gated: head input = the `uor` output's late fall) checks each
stage's fall at the stage OUTPUT against the earliest reuse; it lacks the
in-flight term `(p i).hi - (q i).lo` (chain wire into the next LUT against
the tap wire into it), the same missing term as row D2. Within a four-phase
handshake the gate's low phase is a whole return-to-zero (the join's inputs
must fall and rise again), so a large margin is expected; not measured here.

`long_dip_no_early`, `long_dip_rises`: the hypotheses of `no_early` are met
by a concrete run (`gE_gated`, gate low on `[10, 30)`), and its `z` does rise
(at `30 + 7`), so neither theorem is vacuous.

Core Lean only; no sorry, no declared axiom, no native code.
-/

namespace Formal.Cells.GcdCells
open Formal.Cells
open Formal.Cells.PipeTimed

/-- **The gated line, per-pin.** `s 0` = `uor`, `s 1` = `g[0]`, `s (i+1)` =
`g[i]` for `i ≥ 1`; the output is `s N`. -/
structure Gated (g : Trace) (s : Nat → Trace) (r0 r1 : Ret) (p q : Nat → Ret) : Prop where
  h0 : ∀ t, s 0 t = g (r0.σ t)
  h1 : ∀ t, s 1 t = s 0 (r1.σ t)
  hs : ∀ i, 1 ≤ i → ∀ t, s (i + 1) t = (s i ((p i).σ t) && g ((q i).σ t))

/-- Sum of the lower bounds from the gate to stage `i` along the chain. -/
def L (r0 r1 : Ret) (p : Nat → Ret) : Nat → Nat
  | 0 => r0.lo
  | 1 => r0.lo + r1.lo
  | i + 1 => L r0 r1 p i + (p i).lo

/-- From when stage `i` no longer shows the previous token (gate fell at `F`). -/
def V (r0 r1 : Ret) (q : Nat → Ret) (F : Nat) : Nat → Nat
  | 0 => r0.fst F
  | 1 => r1.fst (r0.fst F)
  | i + 1 => (q i).fst F

/-- Earliest instant stage `i` is guaranteed high (gate rose at `T`). -/
def A (r0 r1 : Ret) (p q : Nat → Ret) (T : Nat) : Nat → Nat
  | 0 => r0.fst T
  | 1 => r1.fst (r0.fst T)
  | i + 1 => max ((p i).fst (A r0 r1 p q T i)) ((q i).fst T)

/-- Until when stage `i` is guaranteed high (gate falls at `F2`). -/
def B (r0 r1 : Ret) (p q : Nat → Ret) (F2 : Nat) : Nat → Nat
  | 0 => r0.fst F2
  | 1 => r1.fst (r0.fst F2)
  | i + 1 => min ((p i).fst (B r0 r1 p q F2 i)) ((q i).fst F2)

/-- Sum of the upper bounds (the tap path included) to stage `i`. -/
def H (r0 r1 : Ret) (p q : Nat → Ret) : Nat → Nat
  | 0 => r0.hi
  | 1 => r0.hi + r1.hi
  | i + 1 => max (H r0 r1 p q i + (p i).hi) (q i).hi

theorem L_succ (r0 r1 : Ret) (p : Nat → Ret) (i : Nat) (h : 1 ≤ i) :
    L r0 r1 p (i + 1) = L r0 r1 p i + (p i).lo := by
  cases i with
  | zero => omega
  | succ k => rfl

theorem V_succ (r0 r1 : Ret) (q : Nat → Ret) (F i : Nat) (h : 1 ≤ i) :
    V r0 r1 q F (i + 1) = (q i).fst F := by
  cases i with
  | zero => omega
  | succ k => rfl

theorem A_succ (r0 r1 : Ret) (p q : Nat → Ret) (T i : Nat) (h : 1 ≤ i) :
    A r0 r1 p q T (i + 1) = max ((p i).fst (A r0 r1 p q T i)) ((q i).fst T) := by
  cases i with
  | zero => omega
  | succ k => rfl

theorem B_succ (r0 r1 : Ret) (p q : Nat → Ret) (F2 i : Nat) (h : 1 ≤ i) :
    B r0 r1 p q F2 (i + 1) = min ((p i).fst (B r0 r1 p q F2 i)) ((q i).fst F2) := by
  cases i with
  | zero => omega
  | succ k => rfl

theorem H_succ (r0 r1 : Ret) (p q : Nat → Ret) (i : Nat) (h : 1 ≤ i) :
    H r0 r1 p q (i + 1) = max (H r0 r1 p q i + (p i).hi) (q i).hi := by
  cases i with
  | zero => omega
  | succ k => rfl

/-- A read map turns "high only from `T'`" upstream into "high only from
`T' + lo`" downstream (`T' ≥ 1`). -/
theorem late_read (r : Ret) {T' t : Nat} (h1 : 1 ≤ T') (h : T' ≤ r.σ t) : T' + r.lo ≤ t := by
  have := r.le t; omega

section gated
variable {g : Trace} {s : Nat → Trace} {r0 r1 : Ret} {p q : Nat → Ret}

/-- **No early request.** The gate low on `[F, T)` (`F < T`). Under
H_GFLUSH at every stage `1 ≤ i < N`, from `V i` on stage `i` is high only at
or after `T + L i`. -/
theorem no_early (G : Gated g s r0 r1 p q) (N F T : Nat) (hFT : F < T)
    (hlow : ∀ u, F ≤ u → u < T → g u = false)
    (H_GFLUSH : ∀ i, 1 ≤ i → i < N → (p i).fst (V r0 r1 q F i) ≤ (q i).fst T) :
    ∀ i, i ≤ N → ∀ t, V r0 r1 q F i ≤ t → s i t = true → T + L r0 r1 p i ≤ t := by
  intro i
  induction i with
  | zero =>
    intro _ t ht hs
    rw [G.h0] at hs
    have e1 : F ≤ r0.σ t := r0.fst_after ht
    have e2 : T ≤ r0.σ t := by
      apply Classical.byContradiction; intro hc
      rw [hlow _ e1 (by omega)] at hs; exact Bool.noConfusion hs
    exact late_read r0 (by omega) e2
  | succ i ih =>
    intro hiN t ht hs
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      rw [G.h1] at hs
      have e1 : r0.fst F ≤ r1.σ t := r1.fst_after ht
      have := ih (by omega) _ e1 hs
      have := late_read r1 (by omega) this
      show T + (r0.lo + r1.lo) ≤ t
      simp only [L] at this; omega
    · rw [G.hs i hpos] at hs
      rw [V_succ r0 r1 q F i hpos] at ht
      rw [L_succ r0 r1 p i hpos]
      have hsi : s i ((p i).σ t) = true := by
        cases h : s i ((p i).σ t) <;> simp_all
      have hg : g ((q i).σ t) = true := by
        cases h : g ((q i).σ t) <;> simp_all
      rcases Nat.lt_or_ge ((p i).σ t) (V r0 r1 q F i) with c | c
      · -- the chain pin still reads the stale stage: the tap must read the gate low
        have t1 : t < (p i).fst (V r0 r1 q F i) := by
          apply Classical.byContradiction; intro hc
          have := (p i).fst_after (c := V r0 r1 q F i) (t := t) (by omega); omega
        have t2 : t < (q i).fst T := by have := H_GFLUSH i hpos (by omega); omega
        have u1 : F ≤ (q i).σ t := (q i).fst_after ht
        have u2 : (q i).σ t < T := (q i).fst_before t2
        rw [hlow _ u1 u2] at hg; exact Bool.noConfusion hg
      · have h1 := ih (by omega) _ c hsi
        have h2 : 1 ≤ T + L r0 r1 p i := by omega
        have := late_read (p i) h2 h1
        omega

/-- **Fast fall.** For `i ≥ 1`, stage `i + 1` is clear of the previous token one
tap read after the gate fell. -/
theorem fast_fall (F i : Nat) (h : 1 ≤ i) : V r0 r1 q F (i + 1) ≤ F + (q i).hi := by
  rw [V_succ r0 r1 q F i h]; exact (q i).fst_le F

/-- **The rise arrives.** The gate high on `[T, F2)`: stage `i` is high on
`[A i, B i)`. No hypothesis beyond the gate relations. -/
theorem rises (G : Gated g s r0 r1 p q) (T F2 : Nat)
    (hhigh : ∀ u, T ≤ u → u < F2 → g u = true) :
    ∀ i t, A r0 r1 p q T i ≤ t → t < B r0 r1 p q F2 i → s i t = true := by
  intro i
  induction i with
  | zero =>
    intro t h1 h2
    rw [G.h0]; exact hhigh _ (r0.fst_after h1) (r0.fst_before h2)
  | succ i ih =>
    intro t h1 h2
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      rw [G.h1]
      exact ih _ (r1.fst_after h1) (r1.fst_before h2)
    · rw [A_succ r0 r1 p q T i hpos] at h1
      rw [B_succ r0 r1 p q F2 i hpos] at h2
      rw [G.hs i hpos]
      have a1 : (p i).fst (A r0 r1 p q T i) ≤ t := by omega
      have a2 : (q i).fst T ≤ t := by omega
      have b1 : t < (p i).fst (B r0 r1 p q F2 i) := by omega
      have b2 : t < (q i).fst F2 := by omega
      rw [ih _ ((p i).fst_after a1) ((p i).fst_before b1),
          hhigh _ ((q i).fst_after a2) ((q i).fst_before b2)]
      rfl

end gated

/-- **The rise is bounded.** `A i ≤ T + H i`. -/
theorem rise_by (r0 r1 : Ret) (p q : Nat → Ret) (T : Nat) :
    ∀ i, A r0 r1 p q T i ≤ T + H r0 r1 p q i := by
  intro i
  induction i with
  | zero => exact r0.fst_le T
  | succ i ih =>
    rcases Nat.eq_zero_or_pos i with h0 | hpos
    · subst h0
      have e1 := r0.fst_le T
      have e2 := r1.fst_le (r0.fst T)
      show r1.fst (r0.fst T) ≤ T + (r0.hi + r1.hi)
      omega
    · rw [A_succ r0 r1 p q T i hpos, H_succ r0 r1 p q i hpos]
      have e1 := (p i).fst_le (A r0 r1 p q T i)
      have e2 := (q i).fst_le T
      have m1 := Nat.le_max_left (H r0 r1 p q i + (p i).hi) (q i).hi
      have m2 := Nat.le_max_right (H r0 r1 p q i + (p i).hi) (q i).hi
      have : (p i).fst (A r0 r1 p q T i) ≤ T + max (H r0 r1 p q i + (p i).hi) (q i).hi := by
        omega
      have : (q i).fst T ≤ T + max (H r0 r1 p q i + (p i).hi) (q i).hi := by omega
      exact Nat.max_le.mpr ⟨by assumption, by assumption⟩

/-! ## H_GFLUSH in delays -/

/-- Stage 1 (behind the two ungated buffers `uor`, `g[0]`). -/
theorem gflush1_of_lat (r0 r1 : Ret) (p q : Nat → Ret) {F T : Nat} (hT : 1 ≤ T)
    (hlat : F + r0.hi + r1.hi + (p 1).hi ≤ T + (q 1).lo) :
    (p 1).fst (V r0 r1 q F 1) ≤ (q 1).fst T := by
  have e1 := r0.fst_le F
  have e2 := r1.fst_le (r0.fst F)
  have e3 := (p 1).fst_le (r1.fst (r0.fst F))
  have e4 := (q 1).fst_lo (c := T) hT
  show (p 1).fst (r1.fst (r0.fst F)) ≤ (q 1).fst T
  omega

/-- Stage `i ≥ 2` (its chain input was flushed by the previous tap). -/
theorem gflush_of_lat (r0 r1 : Ret) (p q : Nat → Ret) {F T i : Nat} (hi : 2 ≤ i) (hT : 1 ≤ T)
    (hlat : F + (q (i - 1)).hi + (p i).hi ≤ T + (q i).lo) :
    (p i).fst (V r0 r1 q F i) ≤ (q i).fst T := by
  obtain ⟨k, rfl⟩ : ∃ k, i = k + 1 := ⟨i - 1, by omega⟩
  rw [V_succ r0 r1 q F k (by omega)]
  have e1 := (q k).fst_le F
  have e2 := (p (k + 1)).fst_le ((q k).fst F)
  have e3 := (q (k + 1)).fst_lo (c := T) hT
  simp only [Nat.add_sub_cancel] at hlat
  omega

/-! ## H_GFLUSH is needed (N = 2)

Gate high, low on `[10, 12)`, high again. `uor` and `g[0]` 3 ticks each, the
chain and tap pins of `g[1]` 1 tick. `L 2 = 7`, `V 2 = 11`: the claim of
`no_early` would be "high from 11 on only at or after 19". But the dip has not
yet reached `s 1` when the rise reaches the tap, so `z = s 2` is high at 13.
H_GFLUSH 1 fails: `(p 1).fst (V 1) = 17 > 13 = (q 1).fst 12`. -/

def gD : Trace := fun u => !decide (10 ≤ u ∧ u < 12)
def sD : Nat → Trace
  | 0 => fun t => gD (t - 3)
  | 1 => fun t => gD (t - 6)
  | i + 2 => fun t => sD (i + 1) (t - 1) && gD (t - 1)

/-- The run is a behaviour of the per-pin model. -/
theorem gD_gated : Gated gD sD (Ret.shift 3) (Ret.shift 3) (fun _ => Ret.shift 1)
    (fun _ => Ret.shift 1) where
  h0 _ := rfl
  h1 t := by show gD (t - 6) = gD (t - 3 - 3); rw [Nat.sub_sub]
  hs i hi t := by
    rcases i with _ | i
    · omega
    · rfl

/-- **Without H_GFLUSH the matched delay is lost.** The gate is low on
`[10, 12)`; H_GFLUSH 1 fails; and `z = s 2` is high at 13, after `V 2 = 11`
but before `12 + L 2 = 19`. -/
theorem flush_needed :
    (∀ u, 10 ≤ u → u < 12 → gD u = false) ∧
    ¬ ((Ret.shift 1).fst (V (Ret.shift 3) (Ret.shift 3) (fun _ => Ret.shift 1) 10 1) ≤
        (Ret.shift 1).fst 12) ∧
    V (Ret.shift 3) (Ret.shift 3) (fun _ => Ret.shift 1) 10 2 = 11 ∧
    L (Ret.shift 3) (Ret.shift 3) (fun _ => Ret.shift 1) 2 = 7 ∧
    sD 2 13 = true ∧ 13 < 12 + 7 := by
  have a1 := Ret.fst_shift 3 10 (by omega)
  have a2 := Ret.fst_shift 3 13 (by omega)
  have a3 := Ret.fst_shift 1 16 (by omega)
  have a4 := Ret.fst_shift 1 12 (by omega)
  have a5 := Ret.fst_shift 1 10 (by omega)
  refine ⟨?_, ?_, ?_, rfl, by decide, by omega⟩
  · intro u h1 h2; simp [gD]; omega
  · show ¬ ((Ret.shift 1).fst ((Ret.shift 3).fst ((Ret.shift 3).fst 10)) ≤ (Ret.shift 1).fst 12)
    rw [a1, a2, a3, a4]; omega
  · show (Ret.shift 1).fst 10 = 11
    rw [a5]

/-- **Non-vacuity of `no_early`.** The same line with a gate low on `[10, 30)`
meets H_GFLUSH 1 (`17 ≤ 31`), so `no_early` applies to it with `N = 2`: from
`V 2 = 11` on, `z` is high only from `30 + 7`. -/
def gE : Trace := fun u => !decide (10 ≤ u ∧ u < 30)
def sE : Nat → Trace
  | 0 => fun t => gE (t - 3)
  | 1 => fun t => gE (t - 6)
  | i + 2 => fun t => sE (i + 1) (t - 1) && gE (t - 1)

theorem gE_gated : Gated gE sE (Ret.shift 3) (Ret.shift 3) (fun _ => Ret.shift 1)
    (fun _ => Ret.shift 1) where
  h0 _ := rfl
  h1 t := by show gE (t - 6) = gE (t - 3 - 3); rw [Nat.sub_sub]
  hs i hi t := by
    rcases i with _ | i
    · omega
    · rfl

theorem long_dip_no_early :
    ∀ t, V (Ret.shift 3) (Ret.shift 3) (fun _ => Ret.shift 1) 10 2 ≤ t → sE 2 t = true →
      30 + L (Ret.shift 3) (Ret.shift 3) (fun _ => Ret.shift 1) 2 ≤ t := by
  have a1 := Ret.fst_shift 3 10 (by omega)
  have a2 := Ret.fst_shift 3 13 (by omega)
  have a3 := Ret.fst_shift 1 16 (by omega)
  have a4 := Ret.fst_shift 1 30 (by omega)
  refine no_early gE_gated 2 10 30 (by omega) (fun u h1 h2 => by simp [gE]; omega) ?_ 2 (Nat.le_refl _)
  intro i h1 h2
  obtain rfl : i = 1 := by omega
  show (Ret.shift 1).fst ((Ret.shift 3).fst ((Ret.shift 3).fst 10)) ≤ (Ret.shift 1).fst 30
  rw [a1, a2, a3, a4]; omega

/-- ... and it is not vacuous there either: `z` does rise, at `30 + 7`. -/
theorem long_dip_rises : sE 2 37 = true ∧ sE 2 36 = false := by decide

end Formal.Cells.GcdCells
