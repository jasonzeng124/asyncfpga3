import Formal.Cells.ArbNoWithdraw

/-!
# Probe Bset: the sharp H_SETTLED of the held `bd_arbiter`, its latency table on gcd_hw, and
its discharge for link-driven clients

Shard B, 2026-10-29. Note: `formal/notes/B-arb-settled.md`. Needs Mathlib (through
`ArbNoWithdraw` → `OnGcdArbKappaSrv`). Follows `ArbNoWithdraw` (probe Bbare,
`notes/B-arb-no-withdraw.md`), which it imports read-only.

7h/7j (`ArbHeldTimed`, `ArbHeldTimed2`) assume H_SETTLED `ta + wa0s + qf ≤ t0 ∧ ta + wa0k + ckf ≤ t0`:
A0's rise has reached ustate's q OUTPUT (and ua_k's view) before client k drops r_k AT ITS
DRIVER. On gcd_hw's routed arcs Bbare found it needs a client latency up to 1.59 ns.

## Results

1. **The sharp condition** (`ScnP` / `Scn2P`, field `H_PIN`): `ta + wa0s ≤ t0 + wr_ks`, i.e. A0's
   rise reaches ustate's hold pin I4 no later than r_k's fall reaches ustate's request pin.
   The second conjunct of H_SETTLED is dropped: it is not used by any exclusion theorem.
   * `q_hi` / `q_lo2` re-proved on the real INIT (`FS_r1q`, `FS_r2q`: with the releasing
     request still high at its pin, q's value is its own feedback whatever A0 is).
   * The whole 7h and 7j exclusion chain is re-proved verbatim on `ScnP` / `Scn2P`:
     `rt1_exclusion`, `rt2_exclusion_arcs` (7h), `rt1_exclusion2`, `rt2_exclusion2_arcs` (7j).
   * It generalizes 7h/7j: `ofScn`, `ofScn2` (H_SETTLED ⇒ H_PIN). Strictly:
     `strict_witness` (runs of 7j's `D0` with A0 rising 50 ps before the release meet `ScnP` /
     `Scn2P` while H_SETTLED fails; the exclusion theorems apply to them).
   * Exact: `q_glitch` (7h; when `t0 + wr1s + qf < ta + wa0s + qr` and A0 was still low,
     q FALLS at `t0 + wr1s + qf`, before `QB`) and `q_glitch2` (7j; when `t0 + wr2s < ta + wa0s`,
     q RISES at `t0 + wr2s + qr`, before `QBb`). So H_PIN is exact for `q_lo2` on every record,
     and for `q_hi` when `qr = qf` (every `Real7` record).
2. **From causality** (`settledP1_of_causal`, `settledP2_of_causal`): with Bbare's `Caus_k`
   (client latency `L` from A_k's rise at ua_k's output to r_k's fall at its driver), H_PIN
   holds as soon as `wa0s ≤ wa0k + ckr + L + wr_ks`. Non-vacuous on `W1c` at `L = 0`.
3. **The table** (`setTbl2`, forms `fsh1`/`fsh2`: `ΣP ≤ ΣQ + L` with `P = [dS2|dS1, es, ps]`,
   `Q = [d12, ek, pk, ack, rsk]`): `settledP_safe` (every realization at κ ≤ κS2, all 72
   clients), `setTbl2_max` (502.361 ps, seed 2 merge12.uarb2 client 2), `setTbl2_pos` (21 of
   72 clients need `L > 0`), and `settledP_tight`: for each of those 21, latency `L − 10 fs`
   FAILS on a realization at every κ ≥ κS2 (`tightRows`), so the table is exact to 10 fs and
   `L = 0` fails for exactly those 21 (`settledP_L0_fails`).
4. **D2 with the sharp condition** (`design_gate_held_sharp`, `design_gate_held_sharp_causal`):
   OnGcdArbKappaSrv's four handover conclusions on `ScnP`/`Scn2P`, and with H_PIN derived from
   `Caus_k` at latency `setTbl2` plus H_RK_ROUTE (`rs_k ≤ wr_ks`: the r_k route to ustate is at
   least its extracted suffix).
5. **Link clients, discharged.** `LinkRel.release`: under LinkExact's exact conjunction the
   link controller cannot drop its request before `Rb + Blo`; with H_ACK_RB (`Rb` = A_k's
   rise) and H_ACK_READ (`x ≤ Blo`, `x` the controller's realised O6 arc: the routed wire and
   site pin in front of it are ≥ 0 and not credited), `Caus_k` holds at latency `x`
   (`link_caus1`, `link_caus2`). `link_pin1`/`link_pin2`: on 18 of gcd_hw's 20 link-client
   instances (`linkTbl1`, `linkTbl2`), H_PIN follows for every realization at κ ≤ κS2 in which
   the controller's O6 arc is at the die's shared corner (H_SAME_CORNER), with NO latency
   hypothesis; `design_link_discharged1`/`design_link_discharged2` give the handover
   conclusions. `link_short`: on the remaining two (seed 3 and seed 4 merge2.uarb1 client 2)
   the O6 arc alone does not suffice at κS2 (a realization with zero ack route violates the
   form); the missing arcs are the routed wire + site pin from ua2's O6 to the controller's I1.
   Non-vacuity: `link_caus1_nonvacuous` (LinkExact's `P0` behaviour composed with `W1s`, a
   time-shifted `W1c`).

## NOT covered
* A windowed `Scn` (probe Barb2); the separate idealized/causal runs of Bbare remain.
* The routed ack wire + site pin of every link controller (not extracted), so 2 of the 20
  link-client instances stay conditional; whether the controller is placed as a 6LUT
  (H_LUT6_O6, named) is not read from the placement.
* Steer and R0 clients: their release loops (join C-element, `uack` OR) have no extracted arcs.
* 7h direction with `qr < qf`: H_PIN is proved sufficient, `q_glitch` shows only the weaker
  `ta + wa0s + qr ≤ t0 + wr1s + qf` necessary; the gap (`qf − qr`, zero on every `Real7`
  record) is not decided.
* Whether a violated H_PIN breaks EXCLUSION (the counter-traces stop at q's early edge).
* Kleene X, metastability, κ itself.

## Assumed (named)
7h's gate relations `Run` (real INITs, rise-fast pure-delay OR channel, a route per pin) and
`Server` (H_SERVER_MIN); the idealized scenario fields of `Scn`/`Scn2` except H_SETTLED;
H_PIN (sections 1-2, 6), or Bbare's `Caus_k` (H_A0_LOW_BEFORE, H_CLIENT_LAT) plus H_RK_ROUTE
(sections 4, 6); A's corner model (H_SHARED_CORNER, H_SCATTER κ, lit reading) over Bar's
UNTRUSTED extraction, `Real7`/`Real1`/`Real2`, H_SERVER_GRAPH (as OnGcdArbKappaSrv);
for section 7 also LinkExact's `Wf`/`Conj`/`Beh` (box, environment, controller and latch
relations), H_ACK_RB, H_ACK_READ, H_SAME_CORNER, H_LUT6_O6, and the netlist reading of which
cell drives each r_k (Bbare's `drv2.py`, identical on the four seeds).
-/

namespace Formal.Cells.ArbSettled

open Formal.Cells

/-! ## 1. The sharp condition, 7h direction (client 1 releases) -/

namespace H
open Formal.Cells.ArbHeldTimed (Dl Sigs Run FS FR FG1 FG2 CE FS_eq FR_eq FG1_eq FG2_eq CE_eq
  FS_hold FS_rel FR_r1r2 FR_lo int_ind and_dec_false TR QB G1 G2 RR RT1 T1 T2 RT2 A0Fork)

/-- With r1 and q high at ustate's pins, q stays high whatever r2 and A0 are (real INIT). -/
theorem FS_r1q : ∀ r2 a0 : Bool, FS true r2 true a0 = true := by decide

/-- 7h's handover scenario with H_SETTLED replaced by **H_PIN**: A0's rise reaches ustate's I4
no later than r1's fall reaches ustate's I0 (both at the pins). -/
structure ScnP (D : Dl) (s : Sigs) (t0 ta TA TA2 Hz : Int) : Prop where
  H_ORDER : ta ≤ t0 ∧ ta < TA ∧ t0 < TA ∧ TA < TA2 ∧ TA2 < Hz
  H_r1 : ∀ t, t < Hz → s.r1 t = decide (t < t0)
  H_r2 : ∀ t, t < Hz → s.r2 t = true
  H_A0 : ∀ t, ta ≤ t → t < Hz → s.A0 t = (decide (t < TA) || decide (TA2 ≤ t))
  H_A0_prev : s.A0 (ta - 1) = false
  H_q_init : ∀ t, t < t0 → s.q t = true
  H_A1_init : ∀ t, t < t0 → s.A1 t = true
  H_A2_init : ∀ t, t < t0 → s.A2 t = false
  /-- **H_PIN** (rise-side twin of rule J): `ta + wa0s ≤ t0 + wr1s`. -/
  H_PIN : ta + D.wa0s ≤ t0 + D.wr1s

/-- 7h's H_SETTLED implies H_PIN: the sharp scenario generalizes 7h's. -/
theorem ofScn {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz : Int}
    (S : ArbHeldTimed.Scn D s t0 ta TA TA2 Hz) : ScnP D s t0 ta TA TA2 Hz := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := S.H_SETTLED
  exact ⟨S.H_ORDER, S.H_r1, S.H_r2, S.H_A0, S.H_A0_prev, S.H_q_init, S.H_A1_init, S.H_A2_init,
    by omega⟩

section
variable {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz : Int}

theorem A0_hi1 (S : ScnP D s t0 ta TA TA2 Hz) (t : Int) (h1 : ta ≤ t) (h2 : t < TA) :
    s.A0 t = true := by
  have := S.H_ORDER
  rw [S.H_A0 t h1 (by omega)]; simp; omega

theorem A0_lo (S : ScnP D s t0 ta TA TA2 Hz) (t : Int) (h1 : TA ≤ t) (h2 : t < TA2) :
    s.A0 t = false := by
  have := S.H_ORDER
  rw [S.H_A0 t (by omega) (by omega)]; simp; omega

theorem A0_hi2 (S : ScnP D s t0 ta TA TA2 Hz) (t : Int) (h1 : TA2 ≤ t) (h2 : t < Hz) :
    s.A0 t = true := by
  have := S.H_ORDER
  rw [S.H_A0 t (by omega) h2]; simp; omega

theorem r1_lo (S : ScnP D s t0 ta TA TA2 Hz) (t : Int) (h1 : t0 ≤ t) (h2 : t < Hz) :
    s.r1 t = false := by
  rw [S.H_r1 t h2]; simp; omega

theorem r1_hi (S : ScnP D s t0 ta TA TA2 Hz) (t : Int) (h1 : t < t0) :
    s.r1 t = true := by
  have := S.H_ORDER
  rw [S.H_r1 t (by omega)]; simp; omega

theorem R0_hi (R : Run D s) (S : ScnP D s t0 ta TA TA2 Hz) (t : Int) (h : t < TR D t0)
    (hz : t < Hz) : s.R0 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  unfold TR at h
  rw [R.H_R0 t, r1_hi S (t - D.wr1s - D.Rf1) (by omega), S.H_r2 (t - D.wr2s - D.Rf2) (by omega),
    FR_r1r2]
  simp

theorem TA_ge (R : Run D s) (S : ScnP D s t0 ta TA TA2 Hz) : TR D t0 + D.smin ≤ TA := by
  have ho := S.H_ORDER
  have := D.H_NONNEG
  have e1 : s.A0 TA = false := A0_lo S TA (by omega) (by omega)
  have e0 : s.A0 (TA - 1) = true := A0_hi1 S _ (by omega) (by omega)
  obtain ⟨u, hu, hR, hv⟩ := R.H_SRV TA (by rw [e1, e0]; simp)
  rw [e1] at hR
  have hu1 : ta ≤ u := by
    by_cases hc : ta ≤ u
    · exact hc
    · have := hv (ta - 1) (by omega) (by omega)
      rw [S.H_A0_prev, e0] at this; exact absurd this (by simp)
  by_cases hc : TR D t0 + D.smin ≤ TA
  · exact hc
  · have := R0_hi R S u (by omega) (by omega)
    rw [hR] at this; exact absurd this (by simp)

/-- **q is high until `QB`, under H_PIN** (re-proof of 7h's `q_hi`, real INIT). At each
`t ≥ t0`, ustate's slow (`qf`) view has either r1 still high at I0 (then q holds by `FS_r1q`)
or, by H_PIN, A0's rise already at I4 (then q holds by `FS_hold`). -/
theorem q_hi (R : Run D s) (S : ScnP D s t0 ta TA TA2 Hz) :
    ∀ t, t < QB D TA → s.q t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have hp := S.H_PIN; have := S.H_ORDER
  refine int_ind (fun t => t < QB D TA → s.q t = true) t0
    (fun t ht _ => S.H_q_init t ht) ?_
  intro t ht ih hb
  unfold QB at hb
  have hfb : s.q (t - D.wfb - D.qf) = true := ih _ (by omega) (by unfold QB; omega)
  have hv : FS (s.r1 (t - D.wr1s - D.qf)) (s.r2 (t - D.wr2s - D.qf)) (s.q (t - D.wfb - D.qf))
      (s.A0 (t - D.wa0s - D.qf)) = true := by
    rw [hfb]
    by_cases hc : t - D.wr1s - D.qf < t0
    · rw [r1_hi S _ hc, FS_r1q]
    · rw [A0_hi1 S _ (by omega) (by omega), FS_hold]
  rw [R.H_q t, hv, Bool.or_true]

theorem R0_lo (R : Run D s) (S : ScnP D s t0 ta TA TA2 Hz) (t : Int)
    (h1 : TR D t0 ≤ t) (h2 : t < RR D TA) (hz : t < Hz) : s.R0 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  unfold TR at h1; unfold RR at h2
  rw [R.H_R0 t, r1_lo S (t - D.wr1s - D.Rr1) (by omega) (by omega),
    r1_lo S (t - D.wr1s - D.Rf1) (by omega) (by omega),
    q_hi R S _ (by omega), q_hi R S (t - D.wfb - D.Rfq) (by omega), FR_lo, FR_lo]
  simp

theorem TA2_ge (R : Run D s) (S : ScnP D s t0 ta TA TA2 Hz) : RR D TA + D.smin ≤ TA2 := by
  have ho := S.H_ORDER
  have := D.H_NONNEG
  have hTA := TA_ge R S
  have e1 : s.A0 TA2 = true := A0_hi2 S TA2 (by omega) (by omega)
  have e0 : s.A0 (TA2 - 1) = false := A0_lo S _ (by omega) (by omega)
  obtain ⟨u, hu, hR, hv⟩ := R.H_SRV TA2 (by rw [e1, e0]; simp)
  rw [e1] at hR
  have hu1 : TA ≤ u := by
    by_cases hc : TA ≤ u
    · exact hc
    · have := hv (TA - 1) (by omega) (by omega)
      rw [A0_hi1 S (TA - 1) (by omega) (by omega), e0] at this; exact absurd this (by simp)
  by_cases hc : RR D TA + D.smin ≤ TA2
  · exact hc
  · unfold TR at hTA
    have := R0_lo R S u (by unfold TR; omega) (by omega) (by omega)
    rw [hR] at this; exact absurd this (by simp)

theorem q_lo (R : Run D s) (S : ScnP D s t0 ta TA TA2 Hz) :
    ∀ t, QB D TA ≤ t → t < Hz → s.q t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.H_ORDER
  have hTA := TA_ge R S
  have hTA2 := TA2_ge R S
  unfold TR at hTA; unfold RR QB at hTA2
  refine int_ind (fun t => QB D TA ≤ t → t < Hz → s.q t = false) (QB D TA)
    (fun t ht h _ => absurd h (by omega)) ?_
  intro t _ ih hb hz
  unfold QB at hb
  have view : ∀ d, D.qr ≤ d → d ≤ D.qf →
      FS (s.r1 (t - D.wr1s - d)) (s.r2 (t - D.wr2s - d)) (s.q (t - D.wfb - d))
        (s.A0 (t - D.wa0s - d)) = false := by
    intro d hd1 hd2
    rw [r1_lo S _ (by omega) (by omega), S.H_r2 _ (by omega)]
    by_cases hc : t - D.wa0s - d < TA2
    · rw [A0_lo S _ (by omega) hc, FS_rel]
    · rw [A0_hi2 S _ (by omega) (by omega), FS_hold]
      exact ih _ (by omega) (by unfold QB; omega) (by omega)
  rw [R.H_q t, view D.qr (by omega) (by omega), view D.qf (by omega) (by omega)]
  rfl

theorem q_eq (R : Run D s) (S : ScnP D s t0 ta TA TA2 Hz) (t : Int) (hz : t < Hz) :
    s.q t = decide (t < QB D TA) := by
  by_cases h : t < QB D TA
  · rw [q_hi R S t h]; simp [h]
  · rw [q_lo R S t (by omega) hz]; simp [h]

theorem g2_eq (R : Run D s) (S : ScnP D s t0 ta TA TA2 Hz) (t : Int) (hz : t < Hz) :
    s.g2 t = decide (G2 D TA ≤ t) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  rw [R.H_g2 t, FG2_eq, FG2_eq, S.H_r2 _ (by omega), S.H_r2 _ (by omega),
    q_eq R S _ (by omega), q_eq R S (t - D.wq - D.g2f) (by omega)]
  unfold G2
  by_cases h : QB D TA + D.wq + D.g2r ≤ t
  · have : ¬ (t - D.wq - D.g2r < QB D TA) := by omega
    simp [h, this]
  · have e1 : t - D.wq - D.g2r < QB D TA := by omega
    have e2 : t - D.wq - D.g2f < QB D TA := by omega
    simp [h, e1, e2]

theorem g1_eq (R : Run D s) (S : ScnP D s t0 ta TA TA2 Hz) (t : Int) (hz : t < Hz) :
    s.g1 t = decide (t < G1 D t0 TA) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  rw [R.H_g1 t, FG1_eq, FG1_eq, S.H_r1 _ (by omega), S.H_r1 (t - D.wr1g - D.g1f1) (by omega),
    q_eq R S _ (by omega), q_eq R S (t - D.wq - D.g1fq) (by omega)]
  unfold G1
  by_cases h : t < min (t0 + D.wr1g + D.g1f1) (QB D TA + D.wq + D.g1fq)
  · have e1 : t - D.wr1g - D.g1f1 < t0 := by omega
    have e2 : t - D.wq - D.g1fq < QB D TA := by omega
    simp [h, e1, e2]
  · rw [and_dec_false (by omega), and_dec_false (by omega)]
    simp [h]

theorem overlap_exact (R : Run D s) (S : ScnP D s t0 ta TA TA2 Hz) (t : Int) (hz : t < Hz) :
    (s.g1 t && s.g2 t) = true ↔ (G2 D TA ≤ t ∧ t < G1 D t0 TA) := by
  rw [g1_eq R S t hz, g2_eq R S t hz]
  simp; omega

/-- **RT1 ⇒ grant exclusion under H_PIN** (7h's `rt1_exclusion` on `ScnP`). -/
theorem rt1_exclusion (R : Run D s) (S : ScnP D s t0 ta TA TA2 Hz) (H_RT1 : RT1 D) :
    ∀ t, t < Hz → (s.g1 t && s.g2 t) = false := by
  have hTA := TA_ge R S
  intro t hz
  cases hc : (s.g1 t && s.g2 t)
  · rfl
  · have := (overlap_exact R S t hz).1 hc
    unfold G1 G2 QB at this; unfold TR at hTA; unfold RT1 at H_RT1
    omega

theorem A1_low_after (R : Run D s) (S : ScnP D s t0 ta TA TA2 Hz)
    (H_RT2a : T1 D t0 TA + D.wfa1 ≤ TA2 + D.wa01) :
    ∀ t, T1 D t0 TA ≤ t → t < Hz → s.A1 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.H_ORDER
  refine int_ind (fun t => T1 D t0 TA ≤ t → t < Hz → s.A1 t = false) (T1 D t0 TA)
    (fun t ht h _ => absurd h (by omega)) ?_
  intro t _ ih hb hz
  unfold T1 at hb H_RT2a
  have view : ∀ d, D.c1r ≤ d → d ≤ D.c1f →
      CE (s.g1 (t - D.wg1 - d)) (s.A0 (t - D.wa01 - d)) (s.A1 (t - D.wfa1 - d)) = false := by
    intro d hd1 hd2
    rw [g1_eq R S _ (by omega), CE_eq]
    have : ¬ (t - D.wg1 - d < G1 D t0 TA) := by omega
    simp only [this, decide_false, Bool.false_and, Bool.false_or]
    by_cases hc : t - D.wa01 - d < TA2
    · rw [A0_lo S _ (by omega) hc]; simp
    · rw [ih _ (by omega) (by unfold T1; omega) (by omega)]; simp
  rw [R.H_A1 t, view D.c1r (by omega) (by omega), view D.c1f (by omega) (by omega)]
  rfl

theorem A2_low_before (R : Run D s) (S : ScnP D s t0 ta TA TA2 Hz)
    (H_A0_FORK : TA + D.wa02 ≤ G2 D TA + D.wg2) :
    ∀ t, t < T2 D TA2 → t < Hz → s.A2 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.H_ORDER
  refine int_ind (fun t => t < T2 D TA2 → t < Hz → s.A2 t = false) t0
    (fun t ht _ _ => S.H_A2_init t ht) ?_
  intro t _ ih hb hz
  unfold T2 at hb
  have view : ∀ d, D.c2r ≤ d → d ≤ D.c2f →
      CE (s.g2 (t - D.wg2 - d)) (s.A0 (t - D.wa02 - d)) (s.A2 (t - D.wfa2 - d)) = false := by
    intro d hd1 hd2
    rw [ih _ (by omega) (by unfold T2; omega) (by omega), CE_eq, g2_eq R S _ (by omega)]
    by_cases hc : t - D.wa02 - d < TA
    · have : ¬ (G2 D TA ≤ t - D.wg2 - d) := by omega
      simp [this]
    · rw [A0_lo S _ (by omega) (by omega)]; simp
  rw [R.H_A2 t, view D.c2r (by omega) (by omega), view D.c2f (by omega) (by omega)]
  rfl

theorem rt2_exclusion (R : Run D s) (S : ScnP D s t0 ta TA TA2 Hz)
    (H_RT2a : T1 D t0 TA + D.wfa1 ≤ TA2 + D.wa01)
    (H_RT2b : T1 D t0 TA ≤ T2 D TA2)
    (H_A0_FORK : TA + D.wa02 ≤ G2 D TA + D.wg2) :
    ∀ t, t < Hz → (s.A1 t && s.A2 t) = false := by
  intro t hz
  by_cases h : T1 D t0 TA ≤ t
  · rw [A1_low_after R S H_RT2a t h hz]; rfl
  · rw [A2_low_before R S H_A0_FORK t (by omega) hz]; simp

/-- **RT2 + A0Fork ⇒ ack exclusion under H_PIN** (7h's `rt2_exclusion_arcs` on `ScnP`). -/
theorem rt2_exclusion_arcs (R : Run D s) (S : ScnP D s t0 ta TA TA2 Hz)
    (H_RT2 : RT2 D) (H_fork : A0Fork D) :
    ∀ t, t < Hz → (s.A1 t && s.A2 t) = false := by
  have := D.H_NONNEG
  have hTA := TA_ge R S
  have hTA2 := TA2_ge R S
  obtain ⟨h1, h2, h3, h4⟩ := H_RT2
  unfold TR at hTA; unfold RR QB at hTA2; unfold A0Fork at H_fork
  apply rt2_exclusion R S
  · unfold T1 G1 QB; omega
  · unfold T1 T2 G1 QB; omega
  · unfold G2 QB; omega

end

/-- **Exactness, 7h direction (counter-trace).** If r1's fall reaches ustate (slow view) before
A0's rise does (fast view), `t0 + wr1s + qf < ta + wa0s + qr`, and A0 was still low at ustate's
views (H_A0_LOW_BEFORE on `[t0 + wr1s − wa0s, ta)`), then in every run q FALLS at
`t0 + wr1s + qf`, which is before `QB`: the arbiter drops client 1's state while the server
still serves client 1. With `qr = qf` (every `Real7` record) the failing condition is exactly
`¬ H_PIN`. -/
theorem q_glitch {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz : Int} (R : Run D s)
    (S : ArbNoWithdraw.ScnNS D s t0 ta TA TA2 Hz)
    (H_FAIL : t0 + D.wr1s + D.qf < ta + D.wa0s + D.qr)
    (H_A0_LOW : ∀ u, t0 + D.wr1s - D.wa0s ≤ u → u < ta → s.A0 u = false)
    (hz : t0 + D.wr1s + D.qf < Hz) :
    s.q (t0 + D.wr1s + D.qf) = false ∧ t0 + D.wr1s + D.qf < QB D TA := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := S.H_ORDER
  refine ⟨?_, by unfold QB; omega⟩
  have view : ∀ d, D.qr ≤ d → d ≤ D.qf →
      FS (s.r1 (t0 + D.wr1s + D.qf - D.wr1s - d)) (s.r2 (t0 + D.wr1s + D.qf - D.wr2s - d))
        (s.q (t0 + D.wr1s + D.qf - D.wfb - d)) (s.A0 (t0 + D.wr1s + D.qf - D.wa0s - d)) =
        false := by
    intro d hd1 hd2
    rw [S.H_r1 _ (by omega), S.H_r2 _ (by omega), H_A0_LOW _ (by omega) (by omega)]
    have : ¬ (t0 + D.wr1s + D.qf - D.wr1s - d < t0) := by omega
    simp only [this, decide_false]
    exact FS_rel _
  rw [R.H_q, view D.qr (by omega) (by omega), view D.qf (by omega) (by omega)]
  rfl

end H

/-! ## 2. The sharp condition, 7j direction (client 2 releases) -/

namespace J
open Formal.Cells.ArbHeldTimed (Dl Sigs Run FS FR FG1 FG2 CE FS_eq FR_eq FG1_eq FG2_eq CE_eq
  FS_hold FS_rel int_ind and_dec_false)
open Formal.Cells.ArbHeldTimed2 (FS_bool FS_set FR_r1 FG1_r1 TRb QBb RRb G1b G2b RT1b T1b T2b
  RT2b A0Fork2)

/-- With r2 high and q low at ustate's pins, q stays low whatever r1 and A0 are (real INIT). -/
theorem FS_r2q : ∀ r1 a0 : Bool, FS r1 true false a0 = false := by decide

/-- 7j's mirror scenario with H_SETTLED replaced by **H_PIN**: `ta + wa0s ≤ t0 + wr2s`. -/
structure Scn2P (D : Dl) (s : Sigs) (t0 ta TA TA2 Hz : Int) : Prop where
  H_ORDER : ta ≤ t0 ∧ ta < TA ∧ t0 < TA ∧ TA < TA2 ∧ TA2 < Hz
  H_r1 : ∀ t, t < Hz → s.r1 t = true
  H_r2 : ∀ t, t < Hz → s.r2 t = decide (t < t0)
  H_A0 : ∀ t, ta ≤ t → t < Hz → s.A0 t = (decide (t < TA) || decide (TA2 ≤ t))
  H_A0_prev : s.A0 (ta - 1) = false
  H_q_init : ∀ t, t < t0 → s.q t = false
  H_A1_init : ∀ t, t < t0 → s.A1 t = false
  H_A2_init : ∀ t, t < t0 → s.A2 t = true
  /-- **H_PIN** (mirror): `ta + wa0s ≤ t0 + wr2s`. -/
  H_PIN : ta + D.wa0s ≤ t0 + D.wr2s

theorem ofScn2 {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz : Int}
    (S : ArbHeldTimed2.Scn2 D s t0 ta TA TA2 Hz) : Scn2P D s t0 ta TA TA2 Hz := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := S.H_SETTLED
  exact ⟨S.H_ORDER, S.H_r1, S.H_r2, S.H_A0, S.H_A0_prev, S.H_q_init, S.H_A1_init, S.H_A2_init,
    by omega⟩

section
variable {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz : Int}

theorem A0_hi1b (S : Scn2P D s t0 ta TA TA2 Hz) (t : Int) (h1 : ta ≤ t) (h2 : t < TA) :
    s.A0 t = true := by
  have := S.H_ORDER
  rw [S.H_A0 t h1 (by omega)]; simp; omega

theorem A0_lob (S : Scn2P D s t0 ta TA TA2 Hz) (t : Int) (h1 : TA ≤ t) (h2 : t < TA2) :
    s.A0 t = false := by
  have := S.H_ORDER
  rw [S.H_A0 t (by omega) (by omega)]; simp; omega

theorem A0_hi2b (S : Scn2P D s t0 ta TA TA2 Hz) (t : Int) (h1 : TA2 ≤ t) (h2 : t < Hz) :
    s.A0 t = true := by
  have := S.H_ORDER
  rw [S.H_A0 t (by omega) h2]; simp; omega

theorem r2_lo (S : Scn2P D s t0 ta TA TA2 Hz) (t : Int) (h1 : t0 ≤ t) (h2 : t < Hz) :
    s.r2 t = false := by
  rw [S.H_r2 t h2]; simp; omega

theorem r2_hi (S : Scn2P D s t0 ta TA TA2 Hz) (t : Int) (h1 : t < t0) :
    s.r2 t = true := by
  have := S.H_ORDER
  rw [S.H_r2 t (by omega)]; simp; omega

theorem R0_hi2 (R : Run D s) (S : Scn2P D s t0 ta TA TA2 Hz) (t : Int) (h : t < TRb D t0)
    (hz : t < Hz) : s.R0 t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  unfold TRb at h
  rw [R.H_R0 t, S.H_r1 (t - D.wr1s - D.Rf1) (by omega), r2_hi S (t - D.wr2s - D.Rf2) (by omega),
    FR_r1]
  simp

theorem TA_ge2 (R : Run D s) (S : Scn2P D s t0 ta TA TA2 Hz) : TRb D t0 + D.smin ≤ TA := by
  have ho := S.H_ORDER
  have := D.H_NONNEG
  have e1 : s.A0 TA = false := A0_lob S TA (by omega) (by omega)
  have e0 : s.A0 (TA - 1) = true := A0_hi1b S _ (by omega) (by omega)
  obtain ⟨u, hu, hR, hv⟩ := R.H_SRV TA (by rw [e1, e0]; simp)
  rw [e1] at hR
  have hu1 : ta ≤ u := by
    by_cases hc : ta ≤ u
    · exact hc
    · have := hv (ta - 1) (by omega) (by omega)
      rw [S.H_A0_prev, e0] at this; exact absurd this (by simp)
  by_cases hc : TRb D t0 + D.smin ≤ TA
  · exact hc
  · have := R0_hi2 R S u (by omega) (by omega)
    rw [hR] at this; exact absurd this (by simp)

/-- **q is low until `QBb`, under H_PIN** (re-proof of 7j's `q_lo2`, real INIT). In each of
ustate's two views, r2 is either still high at I1 (then q holds 0 by `FS_r2q`) or, by H_PIN,
A0's rise is already at I4 (then q holds by `FS_hold`). -/
theorem q_lo2 (R : Run D s) (S : Scn2P D s t0 ta TA TA2 Hz) :
    ∀ t, t < QBb D TA → s.q t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have hp := S.H_PIN; have := S.H_ORDER
  refine int_ind (fun t => t < QBb D TA → s.q t = false) t0
    (fun t ht _ => S.H_q_init t ht) ?_
  intro t ht ih hb
  unfold QBb at hb
  have view : ∀ d, D.qr ≤ d → d ≤ D.qf →
      FS (s.r1 (t - D.wr1s - d)) (s.r2 (t - D.wr2s - d)) (s.q (t - D.wfb - d))
        (s.A0 (t - D.wa0s - d)) = false := by
    intro d hd1 hd2
    rw [ih (t - D.wfb - d) (by omega) (by unfold QBb; omega)]
    by_cases hc : t - D.wr2s - d < t0
    · rw [r2_hi S _ hc, FS_r2q]
    · rw [A0_hi1b S _ (by omega) (by omega), FS_hold]
  rw [R.H_q t, view D.qr (by omega) (by omega), view D.qf (by omega) (by omega)]
  rfl

theorem R0_lo2 (R : Run D s) (S : Scn2P D s t0 ta TA TA2 Hz) (t : Int)
    (h1 : TRb D t0 ≤ t) (h2 : t < RRb D TA) (hz : t < Hz) : s.R0 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  unfold TRb at h1; unfold RRb at h2
  rw [R.H_R0 t, S.H_r1 (t - D.wr1s - D.Rr1) (by omega), S.H_r1 (t - D.wr1s - D.Rf1) (by omega),
    r2_lo S (t - D.wr2s - D.Rr2) (by omega) (by omega),
    r2_lo S (t - D.wr2s - D.Rf2) (by omega) (by omega),
    q_lo2 R S _ (by omega), q_lo2 R S (t - D.wfb - D.Rfq) (by omega), FR_r1]
  rfl

theorem TA2_ge2 (R : Run D s) (S : Scn2P D s t0 ta TA TA2 Hz) : RRb D TA + D.smin ≤ TA2 := by
  have ho := S.H_ORDER
  have := D.H_NONNEG
  have hTA := TA_ge2 R S
  have e1 : s.A0 TA2 = true := A0_hi2b S TA2 (by omega) (by omega)
  have e0 : s.A0 (TA2 - 1) = false := A0_lob S _ (by omega) (by omega)
  obtain ⟨u, hu, hR, hv⟩ := R.H_SRV TA2 (by rw [e1, e0]; simp)
  rw [e1] at hR
  have hu1 : TA ≤ u := by
    by_cases hc : TA ≤ u
    · exact hc
    · have := hv (TA - 1) (by omega) (by omega)
      rw [A0_hi1b S (TA - 1) (by omega) (by omega), e0] at this; exact absurd this (by simp)
  by_cases hc : RRb D TA + D.smin ≤ TA2
  · exact hc
  · unfold TRb at hTA
    have := R0_lo2 R S u (by unfold TRb; omega) (by omega) (by omega)
    rw [hR] at this; exact absurd this (by simp)

theorem q_hi2 (R : Run D s) (S : Scn2P D s t0 ta TA TA2 Hz) :
    ∀ t, QBb D TA ≤ t → t < Hz → s.q t = true := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.H_ORDER
  have hTA := TA_ge2 R S
  have hTA2 := TA2_ge2 R S
  unfold TRb at hTA; unfold RRb QBb at hTA2
  refine int_ind (fun t => QBb D TA ≤ t → t < Hz → s.q t = true) (QBb D TA)
    (fun t ht h _ => absurd h (by omega)) ?_
  intro t _ ih hb hz
  unfold QBb at hb
  have view : FS (s.r1 (t - D.wr1s - D.qr)) (s.r2 (t - D.wr2s - D.qr)) (s.q (t - D.wfb - D.qr))
      (s.A0 (t - D.wa0s - D.qr)) = true := by
    rw [S.H_r1 _ (by omega), r2_lo S _ (by omega) (by omega)]
    by_cases hc : t - D.wa0s - D.qr < TA2
    · rw [A0_lob S _ (by omega) hc, FS_set]
    · rw [A0_hi2b S _ (by omega) (by omega), FS_hold]
      exact ih _ (by omega) (by unfold QBb; omega) (by omega)
  rw [R.H_q t, view]
  rfl

theorem q_eq2 (R : Run D s) (S : Scn2P D s t0 ta TA TA2 Hz) (t : Int) (hz : t < Hz) :
    s.q t = decide (QBb D TA ≤ t) := by
  by_cases h : QBb D TA ≤ t
  · rw [q_hi2 R S t h hz]; simp [h]
  · rw [q_lo2 R S t (by omega)]; simp [h]

theorem g1_eq2 (R : Run D s) (S : Scn2P D s t0 ta TA TA2 Hz) (t : Int) (hz : t < Hz) :
    s.g1 t = decide (G1b D TA ≤ t) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  rw [R.H_g1 t, S.H_r1 _ (by omega), S.H_r1 (t - D.wr1g - D.g1f1) (by omega), FG1_r1, FG1_r1,
    q_eq2 R S _ (by omega), q_eq2 R S (t - D.wq - D.g1fq) (by omega)]
  unfold G1b
  by_cases h : QBb D TA + D.wq + D.g1rq ≤ t
  · have : QBb D TA ≤ t - D.wq - D.g1rq := by omega
    simp [h, this]
  · have e1 : ¬ QBb D TA ≤ t - D.wq - D.g1rq := by omega
    have e2 : ¬ QBb D TA ≤ t - D.wq - D.g1fq := by omega
    simp [h, e1, e2]

theorem g2_eq2 (R : Run D s) (S : Scn2P D s t0 ta TA TA2 Hz) (t : Int) (hz : t < Hz) :
    s.g2 t = decide (t < G2b D t0 TA) := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL
  rw [R.H_g2 t, FG2_eq, FG2_eq, S.H_r2 _ (by omega), S.H_r2 (t - D.wr2g - D.g2f) (by omega),
    q_eq2 R S _ (by omega), q_eq2 R S (t - D.wq - D.g2f) (by omega)]
  unfold G2b
  by_cases h : t < min (t0 + D.wr2g) (QBb D TA + D.wq) + D.g2f
  · have e1 : t - D.wr2g - D.g2f < t0 := by omega
    have e2 : ¬ QBb D TA ≤ t - D.wq - D.g2f := by omega
    simp [h, e1, e2]
  · by_cases a : t - D.wr2g - D.g2r < t0 <;> by_cases b : QBb D TA ≤ t - D.wq - D.g2r <;>
    by_cases c : t - D.wr2g - D.g2f < t0 <;> by_cases d : QBb D TA ≤ t - D.wq - D.g2f <;>
    simp [a, b, c, d, h] <;> omega

theorem overlap_exact2 (R : Run D s) (S : Scn2P D s t0 ta TA TA2 Hz) (t : Int) (hz : t < Hz) :
    (s.g1 t && s.g2 t) = true ↔ (G1b D TA ≤ t ∧ t < G2b D t0 TA) := by
  rw [g1_eq2 R S t hz, g2_eq2 R S t hz]
  simp

/-- **RT1b ⇒ grant exclusion under H_PIN** (7j's `rt1_exclusion2` on `Scn2P`). -/
theorem rt1_exclusion2 (R : Run D s) (S : Scn2P D s t0 ta TA TA2 Hz) (H_RT1 : RT1b D) :
    ∀ t, t < Hz → (s.g1 t && s.g2 t) = false := by
  have hTA := TA_ge2 R S
  intro t hz
  cases hc : (s.g1 t && s.g2 t)
  · rfl
  · have := (overlap_exact2 R S t hz).1 hc
    unfold G1b G2b QBb at this; unfold TRb at hTA; unfold RT1b at H_RT1
    omega

theorem A2_low_after2 (R : Run D s) (S : Scn2P D s t0 ta TA TA2 Hz)
    (H_RT2a : T1b D t0 TA + D.wfa2 ≤ TA2 + D.wa02) :
    ∀ t, T1b D t0 TA ≤ t → t < Hz → s.A2 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.H_ORDER
  refine int_ind (fun t => T1b D t0 TA ≤ t → t < Hz → s.A2 t = false) (T1b D t0 TA)
    (fun t ht h _ => absurd h (by omega)) ?_
  intro t _ ih hb hz
  unfold T1b at hb H_RT2a
  have view : ∀ d, D.c2r ≤ d → d ≤ D.c2f →
      CE (s.g2 (t - D.wg2 - d)) (s.A0 (t - D.wa02 - d)) (s.A2 (t - D.wfa2 - d)) = false := by
    intro d hd1 hd2
    rw [g2_eq2 R S _ (by omega), CE_eq]
    have : ¬ (t - D.wg2 - d < G2b D t0 TA) := by omega
    simp only [this, decide_false, Bool.false_and, Bool.false_or]
    by_cases hc : t - D.wa02 - d < TA2
    · rw [A0_lob S _ (by omega) hc]; simp
    · rw [ih _ (by omega) (by unfold T1b; omega) (by omega)]; simp
  rw [R.H_A2 t, view D.c2r (by omega) (by omega), view D.c2f (by omega) (by omega)]
  rfl

theorem A1_low_before2 (R : Run D s) (S : Scn2P D s t0 ta TA TA2 Hz)
    (H_A0_FORK : TA + D.wa01 ≤ G1b D TA + D.wg1) :
    ∀ t, t < T2b D TA2 → t < Hz → s.A1 t = false := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := D.H_LOOP_POS
  have := S.H_ORDER
  refine int_ind (fun t => t < T2b D TA2 → t < Hz → s.A1 t = false) t0
    (fun t ht _ _ => S.H_A1_init t ht) ?_
  intro t _ ih hb hz
  unfold T2b at hb
  have view : ∀ d, D.c1r ≤ d → d ≤ D.c1f →
      CE (s.g1 (t - D.wg1 - d)) (s.A0 (t - D.wa01 - d)) (s.A1 (t - D.wfa1 - d)) = false := by
    intro d hd1 hd2
    rw [ih _ (by omega) (by unfold T2b; omega) (by omega), CE_eq, g1_eq2 R S _ (by omega)]
    by_cases hc : t - D.wa01 - d < TA
    · have : ¬ (G1b D TA ≤ t - D.wg1 - d) := by omega
      simp [this]
    · rw [A0_lob S _ (by omega) (by omega)]; simp
  rw [R.H_A1 t, view D.c1r (by omega) (by omega), view D.c1f (by omega) (by omega)]
  rfl

theorem rt2_exclusion2 (R : Run D s) (S : Scn2P D s t0 ta TA TA2 Hz)
    (H_RT2a : T1b D t0 TA + D.wfa2 ≤ TA2 + D.wa02)
    (H_RT2b : T1b D t0 TA ≤ T2b D TA2)
    (H_A0_FORK : TA + D.wa01 ≤ G1b D TA + D.wg1) :
    ∀ t, t < Hz → (s.A1 t && s.A2 t) = false := by
  intro t hz
  by_cases h : T1b D t0 TA ≤ t
  · rw [A2_low_after2 R S H_RT2a t h hz]; simp
  · rw [A1_low_before2 R S H_A0_FORK t (by omega) hz]; simp

/-- **RT2b + A0Fork2 ⇒ ack exclusion under H_PIN** (7j's `rt2_exclusion2_arcs` on `Scn2P`). -/
theorem rt2_exclusion2_arcs (R : Run D s) (S : Scn2P D s t0 ta TA TA2 Hz)
    (H_RT2 : RT2b D) (H_fork : A0Fork2 D) :
    ∀ t, t < Hz → (s.A1 t && s.A2 t) = false := by
  have := D.H_NONNEG
  have hTA := TA_ge2 R S
  have hTA2 := TA2_ge2 R S
  obtain ⟨h1, h2, h3, h4⟩ := H_RT2
  unfold TRb at hTA; unfold RRb QBb at hTA2; unfold A0Fork2 at H_fork
  apply rt2_exclusion2 R S
  · unfold T1b G2b QBb; omega
  · unfold T1b T2b G2b QBb; omega
  · unfold G1b QBb; omega

end

/-- **Exactness, 7j direction (counter-trace), every record.** If r2's fall reaches ustate
before A0's rise does, `t0 + wr2s < ta + wa0s`, and A0 was low at that view instant
(H_A0_LOW_BEFORE), then in every run q RISES at `t0 + wr2s + qr`, before `QBb`: the arbiter
grants client 1 while the server still serves client 2. So H_PIN is exactly the condition of
`q_lo2`. -/
theorem q_glitch2 {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz : Int} (R : Run D s)
    (S : ArbNoWithdraw.Scn2NS D s t0 ta TA TA2 Hz)
    (H_FAIL : t0 + D.wr2s < ta + D.wa0s)
    (H_A0_LOW : s.A0 (t0 + D.wr2s - D.wa0s) = false)
    (hz : t0 + D.wr2s + D.qr < Hz) :
    s.q (t0 + D.wr2s + D.qr) = true ∧ t0 + D.wr2s + D.qr < QBb D TA := by
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := S.H_ORDER
  refine ⟨?_, by unfold QBb; omega⟩
  have e1 : t0 + D.wr2s + D.qr - D.wr2s - D.qr = t0 := by omega
  have e2 : t0 + D.wr2s + D.qr - D.wa0s - D.qr = t0 + D.wr2s - D.wa0s := by omega
  rw [R.H_q, S.H_r1 _ (by omega), e1, e2, S.H_r2 _ (by omega), H_A0_LOW]
  simp [FS_set]

end J

/-! ## 3. Strictness: runs that meet H_PIN but not H_SETTLED -/

section strict
open Formal.Cells.ArbHeldTimed (Dl Sigs Run FS_eq FR_eq FG1_eq FG2_eq CE_eq RT1 RT2 A0Fork)
open Formal.Cells.ArbHeldTimed2 (FS_bool D0 W1 W2 RT1b RT2b A0Fork2 D0_all)

/-- 7j's `W1` with A0 rising at `-50`, only 50 ps before client 1's release at `0`. -/
def W1p : Sigs := { W1 with A0 := fun t => (decide (-50 ≤ t) && decide (t < 264)) || decide (552 ≤ t) }
/-- 7j's `W2` with A0 rising at `-50`. -/
def W2p : Sigs := { W2 with A0 := fun t => (decide (-50 ≤ t) && decide (t < 264)) || decide (484 ≤ t) }

theorem W1p_run : Run D0 W1p where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [W1p, W1, D0, ArbHeldTimed.prj, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [W1p, W1, D0, ArbHeldTimed.prj, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [W1p, W1, D0, ArbHeldTimed.prj, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [W1p, W1, D0, ArbHeldTimed.prj, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [W1p, W1, D0, ArbHeldTimed.prj, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [W1p, W1, D0, ArbHeldTimed.prj, CE_eq]; omega
  H_SRV := by
    intro t h
    have ht : t = -50 ∨ t = 264 ∨ t = 552 := by
      exact Classical.byContradiction fun hc => h (by rw [Bool.eq_iff_iff]; simp [W1p]; omega)
    rcases ht with rfl | rfl | rfl
    · exact ⟨-162, by simp [D0, ArbHeldTimed.prj], by simp [W1p, W1],
        fun v _ _ => by simp [W1p]; omega⟩
    · exact ⟨152, by simp [D0, ArbHeldTimed.prj], by simp [W1p, W1],
        fun v _ _ => by simp [W1p]; omega⟩
    · exact ⟨440, by simp [D0, ArbHeldTimed.prj], by simp [W1p, W1],
        fun v _ _ => by simp [W1p]; omega⟩

theorem W2p_run : Run D0 W2p where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [W2p, W2, D0, ArbHeldTimed.prj, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [W2p, W2, D0, ArbHeldTimed.prj, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [W2p, W2, D0, ArbHeldTimed.prj, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [W2p, W2, D0, ArbHeldTimed.prj, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [W2p, W2, D0, ArbHeldTimed.prj, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [W2p, W2, D0, ArbHeldTimed.prj, CE_eq]; omega
  H_SRV := by
    intro t h
    have ht : t = -50 ∨ t = 264 ∨ t = 484 := by
      exact Classical.byContradiction fun hc => h (by rw [Bool.eq_iff_iff]; simp [W2p]; omega)
    rcases ht with rfl | rfl | rfl
    · exact ⟨-162, by simp [D0, ArbHeldTimed.prj], by simp [W2p, W2],
        fun v _ _ => by simp [W2p]; omega⟩
    · exact ⟨152, by simp [D0, ArbHeldTimed.prj], by simp [W2p, W2],
        fun v _ _ => by simp [W2p]; omega⟩
    · exact ⟨372, by simp [D0, ArbHeldTimed.prj], by simp [W2p, W2],
        fun v _ _ => by simp [W2p]; omega⟩

theorem W1p_scn (Hz : Int) (hz : 552 < Hz) : H.ScnP D0 W1p 0 (-50) 264 552 Hz where
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [W1p]; omega
  H_A0_prev := by simp [W1p]
  H_q_init := by intro t h; simp [W1p, W1]; omega
  H_A1_init := by intro t h; simp [W1p, W1]; omega
  H_A2_init := by intro t h; simp [W1p, W1]; omega
  H_PIN := by simp [D0, ArbHeldTimed.prj]

theorem W2p_scn (Hz : Int) (hz : 484 < Hz) : J.Scn2P D0 W2p 0 (-50) 264 484 Hz where
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [W2p]; omega
  H_A0_prev := by simp [W2p]
  H_q_init := by intro t h; simp [W2p, W2]; omega
  H_A1_init := by intro t h; simp [W2p, W2]; omega
  H_A2_init := by intro t h; simp [W2p, W2]; omega
  H_PIN := by simp [D0, ArbHeldTimed.prj]

/-- **The sharp scenarios are strictly more general and non-vacuous.** On 7j's `D0` (which
meets RT1, RT2, A0Fork, RT1b, RT2b, A0Fork2), `W1p`/`W2p` are runs of the gate relations (all
`t`, server included) that satisfy `ScnP`/`Scn2P` for every horizon past the second server
edge, while BOTH conjuncts of 7h/7j's H_SETTLED fail for them (A0 rises 50 ps before the
release; `qf = c1f = c2f = 124`). The exclusion theorems therefore apply to runs 7h/7j did
not cover; here they give exclusion on all of `W1p`/`W2p` below the horizon. -/
theorem strict_witness :
    (RT1 D0 ∧ RT2 D0 ∧ A0Fork D0 ∧ RT1b D0 ∧ RT2b D0 ∧ A0Fork2 D0) ∧
    Run D0 W1p ∧ (∀ Hz, 552 < Hz → H.ScnP D0 W1p 0 (-50) 264 552 Hz) ∧
    ¬ ((-50 : Int) + D0.wa0s + D0.qf ≤ 0) ∧ ¬ ((-50 : Int) + D0.wa01 + D0.c1f ≤ 0) ∧
    Run D0 W2p ∧ (∀ Hz, 484 < Hz → J.Scn2P D0 W2p 0 (-50) 264 484 Hz) ∧
    ¬ ((-50 : Int) + D0.wa0s + D0.qf ≤ 0) ∧ ¬ ((-50 : Int) + D0.wa02 + D0.c2f ≤ 0) ∧
    (∀ t, t < 600 → (W1p.g1 t && W1p.g2 t) = false ∧ (W1p.A1 t && W1p.A2 t) = false) ∧
    (∀ t, t < 600 → (W2p.g1 t && W2p.g2 t) = false ∧ (W2p.A1 t && W2p.A2 t) = false) := by
  refine ⟨D0_all, W1p_run, W1p_scn, by simp [D0, ArbHeldTimed.prj],
    by simp [D0, ArbHeldTimed.prj], W2p_run, W2p_scn, by simp [D0, ArbHeldTimed.prj],
    by simp [D0, ArbHeldTimed.prj], ?_, ?_⟩
  · intro t ht
    exact ⟨H.rt1_exclusion W1p_run (W1p_scn 600 (by omega)) D0_all.1 t ht,
      H.rt2_exclusion_arcs W1p_run (W1p_scn 600 (by omega)) D0_all.2.1 D0_all.2.2.1 t ht⟩
  · intro t ht
    exact ⟨J.rt1_exclusion2 W2p_run (W2p_scn 600 (by omega)) D0_all.2.2.2.1 t ht,
      J.rt2_exclusion2_arcs W2p_run (W2p_scn 600 (by omega)) D0_all.2.2.2.2.1
        D0_all.2.2.2.2.2 t ht⟩

end strict

/-! ## 4. H_PIN from the four-phase causality -/

section causal
open Formal.Cells.ArbHeldTimed (Dl Sigs Run)
open Formal.Cells.ArbNoWithdraw (Caus1 Caus2 A1_rise_after A2_rise_after W1c W1c_run)

/-- **H_PIN (client 1) from causality.** In any run of 7h's gate relations with Bbare's causal
history `Caus1` (client latency `L` from A1's rise at ua1's output to r1's fall at its driver),
H_PIN holds as soon as H_ARC_P: `wa0s ≤ wa01 + c1r + L + wr1s`. Compared with Bbare's
`settled1_of_causal`: no `qf` on the left, the r1 route on the right. -/
theorem settledP1_of_causal {D : Dl} {s : Sigs} (R : Run D s) {ta t0 L : Int}
    (hc : Caus1 D s ta t0 L) (H_ARC_P : D.wa0s ≤ D.wa01 + D.c1r + L + D.wr1s) :
    ta + D.wa0s ≤ t0 + D.wr1s := by
  obtain ⟨T, hT, hlo, h0, hlat⟩ := hc
  have := A1_rise_after R hT hlo h0
  omega

theorem settledP2_of_causal {D : Dl} {s : Sigs} (R : Run D s) {ta t0 L : Int}
    (hc : Caus2 D s ta t0 L) (H_ARC_P : D.wa0s ≤ D.wa02 + D.c2r + L + D.wr2s) :
    ta + D.wa0s ≤ t0 + D.wr2s := by
  obtain ⟨T, hT, hlo, h0, hlat⟩ := hc
  have := A2_rise_after R hT hlo h0
  omega

/-- Non-vacuity: Bbare's `W1c` (A1 rising at -944 on 7j's `D0`) has a causal history at
latency 0, and H_ARC_P holds at `L = 0` on `D0`. -/
theorem settledP1_nonvacuous :
    Run ArbHeldTimed2.D0 W1c ∧ Caus1 ArbHeldTimed2.D0 W1c (-1000) 0 0 ∧
      ArbHeldTimed2.D0.wa0s ≤ ArbHeldTimed2.D0.wa01 + ArbHeldTimed2.D0.c1r + 0 +
        ArbHeldTimed2.D0.wr1s := by
  refine ⟨W1c_run, ⟨-944, by simp [W1c], ?_, ?_, by omega⟩,
    by simp [ArbHeldTimed2.D0, ArbHeldTimed.prj]⟩
  · intro u h1 h2; simp [W1c, ArbHeldTimed2.D0, ArbHeldTimed.prj] at h1 ⊢; omega
  · intro u h1 h2; simp [W1c, ArbHeldTimed2.W1, ArbHeldTimed2.D0, ArbHeldTimed.prj] at h1 ⊢
    omega

end causal

/-! ## 5. The latency table on gcd_hw's routed arcs -/

section data
open Formal.Cells.OnGcdArbKappa
open Formal.Cells.ConstraintsKappa
open Formal.Core.Substrate (Kappa pathDelay)

/-- H_ARC_P for client 1 under `Real7` (`ac`, `dS1` cancel), with the r1 route credited by its
extracted suffix `rs1` (H_RK_ROUTE): `dS2 + es + ps ≤ d12 + e1 + p1 + ac1 + rs1 + L` (fs). -/
def fsh1 (L : Nat) : Form := ⟨[.dS2, .es, .ps], [.d12, .e1, .p1, .ac1, .rs1], 0, L, false⟩
/-- Client 2: `dS1 + es + ps ≤ d12 + e2 + p2 + ac2 + rs2 + L`. -/
def fsh2 (L : Nat) : Form := ⟨[.dS1, .es, .ps], [.d12, .e2, .p2, .ac2, .rs2], 0, L, false⟩

/-- Per arbiter: the least client latencies (fs) certified at κS2 (script
`/tmp/claude-0/probes/Bset/tbl2.py`; the kernel checks them, `set2_cert`). -/
def setTbl2 : List ((E → Quad) × Nat × Nat) := [(v_g2_merge10_uarb1, 0, 0), (v_g2_merge11_uarb1, 194661, 222504), (v_g2_merge12_uarb1, 0, 0), (v_g2_merge12_uarb2, 0, 502361), (v_g2_merge2_uarb1, 63855, 0), (v_g2_merge3_uarb1, 0, 0), (v_g2_merge4_uarb1, 0, 0), (v_g2_merge6_uarb1, 87401, 0), (v_g2_merge9_uarb1, 7114, 0), (v_g3_merge10_uarb1, 0, 0), (v_g3_merge11_uarb1, 58283, 70167), (v_g3_merge12_uarb1, 51295, 0), (v_g3_merge12_uarb2, 0, 0), (v_g3_merge2_uarb1, 60980, 134713), (v_g3_merge3_uarb1, 0, 0), (v_g3_merge4_uarb1, 0, 23661), (v_g3_merge6_uarb1, 0, 0), (v_g3_merge9_uarb1, 0, 489659), (v_g4_merge10_uarb1, 0, 0), (v_g4_merge11_uarb1, 0, 0), (v_g4_merge12_uarb1, 0, 0), (v_g4_merge12_uarb2, 0, 0), (v_g4_merge2_uarb1, 94210, 124988), (v_g4_merge3_uarb1, 0, 0), (v_g4_merge4_uarb1, 0, 0), (v_g4_merge6_uarb1, 0, 0), (v_g4_merge9_uarb1, 247770, 0), (v_gd_merge10_uarb1, 0, 0), (v_gd_merge11_uarb1, 0, 370871), (v_gd_merge12_uarb1, 222704, 13722), (v_gd_merge12_uarb2, 0, 0), (v_gd_merge2_uarb1, 0, 0), (v_gd_merge3_uarb1, 0, 0), (v_gd_merge4_uarb1, 214091, 0), (v_gd_merge6_uarb1, 0, 0), (v_gd_merge9_uarb1, 0, 436342)]

theorem setTbl2_fst : setTbl2.map Prod.fst = arbs := rfl

theorem set2_cert : setTbl2.all (fun e => certFor .lit (fsh1 e.2.1) e.1 216552148868 1000000000000 &&
    certFor .lit (fsh2 e.2.2) e.1 216552148868 1000000000000) = true := by decide +kernel

/-- **The sharp latency that suffices.** For every routed gcd_hw arbiter, every κ ≤ κS2 and
every realization: H_ARC_P holds for client 1 with latency `L1` and client 2 with `L2`. -/
theorem settledP_safe {e : (E → Quad) × Nat × Nat} (he : e ∈ setTbl2) (k : Kappa)
    (H_KAPPA : k.num * 1000000000000 ≤ k.den * 216552148868) {d : E → Nat}
    (hd : (litModel k e.1).Realizes d) : holds d (fsh1 e.2.1) ∧ holds d (fsh2 e.2.2) := by
  have hc := List.all_eq_true.1 set2_cert e he
  simp only [Bool.and_eq_true] at hc
  exact ⟨form_safe (by decide) hc.1 k H_KAPPA d hd, form_safe (by decide) hc.2 k H_KAPPA d hd⟩

/-- The largest entry: 502.361 ps (seed 2 merge12.uarb2, client 2); Bbare's form needed
1590.934 ps. -/
theorem setTbl2_max : setTbl2.all (fun e => decide (e.2.1 ≤ 502361 ∧ e.2.2 ≤ 502361)) = true ∧
    (v_g2_merge12_uarb2, 0, 502361) ∈ setTbl2 := by
  refine ⟨by decide, ?_⟩
  simp [setTbl2]

/-- 21 of the 72 clients need a positive latency; the other 51 are safe at `L = 0`. -/
theorem setTbl2_pos : (setTbl2.map (fun e => (if 0 < e.2.1 then 1 else 0) +
    (if 0 < e.2.2 then 1 else 0))).sum = 21 := by decide

/-- κS2's row for a form (`neg` = no safe side claimed; `pu/qu` = κS2; binding endpoint chosen
by the unsafe certificate). -/
def mkRow (f : Form) (v : E → Quad) : Row :=
  if (⟨"", .lit, f, v, true, 0, 1, false, 216552148868, 1000000000000⟩ : Row).certUnsafe
  then ⟨"", .lit, f, v, true, 0, 1, false, 216552148868, 1000000000000⟩
  else ⟨"", .lit, f, v, true, 0, 1, true, 216552148868, 1000000000000⟩

theorem mkRow_fields (f : Form) (v : E → Quad) : (mkRow f v).f = f ∧ (mkRow f v).v = v ∧
    (mkRow f v).rd = .lit ∧ (mkRow f v).pu = 216552148868 ∧ (mkRow f v).qu = 1000000000000 := by
  unfold mkRow; split <;> exact ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- For every positive table entry `L`, the row of latency `L − 10 fs`. -/
def tightRows : List Row := setTbl2.flatMap fun e =>
  (if 0 < e.2.1 then [mkRow (fsh1 (e.2.1 - 10)) e.1] else []) ++
  (if 0 < e.2.2 then [mkRow (fsh2 (e.2.2 - 10)) e.1] else [])

theorem tightRows_ok : tightRows.all (fun r => r.ok) = true := by decide +kernel
theorem tightRows_len : tightRows.length = 21 := by decide

theorem mem_tight1 {e : (E → Quad) × Nat × Nat} (he : e ∈ setTbl2) (h : 0 < e.2.1) :
    mkRow (fsh1 (e.2.1 - 10)) e.1 ∈ tightRows := by
  unfold tightRows; rw [List.mem_flatMap]; exact ⟨e, he, by simp [h]⟩

theorem mem_tight2 {e : (E → Quad) × Nat × Nat} (he : e ∈ setTbl2) (h : 0 < e.2.2) :
    mkRow (fsh2 (e.2.2 - 10)) e.1 ∈ tightRows := by
  unfold tightRows; rw [List.mem_flatMap]; exact ⟨e, he, by simp [h]⟩

theorem row_viol {f : Form} {v : E → Quad} (hr : (mkRow f v).ok = true) (k : Kappa)
    (H_KAPPA : k.den * 216552148868 ≤ k.num * 1000000000000) :
    ∃ d : E → Nat, (litModel k v).Realizes d ∧ ¬ holds d f := by
  obtain ⟨hf, hv, hrd, hp, hq⟩ := mkRow_fields f v
  obtain ⟨d, hd, hlt⟩ := row_unsafe_ex (mkRow f v) hr k (by rw [hp, hq]; exact H_KAPPA)
  rw [hf, hv, hrd] at *
  refine ⟨d, hd, ?_⟩
  unfold holds; omega

/-- **The table is exact to 10 fs.** For each of the 21 positive entries `L` and every
κ ≥ κS2, some realization of the arbiter's extracted arcs violates H_ARC_P at latency
`L − 10 fs`. -/
theorem settledP_tight {e : (E → Quad) × Nat × Nat} (he : e ∈ setTbl2) (k : Kappa)
    (H_KAPPA : k.den * 216552148868 ≤ k.num * 1000000000000) :
    (0 < e.2.1 → ∃ d : E → Nat, (litModel k e.1).Realizes d ∧ ¬ holds d (fsh1 (e.2.1 - 10))) ∧
    (0 < e.2.2 → ∃ d : E → Nat, (litModel k e.1).Realizes d ∧ ¬ holds d (fsh2 (e.2.2 - 10))) :=
  ⟨fun h => row_viol (List.all_eq_true.1 tightRows_ok _ (mem_tight1 he h)) k H_KAPPA,
   fun h => row_viol (List.all_eq_true.1 tightRows_ok _ (mem_tight2 he h)) k H_KAPPA⟩

/-- Consequently zero latency fails exactly on the 21 positive entries (and holds on the
other 51 by `settledP_safe`). -/
theorem settledP_L0_fails {e : (E → Quad) × Nat × Nat} (he : e ∈ setTbl2) (k : Kappa)
    (H_KAPPA : k.den * 216552148868 ≤ k.num * 1000000000000) :
    (0 < e.2.1 → ∃ d : E → Nat, (litModel k e.1).Realizes d ∧ ¬ holds d (fsh1 0)) ∧
    (0 < e.2.2 → ∃ d : E → Nat, (litModel k e.1).Realizes d ∧ ¬ holds d (fsh2 0)) := by
  obtain ⟨h1, h2⟩ := settledP_tight he k H_KAPPA
  refine ⟨fun h => ?_, fun h => ?_⟩
  · obtain ⟨d, hd, hn⟩ := h1 h
    exact ⟨d, hd, fun hh => hn (by unfold holds fsh1 at *; simp only at *; omega)⟩
  · obtain ⟨d, hd, hn⟩ := h2 h
    exact ⟨d, hd, fun hh => hn (by unfold holds fsh2 at *; simp only at *; omega)⟩

end data

/-! ## 6. D2 at the gate level with the sharp condition -/

section design
open Formal.Cells.OnGcdArbKappa
open Formal.Cells.ArbHeldTimed (Dl Sigs Run)
open Formal.Cells.ArbNoWithdraw (Caus1 Caus2 ScnNS Scn2NS)
open Formal.Core.Substrate (Kappa pathDelay)

theorem ScnNS.toP {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz : Int} (S : ScnNS D s t0 ta TA TA2 Hz)
    (h : ta + D.wa0s ≤ t0 + D.wr1s) : H.ScnP D s t0 ta TA TA2 Hz :=
  ⟨S.H_ORDER, S.H_r1, S.H_r2, S.H_A0, S.H_A0_prev, S.H_q_init, S.H_A1_init, S.H_A2_init, h⟩

theorem Scn2NS.toP {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz : Int} (S : Scn2NS D s t0 ta TA TA2 Hz)
    (h : ta + D.wa0s ≤ t0 + D.wr2s) : J.Scn2P D s t0 ta TA TA2 Hz :=
  ⟨S.H_ORDER, S.H_r1, S.H_r2, S.H_A0, S.H_A0_prev, S.H_q_init, S.H_A1_init, S.H_A2_init, h⟩

/-- `OnGcdArbKappa.rt2_gate` on `ScnP`. -/
theorem rt2_gateP (d : E → Nat) (hP : holds d F_mP) (hG : holds d F_mG) (hA : holds d F_mA)
    (hGG : holds d F_mGG) (hF : holds d F_fork2) {D : Dl} {s : Sigs}
    {t0 ta TA TA2 Hz : Int} (h : OnGcdArbA0.Real7 (xOf d) D)
    (H_SERVER_GRAPH : (d .srv : Int) ≤ D.smin) (R : Run D s)
    (S : H.ScnP D s t0 ta TA TA2 Hz) :
    ∀ t, t < Hz → (s.A1 t && s.A2 t) = false := by
  simp only [holds, F_mP, F_mG, F_mA, F_mGG, F_fork2, pathDelay, List.map, List.sum_cons,
    List.sum_nil] at hP hG hA hGG hF
  have e : 0 ≤ OnGcdArbA0.mP (xOf d) + D.smin ∧ 0 ≤ OnGcdArbA0.mG (xOf d) + 2 * D.smin ∧
      0 ≤ OnGcdArbA0.mA (xOf d) + D.smin ∧ 0 ≤ OnGcdArbA0.mGG (xOf d) + 2 * D.smin := by
    simp only [OnGcdArbA0.mP, OnGcdArbA0.mG, OnGcdArbA0.mA, OnGcdArbA0.mGG, OnGcdArbA0.Rsrv,
      OnGcdArbA0.As, OnGcdArbA0.A1r, OnGcdArbA0.A2r, xOf]
    omega
  have f : 0 ≤ OnGcdArbA0.mF (xOf d) := by
    simp only [OnGcdArbA0.mF, OnGcdArbA0.As, OnGcdArbA0.A2r, xOf]; omega
  exact H.rt2_exclusion_arcs R S ((OnGcdArbA0.rt2_iff _ D h).2 e)
    ((OnGcdArbA0.a0fork_iff _ D h).2 f)

/-- `OnGcdArbKappa.rt2b_gate` on `Scn2P`. -/
theorem rt2b_gateP (d : E → Nat) (hP : holds d F_nP) (hG : holds d F_nG) (hA : holds d F_nA)
    (hGG : holds d F_nGG) (hF : holds d F_fork1) {D : Dl} {s : Sigs}
    {t0 ta TA TA2 Hz : Int} (h : OnGcdArbA0.Real7 (xOfB d) D)
    (H_SERVER_GRAPH : (d .srv : Int) ≤ D.smin) (R : Run D s)
    (S : J.Scn2P D s t0 ta TA TA2 Hz) :
    ∀ t, t < Hz → (s.A1 t && s.A2 t) = false := by
  simp only [holds, F_nP, F_nG, F_nA, F_nGG, F_fork1, pathDelay, List.map, List.sum_cons,
    List.sum_nil] at hP hG hA hGG hF
  have e : 0 ≤ OnGcdArbA0.nP (xOfB d) + D.smin ∧ 0 ≤ OnGcdArbA0.nG (xOfB d) + 2 * D.smin ∧
      0 ≤ OnGcdArbA0.nA (xOfB d) + D.smin ∧ 0 ≤ OnGcdArbA0.nGG (xOfB d) + 2 * D.smin := by
    simp only [OnGcdArbA0.nP, OnGcdArbA0.nG, OnGcdArbA0.nA, OnGcdArbA0.nGG, OnGcdArbA0.Rsrv,
      OnGcdArbA0.As, OnGcdArbA0.A1r, OnGcdArbA0.A2r, xOfB, xOf]
    omega
  have f : 0 ≤ OnGcdArbA0.nF (xOfB d) := by
    simp only [OnGcdArbA0.nF, OnGcdArbA0.As, OnGcdArbA0.A1r, xOfB, xOf]; omega
  exact J.rt2_exclusion2_arcs R S ((OnGcdArbA0.rt2b_iff _ D h).2 e)
    ((OnGcdArbA0.a0fork2_iff _ D h).2 f)

/-- `OnGcdArbKappa.rt1s_gate` on `ScnP`. -/
theorem rt1s_gateP (d : E → Nat) (h : holds d F_rt1s) {cr : Int} {D : Dl}
    {s : Sigs} {t0 ta TA TA2 Hz : Int} (hr : OnGcdArbFix.Real1 (qOf d) cr (d .cq) D)
    (hA : D.wa0s = d .ac + d .dS1 + d .dS2 + d .es + d .ps) (hq : D.qf = d .aq)
    (H_SERVER_GRAPH : (d .srv : Int) ≤ D.smin)
    (R : Run D s) (S : H.ScnP D s t0 ta TA TA2 Hz) :
    ∀ t, t < Hz → (s.g1 t && s.g2 t) = false := by
  simp only [holds, F_rt1s, pathDelay, List.map, List.sum_cons, List.sum_nil] at h
  refine H.rt1_exclusion R S ((OnGcdArbFix.rt1_iff _ cr _ D hr).2 (Or.inl ?_))
  simp only [OnGcdArbFix.Q.m1, qOf]; rw [hA, hq]; omega

/-- `OnGcdArbKappa.rt1bs_gate` on `Scn2P`. -/
theorem rt1bs_gateP (d : E → Nat) (h : holds d F_rt1bs) {cr : Int} {D : Dl}
    {s : Sigs} {t0 ta TA TA2 Hz : Int} (hr : OnGcdArbFix.Real2 (qOf d) cr (d .cq) D)
    (hA : D.wa0s = d .ac + d .dS1 + d .dS2 + d .es + d .ps) (hq : D.qr = d .aq)
    (H_SERVER_GRAPH : (d .srv : Int) ≤ D.smin)
    (R : Run D s) (S : J.Scn2P D s t0 ta TA TA2 Hz) :
    ∀ t, t < Hz → (s.g1 t && s.g2 t) = false := by
  simp only [holds, F_rt1bs, pathDelay, List.map, List.sum_cons, List.sum_nil] at h
  refine J.rt1_exclusion2 R S ((OnGcdArbFix.rt1b_iff _ cr _ D hr).2 (Or.inl ?_))
  simp only [OnGcdArbFix.Q.m2, qOf]; rw [hA, hq]; omega

/-- **D2 at the gate level, sharp scenarios.** OnGcdArbKappaSrv's `design_gate_held` (κ ≤ κS2,
every routed gcd_hw arbiter, every realization) with 7h/7j's `Scn`/`Scn2` replaced by
`ScnP`/`Scn2P` (H_PIN instead of H_SETTLED). By `H.ofScn`/`J.ofScn2` this contains the
original statement. -/
theorem design_gate_held_sharp {v : E → Quad} (hv : v ∈ arbs) (k : Kappa)
    (H_KAPPA : k.num * 1000000000000 ≤ k.den * 216552148868) {d : E → Nat}
    (hd : (litModel k v).Realizes d) :
    (∀ (D : Dl) (s : Sigs) (t0 ta TA TA2 Hz : Int),
      OnGcdArbA0.Real7 (xOf d) D → (d .srv : Int) ≤ D.smin → Run D s →
      H.ScnP D s t0 ta TA TA2 Hz → ∀ t, t < Hz → (s.A1 t && s.A2 t) = false) ∧
    (∀ (D : Dl) (s : Sigs) (t0 ta TA TA2 Hz : Int),
      OnGcdArbA0.Real7 (xOfB d) D → (d .srv : Int) ≤ D.smin → Run D s →
      J.Scn2P D s t0 ta TA TA2 Hz → ∀ t, t < Hz → (s.A1 t && s.A2 t) = false) ∧
    (∀ (cr : Int) (D : Dl) (s : Sigs) (t0 ta TA TA2 Hz : Int),
      OnGcdArbFix.Real1 (qOf d) cr (d .cq) D →
      D.wa0s = d .ac + d .dS1 + d .dS2 + d .es + d .ps → D.qf = d .aq →
      (d .srv : Int) ≤ D.smin → Run D s →
      H.ScnP D s t0 ta TA TA2 Hz → ∀ t, t < Hz → (s.g1 t && s.g2 t) = false) ∧
    (∀ (cr : Int) (D : Dl) (s : Sigs) (t0 ta TA TA2 Hz : Int),
      OnGcdArbFix.Real2 (qOf d) cr (d .cq) D →
      D.wa0s = d .ac + d .dS1 + d .dS2 + d .es + d .ps → D.qr = d .aq →
      (d .srv : Int) ≤ D.smin → Run D s →
      J.Scn2P D s t0 ta TA TA2 Hz → ∀ t, t < Hz → (s.g1 t && s.g2 t) = false) := by
  have m : ∀ {f : Form}, f ∈ OnGcdArbKappaSrv.formsHeld → holds d f := fun hf =>
    OnGcdArbKappaSrv.design_held_holds hv hf k H_KAPPA hd
  refine ⟨fun D s t0 ta TA TA2 Hz h hs R S => rt2_gateP d
      (m (by simp [OnGcdArbKappaSrv.formsHeld])) (m (by simp [OnGcdArbKappaSrv.formsHeld]))
      (m (by simp [OnGcdArbKappaSrv.formsHeld])) (m (by simp [OnGcdArbKappaSrv.formsHeld]))
      (m (by simp [OnGcdArbKappaSrv.formsHeld])) h hs R S,
    fun D s t0 ta TA TA2 Hz h hs R S => rt2b_gateP d
      (m (by simp [OnGcdArbKappaSrv.formsHeld])) (m (by simp [OnGcdArbKappaSrv.formsHeld]))
      (m (by simp [OnGcdArbKappaSrv.formsHeld])) (m (by simp [OnGcdArbKappaSrv.formsHeld]))
      (m (by simp [OnGcdArbKappaSrv.formsHeld])) h hs R S,
    fun cr D s t0 ta TA TA2 Hz h hA hq hs R S =>
      rt1s_gateP d (m (by simp [OnGcdArbKappaSrv.formsHeld])) h hA hq hs R S,
    fun cr D s t0 ta TA TA2 Hz h hA hq hs R S =>
      rt1bs_gateP d (m (by simp [OnGcdArbKappaSrv.formsHeld])) h hA hq hs R S⟩

theorem mem_arbs_of2 {e : (E → Quad) × Nat × Nat} (he : e ∈ setTbl2) : e.1 ∈ arbs := by
  rw [← setTbl2_fst]; exact List.mem_map_of_mem he

/-- **D2 with H_PIN derived from the client's causality** (the sharp twin of Bbare's
`design_gate_held_causal`). For every κ ≤ κS2, routed arbiter `e.1` and realization `d`: the
four handover conclusions hold for every idealized run `s` meeting `Scn`/`Scn2` WITHOUT
H_SETTLED, given a causal run `sr` of the same record (same `ta`, `t0`) whose client latency
is at least setTbl2's `L_k`, and H_RK_ROUTE: r_k's route to ustate is at least its extracted
suffix (`rs_k ≤ wr_ks`; the common prefix from the driver is ≥ 0). -/
theorem design_gate_held_sharp_causal {e : (E → Quad) × Nat × Nat} (he : e ∈ setTbl2)
    (k : Kappa) (H_KAPPA : k.num * 1000000000000 ≤ k.den * 216552148868) {d : E → Nat}
    (hd : (litModel k e.1).Realizes d) :
    (∀ (D : Dl) (s sr : Sigs) (t0 ta TA TA2 Hz L : Int),
      OnGcdArbA0.Real7 (xOf d) D → (d .srv : Int) ≤ D.smin → Run D s →
      ScnNS D s t0 ta TA TA2 Hz → Run D sr → Caus1 D sr ta t0 L → (e.2.1 : Int) ≤ L →
      (d .rs1 : Int) ≤ D.wr1s → ∀ t, t < Hz → (s.A1 t && s.A2 t) = false) ∧
    (∀ (D : Dl) (s sr : Sigs) (t0 ta TA TA2 Hz L : Int),
      OnGcdArbA0.Real7 (xOfB d) D → (d .srv : Int) ≤ D.smin → Run D s →
      Scn2NS D s t0 ta TA TA2 Hz → Run D sr → Caus2 D sr ta t0 L → (e.2.2 : Int) ≤ L →
      (d .rs2 : Int) ≤ D.wr2s → ∀ t, t < Hz → (s.A1 t && s.A2 t) = false) ∧
    (∀ (cr : Int) (D : Dl) (s sr : Sigs) (t0 ta TA TA2 Hz L : Int),
      OnGcdArbFix.Real1 (qOf d) cr (d .cq) D →
      D.wa0s = d .ac + d .dS1 + d .dS2 + d .es + d .ps → D.qf = d .aq →
      D.wa01 = d .ac + d .dS1 + d .d12 + d .e1 + d .p1 → D.c1r = d .ac1 →
      (d .srv : Int) ≤ D.smin → Run D s →
      ScnNS D s t0 ta TA TA2 Hz → Run D sr → Caus1 D sr ta t0 L → (e.2.1 : Int) ≤ L →
      (d .rs1 : Int) ≤ D.wr1s → ∀ t, t < Hz → (s.g1 t && s.g2 t) = false) ∧
    (∀ (cr : Int) (D : Dl) (s sr : Sigs) (t0 ta TA TA2 Hz L : Int),
      OnGcdArbFix.Real2 (qOf d) cr (d .cq) D →
      D.wa0s = d .ac + d .dS1 + d .dS2 + d .es + d .ps → D.qr = d .aq →
      D.wa02 = d .ac + d .dS2 + d .d12 + d .e2 + d .p2 → D.c2r = d .ac2 →
      (d .srv : Int) ≤ D.smin → Run D s →
      Scn2NS D s t0 ta TA TA2 Hz → Run D sr → Caus2 D sr ta t0 L → (e.2.2 : Int) ≤ L →
      (d .rs2 : Int) ≤ D.wr2s → ∀ t, t < Hz → (s.g1 t && s.g2 t) = false) := by
  have G := design_gate_held_sharp (mem_arbs_of2 he) k H_KAPPA hd
  obtain ⟨h1, h2⟩ := settledP_safe he k H_KAPPA hd
  simp only [holds, fsh1, fsh2, pathDelay, List.map, List.sum_cons, List.sum_nil] at h1 h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro D s sr t0 ta TA TA2 Hz L hR hs R S Rr C hL hrk
    have hR' := hR
    obtain ⟨e1, e2, _, _, _, _, _, _, _, e10, _⟩ := hR'
    simp only [OnGcdArbA0.As, OnGcdArbA0.A1r, xOf] at e1 e2 e10
    exact G.1 D s t0 ta TA TA2 Hz hR hs R
      (ScnNS.toP S (settledP1_of_causal Rr C (by omega)))
  · intro D s sr t0 ta TA TA2 Hz L hR hs R S Rr C hL hrk
    have hR' := hR
    obtain ⟨e1, _, e3, _, _, _, _, _, _, _, _, e12, _⟩ := hR'
    simp only [OnGcdArbA0.As, OnGcdArbA0.A2r, xOfB, xOf] at e1 e3 e12
    exact G.2.1 D s t0 ta TA TA2 Hz hR hs R
      (Scn2NS.toP S (settledP2_of_causal Rr C (by omega)))
  · intro cr D s sr t0 ta TA TA2 Hz L hR hA hq hA1 hc1r hs R S Rr C hL hrk
    exact G.2.2.1 cr D s t0 ta TA TA2 Hz hR hA hq hs R
      (ScnNS.toP S (settledP1_of_causal Rr C (by omega)))
  · intro cr D s sr t0 ta TA TA2 Hz L hR hA hqr hA2 hc2r hs R S Rr C hL hrk
    exact G.2.2.2 cr D s t0 ta TA TA2 Hz hR hA hqr hs R
      (Scn2NS.toP S (settledP2_of_causal Rr C (by omega)))

end design

/-! ## 7. Link-driven clients: H_PIN discharged from LinkExact and the controller's arc -/

section link
open Formal.Cells.OnGcdArbKappa
open Formal.Cells.ConstraintsKappa
open Formal.Core.Substrate (Kappa Corner CArc CornerModel Scat pathDelay pathArc)
open Formal.Cells.ArbHeldTimed (Dl Sigs Run)
open Formal.Cells.ArbNoWithdraw (Caus1 Caus2 ScnNS Scn2NS)

/-- **The link controller as client** (LinkExact's model, verbatim): some stage parameters `P`
in LinkExact's scope (`Wf`) meeting its exact conjunction (`Conj`), a behaviour in its box,
with
* H_ACK_RB: `P.Rb = T`, the ack_out rise time of LinkExact's environment IS the rise `T` of
  the arbiter's A_k (both at ua_k's O6 output, the net's driver);
* H_ACK_READ: `x ≤ P.Blo`, the controller's ack read delay is at least `x` (its realised O6
  arc; the routed wire and site pin in front of it are ≥ 0 and NOT credited);
* the request was surely up (`P.U1 ≤ t0`) and the node (the r_k driver) is not high at `t0`. -/
def LinkRel (x T t0 : Int) : Prop :=
  ∃ (P : LinkExact.Par) (v : Bool) (pa pb pq pr pd pe pf : LibGapSteer.Rd)
    (r a b dd c q : Int → K3),
    LinkExact.Wf P ∧ LinkExact.Conj P ∧ LinkExact.Beh P v pa pb pq pr pd pe pf r a b dd c q ∧
    P.Rb = T ∧ x ≤ P.Blo ∧ P.U1 ≤ t0 ∧ c t0 ≠ .t

/-- **The link cannot release before its C-element has seen the ack and the read delay has
elapsed**: `T + x ≤ t0` (from `ArbNoWithdraw.link_no_withdraw`, i.e. LinkExact's
`sufficient`). -/
theorem LinkRel.release {x T t0 : Int} (h : LinkRel x T t0) : T + x ≤ t0 := by
  obtain ⟨P, v, pa, pb, pq, pr, pd, pe, pf, r, a, b, dd, c, q, S, H, Bh, hRb, hx, hU, hc⟩ := h
  apply Classical.byContradiction; intro hn
  exact hc (ArbNoWithdraw.link_no_withdraw S H Bh t0 hU (by omega))

/-- **Bbare's causal history, client 1, for a link client**, at latency `x`. -/
theorem link_caus1 {D : Dl} {sr : Sigs} {ta t0 T x : Int} (hT : sr.A1 T = true)
    (hlo : ∀ u, T - D.wfa1 - D.c1f ≤ u → u < T → sr.A1 u = false)
    (h0 : ∀ u, T - D.wa01 - D.c1f ≤ u → u < ta → sr.A0 u = false) (hL : LinkRel x T t0) :
    Caus1 D sr ta t0 x := ⟨T, hT, hlo, h0, hL.release⟩

theorem link_caus2 {D : Dl} {sr : Sigs} {ta t0 T x : Int} (hT : sr.A2 T = true)
    (hlo : ∀ u, T - D.wfa2 - D.c2f ≤ u → u < T → sr.A2 u = false)
    (h0 : ∀ u, T - D.wa02 - D.c2f ≤ u → u < ta → sr.A0 u = false) (hL : LinkRel x T t0) :
    Caus2 D sr ta t0 x := ⟨T, hT, hlo, h0, hL.release⟩

/-! ### The arbiter's arcs plus the controller's O6 arc, one shared corner -/

/-- prjxray `A6LUT (IOPATH A1..A6 O6 (0.045::0.056)(0.100::0.124))`, flat over pins, SLICEL and
SLICEM (`notes/B-arb-corners-pin.md`), in fs: the `bd_c2n` controller's I1 → O arc, under
H_LUT6_O6 (the controller, a `LUT6` primitive, sits on a 6LUT and drives O6; named, the
placement is not read here). -/
def lutO6 : Quad := (45000, 56000, 100000, 124000)

def vL (v : E → Quad) : Option E → Quad
  | none => lutO6
  | some e => v e

def arcL (v : E → Quad) (o : Option E) : CArc := mkArc (vL v o).1 (vL v o).2.2.2

/-- The `lit` model of one arbiter extended by the controller arc (`none`). -/
def litL (k : Kappa) (v : E → Quad) : CornerModel (Option E) := ⟨arcL v, k⟩

/-- The controller arc's `lit` endpoints (FAST_MIN, SLOW_MAX). -/
def lutArc : CArc := mkArc 45000 124000

def dL (d : E → Nat) (x : Nat) : Option E → Nat
  | none => x
  | some e => d e

/-- H_SAME_CORNER: a realization of the arbiter's arcs at corner `c` together with a delay of
the controller arc at the SAME corner is a realization of the extended model. -/
theorem realizes_ext {k : Kappa} {c : Corner} {v : E → Quad} {d : E → Nat} {x : Nat}
    (hd : (litModel k v).RealizesAt c d) (hx : Scat k c lutArc x) :
    (litL k v).RealizesAt c (dL d x) := by
  intro o
  cases o with
  | none => exact hx
  | some e => exact hd e

/-- H_ARC_P at latency = the controller arc, client 1 / client 2 (no constant). -/
def lP1 : List (Option E) := [some .dS2, some .es, some .ps]
def lQ1 : List (Option E) := [some .d12, some .e1, some .p1, some .ac1, some .rs1, none]
def lP2 : List (Option E) := [some .dS1, some .es, some .ps]
def lQ2 : List (Option E) := [some .d12, some .e2, some .p2, some .ac2, some .rs2, none]

/-- The κS2 certificate on the extended model (both endpoints, cleared). -/
def certL (v : E → Quad) (P Q : List (Option E)) : Bool :=
  decide (216552148868 * (ep false (pathArc (Q.map (arcL v))) + ep false (pathArc (P.map (arcL v)))) +
      1000000000000 * (ep false (pathArc (P.map (arcL v))) + 0) ≤
    1000000000000 * (ep false (pathArc (Q.map (arcL v))) + 0)) &&
  decide (216552148868 * (ep true (pathArc (Q.map (arcL v))) + ep true (pathArc (P.map (arcL v)))) +
      1000000000000 * (ep true (pathArc (P.map (arcL v))) + 0) ≤
    1000000000000 * (ep true (pathArc (Q.map (arcL v))) + 0))

theorem certL_safe {v : E → Quad} {P Q : List (Option E)} (hc : certL v P Q = true) (k : Kappa)
    (H_KAPPA : k.num * 1000000000000 ≤ k.den * 216552148868) : AllOK (litL k v) P Q 0 0 := by
  apply allOK_of_gen
  rw [genOK_iff_ep]
  unfold certL at hc
  simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
  intro s
  cases s
  · exact safe_arith (by decide) k.num_le H_KAPPA hc.1
  · exact safe_arith (by decide) k.num_le H_KAPPA hc.2

/-- gcd_hw's link-driven arbiter clients (drivers read from the four synth netlists by Bbare's
`drv2.py`: the r_k pin is driven by `<link>.ctl.u.u` O, whose I1 is the arbiter's ack):
client 1 of merge10; client 2 of merge2, merge4, merge6, merge10. Listed here: the 18 of
those 20 instances on which the O6 arc alone discharges H_ARC_P. -/
def linkTbl1 : List (E → Quad) :=
  [v_g2_merge10_uarb1, v_g3_merge10_uarb1, v_g4_merge10_uarb1, v_gd_merge10_uarb1]
def linkTbl2 : List (E → Quad) :=
  [v_g2_merge2_uarb1, v_gd_merge2_uarb1,
   v_g2_merge4_uarb1, v_g3_merge4_uarb1, v_g4_merge4_uarb1, v_gd_merge4_uarb1,
   v_g2_merge6_uarb1, v_g3_merge6_uarb1, v_g4_merge6_uarb1, v_gd_merge6_uarb1,
   v_g2_merge10_uarb1, v_g3_merge10_uarb1, v_g4_merge10_uarb1, v_gd_merge10_uarb1]

theorem link_cert1 : linkTbl1.all (fun v => certL v lP1 lQ1) = true := by decide +kernel
theorem link_cert2 : linkTbl2.all (fun v => certL v lP2 lQ2) = true := by decide +kernel

theorem linkTbl1_sub {v : E → Quad} (hv : v ∈ linkTbl1) : v ∈ arbs := by
  simp only [linkTbl1, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl <;> simp [arbs]

theorem linkTbl2_sub {v : E → Quad} (hv : v ∈ linkTbl2) : v ∈ arbs := by
  simp only [linkTbl2, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    simp [arbs]

/-- **H_PIN discharged for a link client 1** (merge10, 4 seeds). For every κ ≤ κS2, every
realization `d` of the arbiter's arcs at a corner `c`, every delay `x` of the controller's O6
arc at the same corner: in any run `sr` of the 7h record (with ua1's A0 route and arc, and
ustate's A0 route, at their realised values; H_RK_ROUTE), if A1 rose at `T` (low on its
windows before, A0 low before `ta`) and the controller is LinkExact's (`LinkRel x T t0`), then
`ta + wa0s ≤ t0 + wr1s`. No latency is assumed. -/
theorem link_pin1 {v : E → Quad} (hv : v ∈ linkTbl1) (k : Kappa)
    (H_KAPPA : k.num * 1000000000000 ≤ k.den * 216552148868) {c : Corner} {d : E → Nat}
    (hd : (litModel k v).RealizesAt c d) {x : Nat} (hx : Scat k c lutArc x) {D : Dl}
    (hA : D.wa0s = d .ac + d .dS1 + d .dS2 + d .es + d .ps)
    (hA1 : D.wa01 = d .ac + d .dS1 + d .d12 + d .e1 + d .p1) (hc1 : D.c1r = d .ac1)
    (H_RK_ROUTE : (d .rs1 : Int) ≤ D.wr1s) {sr : Sigs} (R : Run D sr) {ta t0 T : Int}
    (hT : sr.A1 T = true) (hlo : ∀ u, T - D.wfa1 - D.c1f ≤ u → u < T → sr.A1 u = false)
    (h0 : ∀ u, T - D.wa01 - D.c1f ≤ u → u < ta → sr.A0 u = false) (hL : LinkRel x T t0) :
    ta + D.wa0s ≤ t0 + D.wr1s := by
  have hc := certL_safe (List.all_eq_true.1 link_cert1 v hv) k H_KAPPA (dL d x)
    ⟨c, realizes_ext hd hx⟩
  simp only [pathDelay, lP1, lQ1, List.map, List.sum_cons, List.sum_nil, dL] at hc
  exact settledP1_of_causal R (link_caus1 hT hlo h0 hL) (by omega)

/-- **H_PIN discharged for a link client 2** (merge2 seeds 2/d, merge4, merge6, merge10). -/
theorem link_pin2 {v : E → Quad} (hv : v ∈ linkTbl2) (k : Kappa)
    (H_KAPPA : k.num * 1000000000000 ≤ k.den * 216552148868) {c : Corner} {d : E → Nat}
    (hd : (litModel k v).RealizesAt c d) {x : Nat} (hx : Scat k c lutArc x) {D : Dl}
    (hA : D.wa0s = d .ac + d .dS1 + d .dS2 + d .es + d .ps)
    (hA2 : D.wa02 = d .ac + d .dS2 + d .d12 + d .e2 + d .p2) (hc2 : D.c2r = d .ac2)
    (H_RK_ROUTE : (d .rs2 : Int) ≤ D.wr2s) {sr : Sigs} (R : Run D sr) {ta t0 T : Int}
    (hT : sr.A2 T = true) (hlo : ∀ u, T - D.wfa2 - D.c2f ≤ u → u < T → sr.A2 u = false)
    (h0 : ∀ u, T - D.wa02 - D.c2f ≤ u → u < ta → sr.A0 u = false) (hL : LinkRel x T t0) :
    ta + D.wa0s ≤ t0 + D.wr2s := by
  have hc := certL_safe (List.all_eq_true.1 link_cert2 v hv) k H_KAPPA (dL d x)
    ⟨c, realizes_ext hd hx⟩
  simp only [pathDelay, lP2, lQ2, List.map, List.sum_cons, List.sum_nil, dL] at hc
  exact settledP2_of_causal R (link_caus2 hT hlo h0 hL) (by omega)

/-- **D2 for link-driven clients with H_SETTLED DISCHARGED** (client 2 releases, 7j): on the
14 instances of `linkTbl2`, for every κ ≤ κS2, realization `d` at corner `c` and controller-arc
delay `x` at the same corner, both handover conclusions of the client-2 release hold for every
idealized run `s` meeting `Scn2` without H_SETTLED, given a causal run `sr` in which the client
is LinkExact's controller (`LinkRel`). No client-latency hypothesis remains. -/
theorem design_link_discharged2 {v : E → Quad} (hv : v ∈ linkTbl2) (k : Kappa)
    (H_KAPPA : k.num * 1000000000000 ≤ k.den * 216552148868) {c : Corner} {d : E → Nat}
    (hd : (litModel k v).RealizesAt c d) {x : Nat} (hx : Scat k c lutArc x) :
    (∀ (D : Dl) (s sr : Sigs) (t0 ta TA TA2 Hz T : Int),
      OnGcdArbA0.Real7 (xOfB d) D → (d .srv : Int) ≤ D.smin → Run D s →
      Scn2NS D s t0 ta TA TA2 Hz → Run D sr → sr.A2 T = true →
      (∀ u, T - D.wfa2 - D.c2f ≤ u → u < T → sr.A2 u = false) →
      (∀ u, T - D.wa02 - D.c2f ≤ u → u < ta → sr.A0 u = false) →
      (d .rs2 : Int) ≤ D.wr2s → LinkRel x T t0 → ∀ t, t < Hz → (s.A1 t && s.A2 t) = false) ∧
    (∀ (cr : Int) (D : Dl) (s sr : Sigs) (t0 ta TA TA2 Hz T : Int),
      OnGcdArbFix.Real2 (qOf d) cr (d .cq) D →
      D.wa0s = d .ac + d .dS1 + d .dS2 + d .es + d .ps → D.qr = d .aq →
      D.wa02 = d .ac + d .dS2 + d .d12 + d .e2 + d .p2 → D.c2r = d .ac2 →
      (d .srv : Int) ≤ D.smin → Run D s →
      Scn2NS D s t0 ta TA TA2 Hz → Run D sr → sr.A2 T = true →
      (∀ u, T - D.wfa2 - D.c2f ≤ u → u < T → sr.A2 u = false) →
      (∀ u, T - D.wa02 - D.c2f ≤ u → u < ta → sr.A0 u = false) →
      (d .rs2 : Int) ≤ D.wr2s → LinkRel x T t0 → ∀ t, t < Hz → (s.g1 t && s.g2 t) = false) := by
  have G := design_gate_held_sharp (linkTbl2_sub hv) k H_KAPPA ⟨c, hd⟩
  refine ⟨?_, ?_⟩
  · intro D s sr t0 ta TA TA2 Hz T hR hs R S Rr hT hlo h0 hrk hL
    have hR' := hR
    obtain ⟨e1, _, e3, _, _, _, _, _, _, _, _, e12, _⟩ := hR'
    simp only [OnGcdArbA0.As, OnGcdArbA0.A2r, xOfB, xOf] at e1 e3 e12
    exact G.2.1 D s t0 ta TA TA2 Hz hR hs R
      (Scn2NS.toP S (link_pin2 hv k H_KAPPA hd hx (by omega) (by omega) e12 hrk Rr hT hlo h0 hL))
  · intro cr D s sr t0 ta TA TA2 Hz T hR hA hqr hA2 hc2r hs R S Rr hT hlo h0 hrk hL
    exact G.2.2.2 cr D s t0 ta TA TA2 Hz hR hA hqr hs R
      (Scn2NS.toP S (link_pin2 hv k H_KAPPA hd hx hA hA2 hc2r hrk Rr hT hlo h0 hL))

/-- **The same for client 1 of merge10 (7h, client 1 releases).** -/
theorem design_link_discharged1 {v : E → Quad} (hv : v ∈ linkTbl1) (k : Kappa)
    (H_KAPPA : k.num * 1000000000000 ≤ k.den * 216552148868) {c : Corner} {d : E → Nat}
    (hd : (litModel k v).RealizesAt c d) {x : Nat} (hx : Scat k c lutArc x) :
    (∀ (D : Dl) (s sr : Sigs) (t0 ta TA TA2 Hz T : Int),
      OnGcdArbA0.Real7 (xOf d) D → (d .srv : Int) ≤ D.smin → Run D s →
      ScnNS D s t0 ta TA TA2 Hz → Run D sr → sr.A1 T = true →
      (∀ u, T - D.wfa1 - D.c1f ≤ u → u < T → sr.A1 u = false) →
      (∀ u, T - D.wa01 - D.c1f ≤ u → u < ta → sr.A0 u = false) →
      (d .rs1 : Int) ≤ D.wr1s → LinkRel x T t0 → ∀ t, t < Hz → (s.A1 t && s.A2 t) = false) ∧
    (∀ (cr : Int) (D : Dl) (s sr : Sigs) (t0 ta TA TA2 Hz T : Int),
      OnGcdArbFix.Real1 (qOf d) cr (d .cq) D →
      D.wa0s = d .ac + d .dS1 + d .dS2 + d .es + d .ps → D.qf = d .aq →
      D.wa01 = d .ac + d .dS1 + d .d12 + d .e1 + d .p1 → D.c1r = d .ac1 →
      (d .srv : Int) ≤ D.smin → Run D s →
      ScnNS D s t0 ta TA TA2 Hz → Run D sr → sr.A1 T = true →
      (∀ u, T - D.wfa1 - D.c1f ≤ u → u < T → sr.A1 u = false) →
      (∀ u, T - D.wa01 - D.c1f ≤ u → u < ta → sr.A0 u = false) →
      (d .rs1 : Int) ≤ D.wr1s → LinkRel x T t0 → ∀ t, t < Hz → (s.g1 t && s.g2 t) = false) := by
  have G := design_gate_held_sharp (linkTbl1_sub hv) k H_KAPPA ⟨c, hd⟩
  refine ⟨?_, ?_⟩
  · intro D s sr t0 ta TA TA2 Hz T hR hs R S Rr hT hlo h0 hrk hL
    have hR' := hR
    obtain ⟨e1, e2, _, _, _, _, _, _, _, e10, _⟩ := hR'
    simp only [OnGcdArbA0.As, OnGcdArbA0.A1r, xOf] at e1 e2 e10
    exact G.1 D s t0 ta TA TA2 Hz hR hs R
      (ScnNS.toP S (link_pin1 hv k H_KAPPA hd hx (by omega) (by omega) e10 hrk Rr hT hlo h0 hL))
  · intro cr D s sr t0 ta TA TA2 Hz T hR hA hq hA1 hc1r hs R S Rr hT hlo h0 hrk hL
    exact G.2.2.1 cr D s t0 ta TA TA2 Hz hR hA hq hs R
      (ScnNS.toP S (link_pin1 hv k H_KAPPA hd hx hA hA1 hc1r hrk Rr hT hlo h0 hL))

/-- κS2 as a scatter bound. -/
def kS2 : Kappa := ⟨216552148868, 1000000000000, by decide, by decide⟩

/-- **The two link instances the O6 arc does not discharge** (seed 3 and seed 4 merge2.uarb1,
client 2). At κS2, a realization of the extended model (ConstraintsKappa's worst one at the
FAST endpoint: the arbiter's data-side arcs at `⌊(1+κ)F⌋`, the request side and the
controller arc at `⌈(1-κ)F⌉`) violates H_ARC_P with latency = the controller arc alone. What
is missing is the routed wire and site pin from ua2's O6 to the controller's I1 (residual at
κS2: 19.9 / 37.6 ps fast / slow endpoint on seed 3, 89.7 ps at the fast endpoint on seed 4;
script `link.py`). -/
theorem link_short :
    (∃ d2 : Option E → Nat, (litL kS2 v_g3_merge2_uarb1).Realizes d2 ∧
      pathDelay d2 lQ2 < pathDelay d2 lP2) ∧
    (∃ d2 : Option E → Nat, (litL kS2 v_g4_merge2_uarb1).Realizes d2 ∧
      pathDelay d2 lQ2 < pathDelay d2 lP2) :=
  ⟨⟨worst (litL kS2 v_g3_merge2_uarb1) lP2 false, ⟨_, worst_realizes _ _ _⟩, by decide +kernel⟩,
   ⟨worst (litL kS2 v_g4_merge2_uarb1) lP2 false, ⟨_, worst_realizes _ _ _⟩, by decide +kernel⟩⟩

/-! ### Non-vacuity of the link composition -/

open Formal.Cells.ArbHeldTimed (FS_eq FR_eq FG1_eq FG2_eq CE_eq)
open Formal.Cells.ArbHeldTimed2 (FS_bool D0)

/-- Bbare's `W1c` shifted by +5244 ps (A1 rises at 4300 = LinkExact `P0`'s `Rb`; r1 falls at
5244). -/
def W1s : Sigs where
  r1 := fun t => decide (t < 5244)
  r2 := fun _ => true
  q := fun t => decide (t < 5632)
  R0 := fun t => decide (t < 5396) || decide (5684 ≤ t)
  g1 := fun t => decide (t < 5396)
  g2 := fun t => decide (5688 ≤ t)
  A0 := fun t => (decide (4244 ≤ t) && decide (t < 5508)) || decide (5796 ≤ t)
  A1 := fun t => decide (4300 ≤ t) && decide (t < 5632)
  A2 := fun t => decide (5852 ≤ t)

theorem W1s_run : Run D0 W1s where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [W1s, D0, ArbHeldTimed.prj, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [W1s, D0, ArbHeldTimed.prj, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [W1s, D0, ArbHeldTimed.prj, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [W1s, D0, ArbHeldTimed.prj, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [W1s, D0, ArbHeldTimed.prj, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [W1s, D0, ArbHeldTimed.prj, CE_eq]; omega
  H_SRV := by
    intro t h
    have ht : t = 4244 ∨ t = 5508 ∨ t = 5796 := by
      exact Classical.byContradiction fun hc => h (by rw [Bool.eq_iff_iff]; simp [W1s]; omega)
    rcases ht with rfl | rfl | rfl
    · exact ⟨4132, by simp [D0, ArbHeldTimed.prj], by simp [W1s], fun v _ _ => by simp [W1s]; omega⟩
    · exact ⟨5396, by simp [D0, ArbHeldTimed.prj], by simp [W1s], fun v _ _ => by simp [W1s]; omega⟩
    · exact ⟨5684, by simp [D0, ArbHeldTimed.prj], by simp [W1s], fun v _ _ => by simp [W1s]; omega⟩

/-- **Non-vacuity of `LinkRel` and `link_caus1`.** LinkExact's witness behaviour at `P0`
(scope, exact conjunction, box) with `Rb = 4300`, `Blo = 380 ≥ 45 ps` (the O6 arc's FAST_MIN),
`U1 = 3521 ≤ 5244` and the node low at 5244 (`P0`'s `V1` = 5021), composed with the run `W1s`
of 7j's `D0` in which A1 rises at 4300 and r1 falls at 5244: all hypotheses of `link_caus1`
hold together, and the causal history has latency 45. (`D0` is corner-mixed: satisfiability
only. The link's node and `W1s`'s r1 are separate traces here; `LinkRel` does not equate
them.) -/
theorem link_caus1_nonvacuous :
    Run D0 W1s ∧ W1s.A1 4300 = true ∧
      (∀ u, 4300 - D0.wfa1 - D0.c1f ≤ u → u < 4300 → W1s.A1 u = false) ∧
      (∀ u, 4300 - D0.wa01 - D0.c1f ≤ u → u < 4244 → W1s.A0 u = false) ∧
      LinkRel 45 4300 5244 ∧ Caus1 D0 W1s 4244 5244 45 ∧ W1s.r1 5243 = true ∧
      W1s.r1 5244 = false := by
  have hlo : ∀ u, 4300 - D0.wfa1 - D0.c1f ≤ u → u < 4300 → W1s.A1 u = false := by
    intro u h1 h2; simp [W1s, D0, ArbHeldTimed.prj] at h1 ⊢; omega
  have h0 : ∀ u, 4300 - D0.wa01 - D0.c1f ≤ u → u < 4244 → W1s.A0 u = false := by
    intro u h1 h2; simp [W1s, D0, ArbHeldTimed.prj] at h1 ⊢; omega
  have hL : LinkRel 45 4300 5244 := by
    obtain ⟨hW, _, hC, _, pa, pb, pq, pr, pd, pe, pf, r, a, b, dd, c, q, hB, hS⟩ :=
      LinkExact.witness true
    refine ⟨LinkExact.P0, true, pa, pb, pq, pr, pd, pe, pf, r, a, b, dd, c, q, hW, hC, hB,
      by decide, by decide, by decide, ?_⟩
    rw [hS.lo 5244 (by decide)]; decide
  exact ⟨W1s_run, by simp [W1s], hlo, h0, hL, link_caus1 (by simp [W1s]) hlo h0 hL,
    by simp [W1s], by simp [W1s]⟩

end link

end Formal.Cells.ArbSettled
