import Formal.Core.XAudit.Events8Arb

/-!
# Formal.Core.XAudit.Events9Arb — the CORRECTED virtual arbiter core, at cell level

Probe E8ArbFix (shard A). See `formal/notes/A-e8arbfix.md`.

`Events8Arb.unc_not_harb` refutes the virtual arbiter core of `HARB7` as events4/model.py built
it (R0 an OR of the grants read after them, D1; ctl 2 steps late, D2). This file states the
corrected core that events4/model.py now builds (`build_arb_fix`), in the shape of the `ND7`
equations of its virtual nodes:

* every virtual node has stage band `F = (1,1)` and own-value band `Q = (1,1)` (the whole read
  sits in the pin bands: a common stage warp cannot factor two independent per-pin reads);
* `ctl` = `¬A0` through `[lo, 10^12]` (`Events8Arb.VCtl`);
* each READER of the arbiter state (grant 1, grant 2, and two SHADOW grants, one per R0 term) is a
  virtual two-pin C-element `VRd` (request pin, filtered ctl pin with its OWN band);
* `R0` = merge of the two shadows, stage and taps `(1,1)` (`Events8Arb.VMerge 1 1 1 1 1 1`).

Proved here:

* `cel2_eval`, **`and_cel`**: a real reader `y t = s (wr t) && e (wq t)` (one LUT term reading
  its request and the state through two independent warps) is a `VRd` node whose ctl pin reads
  `ctl` at `wq t + K`, for ANY `ctl`, `σ`, provided three pointwise ENABLE conditions hold
  (`EnOK`: the enable implies the state term; with the request high and the enable low the
  output holds; with the request low and the enable high the output was low) and the reader is
  low during an initial settled segment.
* **`core_of_en`** (sufficiency modulo the enable): every behaviour of the real `bd_arbiter`
  core in A's per-pin model (`Events8Arb.ArbPin`'s equations, real INITs) whose four readers
  satisfy `EnOK` against one `ctl` (a `VCtl` of `A0`) is a behaviour of the corrected core
  (`CoreFix`, bands from the real per-pin bands by the formulas of model.py).
* `ho2`: an uncontested handover of the real cell (scaled `Events8Arb.ho`: R0 rises 10 steps
  BEFORE the grant) that IS a corrected-core behaviour (`ho2_fix`, with model.py's bands) and is
  NOT an old-core behaviour for ANY bands (`ho2_not_old`).

NOT proved: that `Unc W` + B's RT1 / RT1b + a port protocol give a `ctl` and `σ` with `EnOK`
(the round construction; statement in `Wip/E8Arb/Sufficiency.lean`), the link from `CoreFix` to
`Events7.HARB7` over a parsed `Net4` (the netlist-level wrapper is `Events9ArbBeh`), and that
the corrected core's certificates exist (they do not, with the Events7 log rules: notes §4).
-/

namespace Formal.Core.XAudit.Events9Arb

open Formal.Core.TraceDiscrete (Sig Warp Mono)
open Formal.Core.XAudit.Events2 (cel)
open Formal.Core.XAudit.Events8Arb
open Formal.Cells (o5B o6B)
open Formal.Cells.ArbBinary (ARB_ST GRANT)

/-! ## 1. The corrected core -/

/-- **A virtual reader node** of the corrected core (`ND7` of a two-pin non-merge virtual node,
reset value 0, `F = Q = (1,1)`): pin 0 = request source `s` through `GR` (band `[loR, hiR]`), pin
1 = the filtered `ctl` pin `ctl·[σ = br]` through `GC` (band `[loC, hiC]`). -/
def VRd (loR hiR loC hiC : Nat) (br : Bool) (s ctl y : Sig) : Prop :=
  ∃ (F GR GC Q : Nat → Nat) (r sv : Sig), Warp 1 1 F ∧ Warp loR hiR GR ∧ Warp loC hiC GC ∧
    Warp 1 1 Q ∧ r 0 = true ∧ (∀ x y, x ≤ y → r y = true → r x = true) ∧
    ∀ t, y t = if r (F t) then false else
      cel (fun p : Fin 2 => if p.val = 0 then s (GR (F t)) else (ctl (GC (F t)) && (sv (F t) == br)))
        (y (Q (F t)))

/-- Bands of one reader: request pin, ctl pin. -/
structure RdB where
  loR : Nat
  hiR : Nat
  loC : Nat
  hiC : Nat

/-- **The corrected virtual core** with ctl band `[lo, hi]` and reader bands `bg1 bg2` (grants)
`bs1 bs2` (shadows): there are `ctl` and two shadow signals such that `ctl` is a `VCtl` of the
`A0` source `a`, each grant and shadow is a `VRd` on its request (branch `true` for request 1),
and `R0` is the `(1,1)` merge of the shadows. -/
def CoreFix (lo hi : Nat) (bg1 bg2 bs1 bs2 : RdB) (r1 r2 a R0 g1 g2 : Sig) : Prop :=
  ∃ ctl s1 s2 : Sig, VCtl lo hi a ctl ∧
    VRd bg1.loR bg1.hiR bg1.loC bg1.hiC true r1 ctl g1 ∧
    VRd bg2.loR bg2.hiR bg2.loC bg2.hiC false r2 ctl g2 ∧
    VRd bs1.loR bs1.hiR bs1.loC bs1.hiC true r1 ctl s1 ∧
    VRd bs2.loR bs2.hiR bs2.loC bs2.hiC false r2 ctl s2 ∧
    VMerge 1 1 1 1 1 1 s1 s2 R0

/-- The corrected core's offset `K` (model.py `build_arb_fix`): ctl edges sit `K` after the state
flip they stand for. `Dq(X)` = the per-pin band of reader X's `q` pin (`ArbBands` index 2). -/
def kOf (B : ArbBands) : Nat := min (min (B.g1 2).1 (B.g2 2).1) ((B.r0 2).1 - 2) - 2

/-- ctl band lower end: `DA0 + K − 1`, `DA0` = `ustate`'s `A0` pin (index 4). -/
def loCtl (B : ArbBands) : Nat := (B.st 4).1 + kOf B - 1

/-- Reader bands of model.py: grants `Dr − 1`, `Dq − K − 1`; shadows `Dr − 3`, `Dq − K − 3`. -/
def rdG (br bq : Nat × Nat) (K : Nat) : RdB := ⟨br.1 - 1, br.2 - 1, bq.1 - K - 1, bq.2 - K - 1⟩
def rdS (br bq : Nat × Nat) (K : Nat) : RdB := ⟨br.1 - 3, br.2 - 3, bq.1 - K - 3, bq.2 - K - 3⟩

/-- The corrected core of a real cell with per-pin bands `B` (model.py's formulas). -/
def CoreOf (B : ArbBands) (r1 r2 a R0 g1 g2 : Sig) : Prop :=
  CoreFix (loCtl B) (10 ^ 12) (rdG (B.g1 0) (B.g1 2) (kOf B)) (rdG (B.g2 1) (B.g2 2) (kOf B))
    (rdS (B.r0 0) (B.r0 2) (kOf B)) (rdS (B.r0 1) (B.r0 2) (kOf B)) r1 r2 a R0 g1 g2

/-! ## 2. One reader: an AND term is a virtual C-element under the enable conditions -/

theorem cel2_eval (x y q : Bool) :
    cel (fun p : Fin 2 => if p.val = 0 then x else y) q = (if x = y then x else q) := by
  unfold cel
  cases x <;> cases y <;> cases q <;> simp [Fin.forall_fin_two]

/-- The enable `ctl·[σ = br]` as the reader sees it at its step `t` (ctl read at `wq t + K`,
`σ` at the stage step `t − 1`). -/
def En (ctl sv : Sig) (br : Bool) (wq : Nat → Nat) (K t : Nat) : Bool :=
  ctl (wq t + K) && (sv (t - 1) == br)

/-- **The enable conditions** of one reader `y t = s (wr t) && e (wq t)`:
(A) the enable implies the state term; (B) request high, enable low: the output holds its value
of 2 steps before; (C) request low, enable high: the output was low 2 steps before. -/
def EnOK (s e y : Sig) (wr wq : Nat → Nat) (K : Nat) (ctl sv : Sig) (br : Bool) : Prop :=
  ∀ t, (En ctl sv br wq K t = true → e (wq t) = true) ∧
    (s (wr t) = true → En ctl sv br wq K t = false → e (wq t) = y (t - 2)) ∧
    (s (wr t) = false → En ctl sv br wq K t = true → y (t - 2) = false)

theorem shift1 : Warp 1 1 (fun t => t - 1) :=
  ⟨fun a b hab => by omega, fun t => by omega, fun t => by omega⟩

/-- **`and_cel`**: a real reader `y t = s (wr t) && e (wq t)` (request warp `[Lr, Hr]`, state warp
`[Lq, Hq]`), low on `[0, T0]` with `Lq ≤ T0`, satisfying the enable conditions against `ctl`, `sv`,
is a virtual reader `VRd (Lr−1) (Hr−1) (Lq−K−1) (Hq−K−1)` of `ctl`. -/
theorem and_cel {Lr Hr Lq Hq K T0 : Nat} {br : Bool} {s e y ctl sv : Sig} {wr wq : Nat → Nat}
    (hwr : Warp Lr Hr wr) (hwq : Warp Lq Hq wq) (hLr : 1 ≤ Lr) (hLq : K + 2 ≤ Lq) (hT0 : Lq ≤ T0)
    (hy : ∀ t, y t = (s (wr t) && e (wq t))) (hlow : ∀ t, t ≤ T0 → y t = false)
    (hen : EnOK s e y wr wq K ctl sv br) :
    VRd (Lr - 1) (Hr - 1) (Lq - K - 1) (Hq - K - 1) br s ctl y := by
  have hHq : Lq ≤ Hq := by
    have a := hwq.le_late (Hq + Lq); have b := hwq.early_le (Hq + Lq); omega
  refine ⟨fun t => t - 1, fun u => wr (u + 1), fun u => min (wq (u + 1) + K) (u - (Lq - K - 1)),
    fun t => t - 1, fun u => decide (u < T0), sv, shift1, ?_, ?_, shift1, ?_, ?_, ?_⟩
  · refine ⟨fun a b hab => hwr.mono _ _ (by omega), fun u => ?_, fun u => ?_⟩
    · have := hwr.le_late (u + 1); omega
    · have := hwr.early_le (u + 1); omega
  · refine ⟨fun a b hab => ?_, fun u => by omega, fun u => ?_⟩
    · have := hwq.mono (a + 1) (b + 1) (by omega); omega
    · have := hwq.early_le (u + 1); omega
  · simp; omega
  · intro x z hxz h; simp at h ⊢; omega
  · intro t
    by_cases ht : t - 1 < T0
    · simp only [ht, decide_true, ite_true]; exact hlow t (by omega)
    · simp only [ht, decide_false, Bool.false_eq_true, ite_false]
      have h1 : t - 1 + 1 = t := by omega
      have hq := hwq.le_late t
      have hmin : min (wq t + K) (t - 1 - (Lq - K - 1)) = wq t + K := by omega
      rw [h1, hmin, cel2_eval]
      have hE : (ctl (wq t + K) && (sv (t - 1) == br)) = En ctl sv br wq K t := rfl
      rw [hE, hy t]
      obtain ⟨hA, hB, hC⟩ := hen t
      have h2 : t - 1 - 1 = t - 2 := by omega
      rw [h2]
      cases hs : s (wr t) <;> cases hc : En ctl sv br wq K t
      · simp
      · simp; rw [hC hs hc]
      · simp; rw [hB hs hc, hy (t - 2)]
      · simp [hA hc]

/-! ## 3. Sufficiency modulo the enable -/

/-- **`core_of_en`** (sufficiency modulo the enable). Let `q`, `R0`, `g1`, `g2` satisfy the real
`bd_arbiter` LUT equations (real INITs `ARB_ST`, `GRANT`) with explicit per-pin reads
`fr` (`ustate` O5) and `f1`, `f2` (`ugrant` O5 / O6) in the per-pin bands `B` (as in
`Events8Arb.ArbPin`), the outputs low on an initial settled segment `[0, T0 + 2]`, and side
conditions on the bands (lower ends large enough for the offsets). If one `ctl` that is a
`VCtl (loCtl B) 10^12` of the `A0` source `a`, and selects `sv1 … sv4`, satisfy the enable
conditions `EnOK` for the four readers (grant b on `r_b`, `q` / `¬q`; shadow b = R0's term b
two steps later), then the real cell is a behaviour of the corrected core `CoreOf B`. -/
theorem core_of_en (B : ArbBands) {r1 r2 rs a q R0 g1 g2 ctl sv1 sv2 sv3 sv4 : Sig}
    (fr : Fin 5 → Nat → Nat) (f1 f2 : Fin 3 → Nat → Nat)
    (hfr : Rd 5 B.r0 fr) (hf1 : Rd 3 B.g1 f1) (hf2 : Rd 3 B.g2 f2)
    (hR0 : ∀ t, R0 t = o5B ARB_ST [r1 (fr 0 t), r2 (fr 1 t), q (fr 2 t), rs (fr 3 t), a (fr 4 t), true])
    (hg1 : ∀ t, g1 t = o5B GRANT [r1 (f1 0 t), r2 (f1 1 t), q (f1 2 t), false, false, true])
    (hg2 : ∀ t, g2 t = o6B GRANT [r1 (f2 0 t), r2 (f2 1 t), q (f2 2 t), false, false, true])
    (T0 : Nat) (hlow : ∀ t, t ≤ T0 + 2 → g1 t = false ∧ g2 t = false ∧ R0 t = false)
    (hb1 : 1 ≤ (B.g1 0).1) (hb2 : 1 ≤ (B.g2 1).1) (hb3 : 3 ≤ (B.r0 0).1) (hb4 : 3 ≤ (B.r0 1).1)
    (hq1 : kOf B + 2 ≤ (B.g1 2).1) (hq2 : kOf B + 2 ≤ (B.g2 2).1) (hq3 : kOf B + 4 ≤ (B.r0 2).1)
    (hT1 : (B.g1 2).1 ≤ T0) (hT2 : (B.g2 2).1 ≤ T0) (hT3 : (B.r0 2).1 ≤ T0 + 2)
    (hctl : VCtl (loCtl B) (10 ^ 12) a ctl)
    (e1 : EnOK r1 q g1 (f1 0) (f1 2) (kOf B) ctl sv1 true)
    (e2 : EnOK r2 (fun u => !q u) g2 (f2 1) (f2 2) (kOf B) ctl sv2 false)
    (e3 : EnOK r1 q (fun t => r1 (fr 0 (t + 2)) && q (fr 2 (t + 2))) (fun t => fr 0 (t + 2))
      (fun t => fr 2 (t + 2)) (kOf B) ctl sv3 true)
    (e4 : EnOK r2 (fun u => !q u) (fun t => r2 (fr 1 (t + 2)) && !q (fr 2 (t + 2)))
      (fun t => fr 1 (t + 2)) (fun t => fr 2 (t + 2)) (kOf B) ctl sv4 false) :
    CoreOf B r1 r2 a R0 g1 g2 := by
  -- the reads shifted by the shadow's two merge/tap steps are warps of the band minus 2
  have sh2 : ∀ {lo hi : Nat} {f : Nat → Nat}, Warp lo hi f → 2 ≤ lo → Warp (lo - 2) (hi - 2) (fun t => f (t + 2)) :=
    fun {lo hi f} w h2 => ⟨fun x z hxz => w.mono _ _ (by omega),
      fun t => by have := w.le_late (t + 2); omega, fun t => by have := w.early_le (t + 2); omega⟩
  have hL : ∀ {lo hi : Nat} {f : Nat → Nat}, Warp lo hi f → lo ≤ hi := fun {lo hi f} w => by
    have a := w.le_late (hi + lo); have b := w.early_le (hi + lo); omega
  have hR0e : ∀ t, R0 t = ((r1 (fr 0 t) && q (fr 2 t)) || (r2 (fr 1 t) && !q (fr 2 t))) := fun t => by
    rw [hR0 t, r0_eq]
  refine ⟨ctl, fun t => r1 (fr 0 (t + 2)) && q (fr 2 (t + 2)),
    fun t => r2 (fr 1 (t + 2)) && !q (fr 2 (t + 2)), hctl, ?_, ?_, ?_, ?_, ?_⟩
  · exact and_cel (hf1 0) (hf1 2) hb1 hq1 hT1 (fun t => by rw [hg1 t, g1_eq])
      (fun t ht => (hlow t (by omega)).1) e1
  · exact and_cel (e := fun u => !q u) (hf2 1) (hf2 2) hb2 hq2 hT2 (fun t => by rw [hg2 t, g2_eq])
      (fun t ht => (hlow t (by omega)).2.1) e2
  · have h := and_cel (T0 := T0) (sh2 (hfr 0) (by omega)) (sh2 (hfr 2) (by omega)) (by omega)
      (by simp only [kOf] at hq3 ⊢; omega) (by omega) (fun t => rfl)
      (fun t ht => by
        have := hR0e (t + 2); rw [(hlow (t + 2) (by omega)).2.2] at this
        show (r1 (fr 0 (t + 2)) && q (fr 2 (t + 2))) = false
        revert this
        generalize r1 (fr 0 (t + 2)) = x1; generalize q (fr 2 (t + 2)) = x2
        generalize r2 (fr 1 (t + 2)) = x3
        cases x1 <;> cases x2 <;> cases x3 <;> decide) e3
    simp only [rdS]
    have e1' : (B.r0 0).1 - 2 - 1 = (B.r0 0).1 - 3 := by omega
    have e2' : (B.r0 0).2 - 2 - 1 = (B.r0 0).2 - 3 := by omega
    have e3' : (B.r0 2).1 - 2 - kOf B - 1 = (B.r0 2).1 - kOf B - 3 := by omega
    have e4' : (B.r0 2).2 - 2 - kOf B - 1 = (B.r0 2).2 - kOf B - 3 := by omega
    rw [e1', e2', e3', e4'] at h; exact h
  · have h := and_cel (T0 := T0) (e := fun u => !q u) (sh2 (hfr 1) (by omega)) (sh2 (hfr 2) (by omega))
      (by omega) (by simp only [kOf] at hq3 ⊢; omega) (by omega) (fun t => rfl)
      (fun t ht => by
        have := hR0e (t + 2); rw [(hlow (t + 2) (by omega)).2.2] at this
        show (r2 (fr 1 (t + 2)) && !q (fr 2 (t + 2))) = false
        revert this
        generalize r1 (fr 0 (t + 2)) = x1; generalize q (fr 2 (t + 2)) = x2
        generalize r2 (fr 1 (t + 2)) = x3
        cases x1 <;> cases x2 <;> cases x3 <;> decide) e4
    simp only [rdS]
    have e1' : (B.r0 1).1 - 2 - 1 = (B.r0 1).1 - 3 := by omega
    have e2' : (B.r0 1).2 - 2 - 1 = (B.r0 1).2 - 3 := by omega
    have e3' : (B.r0 2).1 - 2 - kOf B - 1 = (B.r0 2).1 - kOf B - 3 := by omega
    have e4' : (B.r0 2).2 - 2 - kOf B - 1 = (B.r0 2).2 - kOf B - 3 := by omega
    rw [e1', e2', e3', e4'] at h; exact h
  · refine ⟨fun t => t - 1, fun t => t - 1, fun t => t - 1, shift1, shift1, shift1, fun t => ?_⟩
    by_cases ht : 2 ≤ t
    · rw [hR0e t]
      have h : t - 1 - 1 + 2 = t := by omega
      simp only [h]
    · rw [(hlow t (by omega)).2.2]
      have := hR0e (t - 1 - 1 + 2); rw [(hlow (t - 1 - 1 + 2) (by omega)).2.2] at this
      show false = ((r1 (fr 0 (t - 1 - 1 + 2)) && q (fr 2 (t - 1 - 1 + 2))) ||
        (r2 (fr 1 (t - 1 - 1 + 2)) && !q (fr 2 (t - 1 - 1 + 2))))
      exact this

/-! ## 4. The scaled handover: refutes the old core, is a corrected-core behaviour -/

/-- The handover `ho` of `Events8Arb` at a scale where the corrected core's offsets fit: every
read takes 5 steps except `ugrant`'s `q` pin for `g2` (15). Request 2 waits from time 0, request 1
never asks, `A0` falls at 10; `q` falls at 15, `R0` rises at 20, `g2` at 30 (R0 10 steps BEFORE
the grant: D1). -/
def qh2 : Sig := fun t => decide (t < 15)
def R0h2 : Sig := fun t => decide (20 ≤ t)
def g2h2 : Sig := fun t => decide (30 ≤ t)

def Bho2 : ArbBands where
  st := fun _ => (5, 5)
  r0 := fun _ => (5, 5)
  g1 := fun _ => (5, 5)
  g2 := fun i => if i.val = 2 then (15, 15) else (5, 5)

theorem ho2_pin : ArbPin Bho2 lowc oneS lowc a0h qh2 R0h2 lowc g2h2 := by
  refine ⟨⟨fun _ t => t - 5, fun _ => shift_w 5, ?_⟩, ⟨fun _ t => t - 5, fun _ => shift_w 5, ?_⟩,
    ⟨fun _ t => t - 5, fun _ => shift_w 5, ?_⟩,
    ⟨fun i => if i.val = 2 then (fun t => t - 15) else (fun t => t - 5), ?_, ?_⟩⟩
  · intro t
    show qh2 t = o6B ARB_ST [lowc (t - 5), oneS (t - 5), qh2 (t - 5), lowc (t - 5), a0h (t - 5), true]
    rw [st_eq]
    simp only [lowc, oneS, qh2, a0h, Bool.false_or]
    by_cases h : t - 5 < 10
    · simp only [h, decide_true, ite_true]; rw [Bool.eq_iff_iff]; simp; omega
    · simp only [h, decide_false, Bool.false_eq_true, ite_false]; rw [Bool.eq_iff_iff]; simp; omega
  · intro t
    show R0h2 t = o5B ARB_ST [lowc (t - 5), oneS (t - 5), qh2 (t - 5), lowc (t - 5), a0h (t - 5), true]
    rw [r0_eq]; simp only [lowc, oneS, qh2, R0h2]; rw [Bool.eq_iff_iff]; simp; omega
  · intro t
    show lowc t = o5B GRANT [lowc (t - 5), oneS (t - 5), qh2 (t - 5), false, false, true]
    rw [g1_eq]; rfl
  · intro i
    by_cases h : i.val = 2
    · simp only [Bho2, h, if_true]; exact shift_w 15
    · simp only [Bho2, h, if_false]; exact shift_w 5
  · intro t
    show g2h2 t = o6B GRANT [lowc (t - 5), oneS (t - 5), qh2 (t - 15), false, false, true]
    rw [g2_eq]; simp only [oneS, qh2, g2h2]; rw [Bool.eq_iff_iff]; simp; omega

/-- `ho2` is uncontested for every window (request 1 is never pending). -/
theorem ho2_unc (W : Nat) : Unc W lowc oneS lowc g2h2 := fun u _ h _ => by
  simp [Pend, lowc] at h

/-- **No old-core R0 matches `ho2`, for ANY bands**: the old virtual R0 is a merge of the grants,
and `R0` rises at 20 while no grant is high before 30. -/
theorem ho2_not_old (loF hiF lo1 hi1 lo2 hi2 : Nat) : ¬ VMerge loF hiF lo1 hi1 lo2 hi2 lowc g2h2 R0h2 := by
  intro hv
  rcases vmerge_needs_grant hv (t := 20) (by decide) with ⟨u, _, hu⟩ | ⟨u, hu1, hu⟩
  · simp [lowc] at hu
  · simp [g2h2] at hu; omega

theorem kOf_ho2 : kOf Bho2 = 1 := by decide
theorem loCtl_ho2 : loCtl Bho2 = 5 := by decide

/-- The corrected core's ctl for `ho2`: rises at 16 = (q flip 15) + K. -/
def ctl2 : Sig := fun t => decide (16 ≤ t)
def svF : Sig := fun _ => false

theorem ctl2_v : VCtl 5 (10 ^ 12) a0h ctl2 := by
  refine ⟨fun t => t - 1, fun t => t - 5, fun t => t - 1, fun u => decide (u = 0), shift1,
    ⟨fun a b hab => by omega, fun t => by omega, fun t => by
      have : (10 : Nat) ^ 12 = 1000000000000 := by decide
      rw [this]; omega⟩, shift1, by decide, fun x y hxy h => by simp at h ⊢; omega, fun t => ?_⟩
  by_cases h : t - 1 = 0
  · simp only [h, decide_true, ite_true, ctl2]; simp; omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, cel1, ctl2, a0h]
    rw [Bool.eq_iff_iff]; simp; omega

def f2h : Fin 3 → Nat → Nat := fun i => if i.val = 2 then (fun t => t - 15) else (fun t => t - 5)

theorem f2h_rd : Rd 3 Bho2.g2 f2h := by
  intro i
  by_cases h : i.val = 2
  · simp only [Bho2, f2h, h, if_true]; exact shift_w 15
  · simp only [Bho2, f2h, h, if_false]; exact shift_w 5

theorem en_none (s e y : Sig) (wr wq : Nat → Nat) (K : Nat) (ctl : Sig) (hs : ∀ t, s t = false)
    (hy : ∀ t, y t = false) : EnOK s e y wr wq K ctl svF true := by
  intro t
  refine ⟨fun h => by simp [En, svF] at h, fun h => by rw [hs] at h; exact absurd h (by decide),
    fun _ h => by simp [En, svF] at h⟩

/-- **`ho2` IS a corrected-core behaviour**, with model.py's bands computed from its per-pin bands
(`CoreOf Bho2`: `K = 1`, ctl band `[5, 10^12]`), via `core_of_en`: ctl rises at 16 = q flip + K,
`σ` = request 2 throughout. -/
theorem ho2_fix : CoreOf Bho2 lowc oneS a0h R0h2 lowc g2h2 := by
  have hk := kOf_ho2
  have hc : VCtl (loCtl Bho2) (10 ^ 12) a0h ctl2 := by rw [loCtl_ho2]; exact ctl2_v
  refine core_of_en Bho2 (q := qh2) (rs := lowc) (ctl := ctl2) (sv1 := svF) (sv2 := svF) (sv3 := svF)
    (sv4 := svF) (fun _ t => t - 5) (fun _ t => t - 5) f2h
    (fun _ => shift_w 5) (fun _ => shift_w 5) f2h_rd ?_ ?_ ?_ 15 ?_
    (by decide) (by decide) (by decide) (by decide) (by rw [hk]; decide) (by rw [hk]; decide)
    (by rw [hk]; decide) (by decide) (by decide) (by decide) hc ?_ ?_ ?_ ?_
  · intro t
    show R0h2 t = o5B ARB_ST [lowc (t - 5), oneS (t - 5), qh2 (t - 5), lowc (t - 5), a0h (t - 5), true]
    rw [r0_eq]; simp only [lowc, oneS, qh2, R0h2]; rw [Bool.eq_iff_iff]; simp; omega
  · intro t
    show lowc t = o5B GRANT [lowc (t - 5), oneS (t - 5), qh2 (t - 5), false, false, true]
    rw [g1_eq]; rfl
  · intro t
    show g2h2 t = o6B GRANT [lowc (t - 5), oneS (t - 5), qh2 (t - 15), false, false, true]
    rw [g2_eq]; simp only [oneS, qh2, g2h2]; rw [Bool.eq_iff_iff]; simp; omega
  · intro t ht
    refine ⟨rfl, ?_, ?_⟩
    · show decide (30 ≤ t) = false
      simp; omega
    · show decide (20 ≤ t) = false
      simp; omega
  · exact en_none _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl)
  · intro t
    rw [hk]
    refine ⟨fun h => ?_, fun _ h => ?_, fun h => by simp [oneS] at h⟩
    · have e : f2h 2 t = t - 15 := rfl
      simp only [En, e, ctl2, svF] at h ⊢
      show (!decide (t - 15 < 15)) = true
      simp at h ⊢; omega
    · have e : f2h 2 t = t - 15 := rfl
      simp only [En, e, ctl2, svF] at h ⊢
      show (!decide (t - 15 < 15)) = decide (30 ≤ t - 2)
      simp at h; rw [Bool.eq_iff_iff]; simp; omega
  · exact en_none _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => by simp [lowc])
  · intro t
    rw [hk]
    refine ⟨fun h => ?_, fun _ h => ?_, fun h => by simp [oneS] at h⟩
    · simp [En, ctl2, svF, qh2] at h ⊢; omega
    · simp [En, ctl2, svF, qh2, oneS] at h ⊢; omega

/-- **The correction matters, in Lean**: an uncontested behaviour of the real cell that is a
corrected-core behaviour and, for every choice of bands, not an old-core (R0 = merge of the
grants) behaviour. -/
theorem fix_not_old : ∃ (B : ArbBands) (r1 r2 rs a q R0 g1 g2 : Sig),
    ArbPin B r1 r2 rs a q R0 g1 g2 ∧ (∀ W, Unc W r1 r2 g1 g2) ∧ CoreOf B r1 r2 a R0 g1 g2 ∧
    ∀ loF hiF lo1 hi1 lo2 hi2, ¬ VMerge loF hiF lo1 hi1 lo2 hi2 g1 g2 R0 :=
  ⟨Bho2, lowc, oneS, lowc, a0h, qh2, R0h2, lowc, g2h2, ho2_pin, ho2_unc, ho2_fix, ho2_not_old⟩

end Formal.Core.XAudit.Events9Arb
