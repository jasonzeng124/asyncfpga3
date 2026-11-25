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
* `ctl` = `¬A0` through `[lo, 10^15]` (`Events8Arb.VCtl`);
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
* `ho2` (§4): an uncontested handover of the real cell (scaled `Events8Arb.ho`: R0 rises 10 steps
  BEFORE the grant) that IS a corrected-core behaviour (`ho2_fix`, with model.py's bands) and is
  NOT an old-core behaviour for ANY bands (`ho2_not_old`, `fix_not_old`).
* §5, **`core_of_settle`** (sufficiency modulo three per-reader timing conditions): the enable is
  CONSTRUCTED from the real traces (`ctlc`: ustate's A0 read shifted by `K`, stalled until `q` has
  settled in the A0-low phase; `σ` = `q`). It is a `VCtl` (`ctlc_vctl`) when no phase stays
  unsettled for longer than `H` (`hstall`, the "no contest" hypothesis in the form the core
  needs), and the enable conditions reduce to `RdOK` per reader: (B1) a reader never loses its
  state term while it reads its request high unless it was already low (RT1 / RT1b); (B2) a
  reader rises only from settled reads (the corrected port protocol, rise side); (C) a request
  fall is read only at unsettled times (fall side).
* §6: `ho3` satisfies every hypothesis of `core_of_settle` (`ho3_fix`) and is no old-core
  behaviour (`settle_not_old`): the theorem is not vacuous, in exactly the D1 situation.

NOT proved: that `Unc W` + B's RT1 / RT1b + the port protocol of the environment give
`hstall` and `RdOK` (each is one inequality between edge times; the gcd_hw instances are not
discharged; `arbfix/member.py` checks the same construction on recorded runs, untrusted), the
link from `CoreOf` to `Events7.HARB7` over a parsed `Net4` (`Events9ArbBeh` states `HARB7'` as
`HARB7` on a certificate of the corrected shape), and that the corrected core's certificates
exist (they do not, with the Events7 log rules: notes §4).
-/

namespace Formal.Core.XAudit.Events9Arb

open Formal.Core.TraceDiscrete (Sig Warp Mono)
open Formal.Core.XAudit.Events2 (cel)
open Formal.Core.XAudit.Events8Arb
open Formal.Core.LutList (o5B o6B)
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
  CoreFix (loCtl B) (10 ^ 15) (rdG (B.g1 0) (B.g1 2) (kOf B)) (rdG (B.g2 1) (B.g2 2) (kOf B))
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
def EnOK (s e y : Sig) (wr wq : Nat → Nat) (K : Nat) (ctl sv : Sig) (br : Bool) (T0 : Nat) : Prop :=
  ∀ t, T0 < t → (En ctl sv br wq K t = true → e (wq t) = true) ∧
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
    (hen : EnOK s e y wr wq K ctl sv br T0) :
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
      obtain ⟨hA, hB, hC⟩ := hen t (by omega)
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
`VCtl (loCtl B) 10^15` of the `A0` source `a`, and selects `sv1 … sv4`, satisfy the enable
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
    (hctl : VCtl (loCtl B) (10 ^ 15) a ctl)
    (e1 : EnOK r1 q g1 (f1 0) (f1 2) (kOf B) ctl sv1 true T0)
    (e2 : EnOK r2 (fun u => !q u) g2 (f2 1) (f2 2) (kOf B) ctl sv2 false T0)
    (e3 : EnOK r1 q (fun t => r1 (fr 0 (t + 2)) && q (fr 2 (t + 2))) (fun t => fr 0 (t + 2))
      (fun t => fr 2 (t + 2)) (kOf B) ctl sv3 true T0)
    (e4 : EnOK r2 (fun u => !q u) (fun t => r2 (fr 1 (t + 2)) && !q (fr 2 (t + 2)))
      (fun t => fr 1 (t + 2)) (fun t => fr 2 (t + 2)) (kOf B) ctl sv4 false T0) :
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
    · simp only [Bho2, h, ite_true]; exact shift_w 15
    · simp only [Bho2, h, ite_false]; exact shift_w 5
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

theorem ctl2_v : VCtl 5 (10 ^ 15) a0h ctl2 := by
  refine ⟨fun t => t - 1, fun t => t - 5, fun t => t - 1, fun u => decide (u = 0), shift1,
    ⟨fun a b hab => by omega, fun t => by omega, fun t => by
      have : (10 : Nat) ^ 15 = 1000000000000000 := by decide
      rw [this]; omega⟩, shift1, by decide, fun x y hxy h => by simp at h ⊢; omega, fun t => ?_⟩
  by_cases h : t - 1 = 0
  · simp only [h, decide_true, ite_true, ctl2]; simp; omega
  · simp only [h, decide_false, Bool.false_eq_true, ite_false, cel1, ctl2, a0h]
    rw [Bool.eq_iff_iff]; simp; omega

def f2h : Fin 3 → Nat → Nat := fun i => if i.val = 2 then (fun t => t - 15) else (fun t => t - 5)

theorem f2h_rd : Rd 3 Bho2.g2 f2h := by
  intro i
  by_cases h : i.val = 2
  · simp only [Bho2, f2h, h, ite_true]; exact shift_w 15
  · simp only [Bho2, f2h, h, ite_false]; exact shift_w 5

theorem en_none (s e y : Sig) (wr wq : Nat → Nat) (K : Nat) (ctl : Sig) (hs : ∀ t, s t = false)
    (_hy : ∀ t, y t = false) (T0 : Nat) : EnOK s e y wr wq K ctl svF true T0 := by
  intro t _
  refine ⟨fun h => by simp [En, svF] at h, fun h => by rw [hs] at h; exact absurd h (by decide),
    fun _ h => by simp [En, svF] at h⟩

/-- **`ho2` IS a corrected-core behaviour**, with model.py's bands computed from its per-pin bands
(`CoreOf Bho2`: `K = 1`, ctl band `[5, 10^15]`), via `core_of_en`: ctl rises at 16 = q flip + K,
`σ` = request 2 throughout. -/
theorem ho2_fix : CoreOf Bho2 lowc oneS a0h R0h2 lowc g2h2 := by
  have hk := kOf_ho2
  have hc : VCtl (loCtl Bho2) (10 ^ 15) a0h ctl2 := by rw [loCtl_ho2]; exact ctl2_v
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
  · exact en_none _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => rfl) _
  · intro t _
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
  · exact en_none _ _ _ _ _ _ _ (fun _ => rfl) (fun _ => by simp [lowc]) _
  · intro t _
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

/-! ## 5. The canonical enable: ctl = "ustate reads A0 low and q has settled"

The enable is built from the real traces alone: ustate time `u` is SETTLED when ustate reads `A0`
low at `u` and `q` keeps its value at `u` for as long as that read stays low. ctl follows ustate's
A0 read (shifted by `K`) at the times that are ok (A0 read high, or settled) and stalls at the
last ok time otherwise; `σ` = the value of `q` at the reader's q-read time. Then `ctl` is a
`VCtl (loCtl B) 10^15` of `A0` as soon as every time is within `H` of an ok time (no phase stays
unsettled for longer than `H`: the "no contest" hypothesis in the form the core needs), and the
enable conditions reduce to three conditions per reader (`RdOK`). -/

section Canon
attribute [local instance] Classical.propDecidable

/-- ustate time `u` is settled. -/
def Settled (a q : Sig) (f4 : Nat → Nat) (u : Nat) : Prop :=
  a (f4 u) = false ∧ ∀ u', u ≤ u' → (∀ w, u ≤ w → w ≤ u' → a (f4 w) = false) → q u' = q u

/-- ustate time `u` is ok: A0 read high, or settled. -/
def Ok (a q : Sig) (f4 : Nat → Nat) (u : Nat) : Prop := a (f4 u) = true ∨ Settled a q f4 u

/-- The canonical ctl warp (at ctl stage step `v`, ustate time `v + 1 − K`). -/
noncomputable def Gc (a q : Sig) (f4 : Nat → Nat) (K : Nat) : Nat → Nat
  | 0 => f4 (1 - K)
  | v + 1 => if Ok a q f4 (v + 2 - K) then f4 (v + 2 - K) else Gc a q f4 K v

/-- ctl's reset: step 0, and every step before the first ok time. -/
noncomputable def rc (a q : Sig) (f4 : Nat → Nat) (K : Nat) : Sig :=
  fun v => decide (v = 0 ∨ ∀ v', v' ≤ v → ¬ Ok a q f4 (v' + 1 - K))

/-- The canonical ctl. -/
noncomputable def ctlc (a q : Sig) (f4 : Nat → Nat) (K : Nat) : Sig :=
  fun s => if rc a q f4 K (s - 1) = true then false else !a (Gc a q f4 K (s - 1))

variable {a q : Sig} {f4 : Nat → Nat} {K : Nat}

theorem settled_step {u : Nat} (h : Settled a q f4 u) (h1 : a (f4 (u + 1)) = false) :
    Settled a q f4 (u + 1) := by
  refine ⟨h1, fun u' hu hw => ?_⟩
  have e1 := h.2 u' (by omega) (fun w hw1 hw2 => by
    by_cases hwu : w = u
    · subst hwu; exact h.1
    · exact hw w (by omega) hw2)
  have e2 := h.2 (u + 1) (by omega) (fun w hw1 hw2 => by
    by_cases hwu : w = u
    · subst hwu; exact h.1
    · have : w = u + 1 := by omega
      subst this; exact h1)
  rw [e1, e2]

theorem gc_ok (v : Nat) (h : Ok a q f4 (v + 1 - K)) : Gc a q f4 K v = f4 (v + 1 - K) := by
  cases v with
  | zero => rfl
  | succ v =>
    have e : v + 1 + 1 - K = v + 2 - K := by omega
    rw [e] at h ⊢
    simp only [Gc, if_pos h]

theorem gc_le (hf : Mono f4) : ∀ v, Gc a q f4 K v ≤ f4 (v + 1 - K) := by
  intro v
  induction v with
  | zero => exact Nat.le_refl _
  | succ v ih =>
    simp only [Gc]
    split
    · have e : v + 1 + 1 - K = v + 2 - K := by omega
      rw [e]; exact Nat.le_refl _
    · have := hf (v + 1 - K) (v + 1 + 1 - K) (by omega); omega

theorem gc_step (hf : Mono f4) (v : Nat) : Gc a q f4 K v ≤ Gc a q f4 K (v + 1) := by
  show Gc a q f4 K v ≤ (if Ok a q f4 (v + 2 - K) then f4 (v + 2 - K) else Gc a q f4 K v)
  split
  · have := gc_le (a := a) (q := q) (K := K) hf v
    have := hf (v + 1 - K) (v + 2 - K) (by omega); omega
  · exact Nat.le_refl _

theorem mono_of_step {f : Nat → Nat} (h : ∀ v, f v ≤ f (v + 1)) : Mono f := by
  intro x y hxy
  induction y with
  | zero => have : x = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ y ih =>
    by_cases hx : x = y + 1
    · subst hx; exact Nat.le_refl _
    · exact Nat.le_trans (ih (by omega)) (h y)

theorem rc_succ_false {v : Nat} (h : rc a q f4 K (v + 1) = false) (hn : ¬ Ok a q f4 (v + 2 - K)) (hv : 1 ≤ v) :
    rc a q f4 K v = false := by
  simp only [rc, decide_eq_false_iff_not, not_or, Classical.not_forall] at h ⊢
  obtain ⟨_, v', hv', hok⟩ := h
  refine ⟨by omega, v', ?_, hok⟩
  by_cases e : v' = v + 1
  · subst e; exact absurd (by have : v + 1 + 1 - K = v + 2 - K := by omega
                              rw [this] at hok; simpa using hok) hn
  · omega

/-- During a stall (not ok, not in reset) ctl's warp sits at a time where A0 is high. -/
theorem gc_stall (hK : 1 ≤ K) : ∀ v, 1 ≤ v → ¬ Ok a q f4 (v + 1 - K) → rc a q f4 K v = false →
    a (Gc a q f4 K v) = true := by
  intro v
  induction v with
  | zero => intro h; omega
  | succ v ih =>
    intro _ hn hr
    have e : v + 1 + 1 - K = v + 2 - K := by omega
    rw [e] at hn
    have hG : Gc a q f4 K (v + 1) = Gc a q f4 K v := by simp only [Gc, if_neg hn]
    rw [hG]
    by_cases hv : v = 0
    · subst hv
      -- rc 1 = false: some v' ≤ 1 is ok; v' = 1 is excluded, so ustate time 1 - K is ok
      simp only [rc, decide_eq_false_iff_not, not_or, Classical.not_forall] at hr
      obtain ⟨_, v', hv', hok⟩ := hr
      simp at hv'
      have hv0 : v' = 0 := by
        by_cases h1 : v' = 1
        · subst h1; exact absurd (by simpa using hok) hn
        · omega
      subst hv0
      have hok' : Ok a q f4 (0 + 1 - K) := by simpa using hok
      rw [show Gc a q f4 K 0 = f4 (1 - K) from rfl]
      rcases hok' with h | h
      · simpa using h
      · -- settled at 1 - K = 0 (K ≥ 1); time 2 - K is then settled too unless A0 is read high there
        have h0 : 0 + 1 - K = 0 := by omega
        rw [h0] at h
        have h2 : 2 - K = 0 ∨ 2 - K = 1 := by omega
        rcases h2 with h2 | h2
        · exact absurd (Or.inr (by rw [h2]; exact h)) hn
        · cases ha : a (f4 (2 - K))
          · have h01 : (0 : Nat) + 1 = 2 - K := by omega
            exact absurd (Or.inr (by rw [← h01]; exact settled_step h (by rw [h01]; exact ha))) hn
          · exact absurd (Or.inl ha) hn
    · have hr' := rc_succ_false hr hn (by omega)
      by_cases hok : Ok a q f4 (v + 1 - K)
      · rw [gc_ok v hok]
        rcases hok with h | h
        · exact h
        · by_cases hs : v + 2 - K = v + 1 - K
          · exact absurd (Or.inr (by rw [hs]; exact h)) hn
          · have hs' : v + 2 - K = v + 1 - K + 1 := by omega
            cases ha : a (f4 (v + 2 - K))
            · exact absurd (Or.inr (by rw [hs']; exact settled_step h (by rw [← hs']; exact ha))) hn
            · exact absurd (Or.inl ha) hn
      · exact ih (by omega) hok hr'

/-- **ctl's value**: at a ctl time `u + K` (`K ≥ 2`), ctl is high iff ustate time `u` is settled. -/
theorem ctlc_iff (hK : 2 ≤ K) (u : Nat) : ctlc a q f4 K (u + K) = true ↔ Settled a q f4 u := by
  have hv : u + K - 1 + 1 - K = u := by omega
  simp only [ctlc]
  by_cases hr : rc a q f4 K (u + K - 1) = true
  · simp only [hr, if_true]
    simp only [rc, decide_eq_true_eq] at hr
    rcases hr with h | h
    · omega
    · have := h (u + K - 1) (Nat.le_refl _); rw [hv] at this
      exact ⟨fun h' => absurd h' (by decide), fun hs => absurd (Or.inr hs) this⟩
  · have hr' : rc a q f4 K (u + K - 1) = false := by simpa using hr
    simp only [hr', Bool.false_eq_true, if_false]
    by_cases hok : Ok a q f4 u
    · rw [gc_ok (u + K - 1) (by rw [hv]; exact hok), hv]
      constructor
      · intro h; rcases hok with h' | h'
        · rw [h'] at h; exact absurd h (by decide)
        · exact h'
      · intro hs; rw [hs.1]; rfl
    · have := gc_stall (a := a) (q := q) (f4 := f4) (by omega) (u + K - 1) (by omega)
        (by rw [hv]; exact hok) hr'
      rw [this]
      exact ⟨fun h => absurd h (by decide), fun hs => absurd (Or.inr hs) hok⟩

/-- **The canonical ctl is a virtual ctl** of `A0`, band `[DA0lo + K − 1, hi]`, if ustate reads
`A0` through a warp `[D0, D1]` and every time is within `H` of an ok time. -/
theorem ctlc_vctl {D0 D1 H hi : Nat} (hf : Warp D0 D1 f4) (hK : 2 ≤ K)
    (hstall : ∀ v, ∃ v', v' ≤ v ∧ v ≤ v' + H ∧ (v' = 0 ∨ Ok a q f4 (v' + 1 - K)))
    (hhi : H + K + D1 ≤ hi) : VCtl (D0 + K - 1) hi a (ctlc a q f4 K) := by
  have hm : Mono (Gc a q f4 K) := mono_of_step (gc_step hf.mono)
  refine ⟨fun t => t - 1, Gc a q f4 K, fun t => t - 1, rc a q f4 K, shift1,
    ⟨hm, fun v => ?_, fun v => ?_⟩, shift1, by simp [rc], fun x y hxy h => ?_, fun t => ?_⟩
  · have h1 := gc_le (a := a) (q := q) (K := K) hf.mono v
    have h2 := hf.le_late (v + 1 - K)
    omega
  · obtain ⟨v', hv', hvH, hok⟩ := hstall v
    have h1 := hm v' v hv'
    have h2 : Gc a q f4 K v' = f4 (v' + 1 - K) := by
      rcases hok with h | h
      · subst h; rfl
      · exact gc_ok v' h
    have h3 := hf.early_le (v' + 1 - K)
    omega
  · simp only [rc, decide_eq_true_eq] at h ⊢
    rcases h with h | h
    · left; omega
    · right; intro v' hv'; exact h v' (by omega)
  · show ctlc a q f4 K t = _
    simp only [ctlc, cel1]

/-- **The three conditions per reader** (against the settledness of ustate times): with the
request read high, (B1) losing the state term means the output was already low [RT1 / RT1b];
(B2) holding the state term at an unsettled time means the output was already high [rise only
from settled reads: the corrected port protocol P-rise]; with the request read low, (C) a settled
state term means the output was already low [a request fall is read only after ustate reads A0
high again: P-fall]. Only times after the settled reset segment `[0, T0]` count. -/
def RdOK (St : Nat → Prop) (s e y : Sig) (wr wq : Nat → Nat) (T0 : Nat) : Prop :=
  ∀ t, T0 < t → (s (wr t) = true → e (wq t) = false → y (t - 2) = false) ∧
    (s (wr t) = true → e (wq t) = true → ¬ St (wq t) → y (t - 2) = true) ∧
    (s (wr t) = false → St (wq t) → e (wq t) = true → y (t - 2) = false)

theorem enOK_of_rd {s e y : Sig} {wr wq : Nat → Nat} {br : Bool} {T0 : Nat} (hK : 2 ≤ K)
    (he : ∀ u, e u = (q u == br)) (h : RdOK (Settled a q f4) s e y wr wq T0) :
    EnOK s e y wr wq K (ctlc a q f4 K) (fun v => q (wq (v + 1))) br T0 := by
  intro t ht
  have hc := ctlc_iff (a := a) (q := q) (f4 := f4) hK (wq t)
  have hE : En (ctlc a q f4 K) (fun v => q (wq (v + 1))) br wq K t = (ctlc a q f4 K (wq t + K) && e (wq t)) := by
    simp only [En]; rw [he]; have : t - 1 + 1 = t := by omega
    rw [this]
  obtain ⟨h1, h2, h3⟩ := h t ht
  rw [hE]
  refine ⟨fun hx => by simp at hx; exact hx.2, fun hs hx => ?_, fun hs hx => ?_⟩
  · cases hev : e (wq t)
    · exact (h1 hs hev).symm
    · rw [hev] at hx; simp at hx
      exact (h2 hs hev (fun hst => by rw [hc.2 hst] at hx; exact absurd hx (by decide))).symm
  · simp at hx; exact h3 hs (hc.1 hx.1) hx.2

end Canon

/-- **`core_of_settle` (sufficiency, modulo three per-reader timing conditions).** A behaviour of
the real `bd_arbiter` core in A's per-pin model (explicit reads in the per-pin bands `B`; ustate
reads `A0` through `f4`, band `B.st 4`), low on `[0, T0 + 2]`, in which no `A0`-low phase stays
unsettled for longer than `H` (every ustate time is within `H` of an ok time), and whose four
readers satisfy `RdOK` (B1 = RT1, B2 = P-rise, C = P-fall, against settledness), is a
behaviour of the corrected core `CoreOf B`, with the canonical ctl `ctlc` and `σ = q`. -/
theorem core_of_settle (B : ArbBands) {r1 r2 rs a q R0 g1 g2 : Sig}
    (fr : Fin 5 → Nat → Nat) (f1 f2 : Fin 3 → Nat → Nat) (f4 : Nat → Nat)
    (hfr : Rd 5 B.r0 fr) (hf1 : Rd 3 B.g1 f1) (hf2 : Rd 3 B.g2 f2) (hf4 : Warp (B.st 4).1 (B.st 4).2 f4)
    (hR0 : ∀ t, R0 t = o5B ARB_ST [r1 (fr 0 t), r2 (fr 1 t), q (fr 2 t), rs (fr 3 t), a (fr 4 t), true])
    (hg1 : ∀ t, g1 t = o5B GRANT [r1 (f1 0 t), r2 (f1 1 t), q (f1 2 t), false, false, true])
    (hg2 : ∀ t, g2 t = o6B GRANT [r1 (f2 0 t), r2 (f2 1 t), q (f2 2 t), false, false, true])
    (T0 : Nat) (hlow : ∀ t, t ≤ T0 + 2 → g1 t = false ∧ g2 t = false ∧ R0 t = false)
    (hb1 : 1 ≤ (B.g1 0).1) (hb2 : 1 ≤ (B.g2 1).1) (hb3 : 3 ≤ (B.r0 0).1) (hb4 : 3 ≤ (B.r0 1).1)
    (hK2 : 2 ≤ kOf B)
    (hq1 : kOf B + 2 ≤ (B.g1 2).1) (hq2 : kOf B + 2 ≤ (B.g2 2).1) (hq3 : kOf B + 4 ≤ (B.r0 2).1)
    (hT1 : (B.g1 2).1 ≤ T0) (hT2 : (B.g2 2).1 ≤ T0) (hT3 : (B.r0 2).1 ≤ T0 + 2)
    (H : Nat) (hstall : ∀ v, ∃ v', v' ≤ v ∧ v ≤ v' + H ∧ (v' = 0 ∨ Ok a q f4 (v' + 1 - kOf B)))
    (hhi : H + kOf B + (B.st 4).2 ≤ 10 ^ 15)
    (e1 : RdOK (Settled a q f4) r1 q g1 (f1 0) (f1 2) T0)
    (e2 : RdOK (Settled a q f4) r2 (fun u => !q u) g2 (f2 1) (f2 2) T0)
    (e3 : RdOK (Settled a q f4) r1 q (fun t => r1 (fr 0 (t + 2)) && q (fr 2 (t + 2)))
      (fun t => fr 0 (t + 2)) (fun t => fr 2 (t + 2)) T0)
    (e4 : RdOK (Settled a q f4) r2 (fun u => !q u) (fun t => r2 (fr 1 (t + 2)) && !q (fr 2 (t + 2)))
      (fun t => fr 1 (t + 2)) (fun t => fr 2 (t + 2)) T0) :
    CoreOf B r1 r2 a R0 g1 g2 := by
  have hc := ctlc_vctl (a := a) (q := q) hf4 hK2 hstall hhi
  have hc' : VCtl (loCtl B) (10 ^ 15) a (ctlc a q f4 (kOf B)) := by
    simp only [loCtl]; exact hc
  have hb1' : ∀ u : Bool, u = (u == true) := fun u => by cases u <;> rfl
  have hb2' : ∀ u : Bool, (!u) = (u == false) := fun u => by cases u <;> rfl
  exact core_of_en B fr f1 f2 hfr hf1 hf2 hR0 hg1 hg2 T0 hlow hb1 hb2 hb3 hb4 hq1 hq2 hq3 hT1 hT2 hT3 hc'
    (enOK_of_rd hK2 (fun u => hb1' (q u)) e1) (enOK_of_rd hK2 (fun u => hb2' (q u)) e2)
    (enOK_of_rd hK2 (fun u => hb1' (q u)) e3) (enOK_of_rd hK2 (fun u => hb2' (q u)) e4)

/-! ## 6. `core_of_settle` is not vacuous: the handover at scale 6 / 18 -/

/-- The handover at a scale with `K = 2`: every read 6 steps, `ugrant`'s `q` pin for `g2` 18.
`A0` falls at 10, `q` at 16, `R0` rises at 22, `g2` at 34. -/
def qh3 : Sig := fun t => decide (t < 16)
def R0h3 : Sig := fun t => decide (22 ≤ t)
def g2h3 : Sig := fun t => decide (34 ≤ t)

def Bho3 : ArbBands where
  st := fun _ => (6, 6)
  r0 := fun _ => (6, 6)
  g1 := fun _ => (6, 6)
  g2 := fun i => if i.val = 2 then (18, 18) else (6, 6)

def f2h3 : Fin 3 → Nat → Nat := fun i => if i.val = 2 then (fun t => t - 18) else (fun t => t - 6)

theorem f2h3_rd : Rd 3 Bho3.g2 f2h3 := by
  intro i
  by_cases h : i.val = 2
  · simp only [Bho3, f2h3, h, ite_true]; exact shift_w 18
  · simp only [Bho3, f2h3, h, ite_false]; exact shift_w 6

theorem ho3_pin : ArbPin Bho3 lowc oneS lowc a0h qh3 R0h3 lowc g2h3 := by
  refine ⟨⟨fun _ t => t - 6, fun _ => shift_w 6, ?_⟩, ⟨fun _ t => t - 6, fun _ => shift_w 6, ?_⟩,
    ⟨fun _ t => t - 6, fun _ => shift_w 6, ?_⟩, ⟨f2h3, f2h3_rd, ?_⟩⟩
  · intro t
    show qh3 t = o6B ARB_ST [lowc (t - 6), oneS (t - 6), qh3 (t - 6), lowc (t - 6), a0h (t - 6), true]
    rw [st_eq]
    simp only [lowc, oneS, qh3, a0h, Bool.false_or]
    by_cases h : t - 6 < 10
    · simp only [h, decide_true, ite_true]; rw [Bool.eq_iff_iff]; simp; omega
    · simp only [h, decide_false, Bool.false_eq_true, ite_false]; rw [Bool.eq_iff_iff]; simp; omega
  · intro t
    show R0h3 t = o5B ARB_ST [lowc (t - 6), oneS (t - 6), qh3 (t - 6), lowc (t - 6), a0h (t - 6), true]
    rw [r0_eq]; simp only [lowc, oneS, qh3, R0h3]; rw [Bool.eq_iff_iff]; simp; omega
  · intro t
    show lowc t = o5B GRANT [lowc (t - 6), oneS (t - 6), qh3 (t - 6), false, false, true]
    rw [g1_eq]; rfl
  · intro t
    show g2h3 t = o6B GRANT [lowc (f2h3 0 t), oneS (f2h3 1 t), qh3 (f2h3 2 t), false, false, true]
    rw [g2_eq]; simp only [oneS, qh3, g2h3, f2h3]; rw [Bool.eq_iff_iff]; simp; omega

theorem settled3 (u : Nat) : Settled a0h qh3 (fun t => t - 6) u ↔ 16 ≤ u := by
  constructor
  · intro h; have := h.1; simp [a0h] at this; omega
  · intro hu
    refine ⟨by simp [a0h]; omega, fun u' hu' _ => ?_⟩
    simp [qh3]; omega

theorem kOf_ho3 : kOf Bho3 = 2 := by decide

/-- **`ho3` satisfies every hypothesis of `core_of_settle`** (canonical ctl, `H = 0`), so it is a
corrected-core behaviour; and it is no old-core behaviour for any bands. -/
theorem ho3_fix : CoreOf Bho3 lowc oneS a0h R0h3 lowc g2h3 := by
  have hS := settled3
  refine core_of_settle Bho3 (q := qh3) (rs := lowc) (fun _ t => t - 6) (fun _ t => t - 6) f2h3
    (fun t => t - 6) (fun _ => shift_w 6) (fun _ => shift_w 6) f2h3_rd (shift_w 6)
    ?_ ?_ ?_ 18 ?_
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) (by decide) (by decide)
    0 ?_ (by decide) ?_ ?_ ?_ ?_
  · intro t
    show R0h3 t = o5B ARB_ST [lowc (t - 6), oneS (t - 6), qh3 (t - 6), lowc (t - 6), a0h (t - 6), true]
    rw [r0_eq]; simp only [lowc, oneS, qh3, R0h3]; rw [Bool.eq_iff_iff]; simp; omega
  · intro t
    show lowc t = o5B GRANT [lowc (t - 6), oneS (t - 6), qh3 (t - 6), false, false, true]
    rw [g1_eq]; rfl
  · intro t
    show g2h3 t = o6B GRANT [lowc (f2h3 0 t), oneS (f2h3 1 t), qh3 (f2h3 2 t), false, false, true]
    rw [g2_eq]; simp only [oneS, qh3, g2h3, f2h3]; rw [Bool.eq_iff_iff]; simp; omega
  · intro t ht
    refine ⟨rfl, ?_, ?_⟩
    · show decide (34 ≤ t) = false
      simp; omega
    · show decide (22 ≤ t) = false
      simp; omega
  · intro v
    refine ⟨v, Nat.le_refl _, by omega, Or.inr ?_⟩
    by_cases hu : 16 ≤ v + 1 - kOf Bho3
    · exact Or.inr ((hS _).2 hu)
    · left; rw [kOf_ho3] at hu ⊢; simp [a0h]; omega
  · intro t _
    exact ⟨fun h => by simp [lowc] at h, fun h => by simp [lowc] at h, fun _ _ _ => rfl⟩
  · intro t _
    have e : f2h3 2 t = t - 18 := rfl
    refine ⟨fun _ h => ?_, fun _ h hn => ?_, fun h => by simp [oneS] at h⟩
    · rw [e] at h; simp [qh3] at h; simp [g2h3]; omega
    · rw [e] at h hn; simp [qh3] at h
      exact absurd ((hS _).2 (by omega)) hn
  · intro t _
    exact ⟨fun h => by simp [lowc] at h, fun h => by simp [lowc] at h, fun _ _ _ => by simp [lowc]⟩
  · intro t _
    refine ⟨fun _ h => ?_, fun _ h hn => ?_, fun h => by simp [oneS] at h⟩
    · simp [qh3] at h; simp [oneS, qh3]; omega
    · have hn' : ¬ Settled a0h qh3 (fun t => t - 6) (t + 2 - 6) := hn
      simp [qh3] at h
      exact absurd ((hS _).2 (by omega)) hn'

theorem ho3_not_old (loF hiF lo1 hi1 lo2 hi2 : Nat) : ¬ VMerge loF hiF lo1 hi1 lo2 hi2 lowc g2h3 R0h3 := by
  intro hv
  rcases vmerge_needs_grant hv (t := 22) (by decide) with ⟨u, _, hu⟩ | ⟨u, hu1, hu⟩
  · simp [lowc] at hu
  · simp [g2h3] at hu; omega

/-- **Sufficiency instance, in Lean**: an uncontested behaviour of the real cell satisfying the
hypotheses of `core_of_settle` (hence a corrected-core behaviour) that is, for every choice of
bands, not an old-core behaviour. -/
theorem settle_not_old : ∃ (B : ArbBands) (r1 r2 rs a q R0 g1 g2 : Sig),
    ArbPin B r1 r2 rs a q R0 g1 g2 ∧ (∀ W, Unc W r1 r2 g1 g2) ∧ CoreOf B r1 r2 a R0 g1 g2 ∧
    ∀ loF hiF lo1 hi1 lo2 hi2, ¬ VMerge loF hiF lo1 hi1 lo2 hi2 g1 g2 R0 :=
  ⟨Bho3, lowc, oneS, lowc, a0h, qh3, R0h3, lowc, g2h3, ho3_pin,
    fun W u _ h _ => by simp [Pend, lowc] at h, ho3_fix, ho3_not_old⟩

end Formal.Core.XAudit.Events9Arb
