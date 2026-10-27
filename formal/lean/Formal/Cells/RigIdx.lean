import Formal.Cells.RigContract

/-!
# Probe Bri (shard B): `gcd_rig.idx_setup`, sufficient and necessary

Notes: `formal/notes/B-rig-idx.md`.

The constraint `gcd_rig.idx_setup` (cell_constraints.json): the operand
vector, moved by the hk edge that loads `idx`, must have settled at the
frontier latch's `d` pins (and at the direct `a_data`/`b_data` readers that
feed them) at least `su` before the frontier controller's latch enable opens.

`RigContract.idx_setup` states a version of this, but under
`H_TOKEN_STATIC` for the WHOLE window (`aF = 1`, `bF = 0` on
`[e n0 + rhi, e(n0+65536) + rlo)`), which the running ring violates as soon
as the first token is taken (the downstream controller raises `bF`, and
`uenv1` lowers `aF` when `in_ack` rises); it has no non-vacuity witness and no
necessity result. This file restates it:

* `Rig`: the named hypotheses (hk period, rst path band, idx path band, rst
  falls once at `r`, the real `bd_c2n` loop for the frontier controller `F`,
  the enable net `F -> latch en` as a window channel `[enlo, enhi]`). No
  token hypothesis at all: the setup half does not need one.
* `SetupOK`: at every instant `t` of the window after the reset has forced
  the enable low (`t ≥ e n0 + rhi + dlmax + enhi`, `t < e(n0+65536) + vlo`)
  at which the latch enable is high, the latch `d` pins carry the window's
  vector on all of `[t - su, t]`.
* `idx_setup_suff`: `H_IDX_SETUP : vhi + su ≤ 16·Tlo + rlo + dlmin + enlo`
  (with `H_RST_LONG`) gives `SetupOK`, plus the operands' stability on the
  whole window and the enable's forced-low interval.
* `idx_fire`: with the token at F's request only until F's first rise plus
  its loop bound (`H_TOKEN_FIRST`, the form of `gcd_rig.token_static`), F
  rises within `dlmax` of its rst release: the opening exists.
* `cex_rig`, `cex_open`: an explicit run (transport paths at `e n = Tlo·n`,
  F a pure-delay `bd_c2n` loop) satisfying every hypothesis of `Rig` in which
  the enable rises exactly at `e n0 + 16·Tlo + rlo + dlmin + enlo` and the
  operands settle exactly at `e n0 + vhi`.
* `idx_setup_iff`: under side conditions (bands narrower than one hk period,
  `H_RST_LONG_EN`, `H_SHORT`), `SetupOK` for every run satisfying `Rig` holds
  IFF `H_IDX_SETUP`. So the inequality is exact for this obligation.
* `idx_nonvacuous`: at a 7.6 ns hk period with illustrative bands, the run
  `cex_*` satisfies every hypothesis, the enable is high inside the window,
  and the setup conclusion is non-trivial (margin 118 550 ps).

NOT covered: the latch's hold side and the kernel's tolerance of a late
operand (a transparent latch passes a late change; whether the downstream
stages then misread it is the link bundling, not this obligation); routed
numbers; the first window after configuration (`Load` needs `n0 ≥ 65537`).

Core Lean only.
-/

namespace Formal.Cells.RigIdx
open Formal.Cells Formal.Cells.RigContract
open Formal.Cells.CElemTiming (Trace WinDelay exc INIT_c2n c2n_eq)
open Formal.Cells.CTreeTimed (LoopG O_heldG)

/-! ## 1. The hypotheses and the obligation -/

/-- The named hypotheses of the frontier boundary in window `n0`.
`F` = the frontier link controller (`bd_c2n`, real INIT, pins `[aF, bF, q,
rstP]`), `O` its output, `qp` its feedback pin, `En` the latch enable at the
latch, `idxP` the idx-derived operand word at the latch `d` pins. -/
structure Rig (pin : Bool) (vec : Nat) (e : Nat → Nat) (Tlo n0 : Nat)
    (rlo rhi vlo vhi enlo enhi dlmin dlmax dwmin dwmax r : Nat)
    (aF bF rstP O qp En : Trace) (idxP : Nat → Nat) : Prop where
  /-- **H_HK_PERIOD**: every hk period lasts at least `Tlo`. -/
  H_HK_PERIOD : ∀ n, e n + Tlo ≤ e (n + 1)
  /-- **H_LOOP**: F is the real `bd_c2n` INIT in a window-channel loop. -/
  H_LOOP : LoopG (fun t q => exc INIT_c2n (aF t) (bF t) q (rstP t)) O qp dlmin dlmax dwmin dwmax
  /-- **H_PATH_RST**: `rig_rst` -> F's rst pin (tCO(rst_sr) + OR + route + site pin), band `[rlo, rhi]`. -/
  H_PATH_RST : PathOK e rlo rhi (fun n => rigRst (run pin vec n)) rstP
  /-- **H_PATH_IDX**: `idx` -> latch d pins (tCO(idx) + vector decode + route), band `[vlo, vhi]`. -/
  H_PATH_IDX : PathOK e vlo vhi (fun n => (run pin vec n).idx) idxP
  /-- **H_RST_ONE_FALL**: rst at F falls once, at `r`, inside its band. -/
  H_RST_ONE_FALL : e (n0 + 16) + rlo ≤ r ∧ r ≤ e (n0 + 16) + rhi ∧
    (∀ t, e (n0 + 16) + rlo ≤ t → t < r → rstP t = true) ∧
    (∀ t, r ≤ t → t < e (n0 + 16) + rhi → rstP t = false)
  /-- **H_EN**: F's output -> latch enable pin, window channel `[enlo, enhi]`. -/
  H_EN : WinDelay enlo enhi O En

/-- **The obligation `gcd_rig.idx_setup`**: whenever the latch enable is high
in window `n0` (after the reset has forced it low), the `d` pins have carried
the window's vector for at least `su`. -/
def SetupOK (pin : Bool) (vec : Nat) (e : Nat → Nat) (n0 rhi dlmax enhi vlo su : Nat)
    (En : Trace) (idxP : Nat → Nat) : Prop :=
  ∀ t, e n0 + rhi + dlmax + enhi ≤ t → t < e (n0 + 65536) + vlo → En t = true →
    ∀ s, t ≤ s + su → s ≤ t → idxP s = (run pin vec n0).idx

/-! ## 2. Sufficiency -/

section suff
variable {pin : Bool} {vec : Nat} {e : Nat → Nat} {Tlo n0 : Nat}
  {rlo rhi vlo vhi enlo enhi dlmin dlmax dwmin dwmax r su : Nat}
  {aF bF rstP O qp En : Trace} {idxP : Nat → Nat}

/-- rst is high at F from `e n0 + rhi` until its fall `r`. -/
theorem rst_high (R : Rig pin vec e Tlo n0 rlo rhi vlo vhi enlo enhi dlmin dlmax dwmin dwmax r
      aF bF rstP O qp En idxP) (hL : Load n0) :
    ∀ s, e n0 + rhi ≤ s → s < r → rstP s = true := by
  have hL' := hL; unfold Load at hL'
  obtain ⟨_, _, hrHi, _⟩ := R.H_RST_ONE_FALL
  intro s a b
  by_cases hs : s < e (n0 + 16) + rlo
  · exact path_const R.H_PATH_RST true n0 15 (n0 + 16) (by omega)
      (fun m x y => (rr_window hL m x (Nat.lt_of_lt_of_le y (by omega))).2 (by omega)) s a hs
  · exact hrHi s (by omega) b

/-- rst is low at F from `r` until the next window's reset arrives. -/
theorem rst_low (R : Rig pin vec e Tlo n0 rlo rhi vlo vhi enlo enhi dlmin dlmax dwmin dwmax r
      aF bF rstP O qp En idxP) (hL : Load n0) :
    ∀ s, r ≤ s → s < e (n0 + 65536) + rlo → rstP s = false := by
  have hL' := hL; unfold Load at hL'
  obtain ⟨hr1, _, _, hrLo⟩ := R.H_RST_ONE_FALL
  intro s a b
  by_cases hs : s < e (n0 + 16) + rhi
  · exact hrLo s a hs
  · exact path_const R.H_PATH_RST false (n0 + 16) 65519 (n0 + 65536) (by omega)
      (fun m x y => Bool.eq_false_iff.2 (fun hm => by
        have := (rr_window hL m (Nat.le_trans (by omega) x) y).1 hm; omega)) s (by omega) b

/-- **F is held low by the reset** from `e n0 + rhi + dlmax` until
`r + dlmin`, whatever its request, acknowledge and power-up state. -/
theorem F_low (R : Rig pin vec e Tlo n0 rlo rhi vlo vhi enlo enhi dlmin dlmax dwmin dwmax r
      aF bF rstP O qp En idxP) (hL : Load n0)
    (H_RST_LONG : rhi + (dlmax + dwmax) ≤ 16 * Tlo + rlo) :
    ∀ t, e n0 + rhi + dlmax ≤ t → t < r + dlmin → O t = false := by
  have m16 := e_le R.H_HK_PERIOD n0 16 (n0 + 16) rfl
  have hr1 := R.H_RST_ONE_FALL.1
  have hi := rst_high R hL
  intro t h1 h2
  refine O_heldG R.H_LOOP false (e n0 + rhi) r ?_ ?_ t (by omega) h2
  · intro s a b q
    show exc INIT_c2n (aF s) (bF s) q (rstP s) = false
    rw [c2n_eq, hi s a (by omega)]; rfl
  · intro s a b
    show exc INIT_c2n (aF s) (bF s) false (rstP s) = false
    rw [c2n_eq, hi s a b]; rfl

/-- **`gcd_rig.idx_setup`, sufficient.** Given `Rig`, `H_RST_LONG` and
`H_IDX_SETUP : vhi + su ≤ 16·Tlo + rlo + dlmin + enlo`:
(1) `SetupOK`; (2) the operands are the window's vector on
`[e n0 + vhi, e(n0+65536) + vlo)`; (3) F is low on
`[e n0 + rhi + dlmax, r + dlmin)`. No token hypothesis is used. -/
theorem idx_setup_suff (R : Rig pin vec e Tlo n0 rlo rhi vlo vhi enlo enhi dlmin dlmax dwmin dwmax r
      aF bF rstP O qp En idxP) (hL : Load n0)
    (H_RST_LONG : rhi + (dlmax + dwmax) ≤ 16 * Tlo + rlo)
    (H_IDX_SETUP : vhi + su ≤ 16 * Tlo + rlo + dlmin + enlo) :
    SetupOK pin vec e n0 rhi dlmax enhi vlo su En idxP ∧
    (∀ t, e n0 + vhi ≤ t → t < e (n0 + 65536) + vlo → idxP t = (run pin vec n0).idx) ∧
    (∀ t, e n0 + rhi + dlmax ≤ t → t < r + dlmin → O t = false) := by
  have hL' := hL; unfold Load at hL'
  have m16 := e_le R.H_HK_PERIOD n0 16 (n0 + 16) rfl
  have hr1 := R.H_RST_ONE_FALL.1
  have stab : ∀ t, e n0 + vhi ≤ t → t < e (n0 + 65536) + vlo → idxP t = (run pin vec n0).idx :=
    fun t a b => path_const R.H_PATH_IDX _ n0 65535 (n0 + 65536) (by omega)
      (fun m x y => idx_const hL m x y) t a b
  have low := F_low R hL H_RST_LONG
  refine ⟨?_, stab, low⟩
  intro t h1 h2 hEn s hs1 hs2
  obtain ⟨s', a1, a2, eq⟩ := R.H_EN t (by omega)
  rw [eq] at hEn
  by_cases hlt : s' < r + dlmin
  · rw [low s' (by omega) hlt] at hEn; exact absurd hEn (by decide)
  · exact stab s (by omega) (by omega)

/-- **F does open.** With the token at F's request from `e n0 + rhi` until
F's first rise plus its loop bound (`H_TOKEN_FIRST`, the form of
`gcd_rig.token_static`; NOT the whole window), F is high on
`[r + dlmax, r + dlmax + dwmax + dlmin]`. -/
theorem idx_fire (R : Rig pin vec e Tlo n0 rlo rhi vlo vhi enlo enhi dlmin dlmax dwmin dwmax r
      aF bF rstP O qp En idxP) (hL : Load n0)
    (H_HK_POS : 0 < Tlo) (H_RST_LONG : rhi + (dlmax + dwmax) ≤ 16 * Tlo + rlo)
    (H_TOKEN_FIRST : ∀ s, e n0 + rhi ≤ s → s ≤ r + (dlmax + dwmax) → aF s = true ∧ bF s = false) :
    ∀ t, r + dlmax ≤ t → t ≤ r + (dlmax + dwmax) + dlmin → O t = true := by
  have hL' := hL; unfold Load at hL'
  have m16 := e_le R.H_HK_PERIOD n0 16 (n0 + 16) rfl
  have mW := e_le R.H_HK_PERIOD (n0 + 16) 65520 (n0 + 65536) (by omega)
  have hT : 16 * Tlo ≤ 65520 * Tlo := Nat.mul_le_mul_right _ (by omega)
  obtain ⟨hr1, hr2, _, _⟩ := R.H_RST_ONE_FALL
  have F := ResetContract.c2n_frontier R.H_LOOP (e n0 + rhi) r (r + (dlmax + dwmax))
    (rst_high R hL) (by omega) (fun s a b => rst_low R hL s a (by omega))
    H_TOKEN_FIRST (by omega)
  exact F.2

end suff

/-! ## 3. The counter-run: an explicit run satisfying `Rig` -/

theorem div_eq {T n x : Nat} (hT : 0 < T) (h1 : T * n ≤ x) (h2 : x < T * n + T) : x / T = n := by
  apply Nat.le_antisymm
  · exact Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hT).2 (by rw [Nat.succ_mul, Nat.mul_comm]; omega))
  · exact (Nat.le_div_iff_mul_le hT).2 (by rw [Nat.mul_comm]; exact h1)

theorem div_lt {T n x : Nat} (hT : 0 < T) (h : x < T * n) : x / T < n :=
  (Nat.div_lt_iff_lt_mul hT).2 (by rw [Nat.mul_comm]; exact h)

/-- A transport delay `d` from hk edges `e n = T·n` is a `PathOK` with any
band `[lo, hi]` containing `d` that is at most one period wide on each side. -/
theorem pathOK_band {α : Type} (T d lo hi : Nat) (hT : 0 < T) (h1 : lo ≤ d) (h2 : d ≤ hi)
    (h3 : d ≤ lo + T) (h4 : hi ≤ d + T) (v : Nat → α) :
    PathOK (fun n => T * n) lo hi v (fun t => v ((t - d) / T)) := by
  refine ⟨fun n t a b => ?_, fun n t hv a b => ?_⟩
  · simp only at a b; rw [Nat.mul_succ] at b
    show v ((t - d) / T) = v n
    rw [div_eq (n := n) hT (by omega) (by omega)]
  · simp only at a b; rw [Nat.mul_succ] at a b
    show v ((t - d) / T) = v n
    by_cases hc : t < T * n + T + d
    · rw [div_eq (n := n) hT (by omega) (by omega)]
    · rw [div_eq (n := n + 1) hT (by rw [Nat.mul_succ]; omega) (by rw [Nat.mul_succ]; omega), hv]

/-- The counter-run's window: `n0 = 2·65536 + 1`, unpinned, so idx = 2. -/
def n0C : Nat := 131073

theorem load_n0C : Load n0C := by unfold Load n0C; decide

theorem idx_n0C : (run false 0 n0C).idx = 2 := by
  rw [idx_run]; unfold n0C; decide

theorem idx_before (m : Nat) (h : m < n0C) : (run false 0 m).idx ≠ 2 := by
  rw [idx_run]; unfold n0C at h; simp only [Bool.false_eq_true, ite_false]; omega

/-- rst at F: transport `rlo` of `rig_rst`. -/
def rstC (T rlo : Nat) : Trace := fun t => rigRst (run false 0 ((t - rlo) / T))
/-- the operands at the latch: transport `vhi` of `idx`. -/
def idxC (T vhi : Nat) : Nat → Nat := fun t => (run false 0 ((t - vhi) / T)).idx
/-- F's request: the token from the window's edge on; acknowledge 0. -/
def aC (T : Nat) : Trace := fun t => decide (T * n0C ≤ t)
def bC : Trace := fun _ => false
/-- F's output: the excitation `~rst · a` delayed by exactly `dlmin`. -/
def OC (T rlo dlmin : Nat) : Trace := fun t =>
  if t < dlmin then false else (!rstC T rlo (t - dlmin) && aC T (t - dlmin))
def qpC (T rlo dlmin dwmin : Nat) : Trace := fun t =>
  if t < dwmin then false else OC T rlo dlmin (t - dwmin)
def EnC (T rlo dlmin enlo : Nat) : Trace := fun t =>
  if t < enlo then false else OC T rlo dlmin (t - enlo)

theorem n0C_add (T k : Nat) : T * (n0C + k) = T * n0C + T * k := Nat.mul_add _ _ _

/-- **The counter-run satisfies every hypothesis of `Rig`** (no setup
inequality assumed), with `e n = T·n`, `r = T·(n0+16) + rlo`. -/
theorem cex_rig {T rlo rhi vlo vhi enlo enhi dlmin dlmax dwmin dwmax : Nat}
    (hT : 0 < T) (hR : rlo ≤ rhi) (hRn : rhi ≤ rlo + T) (hV : vlo ≤ vhi) (hVn : vhi ≤ vlo + T)
    (hE : enlo ≤ enhi) (hDl : dlmin ≤ dlmax) (hDw : dwmin ≤ dwmax) (hPos : 0 < dlmin + dwmin) :
    Rig false 0 (fun n => T * n) T n0C rlo rhi vlo vhi enlo enhi dlmin dlmax dwmin dwmax
      (T * (n0C + 16) + rlo) (aC T) bC (rstC T rlo) (OC T rlo dlmin) (qpC T rlo dlmin dwmin)
      (EnC T rlo dlmin enlo) (idxC T vhi) := by
  have r16 : rigRst (run false 0 (n0C + 16)) = false :=
    Bool.eq_false_iff.2 (fun hm => by
      have := (rr_window load_n0C (n0C + 16) (by omega) (by omega)).1 hm; omega)
  refine ⟨fun n => Nat.le_of_eq (Nat.mul_succ T n).symm, ?_, pathOK_band T rlo rlo rhi hT (Nat.le_refl _) hR
    (by omega) (by omega) _, pathOK_band T vhi vlo vhi hT hV (Nat.le_refl _) (by omega) (by omega) _,
    ⟨Nat.le_refl _, by omega, fun t a b => absurd b (by omega), fun t a b => ?_⟩, ?_⟩
  · refine ⟨fun t ht => ⟨t - dlmin, by omega, by omega, ?_⟩, fun t ht => ⟨t - dwmin, by omega, by omega, ?_⟩, hPos⟩
    · show OC T rlo dlmin t = exc INIT_c2n (aC T (t - dlmin)) (bC (t - dlmin))
        (qpC T rlo dlmin dwmin (t - dlmin)) (rstC T rlo (t - dlmin))
      rw [c2n_eq]
      unfold OC bC
      rw [if_neg (by omega)]
      cases hq : qpC T rlo dlmin dwmin (t - dlmin)
      · cases aC T (t - dlmin) <;> simp
      · have ha : aC T (t - dlmin) = true := by
          unfold qpC OC at hq
          by_cases h1 : t - dlmin < dwmin
          · rw [if_pos h1] at hq; exact absurd hq (by decide)
          · rw [if_neg h1] at hq
            by_cases h2 : t - dlmin - dwmin < dlmin
            · rw [if_pos h2] at hq; exact absurd hq (by decide)
            · rw [if_neg h2, Bool.and_eq_true] at hq
              have := hq.2; unfold aC at this ⊢; simp only [decide_eq_true_eq] at this ⊢; omega
        rw [ha]; simp
    · show qpC T rlo dlmin dwmin t = OC T rlo dlmin (t - dwmin)
      unfold qpC; rw [if_neg (by omega)]
  · show rigRst (run false 0 ((t - rlo) / T)) = false
    rw [div_eq (n := n0C + 16) hT (by omega) (by rw [n0C_add] at b ⊢; omega)]; exact r16
  · intro t ht
    refine ⟨t - enlo, by omega, by omega, ?_⟩
    show EnC T rlo dlmin enlo t = OC T rlo dlmin (t - enlo)
    unfold EnC; rw [if_neg (by omega)]

/-- **In the counter-run the enable opens exactly at
`T·n0 + 16·T + rlo + dlmin + enlo`**, inside `SetupOK`'s domain. -/
theorem cex_open {T rlo rhi vlo dlmin dlmax dwmax enlo enhi : Nat} (hT : 0 < T)
    (H_RST_LONG_EN : rhi + (dlmax + dwmax) + enhi ≤ 16 * T + rlo)
    (H_SHORT : rlo + dlmin + enlo < 65520 * T + vlo) :
    EnC T rlo dlmin enlo (T * (n0C + 16) + rlo + dlmin + enlo) = true ∧
    T * n0C + rhi + dlmax + enhi ≤ T * (n0C + 16) + rlo + dlmin + enlo ∧
    T * (n0C + 16) + rlo + dlmin + enlo < T * (n0C + 65536) + vlo := by
  have r16 : rigRst (run false 0 (n0C + 16)) = false :=
    Bool.eq_false_iff.2 (fun hm => by
      have := (rr_window load_n0C (n0C + 16) (by omega) (by omega)).1 hm; omega)
  have e1 : T * (n0C + 16) = T * n0C + 16 * T := by rw [n0C_add, Nat.mul_comm T 16]
  have e2 : T * (n0C + 65536) = T * n0C + 65536 * T := by rw [n0C_add, Nat.mul_comm T 65536]
  refine ⟨?_, by omega, by omega⟩
  have hdiv : (T * (n0C + 16) + rlo - rlo) / T = n0C + 16 := by
    rw [Nat.add_sub_cancel, Nat.mul_div_cancel_left _ hT]
  generalize T * (n0C + 16) = X at hdiv e1 ⊢
  unfold EnC OC rstC aC
  rw [if_neg (by omega), if_neg (by omega)]
  have h4 : X + rlo + dlmin + enlo - enlo - dlmin = X + rlo := by
    rw [Nat.add_sub_cancel, Nat.add_sub_cancel]
  rw [h4, hdiv, r16]
  simp only [Bool.not_false, Bool.true_and, decide_eq_true_eq]; omega

/-! ## 4. Exactness -/

/-- **`gcd_rig.idx_setup` is exact.** Under the side conditions (`Tlo > 0`;
ordered bands, each at most one hk period wide; `H_RST_LONG_EN`: F's reset
hold and the enable net settle inside the 16-cycle reset; `H_SHORT`: the
earliest opening is inside the window), `SetupOK` holds for EVERY run
satisfying `Rig` (any hk edge times, any traces, any window, pinned or not)
if and only if `vhi + su ≤ 16·Tlo + rlo + dlmin + enlo`. -/
theorem idx_setup_iff {Tlo rlo rhi vlo vhi su enlo enhi dlmin dlmax dwmin dwmax : Nat}
    (hT : 0 < Tlo) (hR : rlo ≤ rhi) (hRn : rhi ≤ rlo + Tlo) (hV : vlo ≤ vhi) (hVn : vhi ≤ vlo + Tlo)
    (hE : enlo ≤ enhi) (hDl : dlmin ≤ dlmax) (hDw : dwmin ≤ dwmax) (hPos : 0 < dlmin + dwmin)
    (H_RST_LONG_EN : rhi + (dlmax + dwmax) + enhi ≤ 16 * Tlo + rlo)
    (H_SHORT : rlo + dlmin + enlo < 65520 * Tlo + vlo) :
    (∀ (pin : Bool) (vec : Nat) (e : Nat → Nat) (n0 r : Nat) (aF bF rstP O qp En : Trace)
       (idxP : Nat → Nat), Load n0 →
       Rig pin vec e Tlo n0 rlo rhi vlo vhi enlo enhi dlmin dlmax dwmin dwmax r aF bF rstP O qp En idxP →
       SetupOK pin vec e n0 rhi dlmax enhi vlo su En idxP) ↔
    vhi + su ≤ 16 * Tlo + rlo + dlmin + enlo := by
  constructor
  · intro H
    refine Decidable.byContradiction fun hneg => ?_
    have R := cex_rig (enlo := enlo) (enhi := enhi) (dlmax := dlmax) (dwmax := dwmax)
      hT hR hRn hV hVn hE hDl hDw hPos
    have S := H false 0 _ n0C _ _ _ _ _ _ _ _ load_n0C R
    obtain ⟨hO, hd1, hd2⟩ := cex_open (rhi := rhi) (vlo := vlo) (dlmax := dlmax) (dwmax := dwmax)
      (enhi := enhi) hT H_RST_LONG_EN H_SHORT
    have e1 : Tlo * (n0C + 16) = Tlo * n0C + 16 * Tlo := by rw [n0C_add, Nat.mul_comm Tlo 16]
    have hs := S _ hd1 hd2 hO (Tlo * (n0C + 16) + rlo + dlmin + enlo - su) (by omega) (by omega)
    have hpos : Tlo ≤ Tlo * n0C := Nat.le_mul_of_pos_right _ (by unfold n0C; decide)
    apply idx_before ((Tlo * (n0C + 16) + rlo + dlmin + enlo - su - vhi) / Tlo)
      (div_lt hT (by omega))
    rw [← idx_n0C]; exact hs
  · intro H pin vec e n0 r aF bF rstP O qp En idxP hL R
    exact (idx_setup_suff R hL (by omega) H).1

/-! ## 5. Non-vacuity at a 7.6 ns hk period -/

/-- **Non-vacuity.** hk period 7600 ps (`gcd_hw.v`: 27.5 hops at about
275 ps); illustrative bands (NOT routed numbers): rst `[1200, 4800]`, idx
`[900, 4200]`, enable net `[150, 1125]` (the bd_link header's measured
enable-net spread on a routed 32-bit link), F's LUT `[100, 500]`, feedback
wire `[50, 400]`, setup 300. Every hypothesis of `Rig` holds for the run
`cex_*`, `H_IDX_SETUP` holds (margin `121600 + 1200 + 100 + 150 - 4200 - 300 =
118550` ps), the enable is high at an instant inside the window, the
operands there are vector 2 on the whole setup interval, and F fires. -/
theorem idx_nonvacuous :
    Rig false 0 (fun n => 7600 * n) 7600 n0C 1200 4800 900 4200 150 1125 100 500 50 400
      (7600 * (n0C + 16) + 1200) (aC 7600) bC (rstC 7600 1200) (OC 7600 1200 100)
      (qpC 7600 1200 100 50) (EnC 7600 1200 100 150) (idxC 7600 4200) ∧
    4200 + 300 ≤ 16 * 7600 + 1200 + 100 + 150 ∧
    EnC 7600 1200 100 150 (7600 * (n0C + 16) + 1200 + 100 + 150) = true ∧
    7600 * n0C + 4800 + 500 + 1125 ≤ 7600 * (n0C + 16) + 1200 + 100 + 150 ∧
    7600 * (n0C + 16) + 1200 + 100 + 150 < 7600 * (n0C + 65536) + 900 ∧
    (∀ s, 7600 * (n0C + 16) + 1200 + 100 + 150 ≤ s + 300 →
      s ≤ 7600 * (n0C + 16) + 1200 + 100 + 150 → idxC 7600 4200 s = 2) ∧
    OC 7600 1200 100 (7600 * (n0C + 16) + 1200 + 500) = true := by
  have R := cex_rig (T := 7600) (rlo := 1200) (rhi := 4800) (vlo := 900) (vhi := 4200)
    (enlo := 150) (enhi := 1125) (dlmin := 100) (dlmax := 500) (dwmin := 50) (dwmax := 400)
    (by decide) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide) (by decide)
  obtain ⟨hO, hd1, hd2⟩ := cex_open (T := 7600) (rlo := 1200) (rhi := 4800) (vlo := 900)
    (dlmin := 100) (dlmax := 500) (dwmax := 400) (enlo := 150) (enhi := 1125)
    (by decide) (by decide) (by decide)
  have S := idx_setup_suff (su := 300) R load_n0C (by decide) (by decide)
  have e1 : 7600 * (n0C + 16) = 7600 * n0C + 121600 := by rw [n0C_add]
  refine ⟨R, by decide, hO, hd1, hd2, fun s a b => ?_, ?_⟩
  · rw [S.1 _ hd1 hd2 hO s a b, idx_n0C]
  · exact idx_fire R load_n0C (by decide) (by decide)
      (fun s a _ => ⟨decide_eq_true (by generalize n0C = x at *; omega), rfl⟩) _
      (by generalize n0C = x at *; omega) (by generalize n0C = x at *; omega)

end Formal.Cells.RigIdx
