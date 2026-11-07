import Formal.Cells.OpsTimedMux

/-!
# Shard B Phase 2, probe Lt (part 3): non-vacuity of `mux_ok` and `merge_ok`

For each cell, one run with every LUT, wire and delay line a unit transport
delay (`Ret.shift 1`, feedback windows `[1, 1]`), reset high on `[0, 4)`,
and open-loop periodic environments whose edges satisfy every timing
obligation. The cell's internal traces are DEFINED by the gate relations
(the C-elements by recursion through their own feedback wire), so the gate
structures hold by definition; every environment hypothesis and every timing
inequality is proved for every token. Control/merged tokens alternate
between the two inputs, and in the mux each input raises its request while
the other input's transaction is still running (it waits at its join).
`*_witness_values` evaluates the simulated traces at a few instants
(kernel `decide`): x_ack pulses in an x token and not in a y token, and
conversely.
-/

namespace Formal.Cells.OpsTimed
open Formal.Cells
open Formal.Cells.PipeTimed (Ret Trace)
open Formal.Cells.LibCtlMergeMux (or2B c2B j0B j1B)

def uW : Ret := Ret.shift 1
theorem fuW (c : Nat) (hc : 1 ≤ c) : uW.fst c = c + 1 := Ret.fst_shift 1 c hc
def svW (k : Nat) : Bool := decide (k % 2 = 1)
def rstW (t : Nat) : Bool := decide (t < 4)

theorem rstW_hi : ∀ t, t < 4 → rstW t = true := fun t h => by simp [rstW, h]
theorem rstW_lo : ∀ t, 4 ≤ t → rstW t = false := fun t h => by simp [rstW]; omega

theorem win11 {x y : Trace} (h : ∀ t, 1 ≤ t → y t = x (t - 1)) : CElemTiming.WinDelay 1 1 x y :=
  fun t ht => ⟨t - 1, by omega, by omega, h t ht⟩

/-! ## The mux -/
namespace MuxWit

def run : MuxRun where
  Wx := uW
  Wy := uW
  Wc0 := uW
  Wc1 := uW
  Lj0 := uW
  Lj1 := uW
  wj0l := 1
  wj0h := 1
  wj1l := 1
  wj1h := 1
  W0o := uW
  W1o := uW
  W0x := uW
  W1y := uW
  Lor := uW
  Dz := uW
  Wzx := uW
  Wzy := uW
  Lxa := uW
  Lya := uW
  wxal := 1
  wxah := 1
  wyal := 1
  wyah := 1
  Wxa := uW
  Wya := uW
  ξ j := 36 * (j / 2) + 4 + 14 * (j % 2)
  η j := 36 * (j / 2) + 22 + 14 * (j % 2)
  γ j := 18 * (j / 2) + 8 + 8 * (j % 2)
  ζ j := 18 * (j / 2) + 14 + 10 * (j % 2)
  sv := svW
  κ0 m := 2 * m
  κ1 m := 2 * m + 1

-- environment
def x (t : Nat) : Bool := decide (4 ≤ t ∧ (t - 4) % 36 < 14)
def y (t : Nat) : Bool := decide (22 ≤ t ∧ (t - 22) % 36 < 14)
def ctl (t : Nat) : Bool := decide (8 ≤ t ∧ (t - 8) % 18 < 8)
def za (t : Nat) : Bool := decide (14 ≤ t ∧ (t - 14) % 18 < 10)
def sx (t : Nat) : Bool := svW ((t - 4) / 18)
-- the cell, one tick per primitive
def xj (t : Nat) : Bool := x (t - 1)
def yj (t : Nat) : Bool := y (t - 1)
def cj (t : Nat) : Bool := ctl (t - 1)
def j0 : Nat → Bool
  | 0 => false
  | 1 => j0B (xj 0) (cj 0) (sx 0) false (rstW 0)
  | t + 2 => j0B (xj (t + 1)) (cj (t + 1)) (sx (t + 1)) (j0 t) (rstW (t + 1))
def q0 (t : Nat) : Bool := j0 (t - 1)
def j1 : Nat → Bool
  | 0 => false
  | 1 => j1B (yj 0) (cj 0) (sx 0) false (rstW 0)
  | t + 2 => j1B (yj (t + 1)) (cj (t + 1)) (sx (t + 1)) (j1 t) (rstW (t + 1))
def q1 (t : Nat) : Bool := j1 (t - 1)
def e0 (t : Nat) : Bool := j0 (t - 1)
def e1 (t : Nat) : Bool := j1 (t - 1)
def ei (t : Nat) : Bool := or2B (e0 (t - 1)) (e1 (t - 1))
def zr (t : Nat) : Bool := ei (t - 1)
def j0x (t : Nat) : Bool := j0 (t - 1)
def j1y (t : Nat) : Bool := j1 (t - 1)
def zx (t : Nat) : Bool := za (t - 1)
def xa : Nat → Bool
  | 0 => false
  | 1 => c2B (j0x 0) (zx 0) false (rstW 0)
  | t + 2 => c2B (j0x (t + 1)) (zx (t + 1)) (xa t) (rstW (t + 1))
def qa (t : Nat) : Bool := xa (t - 1)
def ya : Nat → Bool
  | 0 => false
  | 1 => c2B (j1y 0) (zx 0) false (rstW 0)
  | t + 2 => c2B (j1y (t + 1)) (zx (t + 1)) (ya t) (rstW (t + 1))
def qb (t : Nat) : Bool := ya (t - 1)
def xak (t : Nat) : Bool := xa (t - 1)
def yak (t : Nat) : Bool := ya (t - 1)

theorem gates : MuxGates run rstW x y ctl za xj yj cj cj sx sx j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zx
    xa qa ya qb xak yak where
  H_WX _ _ := rfl
  H_WY _ _ := rfl
  H_WC0 _ _ := rfl
  H_WC1 _ _ := rfl
  H_UJ0 t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UJ0_FB := win11 (fun _ _ => rfl)
  H_UJ0_POS := by decide
  H_UJ1 t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UJ1_FB := win11 (fun _ _ => rfl)
  H_UJ1_POS := by decide
  H_W0O _ _ := rfl
  H_W1O _ _ := rfl
  H_UOR _ _ := rfl
  H_DZ _ _ := rfl
  H_W0X _ _ := rfl
  H_W1Y _ _ := rfl
  H_WZX _ _ := rfl
  H_WZY _ _ := rfl
  H_UXA t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UXA_FB := win11 (fun _ _ => rfl)
  H_UXA_POS := by decide
  H_UYA t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UYA_FB := win11 (fun _ _ => rfl)
  H_UYA_POS := by decide
  H_WXA _ _ := rfl
  H_WYA _ _ := rfl

theorem enum0 : Enum (fun k => !run.sv k) run.κ0 where
  mono m := by show 2 * m < 2 * (m + 1); omega
  hit m := by show (!decide (2 * m % 2 = 1)) = true; simp
  all k h := ⟨k / 2, by
    have h : (!decide (k % 2 = 1)) = true := h
    simp at h; show 2 * (k / 2) = k; omega⟩

theorem enum1 : Enum run.sv run.κ1 where
  mono m := by show 2 * m + 1 < 2 * (m + 1) + 1; omega
  hit m := by show decide ((2 * m + 1) % 2 = 1) = true; simp
  all k h := ⟨k / 2, by
    have h : decide (k % 2 = 1) = true := h
    simp at h; show 2 * (k / 2) + 1 = k; omega⟩

/-! Closed forms of the derived edges. -/
theorem Xp_eq (j : Nat) : run.Xp j = 36 * (j / 2) + 5 + 14 * (j % 2) := by
  show uW.fst (36 * (j / 2) + 4 + 14 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem Yp_eq (j : Nat) : run.Yp j = 36 * (j / 2) + 23 + 14 * (j % 2) := by
  show uW.fst (36 * (j / 2) + 22 + 14 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem C0_eq (j : Nat) : run.C0 j = 18 * (j / 2) + 9 + 8 * (j % 2) := by
  show uW.fst (18 * (j / 2) + 8 + 8 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem C1_eq (j : Nat) : run.C1 j = 18 * (j / 2) + 9 + 8 * (j % 2) := by
  show uW.fst (18 * (j / 2) + 8 + 8 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem D0_eq (j : Nat) : run.D0 j = 36 * (j / 2) + 9 + 8 * (j % 2) := by
  show run.C0 (2 * (2 * (j / 2)) + j % 2) = _; rw [C0_eq]; omega
theorem D1_eq (j : Nat) : run.D1 j = 36 * (j / 2) + 27 + 8 * (j % 2) := by
  show run.C1 (2 * (2 * (j / 2) + 1) + j % 2) = _; rw [C1_eq]; omega
theorem c0_eq (j : Nat) : run.c0 j = 36 * (j / 2) + 9 + 10 * (j % 2) := by
  show max (run.Xp j) (run.D0 j) = _; rw [Xp_eq, D0_eq]; omega
theorem c1_eq (j : Nat) : run.c1 j = 36 * (j / 2) + 27 + 10 * (j % 2) := by
  show max (run.Yp j) (run.D1 j) = _; rw [Yp_eq, D1_eq]; omega
theorem τ0_eq (j : Nat) : run.τ0 j = 36 * (j / 2) + 10 + 10 * (j % 2) := by
  show uW.fst (run.c0 j) = _; rw [c0_eq, fuW _ (by omega)]; omega
theorem τ1_eq (j : Nat) : run.τ1 j = 36 * (j / 2) + 28 + 10 * (j % 2) := by
  show uW.fst (run.c1 j) = _; rw [c1_eq, fuW _ (by omega)]; omega

theorem E_eq (j : Nat) : run.E j = 18 * (j / 2) + 10 + 10 * (j % 2) := by
  unfold MuxRun.E
  rcases Nat.mod_two_eq_zero_or_one (j / 2) with hk | hk
  · have hs : run.sv (j / 2) = false := by show decide (j / 2 % 2 = 1) = false; simp; omega
    have hi : idx run.κ0 (j / 2) = j / 2 / 2 := by
      have := idx_κ enum0 (j / 2 / 2)
      rw [show run.κ0 (j / 2 / 2) = j / 2 by show 2 * (j / 2 / 2) = j / 2; omega] at this
      exact this
    rw [hs, hi]; simp only [Bool.false_eq_true, ite_false]; rw [τ0_eq]; omega
  · have hs : run.sv (j / 2) = true := by show decide (j / 2 % 2 = 1) = true; simp; omega
    have hi : idx run.κ1 (j / 2) = j / 2 / 2 := by
      have := idx_κ enum1 (j / 2 / 2)
      rw [show run.κ1 (j / 2 / 2) = j / 2 by show 2 * (j / 2 / 2) + 1 = j / 2; omega] at this
      exact this
    rw [hs, hi]; simp only [ite_true]; rw [τ1_eq]; omega

theorem env : MuxEnv run rstW x y ctl za sx sx 4 where
  H_RST_HI := rstW_hi
  H_RST_LO := rstW_lo
  H_X := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 36 * (0 / 2) + 4 + 14 * (0 % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
    · have h1 : 36 * (2 * k / 2) + 4 + 14 * (2 * k % 2) ≤ t := h1
      have h2 : t < 36 * ((2 * k + 1) / 2) + 4 + 14 * ((2 * k + 1) % 2) := h2
      simp only [x, decide_eq_true_eq]; omega
    · have h1 : 36 * ((2 * k + 1) / 2) + 4 + 14 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 36 * ((2 * k + 2) / 2) + 4 + 14 * ((2 * k + 2) % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
  H_Y := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 36 * (0 / 2) + 22 + 14 * (0 % 2) := h2
      simp only [y, decide_eq_false_iff_not]; omega
    · have h1 : 36 * (2 * k / 2) + 22 + 14 * (2 * k % 2) ≤ t := h1
      have h2 : t < 36 * ((2 * k + 1) / 2) + 22 + 14 * ((2 * k + 1) % 2) := h2
      simp only [y, decide_eq_true_eq]; omega
    · have h1 : 36 * ((2 * k + 1) / 2) + 22 + 14 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 36 * ((2 * k + 2) / 2) + 22 + 14 * ((2 * k + 2) % 2) := h2
      simp only [y, decide_eq_false_iff_not]; omega
  H_CTL := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 18 * (0 / 2) + 8 + 8 * (0 % 2) := h2
      simp only [ctl, decide_eq_false_iff_not]; omega
    · have h1 : 18 * (2 * k / 2) + 8 + 8 * (2 * k % 2) ≤ t := h1
      have h2 : t < 18 * ((2 * k + 1) / 2) + 8 + 8 * ((2 * k + 1) % 2) := h2
      simp only [ctl, decide_eq_true_eq]; omega
    · have h1 : 18 * ((2 * k + 1) / 2) + 8 + 8 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 18 * ((2 * k + 2) / 2) + 8 + 8 * ((2 * k + 2) % 2) := h2
      simp only [ctl, decide_eq_false_iff_not]; omega
  H_ZA := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 18 * (0 / 2) + 14 + 10 * (0 % 2) := h2
      simp only [za, decide_eq_false_iff_not]; omega
    · have h1 : 18 * (2 * k / 2) + 14 + 10 * (2 * k % 2) ≤ t := h1
      have h2 : t < 18 * ((2 * k + 1) / 2) + 14 + 10 * ((2 * k + 1) % 2) := h2
      simp only [za, decide_eq_true_eq]; omega
    · have h1 : 18 * ((2 * k + 1) / 2) + 14 + 10 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 18 * ((2 * k + 2) / 2) + 14 + 10 * ((2 * k + 2) % 2) := h2
      simp only [za, decide_eq_false_iff_not]; omega
  H_ENUM0 := enum0
  H_ENUM1 := enum1
  H_S_PIN0 k t h1 h2 := by
    rw [C0_eq] at h1 h2
    show svW ((t - 4) / 18) = svW k
    rw [show (t - 4) / 18 = k by omega]
  H_S_PIN1 k t h1 h2 := by
    rw [C1_eq] at h1 h2
    show svW ((t - 4) / 18) = svW k
    rw [show (t - 4) / 18 = k by omega]

theorem O0_eq (j : Nat) : run.O0 j = run.E j + 1 := by
  show uW.fst (run.E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem O1_eq (j : Nat) : run.O1 j = run.E j + 1 := by
  show uW.fst (run.E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem A0_eq (j : Nat) : run.A0 j = run.E j + 1 := by
  show uW.fst (run.E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem A1_eq (j : Nat) : run.A1 j = run.E j + 1 := by
  show uW.fst (run.E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem ZA_eq (j : Nat) : run.ZA0 j = 18 * (j / 2) + 15 + 10 * (j % 2) ∧
    run.ZA1 j = 18 * (j / 2) + 15 + 10 * (j % 2) := by
  constructor <;> (show uW.fst (18 * (j / 2) + 14 + 10 * (j % 2)) = _; rw [fuW _ (by omega)]; omega)

theorem Z_eq (j : Nat) : run.Z j = run.E j + 3 := by
  unfold MuxRun.Z orEdges
  rw [show run.Lor = uW from rfl, show run.Dz = uW from rfl]
  have hE := E_eq j
  split
  · rw [O0_eq, fuW (run.E j + 1) (by omega), fuW (run.E j + 1 + 1) (by omega)]
  · rw [O1_eq, fuW (run.E j + 1) (by omega), fuW (run.E j + 1 + 1) (by omega)]

theorem XA_eq (j : Nat) : run.XA j = 18 * (j / 2) + 17 + 10 * (j % 2) ∧
    run.YA j = 18 * (j / 2) + 17 + 10 * (j % 2) := by
  have hm : max (run.E j + 1) (18 * (j / 2) + 15 + 10 * (j % 2)) = 18 * (j / 2) + 15 + 10 * (j % 2) := by
    rw [E_eq]; omega
  constructor
  · show uW.fst (uW.fst (max (run.A0 j) (run.ZA0 j))) = _
    rw [A0_eq, (ZA_eq j).1, hm, fuW (18 * (j / 2) + 15 + 10 * (j % 2)) (by omega),
      fuW (18 * (j / 2) + 15 + 10 * (j % 2) + 1) (by omega)]; omega
  · show uW.fst (uW.fst (max (run.A1 j) (run.ZA1 j))) = _
    rw [A1_eq, (ZA_eq j).2, hm, fuW (18 * (j / 2) + 15 + 10 * (j % 2)) (by omega),
      fuW (18 * (j / 2) + 15 + 10 * (j % 2) + 1) (by omega)]; omega

/-- The partners are causal: each reacts one tick after the edge it sees. -/
theorem causal : MuxCausal run uW 1 1 1 1 where
  H_XC_FALL m := by
    rw [(XA_eq _).1]; show _ ≤ 36 * ((2 * m + 1) / 2) + 4 + 14 * ((2 * m + 1) % 2)
    show 18 * (2 * (2 * m) / 2) + 17 + 10 * (2 * (2 * m) % 2) + 1 ≤ _; omega
  H_XC_RISE m := by
    rw [(XA_eq _).1]; show _ ≤ 36 * ((2 * m + 2) / 2) + 4 + 14 * ((2 * m + 2) % 2)
    show 18 * ((2 * (2 * m) + 1) / 2) + 17 + 10 * ((2 * (2 * m) + 1) % 2) + 1 ≤ _; omega
  H_YC_FALL m := by
    rw [(XA_eq _).2]; show _ ≤ 36 * ((2 * m + 1) / 2) + 22 + 14 * ((2 * m + 1) % 2)
    show 18 * (2 * (2 * m + 1) / 2) + 17 + 10 * (2 * (2 * m + 1) % 2) + 1 ≤ _; omega
  H_YC_RISE m := by
    rw [(XA_eq _).2]; show _ ≤ 36 * ((2 * m + 2) / 2) + 22 + 14 * ((2 * m + 2) % 2)
    show 18 * ((2 * (2 * m + 1) + 1) / 2) + 17 + 10 * ((2 * (2 * m + 1) + 1) % 2) + 1 ≤ _; omega
  H_CTL_C j := by
    show uW.fst (18 * (j / 2) + 14 + 10 * (j % 2)) + 1 ≤ 18 * ((j + 1) / 2) + 8 + 8 * ((j + 1) % 2)
    rw [fuW _ (by omega)]; omega
  H_SRV j := by
    rw [Z_eq, E_eq]; show _ ≤ 18 * (j / 2) + 14 + 10 * (j % 2); omega
  H_POS j := by show 1 ≤ 18 * (j / 2) + 8 + 8 * (j % 2); omega

/-- Every static per-arc obligation holds with unit delays. -/
theorem static : MuxStatic run uW 1 1 1 1 1 1 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The event-form obligations, here DERIVED from the causal partners and
the static per-arc inequalities (`mux_timing_of_static`). -/
theorem timing : MuxTiming run 4 :=
  mux_timing_of_static enum0 enum1 causal static (by decide) (by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Xp_eq]; omega
    · rw [D0_eq]; omega
    · rw [Yp_eq]; omega
    · rw [D1_eq]; omega
    · rw [A0_eq, E_eq]; omega
    · rw [(ZA_eq 0).1]; omega
    · rw [A1_eq, E_eq]; omega
    · rw [(ZA_eq 0).2]; omega)

/-- **Non-vacuity of `mux_ok`**: the unit-delay run satisfies every
hypothesis, so all its conclusions hold for it. -/
theorem witness :
    Tok run.Lj0.hi j0 run.E (fun k => !run.sv k) ∧ Tok run.Lj1.hi j1 run.E run.sv ∧
    Tok run.Tz zr run.Z (fun _ => true) ∧
    Tok run.Tx xak run.XA (fun k => !run.sv k) ∧ Tok run.Tx xak (rx run.XA run.κ0) (fun _ => true) ∧
    Tok run.Ty yak run.YA run.sv ∧ Tok run.Ty yak (rx run.YA run.κ1) (fun _ => true) ∧
    (∀ m, run.Xp (2 * m) ≤ run.E (2 * run.κ0 m) ∧ run.C0 (2 * run.κ0 m) ≤ run.E (2 * run.κ0 m)) ∧
    (∀ m, run.Yp (2 * m) ≤ run.E (2 * run.κ1 m) ∧ run.C1 (2 * run.κ1 m) ≤ run.E (2 * run.κ1 m)) ∧
    (∀ j, run.ζ j ≤ run.XA j ∧ run.ζ j ≤ run.YA j) :=
  mux_ok gates env timing

/-- The run is not degenerate: token 0 (s = 0) acknowledges x and not y,
token 1 (s = 1) y and not x, and the server sees both transactions; y's
request is already high during x's token (it waits at its join). -/
theorem witness_values :
    xak 17 = true ∧ yak 17 = false ∧ xak 35 = false ∧ yak 35 = true ∧
    zr 13 = true ∧ zr 31 = true ∧ y 24 = true ∧ j1 24 = false := by
  decide

end MuxWit

/-! ## The merge -/
namespace MergeWit

def run : MergeRun where
  Wxo := uW
  Wyo := uW
  Lor := uW
  Dz := uW
  Wxc := uW
  Wyc := uW
  Wzx := uW
  Wzy := uW
  Lxa := uW
  Lya := uW
  wxal := 1
  wxah := 1
  wyal := 1
  wyah := 1
  Wxa := uW
  Wya := uW
  ρ j := 8 * j + 4
  ζ j := 8 * j + 8
  sv := svW

def x (t : Nat) : Bool := decide (4 ≤ t ∧ (t - 4) % 32 < 8)
def y (t : Nat) : Bool := decide (20 ≤ t ∧ (t - 20) % 32 < 8)
def za (t : Nat) : Bool := decide (8 ≤ t ∧ (t - 8) % 16 < 8)
def xo (t : Nat) : Bool := x (t - 1)
def yo (t : Nat) : Bool := y (t - 1)
def ei (t : Nat) : Bool := or2B (xo (t - 1)) (yo (t - 1))
def zr (t : Nat) : Bool := ei (t - 1)
def zx (t : Nat) : Bool := za (t - 1)
def xa : Nat → Bool
  | 0 => false
  | 1 => c2B (xo 0) (zx 0) false (rstW 0)
  | t + 2 => c2B (xo (t + 1)) (zx (t + 1)) (xa t) (rstW (t + 1))
def qa (t : Nat) : Bool := xa (t - 1)
def ya : Nat → Bool
  | 0 => false
  | 1 => c2B (yo 0) (zx 0) false (rstW 0)
  | t + 2 => c2B (yo (t + 1)) (zx (t + 1)) (ya t) (rstW (t + 1))
def qb (t : Nat) : Bool := ya (t - 1)
def xak (t : Nat) : Bool := xa (t - 1)
def yak (t : Nat) : Bool := ya (t - 1)

theorem gates : MergeGates run rstW x y za xo yo ei zr xo yo zx zx xa qa ya qb xak yak where
  H_WXO _ _ := rfl
  H_WYO _ _ := rfl
  H_UOR _ _ := rfl
  H_DZ _ _ := rfl
  H_WXC _ _ := rfl
  H_WYC _ _ := rfl
  H_WZX _ _ := rfl
  H_WZY _ _ := rfl
  H_UXA t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UXA_FB := win11 (fun _ _ => rfl)
  H_UXA_POS := by decide
  H_UYA t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UYA_FB := win11 (fun _ _ => rfl)
  H_UYA_POS := by decide
  H_WXA _ _ := rfl
  H_WYA _ _ := rfl

theorem env : MergeEnv run rstW x y za 4 where
  H_RST_HI := rstW_hi
  H_RST_LO := rstW_lo
  H_X := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 8 * 0 + 4 := h2
      simp only [x, decide_eq_false_iff_not]; omega
    · have h1 : 8 * (2 * k) + 4 ≤ t := h1
      have h2 : t < 8 * (2 * k + 1) + 4 := h2
      show x t = !decide (k % 2 = 1)
      by_cases hk : k % 2 = 1
      · simp only [x, hk, decide_true, Bool.not_true, decide_eq_false_iff_not]; omega
      · simp only [x, hk, decide_false, Bool.not_false, decide_eq_true_eq]; omega
    · have h1 : 8 * (2 * k + 1) + 4 ≤ t := h1
      have h2 : t < 8 * (2 * k + 2) + 4 := h2
      simp only [x, decide_eq_false_iff_not]; omega
  H_Y := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 8 * 0 + 4 := h2
      simp only [y, decide_eq_false_iff_not]; omega
    · have h1 : 8 * (2 * k) + 4 ≤ t := h1
      have h2 : t < 8 * (2 * k + 1) + 4 := h2
      show y t = decide (k % 2 = 1)
      by_cases hk : k % 2 = 1
      · simp only [y, hk, decide_true, decide_eq_true_eq]; omega
      · simp only [y, hk, decide_false, decide_eq_false_iff_not]; omega
    · have h1 : 8 * (2 * k + 1) + 4 ≤ t := h1
      have h2 : t < 8 * (2 * k + 2) + 4 := h2
      simp only [y, decide_eq_false_iff_not]; omega
  H_ZA := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 8 * 0 + 8 := h2
      simp only [za, decide_eq_false_iff_not]; omega
    · have h1 : 8 * (2 * k) + 8 ≤ t := h1
      have h2 : t < 8 * (2 * k + 1) + 8 := h2
      simp only [za, decide_eq_true_eq]; omega
    · have h1 : 8 * (2 * k + 1) + 8 ≤ t := h1
      have h2 : t < 8 * (2 * k + 2) + 8 := h2
      simp only [za, decide_eq_false_iff_not]; omega

theorem XA_eq (j : Nat) : run.XA j = 8 * j + 11 ∧ run.YA j = 8 * j + 11 := by
  constructor
  · show uW.fst (uW.fst (max (uW.fst (8 * j + 4)) (uW.fst (8 * j + 8)))) = _
    rw [fuW (8 * j + 4) (by omega), fuW (8 * j + 8) (by omega),
      show max (8 * j + 4 + 1) (8 * j + 8 + 1) = 8 * j + 9 by omega,
      fuW (8 * j + 9) (by omega), fuW (8 * j + 9 + 1) (by omega)]
  · show uW.fst (uW.fst (max (uW.fst (8 * j + 4)) (uW.fst (8 * j + 8)))) = _
    rw [fuW (8 * j + 4) (by omega), fuW (8 * j + 8) (by omega),
      show max (8 * j + 4 + 1) (8 * j + 8 + 1) = 8 * j + 9 by omega,
      fuW (8 * j + 9) (by omega), fuW (8 * j + 9 + 1) (by omega)]

theorem Z_eq (j : Nat) : run.Z j = 8 * j + 7 := by
  have h0 : run.XO j = 8 * j + 5 := by show uW.fst (8 * j + 4) = _; rw [fuW _ (by omega)]
  have h1 : run.YO j = 8 * j + 5 := by show uW.fst (8 * j + 4) = _; rw [fuW _ (by omega)]
  unfold MergeRun.Z orEdges
  rw [show run.Lor = uW from rfl, show run.Dz = uW from rfl]
  split
  · rw [h0, fuW (8 * j + 5) (by omega), fuW (8 * j + 5 + 1) (by omega)]
  · rw [h1, fuW (8 * j + 5) (by omega), fuW (8 * j + 5 + 1) (by omega)]

/-- The partners are causal: each reacts one tick after the edge it sees. -/
theorem causal : MergeCausal run 1 1 where
  H_OWN j := by
    rw [(XA_eq j).1, (XA_eq j).2]; show _ ≤ 8 * (j + 1) + 4; split <;> omega
  H_SRV j := by rw [Z_eq]; show _ ≤ 8 * j + 8; omega
  H_POS j := by show 1 ≤ 8 * j + 4; omega

theorem static : MergeStatic run 1 1 1 1 1 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The event-form obligations, DERIVED from the causal partners and the
static per-arc inequalities (`merge_timing_of_static`). -/
theorem timing : MergeTiming run 4 :=
  merge_timing_of_static causal static (by decide) (by
    refine ⟨?_, ?_, ?_, ?_⟩
    · show 4 ≤ uW.fst (8 * 0 + 4); rw [fuW (8 * 0 + 4) (by omega)]; omega
    · show 4 ≤ uW.fst (8 * 0 + 8); rw [fuW (8 * 0 + 8) (by omega)]; omega
    · show 4 ≤ uW.fst (8 * 0 + 4); rw [fuW (8 * 0 + 4) (by omega)]; omega
    · show 4 ≤ uW.fst (8 * 0 + 8); rw [fuW (8 * 0 + 8) (by omega)]; omega)

/-- **Non-vacuity of `merge_ok`.** -/
theorem witness :
    Tok run.Tz zr run.Z (fun _ => true) ∧
    Tok run.Tx xak run.XA (fun k => !run.sv k) ∧ Tok run.Ty yak run.YA run.sv ∧
    (∀ j, run.ρ j ≤ run.Z j ∧ run.ζ j ≤ run.XA j ∧ run.ζ j ≤ run.YA j) :=
  merge_ok gates env timing

theorem witness_values :
    xak 11 = true ∧ yak 11 = false ∧ xak 27 = false ∧ yak 27 = true ∧ zr 7 = true ∧ zr 23 = true := by
  decide

end MergeWit

end Formal.Cells.OpsTimed
