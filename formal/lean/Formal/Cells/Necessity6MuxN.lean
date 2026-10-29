import Formal.Cells.Necessity4MuxN

/-!
# Necessity6MuxN: the boundary of `bdc_muxn.uj_env_latency_req_max`

Probe Bnx6 (shard B). Necessity4MuxN proved the max form of the bdc_muxn join
env latency through the client sufficient (`Nec4.muxn3_ok_staticN`) and the
shipped `S_J_X` not necessary (`Nec4.pass8`), but no boundary run for the max
form: in `Mn3Wit`'s schedule the control return (`S_J_C`) has the same right
side as the max form (10 ticks), so a one-tick violation of the max form
there also breaks `S_J_C`. This file builds a run with a control sender one
tick slower (`Ec = 2`), so that `S_J_C` has one tick more and the max form
alone is off by one.

    S_J_XR i : Lj.hi + wjh ≤ Lj.lo + max Wja.lo ((wo + Lo.lo + Dl + Es) + Wza.lo)
                             + La.lo + Wak.lo + Ex + Wx.lo + s

## Result

* `ClaimN s`: `muxn3_ok_staticN` with `S_J_XR` weakened by `s`, every other
  hypothesis verbatim (gates, environment, causal partners, every other
  `MN3StaticN` field, reset sequencing, the line flush, `1 ≤ N`).
  `claimN0 : ClaimN 0` is the shipped theorem.
* `Mn6.run`: unit LUTs, wires and line (DELAY = 1), every join's feedback
  net 10 ticks, reset held to 11; control tokens select inputs 0, 1, 2, 0, …
  with period 22 (half phase 11); each client raises its request well before
  its token and drops it ONE tick after seeing its ack (`Ex = 1`, tight); the
  control sender moves 2 ticks after seeing ctl_ack (`Ec = 2`, tight); the
  server answers in 1 (`Es = 1`, tight). Real INITs (bd_c2 joins and acks,
  decode LUT3s, `|j` LUT3), every gate relation for all `t`, an open-loop
  periodic environment.
* `failN`, `claimN1_false : ¬ ClaimN 1`: in `Mn6.run` every `MN3StaticN … 1`
  field holds, `S_J_XR` fails by exactly one (`11 = 10 + 1`) for every input,
  `S_J_C` holds with equality (`11 ≤ 11`, so it is met and binding but NOT
  violated), the max is the z_ack branch (`5 > Wja.lo = 1`), reset
  sequencing holds, and the conclusion fails: j_0 is 0 at 42 inside its
  token-0 window `[E 0, E 1) = [32, 43)` (in_0_req's fall reaches uj_0 at 41,
  one tick before the 10-tick net shows j_0's rise).

So `bdc_muxn.uj_env_latency_req_max` is **sufficient +
necessary_at_boundary** (one parameter point, binary `≤` form; the JSON's
strict `+1` is 2 ticks from the refuted point).

## Assumed / proved / NOT covered

Assumed: MuxN3Timed's model (lumped FIFO LUT arcs, window wires, Lt2's
FASTFALL line as FIFO stages, port-level causal partners with minimum
latencies), real (inferred) INITs.
Proved: as above.
NOT covered: an iff over the box; per-pin LUT arcs; the Kleene X `+1`;
DELAY > 1 (`H_FLUSH` is vacuous at `N = 1`).
-/

namespace Formal.Cells.MuxN3Timed
namespace Nec6
open Formal.Cells
open Formal.Cells.OpsTimed
open Formal.Cells.PipeTimed (Ret Trace)
open Formal.Cells.LibCtlMergeMux (c2B)
open Formal.Cells.AMergeGates (or3)
open Formal.Cells.MuxN3Timed.Nec4

/-- The cell's conclusion as `muxn3_ok_staticN` states it. -/
def MN3Concl (P : MN3Run) (j s ak : Nat → Trace) : Prop :=
  (∀ i, i < 3 → Tok (P.Lj i).hi (j i) P.E (P.g i)) ∧
  Tok (ffT P.H P.Tp P.To P.N) (s P.N) P.Z (fun _ => true) ∧
  (∀ i, i < 3 → Tok (P.Ta i) (ak i) (P.XA i) (P.g i) ∧
    Tok (P.Ta i) (ak i) (rx (P.XA i) (P.κ i)) (fun _ => true))

/-- `muxn3_ok_staticN` with `S_J_XR` weakened by `s`, every other hypothesis
verbatim. -/
def ClaimN (sl : Nat) : Prop :=
  ∀ (P : MN3Run) (R : Nat) (Wzc : Ret) (Ex Ec Es wc ls wsj lj wo Dl : Nat) (rst ctl za orj : Trace)
    (x xj cp s0p s1p sl' sj j q jo s ja zx a qa ak : Nat → Trace),
    MN3Gates P rst ctl za x xj cp s0p s1p sl' sj j q jo orj s ja zx a qa ak →
    MN3Env P rst ctl za x s0p s1p R → MN3Causal P Wzc Ex Ec Es →
    MN3StaticN P Wzc Ex Ec Es wc ls wsj lj wo Dl sl →
    (∀ i, i < 3 → (P.Wx i).hi ≤ R ∧ (P.Wc i).hi + (P.Ls i).hi + (P.Wsj i).hi ≤ R ∧
      (P.Lj i).hi + P.wjh i ≤ R ∧ (P.Lj i).hi + (P.Wja i).hi ≤ R ∧ (P.Wza i).hi ≤ R ∧
      (P.La i).hi + P.wah i ≤ R) →
    (∀ i, i < 3 → R ≤ P.Xp i 0 ∧ R ≤ P.D i 0 ∧ R ≤ P.A i 0 ∧ R ≤ P.ZA i 0) →
    (∀ i, 1 ≤ i → i < P.N → ∀ k,
      (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 1)) ≤ (P.Tp i).fst (P.OJ (2 * k + 2)) ∧
      (P.Tp i).fst (P.OJ (2 * k + 1)) ≤ (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 2))) →
    1 ≤ P.N → MN3Concl P j s ak

theorem claimN0 : ClaimN 0 := by
  intro P R Wzc Ex Ec Es wc ls wsj lj wo Dl rst ctl za orj x xj cp s0p s1p sl' sj j q jo s ja zx a qa ak
    G V Cs S hRL hRE hFL hN
  exact muxn3_ok_staticN G V Cs S hRL hRE hFL hN

/-! ## The run: a control sender one tick slower than `Mn3Wit`'s -/
namespace Mn6
open Mn3Wit (svW enum idx_eq)

def run : MN3Run :=
  { Mn3Wit.run with
    wjl := fun _ => 10
    wjh := fun _ => 10
    ξ := fun i j => 66 * (j / 2) + 22 * i + 10 + 30 * (j % 2)
    γ := fun j => 22 * (j / 2) + 28 + 11 * (j % 2)
    ζ := fun j => 22 * (j / 2) + 36 + 11 * (j % 2) }

def rst (t : Nat) : Bool := decide (t < 11)
theorem c2_rst (a b q : Bool) : c2B a b q true = false := by
  cases a <;> cases b <;> cases q <;> decide

-- environment
def x (i t : Nat) : Bool := decide (22 * i + 10 ≤ t ∧ (t - (22 * i + 10)) % 66 < 30)
def ctl (t : Nat) : Bool := decide (28 ≤ t ∧ (t - 28) % 22 < 11)
def za (t : Nat) : Bool := decide (36 ≤ t ∧ (t - 36) % 22 < 11)
def s0d (t : Nat) : Bool := b0 (svW ((t - 28) / 22))
def s1d (t : Nat) : Bool := b1 (svW ((t - 28) / 22))
-- the cell, one tick per primitive, 10-tick join feedback nets
def xj (i t : Nat) : Bool := x i (t - 1)
def cp (_ : Nat) (t : Nat) : Bool := ctl (t - 1)
def s0p (_ : Nat) (t : Nat) : Bool := s0d (t - 1)
def s1p (_ : Nat) (t : Nat) : Bool := s1d (t - 1)
def sl (i t : Nat) : Bool := selF i (s0p i (t - 1)) (s1p i (t - 1)) (cp i (t - 1))
def sj (i t : Nat) : Bool := sl i (t - 1)
def jW (i : Nat) : Nat → Bool
  | t + 11 => c2B (xj i (t + 10)) (sj i (t + 10)) (jW i t) (rst (t + 10))
  | _ => false
def q (i t : Nat) : Bool := jW i (t - 10)
def jo (i t : Nat) : Bool := jW i (t - 1)
def orj (t : Nat) : Bool := or3 (jo 0 (t - 1)) (jo 1 (t - 1)) (jo 2 (t - 1))
def line (n t : Nat) : Bool := orj (t - n)
def ja (i t : Nat) : Bool := jW i (t - 1)
def zx (_ : Nat) (t : Nat) : Bool := za (t - 1)
def aW (i : Nat) : Nat → Bool
  | 0 => false
  | 1 => c2B (ja i 0) (zx i 0) false (rst 0)
  | t + 2 => c2B (ja i (t + 1)) (zx i (t + 1)) (aW i t) (rst (t + 1))
def qa (i t : Nat) : Bool := aW i (t - 1)
def ak (i t : Nat) : Bool := aW i (t - 1)

theorem gates : MN3Gates run rst ctl za x xj cp s0p s1p sl sj jW q jo orj line ja zx aW qa ak where
  H_WX _ _ _ _ := rfl
  H_WC _ _ _ _ := rfl
  H_SEL _ _ _ _ := rfl
  H_WSJ _ _ _ _ := rfl
  H_UJ i _ t ht := by
    match t, ht with
    | 1, _ => exact (c2_rst _ _ _).symm
    | 2, _ => exact (c2_rst _ _ _).symm
    | 3, _ => exact (c2_rst _ _ _).symm
    | 4, _ => exact (c2_rst _ _ _).symm
    | 5, _ => exact (c2_rst _ _ _).symm
    | 6, _ => exact (c2_rst _ _ _).symm
    | 7, _ => exact (c2_rst _ _ _).symm
    | 8, _ => exact (c2_rst _ _ _).symm
    | 9, _ => exact (c2_rst _ _ _).symm
    | 10, _ => exact (c2_rst _ _ _).symm
    | t + 11, _ => rfl
  H_UJ_FB _ _ := fun t ht => by
    have h : 10 ≤ t := ht
    exact ⟨t - 10, by show t ≤ t - 10 + 10; omega, by show t - 10 + 10 ≤ t; omega, rfl⟩
  H_UJ_POS _ _ := Nat.le_of_ble_eq_true rfl
  H_WJO _ _ _ _ := rfl
  H_OR3 _ _ := rfl
  H_LINE := ⟨fun _ _ => rfl, fun i h1 h2 => by
    have : (1 : Nat) ≤ i := h1
    have : i < 1 := h2
    omega⟩
  H_WJA _ _ _ _ := rfl
  H_WZA _ _ _ _ := rfl
  H_UA i _ t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UA_FB _ _ := win11 (fun _ _ => rfl)
  H_UA_POS _ _ := Nat.le_of_ble_eq_true rfl
  H_WAK _ _ _ _ := rfl

/-! Closed forms of the derived edges. -/
theorem Xp_eq (i j : Nat) : run.Xp i j = 66 * (j / 2) + 22 * i + 11 + 30 * (j % 2) := by
  show uW.fst (66 * (j / 2) + 22 * i + 10 + 30 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem Cp_eq (i j : Nat) : run.Cp i j = 22 * (j / 2) + 29 + 11 * (j % 2) := by
  show uW.fst (22 * (j / 2) + 28 + 11 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem Sd_eq (i j : Nat) : run.Sd i j = 22 * (j / 2) + 31 + 11 * (j % 2) := by
  show uW.fst (uW.fst (run.Cp i j)) = _
  rw [Cp_eq, fuW (22 * (j / 2) + 29 + 11 * (j % 2)) (by omega),
    fuW (22 * (j / 2) + 29 + 11 * (j % 2) + 1) (by omega)]; omega
theorem D_eq (i j : Nat) : run.D i j = 66 * (j / 2) + 22 * i + 31 + 11 * (j % 2) := by
  show run.Sd i (2 * (3 * (j / 2) + i) + j % 2) = _; rw [Sd_eq]; omega
theorem c_eq (i j : Nat) : run.c i j = 66 * (j / 2) + 22 * i + 31 + 11 * (j % 2) := by
  show max (run.Xp i j) (run.D i j) = _; rw [Xp_eq, D_eq]; omega
theorem τ_eq (i j : Nat) : run.τ i j = 66 * (j / 2) + 22 * i + 32 + 11 * (j % 2) := by
  show uW.fst (run.c i j) = _; rw [c_eq, fuW _ (by omega)]; omega

theorem E_eq (j : Nat) : run.E j = 22 * (j / 2) + 32 + 11 * (j % 2) := by
  unfold MN3Run.E
  have hs : run.sv (j / 2) = j / 2 % 3 := rfl
  rw [hs, show idx (run.κ (j / 2 % 3)) (j / 2) = j / 2 / 3 from
    idx_eq (j / 2 % 3) (j / 2) (by omega) rfl, τ_eq]
  omega

theorem A_eq (i j : Nat) : run.A i j = run.E j + 1 := by
  show uW.fst (run.E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem ZA_eq (i j : Nat) : run.ZA i j = 22 * (j / 2) + 37 + 11 * (j % 2) := by
  show uW.fst (22 * (j / 2) + 36 + 11 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem Op_eq (i j : Nat) : run.Op i j = run.E j + 1 := by
  show uW.fst (run.E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem OJ_eq (j : Nat) : run.OJ j = run.E j + 2 := by
  show uW.fst (run.Op (run.sv (j / 2)) j) = _
  rw [Op_eq, fuW _ (by omega)]
theorem Z_eq (j : Nat) : run.Z j = run.E j + 3 := by
  show uW.fst (run.OJ j) = _
  rw [OJ_eq, fuW _ (by omega)]
theorem XA_eq (i j : Nat) : run.XA i j = 22 * (j / 2) + 39 + 11 * (j % 2) := by
  have hm : max (run.E j + 1) (22 * (j / 2) + 37 + 11 * (j % 2)) = 22 * (j / 2) + 37 + 11 * (j % 2) := by
    rw [E_eq]; omega
  show uW.fst (uW.fst (max (run.A i j) (run.ZA i j))) = _
  rw [A_eq, ZA_eq, hm, fuW (22 * (j / 2) + 37 + 11 * (j % 2)) (by omega),
    fuW (22 * (j / 2) + 37 + 11 * (j % 2) + 1) (by omega)]; omega

theorem env : MN3Env run rst ctl za x s0p s1p 11 where
  H_RST_HI t h := by simp [rst, h]
  H_RST_LO t h := by simp [rst]; omega
  H_X i _ := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 66 * (0 / 2) + 22 * i + 10 + 30 * (0 % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
    · have h1 : 66 * (2 * k / 2) + 22 * i + 10 + 30 * (2 * k % 2) ≤ t := h1
      have h2 : t < 66 * ((2 * k + 1) / 2) + 22 * i + 10 + 30 * ((2 * k + 1) % 2) := h2
      simp only [x, decide_eq_true_eq]; omega
    · have h1 : 66 * ((2 * k + 1) / 2) + 22 * i + 10 + 30 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 66 * ((2 * k + 2) / 2) + 22 * i + 10 + 30 * ((2 * k + 2) % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
  H_CTL := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 22 * (0 / 2) + 28 + 11 * (0 % 2) := h2
      simp only [ctl, decide_eq_false_iff_not]; omega
    · have h1 : 22 * (2 * k / 2) + 28 + 11 * (2 * k % 2) ≤ t := h1
      have h2 : t < 22 * ((2 * k + 1) / 2) + 28 + 11 * ((2 * k + 1) % 2) := h2
      simp only [ctl, decide_eq_true_eq]; omega
    · have h1 : 22 * ((2 * k + 1) / 2) + 28 + 11 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 22 * ((2 * k + 2) / 2) + 28 + 11 * ((2 * k + 2) % 2) := h2
      simp only [ctl, decide_eq_false_iff_not]; omega
  H_ZA := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 22 * (0 / 2) + 36 + 11 * (0 % 2) := h2
      simp only [za, decide_eq_false_iff_not]; omega
    · have h1 : 22 * (2 * k / 2) + 36 + 11 * (2 * k % 2) ≤ t := h1
      have h2 : t < 22 * ((2 * k + 1) / 2) + 36 + 11 * ((2 * k + 1) % 2) := h2
      simp only [za, decide_eq_true_eq]; omega
    · have h1 : 22 * ((2 * k + 1) / 2) + 36 + 11 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 22 * ((2 * k + 2) / 2) + 36 + 11 * ((2 * k + 2) % 2) := h2
      simp only [za, decide_eq_false_iff_not]; omega
  H_RANGE k := by show k % 3 < 3; omega
  H_ENUM := enum
  H_S_PIN i _ k t h1 h2 := by
    rw [Cp_eq] at h1 h2
    have e : (t - 1 - 28) / 22 = k := by omega
    show b0 (svW ((t - 1 - 28) / 22)) = b0 (svW k) ∧ b1 (svW ((t - 1 - 28) / 22)) = b1 (svW k)
    rw [e]; exact ⟨rfl, rfl⟩

/-- The partners are causal; the clients, the control sender (`Ec = 2`) and
the server are tight. -/
theorem causal : MN3Causal run uW 1 2 1 where
  H_XC_FALL i _ m := by
    rw [XA_eq]; show _ ≤ 66 * ((2 * m + 1) / 2) + 22 * i + 10 + 30 * ((2 * m + 1) % 2)
    show 22 * (2 * (3 * m + i) / 2) + 39 + 11 * (2 * (3 * m + i) % 2) + 1 ≤ _; omega
  H_XC_RISE i _ m := by
    rw [XA_eq]; show _ ≤ 66 * ((2 * m + 2) / 2) + 22 * i + 10 + 30 * ((2 * m + 2) % 2)
    show 22 * ((2 * (3 * m + i) + 1) / 2) + 39 + 11 * ((2 * (3 * m + i) + 1) % 2) + 1 ≤ _; omega
  H_CTL_C j := by
    show uW.fst (22 * (j / 2) + 36 + 11 * (j % 2)) + 2 ≤ 22 * ((j + 1) / 2) + 28 + 11 * ((j + 1) % 2)
    rw [fuW _ (by omega)]; omega
  H_SRV j := by
    rw [Z_eq, E_eq]; show _ ≤ 22 * (j / 2) + 36 + 11 * (j % 2); omega
  H_ES := Nat.le_refl 1
  H_POS j := by show 1 ≤ 22 * (j / 2) + 28 + 11 * (j % 2); omega

/-- Every max-form static obligation, `S_J_XR` weakened by one tick. -/
theorem staticN1 : MN3StaticN run uW 1 2 1 1 1 1 1 1 1 1 where
  H_MIN _ _ := ⟨Nat.le_refl 1, Nat.le_refl 1, Nat.le_refl 1, Nat.le_refl 1, Nat.le_refl 1⟩
  H_DL0 := Nat.le_refl 1
  H_DLT _ _ _ := Nat.le_refl 1
  S_J_XR _ _ := Nat.le_of_ble_eq_true rfl
  S_J_C _ _ := Nat.le_of_ble_eq_true rfl
  S_A_FORK _ _ := Nat.le_of_ble_eq_true rfl
  S_A_RTZ _ _ := Nat.le_of_ble_eq_true rfl
  S_A_J _ _ := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

theorem hRL : ∀ i, i < 3 → (run.Wx i).hi ≤ 11 ∧ (run.Wc i).hi + (run.Ls i).hi + (run.Wsj i).hi ≤ 11 ∧
    (run.Lj i).hi + run.wjh i ≤ 11 ∧ (run.Lj i).hi + (run.Wja i).hi ≤ 11 ∧ (run.Wza i).hi ≤ 11 ∧
    (run.La i).hi + run.wah i ≤ 11 :=
  fun _ _ => ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

theorem hRE : ∀ i, i < 3 → 11 ≤ run.Xp i 0 ∧ 11 ≤ run.D i 0 ∧ 11 ≤ run.A i 0 ∧ 11 ≤ run.ZA i 0 :=
  fun i _ => ⟨by rw [Xp_eq]; omega, by rw [D_eq]; omega, by rw [A_eq, E_eq]; omega,
    by rw [ZA_eq]; omega⟩

theorem hFL : ∀ i, 1 ≤ i → i < run.N → ∀ k,
    (run.H i).fst (ffE run.H run.Tp run.OJ i (2 * k + 1)) ≤ (run.Tp i).fst (run.OJ (2 * k + 2)) ∧
    (run.Tp i).fst (run.OJ (2 * k + 1)) ≤ (run.H i).fst (ffE run.H run.Tp run.OJ i (2 * k + 2)) :=
  fun i h1 h2 => by have : (1 : Nat) ≤ i := h1; have : i < 1 := h2; omega

end Mn6

set_option maxRecDepth 100000 in
/-- **The bdc_muxn max form is necessary at the boundary.** In `Mn6.run`:
every `MN3StaticN … 1` field holds (`S_J_XR` weakened by one tick), `S_J_XR`
fails by exactly one for every input, `S_J_C` holds (with equality), the
max is the z_ack branch, reset sequencing holds, and join 0 is 0 at 42
inside its token-0 window `[E 0, E 1) = [32, 43)`: in_0_req's fall reaches
uj_0 at 41 while the decode is still on and the feedback pin still reads 0
(the net shows j_0's rise only from 42). -/
theorem failN :
    MN3StaticN Mn6.run uW 1 2 1 1 1 1 1 1 1 1 ∧
    (∀ i, i < 3 → (Mn6.run.Lj i).hi + Mn6.run.wjh i = (Mn6.run.Lj i).lo +
      max (Mn6.run.Wja i).lo ((1 + Mn6.run.Lo.lo + 1 + 1) + (Mn6.run.Wza i).lo) + (Mn6.run.La i).lo +
      (Mn6.run.Wak i).lo + 1 + (Mn6.run.Wx i).lo + 1) ∧
    (∀ i, i < 3 → (Mn6.run.Lj i).hi + Mn6.run.wjh i = (Mn6.run.Lj i).lo +
      (1 + Mn6.run.Lo.lo + 1 + 1) + uW.lo + 2 + (Mn6.run.Wc i).lo + (Mn6.run.Ls i).lo + (Mn6.run.Wsj i).lo) ∧
    (∀ i, i < 3 → (Mn6.run.Wja i).lo < (1 + Mn6.run.Lo.lo + 1 + 1) + (Mn6.run.Wza i).lo) ∧
    Mn6.run.E 0 = 32 ∧ Mn6.run.E 1 = 43 ∧
    Mn6.jW 0 31 = false ∧ Mn6.jW 0 32 = true ∧ Mn6.xj 0 41 = false ∧ Mn6.sj 0 41 = true ∧
    Mn6.q 0 41 = false ∧ Mn6.jW 0 42 = false ∧
    ¬ Tok (Mn6.run.Lj 0).hi (Mn6.jW 0) Mn6.run.E (Mn6.run.g 0) ∧
    ¬ MN3Concl Mn6.run Mn6.jW Mn6.line Mn6.ak := by
  have hE0 : Mn6.run.E 0 = 32 := by rw [Mn6.E_eq]
  have hE1 : Mn6.run.E 1 = 43 := by rw [Mn6.E_eq]
  have v : Mn6.jW 0 31 = false ∧ Mn6.jW 0 32 = true ∧ Mn6.xj 0 41 = false ∧ Mn6.sj 0 41 = true ∧
      Mn6.q 0 41 = false ∧ Mn6.jW 0 42 = false := by decide
  have nj : ¬ Tok (Mn6.run.Lj 0).hi (Mn6.jW 0) Mn6.run.E (Mn6.run.g 0) := by
    intro h
    have := h.hi 0 42 (by decide) (by rw [show 2 * 0 = 0 from rfl, hE0]; omega)
      (by rw [show 2 * 0 + 1 = 1 from rfl, hE1]; omega)
    rw [v.2.2.2.2.2] at this; exact absurd this (by decide)
  exact ⟨Mn6.staticN1, fun _ _ => rfl, fun _ _ => rfl, fun _ _ => Nat.le_of_ble_eq_true rfl, hE0, hE1,
    v.1, v.2.1, v.2.2.1, v.2.2.2.1, v.2.2.2.2.1, v.2.2.2.2.2, nj, fun h => nj (h.1 0 (by decide))⟩

/-- Every other hypothesis of `muxn3_ok_staticN` holds in `Mn6.run`, so
`ClaimN 1` is false: weakening the bdc_muxn max form by one tick is unsound. -/
theorem claimN1_false : ¬ ClaimN 1 := by
  intro h
  exact failN.2.2.2.2.2.2.2.2.2.2.2.2.2
    (h Mn6.run 11 uW 1 2 1 1 1 1 1 1 1 Mn6.rst Mn6.ctl Mn6.za Mn6.orj Mn6.x Mn6.xj Mn6.cp Mn6.s0p
      Mn6.s1p Mn6.sl Mn6.sj Mn6.jW Mn6.q Mn6.jo Mn6.line Mn6.ja Mn6.zx Mn6.aW Mn6.qa Mn6.ak
      Mn6.gates Mn6.env Mn6.causal Mn6.staticN1 Mn6.hRL Mn6.hRE Mn6.hFL (Nat.le_refl 1))

end Nec6
end Formal.Cells.MuxN3Timed
