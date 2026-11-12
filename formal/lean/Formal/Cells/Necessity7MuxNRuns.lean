import Formal.Cells.Necessity7MuxN

/-!
# Necessity7MuxNRuns: `bdc_muxn.iso_zack`, the fork form is not necessary

Probe Bnx7 (shard B). Runs for `MN3StaticG` (`Necessity7MuxN`).

`Mn7.run d`: every LUT, wire and feedback net one tick, DELAY = 1, except
the three z_ack → ua_i wires (`Wza i = shift d`). Reset high on `[0, 9)`.
Control token `k` selects input `k % 3`, period 27 per control token;
client `i` raises its request 20 ticks before its token's ctl_req and drops
it 19 ticks after it (slack), the server's fall answer is tight, the control
sender is tight (`Ec = 1`). `Kc = Wzc.lo + Ec + (wc + ls + wsj + lj) = 6`,
`Kz = 4`.

* `passN7`: with `d = 7` the shipped `S_A_FORK` fails (`7 + 2 ≤ 6 + 1` is
  false), every `MN3StaticG` field holds (`S_A_SEQ` with equality,
  `7 ≤ 7`), and `muxn3_ok_gs` gives `muxn3_ok_static`'s conclusion.
* `failSEQ8`, `claimSEQn1_false`: with `d = 8` every `MN3StaticW … 1 0`
  field holds (`S_A_SEQ` weakened by one; unweakened it fails by exactly
  one, `8 = 7 + 1`), and the conclusion fails: z_ack's fall of token 0
  (input 0) reaches ua_1 at 61, j_1's rise of token 1 at 60; ua_1 fires
  inside token 0: in1_ack is 1 at 62, inside `[XA 1 0, XA 1 1) = [46, 63)`,
  where `muxn3_ok` says it is 0.

Binary `≤` forms. NOT covered: the `S_A_R` boundary and the `S_A_J.1`
non-necessity run for bdc_muxn (the bd_mux analogues are
`Necessity7MuxRunsN.failR6` / `passB`); an iff; the `+1`.
-/

namespace Formal.Cells.MuxN3Timed
namespace Nec7
open Formal.Cells
open Formal.Cells.OpsTimed
open Formal.Cells.PipeTimed (Ret Trace)
open Formal.Cells.LibCtlMergeMux (c2B)
open Formal.Cells.AMergeGates (or3)

/-- `MN3StaticG` with `S_A_SEQ` weakened by `sq` and `S_A_R` by `sr`. -/
structure MN3StaticW (P : MN3Run) (Wzc : Ret) (Ex Ec Es wc ls wsj lj wo Dl sq sr : Nat) : Prop where
  H_MIN : ∀ i, i < 3 → wc ≤ (P.Wc i).lo ∧ ls ≤ (P.Ls i).lo ∧ wsj ≤ (P.Wsj i).lo ∧
    lj ≤ (P.Lj i).lo ∧ wo ≤ (P.Wjo i).lo
  H_DL0 : Dl ≤ (P.H 0).lo
  H_DLT : ∀ i, 1 ≤ i → i < P.N → Dl ≤ (P.Tp i).lo
  S_J_X : ∀ i, i < 3 → (P.Lj i).hi + P.wjh i ≤
    (P.Lj i).lo + (P.Wja i).lo + (P.La i).lo + (P.Wak i).lo + Ex + (P.Wx i).lo
  S_J_C : ∀ i, i < 3 → (P.Lj i).hi + P.wjh i ≤
    (P.Lj i).lo + (wo + P.Lo.lo + Dl + Es) + Wzc.lo + Ec + (P.Wc i).lo + (P.Ls i).lo + (P.Wsj i).lo
  S_A_RTZ : ∀ i, i < 3 → (P.Wza i).hi + ((P.La i).hi + P.wah i) ≤
    (P.Wza i).lo + (Wzc.lo + Ec + (wc + ls + wsj + lj)) + (wo + P.Lo.lo + Dl + Es)
  S_A_J2 : ∀ i, i < 3 → (P.Wja i).hi + ((P.La i).hi + P.wah i) ≤
      2 * (wo + P.Lo.lo + Dl + Es) + (Wzc.lo + Ec + (wc + ls + wsj + lj)) + (P.Wza i).lo
  S_A_R : ∀ i, i < 3 →
    (P.La i).hi + P.wah i ≤ (P.La i).lo + (P.Wak i).lo + Ex + (P.Wx i).lo + (P.Lj i).lo + (P.Wja i).lo + sr ∨
    ((P.Wza i).hi + ((P.La i).hi + P.wah i) ≤ (Wzc.lo + Ec + (wc + ls + wsj + lj)) + (P.Wja i).lo + sr ∧
     (P.Wja i).hi + ((P.La i).hi + P.wah i) ≤
      (wo + P.Lo.lo + Dl + Es) + (Wzc.lo + Ec + (wc + ls + wsj + lj)) + (P.Wja i).lo + sr)
  S_A_SEQ : ∀ i, i < 3 → (P.Wza i).hi ≤ (Wzc.lo + Ec + (wc + ls + wsj + lj)) + (P.Wja i).lo + sq

theorem MN3StaticW.toG {P : MN3Run} {Wzc : Ret} {Ex Ec Es wc ls wsj lj wo Dl : Nat}
    (S : MN3StaticW P Wzc Ex Ec Es wc ls wsj lj wo Dl 0 0) : MN3StaticG P Wzc Ex Ec Es wc ls wsj lj wo Dl :=
  ⟨S.H_MIN, S.H_DL0, S.H_DLT, S.S_J_X, S.S_J_C, S.S_A_RTZ, S.S_A_J2, S.S_A_R, S.S_A_SEQ⟩

/-- `muxn3_ok_gs`'s conclusion. -/
def MN3Concl (P : MN3Run) (j : Nat → Trace) (s : Nat → Trace) (ak : Nat → Trace) : Prop :=
  (∀ i, i < 3 → Tok (P.Lj i).hi (j i) P.E (P.g i)) ∧
  Tok (ffT P.H P.Tp P.To P.N) (s P.N) P.Z (fun _ => true) ∧
  (∀ i, i < 3 → Tok (P.Ta i) (ak i) (P.XA i) (P.g i) ∧
    Tok (P.Ta i) (ak i) (rx (P.XA i) (P.κ i)) (fun _ => true))

/-- The claim with `S_A_SEQ` weakened by `sq`, every other hypothesis of
`muxn3_ok_gs` verbatim. -/
def ClaimSEQn (sq : Nat) : Prop :=
  ∀ (P : MN3Run) (Wzc : Ret) (Ex Ec Es wc ls wsj lj wo Dl R : Nat) (rst ctl za orj : Trace)
    (x xj cp s0p s1p sl sj j q jo s ja zx a qa ak : Nat → Trace),
    MN3Gates P rst ctl za x xj cp s0p s1p sl sj j q jo orj s ja zx a qa ak →
    MN3Env P rst ctl za x s0p s1p R → MN3Causal P Wzc Ex Ec Es →
    MN3StaticW P Wzc Ex Ec Es wc ls wsj lj wo Dl sq 0 →
    (∀ i, i < 3 → (P.Wx i).hi ≤ R ∧ (P.Wc i).hi + (P.Ls i).hi + (P.Wsj i).hi ≤ R ∧
      (P.Lj i).hi + P.wjh i ≤ R ∧ (P.Lj i).hi + (P.Wja i).hi ≤ R ∧ (P.Wza i).hi ≤ R ∧
      (P.La i).hi + P.wah i ≤ R) →
    (∀ i, i < 3 → R ≤ P.Xp i 0 ∧ R ≤ P.D i 0 ∧ R ≤ P.ZA i 0) →
    (∀ i, 1 ≤ i → i < P.N → ∀ k,
      (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 1)) ≤ (P.Tp i).fst (P.OJ (2 * k + 2)) ∧
      (P.Tp i).fst (P.OJ (2 * k + 1)) ≤ (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 2))) →
    1 ≤ P.N → MN3Concl P j s ak

theorem claimSEQn0 : ClaimSEQn 0 := by
  intro P Wzc Ex Ec Es wc ls wsj lj wo Dl R rst ctl za orj x xj cp s0p s1p sl sj j q jo s ja zx a qa ak
    G V Cs S hRL hRE hFL hN
  exact muxn3_ok_gs G V Cs S.toG hRL hRE hFL hN

namespace Mn7
open Mn3Wit (svW)

def run (d : Nat) : MN3Run where
  Wx _ := uW
  Wc _ := uW
  Ls _ := uW
  Wsj _ := uW
  Lj _ := uW
  wjl _ := 1
  wjh _ := 1
  Wjo _ := uW
  Wja _ := uW
  Lo := uW
  H _ := uW
  Tp _ := uW
  N := 1
  Wza _ := Ret.shift d
  La _ := uW
  wal _ := 1
  wah _ := 1
  Wak _ := uW
  ξ i j := 81 * (j / 2) + 27 * i + 8 + 39 * (j % 2)
  γ j := 27 * (j / 2) + 28 + 10 * (j % 2)
  ζ j := 27 * (j / 2) + 36 + 17 * (j % 2)
  sv := svW
  κ i m := 3 * m + i

def rst (t : Nat) : Bool := decide (t < 9)
theorem rst_hi : ∀ t, t < 9 → rst t = true := fun t h => by simp [rst, h]
theorem rst_lo : ∀ t, 9 ≤ t → rst t = false := fun t h => by simp [rst]; omega

-- environment
def x (i t : Nat) : Bool := decide (27 * i + 8 ≤ t ∧ (t - (27 * i + 8)) % 81 < 39)
def ctl (t : Nat) : Bool := decide (28 ≤ t ∧ (t - 28) % 27 < 10)
def za (t : Nat) : Bool := decide (36 ≤ t ∧ (t - 36) % 27 < 17)
def s0d (t : Nat) : Bool := b0 (svW ((t - 28) / 27))
def s1d (t : Nat) : Bool := b1 (svW ((t - 28) / 27))
-- the cell
def xj (i t : Nat) : Bool := x i (t - 1)
def cp (_ : Nat) (t : Nat) : Bool := ctl (t - 1)
def s0p (_ : Nat) (t : Nat) : Bool := s0d (t - 1)
def s1p (_ : Nat) (t : Nat) : Bool := s1d (t - 1)
def sl (i t : Nat) : Bool := selF i (s0p i (t - 1)) (s1p i (t - 1)) (cp i (t - 1))
def sj (i t : Nat) : Bool := sl i (t - 1)
def jW (i : Nat) : Nat → Bool
  | 0 => false
  | 1 => c2B (xj i 0) (sj i 0) false (rst 0)
  | t + 2 => c2B (xj i (t + 1)) (sj i (t + 1)) (jW i t) (rst (t + 1))
def q (i t : Nat) : Bool := jW i (t - 1)
def jo (i t : Nat) : Bool := jW i (t - 1)
def orj (t : Nat) : Bool := or3 (jo 0 (t - 1)) (jo 1 (t - 1)) (jo 2 (t - 1))
def line (n t : Nat) : Bool := orj (t - n)
def ja (i t : Nat) : Bool := jW i (t - 1)
/-- z_ack at ua_i through the `d`-tick wire. -/
def zx (d : Nat) (_ : Nat) (t : Nat) : Bool := za (t - d)
def aW (d : Nat) (i : Nat) : Nat → Bool
  | 0 => false
  | 1 => c2B (ja i 0) (zx d i 0) false (rst 0)
  | t + 2 => c2B (ja i (t + 1)) (zx d i (t + 1)) (aW d i t) (rst (t + 1))
def qa (d i t : Nat) : Bool := aW d i (t - 1)
def ak (d i t : Nat) : Bool := aW d i (t - 1)

theorem gates (d : Nat) :
    MN3Gates (run d) rst ctl za x xj cp s0p s1p sl sj jW q jo orj line ja (zx d) (aW d) (qa d) (ak d) where
  H_WX _ _ _ _ := rfl
  H_WC _ _ _ _ := rfl
  H_SEL _ _ _ _ := rfl
  H_WSJ _ _ _ _ := rfl
  H_UJ i _ t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UJ_FB _ _ := win11 (fun _ _ => rfl)
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

section closed
variable (d : Nat)

theorem enum (i : Nat) (hi : i < 3) : Enum ((run d).g i) ((run d).κ i) where
  mono m := by show 3 * m + i < 3 * (m + 1) + i; omega
  hit m := by show decide ((3 * m + i) % 3 = i) = true; simp; omega
  all k h := ⟨k / 3, by
    have h : decide (k % 3 = i) = true := h
    simp at h; show 3 * (k / 3) + i = k; omega⟩

theorem idx_eq (i k : Nat) (hi : i < 3) (hk : k % 3 = i) : idx ((run d).κ i) k = k / 3 := by
  have := idx_κ (enum d i hi) (k / 3)
  rw [show (run d).κ i (k / 3) = k by show 3 * (k / 3) + i = k; omega] at this
  exact this

theorem Xp_eq (i j : Nat) : (run d).Xp i j = 81 * (j / 2) + 27 * i + 9 + 39 * (j % 2) := by
  show uW.fst (81 * (j / 2) + 27 * i + 8 + 39 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem Cp_eq (i j : Nat) : (run d).Cp i j = 27 * (j / 2) + 29 + 10 * (j % 2) := by
  show uW.fst (27 * (j / 2) + 28 + 10 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem Sd_eq (i j : Nat) : (run d).Sd i j = 27 * (j / 2) + 31 + 10 * (j % 2) := by
  show uW.fst (uW.fst ((run d).Cp i j)) = _
  rw [Cp_eq, fuW (27 * (j / 2) + 29 + 10 * (j % 2)) (by omega),
    fuW (27 * (j / 2) + 29 + 10 * (j % 2) + 1) (by omega)]; omega
theorem D_eq (i j : Nat) : (run d).D i j = 81 * (j / 2) + 27 * i + 31 + 10 * (j % 2) := by
  show (run d).Sd i (2 * (3 * (j / 2) + i) + j % 2) = _; rw [Sd_eq]; omega
theorem c_eq (i j : Nat) : (run d).c i j = 81 * (j / 2) + 27 * i + 31 + 17 * (j % 2) := by
  show max ((run d).Xp i j) ((run d).D i j) = _; rw [Xp_eq, D_eq]; omega
theorem τ_eq (i j : Nat) : (run d).τ i j = 81 * (j / 2) + 27 * i + 32 + 17 * (j % 2) := by
  show uW.fst ((run d).c i j) = _; rw [c_eq, fuW _ (by omega)]; omega

theorem E_eq (j : Nat) : (run d).E j = 27 * (j / 2) + 32 + 17 * (j % 2) := by
  unfold MN3Run.E
  have hs : (run d).sv (j / 2) = j / 2 % 3 := rfl
  rw [hs, idx_eq d (j / 2 % 3) (j / 2) (by omega) rfl, τ_eq]
  omega

theorem Op_eq (i j : Nat) : (run d).Op i j = (run d).E j + 1 := by
  show uW.fst ((run d).E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem A_eq (i j : Nat) : (run d).A i j = (run d).E j + 1 := by
  show uW.fst ((run d).E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem ZA_eq (i j : Nat) : (run d).ZA i j = 27 * (j / 2) + 36 + 17 * (j % 2) + d := by
  show (Ret.shift d).fst (27 * (j / 2) + 36 + 17 * (j % 2)) = _; rw [Ret.fst_shift _ _ (by omega)]
theorem OJ_eq (j : Nat) : (run d).OJ j = (run d).E j + 2 := by
  show uW.fst ((run d).Op ((run d).sv (j / 2)) j) = _
  rw [Op_eq, fuW _ (by omega)]
theorem Z_eq (j : Nat) : (run d).Z j = (run d).E j + 3 := by
  show uW.fst ((run d).OJ j) = _
  rw [OJ_eq, fuW _ (by omega)]
theorem XA_eq (i j : Nat) : (run d).XA i j = 27 * (j / 2) + 38 + 17 * (j % 2) + d := by
  have hm : max ((run d).E j + 1) (27 * (j / 2) + 36 + 17 * (j % 2) + d) =
      27 * (j / 2) + 36 + 17 * (j % 2) + d := by
    rw [E_eq]; omega
  show uW.fst (uW.fst (max ((run d).A i j) ((run d).ZA i j))) = _
  rw [A_eq, ZA_eq, hm, fuW (27 * (j / 2) + 36 + 17 * (j % 2) + d) (by omega),
    fuW (27 * (j / 2) + 36 + 17 * (j % 2) + d + 1) (by omega)]; omega

theorem env : MN3Env (run d) rst ctl za x s0p s1p 9 where
  H_RST_HI := rst_hi
  H_RST_LO := rst_lo
  H_X i _ := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 81 * (0 / 2) + 27 * i + 8 + 39 * (0 % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
    · have h1 : 81 * (2 * k / 2) + 27 * i + 8 + 39 * (2 * k % 2) ≤ t := h1
      have h2 : t < 81 * ((2 * k + 1) / 2) + 27 * i + 8 + 39 * ((2 * k + 1) % 2) := h2
      simp only [x, decide_eq_true_eq]; omega
    · have h1 : 81 * ((2 * k + 1) / 2) + 27 * i + 8 + 39 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 81 * ((2 * k + 2) / 2) + 27 * i + 8 + 39 * ((2 * k + 2) % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
  H_CTL := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 27 * (0 / 2) + 28 + 10 * (0 % 2) := h2
      simp only [ctl, decide_eq_false_iff_not]; omega
    · have h1 : 27 * (2 * k / 2) + 28 + 10 * (2 * k % 2) ≤ t := h1
      have h2 : t < 27 * ((2 * k + 1) / 2) + 28 + 10 * ((2 * k + 1) % 2) := h2
      simp only [ctl, decide_eq_true_eq]; omega
    · have h1 : 27 * ((2 * k + 1) / 2) + 28 + 10 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 27 * ((2 * k + 2) / 2) + 28 + 10 * ((2 * k + 2) % 2) := h2
      simp only [ctl, decide_eq_false_iff_not]; omega
  H_ZA := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 27 * (0 / 2) + 36 + 17 * (0 % 2) := h2
      simp only [za, decide_eq_false_iff_not]; omega
    · have h1 : 27 * (2 * k / 2) + 36 + 17 * (2 * k % 2) ≤ t := h1
      have h2 : t < 27 * ((2 * k + 1) / 2) + 36 + 17 * ((2 * k + 1) % 2) := h2
      simp only [za, decide_eq_true_eq]; omega
    · have h1 : 27 * ((2 * k + 1) / 2) + 36 + 17 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 27 * ((2 * k + 2) / 2) + 36 + 17 * ((2 * k + 2) % 2) := h2
      simp only [za, decide_eq_false_iff_not]; omega
  H_RANGE k := by show k % 3 < 3; omega
  H_ENUM := enum d
  H_S_PIN i _ k t h1 h2 := by
    rw [Cp_eq] at h1 h2
    have e : (t - 1 - 28) / 27 = k := by omega
    show b0 (svW ((t - 1 - 28) / 27)) = b0 (svW k) ∧ b1 (svW ((t - 1 - 28) / 27)) = b1 (svW k)
    rw [e]; exact ⟨rfl, rfl⟩

/-- The partners are causal (the control sender and the server's fall are
tight; the clients are tight at `d = 8`). -/
theorem causal (hd : d ≤ 8) : MN3Causal (run d) uW 1 1 1 where
  H_XC_FALL i _ m := by
    rw [XA_eq]; show _ ≤ 81 * ((2 * m + 1) / 2) + 27 * i + 8 + 39 * ((2 * m + 1) % 2)
    show 27 * (2 * (3 * m + i) / 2) + 38 + 17 * (2 * (3 * m + i) % 2) + d + 1 ≤ _; omega
  H_XC_RISE i _ m := by
    rw [XA_eq]; show _ ≤ 81 * ((2 * m + 2) / 2) + 27 * i + 8 + 39 * ((2 * m + 2) % 2)
    show 27 * ((2 * (3 * m + i) + 1) / 2) + 38 + 17 * ((2 * (3 * m + i) + 1) % 2) + d + 1 ≤ _; omega
  H_CTL_C j := by
    show uW.fst (27 * (j / 2) + 36 + 17 * (j % 2)) + 1 ≤ 27 * ((j + 1) / 2) + 28 + 10 * ((j + 1) % 2)
    rw [fuW _ (by omega)]; omega
  H_SRV j := by
    rw [Z_eq, E_eq]; show _ ≤ 27 * (j / 2) + 36 + 17 * (j % 2); omega
  H_ES := Nat.le_refl 1
  H_POS j := by show 1 ≤ 27 * (j / 2) + 28 + 10 * (j % 2); omega

/-- Every field holds; `S_A_SEQ` needs `d ≤ 7 + sq`. -/
theorem staticW (sq : Nat) (h1 : d ≤ 7 + sq) : MN3StaticW (run d) uW 1 1 1 1 1 1 1 1 1 sq 0 where
  H_MIN _ _ := ⟨Nat.le_refl 1, Nat.le_refl 1, Nat.le_refl 1, Nat.le_refl 1, Nat.le_refl 1⟩
  H_DL0 := Nat.le_refl 1
  H_DLT _ _ _ := Nat.le_refl 1
  S_J_X _ _ := Nat.le_of_ble_eq_true rfl
  S_J_C _ _ := Nat.le_of_ble_eq_true rfl
  S_A_RTZ _ _ := by
    show d + (1 + 1) ≤ d + (1 + 1 + (1 + 1 + 1 + 1)) + (1 + 1 + 1 + 1); omega
  S_A_J2 _ _ := by
    show 1 + (1 + 1) ≤ 2 * (1 + 1 + 1 + 1) + (1 + 1 + (1 + 1 + 1 + 1)) + d; omega
  S_A_R _ _ := Or.inl (Nat.le_of_ble_eq_true rfl)
  S_A_SEQ _ _ := by show d ≤ (1 + 1 + (1 + 1 + 1 + 1)) + 1 + sq; omega

theorem rstL (hd : d ≤ 9) : ∀ i, i < 3 → ((run d).Wx i).hi ≤ 9 ∧
    ((run d).Wc i).hi + ((run d).Ls i).hi + ((run d).Wsj i).hi ≤ 9 ∧
    ((run d).Lj i).hi + (run d).wjh i ≤ 9 ∧ ((run d).Lj i).hi + ((run d).Wja i).hi ≤ 9 ∧
    ((run d).Wza i).hi ≤ 9 ∧ ((run d).La i).hi + (run d).wah i ≤ 9 := fun _ _ =>
  ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
    Nat.le_of_ble_eq_true rfl, by show d ≤ 9; omega, Nat.le_of_ble_eq_true rfl⟩

theorem rstE : ∀ i, i < 3 → 9 ≤ (run d).Xp i 0 ∧ 9 ≤ (run d).D i 0 ∧ 9 ≤ (run d).ZA i 0 :=
  fun i _ => ⟨by rw [Xp_eq]; omega, by rw [D_eq]; omega, by rw [ZA_eq]; omega⟩

theorem flush : ∀ i, 1 ≤ i → i < (run d).N → ∀ k,
    ((run d).H i).fst (ffE (run d).H (run d).Tp (run d).OJ i (2 * k + 1)) ≤
      ((run d).Tp i).fst ((run d).OJ (2 * k + 2)) ∧
    ((run d).Tp i).fst ((run d).OJ (2 * k + 1)) ≤
      ((run d).H i).fst (ffE (run d).H (run d).Tp (run d).OJ i (2 * k + 2)) :=
  fun i h1 h2 => by have : (1 : Nat) ≤ i := h1; have : i < 1 := h2; omega

end closed
end Mn7

/-- **`S_A_FORK` is not necessary** (row `bdc_muxn.iso_zack`). With 7-tick
z_ack → ua_i wires the shipped `S_A_FORK` fails (`7 + 2 ≤ 6 + 1` is false;
strict `+1`: by 3), every `MN3StaticG` field holds (`S_A_SEQ` `7 ≤ 7`), and
`muxn3_ok_gs` gives the whole conclusion. At the hand-over from input 0 to
input 1, z_ack's fall and j_1's rise reach ua_1 at the same tick (60). -/
theorem passN7 :
    ¬ (((Mn7.run 7).Wza 0).hi + (((Mn7.run 7).La 0).hi + (Mn7.run 7).wah 0) ≤
        (uW.lo + 1 + (1 + 1 + 1 + 1)) + ((Mn7.run 7).Wja 0).lo) ∧
    MN3StaticG (Mn7.run 7) uW 1 1 1 1 1 1 1 1 1 ∧
    Mn7.zx 7 1 59 = true ∧ Mn7.zx 7 1 60 = false ∧ Mn7.ja 1 59 = false ∧ Mn7.ja 1 60 = true ∧
    Mn7.ak 7 1 70 = false ∧ Mn7.ak 7 1 72 = true ∧
    MN3Concl (Mn7.run 7) Mn7.jW Mn7.line (Mn7.ak 7) := by
  have S := (Mn7.staticW 7 0 (by omega)).toG
  refine ⟨by decide, S, by decide +kernel, by decide +kernel, by decide +kernel, by decide +kernel,
    by decide +kernel, by decide +kernel, ?_⟩
  exact muxn3_ok_gs (Mn7.gates 7) (Mn7.env 7) (Mn7.causal 7 (by omega)) S (Mn7.rstL 7 (by omega))
    (Mn7.rstE 7) (Mn7.flush 7) (Nat.le_refl 1)

/-- **`S_A_SEQ` is necessary at the boundary.** With 8-tick z_ack → ua_i
wires every `MN3StaticW … 1 0` field holds, the unweakened `S_A_SEQ` fails
by exactly one (`8 = 7 + 1`), and in1_ack is 1 at 62, inside
`[XA 1 0, XA 1 1) = [46, 63)` (token 0 selects input 0). -/
theorem failSEQ8 :
    MN3StaticW (Mn7.run 8) uW 1 1 1 1 1 1 1 1 1 1 0 ∧
    ((Mn7.run 8).Wza 1).hi = (uW.lo + 1 + (1 + 1 + 1 + 1)) + ((Mn7.run 8).Wja 1).lo + 1 ∧
    (Mn7.run 8).ZA 1 1 = 61 ∧ (Mn7.run 8).A 1 2 = 60 ∧
    (Mn7.run 8).XA 1 0 = 46 ∧ (Mn7.run 8).XA 1 1 = 63 ∧
    Mn7.zx 8 1 60 = true ∧ Mn7.ja 1 60 = true ∧ Mn7.ak 8 1 62 = true ∧
    ¬ Tok ((Mn7.run 8).Ta 1) (Mn7.ak 8 1) ((Mn7.run 8).XA 1) ((Mn7.run 8).g 1) ∧
    ¬ MN3Concl (Mn7.run 8) Mn7.jW Mn7.line (Mn7.ak 8) := by
  have hX0 : (Mn7.run 8).XA 1 0 = 46 := by rw [Mn7.XA_eq]
  have hX1 : (Mn7.run 8).XA 1 1 = 63 := by rw [Mn7.XA_eq]
  have v : Mn7.zx 8 1 60 = true ∧ Mn7.ja 1 60 = true ∧ Mn7.ak 8 1 62 = true := by decide +kernel
  have nx : ¬ Tok ((Mn7.run 8).Ta 1) (Mn7.ak 8 1) ((Mn7.run 8).XA 1) ((Mn7.run 8).g 1) := by
    intro h
    have := h.hi 0 62 (by decide) (by rw [show 2 * 0 = 0 from rfl, hX0]; omega)
      (by rw [show 2 * 0 + 1 = 1 from rfl, hX1]; omega)
    rw [v.2.2] at this; exact absurd this (by decide)
  exact ⟨Mn7.staticW 8 1 (by omega), rfl, by rw [Mn7.ZA_eq], by rw [Mn7.A_eq, Mn7.E_eq], hX0, hX1,
    v.1, v.2.1, v.2.2, nx, fun h => nx (h.2.2 1 (by omega)).1⟩

/-- The counter-run meets every other hypothesis, so `ClaimSEQn 1` is false. -/
theorem claimSEQn1_false : ¬ ClaimSEQn 1 := by
  intro h
  exact failSEQ8.2.2.2.2.2.2.2.2.2.2
    (h (Mn7.run 8) uW 1 1 1 1 1 1 1 1 1 9 Mn7.rst Mn7.ctl Mn7.za Mn7.orj Mn7.x Mn7.xj Mn7.cp Mn7.s0p
      Mn7.s1p Mn7.sl Mn7.sj Mn7.jW Mn7.q Mn7.jo Mn7.line Mn7.ja (Mn7.zx 8) (Mn7.aW 8) (Mn7.qa 8)
      (Mn7.ak 8) (Mn7.gates 8) (Mn7.env 8) (Mn7.causal 8 (by omega)) failSEQ8.1
      (Mn7.rstL 8 (by omega)) (Mn7.rstE 8) (Mn7.flush 8) (Nat.le_refl 1))

end Nec7
end Formal.Cells.MuxN3Timed
