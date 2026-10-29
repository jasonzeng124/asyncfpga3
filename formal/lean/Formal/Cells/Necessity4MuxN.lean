import Formal.Cells.MuxN3Timed

/-!
# Necessity4MuxN: `bdc_muxn.uj_env_latency_req` is NOT necessary; its max form

Probe Bnx4 (shard B). The row `bdc_muxn.uj_env_latency_req` is the
`MN3Static` field `S_J_X` (`MuxN3Timed`):

    S_J_X i : Lj.hi + wjh ≤ Lj.lo + Wja.lo + La.lo + Wak.lo + Ex + Wx.lo

As for bd_mux (Necessity4Mux), ua_i is a C-element of j_i AND z_ack, so
in_i_ack moves only after `max (A i, ZA i)`, and the z_ack edge is launched
by the same join edge through |j, the line and the server.

## Result

* `MN3StaticN … s` is `MN3Static` with `S_J_X` replaced by its max form
  (weakened by `s`), every other field word for word:

      S_J_XR i : Lj.hi + wjh ≤ Lj.lo + max Wja.lo ((wo + Lo.lo + Dl + Es) + Wza.lo)
                               + La.lo + Wak.lo + Ex + Wx.lo + s

  (`wo`, `Dl`: the shipped lower bounds over the three inputs / the line).
* `staticN_of_static`: `MN3Static → MN3StaticN 0`.
* `muxn3_timing_of_staticN`, `muxn3_ok_staticN`: **sufficient** (the
  shipped proof, the client branch now waits for z_ack too).
* `pass8`: **`S_J_X` is NOT necessary.** `Mn3Wit`'s unit-delay run with every
  join's feedback net 8 ticks and reset held to 11 (`W8.run`; real INITs,
  every gate relation for all `t`): `S_J_X` fails for every input (`9 ≤ 6`),
  its strict form too, every `MN3StaticN 0` field holds (the strict max form
  as well, `10 ≤ 10`), and `muxn3_ok_staticN` gives the cell's conclusion
  (each join fires exactly in its tokens, one z_req transaction per control
  token, in_i_ack exactly in i's tokens). Since `muxn3_ok_staticN` covers
  every run with these windows and latencies, this is non-necessity over the
  box.

NOT proved here: necessity of the max form at its boundary for bdc_muxn
(in this run `S_J_C` has the same right side, 10, so a one-tick violation
would break both; a run with a slower control sender is needed). The bd_mux
counter-run (`Necessity4Mux.fail10`) shows the mechanism on the 2-input
cell. Lumped LUT arcs, FIFO line, as MuxN3Timed.
-/

namespace Formal.Cells.MuxN3Timed
namespace Nec4
open Formal.Cells
open Formal.Cells.OpsTimed
open Formal.Cells.PipeTimed (Ret Trace)
open Formal.Cells.LibCtlMergeMux (c2B)
open Formal.Cells.AMergeGates (or3)

/-- `MN3Static` with `S_J_X` in its max form, weakened by `s`. -/
structure MN3StaticN (P : MN3Run) (Wzc : Ret) (Ex Ec Es wc ls wsj lj wo Dl s : Nat) : Prop where
  H_MIN : ∀ i, i < 3 → wc ≤ (P.Wc i).lo ∧ ls ≤ (P.Ls i).lo ∧ wsj ≤ (P.Wsj i).lo ∧
    lj ≤ (P.Lj i).lo ∧ wo ≤ (P.Wjo i).lo
  H_DL0 : Dl ≤ (P.H 0).lo
  H_DLT : ∀ i, 1 ≤ i → i < P.N → Dl ≤ (P.Tp i).lo
  /-- **S_J_XR**: the max form of `S_J_X`. -/
  S_J_XR : ∀ i, i < 3 → (P.Lj i).hi + P.wjh i ≤
    (P.Lj i).lo + max (P.Wja i).lo ((wo + P.Lo.lo + Dl + Es) + (P.Wza i).lo) + (P.La i).lo +
      (P.Wak i).lo + Ex + (P.Wx i).lo + s
  S_J_C : ∀ i, i < 3 → (P.Lj i).hi + P.wjh i ≤
    (P.Lj i).lo + (wo + P.Lo.lo + Dl + Es) + Wzc.lo + Ec + (P.Wc i).lo + (P.Ls i).lo + (P.Wsj i).lo
  S_A_FORK : ∀ i, i < 3 → (P.Wza i).hi + ((P.La i).hi + P.wah i) ≤
    (Wzc.lo + Ec + (wc + ls + wsj + lj)) + (P.Wja i).lo
  S_A_RTZ : ∀ i, i < 3 → (P.Wza i).hi + ((P.La i).hi + P.wah i) ≤
    (P.Wza i).lo + (Wzc.lo + Ec + (wc + ls + wsj + lj)) + (wo + P.Lo.lo + Dl + Es)
  S_A_J : ∀ i, i < 3 →
    (P.Wja i).hi + ((P.La i).hi + P.wah i) ≤
      (wo + P.Lo.lo + Dl + Es) + (Wzc.lo + Ec + (wc + ls + wsj + lj)) + (P.Wja i).lo ∧
    (P.Wja i).hi + ((P.La i).hi + P.wah i) ≤
      2 * (wo + P.Lo.lo + Dl + Es) + (Wzc.lo + Ec + (wc + ls + wsj + lj)) + (P.Wza i).lo

section suff
variable {P : MN3Run} {Wzc : Ret} {Ex Ec Es wc ls wsj lj wo Dl s : Nat}

theorem staticN_of_static (S : MN3Static P Wzc Ex Ec Es wc ls wsj lj wo Dl) :
    MN3StaticN P Wzc Ex Ec Es wc ls wsj lj wo Dl 0 :=
  ⟨S.H_MIN, S.H_DL0, S.H_DLT, fun i hi => by have := S.S_J_X i hi; omega, S.S_J_C, S.S_A_FORK,
    S.S_A_RTZ, S.S_A_J⟩

theorem GE_minN (hE : ∀ i, i < 3 → Enum (P.g i) (P.κ i)) (hR : ∀ k, P.sv k < 3)
    (Cs : MN3Causal P Wzc Ex Ec Es) (S : MN3StaticN P Wzc Ex Ec Es wc ls wsj lj wo Dl s) (j : Nat) :
    P.γ j + (wc + ls + wsj + lj) ≤ P.E j := by
  have := γ_le_E hE hR Cs.H_POS j; have := S.H_MIN _ (hR (j / 2)); omega

theorem EZ_minN (hE : ∀ i, i < 3 → Enum (P.g i) (P.κ i)) (hR : ∀ k, P.sv k < 3)
    (Cs : MN3Causal P Wzc Ex Ec Es) (S : MN3StaticN P Wzc Ex Ec Es wc ls wsj lj wo Dl s) (hN : 1 ≤ P.N)
    (j : Nat) : P.E j + (wo + P.Lo.lo + Dl + Es) ≤ P.ζ j := by
  have := E_le_Z hE hR Cs.H_POS (fun i hi => (S.H_MIN i hi).2.2.2.2) S.H_DL0 S.H_DLT hN j
  have := Cs.H_SRV j; omega

theorem ZE_minN (hE : ∀ i, i < 3 → Enum (P.g i) (P.κ i)) (hR : ∀ k, P.sv k < 3)
    (Cs : MN3Causal P Wzc Ex Ec Es) (S : MN3StaticN P Wzc Ex Ec Es wc ls wsj lj wo Dl s) (hN : 1 ≤ P.N)
    (j : Nat) : P.ζ j + (Wzc.lo + Ec + (wc + ls + wsj + lj)) ≤ P.E (j + 1) := by
  have h1 := Cs.H_CTL_C j
  have hz : 1 ≤ P.ζ j := by
    have := EZ_minN hE hR Cs S hN j; have := GE_minN hE hR Cs S j; have := Cs.H_POS j; omega
  have h2 := fl Wzc hz
  have h3 := GE_minN hE hR Cs S (j + 1)
  omega

theorem γ_monoN (hE : ∀ i, i < 3 → Enum (P.g i) (P.κ i)) (hR : ∀ k, P.sv k < 3)
    (Cs : MN3Causal P Wzc Ex Ec Es) (S : MN3StaticN P Wzc Ex Ec Es wc ls wsj lj wo Dl s) (hN : 1 ≤ P.N) :
    ∀ a b, a ≤ b → P.γ a ≤ P.γ b :=
  mono_of_step P.γ (fun j => by
    have := GE_minN hE hR Cs S j; have := EZ_minN hE hR Cs S hN j; have := Cs.H_CTL_C j
    have := Wzc.fst_ge (P.ζ j); omega)

/-- **The event-form obligations from the max form** (`muxn3_timing_of_static`
with `S_J_X` replaced by `S_J_XR` at slack 0). -/
theorem muxn3_timing_of_staticN {R : Nat} (hE : ∀ i, i < 3 → Enum (P.g i) (P.κ i))
    (hR : ∀ k, P.sv k < 3) (Cs : MN3Causal P Wzc Ex Ec Es)
    (S : MN3StaticN P Wzc Ex Ec Es wc ls wsj lj wo Dl 0)
    (hRL : ∀ i, i < 3 → (P.Wx i).hi ≤ R ∧ (P.Wc i).hi + (P.Ls i).hi + (P.Wsj i).hi ≤ R ∧
      (P.Lj i).hi + P.wjh i ≤ R ∧ (P.Lj i).hi + (P.Wja i).hi ≤ R ∧ (P.Wza i).hi ≤ R ∧
      (P.La i).hi + P.wah i ≤ R)
    (hRE : ∀ i, i < 3 → R ≤ P.Xp i 0 ∧ R ≤ P.D i 0 ∧ R ≤ P.A i 0 ∧ R ≤ P.ZA i 0)
    (hFL : ∀ i, 1 ≤ i → i < P.N → ∀ k,
      (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 1)) ≤ (P.Tp i).fst (P.OJ (2 * k + 2)) ∧
      (P.Tp i).fst (P.OJ (2 * k + 1)) ≤ (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 2)))
    (hN : 1 ≤ P.N) : MN3Timing P R := by
  have EZ := EZ_minN hE hR Cs S hN
  have ZE := ZE_minN hE hR Cs S hN
  have GE := GE_minN hE hR Cs S
  have GM := γ_monoN hE hR Cs S hN
  have Ep : ∀ j, 1 ≤ P.E j := fun j => by have := GE j; have := Cs.H_POS j; omega
  refine ⟨hRL, hRE, fun i hi j => ⟨?_, ?_⟩, fun i hi j => ⟨?_, ?_⟩, hFL, hN⟩
  · -- uj_i, through client i (max form)
    have e0 : P.τ i j = P.E (2 * P.κ i (j / 2) + j % 2) := by
      have := E_rx (hE i hi) j; unfold rx at this; exact this.symm
    have hXA : P.XA i (2 * P.κ i (j / 2) + j % 2) + Ex ≤ P.ξ i (j + 1) := by
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m := ⟨j / 2, by omega⟩
        have := Cs.H_XC_FALL i hi m
        rw [show 2 * m / 2 = m by omega, show 2 * m % 2 = 0 by omega, Nat.add_zero]; exact this
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m + 1 := ⟨j / 2, by omega⟩
        have := Cs.H_XC_RISE i hi m
        rw [show (2 * m + 1) / 2 = m by omega, show (2 * m + 1) % 2 = 1 by omega]; exact this
    have hA : ∀ n, P.E n + max (P.Wja i).lo ((wo + P.Lo.lo + Dl + Es) + (P.Wza i).lo) +
        (P.La i).lo + (P.Wak i).lo ≤ P.XA i n := by
      intro n
      have := Ep n
      have a := fl (P.Wja i) (Ep n)
      have hz := EZ n
      have z1 := fl (P.Wza i) (c := P.ζ n) (by omega)
      have hc : P.A i n ≤ P.cx i n := by unfold MN3Run.cx; omega
      have hcz : P.ZA i n ≤ P.cx i n := by unfold MN3Run.cx; omega
      have hAe : P.A i n = (P.Wja i).fst (P.E n) := rfl
      have hZe : P.ZA i n = (P.Wza i).fst (P.ζ n) := rfl
      have b := fl (P.La i) (c := P.cx i n) (by omega)
      have c := fl (P.Wak i) (c := (P.La i).fst (P.cx i n)) (by omega)
      show _ ≤ (P.Wak i).fst ((P.La i).fst (P.cx i n)); omega
    have := hA (2 * P.κ i (j / 2) + j % 2)
    have hp : 1 ≤ P.ξ i (j + 1) := by have := Ep (2 * P.κ i (j / 2) + j % 2); omega
    have := fl (P.Wx i) hp
    have : P.Xp i (j + 1) = (P.Wx i).fst (P.ξ i (j + 1)) := rfl
    have t0 : P.c i j + (P.Lj i).lo ≤ P.τ i j := fl (P.Lj i) (by
      have := Cs.H_POS (2 * P.κ i (j / 2) + j % 2)
      have := Sd_ge Cs.H_POS i (2 * P.κ i (j / 2) + j % 2)
      have : P.D i j = P.Sd i (2 * P.κ i (j / 2) + j % 2) := rfl
      unfold MN3Run.c; omega)
    have := S.S_J_XR i hi
    omega
  · -- uj_i, through the server, the control sender and decode i
    have e0 : P.τ i j = P.E (2 * P.κ i (j / 2) + j % 2) := by
      have := E_rx (hE i hi) j; unfold rx at this; exact this.symm
    have hk : P.D i (j + 1) = P.Sd i (2 * P.κ i ((j + 1) / 2) + (j + 1) % 2) := rfl
    have hge : 2 * P.κ i (j / 2) + j % 2 + 1 ≤ 2 * P.κ i ((j + 1) / 2) + (j + 1) % 2 := by
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · rw [show (j + 1) / 2 = j / 2 by omega]; omega
      · have := (hE i hi).mono (j / 2); rw [show (j + 1) / 2 = j / 2 + 1 by omega]; omega
    have g := GM _ _ hge
    have hS := Sd_ge Cs.H_POS i (2 * P.κ i ((j + 1) / 2) + (j + 1) % 2)
    have hz := EZ (2 * P.κ i (j / 2) + j % 2)
    have hc := Cs.H_CTL_C (2 * P.κ i (j / 2) + j % 2)
    have hzz : 1 ≤ P.ζ (2 * P.κ i (j / 2) + j % 2) := by
      have := Ep (2 * P.κ i (j / 2) + j % 2); omega
    have hw := fl Wzc hzz
    have t0 : P.c i j + (P.Lj i).lo ≤ P.τ i j := fl (P.Lj i) (by
      have := Cs.H_POS (2 * P.κ i (j / 2) + j % 2)
      have := Sd_ge Cs.H_POS i (2 * P.κ i (j / 2) + j % 2)
      have : P.D i j = P.Sd i (2 * P.κ i (j / 2) + j % 2) := rfl
      unfold MN3Run.c; omega)
    have := S.S_J_C i hi
    omega
  · have := (P.Wja i).fst_le (P.E j); have := (P.Wza i).fst_le (P.ζ j)
    have := fl (P.Wja i) (Ep (j + 1))
    have := ZE j; have := EZ j; have := S.S_A_FORK i hi; have := S.S_A_J i hi
    unfold MN3Run.cx MN3Run.A MN3Run.ZA; omega
  · have := (P.Wja i).fst_le (P.E j); have := (P.Wza i).fst_le (P.ζ j)
    have hz1 : 1 ≤ P.ζ (j + 1) := by have := EZ (j + 1); have := Ep (j + 1); omega
    have := fl (P.Wza i) hz1
    have := ZE j; have := EZ j; have := EZ (j + 1); have := S.S_A_RTZ i hi; have := S.S_A_J i hi
    unfold MN3Run.cx MN3Run.A MN3Run.ZA; omega

/-- **`muxn3_ok_staticN` (sufficient)**: `muxn3_ok`'s handshake conclusions
from the max-form static obligations. -/
theorem muxn3_ok_staticN {R : Nat} {rst ctl za orj : Trace}
    {x xj cp s0p s1p sl sj j q jo s ja zx a qa ak : Nat → Trace}
    (G : MN3Gates P rst ctl za x xj cp s0p s1p sl sj j q jo orj s ja zx a qa ak)
    (V : MN3Env P rst ctl za x s0p s1p R) (Cs : MN3Causal P Wzc Ex Ec Es)
    (S : MN3StaticN P Wzc Ex Ec Es wc ls wsj lj wo Dl 0)
    (hRL : ∀ i, i < 3 → (P.Wx i).hi ≤ R ∧ (P.Wc i).hi + (P.Ls i).hi + (P.Wsj i).hi ≤ R ∧
      (P.Lj i).hi + P.wjh i ≤ R ∧ (P.Lj i).hi + (P.Wja i).hi ≤ R ∧ (P.Wza i).hi ≤ R ∧
      (P.La i).hi + P.wah i ≤ R)
    (hRE : ∀ i, i < 3 → R ≤ P.Xp i 0 ∧ R ≤ P.D i 0 ∧ R ≤ P.A i 0 ∧ R ≤ P.ZA i 0)
    (hFL : ∀ i, 1 ≤ i → i < P.N → ∀ k,
      (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 1)) ≤ (P.Tp i).fst (P.OJ (2 * k + 2)) ∧
      (P.Tp i).fst (P.OJ (2 * k + 1)) ≤ (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 2)))
    (hN : 1 ≤ P.N) :
    (∀ i, i < 3 → Tok (P.Lj i).hi (j i) P.E (P.g i)) ∧
    Tok (ffT P.H P.Tp P.To P.N) (s P.N) P.Z (fun _ => true) ∧
    (∀ i, i < 3 → Tok (P.Ta i) (ak i) (P.XA i) (P.g i) ∧
      Tok (P.Ta i) (ak i) (rx (P.XA i) (P.κ i)) (fun _ => true)) := by
  have h := muxn3_ok G V (muxn3_timing_of_staticN V.H_ENUM V.H_RANGE Cs S hRL hRE hFL hN) Cs
  exact ⟨h.1, h.2.2.1, h.2.2.2.1⟩

end suff

/-! ## The passing run: `Mn3Wit` with 8-tick join feedback nets -/
namespace W8
open Mn3Wit

def run : MN3Run := { Mn3Wit.run with wjl := fun _ => 8, wjh := fun _ => 8 }

def rst (t : Nat) : Bool := decide (t < 11)
theorem c2_rst (a b q : Bool) : c2B a b q true = false := by
  cases a <;> cases b <;> cases q <;> decide

def jW (i : Nat) : Nat → Bool
  | t + 9 => c2B (xj i (t + 8)) (sj i (t + 8)) (jW i t) (rst (t + 8))
  | _ => false
def q (i t : Nat) : Bool := jW i (t - 8)
def jo (i t : Nat) : Bool := jW i (t - 1)
def orj (t : Nat) : Bool := or3 (jo 0 (t - 1)) (jo 1 (t - 1)) (jo 2 (t - 1))
def line (n t : Nat) : Bool := orj (t - n)
def ja (i t : Nat) : Bool := jW i (t - 1)
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
    | t + 9, _ => rfl
  H_UJ_FB _ _ := fun t ht => by
    have h : 8 ≤ t := ht
    exact ⟨t - 8, by show t ≤ t - 8 + 8; omega, by show t - 8 + 8 ≤ t; omega, rfl⟩
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

theorem env : MN3Env run rst ctl za x s0p s1p 11 where
  H_RST_HI t h := by simp [rst, h]
  H_RST_LO t h := by simp [rst]; omega
  H_X := Mn3Wit.env.H_X
  H_CTL := Mn3Wit.env.H_CTL
  H_ZA := Mn3Wit.env.H_ZA
  H_RANGE := Mn3Wit.env.H_RANGE
  H_ENUM := Mn3Wit.env.H_ENUM
  H_S_PIN := Mn3Wit.env.H_S_PIN

theorem causal : MN3Causal run uW 1 1 1 :=
  ⟨Mn3Wit.causal.H_XC_FALL, Mn3Wit.causal.H_XC_RISE, Mn3Wit.causal.H_CTL_C, Mn3Wit.causal.H_SRV,
    Mn3Wit.causal.H_ES, Mn3Wit.causal.H_POS⟩

theorem staticN : MN3StaticN run uW 1 1 1 1 1 1 1 1 1 0 where
  H_MIN _ _ := ⟨Nat.le_refl 1, Nat.le_refl 1, Nat.le_refl 1, Nat.le_refl 1, Nat.le_refl 1⟩
  H_DL0 := Nat.le_refl 1
  H_DLT _ _ _ := Nat.le_refl 1
  S_J_XR _ _ := Nat.le_of_ble_eq_true rfl
  S_J_C _ _ := Nat.le_of_ble_eq_true rfl
  S_A_FORK _ _ := Nat.le_of_ble_eq_true rfl
  S_A_RTZ _ _ := Nat.le_of_ble_eq_true rfl
  S_A_J _ _ := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

end W8

/-- **`S_J_X` is not necessary** (row `bdc_muxn.uj_env_latency_req`). On
`W8.run` the shipped `S_J_X` fails for every input, by 3 (and its strict
form by 4), the strict max form holds (`1 + 8 + 1 ≤ 10`), every max-form
obligation holds, and the cell's conclusion holds. -/
theorem pass8 :
    (∀ i, i < 3 → ¬ ((W8.run.Lj i).hi + W8.run.wjh i ≤
      (W8.run.Lj i).lo + (W8.run.Wja i).lo + (W8.run.La i).lo + (W8.run.Wak i).lo + 1 + (W8.run.Wx i).lo)) ∧
    (∀ i, i < 3 → (W8.run.Lj i).hi + W8.run.wjh i + 1 ≤
      (W8.run.Lj i).lo + max (W8.run.Wja i).lo ((1 + W8.run.Lo.lo + 1 + 1) + (W8.run.Wza i).lo) +
        (W8.run.La i).lo + (W8.run.Wak i).lo + 1 + (W8.run.Wx i).lo) ∧
    MN3StaticN W8.run uW 1 1 1 1 1 1 1 1 1 0 ∧
    (∀ i, i < 3 → Tok (W8.run.Lj i).hi (W8.jW i) W8.run.E (W8.run.g i)) ∧
    Tok (ffT W8.run.H W8.run.Tp W8.run.To W8.run.N) (W8.line W8.run.N) W8.run.Z (fun _ => true) ∧
    (∀ i, i < 3 → Tok (W8.run.Ta i) (W8.ak i) (W8.run.XA i) (W8.run.g i)) := by
  have h := muxn3_ok_staticN W8.gates W8.env W8.causal W8.staticN
    (fun _ _ => ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
      Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩)
    (fun i _ => ⟨by rw [show W8.run.Xp i 0 = Mn3Wit.run.Xp i 0 from rfl, Mn3Wit.Xp_eq]; omega,
      by rw [show W8.run.D i 0 = Mn3Wit.run.D i 0 from rfl, Mn3Wit.D_eq]; omega,
      by rw [show W8.run.A i 0 = Mn3Wit.run.A i 0 from rfl, Mn3Wit.A_eq, Mn3Wit.E_eq]; omega,
      by rw [show W8.run.ZA i 0 = Mn3Wit.run.ZA i 0 from rfl, Mn3Wit.ZA_eq]; omega⟩)
    (fun i h1 h2 => by have : (1 : Nat) ≤ i := h1; have : i < 1 := h2; omega)
    (Nat.le_refl 1)
  refine ⟨fun _ _ => by show ¬ (1 + 8 ≤ 1 + 1 + 1 + 1 + 1 + 1); decide, fun _ _ => Nat.le_of_ble_eq_true rfl, W8.staticN, h.1, h.2.1,
    fun i hi => (h.2.2 i hi).1⟩

set_option maxRecDepth 100000 in
/-- The run is not degenerate: each input is acknowledged in its own token,
and j_0 rises at 32 (it was 0 at 31). -/
theorem pass8_values :
    W8.ak 0 40 = true ∧ W8.ak 1 40 = false ∧ W8.ak 1 60 = true ∧ W8.ak 2 80 = true ∧
    W8.line 1 35 = true ∧ W8.line 1 55 = true ∧ W8.jW 0 32 = true ∧ W8.jW 0 31 = false := by
  decide

end Nec4
end Formal.Cells.MuxN3Timed
