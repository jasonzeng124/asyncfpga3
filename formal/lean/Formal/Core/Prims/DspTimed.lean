import Formal.Core.Prims.Dsp
import Formal.Core.Prims.DspData

/-!
# Formal.Core.Prims.DspTimed — the ipow DSP cascade under a lumped bounded-delay model

Shard A, probe PrimsDSP. Core Lean only. Notes: `formal/notes/A-prims-dsp.md`.

## Model (hypothesis H_DSP_LUMPED)

Nothing is known about the DSP48E1's internal arcs: prjxray-db gives one band per
(input port, output port) and corner (`DspData`, generated from `DSP_L.sdf`; fast/slow corners,
NOT rise/fall). So each DSP output port is a **lumped bounded-delay stage** (`Lumped W f x y`):
at time `t` the output equals `f v` whenever every input port `i` held the defined word `v i`
throughout `[t - hi_i, t - lo_i]`. At every other time the output may be ANYTHING: any wrong
word, X (`none`), any number of glitches (`lumped_admits_anything`). Signals are
`Int → Option Nat` (integer ps; `none` = some bit not a valid level). This is weaker than a
per-pin transport delay (`transport_lumped`: transport within the bands is one behaviour).

## Results
* `Lumped.constOn`: inputs constant on `[S_i, E_i]` ⇒ output constant `f v` on
  `[max_i (S_i + hi_i), min_i (E_i + lo_i)]`; this composes along the cascade.
* `ipow_mul_settles`: **for any arc table** (`Arcs`: the 8 DSP arcs the cascade uses, plus the
  PCOUT→PCIN / ACOUT→ACIN cascade-wire window `cw`), if the four operand slices at the DSP pins
  are constant on `[T0, T1]` then at every `t ∈ [T0 + settleHi, T1 + settleLo]` the head P and
  tail P ports carry defined words whose bundled 32-bit output is `muli32 va vb` — C's
  multiply. `settleHi` is the max over all 9 pin-to-output paths of the summed arc maxima
  (per path, not per cell), `settleLo` the min of the summed minima.
* `ipow_bundled`: the bundled-data reading: a request that samples the output `dreq` after the
  operands are stable at the pins reads the product if `dreq ≥ settleHi` (and the operands are
  held until `T0 + dreq - settleLo`).
* `settle_px`: with prjxray-db and zero cascade-wire delay: settleHi = **7267 ps slow / 3074 ps
  fast**, settleLo = 1310 slow / 571 fast. `settle_np`: with nextpnr's routed-SDF values
  (one number per port pair) settleHi = 12310 ps (its A→ACOUT is 5400 ps; prjxray says
  ≤ 723). `nextpnr_vs_prjxray`: nextpnr's SDF is BELOW prjxray's slow max on two arcs
  (B→PCOUT 3850 < 3851, PCIN→PCOUT 1710 < 1713), above it on the others.
* `lumped_tight`: the bound cannot be shortened in this model: for any band with lo < hi there
  is an admissible behaviour whose output at `T0 + hi - 1` is X, and one whose output there is
  a defined wrong word (a glitch to a value that is neither the old nor the new result).

## NOT modelled
Fabric routing to the A/B pins and from P (compose with `Lumped.constOn` on identity wires;
their maxima add to `settleHi`), the real cascade-wire delay (parameter `cw`; 0 in `settle_px`),
any correlation between arcs (each lumped window is independent: no corner-correlation κ), the
capture latch's setup/hold, pulse filtering inside the DSP, X on an internal bus being shorter
than the window, the registered modes (unused), and whether prjxray-db's DSP numbers are
right for this part (they are the database's; nothing here measures them).
-/

namespace Formal.Core.Prims.DspTimed
open Formal.Core.Prims Formal.Core.Prims.Dsp Formal.Core.Prims.DspData

/-! ## 1. The lumped stage -/

/-- Lumped bounded-delay stage with per-input windows `W i = (lo, hi)`. -/
def Lumped {k : Nat} (W : Fin k → Int × Int) (f : (Fin k → Nat) → Nat)
    (x : Fin k → Int → Option Nat) (y : Int → Option Nat) : Prop :=
  ∀ (t : Int) (v : Fin k → Nat),
    (∀ i s, t - (W i).2 ≤ s → s ≤ t - (W i).1 → x i s = some (v i)) → y t = some (f v)

/-- `x` carries the defined word `n` throughout `[S, E]`. -/
def ConstOn (x : Int → Option Nat) (n : Nat) (S E : Int) : Prop :=
  ∀ s, S ≤ s → s ≤ E → x s = some n

theorem Lumped.constOn {k : Nat} {W : Fin k → Int × Int} {f : (Fin k → Nat) → Nat}
    {x : Fin k → Int → Option Nat} {y : Int → Option Nat} (h : Lumped W f x y)
    {v : Fin k → Nat} {S E : Fin k → Int} (hx : ∀ i, ConstOn (x i) (v i) (S i) (E i))
    {S' E' : Int} (hS : ∀ i, S i + (W i).2 ≤ S') (hE : ∀ i, E' ≤ E i + (W i).1) :
    ConstOn y (f v) S' E' := by
  intro t h1 h2
  exact h t v (fun i s hs1 hs2 => hx i s (by have := hS i; omega) (by have := hE i; omega))

/-- Per-input transport with delays inside the windows is one behaviour of the lumped stage. -/
theorem transport_lumped {k : Nat} (W : Fin k → Int × Int) (f : (Fin k → Nat) → Nat)
    (x : Fin k → Int → Option Nat) (y : Int → Option Nat) (d : Fin k → Int)
    (hd : ∀ i, (W i).1 ≤ d i ∧ d i ≤ (W i).2)
    (hy : ∀ t v, (∀ i, x i (t - d i) = some (v i)) → y t = some (f v)) : Lumped W f x y :=
  fun t v hv => hy t v (fun i => hv i _ (by have := hd i; omega) (by have := hd i; omega))

/-! ## 2. The lumped stage admits any behaviour inside the window (tightness) -/

/-- A step input: `u` before time 0, `v` from time 0. -/
def stepX (u v : Nat) : Fin 1 → Int → Option Nat := fun _ s => if s < 0 then some u else some v

/-- An output that is right outside `[l, h)` and follows the arbitrary `g` inside it. -/
def junkY (l h : Int) (f : (Fin 1 → Nat) → Nat) (u v : Nat) (g : Int → Option Nat) :
    Int → Option Nat :=
  fun t => if h ≤ t then some (f fun _ => v) else if t < l then some (f fun _ => u) else g t

theorem fin1_eq (i : Fin 1) : i = 0 := Fin.ext (by have := i.isLt; show i.val = 0; omega)

/-- **Anything goes inside the window**: for ANY `g`, the trace that follows `g` on `[l, h)`
after a step at 0 is an admissible behaviour of the lumped stage. -/
theorem lumped_admits_anything (l h : Int) (hlh : l ≤ h) (f : (Fin 1 → Nat) → Nat)
    (u v : Nat) (huv : u ≠ v) (g : Int → Option Nat) :
    Lumped (fun _ => (l, h)) f (stepX u v) (junkY l h f u v g) := by
  intro t w hw
  have hw0 : ∀ s, t - h ≤ s → s ≤ t - l → stepX u v 0 s = some (w 0) := hw 0
  have hfun : ∀ n : Nat, w 0 = n → (f fun _ => n) = f w := fun n hn => by
    congr 1; funext i; rw [fin1_eq i, hn]
  unfold junkY
  by_cases ht : h ≤ t
  · rw [if_pos ht]
    have e := hw0 (t - l) (by omega) (by omega)
    unfold stepX at e; rw [if_neg (by omega)] at e
    rw [hfun v (Option.some.inj e).symm]
  · rw [if_neg ht]
    by_cases ht2 : t < l
    · rw [if_pos ht2]
      have e := hw0 (t - h) (by omega) (by omega)
      unfold stepX at e; rw [if_pos (by omega)] at e
      rw [hfun u (Option.some.inj e).symm]
    · exfalso
      have e1 := hw0 (t - h) (by omega) (by omega)
      have e2 := hw0 (t - l) (by omega) (by omega)
      unfold stepX at e1 e2
      rw [if_pos (by omega)] at e1
      rw [if_neg (by omega)] at e2
      exact huv (Option.some.inj (e1.trans e2.symm))

/-- A defined word that is neither `f u` nor `f v`. -/
def junkVal (f : (Fin 1 → Nat) → Nat) (u v : Nat) : Nat := (f fun _ => u) + (f fun _ => v) + 1

/-- **The settle bound is tight**: one sample before `T0 + hi` (T0 = 0, the input is constant
`v` from 0 on), the model allows an X output, and also a defined output that is neither the old
nor the new value (a glitch). -/
theorem lumped_tight (l h : Int) (hlh : l < h) (f : (Fin 1 → Nat) → Nat) (u v : Nat)
    (huv : u ≠ v) :
    ConstOn (stepX u v 0) v 0 h ∧
    Lumped (fun _ => (l, h)) f (stepX u v) (junkY l h f u v fun _ => none) ∧
    junkY l h f u v (fun _ => none) (h - 1) = none ∧
    Lumped (fun _ => (l, h)) f (stepX u v) (junkY l h f u v fun _ => some (junkVal f u v)) ∧
    junkY l h f u v (fun _ => some (junkVal f u v)) (h - 1) = some (junkVal f u v) ∧
    junkVal f u v ≠ (f fun _ => u) ∧ junkVal f u v ≠ (f fun _ => v) := by
  refine ⟨fun s hs _ => ?_, lumped_admits_anything l h (by omega) f u v huv _, ?_,
    lumped_admits_anything l h (by omega) f u v huv _, ?_, ?_, ?_⟩
  · unfold stepX; rw [if_neg (by omega)]
  · unfold junkY; rw [if_neg (by omega), if_neg (by omega)]
  · unfold junkY; rw [if_neg (by omega), if_neg (by omega)]
  · unfold junkVal; omega
  · unfold junkVal; omega

/-! ## 3. The ipow cascade -/

/-- Vectors of one, two, three items (no Mathlib `![]`). -/
def one1 {α : Type} (p : α) : Fin 1 → α := fun _ => p
def two {α : Type} (p q : α) : Fin 2 → α := fun i => if i.val = 0 then p else q
def three {α : Type} (p q r : α) : Fin 3 → α :=
  fun i => if i.val = 0 then p else if i.val = 1 then q else r

theorem forall_one {P : Fin 1 → Prop} (h0 : P 0) : ∀ i, P i := fun i => by rw [fin1_eq i]; exact h0
theorem forall_two {P : Fin 2 → Prop} (h0 : P 0) (h1 : P 1) : ∀ i, P i := by
  intro ⟨i, hi⟩
  match i, hi with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | n + 2, h => exact absurd h (by omega)
theorem forall_three {P : Fin 3 → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ i, P i := by
  intro ⟨i, hi⟩
  match i, hi with
  | 0, _ => exact h0
  | 1, _ => exact h1
  | 2, _ => exact h2
  | n + 3, h => exact absurd h (by omega)

/-- The arc windows `(lo, hi)` the cascade uses, at one corner. -/
structure Arcs where
  aP : Int × Int
  aPC : Int × Int
  aAC : Int × Int
  acinPC : Int × Int
  bP : Int × Int
  bPC : Int × Int
  pcinP : Int × Int
  pcinPC : Int × Int
  deriving DecidableEq, Repr

/-- One corner of a prjxray band as a window. -/
def win (b : Band) (c : Corner) : Int × Int := (b.lo c, b.hi c)

/-- prjxray-db's arcs at corner `c` (never mixing corners). -/
def pxArcs (c : Corner) : Arcs :=
  ⟨win pxA_P c, win pxA_PCOUT c, win pxA_ACOUT c, win pxACIN_PCOUT c, win pxB_P c,
   win pxB_PCOUT c, win pxPCIN_P c, win pxPCIN_PCOUT c⟩

/-- A single nextpnr SDF value as a window (missing arc read as 0: only used for display). -/
def npw (o : Option Int) : Int × Int := (o.getD 0, o.getD 0)

/-- The values nextpnr wrote into the routed SDF. -/
def npArcs : Arcs :=
  ⟨npw npA_P, npw npA_PCOUT, npw npA_ACOUT, npw npACIN_PCOUT, npw npB_P, npw npB_PCOUT,
   npw npPCIN_P, npw npPCIN_PCOUT⟩

section Bounds
variable (r : Arcs) (cw : Int × Int)

/-- Head PCOUT settles `sPcH` after the operands, holds `ePcH` after they change. -/
def sPcH : Int := max r.aPC.2 r.bPC.2
def ePcH : Int := min r.aPC.1 r.bPC.1
/-- Middle PCOUT: via ACOUT→ACIN, via B = b[31:17], via head PCOUT→PCIN. -/
def sPcM : Int := max (max (r.aAC.2 + cw.2 + r.acinPC.2) r.bPC.2) (sPcH r + cw.2 + r.pcinPC.2)
def ePcM : Int := min (min (r.aAC.1 + cw.1 + r.acinPC.1) r.bPC.1) (ePcH r + cw.1 + r.pcinPC.1)
/-- Tail P: A = a[31:17], B = b[16:0], middle PCOUT→PCIN. -/
def sPT : Int := max (max r.aP.2 r.bP.2) (sPcM r cw + cw.2 + r.pcinP.2)
def ePT : Int := min (min r.aP.1 r.bP.1) (ePcM r cw + cw.1 + r.pcinP.1)
/-- Head P. -/
def sPH : Int := max r.aP.2 r.bP.2
def ePH : Int := min r.aP.1 r.bP.1
/-- The settle bound of the whole 32-bit output, and its hold bound. -/
def settleHi : Int := max (sPH r) (sPT r cw)
def settleLo : Int := min (ePH r) (ePT r cw)

end Bounds

theorem settle_px :
    settleHi (pxArcs .slow) (0, 0) = 7267 ∧ settleHi (pxArcs .fast) (0, 0) = 3074 ∧
    settleLo (pxArcs .slow) (0, 0) = 1310 ∧ settleLo (pxArcs .fast) (0, 0) = 571 := by decide

theorem settle_np : settleHi npArcs (0, 0) = 12310 ∧ settleLo npArcs (0, 0) = 3850 := by decide

theorem nextpnr_vs_prjxray :
    npB_PCOUT = some 3850 ∧ pxB_PCOUT.smax = 3851 ∧
    npPCIN_PCOUT = some 1710 ∧ pxPCIN_PCOUT.smax = 1713 ∧
    npA_ACOUT = some 5400 ∧ pxA_ACOUT.smax = 723 ∧
    npA_P = some 5400 ∧ pxA_P.smax = 3841 ∧ npB_P = some 3850 ∧ pxB_P.smax = 3656 ∧
    npPCIN_P = some 1710 ∧ pxPCIN_P.smax = 1518 ∧ npACIN_PCOUT = some 5200 ∧
    pxACIN_PCOUT.smax = 3833 ∧ npA_PCOUT = some 5400 ∧ pxA_PCOUT.smax = 4036 := by decide

/-- **The ipow multiply settles to C's product.** Operand slices at the DSP pins
`a0 = a[16:0]`, `a1 = a[31:17]`, `b0 = b[16:0]`, `b1 = b[31:17]` constant on `[T0, T1]`; every
DSP port a lumped stage with the windows of `r`; the cascade wires lumped with window `cw`.
Then on `[T0 + settleHi, T1 + settleLo]` the two output ports carry defined words whose bundled
output `w_n36` is `muli32 va vb`. -/
theorem ipow_mul_settles (r : Arcs) (cw : Int × Int)
    (a0 a1 b0 b1 pH pcH acH pcHi acHi pcM pcMi pT : Int → Option Nat)
    (va vb : Nat) (T0 T1 : Int)
    (hA0 : ConstOn a0 (lo17 va) T0 T1) (hA1 : ConstOn a1 (hi15 va) T0 T1)
    (hB0 : ConstOn b0 (lo17 vb) T0 T1) (hB1 : ConstOn b1 (hi15 vb) T0 T1)
    (sP : Lumped (two r.aP r.bP) (fun v => pOut .zero (v 0) (v 1) 0) (two a0 b0) pH)
    (sPC : Lumped (two r.aPC r.bPC) (fun v => pOut .zero (v 0) (v 1) 0) (two a0 b0) pcH)
    (sAC : Lumped (one1 r.aAC) (fun v => acoutF head.aCascade (v 0) 0) (one1 a0) acH)
    (wPC : Lumped (one1 cw) (fun v => v 0) (one1 pcH) pcHi)
    (wAC : Lumped (one1 cw) (fun v => v 0) (one1 acH) acHi)
    (sM : Lumped (three r.acinPC r.bPC r.pcinPC)
      (fun v => pOut .pcinShr17 (acoutF mid.aCascade 0 (v 0)) (v 1) (v 2)) (three acHi b1 pcHi) pcM)
    (wM : Lumped (one1 cw) (fun v => v 0) (one1 pcM) pcMi)
    (sT : Lumped (three r.aP r.bP r.pcinP) (fun v => pOut .pcin (v 0) (v 1) (v 2))
      (three a1 b0 pcMi) pT) :
    ∀ t, T0 + settleHi r cw ≤ t → t ≤ T1 + settleLo r cw →
      ∃ ph pt, pH t = some ph ∧ pT t = some pt ∧
        ph % 2 ^ 17 + 2 ^ 17 * (pt % 2 ^ 15) = muli32 va vb := by
  have cP : ConstOn pH (headP va vb) (T0 + sPH r) (T1 + ePH r) :=
    sP.constOn (v := two (lo17 va) (lo17 vb)) (S := fun _ => T0) (E := fun _ => T1)
      (forall_two hA0 hB0)
      (forall_two (by show T0 + r.aP.2 ≤ _; unfold sPH; omega)
        (by show T0 + r.bP.2 ≤ _; unfold sPH; omega))
      (forall_two (by show _ ≤ T1 + r.aP.1; unfold ePH; omega)
        (by show _ ≤ T1 + r.bP.1; unfold ePH; omega))
  have cPC : ConstOn pcH (headP va vb) (T0 + sPcH r) (T1 + ePcH r) :=
    sPC.constOn (v := two (lo17 va) (lo17 vb)) (S := fun _ => T0) (E := fun _ => T1)
      (forall_two hA0 hB0)
      (forall_two (by show T0 + r.aPC.2 ≤ _; unfold sPcH; omega)
        (by show T0 + r.bPC.2 ≤ _; unfold sPcH; omega))
      (forall_two (by show _ ≤ T1 + r.aPC.1; unfold ePcH; omega)
        (by show _ ≤ T1 + r.bPC.1; unfold ePcH; omega))
  have cAC : ConstOn acH (headAc va) (T0 + r.aAC.2) (T1 + r.aAC.1) :=
    sAC.constOn (v := one1 (lo17 va)) (S := fun _ => T0) (E := fun _ => T1)
      (forall_one hA0) (forall_one (Int.le_refl _)) (forall_one (Int.le_refl _))
  have cPCi : ConstOn pcHi (headP va vb) (T0 + sPcH r + cw.2) (T1 + ePcH r + cw.1) :=
    wPC.constOn (v := one1 (headP va vb)) (S := fun _ => T0 + sPcH r) (E := fun _ => T1 + ePcH r)
      (forall_one cPC) (forall_one (Int.le_refl _)) (forall_one (Int.le_refl _))
  have cACi : ConstOn acHi (headAc va) (T0 + r.aAC.2 + cw.2) (T1 + r.aAC.1 + cw.1) :=
    wAC.constOn (v := one1 (headAc va)) (S := fun _ => T0 + r.aAC.2) (E := fun _ => T1 + r.aAC.1)
      (forall_one cAC) (forall_one (Int.le_refl _)) (forall_one (Int.le_refl _))
  have cM : ConstOn pcM (midP va vb) (T0 + sPcM r cw) (T1 + ePcM r cw) :=
    sM.constOn (v := three (headAc va) (hi15 vb) (headP va vb))
      (S := three (T0 + r.aAC.2 + cw.2) T0 (T0 + sPcH r + cw.2))
      (E := three (T1 + r.aAC.1 + cw.1) T1 (T1 + ePcH r + cw.1))
      (forall_three cACi hB1 cPCi)
      (forall_three (by show T0 + r.aAC.2 + cw.2 + r.acinPC.2 ≤ _; unfold sPcM; omega)
        (by show T0 + r.bPC.2 ≤ _; unfold sPcM; omega)
        (by show T0 + sPcH r + cw.2 + r.pcinPC.2 ≤ _; unfold sPcM; omega))
      (forall_three (by show _ ≤ T1 + r.aAC.1 + cw.1 + r.acinPC.1; unfold ePcM; omega)
        (by show _ ≤ T1 + r.bPC.1; unfold ePcM; omega)
        (by show _ ≤ T1 + ePcH r + cw.1 + r.pcinPC.1; unfold ePcM; omega))
  have cMi : ConstOn pcMi (midP va vb) (T0 + sPcM r cw + cw.2) (T1 + ePcM r cw + cw.1) :=
    wM.constOn (v := one1 (midP va vb)) (S := fun _ => T0 + sPcM r cw)
      (E := fun _ => T1 + ePcM r cw)
      (forall_one cM) (forall_one (Int.le_refl _)) (forall_one (Int.le_refl _))
  have cT : ConstOn pT (tailP va vb) (T0 + sPT r cw) (T1 + ePT r cw) :=
    sT.constOn (v := three (hi15 va) (lo17 vb) (midP va vb))
      (S := three T0 T0 (T0 + sPcM r cw + cw.2))
      (E := three T1 T1 (T1 + ePcM r cw + cw.1))
      (forall_three hA1 hB0 cMi)
      (forall_three (by show T0 + r.aP.2 ≤ _; unfold sPT; omega)
        (by show T0 + r.bP.2 ≤ _; unfold sPT; omega)
        (by show T0 + sPcM r cw + cw.2 + r.pcinP.2 ≤ _; unfold sPT; omega))
      (forall_three (by show _ ≤ T1 + r.aP.1; unfold ePT; omega)
        (by show _ ≤ T1 + r.bP.1; unfold ePT; omega)
        (by show _ ≤ T1 + ePcM r cw + cw.1 + r.pcinP.1; unfold ePT; omega))
  intro t h1 h2
  unfold settleHi at h1
  unfold settleLo at h2
  refine ⟨headP va vb, tailP va vb, cP t (by omega) (by omega), cT t (by omega) (by omega), ?_⟩
  exact ipowMul_eq va vb

/-- **Bundled-data reading.** Operands stable at the DSP pins from `T0` until `T1`, the request
samples the output `dreq` later. If `dreq ≥ settleHi` and the operands are held at least until
`T0 + dreq - settleLo`, the sampled word is C's product. With prjxray at the slow corner and
zero cascade-wire delay this asks for `dreq ≥ 7267 ps` beyond the pin arrival (`settle_px`);
the fabric routes in and out add their own maxima. -/
theorem ipow_bundled (r : Arcs) (cw : Int × Int)
    (a0 a1 b0 b1 pH pcH acH pcHi acHi pcM pcMi pT : Int → Option Nat)
    (va vb : Nat) (T0 T1 dreq : Int)
    (hA0 : ConstOn a0 (lo17 va) T0 T1) (hA1 : ConstOn a1 (hi15 va) T0 T1)
    (hB0 : ConstOn b0 (lo17 vb) T0 T1) (hB1 : ConstOn b1 (hi15 vb) T0 T1)
    (sP : Lumped (two r.aP r.bP) (fun v => pOut .zero (v 0) (v 1) 0) (two a0 b0) pH)
    (sPC : Lumped (two r.aPC r.bPC) (fun v => pOut .zero (v 0) (v 1) 0) (two a0 b0) pcH)
    (sAC : Lumped (one1 r.aAC) (fun v => acoutF head.aCascade (v 0) 0) (one1 a0) acH)
    (wPC : Lumped (one1 cw) (fun v => v 0) (one1 pcH) pcHi)
    (wAC : Lumped (one1 cw) (fun v => v 0) (one1 acH) acHi)
    (sM : Lumped (three r.acinPC r.bPC r.pcinPC)
      (fun v => pOut .pcinShr17 (acoutF mid.aCascade 0 (v 0)) (v 1) (v 2)) (three acHi b1 pcHi) pcM)
    (wM : Lumped (one1 cw) (fun v => v 0) (one1 pcM) pcMi)
    (sT : Lumped (three r.aP r.bP r.pcinP) (fun v => pOut .pcin (v 0) (v 1) (v 2))
      (three a1 b0 pcMi) pT)
    (hreq : settleHi r cw ≤ dreq) (hhold : T0 + dreq ≤ T1 + settleLo r cw) :
    ∃ ph pt, pH (T0 + dreq) = some ph ∧ pT (T0 + dreq) = some pt ∧
      ph % 2 ^ 17 + 2 ^ 17 * (pt % 2 ^ 15) = muli32 va vb :=
  ipow_mul_settles r cw a0 a1 b0 b1 pH pcH acH pcHi acHi pcM pcMi pT va vb T0 T1
    hA0 hA1 hB0 hB1 sP sPC sAC wPC wAC sM wM sT (T0 + dreq) (by omega) hhold

/-- Constant signals satisfy a lumped stage whose windows are non-empty. -/
theorem lumped_const {k : Nat} (W : Fin k → Int × Int) (hW : ∀ i, (W i).1 ≤ (W i).2)
    (f : (Fin k → Nat) → Nat) (x : Fin k → Int → Option Nat) (y : Int → Option Nat)
    (v0 : Fin k → Nat) (hx : ∀ i s, x i s = some (v0 i)) (hy : ∀ t, y t = some (f v0)) :
    Lumped W f x y := by
  intro t v hv
  have : v = v0 := funext fun i =>
    (Option.some.inj ((hx i (t - (W i).2)).symm.trans
      (hv i (t - (W i).2) (Int.le_refl _) (by have := hW i; omega)))).symm
  rw [hy t, this]

/-- The signal that is the defined word `n` at every time. -/
def kst (n : Nat) : Int → Option Nat := fun _ => some n

theorem pxArcs_slow_nonempty :
    (pxArcs .slow).aP.1 ≤ (pxArcs .slow).aP.2 ∧ (pxArcs .slow).aPC.1 ≤ (pxArcs .slow).aPC.2 ∧
    (pxArcs .slow).aAC.1 ≤ (pxArcs .slow).aAC.2 ∧
    (pxArcs .slow).acinPC.1 ≤ (pxArcs .slow).acinPC.2 ∧
    (pxArcs .slow).bP.1 ≤ (pxArcs .slow).bP.2 ∧ (pxArcs .slow).bPC.1 ≤ (pxArcs .slow).bPC.2 ∧
    (pxArcs .slow).pcinP.1 ≤ (pxArcs .slow).pcinP.2 ∧
    (pxArcs .slow).pcinPC.1 ≤ (pxArcs .slow).pcinPC.2 := by decide

/-- **Non-vacuity** of `ipow_mul_settles` at the prjxray slow corner, zero cascade wires: the
signals that hold every port at its final word satisfy every hypothesis at once, and the
sampling interval `[0 + 7267, 10000 + 1310]` is non-empty. (A degenerate run: the operands
never change. It shows the hypotheses are consistent, not that they describe silicon.) -/
theorem ipow_mul_nonvacuous (va vb : Nat) :
    ConstOn (kst (lo17 va)) (lo17 va) 0 10000 ∧ ConstOn (kst (hi15 va)) (hi15 va) 0 10000 ∧
    ConstOn (kst (lo17 vb)) (lo17 vb) 0 10000 ∧ ConstOn (kst (hi15 vb)) (hi15 vb) 0 10000 ∧
    Lumped (two (pxArcs .slow).aP (pxArcs .slow).bP) (fun v => pOut .zero (v 0) (v 1) 0)
      (two (kst (lo17 va)) (kst (lo17 vb))) (kst (headP va vb)) ∧
    Lumped (two (pxArcs .slow).aPC (pxArcs .slow).bPC) (fun v => pOut .zero (v 0) (v 1) 0)
      (two (kst (lo17 va)) (kst (lo17 vb))) (kst (headP va vb)) ∧
    Lumped (one1 (pxArcs .slow).aAC) (fun v => acoutF head.aCascade (v 0) 0) (one1 (kst (lo17 va)))
      (kst (headAc va)) ∧
    Lumped (one1 ((0, 0) : Int × Int)) (fun v => v 0) (one1 (kst (headP va vb))) (kst (headP va vb)) ∧
    Lumped (one1 ((0, 0) : Int × Int)) (fun v => v 0) (one1 (kst (headAc va))) (kst (headAc va)) ∧
    Lumped (three (pxArcs .slow).acinPC (pxArcs .slow).bPC (pxArcs .slow).pcinPC)
      (fun v => pOut .pcinShr17 (acoutF mid.aCascade 0 (v 0)) (v 1) (v 2))
      (three (kst (headAc va)) (kst (hi15 vb)) (kst (headP va vb))) (kst (midP va vb)) ∧
    Lumped (one1 ((0, 0) : Int × Int)) (fun v => v 0) (one1 (kst (midP va vb))) (kst (midP va vb)) ∧
    Lumped (three (pxArcs .slow).aP (pxArcs .slow).bP (pxArcs .slow).pcinP) (fun v => pOut .pcin (v 0) (v 1) (v 2))
      (three (kst (hi15 va)) (kst (lo17 vb)) (kst (midP va vb))) (kst (tailP va vb)) ∧
    0 + settleHi (pxArcs .slow) (0, 0) ≤ 10000 + settleLo (pxArcs .slow) (0, 0) := by
  obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8⟩ := pxArcs_slow_nonempty
  refine ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl,
    lumped_const _ (forall_two h1 h5) _ _ _ (two (lo17 va) (lo17 vb))
      (forall_two (fun _ => rfl) (fun _ => rfl)) (fun _ => rfl),
    lumped_const _ (forall_two h2 h6) _ _ _ (two (lo17 va) (lo17 vb))
      (forall_two (fun _ => rfl) (fun _ => rfl)) (fun _ => rfl),
    lumped_const _ (forall_one h3) _ _ _ (one1 (lo17 va)) (forall_one (fun _ => rfl))
      (fun _ => rfl),
    lumped_const _ (forall_one (by decide)) _ _ _ (one1 (headP va vb))
      (forall_one (fun _ => rfl)) (fun _ => rfl),
    lumped_const _ (forall_one (by decide)) _ _ _ (one1 (headAc va))
      (forall_one (fun _ => rfl)) (fun _ => rfl),
    lumped_const _ (forall_three h4 h6 h8) _ _ _ (three (headAc va) (hi15 vb) (headP va vb))
      (forall_three (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) (fun _ => rfl),
    lumped_const _ (forall_one (by decide)) _ _ _ (one1 (midP va vb))
      (forall_one (fun _ => rfl)) (fun _ => rfl),
    lumped_const _ (forall_three h1 h5 h7) _ _ _ (three (hi15 va) (lo17 vb) (midP va vb))
      (forall_three (fun _ => rfl) (fun _ => rfl) (fun _ => rfl)) (fun _ => rfl),
    by decide⟩

end Formal.Core.Prims.DspTimed
