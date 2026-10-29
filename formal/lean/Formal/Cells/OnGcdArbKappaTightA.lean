import Formal.Cells.OnGcdArbKappa
import Formal.Cells.OnGcdArbKappaTight

/-!
# Probe Bkx19, bridge: the exact threshold on `OnGcdArbKappa`'s own objects

Shard B, 2026-10-29. Needs Mathlib (through `CornerNat`). WIP: NOT checked (see the note). Note: `formal/notes/B-gcd-arb-kappa-tight.md`.

`OnGcdArbKappaTight` is core-only and restates A's `CornerNat` definitions. This file shows the
restatement is definitional (`scat_iff` is `Iff.rfl`) and transfers the headline results to
`OnGcdArbKappa.model k .lit F_rt1b v_g3_merge12_uarb1` over all 35 arc ids `E`:

* `A_rt1b_safe`: κ ≤ κS ⟹ `AllOK` (A's `ConstraintsKappa.AllOK`) for the row;
* `A_rt1b_unsafe`: κ ≥ κU ⟹ ¬ `AllOK`, witnessed by a realization `dE` of ALL 35 arcs at the
  corner `27/5295104` (the 7 arcs of the form as `dU`, every other arc at ⌊(1+κU)·nominal⌋);
* `A_gap_closed`: OnGcdArbKappa's row bounds `κ* = 16587/374773 < κS < κU < κu = 33181/749546`;
* `A_rt1b_gate_unsafe`: every hypothesis of `OnGcdArbKappa.rt1b_gate` except `holds d F_rt1b`
  is met by `dE`, `DU`, `SU`, and the grants overlap: the arc form is necessary for the gate
  theorem at κ ≥ κU.

Assumed / proved / NOT covered: as `OnGcdArbKappaTight`.
-/

namespace Formal.Cells.OnGcdArbKappaTightA

open Formal.Cells

def toK (k : Formal.Core.Substrate.Kappa) : OnGcdArbKappaTight.Kappa :=
  ⟨k.num, k.den, k.den_pos, k.num_le⟩
def toC (c : Formal.Core.Substrate.Corner) : OnGcdArbKappaTight.Corner := ⟨c.w0, c.w1, c.pos⟩
def toA (a : Formal.Core.Substrate.CArc) : OnGcdArbKappaTight.CArc := ⟨a.F, a.S, a.F_le_S⟩

/-- The restated `Scat` IS A's `Scat`. -/
theorem scat_iff (k : Formal.Core.Substrate.Kappa) (c : Formal.Core.Substrate.Corner)
    (a : Formal.Core.Substrate.CArc) (d : Nat) :
    Formal.Core.Substrate.Scat k c a d ↔ OnGcdArbKappaTight.Scat (toK k) (toC c) (toA a) d :=
  Iff.rfl

def emb : OnGcdArbKappaTight.A7 → OnGcdArbKappa.E
  | .rg2 => .rg2
  | .ag2r => .ag2r
  | .qgw => .qgw
  | .pqg => .pqg
  | .rs2 => .rs2
  | .aR2 => .aR2
  | .ag1q => .ag1q

abbrev MA (k : Formal.Core.Substrate.Kappa) : Formal.Core.Substrate.CornerModel OnGcdArbKappa.E :=
  OnGcdArbKappa.model k .lit OnGcdArbKappa.F_rt1b OnGcdArbKappa.v_g3_merge12_uarb1

theorem arc_eq (k : Formal.Core.Substrate.Kappa) (e : OnGcdArbKappaTight.A7) :
    toA ((MA k).arc (emb e)) = OnGcdArbKappaTight.litArc e := by
  cases e <;> rfl

theorem pathP (d : OnGcdArbKappa.E → Nat) :
    Formal.Core.Substrate.pathDelay d OnGcdArbKappa.F_rt1b.P =
      OnGcdArbKappaTight.pathDelay (fun e => d (emb e)) OnGcdArbKappaTight.P7 := rfl
theorem pathQ (d : OnGcdArbKappa.E → Nat) :
    Formal.Core.Substrate.pathDelay d OnGcdArbKappa.F_rt1b.Q =
      OnGcdArbKappaTight.pathDelay (fun e => d (emb e)) OnGcdArbKappaTight.Q7 := rfl

/-- **Safe side on A's objects.** -/
theorem A_rt1b_safe (k : Formal.Core.Substrate.Kappa)
    (H_KAPPA : k.num * 749546000000 ≤ k.den * 33176932320) :
    ConstraintsKappa.AllOK (MA k) OnGcdArbKappa.F_rt1b.P OnGcdArbKappa.F_rt1b.Q 0 0 := by
  intro d ⟨c, hc⟩
  have h := OnGcdArbKappaTight.rt1b_safe (toK k) H_KAPPA (fun e => d (emb e))
    ⟨toC c, fun e => by have := (scat_iff _ _ _ _).1 (hc (emb e)); rw [arc_eq] at this; exact this⟩
  rw [pathP, pathQ]; exact h

def cA : Formal.Core.Substrate.Corner := ⟨5295077, 27, by decide⟩
def kUA : Formal.Core.Substrate.Kappa := ⟨33176932321, 749546000000, by decide, by decide⟩

/-- A realization of all 35 arcs at `cA`, `κU` (fs). -/
def dE : OnGcdArbKappa.E → Nat
  | .ac => 38376
  | .dS1 => 0
  | .dS2 => 165110
  | .d12 => 0
  | .es => 94991
  | .e1 => 101441
  | .e2 => 39682
  | .ps => 114870
  | .p1 => 89807
  | .p2 => 89807
  | .cq => 86442
  | .qs => 220341
  | .qgw => 36319
  | .pqg => 32496
  | .rs1 => 275650
  | .rg1 => 208817
  | .rs2 => 217299
  | .rg2 => 327052
  | .gw1 => 348203
  | .pg1 => 113825
  | .gw2 => 128484
  | .pg2 => 111737
  | .fa1 => 325995
  | .fa2 => 110379
  | .aq => 46992
  | .aRq => 45948
  | .aR1 => 44903
  | .aR2 => 42053
  | .ag1q => 45876
  | .ag1r => 43859
  | .ag2 => 46992
  | .ac1 => 46992
  | .ac2 => 46992
  | .ag2r => 46992
  | .srv => 909561

theorem dE_realizes : (MA kUA).RealizesAt cA dE := by
  intro e; cases e <;> decide

theorem dE_realizes_ge (k : Formal.Core.Substrate.Kappa)
    (H_KAPPA : k.den * 33176932321 ≤ k.num * 749546000000) : (MA k).RealizesAt cA dE := by
  intro e
  have hk : (toK kUA).num * (toK k).den ≤ (toK k).num * (toK kUA).den := by
    show 33176932321 * k.den ≤ k.num * 749546000000
    rw [Nat.mul_comm 33176932321]; exact H_KAPPA
  exact (scat_iff _ _ _ _).2
    (OnGcdArbKappaTight.scat_mono hk ((scat_iff _ _ _ _).1 (dE_realizes e)))

theorem dE_viol :
    Formal.Core.Substrate.pathDelay dE OnGcdArbKappa.F_rt1b.Q + 1 =
      Formal.Core.Substrate.pathDelay dE OnGcdArbKappa.F_rt1b.P := by decide

/-- **Unsafe side on A's objects.** -/
theorem A_rt1b_unsafe (k : Formal.Core.Substrate.Kappa)
    (H_KAPPA : k.den * 33176932321 ≤ k.num * 749546000000) :
    ¬ ConstraintsKappa.AllOK (MA k) OnGcdArbKappa.F_rt1b.P OnGcdArbKappa.F_rt1b.Q 0 0 := by
  intro h
  have := h dE ⟨cA, dE_realizes_ge k H_KAPPA⟩
  have := dE_viol
  omega

/-- **The gap of `OnGcdArbKappa`'s row closed** to `1/749546000000`. -/
theorem A_gap_closed :
    OnGcdArbKappa.R_g3_merge12_uarb1_lit_rt1b.p = 16587 ∧
    OnGcdArbKappa.R_g3_merge12_uarb1_lit_rt1b.q = 374773 ∧
    OnGcdArbKappa.R_g3_merge12_uarb1_lit_rt1b.pu = 33181 ∧
    OnGcdArbKappa.R_g3_merge12_uarb1_lit_rt1b.qu = 749546 ∧
    16587 * 749546000000 < 33176932320 * 374773 ∧ 33176932321 * 749546 < 33181 * 749546000000 :=
  ⟨rfl, rfl, rfl, rfl, by decide, by decide⟩

theorem qOf_real2 : OnGcdArbFix.Real2 (OnGcdArbKappa.qOf dE) 0 0 OnGcdArbKappaTight.DU := by
  unfold OnGcdArbFix.Real2; simp [OnGcdArbKappa.qOf, dE, OnGcdArbKappaTight.DU]

/-- **`rt1b_gate`'s arc hypothesis is necessary at κ ≥ κU.** -/
theorem A_rt1b_gate_unsafe (k : Formal.Core.Substrate.Kappa)
    (H_KAPPA : k.den * 33176932321 ≤ k.num * 749546000000) :
    (MA k).Realizes dE ∧ ¬ OnGcdArbKappa.holds dE OnGcdArbKappa.F_rt1b ∧
    OnGcdArbFix.Real2 (OnGcdArbKappa.qOf dE) 0 0 OnGcdArbKappaTight.DU ∧
    ArbHeldTimed.Run OnGcdArbKappaTight.DU OnGcdArbKappaTight.SU ∧
    ArbHeldTimed2.Scn2 OnGcdArbKappaTight.DU OnGcdArbKappaTight.SU 0 (-1) 259352 259353 400000 ∧
    (OnGcdArbKappaTight.SU.g1 374043 && OnGcdArbKappaTight.SU.g2 374043) = true := by
  refine ⟨⟨cA, dE_realizes_ge k H_KAPPA⟩, ?_, qOf_real2, OnGcdArbKappaTight.SU_run,
    OnGcdArbKappaTight.SU_scn 400000 (by omega), ?_⟩
  · unfold OnGcdArbKappa.holds; have := dE_viol; simp only [OnGcdArbKappa.F_rt1b] at this ⊢; omega
  · rw [OnGcdArbKappaTight.SU_overlap.1, OnGcdArbKappaTight.SU_overlap.2]; rfl

end Formal.Cells.OnGcdArbKappaTightA
