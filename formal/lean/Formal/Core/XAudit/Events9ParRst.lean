import Formal.Core.XAudit.Events9Arb

/-!
# Formal.Core.XAudit.Events9ParRst — the corrected arbiter core with ONE reader reset

Probe E9Par (shard A). See `formal/notes/A-e9par.md`.

The parallel-pair rule (`Events9Par.par_fact`) needs the grant and its shadow to share their
reset signal (`RstSync`; at the netlist level the named hypothesis `Events9Par.HRst`). In
`Events9Arb.VRd` the reset `r` is existential, so `Events9Arb.CoreOf` does not say it. This file
restates the cell-level sufficiency theorem with the reset made explicit:

* `VRdR … ρ …`: `VRd` with the given reset `ρ` (`vrdR_vrd`: it implies `VRd`);
* `CoreFixR` / `CoreOfR`: the corrected core whose four readers (two grants, two shadows) all
  have the SAME reset `ρ` (`coreOfR_coreOf`: it implies `CoreOf`);
* **`and_cel_rst`** (= `Events9Arb.and_cel` with the reset `decide (u < T0)` explicit) and
  **`core_of_en_rst`** (= `Events9Arb.core_of_en`, same hypotheses, same proof): every behaviour of
  the real `bd_arbiter` core satisfying the enable conditions is a behaviour of the corrected core
  with the common reader reset `fun u => decide (u < T0)`.

So the common reset that HRst asks for is what the sufficiency construction produces. NOT proved:
the link from `CoreOfR` to `HRst` over a parsed `Net4` (the same gap as `CoreOf` → `HARB7`), and
the enable conditions themselves (`Events9Arb.core_of_settle` reduces them to RdOK).
-/

namespace Formal.Core.XAudit.Events9Arb

open Formal.Core.TraceDiscrete (Sig Warp Mono)
open Formal.Core.XAudit.Events2 (cel)
open Formal.Core.XAudit.Events8Arb
open Formal.Core.LutList (o5B o6B)
open Formal.Cells.ArbBinary (ARB_ST GRANT)

/-- `VRd` with an explicit reset signal `ρ`. -/
def VRdR (loR hiR loC hiC : Nat) (br : Bool) (ρ s ctl y : Sig) : Prop :=
  ∃ (F GR GC Q : Nat → Nat) (sv : Sig), Warp 1 1 F ∧ Warp loR hiR GR ∧ Warp loC hiC GC ∧
    Warp 1 1 Q ∧ ρ 0 = true ∧ (∀ x y, x ≤ y → ρ y = true → ρ x = true) ∧
    ∀ t, y t = if ρ (F t) then false else
      cel (fun p : Fin 2 => if p.val = 0 then s (GR (F t)) else (ctl (GC (F t)) && (sv (F t) == br)))
        (y (Q (F t)))

theorem vrdR_vrd {loR hiR loC hiC : Nat} {br : Bool} {ρ s ctl y : Sig}
    (h : VRdR loR hiR loC hiC br ρ s ctl y) : VRd loR hiR loC hiC br s ctl y := by
  obtain ⟨F, GR, GC, Q, sv, h1, h2, h3, h4, h5, h6, h7⟩ := h
  exact ⟨F, GR, GC, Q, ρ, sv, h1, h2, h3, h4, h5, h6, h7⟩

/-- The corrected core with one reset `ρ` for its four readers. -/
def CoreFixR (lo hi : Nat) (bg1 bg2 bs1 bs2 : RdB) (ρ r1 r2 a R0 g1 g2 : Sig) : Prop :=
  ∃ ctl s1 s2 : Sig, VCtl lo hi a ctl ∧
    VRdR bg1.loR bg1.hiR bg1.loC bg1.hiC true ρ r1 ctl g1 ∧
    VRdR bg2.loR bg2.hiR bg2.loC bg2.hiC false ρ r2 ctl g2 ∧
    VRdR bs1.loR bs1.hiR bs1.loC bs1.hiC true ρ r1 ctl s1 ∧
    VRdR bs2.loR bs2.hiR bs2.loC bs2.hiC false ρ r2 ctl s2 ∧
    VMerge 1 1 1 1 1 1 s1 s2 R0

def CoreOfR (B : ArbBands) (ρ r1 r2 a R0 g1 g2 : Sig) : Prop :=
  CoreFixR (loCtl B) (10 ^ 15) (rdG (B.g1 0) (B.g1 2) (kOf B)) (rdG (B.g2 1) (B.g2 2) (kOf B))
    (rdS (B.r0 0) (B.r0 2) (kOf B)) (rdS (B.r0 1) (B.r0 2) (kOf B)) ρ r1 r2 a R0 g1 g2

theorem coreOfR_coreOf {B : ArbBands} {ρ r1 r2 a R0 g1 g2 : Sig} (h : CoreOfR B ρ r1 r2 a R0 g1 g2) :
    CoreOf B r1 r2 a R0 g1 g2 := by
  obtain ⟨ctl, s1, s2, hc, h1, h2, h3, h4, hm⟩ := h
  exact ⟨ctl, s1, s2, hc, vrdR_vrd h1, vrdR_vrd h2, vrdR_vrd h3, vrdR_vrd h4, hm⟩

/-- **`and_cel_rst`**: `and_cel` with the reset `decide (u < T0)` explicit. -/
theorem and_cel_rst {Lr Hr Lq Hq K T0 : Nat} {br : Bool} {s e y ctl sv : Sig} {wr wq : Nat → Nat}
    (hwr : Warp Lr Hr wr) (hwq : Warp Lq Hq wq) (hLr : 1 ≤ Lr) (hLq : K + 2 ≤ Lq) (hT0 : Lq ≤ T0)
    (hy : ∀ t, y t = (s (wr t) && e (wq t))) (hlow : ∀ t, t ≤ T0 → y t = false)
    (hen : EnOK s e y wr wq K ctl sv br T0) :
    VRdR (Lr - 1) (Hr - 1) (Lq - K - 1) (Hq - K - 1) br (fun u => decide (u < T0)) s ctl y := by
  have hHq : Lq ≤ Hq := by
    have a := hwq.le_late (Hq + Lq); have b := hwq.early_le (Hq + Lq); omega
  refine ⟨fun t => t - 1, fun u => wr (u + 1), fun u => min (wq (u + 1) + K) (u - (Lq - K - 1)),
    fun t => t - 1, sv, shift1, ?_, ?_, shift1, ?_, ?_, ?_⟩
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

/-- **`core_of_en_rst`**: `core_of_en` with the common reader reset `decide (u < T0)` explicit. -/
theorem core_of_en_rst (B : ArbBands) {r1 r2 rs a q R0 g1 g2 ctl sv1 sv2 sv3 sv4 : Sig}
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
    CoreOfR B (fun u => decide (u < T0)) r1 r2 a R0 g1 g2 := by
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
  · exact and_cel_rst (hf1 0) (hf1 2) hb1 hq1 hT1 (fun t => by rw [hg1 t, g1_eq])
      (fun t ht => (hlow t (by omega)).1) e1
  · exact and_cel_rst (e := fun u => !q u) (hf2 1) (hf2 2) hb2 hq2 hT2 (fun t => by rw [hg2 t, g2_eq])
      (fun t ht => (hlow t (by omega)).2.1) e2
  · have h := and_cel_rst (T0 := T0) (sh2 (hfr 0) (by omega)) (sh2 (hfr 2) (by omega)) (by omega)
      (by simp only [kOf] at hq3 ⊢; omega) (by omega) (fun t => rfl)
      (fun t ht => by
        have := hR0e (t + 2); rw [(hlow (t + 2) (by omega)).2.2] at this
        show (r1 (fr 0 (t + 2)) && q (fr 2 (t + 2))) = false
        revert this
        generalize r1 (fr 0 (t + 2)) = x1; generalize q (fr 2 (t + 2)) = x2
        generalize r2 (fr 1 (t + 2)) = x3
        cases x1 <;> cases x2 <;> cases x3 <;> decide) e3
    simp only [rdS, CoreOfR, CoreFixR]
    have e1' : (B.r0 0).1 - 2 - 1 = (B.r0 0).1 - 3 := by omega
    have e2' : (B.r0 0).2 - 2 - 1 = (B.r0 0).2 - 3 := by omega
    have e3' : (B.r0 2).1 - 2 - kOf B - 1 = (B.r0 2).1 - kOf B - 3 := by omega
    have e4' : (B.r0 2).2 - 2 - kOf B - 1 = (B.r0 2).2 - kOf B - 3 := by omega
    rw [e1', e2', e3', e4'] at h; exact h
  · have h := and_cel_rst (T0 := T0) (e := fun u => !q u) (sh2 (hfr 1) (by omega)) (sh2 (hfr 2) (by omega))
      (by omega) (by simp only [kOf] at hq3 ⊢; omega) (by omega) (fun t => rfl)
      (fun t ht => by
        have := hR0e (t + 2); rw [(hlow (t + 2) (by omega)).2.2] at this
        show (r2 (fr 1 (t + 2)) && !q (fr 2 (t + 2))) = false
        revert this
        generalize r1 (fr 0 (t + 2)) = x1; generalize q (fr 2 (t + 2)) = x2
        generalize r2 (fr 1 (t + 2)) = x3
        cases x1 <;> cases x2 <;> cases x3 <;> decide) e4
    simp only [rdS, CoreOfR, CoreFixR]
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

end Formal.Core.XAudit.Events9Arb
