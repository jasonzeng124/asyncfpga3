import Formal.Cells.SpecFbChain

/-!
# Formal.Cells.GrantExcl — arbiter grants are exclusive once the state has settled (THE Spec semantics, H_ARB(T))

Shard B, THE goal, H_ARB(T).

## Problem, plainly
An arbiter's two grant LUTs read the same state node q through their own routes (`g1 = r1 · q`, `g2 = r2 · ¬q`).
While q moves, one read may still see the old value and the other the new one, so both grants can be high for a
moment (the handover hazard). When can both NOT be high, for every behaviour?

## Results
* `grants_excl`: if g1's INIT can be 1 only when its q pin reads 1, g2's only when its q pin reads 0 (with each gate's
  tied pins at their constant values), and q's source
  is constant on `[a, b]`, then at every time t whose reads of q (both gates) fall in `[a, b]`
  (`a + hi ≤ t ≤ b + lo` for each gate's q pin) at most one grant is high.
* `grants_excl_arb`: with H_ARB(T) (`Spec.ArbOK`): if the state LUT's other inputs are constant on `[t1, t2]`, the
  grants are exclusive on `[t1 + T + hi, t2 + lo]` (both gates' q-pin bands).

## Not covered
Exclusion during the settling window (H_ARB allows q to move for T; `ArbTSpec.spec_double_ack` shows the downstream
consequence), the grant gates' identity on THE target (an instance table), and what the ack C-elements do.
-/

namespace Formal.Cells.GrantExcl

open Formal.Target Formal.Timing.SpecChain Formal.Cells.SpecFbChain

theorem grants_excl {p : DelayPar} {c : ℚ} {g1 g2 : Gate} {src1 src2 : Nat → Nat} {arcs1 arcs2 : Nat → List Arc}
    {S1 S2 : Nat} {x : Beh} (h1 : CGateOK p c g1 src1 arcs1 S1 x) (h2 : CGateOK p c g2 src2 arcs2 S2 x)
    {lo1 hi1 lo2 hi2 : Nat → Nat} (hb1 : CBands p c g1.k arcs1 lo1 hi1) (hb2 : CBands p c g2.k arcs2 lo2 hi2)
    {j1 j2 qn : Nat} (hj1 : j1 < g1.k) (hj2 : j2 < g2.k) (hs1 : src1 j1 = qn) (hs2 : src2 j2 = qn)
    (held1 ov1 held2 ov2 : Nat → Bool)
    (hf1 : ∀ v : Nat → Bool, (∀ i, i < g1.k → held1 i = true → v i = ov1 i) →
      g1.init.testBit (addr g1.k v) = true → v j1 = true)
    (hf2 : ∀ v : Nat → Bool, (∀ i, i < g2.k → held2 i = true → v i = ov2 i) →
      g2.init.testBit (addr g2.k v) = true → v j2 = false)
    (hh1 : ∀ i, i < g1.k → held1 i = true → ∀ t, x (src1 i) t = ov1 i)
    (hh2 : ∀ i, i < g2.k → held2 i = true → ∀ t, x (src2 i) t = ov2 i)
    {a b : Nat} (hq : ∀ t, a ≤ t → t ≤ b → x qn t = x qn a) :
    ∀ t, S1 ≤ t → S2 ≤ t → a + hi1 j1 ≤ t → t ≤ b + lo1 j1 → a + hi2 j2 ≤ t → t ≤ b + lo2 j2 →
      ¬ (x g1.out t = true ∧ x g2.out t = true) := by
  obtain ⟨F1, -, hF1⟩ := h1
  obtain ⟨F2, -, hF2⟩ := h2
  intro t hS1 hS2 ha1 hb1' ha2 hb2' ⟨o1, o2⟩
  obtain ⟨r1, y1⟩ := hF1 t hS1
  obtain ⟨r2, y2⟩ := hF2 t hS2
  have d1 := hb1 j1 hj1 _ (r1 j1 hj1).2
  have d2 := hb2 j2 hj2 _ (r2 j2 hj2).2
  have e1 := (r1 j1 hj1).1
  have e2 := (r2 j2 hj2).1
  have v1 := hf1 _ (fun i hi hh => hh1 i hi hh _) (by rw [← y1]; exact o1)
  have v2 := hf2 _ (fun i hi hh => hh2 i hi hh _) (by rw [← y2]; exact o2)
  rw [hs1, hq _ (by omega) (by omega)] at v1
  rw [hs2, hq _ (by omega) (by omega)] at v2
  rw [v1] at v2; exact Bool.noConfusion v2

theorem grants_excl_arb {p : DelayPar} {c : ℚ} {g1 g2 : Gate} {src1 src2 : Nat → Nat}
    {arcs1 arcs2 : Nat → List Arc} {S1 S2 : Nat} {x : Beh} (h1 : CGateOK p c g1 src1 arcs1 S1 x)
    (h2 : CGateOK p c g2 src2 arcs2 S2 x)
    {lo1 hi1 lo2 hi2 : Nat → Nat} (hb1 : CBands p c g1.k arcs1 lo1 hi1) (hb2 : CBands p c g2.k arcs2 lo2 hi2)
    {j1 j2 : Nat} (A : ArbNodes) (hj1 : j1 < g1.k) (hj2 : j2 < g2.k) (hs1 : src1 j1 = A.q) (hs2 : src2 j2 = A.q)
    (held1 ov1 held2 ov2 : Nat → Bool)
    (hf1 : ∀ v : Nat → Bool, (∀ i, i < g1.k → held1 i = true → v i = ov1 i) →
      g1.init.testBit (addr g1.k v) = true → v j1 = true)
    (hf2 : ∀ v : Nat → Bool, (∀ i, i < g2.k → held2 i = true → v i = ov2 i) →
      g2.init.testBit (addr g2.k v) = true → v j2 = false)
    (hh1 : ∀ i, i < g1.k → held1 i = true → ∀ t, x (src1 i) t = ov1 i)
    (hh2 : ∀ i, i < g2.k → held2 i = true → ∀ t, x (src2 i) t = ov2 i)
    (T : Nat) (harb : ArbOK T [A] x) {t1 t2 : Nat} (hin : ∀ n ∈ A.ins, ConstOn (x n) t1 t2) :
    ∀ t, S1 ≤ t → S2 ≤ t → t1 + T + hi1 j1 ≤ t → t ≤ t2 + lo1 j1 → t1 + T + hi2 j2 ≤ t → t ≤ t2 + lo2 j2 →
      ¬ (x g1.out t = true ∧ x g2.out t = true) := by
  have hc := harb A (List.mem_singleton.mpr rfl) t1 t2 hin
  exact grants_excl h1 h2 hb1 hb2 hj1 hj2 hs1 hs2 held1 ov1 held2 ov2 hf1 hf2 hh1 hh2 (a := t1 + T) (b := t2)
    (fun t h h' => hc t h h')

end Formal.Cells.GrantExcl
