import Formal.Cells.ArbHeldTimed2
/-! Auditor AB2: the 7h/7j "prjxray arcs" `prj` read prjxray's SDF triples
`(0.045::0.056)(0.100::0.124)` as rise 56 / fall 124. They are FAST-corner and
SLOW-corner (min::max), both edges. Here: one-corner pure-delay instances
(rise = fall = d, d anywhere in that corner's band; zero routing) and the six
arc conditions of 7h/7j. The `16 ≤ smin` "tightest condition" disappears. -/
namespace AB2.ArbPrj
open Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2

/-- Zero routing, every arc a pure delay (rise = fall), O6 arcs `a6*`,
O5 arcs per pin `r1 r2 rq` (R0) and `h1 h2 hq` (g1). -/
def oneCorner (q g2 c1 c2 r1 r2 rq h1 h2 hq smin : Int)
    (h : 0 ≤ q ∧ 0 ≤ g2 ∧ 0 ≤ c1 ∧ 0 ≤ c2 ∧ 0 ≤ r1 ∧ 0 ≤ r2 ∧ 0 ≤ rq ∧ 0 ≤ h1 ∧ 0 ≤ h2 ∧
      0 ≤ hq ∧ 0 ≤ smin ∧ 0 < q ∧ 0 < c1 ∧ 0 < c2) : Dl where
  wr1s := 0
  wr2s := 0
  wr1g := 0
  wr2g := 0
  wfb := 0
  wa0s := 0
  wq := 0
  wg1 := 0
  wa01 := 0
  wfa1 := 0
  wg2 := 0
  wa02 := 0
  wfa2 := 0
  qr := q
  qf := q
  Rr1 := r1
  Rf1 := r1
  Rr2 := r2
  Rf2 := r2
  Rrq := rq
  Rfq := rq
  g1r1 := h1
  g1f1 := h1
  g1r2 := h2
  g1f2 := h2
  g1rq := hq
  g1fq := hq
  g2r := g2
  g2f := g2
  c1r := c1
  c1f := c1
  c2r := c2
  c2f := c2
  smin := smin
  H_NONNEG := by omega
  H_RISE_LE_FALL := by omega
  H_LOOP_POS := by omega

/-- SLOW corner (O6 [100,124], O5 I0/I1 [122,152], O5 I2 [121,150]): every one
of the six conditions holds for EVERY server (smin ≥ 0), for every arc value in
the band. -/
theorem slow_all (q g2 c1 c2 r1 r2 rq h1 h2 hq smin : Int)
    (b6 : 100 ≤ q ∧ q ≤ 124 ∧ 100 ≤ g2 ∧ g2 ≤ 124 ∧ 100 ≤ c1 ∧ c1 ≤ 124 ∧ 100 ≤ c2 ∧ c2 ≤ 124)
    (b5 : 122 ≤ r1 ∧ r1 ≤ 152 ∧ 122 ≤ r2 ∧ r2 ≤ 152 ∧ 121 ≤ rq ∧ rq ≤ 150 ∧
          122 ≤ h1 ∧ h1 ≤ 152 ∧ 122 ≤ h2 ∧ h2 ≤ 152 ∧ 121 ≤ hq ∧ hq ≤ 150) (hs : 0 ≤ smin) :
    let D := oneCorner q g2 c1 c2 r1 r2 rq h1 h2 hq smin (by omega)
    RT1 D ∧ RT2 D ∧ A0Fork D ∧ RT1b D ∧ RT2b D ∧ A0Fork2 D := by
  intro D
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp only [D, oneCorner, RT1, A0Fork, RT1b, A0Fork2] <;> omega

/-- FAST corner (O6 [45,56], O5 I0/I1 [44,55], O5 I2 [42,52]): same. -/
theorem fast_all (q g2 c1 c2 r1 r2 rq h1 h2 hq smin : Int)
    (b6 : 45 ≤ q ∧ q ≤ 56 ∧ 45 ≤ g2 ∧ g2 ≤ 56 ∧ 45 ≤ c1 ∧ c1 ≤ 56 ∧ 45 ≤ c2 ∧ c2 ≤ 56)
    (b5 : 44 ≤ r1 ∧ r1 ≤ 55 ∧ 44 ≤ r2 ∧ r2 ≤ 55 ∧ 42 ≤ rq ∧ rq ≤ 52 ∧
          44 ≤ h1 ∧ h1 ≤ 55 ∧ 44 ≤ h2 ∧ h2 ≤ 55 ∧ 42 ≤ hq ∧ hq ≤ 52) (hs : 0 ≤ smin) :
    let D := oneCorner q g2 c1 c2 r1 r2 rq h1 h2 hq smin (by omega)
    RT1 D ∧ RT2 D ∧ A0Fork D ∧ RT1b D ∧ RT2b D ∧ A0Fork2 D := by
  intro D
  refine ⟨?_, ⟨?_, ?_, ?_, ?_⟩, ?_, ?_, ⟨?_, ?_, ?_, ?_⟩, ?_⟩ <;>
    simp only [D, oneCorner, RT1, A0Fork, RT1b, A0Fork2] <;> omega

/-- The 7j "16" is (fall arc from the SLOW corner) − (rise arcs from the FAST
corner): 124 − 56 − 52. It exists only in the mixed-corner reading. -/
theorem sixteen_is_mixed_corner : (124 : Int) - 56 - 52 = 16 := by decide

/-- 7j's D0 is not a one-corner instance: its rise and fall arcs differ. -/
theorem D0_mixed : D0.qr ≠ D0.qf ∧ D0.qr = 56 ∧ D0.qf = 124 := by decide

end AB2.ArbPrj
