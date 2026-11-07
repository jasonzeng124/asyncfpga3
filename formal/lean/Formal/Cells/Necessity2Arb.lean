import Formal.Cells.ArbHeldTimed2

/-!
# Necessity2Arb: the RT2 ack-exclusion fields of `bd_arbiter` are tight to 1 ps

Probe Bsx2 (shard B). Rows `bd_arbiter.rt2_g1`, `rt2_forkA`, `rt2_forkG`
(7h direction, `ArbHeldTimed.rt2_exclusion_arcs`) and `rt2b_g2`,
`rt2b_forkA2`, `rt2b_forkG2` (mirror, `ArbHeldTimed2.rt2_exclusion2_arcs`)
were "sufficient (arc form valid for every server)". The theorems'
hypothesis set: `Run D s` (real INITs of ustate / ugrant / ua1 / ua2, the
rise-fast OR channel per LUT output, one routed delay per pin, the server
relation H_SERVER_MIN), the scenario (`Scn` / `Scn2`), the four RT2 fields,
and the A0 fork (`A0Fork` / `A0Fork2`).

## Result

`Claim sp sg sa sG` is `rt2_exclusion_arcs` with the fields pulse / g1 /
forkA / forkG each weakened by the given slack (Int ticks = ps); every
other hypothesis verbatim. `claim0 : Claim 0 0 0 0` is the existing
theorem. Then, for each of g1, forkA, forkG, ONE tick of slack on that field
ALONE is unsound:

* `g1_false : ¬ Claim 0 1 0 0`, `forkA_false : ¬ Claim 0 0 1 0`,
  `forkG_false : ¬ Claim 0 0 0 1`;
* mirror: `g2_false`, `forkA2_false`, `forkG2_false` on `Claim2`.

Each refutation is an explicit run (`S*`) of the gate relations that holds
for ALL t ∈ ℤ (server relation included; the server answers in exactly
`smin` both times, the worst case the arc form is stated for), satisfies the
scenario for horizon 100, satisfies every other RT2 field and the A0 fork,
violates the named field by exactly 1 ps (`*_viol`), and has BOTH acks high
at t = 20.

* g1 / g2 (`SG1`, `SG2`): g1's fall reaches ua1 one tick too late for its
  loop to close before A0 re-rises. ua1 makes a 1-tick low runt at 19 and
  re-latches high at 20; A2 rises at 20. These runs use c1f = 2 > c1r = 1
  (allowed by H_RISE_LE_FALL); every other arc is 1.
* `g1_false_1C` (`SG1c`): the same with EVERY arc a single delay 1
  (rise = fall, one corner). Then ua1's hole recirculates through its pure
  delay loop forever: A1 = [t < 19] ∨ [t ≥ 22 ∧ t ≡ 2 (mod 4)], an eternal
  runt train (so 7j's hand remark that the hole always shrinks by c1f − c1r
  per round gives no decay at one corner), and A1·A2 holds at 22, 26, ...
* forkA / forkG (`SFA`, `SFG`, mirror `SFA2`, `SFG2`): A1 (A2) falls
  cleanly at 21, A2 (A1) rises at 20: a 1-tick ack overlap. Every arc is 1
  (one corner); the slow leg is a route (A0 -> ua1 for forkA, r1 -> ugrant
  and g1 -> ua1 for forkG).

* pulse / pulse2 (`SP`, `SP2`, end of file): `pulse_false`, `pulse2_false`,
  every arc rise = fall, unmatched A0 forks: an eternal runt train.

So in this model each of these eight fields is **necessary at the boundary**:
no single-field weakening by even 1 ps keeps the theorem. Not shown: that
every violating parameter point fails; the fields are about the worst-case
server (TA, TA2 minimal), so a slower server than `smin` can still pass.
RT1 (grant exclusion) holds on SFA/SFG/SFA2/SFG2 (not a hypothesis of the
theorem, not checked here). The rows' extra +1 (JSON, strict form) is the
Kleene X window of CElemStrict, not this model.
-/

namespace Formal.Cells.Necessity2Arb
open Formal.Cells Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2

/-! ## The weakened claims -/

/-- 7h's `RT2` with per-field slack. -/
structure RT2s (D : Dl) (sp sg sa sG : Int) : Prop where
  pulse : D.c1f + D.wfa1 ≤ D.wa0s + D.qf + D.wfb + D.Rrq + D.smin + sp
  g1 : D.wr1g + D.g1f1 + D.wg1 + D.c1f + D.wfa1 ≤
    D.wr1s + D.Rf1 + 2 * D.smin + D.wa0s + D.qf + D.wfb + D.Rrq + D.wa01 + sg
  forkA : D.wa01 + D.c1f ≤ D.wa0s + D.qf + D.wfb + D.Rrq + D.smin + D.wa02 + D.c2r + sa
  forkG : D.wr1g + D.g1f1 + D.wg1 + D.c1f ≤
    D.wr1s + D.Rf1 + 2 * D.smin + D.wa0s + D.qf + D.wfb + D.Rrq + D.wa02 + D.c2r + sG

/-- `rt2_exclusion_arcs` with the RT2 fields weakened. -/
def Claim (sp sg sa sG : Int) : Prop :=
  ∀ (D : Dl) (s : Sigs) (t0 ta TA TA2 Hz : Int), Run D s → Scn D s t0 ta TA TA2 Hz →
    RT2s D sp sg sa sG → A0Fork D → ∀ t, t < Hz → (s.A1 t && s.A2 t) = false

theorem claim0 : Claim 0 0 0 0 := by
  intro D s t0 ta TA TA2 Hz R S h hf
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact rt2_exclusion_arcs R S ⟨by omega, by omega, by omega, by omega⟩ hf

/-- 7j's `RT2b` with per-field slack. -/
structure RT2bs (D : Dl) (sp sg sa sG : Int) : Prop where
  pulse : D.c2f + D.wfa2 ≤ D.wa0s + D.qr + D.wfb + D.Rrq + D.smin + sp
  g2 : D.wr2g + D.g2f + D.wg2 + D.c2f + D.wfa2 ≤
    D.wr2s + D.Rf2 + 2 * D.smin + D.wa0s + D.qr + D.wfb + D.Rrq + D.wa02 + sg
  forkA : D.wa02 + D.c2f ≤ D.wa0s + D.qr + D.wfb + D.Rrq + D.smin + D.wa01 + D.c1r + sa
  forkG : D.wr2g + D.g2f + D.wg2 + D.c2f ≤
    D.wr2s + D.Rf2 + 2 * D.smin + D.wa0s + D.qr + D.wfb + D.Rrq + D.wa01 + D.c1r + sG

/-- `rt2_exclusion2_arcs` with the RT2b fields weakened. -/
def Claim2 (sp sg sa sG : Int) : Prop :=
  ∀ (D : Dl) (s : Sigs) (t0 ta TA TA2 Hz : Int), Run D s → Scn2 D s t0 ta TA TA2 Hz →
    RT2bs D sp sg sa sG → A0Fork2 D → ∀ t, t < Hz → (s.A1 t && s.A2 t) = false

theorem claim2_0 : Claim2 0 0 0 0 := by
  intro D s t0 ta TA TA2 Hz R S h hf
  obtain ⟨h1, h2, h3, h4⟩ := h
  exact rt2_exclusion2_arcs R S ⟨by omega, by omega, by omega, by omega⟩ hf

/-! ## Delay sets: every arc 1 except `c1f`, `c2f`; free routes -/

/-- Routes wr1s = wr2s = wfb = wa0s = 0; the others free; every arc 1 except
the ua1 / ua2 fall arcs `c1f`, `c2f`. -/
def dN (wr1g wr2g wq wg1 wa01 wfa1 wg2 wa02 wfa2 c1f c2f smin : Int)
    (h : 0 ≤ wr1g ∧ 0 ≤ wr2g ∧ 0 ≤ wq ∧ 0 ≤ wg1 ∧ 0 ≤ wa01 ∧ 0 ≤ wfa1 ∧ 0 ≤ wg2 ∧
      0 ≤ wa02 ∧ 0 ≤ wfa2 ∧ 1 ≤ c1f ∧ 1 ≤ c2f ∧ 0 ≤ smin) : Dl where
  wr1s := 0
  wr2s := 0
  wr1g := wr1g
  wr2g := wr2g
  wfb := 0
  wa0s := 0
  wq := wq
  wg1 := wg1
  wa01 := wa01
  wfa1 := wfa1
  wg2 := wg2
  wa02 := wa02
  wfa2 := wfa2
  qr := 1
  qf := 1
  Rr1 := 1
  Rf1 := 1
  Rr2 := 1
  Rf2 := 1
  Rrq := 1
  Rfq := 1
  g1r1 := 1
  g1f1 := 1
  g1r2 := 1
  g1f2 := 1
  g1rq := 1
  g1fq := 1
  g2r := 1
  g2f := 1
  c1r := 1
  c1f := c1f
  c2r := 1
  c2f := c2f
  smin := smin
  H_NONNEG := by omega
  H_RISE_LE_FALL := by omega
  H_LOOP_POS := by omega

/-! ## Common pieces of the 7h-direction runs (t0 = 0, ta = -1000, TA = 9, TA2 = 19)

TR = 1, TA = TR + smin = 9, QB = 10, RR = 11, TA2 = RR + smin = 19. -/

def A0w : Int → Bool := fun t => (decide (-1000 ≤ t) && decide (t < 9)) || decide (19 ≤ t)

/-! ### g1: ua1 runt, then re-latch (c1f = 2) -/

/-- g1 field violated: wr1g = 16 (g1 falls at 17 through r1), wq = 6 (its
q path would be 17 as well), c1f = 2, wfa1 = 1, smin = 8. -/
def DG1 : Dl := dN 16 0 6 0 0 1 0 0 0 2 1 8 (by omega)

def SG1 : Sigs where
  r1 := fun t => decide (t < 0)
  r2 := fun _ => true
  q := fun t => decide (t < 10)
  R0 := fun t => decide (t < 1) || decide (11 ≤ t)
  g1 := fun t => decide (t < 17)
  g2 := fun t => decide (17 ≤ t)
  A0 := A0w
  A1 := fun t => decide (t < 19) || decide (20 ≤ t)
  A2 := fun t => decide (20 ≤ t)

/-- The shared server proof shape of the 7h-direction runs. -/
theorem srv_7h (s : Sigs) (hA : s.A0 = A0w)
    (hR1 : s.R0 (-1008) = true) (hR2 : s.R0 1 = false) (hR3 : s.R0 11 = true) :
    Server 8 s.R0 s.A0 := by
  rw [hA]
  intro t ht
  have e : t = -1000 ∨ t = 9 ∨ t = 19 := by
    exact Classical.byContradiction fun hc => ht (by rw [Bool.eq_iff_iff]; simp [A0w]; omega)
  rcases e with rfl | rfl | rfl
  · exact ⟨-1008, by omega, by rw [hR1]; simp [A0w], fun v _ _ => by
      rw [Bool.eq_iff_iff]; simp [A0w]; omega⟩
  · exact ⟨1, by omega, by rw [hR2]; simp [A0w], fun v _ _ => by
      rw [Bool.eq_iff_iff]; simp [A0w]; omega⟩
  · exact ⟨11, by omega, by rw [hR3]; simp [A0w], fun v _ _ => by
      rw [Bool.eq_iff_iff]; simp [A0w]; omega⟩

theorem SG1_run : Run DG1 SG1 where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [SG1, DG1, dN, A0w, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [SG1, DG1, dN, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [SG1, DG1, dN, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [SG1, DG1, dN, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [SG1, DG1, dN, A0w, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [SG1, DG1, dN, A0w, CE_eq]; omega
  H_SRV := srv_7h SG1 rfl (by decide) (by decide) (by decide)

theorem SG1_scn : Scn DG1 SG1 0 (-1000) 9 19 100 where
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [SG1, A0w]; omega
  H_A0_prev := by decide
  H_q_init := by intro t ht; simp [SG1]; omega
  H_A1_init := by intro t ht; simp [SG1]; omega
  H_A2_init := by intro t ht; simp [SG1]; omega
  H_SETTLED := by simp [DG1, dN]

/-- The g1 field fails by exactly 1 ps (20 = 19 + 1); the others hold. -/
theorem G1_viol :
    DG1.wr1g + DG1.g1f1 + DG1.wg1 + DG1.c1f + DG1.wfa1 =
      DG1.wr1s + DG1.Rf1 + 2 * DG1.smin + DG1.wa0s + DG1.qf + DG1.wfb + DG1.Rrq + DG1.wa01 + 1 ∧
    RT2s DG1 0 1 0 0 ∧ A0Fork DG1 := by
  refine ⟨by decide, ⟨by decide, by decide, by decide, by decide⟩, by unfold A0Fork; decide⟩

theorem G1_both : (SG1.A1 20 && SG1.A2 20) = true := by decide

theorem g1_false : ¬ Claim 0 1 0 0 := by
  intro h
  have := h DG1 SG1 0 (-1000) 9 19 100 SG1_run SG1_scn G1_viol.2.1 G1_viol.2.2 20 (by omega)
  rw [G1_both] at this; exact absurd this (by decide)

/-! ### g1 at one corner (every arc 1): an eternal runt train -/

/-- wr1g = 15, wg1 = 2, wa01 = 2, wq = 5, wfa1 = 3, c1f = 1. -/
def DG1c : Dl := dN 15 0 5 2 2 3 0 0 0 1 1 8 (by omega)

def SG1c : Sigs where
  r1 := fun t => decide (t < 0)
  r2 := fun _ => true
  q := fun t => decide (t < 10)
  R0 := fun t => decide (t < 1) || decide (11 ≤ t)
  g1 := fun t => decide (t < 16)
  g2 := fun t => decide (16 ≤ t)
  A0 := A0w
  A1 := fun t => decide (t < 19) || (decide (22 ≤ t) && decide (t % 4 = 2))
  A2 := fun t => decide (20 ≤ t)

theorem SG1c_run : Run DG1c SG1c where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [SG1c, DG1c, dN, A0w, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [SG1c, DG1c, dN, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [SG1c, DG1c, dN, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [SG1c, DG1c, dN, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [SG1c, DG1c, dN, A0w, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [SG1c, DG1c, dN, A0w, CE_eq]; omega
  H_SRV := srv_7h SG1c rfl (by decide) (by decide) (by decide)

theorem SG1c_scn : Scn DG1c SG1c 0 (-1000) 9 19 100 where
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [SG1c, A0w]; omega
  H_A0_prev := by decide
  H_q_init := by intro t ht; simp [SG1c]; omega
  H_A1_init := by intro t ht; simp [SG1c]; omega
  H_A2_init := by intro t ht; simp [SG1c]; omega
  H_SETTLED := by simp [DG1c, dN]

theorem G1c_viol :
    DG1c.wr1g + DG1c.g1f1 + DG1c.wg1 + DG1c.c1f + DG1c.wfa1 =
      DG1c.wr1s + DG1c.Rf1 + 2 * DG1c.smin + DG1c.wa0s + DG1c.qf + DG1c.wfb + DG1c.Rrq +
        DG1c.wa01 + 1 ∧
    RT2s DG1c 0 1 0 0 ∧ A0Fork DG1c ∧
    DG1c.c1r = DG1c.c1f ∧ DG1c.qr = DG1c.qf ∧ DG1c.Rr1 = DG1c.Rf1 ∧ DG1c.g1r1 = DG1c.g1f1 ∧
    DG1c.g2r = DG1c.g2f ∧ DG1c.c2r = DG1c.c2f ∧ DG1c.Rrq = DG1c.Rfq ∧ DG1c.g1rq = DG1c.g1fq := by
  refine ⟨by decide, ⟨by decide, by decide, by decide, by decide⟩, by unfold A0Fork; decide, by decide,
    by decide, by decide, by decide, by decide, by decide, by decide, by decide⟩

/-- The ack overlap recurs forever (every 4 ps from 22). -/
theorem G1c_both (k : Nat) : (SG1c.A1 (22 + 4 * k) && SG1c.A2 (22 + 4 * k)) = true := by
  simp [SG1c]; omega

theorem g1_false_1C : ¬ Claim 0 1 0 0 := by
  intro h
  have := h DG1c SG1c 0 (-1000) 9 19 100 SG1c_run SG1c_scn G1c_viol.2.1 G1c_viol.2.2.1 22
    (by omega)
  have e : (SG1c.A1 22 && SG1c.A2 22) = true := by decide
  rw [e] at this; exact absurd this (by decide)

/-! ### forkA: A0's route to ua1 slow (wa01 = 11), every arc 1 -/

def DFA : Dl := dN 0 0 6 0 11 1 0 0 0 1 1 8 (by omega)

def SFA : Sigs where
  r1 := fun t => decide (t < 0)
  r2 := fun _ => true
  q := fun t => decide (t < 10)
  R0 := fun t => decide (t < 1) || decide (11 ≤ t)
  g1 := fun t => decide (t < 1)
  g2 := fun t => decide (17 ≤ t)
  A0 := A0w
  A1 := fun t => decide (t < 21)
  A2 := fun t => decide (20 ≤ t)

theorem SFA_run : Run DFA SFA where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [SFA, DFA, dN, A0w, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [SFA, DFA, dN, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [SFA, DFA, dN, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [SFA, DFA, dN, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [SFA, DFA, dN, A0w, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [SFA, DFA, dN, A0w, CE_eq]; omega
  H_SRV := srv_7h SFA rfl (by decide) (by decide) (by decide)

theorem SFA_scn : Scn DFA SFA 0 (-1000) 9 19 100 where
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [SFA, A0w]; omega
  H_A0_prev := by decide
  H_q_init := by intro t ht; simp [SFA]; omega
  H_A1_init := by intro t ht; simp [SFA]; omega
  H_A2_init := by intro t ht; simp [SFA]; omega
  H_SETTLED := by simp [DFA, dN]

theorem FA_viol :
    DFA.wa01 + DFA.c1f =
      DFA.wa0s + DFA.qf + DFA.wfb + DFA.Rrq + DFA.smin + DFA.wa02 + DFA.c2r + 1 ∧
    RT2s DFA 0 0 1 0 ∧ A0Fork DFA ∧ RT1 DFA := by
  refine ⟨by decide, ⟨by decide, by decide, by decide, by decide⟩, by unfold A0Fork; decide, ?_⟩
  unfold RT1; left; decide

theorem FA_both : (SFA.A1 20 && SFA.A2 20) = true := by decide

theorem forkA_false : ¬ Claim 0 0 1 0 := by
  intro h
  have := h DFA SFA 0 (-1000) 9 19 100 SFA_run SFA_scn FA_viol.2.1 FA_viol.2.2.1 20 (by omega)
  rw [FA_both] at this; exact absurd this (by decide)

/-! ### forkG: g1's leg slow (wr1g = 12, wg1 = 7), wa01 = 3, every arc 1 -/

def DFG : Dl := dN 12 0 6 7 3 1 0 0 0 1 1 8 (by omega)

def SFG : Sigs where
  r1 := fun t => decide (t < 0)
  r2 := fun _ => true
  q := fun t => decide (t < 10)
  R0 := fun t => decide (t < 1) || decide (11 ≤ t)
  g1 := fun t => decide (t < 13)
  g2 := fun t => decide (17 ≤ t)
  A0 := A0w
  A1 := fun t => decide (t < 21)
  A2 := fun t => decide (20 ≤ t)

theorem SFG_run : Run DFG SFG where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [SFG, DFG, dN, A0w, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [SFG, DFG, dN, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [SFG, DFG, dN, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [SFG, DFG, dN, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [SFG, DFG, dN, A0w, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [SFG, DFG, dN, A0w, CE_eq]; omega
  H_SRV := srv_7h SFG rfl (by decide) (by decide) (by decide)

theorem SFG_scn : Scn DFG SFG 0 (-1000) 9 19 100 where
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [SFG, A0w]; omega
  H_A0_prev := by decide
  H_q_init := by intro t ht; simp [SFG]; omega
  H_A1_init := by intro t ht; simp [SFG]; omega
  H_A2_init := by intro t ht; simp [SFG]; omega
  H_SETTLED := by simp [DFG, dN]

theorem FG_viol :
    DFG.wr1g + DFG.g1f1 + DFG.wg1 + DFG.c1f =
      DFG.wr1s + DFG.Rf1 + 2 * DFG.smin + DFG.wa0s + DFG.qf + DFG.wfb + DFG.Rrq + DFG.wa02 +
        DFG.c2r + 1 ∧
    RT2s DFG 0 0 0 1 ∧ A0Fork DFG ∧ RT1 DFG := by
  refine ⟨by decide, ⟨by decide, by decide, by decide, by decide⟩, by unfold A0Fork; decide, ?_⟩
  unfold RT1; left; decide

theorem FG_both : (SFG.A1 20 && SFG.A2 20) = true := by decide

theorem forkG_false : ¬ Claim 0 0 0 1 := by
  intro h
  have := h DFG SFG 0 (-1000) 9 19 100 SFG_run SFG_scn FG_viol.2.1 FG_viol.2.2.1 20 (by omega)
  rw [FG_both] at this; exact absurd this (by decide)

/-! ## Mirror direction (client 2 releases): TRb = 1, TA = 9, QBb = 10, RRb = 11, TA2 = 19 -/

theorem srv_7j (s : Sigs) (hA : s.A0 = A0w)
    (hR1 : s.R0 (-1008) = true) (hR2 : s.R0 1 = false) (hR3 : s.R0 11 = true) :
    Server 8 s.R0 s.A0 := srv_7h s hA hR1 hR2 hR3

/-- g2 field violated: wr2g = 9, wg2 = 7, c2f = 2, wfa2 = 1. -/
def DG2 : Dl := dN 0 9 6 0 0 0 7 0 1 1 2 8 (by omega)

def SG2 : Sigs where
  r1 := fun _ => true
  r2 := fun t => decide (t < 0)
  q := fun t => decide (10 ≤ t)
  R0 := fun t => decide (t < 1) || decide (11 ≤ t)
  g1 := fun t => decide (17 ≤ t)
  g2 := fun t => decide (t < 10)
  A0 := A0w
  A1 := fun t => decide (20 ≤ t)
  A2 := fun t => decide (t < 19) || decide (20 ≤ t)

theorem SG2_run : Run DG2 SG2 where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [SG2, DG2, dN, A0w, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [SG2, DG2, dN, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [SG2, DG2, dN, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [SG2, DG2, dN, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [SG2, DG2, dN, A0w, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [SG2, DG2, dN, A0w, CE_eq]; omega
  H_SRV := srv_7j SG2 rfl (by decide) (by decide) (by decide)

theorem SG2_scn : Scn2 DG2 SG2 0 (-1000) 9 19 100 where
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [SG2, A0w]; omega
  H_A0_prev := by decide
  H_q_init := by intro t ht; simp [SG2]; omega
  H_A1_init := by intro t ht; simp [SG2]; omega
  H_A2_init := by intro t ht; simp [SG2]; omega
  H_SETTLED := by simp [DG2, dN]

theorem G2_viol :
    DG2.wr2g + DG2.g2f + DG2.wg2 + DG2.c2f + DG2.wfa2 =
      DG2.wr2s + DG2.Rf2 + 2 * DG2.smin + DG2.wa0s + DG2.qr + DG2.wfb + DG2.Rrq + DG2.wa02 + 1 ∧
    RT2bs DG2 0 1 0 0 ∧ A0Fork2 DG2 := by
  refine ⟨by decide, ⟨by decide, by decide, by decide, by decide⟩, by unfold A0Fork2; decide⟩

theorem G2_both : (SG2.A1 20 && SG2.A2 20) = true := by decide

theorem g2_false : ¬ Claim2 0 1 0 0 := by
  intro h
  have := h DG2 SG2 0 (-1000) 9 19 100 SG2_run SG2_scn G2_viol.2.1 G2_viol.2.2 20 (by omega)
  rw [G2_both] at this; exact absurd this (by decide)

/-- forkA2: A0's route to ua2 slow (wa02 = 11), every arc 1. -/
def DFA2 : Dl := dN 0 0 6 0 0 0 0 11 1 1 1 8 (by omega)

def SFA2 : Sigs where
  r1 := fun _ => true
  r2 := fun t => decide (t < 0)
  q := fun t => decide (10 ≤ t)
  R0 := fun t => decide (t < 1) || decide (11 ≤ t)
  g1 := fun t => decide (17 ≤ t)
  g2 := fun t => decide (t < 1)
  A0 := A0w
  A1 := fun t => decide (20 ≤ t)
  A2 := fun t => decide (t < 21)

theorem SFA2_run : Run DFA2 SFA2 where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [SFA2, DFA2, dN, A0w, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [SFA2, DFA2, dN, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [SFA2, DFA2, dN, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [SFA2, DFA2, dN, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [SFA2, DFA2, dN, A0w, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [SFA2, DFA2, dN, A0w, CE_eq]; omega
  H_SRV := srv_7j SFA2 rfl (by decide) (by decide) (by decide)

theorem SFA2_scn : Scn2 DFA2 SFA2 0 (-1000) 9 19 100 where
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [SFA2, A0w]; omega
  H_A0_prev := by decide
  H_q_init := by intro t ht; simp [SFA2]; omega
  H_A1_init := by intro t ht; simp [SFA2]; omega
  H_A2_init := by intro t ht; simp [SFA2]; omega
  H_SETTLED := by simp [DFA2, dN]

theorem FA2_viol :
    DFA2.wa02 + DFA2.c2f =
      DFA2.wa0s + DFA2.qr + DFA2.wfb + DFA2.Rrq + DFA2.smin + DFA2.wa01 + DFA2.c1r + 1 ∧
    RT2bs DFA2 0 0 1 0 ∧ A0Fork2 DFA2 := by
  refine ⟨by decide, ⟨by decide, by decide, by decide, by decide⟩, by unfold A0Fork2; decide⟩

theorem FA2_both : (SFA2.A1 20 && SFA2.A2 20) = true := by decide

theorem forkA2_false : ¬ Claim2 0 0 1 0 := by
  intro h
  have := h DFA2 SFA2 0 (-1000) 9 19 100 SFA2_run SFA2_scn FA2_viol.2.1 FA2_viol.2.2 20
    (by omega)
  rw [FA2_both] at this; exact absurd this (by decide)

/-- forkG2: g2's leg slow (wr2g = 12, wg2 = 7), wa02 = 3, every arc 1. -/
def DFG2 : Dl := dN 0 12 6 0 0 0 7 3 1 1 1 8 (by omega)

def SFG2 : Sigs where
  r1 := fun _ => true
  r2 := fun t => decide (t < 0)
  q := fun t => decide (10 ≤ t)
  R0 := fun t => decide (t < 1) || decide (11 ≤ t)
  g1 := fun t => decide (17 ≤ t)
  g2 := fun t => decide (t < 13)
  A0 := A0w
  A1 := fun t => decide (20 ≤ t)
  A2 := fun t => decide (t < 21)

theorem SFG2_run : Run DFG2 SFG2 where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [SFG2, DFG2, dN, A0w, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [SFG2, DFG2, dN, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [SFG2, DFG2, dN, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [SFG2, DFG2, dN, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [SFG2, DFG2, dN, A0w, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [SFG2, DFG2, dN, A0w, CE_eq]; omega
  H_SRV := srv_7j SFG2 rfl (by decide) (by decide) (by decide)

theorem SFG2_scn : Scn2 DFG2 SFG2 0 (-1000) 9 19 100 where
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [SFG2, A0w]; omega
  H_A0_prev := by decide
  H_q_init := by intro t ht; simp [SFG2]; omega
  H_A1_init := by intro t ht; simp [SFG2]; omega
  H_A2_init := by intro t ht; simp [SFG2]; omega
  H_SETTLED := by simp [DFG2, dN]

theorem FG2_viol :
    DFG2.wr2g + DFG2.g2f + DFG2.wg2 + DFG2.c2f =
      DFG2.wr2s + DFG2.Rf2 + 2 * DFG2.smin + DFG2.wa0s + DFG2.qr + DFG2.wfb + DFG2.Rrq +
        DFG2.wa01 + DFG2.c1r + 1 ∧
    RT2bs DFG2 0 0 0 1 ∧ A0Fork2 DFG2 := by
  refine ⟨by decide, ⟨by decide, by decide, by decide, by decide⟩, by unfold A0Fork2; decide⟩

theorem FG2_both : (SFG2.A1 20 && SFG2.A2 20) = true := by decide

theorem forkG2_false : ¬ Claim2 0 0 0 1 := by
  intro h
  have := h DFG2 SFG2 0 (-1000) 9 19 100 SFG2_run SFG2_scn FG2_viol.2.1 FG2_viol.2.2 20
    (by omega)
  rw [FG2_both] at this; exact absurd this (by decide)

/-! ## The pulse fields at one corner (every arc rise = fall): eternal runt trains

`pulse` (7h) / `pulse` of RT2b (7j): A0's low pulse at ua1 (ua2), 10 ps,
is one tick shorter than ua1's (ua2's) fall loop `c1f + wfa1 = 8 + 3`. The
C-element falls at 20, its own low edge is still on the feedback wire when
A0 re-rises, so it re-latches high at 30 for one tick, and the hole
recirculates through the pure-delay loop (period 11) forever; the other ack
rose at 20. Every arc is a single delay (one corner); A0's route to the
releasing client's C-element is 3. This refines `A1_band_overlap_matched`
(matched forks) to a 1-tick, unmatched, one-corner counter-run. -/

/-- `dN` with the ua1 / ua2 rise arcs free as well. -/
def dP (wq wa01 wfa1 wa02 wfa2 c1 c2 smin : Int)
    (h : 0 ≤ wq ∧ 0 ≤ wa01 ∧ 0 ≤ wfa1 ∧ 0 ≤ wa02 ∧ 0 ≤ wfa2 ∧ 1 ≤ c1 ∧ 1 ≤ c2 ∧ 0 ≤ smin) :
    Dl where
  wr1s := 0
  wr2s := 0
  wr1g := 0
  wr2g := 0
  wfb := 0
  wa0s := 0
  wq := wq
  wg1 := 0
  wa01 := wa01
  wfa1 := wfa1
  wg2 := 0
  wa02 := wa02
  wfa2 := wfa2
  qr := 1
  qf := 1
  Rr1 := 1
  Rf1 := 1
  Rr2 := 1
  Rf2 := 1
  Rrq := 1
  Rfq := 1
  g1r1 := 1
  g1f1 := 1
  g1r2 := 1
  g1f2 := 1
  g1rq := 1
  g1fq := 1
  g2r := 1
  g2f := 1
  c1r := c1
  c1f := c1
  c2r := c2
  c2f := c2
  smin := smin
  H_NONNEG := by omega
  H_RISE_LE_FALL := by omega
  H_LOOP_POS := by omega

def DP : Dl := dP 0 3 3 0 0 8 1 8 (by omega)

def SP : Sigs where
  r1 := fun t => decide (t < 0)
  r2 := fun _ => true
  q := fun t => decide (t < 10)
  R0 := fun t => decide (t < 1) || decide (11 ≤ t)
  g1 := fun t => decide (t < 1)
  g2 := fun t => decide (11 ≤ t)
  A0 := A0w
  A1 := fun t => decide (t < 20) || (decide (30 ≤ t) && decide (t % 11 = 8))
  A2 := fun t => decide (20 ≤ t)

theorem SP_run : Run DP SP where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [SP, DP, dP, A0w, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [SP, DP, dP, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [SP, DP, dP, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [SP, DP, dP, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [SP, DP, dP, A0w, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [SP, DP, dP, A0w, CE_eq]; omega
  H_SRV := srv_7h SP rfl (by decide) (by decide) (by decide)

theorem SP_scn : Scn DP SP 0 (-1000) 9 19 100 where
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [SP, A0w]; omega
  H_A0_prev := by decide
  H_q_init := by intro t ht; simp [SP]; omega
  H_A1_init := by intro t ht; simp [SP]; omega
  H_A2_init := by intro t ht; simp [SP]; omega
  H_SETTLED := by simp [DP, dP]

theorem P_viol :
    DP.c1f + DP.wfa1 = DP.wa0s + DP.qf + DP.wfb + DP.Rrq + DP.smin + 1 ∧
    RT2s DP 1 0 0 0 ∧ A0Fork DP := by
  refine ⟨by decide, ⟨by decide, by decide, by decide, by decide⟩, by unfold A0Fork; decide⟩

theorem P_both (k : Nat) : (SP.A1 (30 + 11 * k) && SP.A2 (30 + 11 * k)) = true := by
  simp [SP]; omega

theorem pulse_false : ¬ Claim 1 0 0 0 := by
  intro h
  have := h DP SP 0 (-1000) 9 19 100 SP_run SP_scn P_viol.2.1 P_viol.2.2 30 (by omega)
  have e : (SP.A1 30 && SP.A2 30) = true := by decide
  rw [e] at this; exact absurd this (by decide)

def DP2 : Dl := dP 0 0 0 3 3 1 8 8 (by omega)

def SP2 : Sigs where
  r1 := fun _ => true
  r2 := fun t => decide (t < 0)
  q := fun t => decide (10 ≤ t)
  R0 := fun t => decide (t < 1) || decide (11 ≤ t)
  g1 := fun t => decide (11 ≤ t)
  g2 := fun t => decide (t < 1)
  A0 := A0w
  A1 := fun t => decide (20 ≤ t)
  A2 := fun t => decide (t < 20) || (decide (30 ≤ t) && decide (t % 11 = 8))

theorem SP2_run : Run DP2 SP2 where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [SP2, DP2, dP, A0w, FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [SP2, DP2, dP, FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [SP2, DP2, dP, FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [SP2, DP2, dP, FG2_eq]; omega
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [SP2, DP2, dP, A0w, CE_eq]; omega
  H_A2 := by intro t; rw [Bool.eq_iff_iff]; simp [SP2, DP2, dP, A0w, CE_eq]; omega
  H_SRV := srv_7j SP2 rfl (by decide) (by decide) (by decide)

theorem SP2_scn : Scn2 DP2 SP2 0 (-1000) 9 19 100 where
  H_ORDER := by omega
  H_r1 := fun _ _ => rfl
  H_r2 := fun _ _ => rfl
  H_A0 := by intro t h1 _; rw [Bool.eq_iff_iff]; simp [SP2, A0w]; omega
  H_A0_prev := by decide
  H_q_init := by intro t ht; simp [SP2]; omega
  H_A1_init := by intro t ht; simp [SP2]; omega
  H_A2_init := by intro t ht; simp [SP2]; omega
  H_SETTLED := by simp [DP2, dP]

theorem P2_viol :
    DP2.c2f + DP2.wfa2 = DP2.wa0s + DP2.qr + DP2.wfb + DP2.Rrq + DP2.smin + 1 ∧
    RT2bs DP2 1 0 0 0 ∧ A0Fork2 DP2 := by
  refine ⟨by decide, ⟨by decide, by decide, by decide, by decide⟩, by unfold A0Fork2; decide⟩

theorem pulse2_false : ¬ Claim2 1 0 0 0 := by
  intro h
  have := h DP2 SP2 0 (-1000) 9 19 100 SP2_run SP2_scn P2_viol.2.1 P2_viol.2.2 30 (by omega)
  have e : (SP2.A1 30 && SP2.A2 30) = true := by decide
  rw [e] at this; exact absurd this (by decide)

end Formal.Cells.Necessity2Arb
