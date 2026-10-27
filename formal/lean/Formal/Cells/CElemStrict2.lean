import Formal.Cells.CElemStrict

/-!
# The strict own-feedback race on every C-element variant, the latch pair, and reset release

Continuation of `CElemStrict` (probe Bs; notes/B-celem-strict.md). Same model:
H_TREE (per-pin Kleene mux tree `lutK` on the REAL INIT, one trace per pin),
H_MUX_KLEENE (a moving select reads `x` on `[s, s + w)`), H_FB_PURE (the own
feedback pin is a pure delay `D ≥ 1` of the root), H_IN_PHASES (five input
phases). This file

1. generalises the race theorem to a feedback that starts at a KLEENE value
   `v : K3` (so `v = x`, the power-up state, is covered): `FactsK`, `LoopK`,
   `prefix_okK`, `cleanK`, `hazardK`, `clean_iffK`, `box_iffK`; Bs's `Facts`
   and `Loop` are the case `v = ofBool b` (`factsK_of_facts`, `loopK_of_loop`);
2. discharges the facts by `decide +kernel` for EVERY four-phase cycle
   (direction × follow pin × release pin) of bd_c2, bd_c2_set, bd_c2n,
   bd_c2n_set, bd_c3, bd_c4, bd_c2_norst, bd_c3_norst (`*_all`); bd_ctree
   nodes are bd_c2/bd_c3/bd_c4 instances (cells/rtl/bd_ce.v), so they are
   covered by these;
3. the LUT6_2 latch pair: O5 (bit i) and O6 (bit i+1), with the OTHER bit's
   two pins carrying arbitrary time-varying Kleene traces (`pair_o5_loop`,
   `pair_o6_loop` reduce them to Bs's `latch_facts`);
4. rst as the release pin: the reset pulse is the follow phase (rst
   `0 → x → 1`), its fall the release (`1 → x → 0`), the data pins static at
   a binary vector `w`. Exhaustively over `w` (by decide, from the binary
   spec only): if the cell HOLDS at `w` the race facts hold for `v = ¬reset`
   AND for `v = x` (power-up) (`*_rst_race`), so the exact reset-width
   condition is `D + wa ≤ P` (`reset_width_iff`; strict `Dmax < P` at
   `wa = 1`, `reset_width_strict`); if `w` FORCES the reset value the release
   is race-free for every `D`, `s` (`*_rst_forced`, `forced_clean`); the
   remaining `w` (all inputs at the non-reset value) leaves reset by design.
   Boundary traces on the real INITs: `rst_boundary_x` (bd_c2, w = (1,0),
   equality: `x` at the release tick), `rst_glitch` (binary release before
   the feedback moved: the cell goes back to 1, reset lost),
   `rst_powerup_x` (power-up X, width = D: still `x`), `rst_boundary_x_c2n`
   (bd_c2n with a = b = 0, the link's idle vector), and the strict side clean.

Core Lean; `decide +kernel` on finite facts, `omega` and induction elsewhere.
-/

namespace Formal.Cells
namespace CElemStrict2

open Formal.Cells.CElemFn
open Formal.Cells.CElemStrict

/-! ## 1. The race with a Kleene initial value -/

/-- The spec edge from a Kleene start `v`. -/
def edgeK (v : K3) (n : Bool) (tb wb t : Nat) : K3 :=
  if t < tb then v else if t < tb + wb then K3.x else K3.ofBool n

structure LoopK {ι : Type} (F : ι → K3 → K3) (I0 IX I1 RX R1 : ι) (v : K3)
    (tb wb s wa D : Nat) (i : Nat → ι) (qp G : Nat → K3) : Prop where
  H_TREE : ∀ t, G t = F (i t) (qp t)
  H_FB_PURE : ∀ t, qp t = if t < D then v else G (t - D)
  H_IN_PHASES : ∀ t, i t = phase I0 IX I1 RX R1 tb wb s wa t

structure FactsK {ι : Type} (F : ι → K3 → K3) (I0 IX I1 RX R1 : ι) (v : K3) (n : Bool) : Prop where
  ne : v ≠ K3.ofBool n
  init : F I0 v = v
  win_v : F IX v = K3.x
  win_x : F IX K3.x = K3.x
  follow : ∀ k, F I1 k = K3.ofBool n
  holdX : F RX (K3.ofBool n) = K3.ofBool n
  hold1 : F R1 (K3.ofBool n) = K3.ofBool n
  hzXX : F RX K3.x = K3.x
  hz1X : F R1 K3.x = K3.x
  hzXv : F RX v = K3.x
  hz1v : F R1 v = v

def SpecK (v : K3) (n : Bool) (tb wb : Nat) (G : Nat → K3) : Prop :=
  ∀ t, G t = edgeK v n tb wb t

theorem factsK_of_facts {ι : Type} {F : ι → K3 → K3} {I0 IX I1 RX R1 : ι} {v n : Bool}
    (H : Facts F I0 IX I1 RX R1 v n) : FactsK F I0 IX I1 RX R1 (K3.ofBool v) n :=
  { ne := fun h => H.ne (ofBool_inj h), init := H.init, win_v := H.win_v, win_x := H.win_x,
    follow := H.follow, holdX := H.holdX, hold1 := H.hold1, hzXX := H.hzXX, hz1X := H.hz1X,
    hzXv := H.hzXv, hz1v := H.hz1v }

theorem facts_of_factsK {ι : Type} {F : ι → K3 → K3} {I0 IX I1 RX R1 : ι} {v n : Bool}
    (H : FactsK F I0 IX I1 RX R1 (K3.ofBool v) n) : Facts F I0 IX I1 RX R1 v n :=
  { ne := fun h => H.ne (by rw [h]), init := H.init, win_v := H.win_v, win_x := H.win_x,
    follow := H.follow, holdX := H.holdX, hold1 := H.hold1, hzXX := H.hzXX, hz1X := H.hz1X,
    hzXv := H.hzXv, hz1v := H.hz1v }

theorem loopK_of_loop {ι : Type} {F : ι → K3 → K3} {I0 IX I1 RX R1 : ι} {v : Bool}
    {tb wb s wa D : Nat} {i : Nat → ι} {qp G : Nat → K3}
    (L : Loop F I0 IX I1 RX R1 v tb wb s wa D i qp G) :
    LoopK F I0 IX I1 RX R1 (K3.ofBool v) tb wb s wa D i qp G :=
  ⟨L.H_TREE, L.H_FB_PURE, L.H_IN_PHASES⟩

theorem specK_iff (v n : Bool) (tb wb : Nat) (G : Nat → K3) :
    SpecK (K3.ofBool v) n tb wb G ↔ Spec v n tb wb G := Iff.rfl

section generic
variable {ι : Type} {F : ι → K3 → K3} {I0 IX I1 RX R1 : ι} {v : K3} {n : Bool}
  {tb wb s wa D : Nat} {i : Nat → ι} {qp G : Nat → K3}

theorem prefix_okK (L : LoopK F I0 IX I1 RX R1 v tb wb s wa D i qp G)
    (H : FactsK F I0 IX I1 RX R1 v n) (hD : 1 ≤ D) :
    ∀ t, t < s → G t = edgeK v n tb wb t := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro hts
    rw [L.H_TREE, L.H_IN_PHASES, L.H_FB_PURE]
    unfold phase edgeK
    by_cases h1 : t < tb
    · simp only [h1, ↓reduceIte]
      by_cases h2 : t < D
      · simp only [h2, ↓reduceIte]; exact H.init
      · simp only [h2, ↓reduceIte]
        rw [ih (t - D) (by omega) (by omega)]
        simp only [edgeK, show t - D < tb by omega, ↓reduceIte]; exact H.init
    · simp only [h1, ↓reduceIte]
      by_cases h2 : t < tb + wb
      · simp only [h2, ↓reduceIte]
        by_cases h3 : t < D
        · simp only [h3, ↓reduceIte]; exact H.win_v
        · simp only [h3, ↓reduceIte]
          rw [ih (t - D) (by omega) (by omega)]
          unfold edgeK
          by_cases h4 : t - D < tb
          · simp only [h4, ↓reduceIte]; exact H.win_v
          · simp only [h4, ↓reduceIte, show t - D < tb + wb by omega, ↓reduceIte]; exact H.win_x
      · simp only [h2, ↓reduceIte, hts, ↓reduceIte]; exact H.follow _

theorem cleanK (L : LoopK F I0 IX I1 RX R1 v tb wb s wa D i qp G)
    (H : FactsK F I0 IX I1 RX R1 v n) (hD : 1 ≤ D) (hrace : tb + D + wb ≤ s) :
    SpecK v n tb wb G := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    by_cases hts : t < s
    · exact prefix_okK L H hD t hts
    · rw [L.H_TREE, L.H_IN_PHASES, L.H_FB_PURE]
      have hq : G (t - D) = K3.ofBool n := by
        rw [ih (t - D) (by omega)]
        simp only [edgeK, show ¬ t - D < tb by omega, show ¬ t - D < tb + wb by omega, ↓reduceIte]
      simp only [phase, edgeK, show ¬ t < D by omega, show ¬ t < tb by omega,
        show ¬ t < tb + wb by omega, hts, ↓reduceIte, hq]
      by_cases h5 : t < s + wa
      · simp only [h5, ↓reduceIte]; exact H.holdX
      · simp only [h5, ↓reduceIte]; exact H.hold1

theorem hazardK (L : LoopK F I0 IX I1 RX R1 v tb wb s wa D i qp G)
    (H : FactsK F I0 IX I1 RX R1 v n) (hD : 1 ≤ D) (hord : tb + wb ≤ s)
    (hrace : s < tb + D + wb) :
    G s ≠ K3.ofBool n ∧ edgeK v n tb wb s = K3.ofBool n := by
  have hspec : edgeK v n tb wb s = K3.ofBool n := by
    simp only [edgeK, show ¬ s < tb by omega, show ¬ s < tb + wb by omega, ↓reduceIte]
  refine ⟨?_, hspec⟩
  rw [L.H_TREE, L.H_IN_PHASES, L.H_FB_PURE]
  simp only [phase, show ¬ s < tb by omega, show ¬ s < tb + wb by omega,
    Nat.lt_irrefl, ↓reduceIte]
  have hq : (if s < D then v else G (s - D)) = v ∨
      (if s < D then v else G (s - D)) = K3.x := by
    by_cases h : s < D
    · simp only [h, ↓reduceIte]; simp
    · simp only [h, ↓reduceIte]
      rw [prefix_okK L H hD (s - D) (by omega)]
      unfold edgeK
      by_cases h4 : s - D < tb
      · simp only [h4, ↓reduceIte]; simp
      · simp only [h4, ↓reduceIte, show s - D < tb + wb by omega, ↓reduceIte]; simp
  by_cases h5 : s < s + wa
  · simp only [h5, ↓reduceIte]
    rcases hq with h | h <;> rw [h]
    · rw [H.hzXv]; exact (ofBool_ne_x n).symm
    · rw [H.hzXX]; exact (ofBool_ne_x n).symm
  · simp only [h5, ↓reduceIte]
    rcases hq with h | h <;> rw [h]
    · rw [H.hz1v]; exact H.ne
    · rw [H.hz1X]; exact (ofBool_ne_x n).symm

theorem clean_iffK (L : LoopK F I0 IX I1 RX R1 v tb wb s wa D i qp G)
    (H : FactsK F I0 IX I1 RX R1 v n) (hD : 1 ≤ D) (hord : tb + wb ≤ s) :
    SpecK v n tb wb G ↔ tb + D + wb ≤ s := by
  constructor
  · intro hs
    apply Classical.byContradiction; intro hlt
    have ⟨h1, h2⟩ := hazardK L H hD hord (by omega)
    exact h1 (by rw [hs s]; exact h2)
  · exact cleanK L H hD

/-- **Race-free release.** If the cell's function is the constant `n` in the
follow-settled phase and in both release phases, whatever the feedback reads,
the root is `n` from `tb + wb` on, for every `D` and every release time. -/
theorem forced_clean (L : LoopK F I0 IX I1 RX R1 v tb wb s wa D i qp G)
    (hI1 : ∀ k, F I1 k = K3.ofBool n) (hRX : ∀ k, F RX k = K3.ofBool n)
    (hR1 : ∀ k, F R1 k = K3.ofBool n) : ∀ t, tb + wb ≤ t → G t = K3.ofBool n := by
  intro t ht
  rw [L.H_TREE, L.H_IN_PHASES]
  unfold phase
  simp only [show ¬ t < tb by omega, show ¬ t < tb + wb by omega, ↓reduceIte]
  by_cases h3 : t < s
  · simp only [h3, ↓reduceIte]; exact hI1 _
  · simp only [h3, ↓reduceIte]
    by_cases h4 : t < s + wa
    · simp only [h4, ↓reduceIte]; exact hRX _
    · simp only [h4, ↓reduceIte]; exact hR1 _

end generic

/-! ## Non-vacuity (simulator with a Kleene start) and the box form -/

section sim
variable {ι : Type} (F : ι → K3 → K3) (inp : Nat → ι) (v : K3) (d : Nat)

def simGK : Nat → K3
  | t => F (inp t) (if h : t < d + 1 then v else simGK (t - (d + 1)))
termination_by t => t
decreasing_by omega

def simQK (t : Nat) : K3 := if t < d + 1 then v else simGK F inp v d (t - (d + 1))

theorem sim_loopK {I0 IX I1 RX R1 : ι} {tb wb s wa : Nat}
    (hi : ∀ t, inp t = phase I0 IX I1 RX R1 tb wb s wa t) :
    LoopK F I0 IX I1 RX R1 v tb wb s wa (d + 1) inp (simQK F inp v d) (simGK F inp v d) where
  H_TREE := by
    intro t; rw [simGK]; unfold simQK
    by_cases h : t < d + 1 <;> simp [h]
  H_FB_PURE := fun _ => rfl
  H_IN_PHASES := hi

end sim

theorem loop_existsK {ι : Type} (F : ι → K3 → K3) (I0 IX I1 RX R1 : ι) (v : K3)
    (tb wb s wa D : Nat) (hD : 1 ≤ D) :
    ∃ i qp G, LoopK F I0 IX I1 RX R1 v tb wb s wa D i qp G := by
  obtain ⟨d, rfl⟩ : ∃ d, D = d + 1 := ⟨D - 1, by omega⟩
  exact ⟨_, _, _, sim_loopK F (phase I0 IX I1 RX R1 tb wb s wa) v d (fun _ => rfl)⟩

def SafeBoxK {ι : Type} (F : ι → K3 → K3) (I0 IX I1 RX R1 : ι) (v : K3) (n : Bool)
    (tb wb wa Dlo Dhi slo : Nat) : Prop :=
  ∀ D s, Dlo ≤ D → D ≤ Dhi → slo ≤ s →
    ∀ i qp G, LoopK F I0 IX I1 RX R1 v tb wb s wa D i qp G → SpecK v n tb wb G

theorem box_iffK {ι : Type} {F : ι → K3 → K3} {I0 IX I1 RX R1 : ι} {v : K3} {n : Bool}
    (H : FactsK F I0 IX I1 RX R1 v n) {tb wb wa Dlo Dhi slo : Nat}
    (hlo : 1 ≤ Dlo) (hbox : Dlo ≤ Dhi) (hord : tb + wb ≤ slo) :
    SafeBoxK F I0 IX I1 RX R1 v n tb wb wa Dlo Dhi slo ↔ tb + Dhi + wb ≤ slo := by
  constructor
  · intro hs
    obtain ⟨i, qp, G, L⟩ := loop_existsK F I0 IX I1 RX R1 v tb wb slo wa Dhi (by omega)
    exact (clean_iffK L H (by omega) hord).1 (hs Dhi slo hbox (Nat.le_refl _) (Nat.le_refl _) i qp G L)
  · intro hr D s h1 h2 h3 i qp G L
    exact cleanK L H (by omega) (by omega)

/-! ## A Boolean checker for the facts (so `decide +kernel` can enumerate) -/

def factsB {ι : Type} (F : ι → K3 → K3) (I0 IX I1 RX R1 : ι) (v : K3) (n : Bool) : Bool :=
  decide (v ≠ K3.ofBool n) && decide (F I0 v = v) && decide (F IX v = K3.x) &&
  decide (F IX K3.x = K3.x) && decide (F I1 K3.f = K3.ofBool n) &&
  decide (F I1 K3.t = K3.ofBool n) && decide (F I1 K3.x = K3.ofBool n) &&
  decide (F RX (K3.ofBool n) = K3.ofBool n) && decide (F R1 (K3.ofBool n) = K3.ofBool n) &&
  decide (F RX K3.x = K3.x) && decide (F R1 K3.x = K3.x) && decide (F RX v = K3.x) &&
  decide (F R1 v = v)

theorem factsK_of_B {ι : Type} {F : ι → K3 → K3} {I0 IX I1 RX R1 : ι} {v : K3} {n : Bool}
    (h : factsB F I0 IX I1 RX R1 v n = true) : FactsK F I0 IX I1 RX R1 v n := by
  simp only [factsB, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨⟨h0, h1⟩, h2⟩, h3⟩, h4f⟩, h4t⟩, h4x⟩, h5⟩, h6⟩, h7⟩, h8⟩, h9⟩, h10⟩ := h
  exact { ne := h0, init := h1, win_v := h2, win_x := h3,
          follow := fun k => by cases k; exact h4f; exact h4t; exact h4x,
          holdX := h5, hold1 := h6, hzXX := h7, hz1X := h8, hzXv := h9, hz1v := h10 }

/-! ## 2. Every four-phase cycle of every C-element variant

Pins are a list `[in0, in1, ...]` of the data inputs in the cell's pin order
(I0, I1, ...); `rst` is held at 0 (released), the feedback is the cell's own
`q` pin. `pol j = true` marks an input read through a bubble (bd_c2n's b).
A cycle: the cell holds `v`; every input except the follow pin sits at the
logical value `u = !v`, the follow pin moves `v → x → u` (the cell must
follow to `u`); then the release pin (any pin, possibly the same) moves
`u → x → v` (the cell must hold `u`). -/

/-- Physical pin value from a logical one. -/
def phys (pol : List Bool) (j : Nat) (k : K3) : K3 := if pol.getD j false then K3.not k else k

/-- Input vector: every pin at logical `u`, except pin `sp` (if any) at `val`. -/
def vec (pol : List Bool) (u : Bool) (sp : Option Nat) (val : K3) : List K3 :=
  (List.range pol.length).map fun j => phys pol j (if sp = some j then val else kb u)

/-- The five phase vectors of cycle (v, follow f, release r). -/
def cyc (pol : List Bool) (v : Bool) (f r : Nat) :
    List K3 × List K3 × List K3 × List K3 × List K3 :=
  (vec pol (!v) (some f) (kb v), vec pol (!v) (some f) K3.x, vec pol (!v) none K3.f,
   vec pol (!v) (some r) K3.x, vec pol (!v) (some r) (kb v))

def g (l : List K3) (j : Nat) : K3 := l.getD j K3.f

/-- The cells (INITs and pin maps verbatim from cells/rtl/bd_ce.v via
`CElemFn`), rst pin = 0. -/
def c2L      (l : List K3) (q : K3) : K3 := c2K (g l 0) (g l 1) q K3.f
def c2setL   (l : List K3) (q : K3) : K3 := c2setK (g l 0) (g l 1) q K3.f
def c2nL     (l : List K3) (q : K3) : K3 := c2nK (g l 0) (g l 1) q K3.f
def c2nsetL  (l : List K3) (q : K3) : K3 := c2nsetK (g l 0) (g l 1) q K3.f
def c3L      (l : List K3) (q : K3) : K3 := c3K (g l 0) (g l 1) (g l 2) q K3.f
def c4L      (l : List K3) (q : K3) : K3 := c4K (g l 0) (g l 1) (g l 2) (g l 3) q K3.f
def c2norstL (l : List K3) (q : K3) : K3 := c2norstK (g l 0) (g l 1) q
def c3norstL (l : List K3) (q : K3) : K3 := c3norstK (g l 0) (g l 1) (g l 2) q

/-- All cycles of a cell satisfy the facts. -/
def AllCycles (F : List K3 → K3 → K3) (pol : List Bool) : Prop :=
  ∀ v : Bool, ∀ f r : Fin pol.length,
    let c := cyc pol v f r
    Facts F c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 v (!v)

theorem allCycles_of_B {F : List K3 → K3 → K3} {pol : List Bool}
    (h : ∀ v : Bool, ∀ f r : Fin pol.length,
      let c := cyc pol v f r
      factsB F c.1 c.2.1 c.2.2.1 c.2.2.2.1 c.2.2.2.2 (kb v) (!v) = true) :
    AllCycles F pol := fun v f r => facts_of_factsK (factsK_of_B (h v f r))

/-- bd_c2: 8 cycles (re-checks Bs's `c2_all` in this framework). -/
theorem c2_all8 : AllCycles c2L [false, false] := allCycles_of_B (by decide +kernel)
/-- bd_c2_set (INIT FFE8...): 8 cycles. -/
theorem c2set_all : AllCycles c2setL [false, false] := allCycles_of_B (by decide +kernel)
/-- bd_c2n (INIT 00B2...), b through a bubble: all 8 cycles (Bs had one). -/
theorem c2n_all : AllCycles c2nL [false, true] := allCycles_of_B (by decide +kernel)
/-- bd_c2n_set (INIT FFB2...): 8 cycles. -/
theorem c2nset_all : AllCycles c2nsetL [false, true] := allCycles_of_B (by decide +kernel)
/-- bd_c3 (INIT 0000_FE80_0000_FE80): 2 × 3 × 3 = 18 cycles. -/
theorem c3_all : AllCycles c3L [false, false, false] := allCycles_of_B (by decide +kernel)
/-- bd_c4 (INIT 0000_0000_FFFE_8000): 2 × 4 × 4 = 32 cycles. -/
theorem c4_all : AllCycles c4L [false, false, false, false] := allCycles_of_B (by decide +kernel)
/-- bd_c2_norst (INIT E8E8...): 8 cycles. -/
theorem c2norst_all : AllCycles c2norstL [false, false] := allCycles_of_B (by decide +kernel)
/-- bd_c3_norst (INIT FE80...): 18 cycles. -/
theorem c3norst_all : AllCycles c3norstL [false, false, false] := allCycles_of_B (by decide +kernel)

/-- Usage form: for every cycle of bd_c4 (say), the race is exact. -/
theorem c4_clean_iff (v : Bool) (f r : Fin 4) {tb wb s wa D : Nat} {i : Nat → List K3}
    {qp G : Nat → K3}
    (L : Loop c4L (cyc [false, false, false, false] v f r).1
      (cyc [false, false, false, false] v f r).2.1 (cyc [false, false, false, false] v f r).2.2.1
      (cyc [false, false, false, false] v f r).2.2.2.1 (cyc [false, false, false, false] v f r).2.2.2.2
      v tb wb s wa D i qp G)
    (hD : 1 ≤ D) (hord : tb + wb ≤ s) :
    Spec v (!v) tb wb G ↔ tb + D + wb ≤ s :=
  clean_iff L (c4_all v f r) hD hord

/-! ## 3. The LUT6_2 latch pair: O5 (bit i) and O6 (bit i+1)

Pins: I0 = d[i], I1 = en, I2 = q[i], I3 = d[i+1], I4 = q[i+1], I5 = 1. The
other bit's two pins may carry ANY Kleene trace (they move independently);
the root of each output is still exactly the odd-bit latch function of its
own pins (`Latch.pair_o5_kleene`, `pair_o6_kleene`), so each output's loop
IS a `Loop latF` and Bs's `latch_facts` give the exact strict setup race. -/

theorem pair_o5_eq (d0 en q0 d1 q1 : K3) :
    o5K Latch.PAIR [d0, en, q0, d1, q1, K3.t] = latF (d0, en) q0 := by
  rw [Latch.pair_o5_kleene]; unfold latF; rw [Latch.odd_kleene]

theorem pair_o6_eq (d0 en q0 d1 q1 : K3) :
    o6K Latch.PAIR [d0, en, q0, d1, q1, K3.t] = latF (d1, en) q1 := by
  rw [Latch.pair_o6_kleene]; unfold latF; rw [Latch.odd_kleene]

/-- O5's loop with the other bit's pins `d1 t`, `q1 t` arbitrary. -/
theorem pair_o5_loop {I0 IX I1 RX R1 : K3 × K3} {v : Bool} {tb wb s wa D : Nat}
    {i : Nat → K3 × K3} {qp G d1 q1 : Nat → K3}
    (H_TREE : ∀ t, G t = o5K Latch.PAIR [(i t).1, (i t).2, qp t, d1 t, q1 t, K3.t])
    (H_FB_PURE : ∀ t, qp t = if t < D then K3.ofBool v else G (t - D))
    (H_IN_PHASES : ∀ t, i t = phase I0 IX I1 RX R1 tb wb s wa t) :
    Loop latF I0 IX I1 RX R1 v tb wb s wa D i qp G :=
  ⟨fun t => by rw [H_TREE, pair_o5_eq], H_FB_PURE, H_IN_PHASES⟩

/-- O6's loop (bit i+1: d on I3, q on I4) with bit i's pins arbitrary. -/
theorem pair_o6_loop {I0 IX I1 RX R1 : K3 × K3} {v : Bool} {tb wb s wa D : Nat}
    {i : Nat → K3 × K3} {qp G d0 q0 : Nat → K3}
    (H_TREE : ∀ t, G t = o6K Latch.PAIR [d0 t, (i t).2, q0 t, (i t).1, qp t, K3.t])
    (H_FB_PURE : ∀ t, qp t = if t < D then K3.ofBool v else G (t - D))
    (H_IN_PHASES : ∀ t, i t = phase I0 IX I1 RX R1 tb wb s wa t) :
    Loop latF I0 IX I1 RX R1 v tb wb s wa D i qp G :=
  ⟨fun t => by rw [H_TREE, pair_o6_eq], H_FB_PURE, H_IN_PHASES⟩

/-- Pair bit i (O5): setup against the enable fall is exact and strict,
whatever bit i+1 does. -/
theorem pair_o5_clean_iff (v : Bool) {tb wb s wa D : Nat}
    {i : Nat → K3 × K3} {qp G d1 q1 : Nat → K3}
    (H_TREE : ∀ t, G t = o5K Latch.PAIR [(i t).1, (i t).2, qp t, d1 t, q1 t, K3.t])
    (H_FB_PURE : ∀ t, qp t = if t < D then K3.ofBool v else G (t - D))
    (H_IN_PHASES : ∀ t, i t = phase (kb v, K3.t) (K3.x, K3.t) (kb (!v), K3.t)
      (kb (!v), K3.x) (kb (!v), K3.f) tb wb s wa t)
    (hD : 1 ≤ D) (hord : tb + wb ≤ s) :
    Spec v (!v) tb wb G ↔ tb + D + wb ≤ s :=
  clean_iff (pair_o5_loop H_TREE H_FB_PURE H_IN_PHASES) (latch_facts v) hD hord

/-- Pair bit i+1 (O6): the same. -/
theorem pair_o6_clean_iff (v : Bool) {tb wb s wa D : Nat}
    {i : Nat → K3 × K3} {qp G d0 q0 : Nat → K3}
    (H_TREE : ∀ t, G t = o6K Latch.PAIR [d0 t, (i t).2, q0 t, (i t).1, qp t, K3.t])
    (H_FB_PURE : ∀ t, qp t = if t < D then K3.ofBool v else G (t - D))
    (H_IN_PHASES : ∀ t, i t = phase (kb v, K3.t) (K3.x, K3.t) (kb (!v), K3.t)
      (kb (!v), K3.x) (kb (!v), K3.f) tb wb s wa t)
    (hD : 1 ≤ D) (hord : tb + wb ≤ s) :
    Spec v (!v) tb wb G ↔ tb + D + wb ≤ s :=
  clean_iff (pair_o6_loop H_TREE H_FB_PURE H_IN_PHASES) (latch_facts v) hD hord

/-! ## 4. rst as the release pin (reset release against the feedback)

The moving pin is rst; the data pins are static at a binary vector. Phases
of rst: `I0 = 0` (before reset), `IX = x` (assert edge), `I1 = 1` (held,
the cell must go to the reset value `n`), `RX = x` (release edge), `R1 = 0`
(released: the cell must HOLD `n`). `v` is the feedback before reset: the
non-reset value, or `x` (power-up: configuration does not define a LUT
loop). For power-up take `tb = 0`, `wb = 0` (rst high from the start).

Classification by the BINARY spec at the static vector (rst = 0):
* hold (`∀ q, cell(w, q) = q`): the race facts hold, for `v = ¬n` and
  `v = x`;
* forced (`∀ q, cell(w, q) = n`): race-free, the cell's function is `n` for
  every rst and every feedback value (Kleene);
* otherwise (all inputs at the non-reset value): the cell leaves reset by
  design (the spec is a follow, not a hold).
The checks below quantify over every binary `w` and every Kleene `v`. -/

def RST : K3 × K3 × K3 × K3 × K3 := (K3.f, K3.x, K3.t, K3.x, K3.f)

/-- The rst-driven cell at static inputs. `r` = rst pin, `q` = feedback. -/
def c2R (a b : Bool) (r q : K3) : K3 := c2K (kb a) (kb b) q r
def c2setR (a b : Bool) (r q : K3) : K3 := c2setK (kb a) (kb b) q r
def c2nR (a b : Bool) (r q : K3) : K3 := c2nK (kb a) (kb b) q r
def c2nsetR (a b : Bool) (r q : K3) : K3 := c2nsetK (kb a) (kb b) q r
def c3R (a b c : Bool) (r q : K3) : K3 := c3K (kb a) (kb b) (kb c) q r
def c4R (a b c d : Bool) (r q : K3) : K3 := c4K (kb a) (kb b) (kb c) (kb d) q r
/-- bd_latch_rst (pins I0 = d, I1 = en, I2 = q, I3 = rst). -/
def latRstR (init : Nat) (d en : Bool) (r q : K3) : K3 := lutK init [kb d, kb en, q, r, K3.f, K3.f]

/-- The rst facts, Boolean form. -/
def rstB (F : K3 → K3 → K3) (v : K3) (n : Bool) : Bool := factsB F K3.f K3.x K3.t K3.x K3.f v n

/-- Constant `n` in every rst/feedback value. -/
def forcedB (F : K3 → K3 → K3) (n : Bool) : Bool :=
  [K3.f, K3.t, K3.x].all fun r => [K3.f, K3.t, K3.x].all fun k => decide (F r k = K3.ofBool n)

theorem forced_of_B {F : K3 → K3 → K3} {n : Bool} (h : forcedB F n = true) :
    ∀ r k, F r k = K3.ofBool n := by
  intro r k
  simp only [forcedB, List.all_cons, List.all_nil, Bool.and_true, Bool.and_eq_true,
    decide_eq_true_eq] at h
  cases r <;> cases k <;> simp_all

/-- bd_c2 (reset value 0): every hold vector races, every forced vector is
race-free; for every Kleene start `v ≠ 0`. -/
theorem c2_rst_dec : ∀ a b : Bool,
    ((∀ q : Bool, c2B a b q false = q) → ∀ v : K3, v ≠ K3.f → rstB (c2R a b) v false = true) ∧
    ((∀ q : Bool, c2B a b q false = false) → forcedB (c2R a b) false = true) := by
  decide +kernel
theorem c2set_rst_dec : ∀ a b : Bool,
    ((∀ q : Bool, c2setB a b q false = q) → ∀ v : K3, v ≠ K3.t → rstB (c2setR a b) v true = true) ∧
    ((∀ q : Bool, c2setB a b q false = true) → forcedB (c2setR a b) true = true) := by
  decide +kernel
theorem c2n_rst_dec : ∀ a b : Bool,
    ((∀ q : Bool, c2nB a b q false = q) → ∀ v : K3, v ≠ K3.f → rstB (c2nR a b) v false = true) ∧
    ((∀ q : Bool, c2nB a b q false = false) → forcedB (c2nR a b) false = true) := by
  decide +kernel
theorem c2nset_rst_dec : ∀ a b : Bool,
    ((∀ q : Bool, c2nsetB a b q false = q) → ∀ v : K3, v ≠ K3.t → rstB (c2nsetR a b) v true = true) ∧
    ((∀ q : Bool, c2nsetB a b q false = true) → forcedB (c2nsetR a b) true = true) := by
  decide +kernel
theorem c3_rst_dec : ∀ a b c : Bool,
    ((∀ q : Bool, c3B a b c q false = q) → ∀ v : K3, v ≠ K3.f → rstB (c3R a b c) v false = true) ∧
    ((∀ q : Bool, c3B a b c q false = false) → forcedB (c3R a b c) false = true) := by
  decide +kernel
theorem c4_rst_dec : ∀ a b c d : Bool,
    ((∀ q : Bool, c4B a b c d q false = q) → ∀ v : K3, v ≠ K3.f → rstB (c4R a b c d) v false = true) ∧
    ((∀ q : Bool, c4B a b c d q false = false) → forcedB (c4R a b c d) false = true) := by
  decide +kernel
theorem latrst0_rst_dec : ∀ d en : Bool,
    ((∀ q : Bool, lutB Latch.RST0 [d, en, q, false, false, false] = q) →
      ∀ v : K3, v ≠ K3.f → rstB (latRstR Latch.RST0 d en) v false = true) ∧
    ((∀ q : Bool, lutB Latch.RST0 [d, en, q, false, false, false] = false) →
      forcedB (latRstR Latch.RST0 d en) false = true) := by
  decide +kernel
theorem latrst1_rst_dec : ∀ d en : Bool,
    ((∀ q : Bool, lutB Latch.RST1 [d, en, q, false, false, false] = q) →
      ∀ v : K3, v ≠ K3.t → rstB (latRstR Latch.RST1 d en) v true = true) ∧
    ((∀ q : Bool, lutB Latch.RST1 [d, en, q, false, false, false] = true) →
      forcedB (latRstR Latch.RST1 d en) true = true) := by
  decide +kernel

/-- Usage form for bd_c2 (the others are the same two lines). -/
theorem c2_rst_race {a b : Bool} (hhold : ∀ q : Bool, c2B a b q false = q) {v : K3}
    (hv : v ≠ K3.f) : FactsK (c2R a b) K3.f K3.x K3.t K3.x K3.f v false :=
  factsK_of_B ((c2_rst_dec a b).1 hhold v hv)

theorem c2_rst_forced {a b : Bool} (hf : ∀ q : Bool, c2B a b q false = false) :
    ∀ r k, c2R a b r k = K3.f := forced_of_B ((c2_rst_dec a b).2 hf)

theorem c2n_rst_race {a b : Bool} (hhold : ∀ q : Bool, c2nB a b q false = q) {v : K3}
    (hv : v ≠ K3.f) : FactsK (c2nR a b) K3.f K3.x K3.t K3.x K3.f v false :=
  factsK_of_B ((c2n_rst_dec a b).1 hhold v hv)

/-- The hold / forced / leaving vectors of bd_c2 and bd_c2n, by name. -/
theorem c2_rst_classes :
    (∀ q, c2B true false q false = q) ∧ (∀ q, c2B false true q false = q) ∧
    (∀ q, c2B false false q false = false) ∧ ¬ (∀ q, c2B true true q false = q) := by decide
theorem c2n_rst_classes :
    (∀ q, c2nB false false q false = q) ∧ (∀ q, c2nB true true q false = q) ∧
    (∀ q, c2nB false true q false = false) ∧ ¬ (∀ q, c2nB true false q false = q) := by decide

/-- **The exact reset-width condition.** `P` = rst's binary high width: from
its assert edge settled (`tb + wb`) to its release edge settled (`s + wa`).
Over `D ∈ [Dlo, Dhi]` and every release with width at least `P`, every
behaviour holds the reset value iff `Dhi + wa ≤ P`. -/
theorem reset_width_iff {F : K3 → K3 → K3} {v : K3} {n : Bool}
    (H : FactsK F K3.f K3.x K3.t K3.x K3.f v n) {tb wb wa Dlo Dhi P : Nat}
    (hlo : 1 ≤ Dlo) (hbox : Dlo ≤ Dhi) (hP : wa ≤ P) :
    SafeBoxK F K3.f K3.x K3.t K3.x K3.f v n tb wb wa Dlo Dhi (tb + wb + P - wa) ↔
      Dhi + wa ≤ P := by
  rw [box_iffK H hlo hbox (by omega)]; omega

/-- With the release select X for one tick: the reset must be held strictly
longer than the loop, `Dhi < P`. -/
theorem reset_width_strict {F : K3 → K3 → K3} {v : K3} {n : Bool}
    (H : FactsK F K3.f K3.x K3.t K3.x K3.f v n) {tb wb Dlo Dhi P : Nat}
    (hlo : 1 ≤ Dlo) (hbox : Dlo ≤ Dhi) (hP : 1 ≤ P) :
    SafeBoxK F K3.f K3.x K3.t K3.x K3.f v n tb wb 1 Dlo Dhi (tb + wb + P - 1) ↔ Dhi < P := by
  rw [reset_width_iff H hlo hbox hP]; omega

/-- Instantaneous release select (`wa = 0`): `Dhi ≤ P` exact. -/
theorem reset_width_atomic {F : K3 → K3 → K3} {v : K3} {n : Bool}
    (H : FactsK F K3.f K3.x K3.t K3.x K3.f v n) {tb wb Dlo Dhi P : Nat}
    (hlo : 1 ≤ Dlo) (hbox : Dlo ≤ Dhi) :
    SafeBoxK F K3.f K3.x K3.t K3.x K3.f v n tb wb 0 Dlo Dhi (tb + wb + P - 0) ↔ Dhi ≤ P := by
  rw [reset_width_iff H hlo hbox (Nat.zero_le _)]; omega

/-- Forced vector: race-free reset release, any width, any loop delay. -/
theorem c2_rst_forced_clean {tb wb s wa D : Nat} {v : K3} {i : Nat → K3} {qp G : Nat → K3}
    (L : LoopK (c2R false false) K3.f K3.x K3.t K3.x K3.f v tb wb s wa D i qp G) :
    ∀ t, tb + wb ≤ t → G t = K3.f := by
  have hf := c2_rst_forced (a := false) (b := false) (by decide)
  exact forced_clean (n := false) L (fun k => hf _ k) (fun k => hf _ k) (fun k => hf _ k)

/-! ### Boundary traces on the real INIT (D = 420, as in CElemStrict) -/

def rstPh (tb wb s wa : Nat) : Nat → K3 := phase K3.f K3.x K3.t K3.x K3.f tb wb s wa

/-- bd_c2, a = 1, b = 0 (hold), q = 1 before reset, rst asserted at 0 with a
one-tick X edge, released with B's non-strict width at equality
(`P = D = 420`, release select X at 420): the root reads 0 at 419 and `x`
at 420. -/
theorem rst_boundary_x :
    simGK (c2R true false) (rstPh 0 1 420 1) K3.t 419 419 = K3.f ∧
    simGK (c2R true false) (rstPh 0 1 420 1) K3.t 419 420 = K3.x := by
  have L := sim_loopK (c2R true false) (rstPh 0 1 420 1) K3.t 419
    (I0 := K3.f) (IX := K3.x) (I1 := K3.t) (RX := K3.x) (R1 := K3.f)
    (tb := 0) (wb := 1) (s := 420) (wa := 1) (fun _ => rfl)
  have H := c2_rst_race (a := true) (b := false) (by decide) (v := K3.t) (by decide)
  refine ⟨?_, ?_⟩
  · rw [prefix_okK L H (by omega) 419 (by omega)]; decide
  · rw [L.H_TREE]
    unfold simQK
    simp only [show ¬ (420 < 419 + 1) by omega, ↓reduceIte]
    rw [prefix_okK L H (by omega) (420 - (419 + 1)) (by omega)]
    decide

/-- The strict side: one tick longer, clean for ever. -/
theorem rst_strict_clean :
    SpecK K3.t false 0 1 (simGK (c2R true false) (rstPh 0 1 421 1) K3.t 419) :=
  cleanK (sim_loopK _ _ _ _ (fun _ => rfl))
    (c2_rst_race (a := true) (b := false) (by decide) (v := K3.t) (by decide)) (by omega) (by omega)

/-- Binary release (wa = 0) before the feedback moved (P = 299 < D): the
cell returns to 1, the reset is lost. -/
theorem rst_glitch :
    simGK (c2R true false) (rstPh 0 1 300 0) K3.t 419 300 = K3.t := by
  have L := sim_loopK (c2R true false) (rstPh 0 1 300 0) K3.t 419
    (I0 := K3.f) (IX := K3.x) (I1 := K3.t) (RX := K3.x) (R1 := K3.f)
    (tb := 0) (wb := 1) (s := 300) (wa := 0) (fun _ => rfl)
  rw [L.H_TREE]
  unfold simQK
  simp only [show (300 < 419 + 1) by omega, ↓reduceIte]
  decide

/-- Power-up: q = x, rst high from tick 0 (`tb = wb = 0`), released with
width equal to the loop (`P = D = 420`, select X at 419): the root is `x`
at the release tick: the reset did not define the cell. -/
theorem rst_powerup_x :
    simGK (c2R true false) (rstPh 0 0 419 1) K3.x 419 419 = K3.x := by
  have L := sim_loopK (c2R true false) (rstPh 0 0 419 1) K3.x 419
    (I0 := K3.f) (IX := K3.x) (I1 := K3.t) (RX := K3.x) (R1 := K3.f)
    (tb := 0) (wb := 0) (s := 419) (wa := 1) (fun _ => rfl)
  rw [L.H_TREE]
  unfold simQK
  simp only [show (419 < 419 + 1) by omega, ↓reduceIte]
  decide

theorem rst_powerup_strict_clean :
    SpecK K3.x false 0 0 (simGK (c2R true false) (rstPh 0 0 420 1) K3.x 419) :=
  cleanK (sim_loopK _ _ _ _ (fun _ => rfl))
    (c2_rst_race (a := true) (b := false) (by decide) (v := K3.x) (by decide)) (by omega) (by omega)

/-- bd_c2n at a = b = 0 (the link's idle vector, a hold for C(a, ¬b)):
equality gives `x` at the release tick. -/
theorem rst_boundary_x_c2n :
    simGK (c2nR false false) (rstPh 0 1 420 1) K3.t 419 420 = K3.x := by
  have L := sim_loopK (c2nR false false) (rstPh 0 1 420 1) K3.t 419
    (I0 := K3.f) (IX := K3.x) (I1 := K3.t) (RX := K3.x) (R1 := K3.f)
    (tb := 0) (wb := 1) (s := 420) (wa := 1) (fun _ => rfl)
  have H := c2n_rst_race (a := false) (b := false) (by decide) (v := K3.t) (by decide)
  rw [L.H_TREE]
  unfold simQK
  simp only [show ¬ (420 < 419 + 1) by omega, ↓reduceIte]
  rw [prefix_okK L H (by omega) (420 - (419 + 1)) (by omega)]
  decide

end CElemStrict2
end Formal.Cells
