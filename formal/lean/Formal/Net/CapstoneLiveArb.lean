import Formal.Net.CapstoneCut

/-!
# Probe C-8u (2): gcd_hw's arbiters never need unbounded arbitration time

The 8 multi-input control_merges of gcd_hw are `bd_arbiter` stages (9 `AMerge` stages: the
3-input one is a cascade of two). On this fabric no bounded arbitration time exists: when both
requests are high and no grant is held, the arbiter's decision loop can stay undecided (or
oscillate) for an unbounded time (track 7, B's digital race). So a liveness proof may assume a
delay bound for a grant ONLY when the grant is not contested.

## The hypothesis on the arbiter (named, per stage)

**H_ARB_UNCONTESTED_BOUNDED `H`** (`ArbUnc`): for each grant,
* rise: if, on a whole window `[t, t + H]`, the grant is excited to rise (its request high,
  the other grant low, `A0 = z.ack` low) AND THE OTHER REQUEST IS LOW (no contest), the grant
  is high somewhere in the window;
* fall: if its request is low on the whole window, the grant is low somewhere in it (a
  release is never contested).

It says nothing about a contested window: there the grant may stay low forever. It is the
bounded-delay hypothesis of the grant LUTs restricted to the one-request case, where the
arbiter is an ordinary combinational path (B's `gr1_eq`/`gr2_eq` at settled `q`).

**The full law `ArbSettle H`** is the same with the "other request low" premise dropped: the
grant then behaves like a bounded-delay gate even under contest. That is what a progress
argument needs (`arb_frozen_quiet`), and it is FALSE for a bare arbiter: `stall_*` below is a
trace meeting the cell model `CM.AMerge` and H_ARB_UNCONTESTED_BOUNDED in which both requests
stay high and no grant ever rises.

## Results

* `settle_of_uncontended`: on any arbiter stage where "both requests high → a grant is held"
  (no free contention), H_ARB_UNCONTESTED_BOUNDED implies the full law `ArbSettle`.
* `gcd_hw_never_contested`: in every gcd_hw circuit run meeting H_CELLS, H_BUNDLE,
  H_START_ONCE and H_WALK, no arbiter stage is ever in the contested state (both requests
  high, no grant held). This is 8q/8r's `gcd_hw_arbiters_uncontended'`, restated.
* **`gcd_hw_arb_settle`**: under the same hypotheses plus H_ARB_UNCONTESTED_BOUNDED `H` at a
  stage, that stage's grants obey the full bounded law `ArbSettle H`: every arbitration in
  gcd_hw completes within `H`, with no metastability-resolution bound assumed.
* `arb_frozen_quiet`: under `ArbSettle H`, an arbiter whose ports and grants do not move for
  `H + 1` ticks has no excited grant: the arbiter's share of `CapstoneLiveRank`'s
  H_FROZEN_QUIET.
* Negative control `stall_cell`, `stall_unc`, `stall_not_settle`: H_ARB_UNCONTESTED_BOUNDED
  alone does not bound a contest, so 8r's "no free contention" is a necessary input.

What this does NOT show: that the circuit as a whole makes progress (H_NO_DEADLOCK) or that
it latches out0 within a bound. See `formal/notes/C-8u-live.md`.
-/

namespace Formal.Net.CapNet.Live
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe (Good)

/-- Grant 1's rise excitation: `r1` high, `g2` low, `A0` low (H_ARB1's guard). -/
def ex1 (x z : Chan) (g2 : Trace) (t : Nat) : Bool := x.req t && !g2 t && !z.ack t
/-- Grant 2's rise excitation. -/
def ex2 (y z : Chan) (g1 : Trace) (t : Nat) : Bool := y.req t && !g1 t && !z.ack t

/-- `p` holds on the whole window `[t, t + H]`. -/
def Win (H t : Nat) (p : Nat → Prop) : Prop := ∀ u, t ≤ u → u ≤ t + H → p u
/-- `p` holds somewhere in `[t, t + H]`. -/
def Ev (H t : Nat) (p : Nat → Prop) : Prop := ∃ u, t ≤ u ∧ u ≤ t + H ∧ p u

/-- The contested state: both requests high, no grant held. Only here would the arbiter
need to arbitrate, and only here is its decision time unbounded on this fabric. -/
def Contested (x y : Chan) (g1 g2 : Trace) (t : Nat) : Prop :=
  x.req t = true ∧ y.req t = true ∧ g1 t = false ∧ g2 t = false

/-- **H_ARB_UNCONTESTED_BOUNDED `H`**: the grants settle within `H` when not contested. -/
structure ArbUnc (H : Nat) (x y z : Chan) (g1 g2 : Trace) : Prop where
  rise1 : ∀ t, Win H t (fun u => ex1 x z g2 u = true ∧ y.req u = false) → Ev H t (fun u => g1 u = true)
  rise2 : ∀ t, Win H t (fun u => ex2 y z g1 u = true ∧ x.req u = false) → Ev H t (fun u => g2 u = true)
  fall1 : ∀ t, Win H t (fun u => x.req u = false) → Ev H t (fun u => g1 u = false)
  fall2 : ∀ t, Win H t (fun u => y.req u = false) → Ev H t (fun u => g2 u = false)

/-- The full bounded law: the grants settle within `H` whenever excited, contest or not. -/
structure ArbSettle (H : Nat) (x y z : Chan) (g1 g2 : Trace) : Prop where
  rise1 : ∀ t, Win H t (fun u => ex1 x z g2 u = true) → Ev H t (fun u => g1 u = true)
  rise2 : ∀ t, Win H t (fun u => ex2 y z g1 u = true) → Ev H t (fun u => g2 u = true)
  fall1 : ∀ t, Win H t (fun u => x.req u = false) → Ev H t (fun u => g1 u = false)
  fall2 : ∀ t, Win H t (fun u => y.req u = false) → Ev H t (fun u => g2 u = false)

/-- **No contest ⇒ bounded arbitration.** If both requests are never high with no grant
held, the uncontested bound is the full bound. -/
theorem settle_of_uncontended {H : Nat} {x y z : Chan} {g1 g2 : Trace}
    (hU : ∀ t, x.req t = true → y.req t = true → g1 t = true ∨ g2 t = true)
    (hB : ArbUnc H x y z g1 g2) : ArbSettle H x y z g1 g2 where
  rise1 t hw := by
    apply Classical.byContradiction
    intro hno
    apply hno
    apply hB.rise1 t
    intro u h1 h2
    refine ⟨hw u h1 h2, ?_⟩
    have he := hw u h1 h2
    simp only [ex1, Bool.and_eq_true, Bool.not_eq_true'] at he
    cases hy : y.req u
    · rfl
    · rcases hU u he.1.1 hy with g | g
      · exact absurd ⟨u, h1, h2, g⟩ hno
      · rw [he.1.2] at g; cases g
  rise2 t hw := by
    apply Classical.byContradiction
    intro hno
    apply hno
    apply hB.rise2 t
    intro u h1 h2
    refine ⟨hw u h1 h2, ?_⟩
    have he := hw u h1 h2
    simp only [ex2, Bool.and_eq_true, Bool.not_eq_true'] at he
    cases hx : x.req u
    · rfl
    · rcases hU u hx he.1.1 with g | g
      · rw [he.1.2] at g; cases g
      · exact absurd ⟨u, h1, h2, g⟩ hno
  fall1 := hB.fall1
  fall2 := hB.fall2

/-- No-contention, as a statement about the contested state. -/
theorem never_contested_iff {x y : Chan} {g1 g2 : Trace} :
    (∀ t, x.req t = true → y.req t = true → g1 t = true ∨ g2 t = true) ↔
      ∀ t, ¬ Contested x y g1 g2 t := by
  constructor
  · rintro h t ⟨hx, hy, h1, h2⟩
    rcases h t hx hy with g | g
    · rw [h1] at g; cases g
    · rw [h2] at g; cases g
  · intro h t hx hy
    cases h1 : g1 t
    · cases h2 : g2 t
      · exact absurd ⟨hx, hy, h1, h2⟩ (h t)
      · exact Or.inr rfl
    · exact Or.inl rfl

/-- **The arbiter's share of H_FROZEN_QUIET.** Under the full law, an arbiter whose ports
and grants do not move on `[t, t + H]` has no excited grant at `t`. -/
theorem arb_frozen_quiet {H : Nat} {x y z : Chan} {g1 g2 : Trace} (hS : ArbSettle H x y z g1 g2)
    {t : Nat}
    (hfz : Win H t (fun u => g1 u = g1 t ∧ g2 u = g2 t ∧ x.req u = x.req t ∧ y.req u = y.req t ∧
      z.ack u = z.ack t)) :
    (ex1 x z g2 t = true → g1 t = true) ∧ (ex2 y z g1 t = true → g2 t = true) ∧
    (x.req t = false → g1 t = false) ∧ (y.req t = false → g2 t = false) := by
  refine ⟨fun he => ?_, fun he => ?_, fun hr => ?_, fun hr => ?_⟩
  · obtain ⟨u, h1, h2, g⟩ := hS.rise1 t (fun u h1 h2 => by
      obtain ⟨a1, a2, a3, a4, a5⟩ := hfz u h1 h2
      simp only [ex1] at he ⊢; rw [a2, a3, a5]; exact he)
    rw [(hfz u h1 h2).1] at g; exact g
  · obtain ⟨u, h1, h2, g⟩ := hS.rise2 t (fun u h1 h2 => by
      obtain ⟨a1, a2, a3, a4, a5⟩ := hfz u h1 h2
      simp only [ex2] at he ⊢; rw [a1, a4, a5]; exact he)
    rw [(hfz u h1 h2).2.1] at g; exact g
  · obtain ⟨u, h1, h2, g⟩ := hS.fall1 t (fun u h1 h2 => by show (x.req u = false); rw [(hfz u h1 h2).2.2.1]; exact hr)
    rw [(hfz u h1 h2).1] at g; exact g
  · obtain ⟨u, h1, h2, g⟩ := hS.fall2 t (fun u h1 h2 => by show (y.req u = false); rw [(hfz u h1 h2).2.2.2.1]; exact hr)
    rw [(hfz u h1 h2).2.1] at g; exact g

/-! ## gcd_hw -/

/-- **No gcd_hw arbiter stage is ever contested** (8q/8r restated). -/
theorem gcd_hw_never_contested (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1)
    (y : CapSafe.TS) (hy : Good a b y) (H_WALK : WalkOK (σY a b y) (omOf a b y))
    (o : Fin NO) (x u z : Fin NC) (w : Nat) (ho : opAt o = .amerge x u z w)
    (g1 g2 : Trace) (M : CM.AMerge (ch x) (ch u) (ch z) g1 g2) :
    ∀ t, ¬ Contested (ch x) (ch u) g1 g2 t :=
  never_contested_iff.mp
    (gcd_hw_arbiters_uncontended' a b ch H_CELLS H_BUNDLE H_START_ONCE y hy H_WALK o x u z w ho g1 g2 M)

/-- **Every gcd_hw arbitration completes within `H`.** Under H_CELLS, H_BUNDLE,
H_START_ONCE, H_WALK and H_ARB_UNCONTESTED_BOUNDED `H` at an arbiter stage, the stage's
grants obey the full bounded law: no unbounded arbitration (metastability resolution) time
is ever needed in gcd_hw. -/
theorem gcd_hw_arb_settle (a b H : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1)
    (y : CapSafe.TS) (hy : Good a b y) (H_WALK : WalkOK (σY a b y) (omOf a b y))
    (o : Fin NO) (x u z : Fin NC) (w : Nat) (ho : opAt o = .amerge x u z w)
    (g1 g2 : Trace) (M : CM.AMerge (ch x) (ch u) (ch z) g1 g2)
    (H_ARB_UNCONTESTED_BOUNDED : ArbUnc H (ch x) (ch u) (ch z) g1 g2) :
    ArbSettle H (ch x) (ch u) (ch z) g1 g2 :=
  settle_of_uncontended
    (gcd_hw_arbiters_uncontended' a b ch H_CELLS H_BUNDLE H_START_ONCE y hy H_WALK o x u z w ho g1 g2 M)
    H_ARB_UNCONTESTED_BOUNDED

/-! ## Negative control: a contest stalls forever under the cell model and the uncontested
bound -/

/-- Request high from tick 1 on. -/
def rq : Trace := fun t => decide (1 ≤ t)
def sx : Chan := ⟨rq, fun _ => false, fun _ => 0⟩
def sy : Chan := ⟨rq, fun _ => false, fun _ => 0⟩
def sz : Chan := ⟨fun _ => false, fun _ => false, fun _ => 0⟩
def gq : Trace := fun _ => false

/-- The stalled run meets the arbiter-merge cell model. -/
theorem stall_cell : CM.AMerge sx sy sz gq gq where
  H_ARB1 t h := absurd rfl h
  H_ARB2 t h := absurd rfl h
  H_ARB_EXCL t := rfl
  zr t h := absurd rfl h
  H_AMERGE_RTZ t h1 h2 := by simp [sz] at h2
  xa t h := absurd rfl h
  ya t h := absurd rfl h
  dat t := rfl
  i1 := rfl
  i2 := rfl
  iz := rfl
  ix := rfl
  iy := rfl

/-- It meets H_ARB_UNCONTESTED_BOUNDED for every `H` (a rise window always meets tick 0,
where the request is low, or a tick where the other request is high). -/
theorem stall_unc (H : Nat) : ArbUnc H sx sy sz gq gq where
  rise1 t hw := by
    by_cases h0 : t = 0
    · subst h0; have := (hw 0 (Nat.le_refl _) (by omega)).1; simp [ex1, sx, rq] at this
    · have := (hw t (Nat.le_refl _) (by omega)).2; simp [sy, rq] at this; omega
  rise2 t hw := by
    by_cases h0 : t = 0
    · subst h0; have := (hw 0 (Nat.le_refl _) (by omega)).1; simp [ex2, sy, rq] at this
    · have := (hw t (Nat.le_refl _) (by omega)).2; simp [sx, rq] at this; omega
  fall1 t _ := ⟨t, Nat.le_refl _, by omega, rfl⟩
  fall2 t _ := ⟨t, Nat.le_refl _, by omega, rfl⟩

/-- It is contested at every tick from 1 on, and violates the full law for every `H`. -/
theorem stall_contested (t : Nat) (ht : 1 ≤ t) : Contested sx sy gq gq t := by
  simp [Contested, sx, sy, rq, gq]; omega

theorem stall_not_settle (H : Nat) : ¬ ArbSettle H sx sy sz gq gq := by
  intro hS
  obtain ⟨u, _, _, g⟩ := hS.rise1 1 (fun u h1 _ => by simp [ex1, sx, sz, rq, gq]; omega)
  simp [gq] at g

end Formal.Net.CapNet.Live
