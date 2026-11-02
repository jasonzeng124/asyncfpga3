import Formal.Timing.SpecChain

/-!
# Settle windows and storage loops on the collapsed relation (shard C)

**Problem, plainly.** After `SpecChain`/`CViewPS`, every logic gate of THE target is a
`CGateOK` gate: pin `i` reads a source node through a composite delay that is a sum of
admissible arc delays. A storage node (C-element, latch, arbiter state) is such a gate whose
feedback pin's source is its own output, the loop delay being the sum over the routed loop.
What does the relation alone guarantee about (a) a gate whose inputs are stable, and (b) a
storage node whose other inputs CONFIRM its value?

**Proved** (sane parameters, corner `c ∈ [0,1]`, arcs ordered):
* `sumAdm_bounds`: a composite delay lies in `[Σ dmin, Σ dmax]` of its arcs.
* `cgate_stable`: inputs stable on `[S i, U i]` ⇒ output = INIT at those values on
  `[max(S, S i + Σdmax i), min(U i + Σdmin i)]` (the collapsed analogue of `gate_stable`).
* `cgate_hold`: feedback pin `j` reads the gate's own output, with loop delay at least 1 ps
  (`1 ≤ Σ dmin`); the other pins hold values `v` on their windows; INIT at `(v, q)` is `q`
  (the pins confirm `q`); the output is `q` on `[T0 - Σdmax_j, T0)`. Then the output stays `q`
  on all of `[T0, E]`, for any `E` within every confirming pin's window. Proof by strong
  induction on time: each feedback read falls in the primed segment or an earlier instant.

**Not shown.** How the primed segment arises (a forcing phase: `cgate_stable` with values
that force `q` whatever the feedback is, held for at least the loop's `Σ dmax`; B's
`fb_switch` side condition); what happens when the confirming pins change (a new episode).
-/

namespace Formal.Timing.SpecLoop
open Formal.Target Formal.Timing.SpecSettle Formal.Timing.SpecChain

def sumMax (p : DelayPar) (es : List Arc) : Nat := (es.map (dmax p)).sum
def sumMin (p : DelayPar) (es : List Arc) : Nat := (es.map (dmin p)).sum

/-- Every arc ordered (`fmin ≤ smin`, `fmax ≤ smax`). -/
def ArcsOrd (es : List Arc) : Prop := ∀ e ∈ es, e.fmin ≤ e.smin ∧ e.fmax ≤ e.smax

theorem sumAdm_bounds {p : DelayPar} {c : ℚ} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∀ (es : List Arc) (D : Nat), ArcsOrd es → SumAdm p c es D → sumMin p es ≤ D ∧ D ≤ sumMax p es
  | [], D, _, h => by simp [SumAdm] at h; simp [sumMin, sumMax, h]
  | e :: es, D, ho, ⟨d, hd, hle, hr⟩ => by
    have he := ho e List.mem_cons_self
    have h1 := adm_le_dmax hp hc0 hc1 he.2 hd
    have h2 := dmin_le_adm hp hc0 hc1 he.1 hd
    obtain ⟨r1, r2⟩ := sumAdm_bounds hp hc0 hc1 es (D - d) (fun e' h' => ho e' (List.mem_cons_of_mem _ h')) hr
    simp only [sumMin, sumMax, List.map_cons, List.sum_cons] at r1 r2 ⊢
    omega

/-- **Settle window of a collapsed gate.** -/
theorem cgate_stable {p : DelayPar} {c : ℚ} {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc} {S : Nat}
    {x : Beh} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hord : ∀ i, i < g.k → ArcsOrd (arcs i))
    (hg : CGateOK p c g src arcs S x) (Si Ui : Nat → Nat) (v : Nat → Bool)
    (hin : ∀ i, i < g.k → ∀ t, Si i ≤ t → t ≤ Ui i → x (src i) t = v i) :
    ∀ t, S ≤ t → (∀ i, i < g.k → Si i + sumMax p (arcs i) ≤ t ∧ t ≤ Ui i + sumMin p (arcs i)) →
      x g.out t = g.init.testBit (addr g.k v) := by
  obtain ⟨F, -, hF⟩ := hg
  intro t ht hw
  obtain ⟨hr, ho⟩ := hF t ht
  rw [ho]; congr 1
  apply SpecSettle.addr_congr
  intro i hi
  obtain ⟨h1, h2⟩ := hr i hi
  obtain ⟨b1, b2⟩ := sumAdm_bounds hp hc0 hc1 _ _ (hord i hi) h2
  obtain ⟨w1, w2⟩ := hw i hi
  exact hin i hi (F i t) (by omega) (by omega)

/-- **A storage node holds a confirmed value through its routed loop.** -/
theorem cgate_hold {p : DelayPar} {c : ℚ} {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc} {S : Nat}
    {x : Beh} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hord : ∀ i, i < g.k → ArcsOrd (arcs i))
    (hg : CGateOK p c g src arcs S x) {j : Nat} (hj : j < g.k) (hfb : src j = g.out)
    (hlo : 1 ≤ sumMin p (arcs j))
    (Si Ui : Nat → Nat) (v : Nat → Bool) (q : Bool)
    (hin : ∀ i, i < g.k → i ≠ j → ∀ t, Si i ≤ t → t ≤ Ui i → x (src i) t = v i)
    (hconf : g.init.testBit (addr g.k fun i => if i = j then q else v i) = q)
    (T0 E : Nat) (hS : S ≤ T0)
    (hw : ∀ i, i < g.k → i ≠ j → Si i + sumMax p (arcs i) ≤ T0 ∧ E ≤ Ui i + sumMin p (arcs i))
    (hprime : ∀ t, T0 - sumMax p (arcs j) ≤ t → t < T0 → x g.out t = q) :
    ∀ t, T0 ≤ t → t ≤ E → x g.out t = q := by
  obtain ⟨F, -, hF⟩ := hg
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro h1 h2
    obtain ⟨hr, ho⟩ := hF t (by omega)
    rw [ho, ← hconf]; congr 1
    apply SpecSettle.addr_congr
    intro i hi
    obtain ⟨r1, r2⟩ := hr i hi
    obtain ⟨b1, b2⟩ := sumAdm_bounds hp hc0 hc1 _ _ (hord i hi) r2
    by_cases e : i = j
    · subst e
      simp only [ite_true]
      rw [hfb]
      by_cases hlt : F i t < T0
      · exact hprime _ (by omega) hlt
      · exact ih (F i t) (by omega) (by omega) (by omega)
    · simp only [e, ite_false]
      obtain ⟨w1, w2⟩ := hw i hi e
      exact hin i hi e (F i t) (by omega) (by omega)

end Formal.Timing.SpecLoop
