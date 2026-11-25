import Formal.Cells.SpecFb
import Formal.Cells.Ua1Static
import Formal.Timing.SpecChain

/-!
# Formal.Cells.SpecFbChain — a feedback LUT whose loop runs through the routing (frozen Spec semantics)

Shard B, THE goal, S3.

## Problem, plainly
`SpecFb.fb_switch` (a storage LUT switches cleanly when its set condition lasts at least its feedback
delay) assumes the feedback pin reads the LUT's own output node directly. On the decoded targets every
feedback goes through a route of 4-13 copy gates (pips, wires, site hops), each with its own read time and
admissible delay. Does the clean-switch rule still hold, with the feedback delay replaced by the summed
delay of the route plus the pin arc? And are the integer window ends that B's static race margins use
(`Ua1Static.lo/hi`, summed over arc lists in `Ua1Static`, `RaceStaticPS`) sound bounds on every admissible
summed delay?

## Results
* `cfb_forced`, `cfb_stays`, `cfb_switch`: the three `SpecFb` lemmas for shard C's collapsed gate relation
  `SpecChain.CGateOK` (pins read their SOURCE nodes through copy chains, each composite delay a sum of one
  admissible delay per arc), with the feedback pin's source equal to the gate's own output. The bounds
  `lo j`, `hi j` are now bounds on the composite (route + pin) delay.
* `adm_lo`, `adm_hi`: every `Adm`-admissible delay lies in `[Ua1Static.lo, Ua1Static.hi]` (the ceiling of
  the window's lower end, the floor of its upper end).
* `sumAdm_bounds`: every composite delay `D` with `SumAdm p c es D` satisfies
  `Σ lo ≤ D ≤ Σ hi` over the arcs `es`. So `Ua1Static.loopHi`-style sums ARE upper bounds on the real
  loop delay of every behaviour, and `pathLo`-style sums lower bounds on the real path delay.
* `cbands_of_sums`: hence `CBands` holds with `lo i = Σ lo`, `hi i = Σ hi` per pin (clamped at 0), which is
  what `cfb_switch` needs.

## Not covered
That a given forcing episode lasts at least the loop's `hi` in every behaviour (that is causality through
the rest of the network: the open S3/S4 obligation); which chains the target has (data; C's `ChunkCM`
route, or a per-node generated check).
-/

namespace Formal.Cells.SpecFbChain

open Formal.Target Formal.Timing.SpecChain

/-- Nat bounds on every admissible composite delay of each pin. -/
def CBands (p : DelayPar) (c : ℚ) (k : Nat) (arcs : Nat → List Arc) (lo hi : Nat → Nat) : Prop :=
  ∀ i, i < k → ∀ D, SumAdm p c (arcs i) D → lo i ≤ D ∧ D ≤ hi i

/-- `v` is a combination of source values the composite reads can see at `t` (pin `j` excluded). -/
def CVisible (x : Beh) (k : Nat) (src : Nat → Nat) (lo hi : Nat → Nat) (j t : Nat) (v : Nat → Bool) :
    Prop :=
  ∀ i, i < k → i ≠ j → ∃ u, u + lo i ≤ t ∧ t ≤ u + hi i ∧ v i = x (src i) u

theorem creads_visible {p : DelayPar} {c : ℚ} {k : Nat} {arcs : Nat → List Arc} {src : Nat → Nat}
    {x : Beh} {lo hi : Nat → Nat} (hb : CBands p c k arcs lo hi) (F : Nat → Nat → Nat) (t j : Nat)
    (hr : ∀ i, i < k → F i t ≤ t ∧ SumAdm p c (arcs i) (t - F i t)) :
    CVisible x k src lo hi j t (fun i => x (src i) (F i t)) := by
  intro i hi' _
  have h := hr i hi'
  have hd := hb i hi' _ h.2
  exact ⟨F i t, by omega, by omega, rfl⟩

/-- **Forced value** (collapsed form). -/
theorem cfb_forced {p : DelayPar} {c : ℚ} {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc}
    {S : Nat} {x : Beh} (hg : CGateOK p c g src arcs S x) {lo hi : Nat → Nat}
    (hb : CBands p c g.k arcs lo hi) {j s e : Nat} (hs : S ≤ s) {cv : Bool}
    (hforce : ∀ t, s ≤ t → t ≤ e → ∀ v : Nat → Bool, CVisible x g.k src lo hi j t v →
      g.init.testBit (addr g.k v) = cv) :
    ∀ t, s ≤ t → t ≤ e → x g.out t = cv := by
  obtain ⟨F, _, hF⟩ := hg
  intro t hst hte
  obtain ⟨hr, hy⟩ := hF t (by omega)
  rw [hy]
  exact hforce t hst hte _ (creads_visible hb F t j hr)

/-- **Confirmed value stays** (collapsed form): the feedback pin's source is the gate's own output. -/
theorem cfb_stays {p : DelayPar} {c : ℚ} {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc}
    {S : Nat} {x : Beh} (hg : CGateOK p c g src arcs S x) {lo hi : Nat → Nat}
    (hb : CBands p c g.k arcs lo hi) {j : Nat} (hj : j < g.k) (hfb : src j = g.out) (hlo : 1 ≤ lo j)
    {s e : Nat} (hs : S ≤ s) {b : Bool}
    (hpre : ∀ t, s ≤ t + hi j → t < s → x g.out t = b)
    (hconf : ∀ t, s ≤ t → t ≤ e → ∀ v : Nat → Bool, v j = b → CVisible x g.k src lo hi j t v →
      g.init.testBit (addr g.k v) = b) :
    ∀ t, s ≤ t → t ≤ e → x g.out t = b := by
  obtain ⟨F, _, hF⟩ := hg
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro hst hte
    obtain ⟨hr, hy⟩ := hF t (by omega)
    have hj' := hr j hj
    have hd := hb j hj _ hj'.2
    have hfj : x g.out (F j t) = b := by
      by_cases hc : s ≤ F j t
      · exact ih (F j t) (by omega) hc (by omega)
      · exact hpre (F j t) (by omega) (by omega)
    rw [hy]
    apply hconf t hst hte
    · show x (src j) (F j t) = b
      rw [hfb]; exact hfj
    · exact creads_visible hb F t j hr

/-- **Clean switch through a routed feedback**: forced for at least the composite feedback delay's upper
bound (route + pin arc), then confirmed. -/
theorem cfb_switch {p : DelayPar} {c : ℚ} {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc}
    {S : Nat} {x : Beh} (hg : CGateOK p c g src arcs S x) {lo hi : Nat → Nat}
    (hb : CBands p c g.k arcs lo hi) {j : Nat} (hj : j < g.k) (hfb : src j = g.out) (hlo : 1 ≤ lo j)
    {s e e' : Nat} (hs : S ≤ s) (hlong : s + hi j ≤ e + 1) {cv : Bool}
    (hforce : ∀ t, s ≤ t → t ≤ e → ∀ v : Nat → Bool, CVisible x g.k src lo hi j t v →
      g.init.testBit (addr g.k v) = cv)
    (hconf : ∀ t, e + 1 ≤ t → t ≤ e' → ∀ v : Nat → Bool, v j = cv → CVisible x g.k src lo hi j t v →
      g.init.testBit (addr g.k v) = cv) :
    ∀ t, s ≤ t → t ≤ e' → x g.out t = cv := by
  have h1 := cfb_forced hg hb (j := j) hs hforce
  have h2 := cfb_stays hg hb hj hfb hlo (s := e + 1) (e := e') (by omega) (b := cv)
    (fun t h3 h4 => h1 t (by omega) (by omega)) hconf
  intro t hst hte
  by_cases ht : t ≤ e
  · exact h1 t hst ht
  · exact h2 t (by omega) hte

/-! ## The integer window ends are sound bounds -/

open Formal.Cells.Ua1Static (lo hi)

theorem adm_lo {p : DelayPar} {c : ℚ} {e : Arc} {d : Nat} (h : Adm p c e d) :
    lo p.g p.κ c e ≤ (d : Int) := by
  unfold lo
  rw [Rat.ceil_le_iff]
  have := h.1
  push_cast
  exact this

theorem adm_hi {p : DelayPar} {c : ℚ} {e : Arc} {d : Nat} (h : Adm p c e d) :
    (d : Int) ≤ hi p.g p.κ c e := by
  unfold hi
  rw [Rat.le_floor_iff]
  have := h.2
  push_cast
  exact this

/-- **Summed window ends bound every composite delay.** -/
theorem sumAdm_bounds {p : DelayPar} {c : ℚ} :
    ∀ (es : List Arc) (D : Nat), SumAdm p c es D →
      (es.map (lo p.g p.κ c)).sum ≤ (D : Int) ∧ (D : Int) ≤ (es.map (hi p.g p.κ c)).sum
  | [], D, h => by
    simp only [SumAdm] at h
    subst h; simp
  | e :: es, D, h => by
    obtain ⟨d, hd, hdD, hrest⟩ := h
    have ih := sumAdm_bounds es (D - d) hrest
    have h1 := adm_lo hd
    have h2 := adm_hi hd
    simp only [List.map_cons, List.sum_cons]
    constructor <;> omega

/-- **CBands from the summed window ends** (clamped at 0 for the lower end). -/
theorem cbands_of_sums {p : DelayPar} {c : ℚ} {k : Nat} (arcs : Nat → List Arc) :
    CBands p c k arcs (fun i => ((arcs i).map (lo p.g p.κ c)).sum.toNat)
      (fun i => ((arcs i).map (hi p.g p.κ c)).sum.toNat) := by
  intro i _ D hD
  have := sumAdm_bounds (arcs i) D hD
  show ((arcs i).map (lo p.g p.κ c)).sum.toNat ≤ D ∧ D ≤ ((arcs i).map (hi p.g p.κ c)).sum.toNat
  constructor <;> omega

end Formal.Cells.SpecFbChain
