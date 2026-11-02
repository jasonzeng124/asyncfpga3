import Formal.Timing.SpecSettle
import Formal.Cells.SpecFb
import Formal.Cells.Ua1Static

/-!
# Copy chains collapse: a logic gate reads its source through the routing, with the summed delay (shard C)

**Problem, plainly.** In the decoded netlist of THE target every routing pip, wire and site
hop is a one-pin copy gate (`k = 1`, INIT `0b10`), so a LUT pin reaches the LUT output that
drives it through a chain of 4-13 copy gates (a C-element's own feedback, too). Cell-level
reasoning (S3/S4) wants "pin `i` of this LUT reads node `s` with some delay", not 187k nodes.
Is that sound in the Spec's semantics, where each copy gate has its own read time and its own
admissible delay?

**Proved** (`Spec.GateOK` for every gate, sane parameters, one corner `c ∈ [0,1]`):
* `copy_read`: a copy gate's output at `t` is its input at the read time `f t`.
* `chain_read`: along a chain of copy gates from `u` to `v` (`chainOK`), there is ONE
  non-decreasing read time `F` with `x v t = x u (F t)` and `t - F t` a sum of one admissible
  delay per chain arc, at the same corner (`SumAdm`), from `chainStart` on. Transport,
  inertial (a read time that jumps) and glitch behaviour of the chain are all kept: the
  collapsed read is just the composition of the individual reads.
* `collapse`: a gate whose pins read through such chains satisfies the same kind of relation
  as `GateOK` with sources in place of pin nodes and summed delays (`CGateOK`): per-pin
  monotone reads, each composite delay a sum of admissible arc delays (pin arc first), output
  = INIT at the reads, from `g.start + Σ (chainStart + dmax)` on.
* `collapse_net`: the same for every gate of a well-formed netlist in every `Behaves`
  behaviour, given per-pin chains as gate lists of the netlist.

**Not shown.** Which chains the target has (that is data: a generator plus a check on
`DecodedPS.net`, not done here); anything about a node with several readers beyond what each
reader's own chain says (each read is collapsed separately: two readers of one net may see
it at different delays, as the fabric allows). Before the stated start time nothing is said
(power-up).
-/

namespace Formal.Timing.SpecChain
open Formal.Target Formal.Timing.SpecSettle

/-- `D` is a sum of one admissible delay per arc of `es` (all at corner `c`). -/
def SumAdm (p : DelayPar) (c : ℚ) : List Arc → Nat → Prop
  | [], D => D = 0
  | e :: es, D => ∃ d, Adm p c e d ∧ d ≤ D ∧ SumAdm p c es (D - d)

/-- The pin-0 arc of a gate. -/
abbrev arc0 (g : Gate) : Arc := g.arcs.getD 0 default

/-- A chain of copy gates ending at node `v` and starting from node `u`, listed from `v`
backwards: the head drives `v`, each gate reads the next one's output, the last reads `u`. -/
def chainOK : Nat → List Gate → Nat → Bool
  | v, [], u => v == u
  | v, c :: cs, u => c.k == 1 && c.init == 2 && c.out == v && chainOK (c.ins.getD 0 0) cs u

/-- From when the collapsed read of a chain is guaranteed. -/
def chainStart (p : DelayPar) : List Gate → Nat
  | [] => 0
  | c :: cs => c.start p + dmax p (arc0 c) + chainStart p cs

theorem addr_one (v : Nat → Bool) : addr 1 v = if v 0 then 1 else 0 := by
  simp [addr]

theorem copy_read {p : DelayPar} {c : ℚ} {g : Gate} {x : Beh} (hg : GateOK p c g x)
    (hk : g.k = 1) (hi : g.init = 2) :
    ∃ f : Nat → Nat, Monotone f ∧ ∀ t, g.start p ≤ t →
      f t ≤ t ∧ Adm p c (arc0 g) (t - f t) ∧ x g.out t = x (g.ins.getD 0 0) (f t) := by
  obtain ⟨f, hm, hf⟩ := hg
  refine ⟨f 0, hm 0 (by omega), fun t ht => ?_⟩
  obtain ⟨hr, ho⟩ := hf t ht
  obtain ⟨h1, h2⟩ := hr 0 (by omega)
  refine ⟨h1, h2, ?_⟩
  rw [ho, hk, hi, addr_one]
  cases x (g.ins.getD 0 0) (f 0 t) <;> decide

theorem chain_read {p : DelayPar} {c : ℚ} {x : Beh} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∀ (cs : List Gate) (v u : Nat), chainOK v cs u = true →
      (∀ g ∈ cs, GateOK p c g x ∧ ArcsOK g) →
      ∃ F : Nat → Nat, Monotone F ∧ ∀ t, chainStart p cs ≤ t →
        F t ≤ t ∧ SumAdm p c (cs.map arc0) (t - F t) ∧ x v t = x u (F t)
  | [], v, u, h, _ => by
    simp only [chainOK, beq_iff_eq] at h
    subst h
    exact ⟨id, monotone_id, fun t _ => ⟨Nat.le_refl _, by simp [SumAdm], rfl⟩⟩
  | g :: cs, v, u, h, hall => by
    simp only [chainOK, Bool.and_eq_true, beq_iff_eq] at h
    obtain ⟨⟨⟨hk, hi⟩, hv⟩, hrest⟩ := h
    obtain ⟨hg, harc⟩ := hall g List.mem_cons_self
    obtain ⟨f, hfm, hf⟩ := copy_read hg hk hi
    obtain ⟨F, hFm, hF⟩ := chain_read hp hc0 hc1 cs _ u hrest (fun g' h' => hall g' (List.mem_cons_of_mem _ h'))
    refine ⟨F ∘ f, hFm.comp hfm, fun t ht => ?_⟩
    simp only [chainStart] at ht
    obtain ⟨h1, h2, h3⟩ := hf t (by omega)
    have hd : t - f t ≤ dmax p (arc0 g) := adm_le_dmax hp hc0 hc1 (harc 0).2 h2
    obtain ⟨g1, g2, g3⟩ := hF (f t) (by omega)
    refine ⟨by simp only [Function.comp]; omega, ?_, ?_⟩
    · simp only [List.map_cons, SumAdm, Function.comp]
      exact ⟨t - f t, h2, by omega, by rwa [show t - F (f t) - (t - f t) = f t - F (f t) by omega]⟩
    · rw [← hv, h3, g3]; rfl

/-- The collapsed gate relation: pin `i` reads `src i` at `F i t`; the composite delay is a
sum of admissible delays over `arcs i` (all at corner `c`); output = INIT at the reads. -/
def CGateOK (p : DelayPar) (c : ℚ) (g : Gate) (src : Nat → Nat) (arcs : Nat → List Arc) (S : Nat)
    (x : Beh) : Prop :=
  ∃ F : Nat → Nat → Nat,
    (∀ i, i < g.k → Monotone (F i)) ∧
    ∀ t, S ≤ t →
      (∀ i, i < g.k → F i t ≤ t ∧ SumAdm p c (arcs i) (t - F i t)) ∧
      x g.out t = g.init.testBit (addr g.k fun i => x (src i) (F i t))

/-- A pin's chain: its source node and the copy gates from the pin node back to it. -/
structure PinChain where
  src : Nat
  chain : List Gate

/-- The composite arcs of pin `i`: the gate's own pin arc, then the chain's arcs. -/
def pinArcs (g : Gate) (pcs : List PinChain) (i : Nat) : List Arc :=
  g.arcs.getD i default :: ((pcs.getD i ⟨0, []⟩).chain.map arc0)

/-- From when the collapsed relation of `g` is guaranteed. -/
def cStart (p : DelayPar) (g : Gate) (pcs : List PinChain) : Nat :=
  g.start p + ((List.range g.k).map fun i =>
    chainStart p (pcs.getD i ⟨0, []⟩).chain + dmax p (g.arcs.getD i default)).sum

/-- The per-gate check: every pin's chain leads from the pin node back to its source. -/
def pinsOK (g : Gate) (pcs : List PinChain) : Bool :=
  (List.range g.k).all fun i => chainOK (g.ins.getD i 0) (pcs.getD i ⟨0, []⟩).chain (pcs.getD i ⟨0, []⟩).src

theorem le_sum_range (k : Nat) (h : Nat → Nat) {i : Nat} (hi : i < k) :
    h i ≤ ((List.range k).map h).sum := by
  induction k with
  | zero => omega
  | succ k ih =>
    rw [List.range_succ, List.map_append, List.sum_append]
    by_cases e : i = k
    · subst e; simp
    · have := ih (by omega); omega

theorem collapse {p : DelayPar} {c : ℚ} {x : Beh} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    {g : Gate} (hg : GateOK p c g x) (harc : ArcsOK g) (pcs : List PinChain) (hpins : pinsOK g pcs = true)
    (hch : ∀ i, i < g.k → ∀ g' ∈ (pcs.getD i ⟨0, []⟩).chain, GateOK p c g' x ∧ ArcsOK g') :
    CGateOK p c g (fun i => (pcs.getD i ⟨0, []⟩).src) (pinArcs g pcs) (cStart p g pcs) x := by
  have hc : ∀ i, i < g.k → ∃ F : Nat → Nat, Monotone F ∧
      ∀ t, chainStart p (pcs.getD i ⟨0, []⟩).chain ≤ t →
        F t ≤ t ∧ SumAdm p c ((pcs.getD i ⟨0, []⟩).chain.map arc0) (t - F t) ∧
        x (g.ins.getD i 0) t = x (pcs.getD i ⟨0, []⟩).src (F t) := by
    intro i hi
    have hok : chainOK (g.ins.getD i 0) (pcs.getD i ⟨0, []⟩).chain (pcs.getD i ⟨0, []⟩).src = true := by
      simp only [pinsOK, List.all_eq_true, List.mem_range] at hpins; exact hpins i hi
    exact chain_read hp hc0 hc1 _ _ _ hok (hch i hi)
  choose! Fc hFm hF using hc
  obtain ⟨f, hfm, hf⟩ := hg
  refine ⟨fun i => Fc i ∘ f i, fun i hi => (hFm i hi).comp (hfm i hi), fun t ht => ?_⟩
  have hst : g.start p ≤ t := by unfold cStart at ht; omega
  obtain ⟨hr, ho⟩ := hf t hst
  have hbig : ∀ i, i < g.k → chainStart p (pcs.getD i ⟨0, []⟩).chain + dmax p (g.arcs.getD i default) ≤
      t - g.start p := by
    intro i hi
    have := le_sum_range g.k (fun i => chainStart p (pcs.getD i ⟨0, []⟩).chain +
      dmax p (g.arcs.getD i default)) hi
    unfold cStart at ht; omega
  have hpin : ∀ i, i < g.k → chainStart p (pcs.getD i ⟨0, []⟩).chain ≤ f i t := by
    intro i hi
    obtain ⟨h1, h2⟩ := hr i hi
    have hd : t - f i t ≤ dmax p (g.arcs.getD i default) := adm_le_dmax hp hc0 hc1 (harc i).2 h2
    have := hbig i hi
    omega
  refine ⟨fun i hi => ?_, ?_⟩
  · obtain ⟨h1, h2⟩ := hr i hi
    obtain ⟨g1, g2, -⟩ := hF i hi (f i t) (hpin i hi)
    refine ⟨by simp only [Function.comp]; omega, ?_⟩
    simp only [pinArcs, SumAdm, Function.comp]
    exact ⟨t - f i t, h2, by omega, by rwa [show t - Fc i (f i t) - (t - f i t) = f i t - Fc i (f i t) by omega]⟩
  · rw [ho]
    congr 1
    apply addr_congr
    intro i hi
    obtain ⟨-, -, g3⟩ := hF i hi (f i t) (hpin i hi)
    simp only [Function.comp]
    exact g3

/-- **On a netlist.** In every behaviour of a well-formed netlist, every listed gate with
checked pin chains made of the netlist's gates satisfies the collapsed relation, at the one
corner of the behaviour. -/
theorem collapse_net {p : DelayPar} {N : Net} {x : Beh} (hp : Sane p) (hN : N.WF) (hb : Behaves p N x)
    (L : List (Gate × List PinChain))
    (hL : ∀ e ∈ L, e.1 ∈ N.gates ∧ pinsOK e.1 e.2 = true ∧
      ∀ i, i < e.1.k → ∀ g' ∈ (e.2.getD i ⟨0, []⟩).chain, g' ∈ N.gates) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ e ∈ L,
      CGateOK p c e.1 (fun i => (e.2.getD i ⟨0, []⟩).src) (pinArcs e.1 e.2) (cStart p e.1 e.2) x := by
  obtain ⟨c, hc0, hc1, hall⟩ := hb
  refine ⟨c, hc0, hc1, fun e he => ?_⟩
  obtain ⟨hg, hpins, hch⟩ := hL e he
  exact collapse hp hc0 hc1 (hall _ hg) (arcsOK_of_wf hN hg) e.2 hpins
    (fun i hi g' hg' => ⟨hall g' (hch i hi g' hg'), arcsOK_of_wf hN (hch i hi g' hg')⟩)

end Formal.Timing.SpecChain

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
#print axioms Formal.Cells.SpecFbChain.creads_visible
#print axioms Formal.Cells.SpecFbChain.cfb_forced
#print axioms Formal.Cells.SpecFbChain.cfb_stays
#print axioms Formal.Cells.SpecFbChain.cfb_switch
#print axioms Formal.Cells.SpecFbChain.adm_lo
#print axioms Formal.Cells.SpecFbChain.adm_hi
#print axioms Formal.Cells.SpecFbChain.sumAdm_bounds
#print axioms Formal.Cells.SpecFbChain.cbands_of_sums
