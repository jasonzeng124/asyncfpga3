import Formal.Timing.SpecSettle
import Formal.Cells.ArbClean
import Formal.Cells.SpecFb
import Formal.Cells.Ua1Static
import Formal.Target.NetPS.All

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

/-!
# Formal.Cells.ArbCleanPS — the table facts of THE target gcd_ps's nine arbiter state LUTs

Shard B, THE goal (target `gcd_ps_e6bb4aec`, since 2026-11-01 19:35).

## Problem, plainly
`ArbClean.q_clean_set_gen` decides a separated arbitration from two facts about the state LUT's
table (set: r1 = 1, r2 = 0, rst = 0, A0 = 0 forces q = 1; conflict: r1 = 1, q = 1, rst = 0 keeps
q = 1). Do the nine state LUTs decoded from the gcd_ps bitstream have these facts, with the pin roles
read off their tables?

## Result
`targetQPS_facts`: yes, all nine (kernel `decide`). `targetQPS_swap_fails`: negative control.

## Not shown
The rows are GENERATED data (tools-B/target/gen_targetq.py on tools-B/target/lean2json.py output of
`Formal/Target/NetPS`); that they ARE gates of `Formal.Target.DecodedPS.net` is a separate link
(as `TargetLink` does for the previous target). The pin roles come from the generator's tracing.
Nothing about timing: separation of the two requests at each arbiter is still to be derived.
-/

namespace Formal.Cells.ArbCleanPS
open Formal.Cells.ArbClean

/-- (name, k, INIT, roles ⟨r1, r2, fb, rst, a0, tied⟩) of each gcd_ps ustate O6 gate. -/
def targetQPS : List (String × Nat × Nat × Roles) := [
  ("SLICE_X38Y51.BLUT.O6", 6, 0xffffaab2e4e4e4e4, ⟨2, 1, 0, 4, 3, [(5, true)]⟩),
  ("SLICE_X39Y24.ALUT.O6", 6, 0xffefaaaeccccf0f0, ⟨1, 2, 4, 0, 3, [(5, true)]⟩),
  ("SLICE_X16Y25.BLUT.O6", 6, 0xffffaba2ee44ee44, ⟨3, 1, 0, 4, 2, [(5, true)]⟩),
  ("SLICE_X16Y31.ALUT.O6", 6, 0xfffbf1f0ff00cccc, ⟨3, 1, 4, 2, 0, [(5, true)]⟩),
  ("SLICE_X16Y18.DLUT.O6", 6, 0xffefff02aaaaf0f0, ⟨0, 2, 4, 3, 1, [(5, true)]⟩),
  ("SLICE_X14Y18.ALUT.O6", 6, 0xffefccceaaaaf0f0, ⟨0, 2, 4, 1, 3, [(5, true)]⟩),
  ("SLICE_X14Y19.ALUT.O6", 6, 0xfcfcfddcfa0afa0a, ⟨3, 0, 2, 1, 4, [(5, true)]⟩),
  ("SLICE_X18Y24.ALUT.O6", 6, 0xfffdcdccff00aaaa, ⟨3, 0, 4, 1, 2, [(5, true)]⟩),
  ("SLICE_X39Y21.CLUT.O6", 6, 0xffabff8afafa5050, ⟨4, 2, 0, 3, 1, [(5, true)]⟩)]

/-- **All nine gcd_ps ustates meet both table facts.** -/
theorem targetQPS_facts :
    targetQPS.all (fun r => setFact r.2.1 r.2.2.1 r.2.2.2 && confFact r.2.1 r.2.2.1 r.2.2.2) = true := by
  decide +kernel

/-- Negative control: swapping r1 and r2 of the first gate breaks the set fact. -/
theorem targetQPS_swap_fails :
    setFact 6 0xffffaab2e4e4e4e4 ⟨1, 2, 0, 4, 3, [(5, true)]⟩ = false := by decide +kernel

end Formal.Cells.ArbCleanPS

/-!
# Formal.Cells.RaceStaticPS — the tightest C-element race of THE target gcd_ps, at Spec's own window ends

Shard B, THE goal, S3. GENERATED by tools-B/ps/gen_race_ps.py.

## Problem, plainly
Storage node `SLICE_X32Y45.ALUT.O6` (gate 120808 of `Formal.Target.DecodedPS.net`; the routed cell
`ulink_n_falseResult_85.many.stage[0].u.ctl.u.u`, a link controller C-element) is the node with the
smallest static race margin found by B's scan (16 rig + 16 full-width vectors, corner 0.5): its tightest
flipping episode is ended by a causal path that starts at its own output and comes back to its pin 4
(36 arcs), while its own new value comes round its feedback loop to pin 0 (7 arcs). If, with every delay
inside Spec's `Adm` window (g = 1, corner 1/2, scatter κ), the path can be faster than the loop, the node
can latch a runt (`SpecFb.fb_runt_oscillates`; seen in simulation).

## Results (decided on the generated arc data, integer ps)
* `race_holds`: at κ = 0.435 the path's smallest admissible total (1099 ps) is at least the loop's largest
  (1091 ps): fb_switch's timing premise holds for this episode under every admissible delay.
* `race_fails`: at κ = 0.44 the path's smallest total (1093 ps) is below the loop's largest (1094 ps).
Simulation with the same per-pin choice (tools-B/ps/kadv.py map): clean at κ = 0.435, runt at 0.44.

## Not covered
That the episode is ended by this path in every behaviour (causality: a network fact); that no other node
or episode binds at a smaller κ (the scan is simulation over 32 vectors, one corner); the dynamics. The
link of these arcs to `DecodedPS.net` is in `TargetLinkPS`.
-/

namespace Formal.Cells.RaceStaticPS
open Formal.Target Formal.Cells.Ua1Static

def racePath : List Arc := [⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨33, 51, 113, 147⟩, ⟨52, 74, 118, 153⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨79, 99, 193, 240⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨50, 135, 111, 209⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨131, 163, 329, 408⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨44, 63, 108, 140⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨133, 165, 329, 408⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨78, 98, 192, 238⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨79, 99, 193, 240⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨50, 71, 115, 149⟩, ⟨33, 83, 111, 176⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨83, 104, 202, 250⟩]
def raceLoop : List Arc := [⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨35, 62, 102, 142⟩, ⟨33, 51, 113, 147⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩, ⟨225, 281, 528, 655⟩]

def pathLo (g κ c : ℚ) : Int := (racePath.map (lo g κ c)).sum
def loopHi (g κ c : ℚ) : Int := (raceLoop.map (hi g κ c)).sum

theorem race_holds : loopHi 1 (87/200) (1/2) ≤ pathLo 1 (87/200) (1/2) := by decide +kernel
theorem race_fails : pathLo 1 (11/25) (1/2) < loopHi 1 (11/25) (1/2) := by decide +kernel
theorem race_numbers : pathLo 1 (87/200) (1/2) = 1099 ∧ loopHi 1 (87/200) (1/2) = 1091 ∧
    pathLo 1 (11/25) (1/2) = 1093 ∧ loopHi 1 (11/25) (1/2) = 1094 := by decide +kernel

end Formal.Cells.RaceStaticPS

/-!
# Formal.Cells.TargetLinkPS — B's gcd_ps data, tied to shard A's Lean netlist (GENERATED by tools-B/ps/gen_race_ps.py)

`ArbCleanPS.targetQPS` (the nine ustates' names, tables, pin counts) and `RaceStaticPS.racePath`/`raceLoop` were
generated from a JSON rebuild of `Formal/Target/NetPS`. Here each is proved equal to the corresponding gate or arc
of `Formal.Target.DecodedPS.net`, and the path and loop are shown wired as claimed, so `targetQPS_facts` and
`race_holds`/`race_fails` are statements about the netlist THE theorem is about. Not re-derived: the roles of the
ustate pins (generator's table analysis; `targetQPS_facts` checks the facts they are used for).
-/

namespace Formal.Cells.TargetLinkPS

open Formal.Target Formal.Target.DecodedPS

/-- Gate `i` of the decoded gcd_ps netlist. -/
def gate (i : Nat) : Gate := net.gates.getD i default

theorem getD_skip {α : Type} (l1 l2 : List α) (h : l1.length = 2500) (i : Nat) (d : α) :
    (l1 ++ l2).getD (i + 2500) d = l2.getD i d := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_right (by omega)]
  congr 2; omega

theorem getD_left {α : Type} (l1 l2 : List α) (i : Nat) (hi : i < l1.length) (d : α) :
    (l1 ++ l2).getD i d = l1.getD i d := by
  simp only [List.getD_eq_getElem?_getD]
  rw [List.getElem?_append_left hi]

theorem gate_28304 : gate 28304 = (g011).getD 804 default := by
  show gates.getD (804 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len]
  rw [getD_left _ _ _ (by rw [g011_len]; omega)]

theorem gate_28366 : gate 28366 = (g011).getD 866 default := by
  show gates.getD (866 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len]
  rw [getD_left _ _ _ (by rw [g011_len]; omega)]

theorem gate_37325 : gate 37325 = (g014).getD 2325 default := by
  show gates.getD (2325 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len]
  rw [getD_left _ _ _ (by rw [g014_len]; omega)]

theorem gate_37766 : gate 37766 = (g015).getD 266 default := by
  show gates.getD (266 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len]
  rw [getD_left _ _ _ (by rw [g015_len]; omega)]

theorem gate_37978 : gate 37978 = (g015).getD 478 default := by
  show gates.getD (478 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len]
  rw [getD_left _ _ _ (by rw [g015_len]; omega)]

theorem gate_47283 : gate 47283 = (g018).getD 2283 default := by
  show gates.getD (2283 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len]
  rw [getD_left _ _ _ (by rw [g018_len]; omega)]

theorem gate_120675 : gate 120675 = (g048).getD 675 default := by
  show gates.getD (675 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len]
  rw [getD_left _ _ _ (by rw [g048_len]; omega)]

theorem gate_120679 : gate 120679 = (g048).getD 679 default := by
  show gates.getD (679 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len]
  rw [getD_left _ _ _ (by rw [g048_len]; omega)]

theorem gate_120729 : gate 120729 = (g048).getD 729 default := by
  show gates.getD (729 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len]
  rw [getD_left _ _ _ (by rw [g048_len]; omega)]

theorem gate_120730 : gate 120730 = (g048).getD 730 default := by
  show gates.getD (730 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len]
  rw [getD_left _ _ _ (by rw [g048_len]; omega)]

theorem gate_120782 : gate 120782 = (g048).getD 782 default := by
  show gates.getD (782 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len]
  rw [getD_left _ _ _ (by rw [g048_len]; omega)]

theorem gate_120783 : gate 120783 = (g048).getD 783 default := by
  show gates.getD (783 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len]
  rw [getD_left _ _ _ (by rw [g048_len]; omega)]

theorem gate_120799 : gate 120799 = (g048).getD 799 default := by
  show gates.getD (799 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len]
  rw [getD_left _ _ _ (by rw [g048_len]; omega)]

theorem gate_120800 : gate 120800 = (g048).getD 800 default := by
  show gates.getD (800 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len]
  rw [getD_left _ _ _ (by rw [g048_len]; omega)]

theorem gate_120801 : gate 120801 = (g048).getD 801 default := by
  show gates.getD (801 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len]
  rw [getD_left _ _ _ (by rw [g048_len]; omega)]

theorem gate_120802 : gate 120802 = (g048).getD 802 default := by
  show gates.getD (802 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len]
  rw [getD_left _ _ _ (by rw [g048_len]; omega)]

theorem gate_120803 : gate 120803 = (g048).getD 803 default := by
  show gates.getD (803 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len]
  rw [getD_left _ _ _ (by rw [g048_len]; omega)]

theorem gate_120804 : gate 120804 = (g048).getD 804 default := by
  show gates.getD (804 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len]
  rw [getD_left _ _ _ (by rw [g048_len]; omega)]

theorem gate_120808 : gate 120808 = (g048).getD 808 default := by
  show gates.getD (808 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len]
  rw [getD_left _ _ _ (by rw [g048_len]; omega)]

theorem gate_120920 : gate 120920 = (g048).getD 920 default := by
  show gates.getD (920 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len]
  rw [getD_left _ _ _ (by rw [g048_len]; omega)]

theorem gate_135592 : gate 135592 = (g054).getD 592 default := by
  show gates.getD (592 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135593 : gate 135593 = (g054).getD 593 default := by
  show gates.getD (593 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135597 : gate 135597 = (g054).getD 597 default := by
  show gates.getD (597 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135818 : gate 135818 = (g054).getD 818 default := by
  show gates.getD (818 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135819 : gate 135819 = (g054).getD 819 default := by
  show gates.getD (819 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135820 : gate 135820 = (g054).getD 820 default := by
  show gates.getD (820 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135821 : gate 135821 = (g054).getD 821 default := by
  show gates.getD (821 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135822 : gate 135822 = (g054).getD 822 default := by
  show gates.getD (822 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135829 : gate 135829 = (g054).getD 829 default := by
  show gates.getD (829 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135935 : gate 135935 = (g054).getD 935 default := by
  show gates.getD (935 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135936 : gate 135936 = (g054).getD 936 default := by
  show gates.getD (936 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135937 : gate 135937 = (g054).getD 937 default := by
  show gates.getD (937 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135940 : gate 135940 = (g054).getD 940 default := by
  show gates.getD (940 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135950 : gate 135950 = (g054).getD 950 default := by
  show gates.getD (950 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135951 : gate 135951 = (g054).getD 951 default := by
  show gates.getD (951 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135952 : gate 135952 = (g054).getD 952 default := by
  show gates.getD (952 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135953 : gate 135953 = (g054).getD 953 default := by
  show gates.getD (953 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135956 : gate 135956 = (g054).getD 956 default := by
  show gates.getD (956 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135964 : gate 135964 = (g054).getD 964 default := by
  show gates.getD (964 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135965 : gate 135965 = (g054).getD 965 default := by
  show gates.getD (965 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135966 : gate 135966 = (g054).getD 966 default := by
  show gates.getD (966 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135967 : gate 135967 = (g054).getD 967 default := by
  show gates.getD (967 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_135972 : gate 135972 = (g054).getD 972 default := by
  show gates.getD (972 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len]
  rw [getD_left _ _ _ (by rw [g054_len]; omega)]

theorem gate_140533 : gate 140533 = (g056).getD 533 default := by
  show gates.getD (533 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len, getD_skip _ _ g054_len, getD_skip _ _ g055_len]
  rw [getD_left _ _ _ (by rw [g056_len]; omega)]

theorem gate_140534 : gate 140534 = (g056).getD 534 default := by
  show gates.getD (534 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len, getD_skip _ _ g054_len, getD_skip _ _ g055_len]
  rw [getD_left _ _ _ (by rw [g056_len]; omega)]

theorem gate_140537 : gate 140537 = (g056).getD 537 default := by
  show gates.getD (537 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len, getD_skip _ _ g054_len, getD_skip _ _ g055_len]
  rw [getD_left _ _ _ (by rw [g056_len]; omega)]

theorem gate_144471 : gate 144471 = (g057).getD 1971 default := by
  show gates.getD (1971 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len, getD_skip _ _ g054_len, getD_skip _ _ g055_len, getD_skip _ _ g056_len]
  rw [getD_left _ _ _ (by rw [g057_len]; omega)]

theorem gate_146154 : gate 146154 = (g058).getD 1154 default := by
  show gates.getD (1154 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len, getD_skip _ _ g054_len, getD_skip _ _ g055_len, getD_skip _ _ g056_len, getD_skip _ _ g057_len]
  rw [getD_left _ _ _ (by rw [g058_len]; omega)]

theorem gate_146200 : gate 146200 = (g058).getD 1200 default := by
  show gates.getD (1200 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500 + 2500) default = _
  simp only [gates]
  rw [getD_skip _ _ g000_len, getD_skip _ _ g001_len, getD_skip _ _ g002_len, getD_skip _ _ g003_len, getD_skip _ _ g004_len, getD_skip _ _ g005_len, getD_skip _ _ g006_len, getD_skip _ _ g007_len, getD_skip _ _ g008_len, getD_skip _ _ g009_len, getD_skip _ _ g010_len, getD_skip _ _ g011_len, getD_skip _ _ g012_len, getD_skip _ _ g013_len, getD_skip _ _ g014_len, getD_skip _ _ g015_len, getD_skip _ _ g016_len, getD_skip _ _ g017_len, getD_skip _ _ g018_len, getD_skip _ _ g019_len, getD_skip _ _ g020_len, getD_skip _ _ g021_len, getD_skip _ _ g022_len, getD_skip _ _ g023_len, getD_skip _ _ g024_len, getD_skip _ _ g025_len, getD_skip _ _ g026_len, getD_skip _ _ g027_len, getD_skip _ _ g028_len, getD_skip _ _ g029_len, getD_skip _ _ g030_len, getD_skip _ _ g031_len, getD_skip _ _ g032_len, getD_skip _ _ g033_len, getD_skip _ _ g034_len, getD_skip _ _ g035_len, getD_skip _ _ g036_len, getD_skip _ _ g037_len, getD_skip _ _ g038_len, getD_skip _ _ g039_len, getD_skip _ _ g040_len, getD_skip _ _ g041_len, getD_skip _ _ g042_len, getD_skip _ _ g043_len, getD_skip _ _ g044_len, getD_skip _ _ g045_len, getD_skip _ _ g046_len, getD_skip _ _ g047_len, getD_skip _ _ g048_len, getD_skip _ _ g049_len, getD_skip _ _ g050_len, getD_skip _ _ g051_len, getD_skip _ _ g052_len, getD_skip _ _ g053_len, getD_skip _ _ g054_len, getD_skip _ _ g055_len, getD_skip _ _ g056_len, getD_skip _ _ g057_len]
  rw [getD_left _ _ _ (by rw [g058_len]; omega)]

/-- The nine ustate O6 gates of `ArbCleanPS.targetQPS` are gates of the decoded netlist, with the same name,
pin count and table. -/
theorem q0 : (gate 144471).name = "SLICE_X38Y51.BLUT.O6" ∧ (gate 144471).k = 6 ∧ (gate 144471).init = 18446650284053947620 := by
  rw [gate_144471]; decide +kernel

theorem q1 : (gate 146200).name = "SLICE_X39Y24.ALUT.O6" ∧ (gate 146200).k = 6 ∧ (gate 146200).init = 18442146666842484976 := by
  rw [gate_146200]; decide +kernel

theorem q2 : (gate 37766).name = "SLICE_X16Y25.BLUT.O6" ∧ (gate 37766).k = 6 ∧ (gate 37766).init = 18446651315003387460 := by
  rw [gate_37766]; decide +kernel

theorem q3 : (gate 37978).name = "SLICE_X16Y31.ALUT.O6" ∧ (gate 37978).k = 6 ∧ (gate 37978).init = 18445602716198685900 := by
  rw [gate_37978]; decide +kernel

theorem q4 : (gate 37325).name = "SLICE_X16Y18.DLUT.O6" ∧ (gate 37325).k = 6 ∧ (gate 37325).init = 18442239386023817456 := by
  rw [gate_37325]; decide +kernel

theorem q5 : (gate 28304).name = "SLICE_X14Y18.ALUT.O6" ∧ (gate 28304).k = 6 ∧ (gate 28304).init = 18442184187104129264 := by
  rw [gate_28304]; decide +kernel

theorem q6 : (gate 28366).name = "SLICE_X14Y19.ALUT.O6" ∧ (gate 28366).k = 6 ∧ (gate 28366).init = 18229724517218581002 := by
  rw [gate_28366]; decide +kernel

theorem q7 : (gate 47283).name = "SLICE_X18Y24.ALUT.O6" ∧ (gate 47283).k = 6 ∧ (gate 47283).init = 18446125929114675882 := by
  rw [gate_47283]; decide +kernel

theorem q8 : (gate 146154).name = "SLICE_X39Y21.CLUT.O6" ∧ (gate 146154).k = 6 ∧ (gate 146154).init = 18423099673070424144 := by
  rw [gate_146154]; decide +kernel

/-- The arcs of `RaceStaticPS.racePath` and `raceLoop` are the decoded netlist's arcs of these gate pins. -/
theorem racePath_eq : Formal.Cells.RaceStaticPS.racePath = [(gate 120803).arcs.getD 0 default, (gate 120802).arcs.getD 0 default, (gate 120801).arcs.getD 0 default, (gate 120800).arcs.getD 0 default, (gate 120799).arcs.getD 0 default, (gate 120804).arcs.getD 0 default, (gate 140537).arcs.getD 4 default, (gate 140534).arcs.getD 0 default, (gate 140533).arcs.getD 0 default, (gate 135593).arcs.getD 0 default, (gate 135592).arcs.getD 0 default, (gate 135597).arcs.getD 0 default, (gate 135829).arcs.getD 3 default, (gate 135821).arcs.getD 0 default, (gate 135820).arcs.getD 0 default, (gate 135819).arcs.getD 0 default, (gate 135818).arcs.getD 0 default, (gate 135822).arcs.getD 0 default, (gate 135972).arcs.getD 3 default, (gate 135966).arcs.getD 0 default, (gate 135965).arcs.getD 0 default, (gate 135964).arcs.getD 0 default, (gate 135967).arcs.getD 0 default, (gate 135956).arcs.getD 4 default, (gate 135952).arcs.getD 0 default, (gate 135951).arcs.getD 0 default, (gate 135950).arcs.getD 0 default, (gate 135953).arcs.getD 0 default, (gate 135940).arcs.getD 4 default, (gate 135937).arcs.getD 0 default, (gate 135936).arcs.getD 0 default, (gate 135935).arcs.getD 0 default, (gate 120920).arcs.getD 0 default, (gate 120675).arcs.getD 0 default, (gate 120679).arcs.getD 0 default, (gate 120808).arcs.getD 4 default] := by
  simp only [gate_120675, gate_120679, gate_120799, gate_120800, gate_120801, gate_120802, gate_120803, gate_120804, gate_120808, gate_120920, gate_135592, gate_135593, gate_135597, gate_135818, gate_135819, gate_135820, gate_135821, gate_135822, gate_135829, gate_135935, gate_135936, gate_135937, gate_135940, gate_135950, gate_135951, gate_135952, gate_135953, gate_135956, gate_135964, gate_135965, gate_135966, gate_135967, gate_135972, gate_140533, gate_140534, gate_140537]
  decide +kernel

theorem raceLoop_eq : Formal.Cells.RaceStaticPS.raceLoop = [(gate 120783).arcs.getD 0 default, (gate 120782).arcs.getD 0 default, (gate 120730).arcs.getD 0 default, (gate 120729).arcs.getD 0 default, (gate 120675).arcs.getD 0 default, (gate 120679).arcs.getD 0 default, (gate 120808).arcs.getD 0 default] := by
  simp only [gate_120675, gate_120679, gate_120729, gate_120730, gate_120782, gate_120783, gate_120808]
  decide +kernel

/-- **The race verdicts as statements about the decoded netlist's own arcs.** -/
theorem race_holds_decoded :
    (([(gate 120783).arcs.getD 0 default, (gate 120782).arcs.getD 0 default, (gate 120730).arcs.getD 0 default, (gate 120729).arcs.getD 0 default, (gate 120675).arcs.getD 0 default, (gate 120679).arcs.getD 0 default, (gate 120808).arcs.getD 0 default]).map (Formal.Cells.Ua1Static.hi 1 (87/200) (1/2))).sum <=
      (([(gate 120803).arcs.getD 0 default, (gate 120802).arcs.getD 0 default, (gate 120801).arcs.getD 0 default, (gate 120800).arcs.getD 0 default, (gate 120799).arcs.getD 0 default, (gate 120804).arcs.getD 0 default, (gate 140537).arcs.getD 4 default, (gate 140534).arcs.getD 0 default, (gate 140533).arcs.getD 0 default, (gate 135593).arcs.getD 0 default, (gate 135592).arcs.getD 0 default, (gate 135597).arcs.getD 0 default, (gate 135829).arcs.getD 3 default, (gate 135821).arcs.getD 0 default, (gate 135820).arcs.getD 0 default, (gate 135819).arcs.getD 0 default, (gate 135818).arcs.getD 0 default, (gate 135822).arcs.getD 0 default, (gate 135972).arcs.getD 3 default, (gate 135966).arcs.getD 0 default, (gate 135965).arcs.getD 0 default, (gate 135964).arcs.getD 0 default, (gate 135967).arcs.getD 0 default, (gate 135956).arcs.getD 4 default, (gate 135952).arcs.getD 0 default, (gate 135951).arcs.getD 0 default, (gate 135950).arcs.getD 0 default, (gate 135953).arcs.getD 0 default, (gate 135940).arcs.getD 4 default, (gate 135937).arcs.getD 0 default, (gate 135936).arcs.getD 0 default, (gate 135935).arcs.getD 0 default, (gate 120920).arcs.getD 0 default, (gate 120675).arcs.getD 0 default, (gate 120679).arcs.getD 0 default, (gate 120808).arcs.getD 4 default]).map (Formal.Cells.Ua1Static.lo 1 (87/200) (1/2))).sum := by
  rw [← racePath_eq, ← raceLoop_eq]; exact Formal.Cells.RaceStaticPS.race_holds

theorem race_fails_decoded :
    (([(gate 120803).arcs.getD 0 default, (gate 120802).arcs.getD 0 default, (gate 120801).arcs.getD 0 default, (gate 120800).arcs.getD 0 default, (gate 120799).arcs.getD 0 default, (gate 120804).arcs.getD 0 default, (gate 140537).arcs.getD 4 default, (gate 140534).arcs.getD 0 default, (gate 140533).arcs.getD 0 default, (gate 135593).arcs.getD 0 default, (gate 135592).arcs.getD 0 default, (gate 135597).arcs.getD 0 default, (gate 135829).arcs.getD 3 default, (gate 135821).arcs.getD 0 default, (gate 135820).arcs.getD 0 default, (gate 135819).arcs.getD 0 default, (gate 135818).arcs.getD 0 default, (gate 135822).arcs.getD 0 default, (gate 135972).arcs.getD 3 default, (gate 135966).arcs.getD 0 default, (gate 135965).arcs.getD 0 default, (gate 135964).arcs.getD 0 default, (gate 135967).arcs.getD 0 default, (gate 135956).arcs.getD 4 default, (gate 135952).arcs.getD 0 default, (gate 135951).arcs.getD 0 default, (gate 135950).arcs.getD 0 default, (gate 135953).arcs.getD 0 default, (gate 135940).arcs.getD 4 default, (gate 135937).arcs.getD 0 default, (gate 135936).arcs.getD 0 default, (gate 135935).arcs.getD 0 default, (gate 120920).arcs.getD 0 default, (gate 120675).arcs.getD 0 default, (gate 120679).arcs.getD 0 default, (gate 120808).arcs.getD 4 default]).map (Formal.Cells.Ua1Static.lo 1 (11/25) (1/2))).sum <
      (([(gate 120783).arcs.getD 0 default, (gate 120782).arcs.getD 0 default, (gate 120730).arcs.getD 0 default, (gate 120729).arcs.getD 0 default, (gate 120675).arcs.getD 0 default, (gate 120679).arcs.getD 0 default, (gate 120808).arcs.getD 0 default]).map (Formal.Cells.Ua1Static.hi 1 (11/25) (1/2))).sum := by
  rw [← racePath_eq, ← raceLoop_eq]; exact Formal.Cells.RaceStaticPS.race_fails

/-- The episode path is wired: pin 4 of gate 120808 reads the first listed gate, each listed pin reads the next listed gate's output, and the last reads gate 120808's own output. -/
theorem racePath_wired :
    (gate 120808).ins.getD 4 0 = 120803 ∧
    (gate 120803).ins.getD 0 0 = 120802 ∧
    (gate 120802).ins.getD 0 0 = 120801 ∧
    (gate 120801).ins.getD 0 0 = 120800 ∧
    (gate 120800).ins.getD 0 0 = 120799 ∧
    (gate 120799).ins.getD 0 0 = 120804 ∧
    (gate 120804).ins.getD 0 0 = 140537 ∧
    (gate 140537).ins.getD 4 0 = 140534 ∧
    (gate 140534).ins.getD 0 0 = 140533 ∧
    (gate 140533).ins.getD 0 0 = 135593 ∧
    (gate 135593).ins.getD 0 0 = 135592 ∧
    (gate 135592).ins.getD 0 0 = 135597 ∧
    (gate 135597).ins.getD 0 0 = 135829 ∧
    (gate 135829).ins.getD 3 0 = 135821 ∧
    (gate 135821).ins.getD 0 0 = 135820 ∧
    (gate 135820).ins.getD 0 0 = 135819 ∧
    (gate 135819).ins.getD 0 0 = 135818 ∧
    (gate 135818).ins.getD 0 0 = 135822 ∧
    (gate 135822).ins.getD 0 0 = 135972 ∧
    (gate 135972).ins.getD 3 0 = 135966 ∧
    (gate 135966).ins.getD 0 0 = 135965 ∧
    (gate 135965).ins.getD 0 0 = 135964 ∧
    (gate 135964).ins.getD 0 0 = 135967 ∧
    (gate 135967).ins.getD 0 0 = 135956 ∧
    (gate 135956).ins.getD 4 0 = 135952 ∧
    (gate 135952).ins.getD 0 0 = 135951 ∧
    (gate 135951).ins.getD 0 0 = 135950 ∧
    (gate 135950).ins.getD 0 0 = 135953 ∧
    (gate 135953).ins.getD 0 0 = 135940 ∧
    (gate 135940).ins.getD 4 0 = 135937 ∧
    (gate 135937).ins.getD 0 0 = 135936 ∧
    (gate 135936).ins.getD 0 0 = 135935 ∧
    (gate 135935).ins.getD 0 0 = 120920 ∧
    (gate 120920).ins.getD 0 0 = 120675 ∧
    (gate 120675).ins.getD 0 0 = 120679 ∧
    (gate 120679).ins.getD 0 0 = 120808 := by
  simp only [gate_120675, gate_120679, gate_120799, gate_120800, gate_120801, gate_120802, gate_120803, gate_120804, gate_120808, gate_120920, gate_135592, gate_135593, gate_135597, gate_135818, gate_135819, gate_135820, gate_135821, gate_135822, gate_135829, gate_135935, gate_135936, gate_135937, gate_135940, gate_135950, gate_135951, gate_135952, gate_135953, gate_135956, gate_135964, gate_135965, gate_135966, gate_135967, gate_135972, gate_140533, gate_140534, gate_140537]
  decide +kernel

/-- The feedback route consists of copy gates (one pin, table 0b10). -/
theorem raceLoop_copies :
    (gate 120783).k = 1 ∧ (gate 120783).init = 2 ∧
    (gate 120782).k = 1 ∧ (gate 120782).init = 2 ∧
    (gate 120730).k = 1 ∧ (gate 120730).init = 2 ∧
    (gate 120729).k = 1 ∧ (gate 120729).init = 2 ∧
    (gate 120675).k = 1 ∧ (gate 120675).init = 2 ∧
    (gate 120679).k = 1 ∧ (gate 120679).init = 2 := by
  simp only [gate_120783, gate_120782, gate_120730, gate_120729, gate_120675, gate_120679]
  decide +kernel

/-- The feedback loop is wired: pin 0 reads a chain of copy gates that starts at gate 120808's own output. -/
theorem raceLoop_wired :
    (gate 120808).ins.getD 0 0 = 120783 ∧
    (gate 120783).ins.getD 0 0 = 120782 ∧
    (gate 120782).ins.getD 0 0 = 120730 ∧
    (gate 120730).ins.getD 0 0 = 120729 ∧
    (gate 120729).ins.getD 0 0 = 120675 ∧
    (gate 120675).ins.getD 0 0 = 120679 ∧
    (gate 120679).ins.getD 0 0 = 120808 := by
  simp only [gate_120675, gate_120679, gate_120729, gate_120730, gate_120782, gate_120783, gate_120808]
  decide +kernel

/-- Pin chains of gate 120808: the feedback pin 0 reads the gate's own output through its route of copy gates;
the other pins read their pin nodes directly. -/
def racePcs : List Formal.Timing.SpecChain.PinChain := [⟨120808, [gate 120783, gate 120782, gate 120730, gate 120729, gate 120675, gate 120679]⟩, ⟨120787, []⟩, ⟨120790, []⟩, ⟨120797, []⟩, ⟨120803, []⟩, ⟨120807, []⟩]

/-- The chains are wired as listed (shard C's per-gate check `pinsOK`, decided on the netlist). -/
theorem race_pinsOK : Formal.Timing.SpecChain.pinsOK (gate 120808) racePcs = true := by
  simp only [racePcs, gate_120675, gate_120679, gate_120729, gate_120730, gate_120782, gate_120783, gate_120808]
  decide +kernel

/-- The composite feedback arcs (pin arc, then the route) have window-end sum 1091 ps at κ = (87/200), corner 1/2. -/
theorem race_loop_hi :
    ((Formal.Timing.SpecChain.pinArcs (gate 120808) racePcs 0).map (Formal.Cells.Ua1Static.hi 1 (87/200) (1/2))).sum = 1091 := by
  simp only [racePcs, Formal.Timing.SpecChain.pinArcs, gate_120675, gate_120679, gate_120729, gate_120730, gate_120782, gate_120783, gate_120808]
  decide +kernel

/-- **In every behaviour at g = 1, κ = 0.435, corner 1/2, node 120808's routed feedback delay is at most 1091 ps**:
every composite delay its feedback pin can have (one admissible delay per arc, `SumAdm`) is bounded. With C's
`SpecChain.collapse` and `SpecFbChain.cfb_switch`, a set condition lasting 1091 ps switches the node cleanly. -/
theorem race_loop_delay_le {D : Nat}
    (h : Formal.Timing.SpecChain.SumAdm ⟨1, (87/200)⟩ (1/2) (Formal.Timing.SpecChain.pinArcs (gate 120808) racePcs 0) D) :
    D ≤ 1091 := by
  have := (Formal.Cells.SpecFbChain.sumAdm_bounds _ D h).2
  have e := race_loop_hi
  simp only at this
  omega

end Formal.Cells.TargetLinkPS
#print axioms Formal.Cells.TargetLinkPS.q0
#print axioms Formal.Cells.TargetLinkPS.q1
#print axioms Formal.Cells.TargetLinkPS.q2
#print axioms Formal.Cells.TargetLinkPS.q3
#print axioms Formal.Cells.TargetLinkPS.q4
#print axioms Formal.Cells.TargetLinkPS.q5
#print axioms Formal.Cells.TargetLinkPS.q6
#print axioms Formal.Cells.TargetLinkPS.q7
#print axioms Formal.Cells.TargetLinkPS.q8
#print axioms Formal.Cells.TargetLinkPS.racePath_eq
#print axioms Formal.Cells.TargetLinkPS.raceLoop_eq
#print axioms Formal.Cells.TargetLinkPS.race_holds_decoded
#print axioms Formal.Cells.TargetLinkPS.race_fails_decoded
#print axioms Formal.Cells.TargetLinkPS.racePath_wired
#print axioms Formal.Cells.TargetLinkPS.raceLoop_copies
#print axioms Formal.Cells.TargetLinkPS.raceLoop_wired
#print axioms Formal.Cells.TargetLinkPS.race_pinsOK
#print axioms Formal.Cells.TargetLinkPS.race_loop_hi
#print axioms Formal.Cells.TargetLinkPS.race_loop_delay_le
