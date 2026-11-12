import Formal.Timing.SpecChain
import Formal.Net.TimedOccX
import Mathlib.Data.List.Nodup

/-!
# From Spec behaviours to the timed occurrence-net model (shard C, S4 bridge)

**Problem, plainly.** `TimedOcc`/`TimedOccX` reason about a gate model with per-source read times inside
`[lo, hi]`. THE statement's semantics is `Spec.GateOK` on every gate of the decoded netlist, and the collapsed
view (`SpecChain.CGateOK`, proved for every logic gate of THE target in `CViewPS.collapsed`) gives each logic
gate per-pin monotone reads of its sources with composite delays that are sums of `Adm` delays at the
behaviour's corner `c`. Does that give the timed model's read hypotheses, with corner-specific integer bounds?

**Proved:**
* `loC_le`/`le_hiC`, `sumAdm_corner`: at corner `c`, an admissible arc delay lies in
  `[⌈(1-κ)·lerp(fmin,smin,c)/g⌉, ⌊(1+κ)·lerp(fmax,smax,c)·g⌋]`, and a composite delay between the sums.
* `reads_of_cgate`: for a timed net whose gates each come with a `CGateOK` fact (distinct sources, pin list =
  sources, function = INIT at the address, `lo`/`hi` at most/at least the corner sums, start before `t0`),
  there are read times `r` satisfying `TBehX`'s `rd` (given `hi ≤ H`), `mono` and `geq` fields.

**Not shown here:** the quiet start and the environment rule (the other `TBehX` fields), the `lo ≥ 1` check
(data), any instance.
-/

namespace Formal.Net.OccNet.Bridge
open Formal.Target Formal.Timing.SpecSettle Formal.Timing.SpecChain Formal.Net.OccNet Formal.Net.OccNet.Timed

/-- Corner-specific integer bounds of one arc. -/
def loC (p : DelayPar) (c : ℚ) (e : Arc) : Nat := (⌈(1 - p.κ) * lerp e.fmin e.smin c / p.g⌉).toNat
def hiC (p : DelayPar) (c : ℚ) (e : Arc) : Nat := (⌊(1 + p.κ) * lerp e.fmax e.smax c * p.g⌋).toNat

theorem loC_le {p : DelayPar} {c : ℚ} {e : Arc} {d : Nat} (h : Adm p c e d) : loC p c e ≤ d := by
  have h2 : ⌈(1 - p.κ) * lerp e.fmin e.smin c / p.g⌉ ≤ (d : ℤ) := Int.ceil_le.mpr (by exact_mod_cast h.1)
  unfold loC; omega

theorem le_hiC {p : DelayPar} {c : ℚ} {e : Arc} {d : Nat} (h : Adm p c e d) : d ≤ hiC p c e := by
  have h2 : (d : ℤ) ≤ ⌊(1 + p.κ) * lerp e.fmax e.smax c * p.g⌋ := Int.le_floor.mpr (by exact_mod_cast h.2)
  unfold hiC; omega

def sumLoC (p : DelayPar) (c : ℚ) (es : List Arc) : Nat := (es.map (loC p c)).sum
def sumHiC (p : DelayPar) (c : ℚ) (es : List Arc) : Nat := (es.map (hiC p c)).sum

theorem sumAdm_corner {p : DelayPar} {c : ℚ} :
    ∀ (es : List Arc) (D : Nat), SumAdm p c es D → sumLoC p c es ≤ D ∧ D ≤ sumHiC p c es
  | [], D, h => by simp [SumAdm] at h; simp [sumLoC, sumHiC, h]
  | e :: es, D, ⟨d, hd, hle, hr⟩ => by
    have h1 := loC_le hd
    have h2 := le_hiC hd
    obtain ⟨r1, r2⟩ := sumAdm_corner es (D - d) hr
    simp only [sumLoC, sumHiC, List.map_cons, List.sum_cons] at r1 r2 ⊢
    omega

/-- What the bridge needs of one gate of the timed net. -/
structure GateFact (p : DelayPar) (c : ℚ) (N : TNet Nat) (x : Beh) (t0 : Nat) (v : Nat) : Prop where
  ex : ∃ (g : Gate) (src : Nat → Nat) (arcs : Nat → List Arc) (S : Nat),
    CGateOK p c g src arcs S x ∧ S ≤ t0 + 1 ∧
    N.pins v = (List.range g.k).map src ∧ (N.pins v).Nodup ∧ g.out = v ∧
    (∀ l, N.F v l = g.init.testBit (addr g.k fun i => l.getD i false)) ∧
    (∀ i, i < g.k → N.lo v (src i) ≤ sumLoC p c (arcs i) ∧ sumHiC p c (arcs i) ≤ N.hi v (src i))

theorem idx_of_nodup {src : Nat → Nat} {k : Nat} (hnd : ((List.range k).map src).Nodup) {i j : Nat}
    (hi : i < k) (hj : j < k) (h : src i = src j) : i = j := by
  exact (List.nodup_map_iff_inj_on (List.nodup_range)).1 hnd i (List.mem_range.2 hi) j (List.mem_range.2 hj) h

/-- **The read hypotheses of the timed model from `CGateOK`.** -/
theorem reads_of_cgate {p : DelayPar} {c : ℚ} {N : TNet Nat} {x : Beh} {t0 H : Nat}
    (hF : ∀ v, N.gate v = true → GateFact p c N x t0 v)
    (hH : ∀ v w, N.gate v = true → w ∈ N.pins v → N.hi v w ≤ H) :
    ∃ r : Nat → Nat → Nat → Nat,
      (∀ v w t, N.gate v = true → w ∈ N.pins v → t0 < t →
        N.lo v w ≤ t - r v w t ∧ t - r v w t ≤ N.hi v w ∧ r v w t ≤ t ∧ t0 ≤ r v w t + H) ∧
      (∀ v w t t', N.gate v = true → w ∈ N.pins v → t0 < t → t ≤ t' → r v w t ≤ r v w t') ∧
      (∀ v t, N.gate v = true → t0 < t → x v t = N.F v ((N.pins v).map fun w => x w (r v w t))) := by
  classical
  -- choose the data per gate
  have hc : ∀ v, ∃ R : Nat → Nat → Nat, N.gate v = true →
      (∀ w t, w ∈ N.pins v → t0 < t →
        N.lo v w ≤ t - R w t ∧ t - R w t ≤ N.hi v w ∧ R w t ≤ t ∧ t0 ≤ R w t + H) ∧
      (∀ w t t', w ∈ N.pins v → t0 < t → t ≤ t' → R w t ≤ R w t') ∧
      (∀ t, t0 < t → x v t = N.F v ((N.pins v).map fun w => x w (R w t))) := by
    intro v
    by_cases hg : N.gate v = true
    · obtain ⟨g, src, arcs, S, ⟨Fr, hmono, hok⟩, hS, hpins, hnd, hout, hfun, hlh⟩ := (hF v hg).ex
      subst hout
      -- the read of source `w`: the read of its (unique) pin
      let idx : Nat → Nat := fun w => ((List.range g.k).map src).idxOf w
      have hidx : ∀ i, i < g.k → idx (src i) = i := by
        intro i hi
        have hm : src i ∈ (List.range g.k).map src := List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩
        have hlt : idx (src i) < ((List.range g.k).map src).length := List.idxOf_lt_length_iff.2 hm
        have hget := List.getElem_idxOf hlt
        simp only [List.getElem_map, List.getElem_range] at hget
        have hlt' : idx (src i) < g.k := by simpa using hlt
        exact idx_of_nodup (hpins ▸ hnd) hlt' hi hget
      have hmem : ∀ w, w ∈ N.pins g.out → ∃ i, i < g.k ∧ src i = w := by
        intro w hw; rw [hpins] at hw
        obtain ⟨i, hi, he⟩ := List.mem_map.1 hw
        exact ⟨i, List.mem_range.1 hi, he⟩
      refine ⟨fun w t => Fr (idx w) t, fun _ => ⟨?_, ?_, ?_⟩⟩
      · intro w t hw ht
        obtain ⟨i, hi, rfl⟩ := hmem w hw
        simp only [hidx i hi]
        obtain ⟨hr, _⟩ := hok t (by omega)
        obtain ⟨h1, h2⟩ := hr i hi
        obtain ⟨b1, b2⟩ := sumAdm_corner _ _ h2
        obtain ⟨l1, l2⟩ := hlh i hi
        have := hH g.out (src i) hg (by rw [hpins]; exact List.mem_map.2 ⟨i, List.mem_range.2 hi, rfl⟩)
        omega
      · intro w t t' hw ht htt
        obtain ⟨i, hi, rfl⟩ := hmem w hw
        simp only [hidx i hi]
        exact hmono i hi htt
      · intro t ht
        obtain ⟨_, ho⟩ := hok t (by omega)
        rw [ho, hfun]
        congr 1
        apply Formal.Timing.SpecSettle.addr_congr
        intro i hi
        simp [hpins, hi, hidx i hi]
    · exact ⟨fun _ _ => 0, fun h => absurd h hg⟩
  choose R hR using hc
  refine ⟨fun v w t => R v w t, ?_, ?_, ?_⟩
  · intro v w t hg hw ht; exact (hR v hg).1 w t hw ht
  · intro v w t t' hg hw ht htt; exact (hR v hg).2.1 w t t' hw ht htt
  · intro v t hg ht; exact (hR v hg).2.2 t ht

end Formal.Net.OccNet.Bridge
