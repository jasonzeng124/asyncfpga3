import Formal.Target.Spec
import Mathlib.Data.Rat.Floor
import Mathlib.Tactic.GCongr
import Mathlib.Tactic.Linarith

/-!
# Interval timing (settle and hold) in the frozen Spec's own gate semantics (shard C)

**Problem, plainly.** Every bundling obligation of THE theorem (data settles before its
request; a value holds until it has been read) is a statement about how long a gate's
output can lag, or lead, its inputs. Shard C's older interval checker
(`Formal.Timing.Checker`) is proved sound against its own run semantics, not against
`Formal.Target.Spec`. This file proves the interval rules directly for `Spec.GateOK`
(H_PRIM with H_DELAY(g, κ): per-pin monotone read times, every read delay admissible,
output = the INIT bit at the address of the reads).

**Proved.**
* `dmax`, `dmin`: integer bounds on every admissible read delay of an arc, valid at every
  corner `c ∈ [0,1]` for sane parameters (`Sane`: `0 ≤ κ ≤ 1`, `0 < g`) and an ordered arc:
  `⌈(1-κ)·fmin / g⌉ ≤ d ≤ ⌈(1+κ)·smax · g⌉` (`adm_le_dmax`, `dmin_le_adm`).
  (Changed 2026-11-01 with `Spec.Adm`, owner decision 3: the old bounds `⌈fmin/g⌉ ≤ d ≤ ⌈smax·g⌉`
  came from the global band, which `Adm` no longer has; the old `adm_le_dmax` is false for the new
  `Adm` at κ > 0. Edited by shard A at the owner's instruction.)
* `gate_stable`: if every input `i` of a gate holds the value `v i` on `[S i, U i]`, then
  the output holds `INIT[addr v]` on `[max(start, S i + dmax i), min(U i + dmin i)]`.
  The window can be empty; then the lemma says nothing.
* `cert_sound`: for a list of gates and a certificate `(S, U, V)` (a stability window
  and a value per node) that `certOK` accepts, every gate output of the list is
  stable at its certified value on its certified window, in every `Behaves` behaviour,
  provided the nodes the list reads from outside are (hypothesis `hext`). `certOK` checks,
  per gate, only the local rule of `gate_stable` and that each input is either external or
  the output of an EARLIER gate of the list (so it is an STA pass in topological order).
  It is a Boolean function: run it on a decoded netlist.

**Not shown.** Nothing about feedback (a loop's nodes are never certified by this rule:
an input must be external or earlier); nothing about which windows a design needs (that
is the obligation generator); glitches inside a window are excluded only because the
window certifies a constant value.
-/

namespace Formal.Timing.SpecSettle
open Formal.Target

/-! ## Delay bounds -/

/-- Sane delay parameters: scatter in `[0, 1]`, positive guard. -/
def Sane (p : DelayPar) : Prop := 0 ≤ p.κ ∧ p.κ ≤ 1 ∧ 0 < p.g

/-- Upper bound on every admissible read delay of `e` (ps), at every corner: `⌈(1+κ)·smax·g⌉`. -/
def dmax (p : DelayPar) (e : Arc) : Nat := (⌈(1 + p.κ) * (e.smax : ℚ) * p.g⌉).toNat

/-- Lower bound on every admissible read delay of `e` (ps), at every corner: `⌈(1-κ)·fmin / g⌉`. -/
def dmin (p : DelayPar) (e : Arc) : Nat := (⌈(1 - p.κ) * (e.fmin : ℚ) / p.g⌉).toNat

theorem adm_le_dmax {p : DelayPar} {c : ℚ} {e : Arc} {d : Nat} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (he : e.fmax ≤ e.smax) (h : Adm p c e d) : d ≤ dmax p e := by
  obtain ⟨hk0, hk1, hg⟩ := hp
  have he' : (e.fmax : ℚ) ≤ e.smax := by exact_mod_cast he
  have hl : lerp e.fmax e.smax c ≤ e.smax := by unfold lerp; nlinarith
  have hk : (0 : ℚ) ≤ 1 + p.κ := by linarith
  have h1 : (d : ℚ) ≤ (1 + p.κ) * (e.smax : ℚ) * p.g :=
    le_trans h.2 (by gcongr)
  have h2 : (d : ℚ) ≤ (⌈(1 + p.κ) * (e.smax : ℚ) * p.g⌉ : ℚ) := le_trans h1 (Int.le_ceil _)
  have h3 : (d : ℤ) ≤ ⌈(1 + p.κ) * (e.smax : ℚ) * p.g⌉ := by exact_mod_cast h2
  unfold dmax
  omega

theorem dmin_le_adm {p : DelayPar} {c : ℚ} {e : Arc} {d : Nat} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (he : e.fmin ≤ e.smin) (h : Adm p c e d) : dmin p e ≤ d := by
  obtain ⟨hk0, hk1, hg⟩ := hp
  have he' : (e.fmin : ℚ) ≤ e.smin := by exact_mod_cast he
  have hl : (e.fmin : ℚ) ≤ lerp e.fmin e.smin c := by unfold lerp; nlinarith
  have hk : (0 : ℚ) ≤ 1 - p.κ := by linarith
  have h1 : (1 - p.κ) * (e.fmin : ℚ) / p.g ≤ (d : ℚ) := le_trans (by gcongr) h.1
  have h2 : ⌈(1 - p.κ) * (e.fmin : ℚ) / p.g⌉ ≤ (d : ℤ) := Int.ceil_le.mpr (by exact_mod_cast h1)
  unfold dmin
  omega

/-- The arc facts the bounds need, per pin. -/
def ArcsOK (g : Gate) : Prop :=
  ∀ i, (g.arcs.getD i default).fmin ≤ (g.arcs.getD i default).smin ∧
    (g.arcs.getD i default).fmax ≤ (g.arcs.getD i default).smax

theorem arcsOK_of_wf {N : Net} (hN : N.WF) {g : Gate} (hg : g ∈ N.gates) : ArcsOK g := by
  intro i
  by_cases hi : i < g.arcs.length
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]
    obtain ⟨-, -, -, -, -, ha⟩ := hN.1 g hg
    obtain ⟨-, -, h3, h4⟩ := ha _ (List.getElem_mem hi)
    exact ⟨h3, h4⟩
  · rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega), Option.getD_none]
    exact ⟨Nat.le_refl _, Nat.le_refl _⟩

/-! ## One gate -/

theorem addr_congr : ∀ (k : Nat) (a b : Nat → Bool), (∀ i, i < k → a i = b i) → addr k a = addr k b
  | 0, _, _, _ => rfl
  | k + 1, a, b, h => by
    simp only [addr]
    rw [addr_congr k a b (fun i hi => h i (by omega)), h k (by omega)]

/-- The arc of pin `i`. -/
abbrev arcOf (g : Gate) (i : Nat) : Arc := g.arcs.getD i default
/-- The node of pin `i`. -/
abbrev pinOf (g : Gate) (i : Nat) : Nat := g.ins.getD i 0

/-- **One gate.** Inputs stable on windows ⇒ output stable on the shifted intersection. -/
theorem gate_stable {p : DelayPar} {c : ℚ} {g : Gate} {x : Beh} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1)
    (harc : ArcsOK g) (hg : GateOK p c g x)
    (S U : Nat → Nat) (v : Nat → Bool)
    (hin : ∀ i, i < g.k → ∀ t, S i ≤ t → t ≤ U i → x (pinOf g i) t = v i) :
    ∀ t, g.start p ≤ t → (∀ i, i < g.k → S i + dmax p (arcOf g i) ≤ t ∧ t ≤ U i + dmin p (arcOf g i)) →
      x g.out t = g.init.testBit (addr g.k v) := by
  obtain ⟨f, -, hf⟩ := hg
  intro t hst hw
  obtain ⟨hrd, hout⟩ := hf t hst
  rw [hout]
  congr 1
  apply addr_congr
  intro i hi
  obtain ⟨hle, hadm⟩ := hrd i hi
  have h1 : t - f i t ≤ dmax p (arcOf g i) := adm_le_dmax hp hc0 hc1 (harc i).2 hadm
  have h2 : dmin p (arcOf g i) ≤ t - f i t := dmin_le_adm hp hc0 hc1 (harc i).1 hadm
  obtain ⟨hs, hu⟩ := hw i hi
  exact hin i hi (f i t) (by omega) (by omega)

/-! ## A certificate over a list of gates (an STA pass in topological order) -/

/-- A certificate: per node, a stability window `[S v, U v]` and the value held on it. -/
structure Cert where
  S : Nat → Nat
  U : Nat → Nat
  V : Nat → Bool

/-- Node `n` is stable at its certified value on its certified window in `x`. -/
def Cert.Stable (C : Cert) (x : Beh) (n : Nat) : Prop :=
  ∀ t, C.S n ≤ t → t ≤ C.U n → x n t = C.V n

/-- The local rule for one gate: its window lies inside every input's window shifted by
the pin's delay bounds and after the gate's start, and its value is the INIT bit at the
certified input values. -/
def gateRule (p : DelayPar) (C : Cert) (g : Gate) : Bool :=
  decide (g.start p ≤ C.S g.out) &&
  (List.range g.k).all (fun i =>
    decide (C.S (pinOf g i) + dmax p (arcOf g i) ≤ C.S g.out) &&
    decide (C.U g.out ≤ C.U (pinOf g i) + dmin p (arcOf g i))) &&
  (C.V g.out == g.init.testBit (addr g.k (fun i => C.V (pinOf g i))))

/-- The checker: walk the gates in order; every input must be external or the output of
an earlier gate (`known`), and every gate must pass `gateRule`. -/
def certOK (p : DelayPar) (C : Cert) : List Nat → List Gate → Bool
  | _, [] => true
  | known, g :: gs =>
    (List.range g.k).all (fun i => known.contains (pinOf g i)) && gateRule p C g &&
      certOK p C (g.out :: known) gs

theorem gateRule_sound {p : DelayPar} {c : ℚ} {C : Cert} {g : Gate} {x : Beh}
    (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hw : ArcsOK g) (hg : GateOK p c g x) (hr : gateRule p C g = true)
    (hin : ∀ i, i < g.k → C.Stable x (pinOf g i)) : C.Stable x g.out := by
  simp only [gateRule, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range,
    beq_iff_eq] at hr
  obtain ⟨⟨hst, hpins⟩, hv⟩ := hr
  unfold Cert.Stable at hin ⊢
  intro t h1 h2
  rw [hv]
  apply gate_stable hp hc0 hc1 hw hg (fun i => C.S (pinOf g i)) (fun i => C.U (pinOf g i)) (fun i => C.V (pinOf g i))
    (fun i hi t' a b => hin i hi t' a b) t (by omega)
  intro i hi
  have := hpins i hi
  exact ⟨by omega, by omega⟩

/-- **Soundness of the certificate checker.** If the nodes in `known` are stable, every gate
of `gs` holds in `x`, and `certOK` accepts, then every gate output of `gs` is stable. -/
theorem cert_sound {p : DelayPar} {c : ℚ} {C : Cert} {x : Beh} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∀ (known : List Nat) (gs : List Gate), (∀ g ∈ gs, ArcsOK g) →
      (∀ n ∈ known, C.Stable x n) → (∀ g ∈ gs, GateOK p c g x) → certOK p C known gs = true →
      ∀ g ∈ gs, C.Stable x g.out
  | _, [], _, _, _, _ => fun g hg => absurd hg List.not_mem_nil
  | known, g :: gs, hws, hk, hgs, hc => by
    simp only [certOK, Bool.and_eq_true, List.all_eq_true, List.mem_range,
      List.contains_iff_mem] at hc
    obtain ⟨⟨hpin, hr⟩, hrest⟩ := hc
    have hout : C.Stable x g.out :=
      gateRule_sound hp hc0 hc1 (hws g List.mem_cons_self) (hgs g List.mem_cons_self) hr (fun i hi => hk _ (hpin i hi))
    intro g' hg'
    rcases List.mem_cons.mp hg' with e | e
    · subst e; exact hout
    · exact cert_sound hp hc0 hc1 (g.out :: known) gs (fun g'' h'' => hws g'' (List.mem_cons_of_mem _ h''))
        (fun n hn => by
          rcases List.mem_cons.mp hn with e' | e'
          · subst e'; exact hout
          · exact hk n e')
        (fun g'' h'' => hgs g'' (List.mem_cons_of_mem _ h'')) hrest g' e

/-- **On a netlist.** For a behaviour of `N` (one corner for the die), a certificate
accepted on a list of `N`'s gates is sound. -/
theorem cert_sound_net {p : DelayPar} {N : Net} {x : Beh} (hp : Sane p) (hN : N.WF) (hb : Behaves p N x) {C : Cert}
    (known : List Nat) (gs : List Gate) (hsub : ∀ g ∈ gs, g ∈ N.gates)
    (hk : ∀ n ∈ known, C.Stable x n) (hc : certOK p C known gs = true) :
    ∀ g ∈ gs, C.Stable x g.out := by
  obtain ⟨c, hc0, hc1, hall⟩ := hb
  exact cert_sound hp hc0 hc1 known gs (fun g hg => arcsOK_of_wf hN (hsub g hg)) hk
    (fun g hg => hall g (hsub g hg)) hc

end Formal.Timing.SpecSettle
