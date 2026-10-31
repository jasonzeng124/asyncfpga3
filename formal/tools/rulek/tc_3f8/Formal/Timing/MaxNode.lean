import Formal.Timing.Unroll

/-!
# Probe C-10l: C-element "max nodes" in the late-side semantics

tcheck's late sides (C-10h, `Formal.Timing.Unroll.pot_sound`) are OR-causal: in
10a's `Run`, a node changes only if SOME input pin changed, so its earliest change
is the MIN over its in-arcs. A C-element is an AND for timing purposes: if pin `k`
agrees with the output at the time origin, the output cannot move before pin `k`
has moved. Its earliest change is therefore bounded below by the MAX over such
pins. Rule X (C-10k) used this only through a hand-picked switch pin
(`FbFirstRt.cel_next_needs_all`, "pick any one input"); Xi needed **H_OR_IDLE**
(the inactive steer branch's C-element at rest, ALL inputs agreeing) to apply it
to the other roots of an OR'ed acknowledge.

This file:

* `AllBefore r v grp` (**H_ALL**): every change of node `v` comes no earlier than
  some change of every pin `k ∈ grp` (arc indices of the netlist).
* `potMax_sound`: a potential certificate in which a "max node" `v` (non-empty
  group `M v`) needs only ONE arc of its group to satisfy the arc condition
  (and its other in-arcs none), is sound for every `Run` satisfying H_ALL at
  its max nodes. Python may choose the arc: any choice that passes is sound,
  and the best choice is the max over the group.
* `cel_needs_pin`: H_ALL is a THEOREM of the bounded-delay semantics for a
  C-element node, per pin: if the node's function holds its value whenever
  pin `ka` and the feedback pin `kf` both show it (`maj`-style hold, any
  C-element LUT with reset inactive), the output and pin `ka` agree at the
  origin, and H_FB_FIRST holds in `Run` form (at each output change the
  feedback pin already reads the output: B's C2, discharged by rule Rc via
  `FbFirstRt.fbFirst_of_resp`), then every output change needs a prior change
  of pin `ka`. No "at rest" assumption on the OTHER pins is needed.
* `allBefore_of_pins`: the per-pin lemma over a whole group.

Consequence for rule X (`rules10l.py`, rows Xm): the z driver `D` just fired, so
all its handshake inputs agree with it (group = all of them; this is
`cel_next_needs_all`'s content, now a max over the group checked by tcheck);
each other root `r` of an OR'ed acknowledge is a link controller whose
request pin is low with its output at the launch (**H_REQ_AGREE**: the steer's
request has returned to zero before `D`'s return to zero, which it causes;
a protocol fact), so its group is that one pin. H_OR_IDLE (all of `r`'s inputs
at rest) is no longer used.

Core Lean only.
-/

namespace Formal.Timing.MaxNode
open Formal.Timing Formal.Net

/-- **H_ALL** at node `v` for the pin group `grp` (arc indices). -/
def AllBefore {net : Netlist} {sig : Nat → Trace} (r : Run net sig) (v : Nat) (grp : List Nat) :
    Prop :=
  ∀ t, changes (sig v) t → ∀ k ∈ grp, ∃ s, s ≤ t ∧ changes (r.pin k) s

/-- The certificate with max nodes: `M v = []` is an ordinary (OR) node, every
in-arc checked as in `PotOK`; `M v ≠ []` is a max node, ONE arc of its group
must satisfy the arc condition. -/
def PotMaxOK (net : Netlist) (M : Nat → List Nat) (pot : Nat → Nat) : Prop :=
  (∀ a ∈ net.arcs, a.dst = 0 ∨ M a.dst ≠ [] ∨
      (pot a.dst ≤ rho pot a.src + a.lo ∧ (a.lo = 0 → a.src < a.dst))) ∧
  (∀ v, v ≠ 0 → M v ≠ [] → ∃ k ∈ M v, ∃ a, net.arcs[k]? = some a ∧
      pot v ≤ rho pot a.src + a.lo ∧ (a.lo = 0 → a.src < v))

/-- **Soundness of a max-node certificate.** -/
theorem potMax_sound {net : Netlist} {M : Nat → List Nat} {pot : Nat → Nat}
    (hp : PotMaxOK net M pot) {sig : Nat → Trace} (r : Run net sig)
    (hall : ∀ v, v ≠ 0 → M v ≠ [] → AllBefore r v (M v)) :
    ∀ t v, v ≠ 0 → changes (sig v) t → pot v ≤ t := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t iht =>
  intro v
  induction v using Nat.strongRecOn with
  | ind v ihv =>
  intro hv hc
  -- the common step: an arc `a` (index k) into the bound for `v`, whose pin changed at `s ≤ t`
  have step : ∀ k a s, net.arcs[k]? = some a → s ≤ t → changes (r.pin k) s →
      pot v ≤ rho pot a.src + a.lo → (a.lo = 0 → a.src < v) → pot v ≤ t := by
    intro k a s hk hst hpk hle hz
    obtain ⟨s', hs', hsl⟩ := pin_cause (r.bd k a hk) (r.quiet k a hk) hpk
    by_cases hs0 : a.src = 0
    · simp only [rho, hs0, ite_true] at hle; omega
    · simp only [rho, hs0, ite_false] at hle
      by_cases hlt : s' < t
      · have := iht s' hlt a.src hs0 hs'; omega
      · have e1 : s' = t := by omega
        have hlo : a.lo = 0 := by omega
        subst e1
        have := ihv a.src (hz hlo) hs0 hs'; omega
  by_cases hM : M v = []
  · obtain ⟨k, a, hk, hd, hpc⟩ := r.node_changes hv hc
    rcases hp.1 a (List.mem_of_getElem? hk) with h0 | hm | ⟨hle, hz⟩
    · exact absurd (hd ▸ h0) hv
    · exact absurd (hd ▸ hM) hm
    · rw [hd] at hle hz
      exact step k a t hk (Nat.le_refl t) hpc hle hz
  · obtain ⟨k, hkM, a, hk, hle, hz⟩ := hp.2 v hv hM
    obtain ⟨s, hst, hpk⟩ := hall v hv hM t hc k hkM
    exact step k a s hk hst hpk hle hz

/-- **A C-element output needs every agreeing pin to move first** (H_ALL from
the bounded-delay semantics, per pin). Hypotheses:
* `hhold`: the node function keeps `w` while pin `ka` and the feedback pin `kf`
  both read `w` (true of `maj` and of every C-element LUT with reset inactive);
* `h0`, `ha0`: output and pin `ka` both read `w` at the origin;
* `hfb` (H_FB_FIRST, Run form): at each output change the feedback pin
  already reads the output's current value. -/
theorem cel_needs_pin {net : Netlist} {sig : Nat → Trace} (r : Run net sig) {v : Nat}
    (hv : v ≠ 0) {ka kf : Nat} {w : Bool}
    (hhold : ∀ x : Nat → Bool, x ka = w → x kf = w → r.g v x = w)
    (h0 : sig v 0 = w) (ha0 : r.pin ka 0 = w)
    (hfb : ∀ u, changes (sig v) u → r.pin kf (u + 1) = sig v u) :
    ∀ t, changes (sig v) t → ∃ s, s ≤ t ∧ changes (r.pin ka) s := by
  intro t hc
  apply Classical.byContradiction; intro hn
  have hka : ∀ u, u ≤ t + 1 → r.pin ka u = w := by
    have := const_before (i := r.pin ka) (a := t + 1) (fun s hs => by
      apply Classical.byContradiction; intro h; exact hn ⟨s, by omega, hs⟩)
    intro u hu; rw [this u hu, ha0]
  have hv' : ∀ u, u ≤ t + 1 → sig v u = w := by
    intro u
    induction u with
    | zero => intro _; exact h0
    | succ u ih =>
      intro hu
      have hu' : sig v u = w := ih (by omega)
      apply Classical.byContradiction; intro hne
      have hch : changes (sig v) u := by
        intro e; exact hne (e ▸ hu')
      have hf : r.pin kf (u + 1) = w := by rw [hfb u hch, hu']
      apply hne
      rw [r.node v hv (u + 1)]
      exact hhold _ (hka (u + 1) hu) hf
  exact hc ((hv' t (by omega)).trans (hv' (t + 1) (Nat.le_refl _)).symm)

/-- The per-pin lemma over a group: H_ALL for every pin of `grp` that agrees
with the output at the origin and has the hold property. -/
theorem allBefore_of_pins {net : Netlist} {sig : Nat → Trace} (r : Run net sig) {v : Nat}
    (hv : v ≠ 0) {grp : List Nat} {kf : Nat} {w : Bool}
    (hhold : ∀ ka ∈ grp, ∀ x : Nat → Bool, x ka = w → x kf = w → r.g v x = w)
    (h0 : sig v 0 = w) (ha0 : ∀ ka ∈ grp, r.pin ka 0 = w)
    (hfb : ∀ u, changes (sig v) u → r.pin kf (u + 1) = sig v u) :
    AllBefore r v grp := by
  intro t hc k hk
  exact cel_needs_pin r hv (hhold k hk) h0 (ha0 k hk) hfb t hc

/-! ## The C-element function holds: `maj` on (pin a, pin b, feedback) -/

/-- The 2-input C-element as a node function of three pins. -/
def celFn (ka kb kf : Nat) (x : Nat → Bool) : Bool :=
  (x ka && x kb) || (x kf && (x ka || x kb))

theorem celFn_hold_a (ka kb kf : Nat) (w : Bool) (x : Nat → Bool) (h1 : x ka = w) (h2 : x kf = w) :
    celFn ka kb kf x = w := by
  unfold celFn; rw [h1, h2]; cases w <;> simp

theorem celFn_hold_b (ka kb kf : Nat) (w : Bool) (x : Nat → Bool) (h1 : x kb = w) (h2 : x kf = w) :
    celFn ka kb kf x = w := by
  unfold celFn; rw [h1, h2]; cases w <;> simp

/-- **Necessity of the agreement premise** (why H_OR_IDLE's "all inputs" can be
dropped but the agreeing pin cannot be guessed): a C-element half-excited at
the origin (pin `a` already at the target value) fires on pin `b` alone. With
`a = b = 1` held from time 1 and feedback `0`, the output is `1` at time 1
although pin `a` never changes after the origin's value `true`. -/
theorem celFn_half_excited :
    celFn 0 1 2 (fun k => k == 0 || k == 1) = true ∧ celFn 0 1 2 (fun k => k == 0) = false := by
  decide

end Formal.Timing.MaxNode
