import Formal.Timing.MaxNode

/-!
# Probe C-10l: crediting a shared prefix once, on the cyclic late side

C-10b's `Rules.race_sound_clean` credits the shared prefix of a two-path race
(both sides launched at a common node `X`) under **H_CLEAN_EDGE** at `X`, and
`Rules.prefix_credit_needs_clean_edge` shows the credit is unsound without it.
That is a DAG statement. tcheck's late sides (C-10h) are certificates on the
cyclic routed graph, and rule X/Xi's critical late path is a LOOP:

    D → (DACK ripple) → X → fork → … → D's input → D → (DACK ripple) → X → z pin

whose first pass `D → X` is also the whole of the data side's long part
(`D → X → z pin → u → u's feedback`). Without credit the band charges that
ripple twice: at 1.155 on the data side and at 0.772 on the late side.

**The split.** Let `e` be the late-side node of `X` in phase 0 (the response to
the launch at `D`), and `τ` the time of `X`'s one edge (H_CLEAN_EDGE). Every
causal chain to a late node either passes through `e`, and then starts no
earlier than `τ`, or avoids `e`. So with two certificates,

* `potB`: a potential for the late netlist with `e`'s out-arcs dropped,
* `potA`: a potential for the late netlist "launched at `e`" (arcs out of `e`
  count from 0, arcs out of the real launch are dropped),

every change of a node `v` happens no earlier than `min (potB v) (τ + potA v)`
(`pot2_sound`). With the data side split the same way (latest data `lD` from
`D`, latest data `lA` from `X`), the race holds if `lD + setup ≤ potB(target)`
and `lA + setup ≤ potA(target)` (tcheck `Tcheck.xverdict_sound`): the shared
prefix's `hi` and `lo` never meet in one inequality.

Max nodes (`MaxNode`) combine with the split unchanged: a max node needs ONE
arc of its group that satisfies both certificates' conditions.

Hypotheses (all in the statement):
* `Run` (10a: H_LAUNCH, H_BOUNDED_DELAY, H_QUIESCENT, H_LOCAL, H_ZERO_DELAY_FN);
* **H_CLEAN_EDGE(X)** (`hcl`): node `e` changes at most once, at `τ`. Physical
  for a wire (one sample per wire, `Rules.shift_window`); for a LUT output it
  holds under H_KLEENE_LUT when one input changes, or several in the same
  direction through a unate function (the DACK ripple's ANDs, a steer's OR
  with the inactive branch held low). C-10b's counterexample shows it is
  necessary;
* H_ALL at the max nodes (`MaxNode.cel_needs_pin` derives it).

Core Lean only.
-/

namespace Formal.Timing.SharedPrefix
open Formal.Timing Formal.Net Formal.Timing.MaxNode

/-- The `potB` condition on arc `a` into `v`: vacuous for arcs out of `e`. -/
def CondB (e : Nat) (potB : Nat → Nat) (v : Nat) (a : Arc) : Prop :=
  a.src = e ∨ potB v ≤ rho potB a.src + a.lo

/-- The `potA` condition on arc `a` into `v`: vacuous for arcs out of the real
launch; arcs out of `e` count from 0. -/
def CondA (e : Nat) (potA : Nat → Nat) (v : Nat) (a : Arc) : Prop :=
  a.src = 0 ∨ potA v ≤ (if a.src = e then 0 else potA a.src) + a.lo

/-- The two-potential certificate, with max nodes `M`. -/
def Pot2OK (net : Netlist) (M : Nat → List Nat) (e : Nat) (potB potA : Nat → Nat) : Prop :=
  (∀ a ∈ net.arcs, a.dst = 0 ∨ M a.dst ≠ [] ∨
      ((a.lo = 0 → a.src < a.dst) ∧ CondB e potB a.dst a ∧ CondA e potA a.dst a)) ∧
  (∀ v, v ≠ 0 → M v ≠ [] → ∃ k ∈ M v, ∃ a, net.arcs[k]? = some a ∧
      (a.lo = 0 → a.src < v) ∧ CondB e potB v a ∧ CondA e potA v a)

/-- **Shared-prefix credit on a cyclic netlist.** Under H_CLEAN_EDGE at `e`
(one change, at `τ`) and H_ALL at the max nodes, every change of a node other
than the launch happens no earlier than `min (potB v) (τ + potA v)`. -/
theorem pot2_sound {net : Netlist} {M : Nat → List Nat} {e : Nat} {potB potA : Nat → Nat}
    (hp : Pot2OK net M e potB potA) (he : e ≠ 0) {sig : Nat → Trace} (r : Run net sig)
    (hall : ∀ v, v ≠ 0 → M v ≠ [] → AllBefore r v (M v))
    {τ : Nat} (hcl : ∀ t, changes (sig e) t → t = τ) :
    ∀ t v, v ≠ 0 → changes (sig v) t → min (potB v) (τ + potA v) ≤ t := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t iht =>
  intro v
  induction v using Nat.strongRecOn with
  | ind v ihv =>
  intro hv hc
  have step : ∀ k a s, net.arcs[k]? = some a → s ≤ t → changes (r.pin k) s →
      (a.lo = 0 → a.src < v) → CondB e potB v a → CondA e potA v a →
      min (potB v) (τ + potA v) ≤ t := by
    intro k a s hk hst hpk hz hB hA
    obtain ⟨s', hs', hsl⟩ := pin_cause (r.bd k a hk) (r.quiet k a hk) hpk
    by_cases hs0 : a.src = 0
    · -- the real launch: s' = 0, potB's condition applies (a.src ≠ e)
      have := r.launch s' (hs0 ▸ hs')
      rcases hB with h | h
      · exact absurd (h ▸ hs0) he
      · simp only [rho, hs0, ite_true] at h; omega
    · by_cases hse : a.src = e
      · -- through the shared node: its one change is at τ
        have := hcl s' (hse ▸ hs')
        rcases hA with h | h
        · exact absurd h hs0
        · simp only [hse, ite_true] at h; omega
      · rcases hB with h | hB
        · exact absurd h hse
        rcases hA with h | hA
        · exact absurd h hs0
        simp only [rho, hs0, ite_false] at hB
        simp only [hse, ite_false] at hA
        have ih : min (potB a.src) (τ + potA a.src) ≤ s' := by
          by_cases hlt : s' < t
          · exact iht s' hlt a.src hs0 hs'
          · have e1 : s' = t := by omega
            have hlo : a.lo = 0 := by omega
            subst e1
            exact ihv a.src (hz hlo) hs0 hs'
        omega
  by_cases hM : M v = []
  · obtain ⟨k, a, hk, hd, hpc⟩ := r.node_changes hv hc
    rcases hp.1 a (List.mem_of_getElem? hk) with h0 | hm | ⟨hz, hB, hA⟩
    · exact absurd (hd ▸ h0) hv
    · exact absurd (hd ▸ hM) hm
    · rw [hd] at hz hB hA
      exact step k a t hk (Nat.le_refl t) hpc hz hB hA
  · obtain ⟨k, hkM, a, hk, hz, hB, hA⟩ := hp.2 v hv hM
    obtain ⟨s, hst, hpk⟩ := hall v hv hM t hc k hkM
    exact step k a s hk hst hpk hz hB hA

/-- Without max nodes (`M = fun _ => []`): the plain shared-prefix credit. -/
theorem pot2_sound_or {net : Netlist} {e : Nat} {potB potA : Nat → Nat}
    (hp : Pot2OK net (fun _ => []) e potB potA) (he : e ≠ 0) {sig : Nat → Trace}
    (r : Run net sig) {τ : Nat} (hcl : ∀ t, changes (sig e) t → t = τ) :
    ∀ t v, v ≠ 0 → changes (sig v) t → min (potB v) (τ + potA v) ≤ t :=
  pot2_sound hp he r (fun _ _ h => absurd rfl h) hcl

/-! ## Non-vacuity: the credit is strictly better than either certificate alone

The netlist `0 → 1 → 2 → 3` (`[10,10]` each, the "ripple" `0 → 1` and the
fork `1 → 2`) plus a short cut `1 → 3` of 1 ps: the late target `3` is 11 ps
after the launch through `1`. Without credit the data side would be charged
from 0; with credit `potA 3 = 1` counts from `X = 1`'s edge (`τ ≥ 10`), and
`potB 3` (arcs out of `1` dropped) is unbounded: the cap. -/

def toyNet : Netlist := ⟨[⟨0, 1, 10, 10⟩, ⟨1, 2, 10, 10⟩, ⟨2, 3, 10, 10⟩, ⟨1, 3, 1, 1⟩]⟩

def toyPotB : Nat → Nat := fun v => if v = 1 then 10 else 1000
def toyPotA : Nat → Nat := fun v => if v = 1 then 0 else if v = 2 then 10 else 1

theorem toy_ok : Pot2OK toyNet (fun _ => []) 1 toyPotB toyPotA := by
  refine ⟨?_, fun _ _ h => absurd rfl h⟩
  intro a ha
  simp only [toyNet, List.mem_cons, List.mem_nil_iff, or_false] at ha
  rcases ha with rfl | rfl | rfl | rfl <;>
    simp [CondB, CondA, rho, toyPotB, toyPotA]

end Formal.Timing.SharedPrefix
