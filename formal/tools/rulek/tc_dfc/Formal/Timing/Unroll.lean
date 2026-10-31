import Formal.Timing.Semantics

/-!
# Earliest change in a CYCLIC netlist, from a checked potential (probe C-10h)

10a's checker (`Checker.lean`, `WinArray.lean`) computes exact windows on a DAG.
The late side of rules F, R and H (C-10e/10g) is a path that may cross state
nodes and loop back: its graph is cyclic. 10g chose that path by a Python
Dijkstra (H_EXTRACT_MIN, unverified). An "unrolled DAG" of a cyclic graph is
either infinite or cut at a depth that is itself an untrusted choice. This file
replaces both by a **certificate**: an untrusted potential `pot : Nat → Nat`
(Python proposes Dijkstra's distances) that the checker verifies arc by arc.

`pot_sound`: for ANY netlist (cycles allowed; 10a's `Run`, unchanged, with the
launch at node 0), if every arc `a` with `a.dst ≠ 0` satisfies

    pot a.dst ≤ rho pot a.src + a.lo        (rho: 0 at the launch, else pot)
    a.lo = 0 → a.src < a.dst               (no zero-delay cycle: well-founded)

then every change of a node `v ≠ 0` happens at a time `≥ pot v`. Taking
`pot = min(dist, C)` (capped shortest-path distances on the `lo` delays) always
satisfies the check, and then the bound is the shortest-path distance: the
earliest window of the infinite unrolling of the graph. Whatever Python
proposes, a potential that passes the check is a sound lower bound, so a wrong
(or adversarial) choice can only make the bound smaller or the check FAIL,
never an unsound PASS. (Tightness, i.e. that the bound equals the earliest
change, is NOT proved here; it is checked empirically against Dijkstra.)

The `Run` semantics on a cyclic netlist is the same structure as 10a's
(H_LAUNCH, H_BOUNDED_DELAY, H_QUIESCENT, H_LOCAL, H_ZERO_DELAY_FN); nothing in it
requires a DAG. The only fact used is that a node other than the launch changes
only if one of its input pins does (`Run.node_changes`) and a pin changes only
`≥ lo` after a change of its source (`pin_cause` below).
-/

namespace Formal.Timing
open Formal.Net

/-- A bounded-delay pin that changes at `t` copies a change of its source that
happened at some `s` with `s + lo ≤ t` (H_BOUNDED_DELAY + H_QUIESCENT). -/
theorem pin_cause {lo hi t : Nat} {i o : Trace} (hbd : BoundedDelay lo hi i o)
    (h0 : o 0 = i 0) (ht : changes o t) : ∃ s, changes i s ∧ s + lo ≤ t := by
  apply Classical.byContradiction; intro hn
  have hw : ∀ s, changes i s → t + 1 - lo ≤ s := by
    intro s hs; apply Classical.byContradiction; intro h; exact hn ⟨s, hs, by omega⟩
  have ib : ∀ s, s ≤ t + 1 - lo → i s = i 0 := const_before hw
  have ob : ∀ s, s ≤ t + 1 → o s = i 0 := by
    intro s
    induction s with
    | zero => intro _; exact h0
    | succ s ih =>
      intro hs
      by_cases hc : o s = o (s + 1)
      · rw [← hc]; exact ih (by omega)
      · obtain ⟨d, hld, _, _, heq⟩ := hbd.cause s hc
        rw [heq]; exact ib _ (by omega)
  exact ht ((ob t (by omega)).trans (ob (t + 1) (by omega)).symm)

/-- The launch counts 0 (its only change is at time 0, H_LAUNCH). -/
def rho (pot : Nat → Nat) (x : Nat) : Nat := if x = 0 then 0 else pot x

/-- The certificate condition, arc by arc (arcs into the launch are ignored:
the launch is not driven in `Run`). -/
def PotOK (net : Netlist) (pot : Nat → Nat) : Prop :=
  ∀ a ∈ net.arcs, a.dst = 0 ∨ (pot a.dst ≤ rho pot a.src + a.lo ∧ (a.lo = 0 → a.src < a.dst))

/-- Executable form of `PotOK`. -/
def potArcOK (pot : Nat → Nat) (a : Arc) : Bool :=
  a.dst == 0 || (decide (pot a.dst ≤ rho pot a.src + a.lo) && (a.lo != 0 || decide (a.src < a.dst)))

def potOK (arcs : List Arc) (pot : Nat → Nat) : Bool := arcs.all (potArcOK pot)

theorem potArcOK_iff (pot : Nat → Nat) (a : Arc) : potArcOK pot a = true ↔
    (a.dst = 0 ∨ (pot a.dst ≤ rho pot a.src + a.lo ∧ (a.lo = 0 → a.src < a.dst))) := by
  simp only [potArcOK, Bool.or_eq_true, beq_iff_eq, Bool.and_eq_true, decide_eq_true_eq,
    bne_iff_ne, ne_eq]
  constructor
  · rintro (h | ⟨h1, h2 | h2⟩)
    · exact Or.inl h
    · exact Or.inr ⟨h1, fun h => absurd h h2⟩
    · exact Or.inr ⟨h1, fun _ => h2⟩
  · rintro (h | ⟨h1, h2⟩)
    · exact Or.inl h
    · by_cases hl : a.lo = 0
      · exact Or.inr ⟨h1, Or.inr (h2 hl)⟩
      · exact Or.inr ⟨h1, Or.inl hl⟩

theorem potOK_iff (net : Netlist) (pot : Nat → Nat) : potOK net.arcs pot = true ↔ PotOK net pot := by
  simp only [potOK, List.all_eq_true, PotOK, potArcOK_iff]

/-- **Soundness of a checked potential on a cyclic netlist.** In every `Run`,
every change of a node other than the launch happens no earlier than its
potential. (Strong induction on the time, then on the node index for the
zero-delay arcs.) -/
theorem pot_sound {net : Netlist} {pot : Nat → Nat} (hp : PotOK net pot)
    {sig : Nat → Trace} (r : Run net sig) :
    ∀ t v, v ≠ 0 → changes (sig v) t → pot v ≤ t := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t iht =>
  intro v
  induction v using Nat.strongRecOn with
  | ind v ihv =>
  intro hv hc
  obtain ⟨k, a, hk, hd, hpc⟩ := r.node_changes hv hc
  obtain ⟨s, hs, hsl⟩ := pin_cause (r.bd k a hk) (r.quiet k a hk) hpc
  rcases hp a (List.mem_of_getElem? hk) with h0 | ⟨hle, hz⟩
  · exact absurd (hd ▸ h0) hv
  · rw [hd] at hle
    by_cases hs0 : a.src = 0
    · simp only [rho, hs0, ite_true] at hle; omega
    · simp only [rho, hs0, ite_false] at hle
      by_cases hst : s < t
      · have := iht s hst a.src hs0 hs; omega
      · have hst' : s = t := by omega
        have hlo : a.lo = 0 := by omega
        have hlt : a.src < v := hd ▸ hz hlo
        subst hst'
        have := ihv a.src hlt hs0 hs; omega

/-- The same through the executable check. -/
theorem potOK_sound {net : Netlist} {pot : Nat → Nat} (hp : potOK net.arcs pot = true)
    {sig : Nat → Trace} (r : Run net sig) :
    ∀ t v, v ≠ 0 → changes (sig v) t → pot v ≤ t :=
  pot_sound ((potOK_iff net pot).1 hp) r

end Formal.Timing
