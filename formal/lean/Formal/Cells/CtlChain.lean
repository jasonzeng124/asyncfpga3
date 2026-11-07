import Formal.Cells.SpecFbChain
import Formal.Timing.SpecLoop

/-!
# Formal.Cells.CtlChain — sound lower bounds on when a node can change: controlling chains (THE Spec semantics)

Shard B, 2026-11-07, toward the environment premise hA of the C-element cell theorems (S4).

## Problem, plainly
C's relative-timing orders ("c fires before b", tools/huff/out_rt_pairs.txt) need, for each order, a LOWER bound on
when the re-enabling node b can change after a common cause A. C's time-separation tool (tools/huff/tse) computes
one from "necessary predecessors" judged on zero-delay values: not sound. Here is the sound form in the frozen
Spec's semantics (collapsed gate relation `CGateOK`, routed composite pin delays): a gate whose INIT is `w`
whenever pin `j` reads `b` (its tied pins at their constants) keeps output `w` as long as `j`'s source shows `b`,
delayed by the pin's composite delay band. Chained, a node held by a chain from the cause cannot change before the
cause's change plus the chain's summed LOWER delays, in every behaviour, with no assumption on any other node.

## Proved (standard axioms)
* `Holds x m b n w S lo hi`: `n = w` on `[a + hi, e + lo]` (from `S`) whenever `m = b` on `[a, e]`.
* `holds_of_ctl`: a collapsed gate with an INIT controlling fact on pin `j` gives `Holds` for its pin band.
* `ctlfact` (decidable over the `2^k` INIT addresses) and `ctl_of_ctlfact`.
* `chain_holds`: composition along a list of steps: if the chain's first node shows `b0` on `[a, e]` and
  `a ≥` every step's start, the last node shows its value on `[a + Σhi, e + Σlo]`.
* Reading for an order: with `e` = the cause's change time A, the chain's end cannot change before `A + Σlo`.

## Not shown
The upper (forcing) half of an order (c fires by A + HI); that the cause node held its value from `a`; any instance.
-/

namespace Formal.Cells.CtlChain

open Formal.Target Formal.Timing.SpecChain Formal.Cells.SpecFbChain

/-- Node `n` shows `w` on `[a + hi, e + lo]` (from `S` on) whenever node `m` shows `b` on `[a, e]`. -/
def Holds (x : Beh) (m : Nat) (b : Bool) (n : Nat) (w : Bool) (S lo hi : Nat) : Prop :=
  ∀ a e, (∀ t, a ≤ t → t ≤ e → x m t = b) → ∀ t, S ≤ t → a + hi ≤ t → t ≤ e + lo → x n t = w

/-- **A controlled gate holds.** If the INIT is `w` at every address whose pin `j` is `b` and whose tied pins are
at their constants, the output is `w` while pin `j`'s source shows `b`, through the pin's band. -/
theorem holds_of_ctl {p : DelayPar} {c : ℚ} {g : Gate} {src : Nat → Nat} {arcs : Nat → List Arc} {S : Nat}
    {x : Beh} (hg : CGateOK p c g src arcs S x) {lo hi : Nat → Nat} (hb : CBands p c g.k arcs lo hi)
    {j : Nat} (hj : j < g.k) (b w : Bool) (held ov : Nat → Bool)
    (hf : ∀ v : Nat → Bool, (∀ i, i < g.k → held i = true → v i = ov i) → v j = b →
      g.init.testBit (addr g.k v) = w)
    (hh : ∀ i, i < g.k → held i = true → ∀ t, x (src i) t = ov i) :
    Holds x (src j) b g.out w S (lo j) (hi j) := by
  obtain ⟨F, -, hF⟩ := hg
  intro a e hm t hS h1 h2
  obtain ⟨r, y⟩ := hF t hS
  have d := hb j hj _ (r j hj).2
  have e1 := (r j hj).1
  rw [y]
  exact hf _ (fun i hi hh' => hh i hi hh' _) (hm _ (by omega) (by omega))

/-- The controlling fact at every INIT address (tied pins `held` at `ov`). -/
def ctlfact (k init j : Nat) (b w : Bool) (held ov : Nat → Bool) : Bool :=
  (List.range (2 ^ k)).all fun a =>
    !(((List.range k).all fun i => !held i || (a.testBit i == ov i)) && (a.testBit j == b)) ||
      (init.testBit a == w)

theorem ctl_of_ctlfact {k init j : Nat} {b w : Bool} {held ov : Nat → Bool}
    (h : ctlfact k init j b w held ov = true) (hj : j < k) :
    ∀ v : Nat → Bool, (∀ i, i < k → held i = true → v i = ov i) → v j = b → init.testBit (addr k v) = w := by
  intro v hh hv
  simp only [ctlfact, List.all_eq_true, List.mem_range] at h
  have := h _ (Formal.Timing.SpecLoop.addr_lt k v)
  have hheld : ((List.range k).all fun i => !held i || ((addr k v).testBit i == ov i)) = true := by
    simp only [List.all_eq_true, List.mem_range]
    intro i hi
    rw [Formal.Timing.SpecLoop.addr_testBit k v i hi]
    cases hc : held i
    · simp
    · simp [hh i hi hc]
  rw [hheld, Formal.Timing.SpecLoop.addr_testBit k v j hj, hv] at this
  simpa using this

/-- One step of a chain: the next node, its held value, and its relation's start and pin band. -/
structure Step where
  n : Nat
  w : Bool
  S : Nat
  lo : Nat
  hi : Nat

/-- Every step holds, from the previous node and value. -/
def ChainOK (x : Beh) : Nat → Bool → List Step → Prop
  | _, _, [] => True
  | m, b, s :: ss => Holds x m b s.n s.w s.S s.lo s.hi ∧ ChainOK x s.n s.w ss

def sumLo (ss : List Step) : Nat := (ss.map Step.lo).sum
def sumHi (ss : List Step) : Nat := (ss.map Step.hi).sum

/-- The node and value at the end of a chain. -/
def lastN : Nat → Bool → List Step → Nat × Bool
  | m, b, [] => (m, b)
  | _, _, s :: ss => lastN s.n s.w ss

/-- **Chains compose.** If the first node shows `b` on `[a, e]` and `a` is at least every step's start, the
chain's last node shows its value on `[a + Σhi, e + Σlo]`. -/
theorem chain_holds (x : Beh) :
    ∀ (ss : List Step) (m : Nat) (b : Bool), ChainOK x m b ss → ∀ a e, (∀ s ∈ ss, s.S ≤ a) →
      (∀ t, a ≤ t → t ≤ e → x m t = b) →
      ∀ t, a + sumHi ss ≤ t → t ≤ e + sumLo ss → x (lastN m b ss).1 t = (lastN m b ss).2
  | [], m, b, _, a, e, _, hm, t, h1, h2 => by simp [sumHi, sumLo] at h1 h2; exact hm t h1 h2
  | s :: ss, m, b, ⟨hs, hc⟩, a, e, hS, hm, t, h1, h2 => by
    simp only [sumHi, sumLo, List.map_cons, List.sum_cons] at h1 h2
    have hS0 := hS s List.mem_cons_self
    have step : ∀ t, a + s.hi ≤ t → t ≤ e + s.lo → x s.n t = s.w := fun t u1 u2 =>
      hs a e hm t (by omega) u1 u2
    have := chain_holds x ss s.n s.w hc (a + s.hi) (e + s.lo)
      (fun s' h' => le_trans (hS s' (List.mem_cons_of_mem _ h')) (Nat.le_add_right _ _)) step t
      (by unfold sumHi; omega) (by unfold sumLo; omega)
    simpa [lastN] using this

end Formal.Cells.CtlChain
