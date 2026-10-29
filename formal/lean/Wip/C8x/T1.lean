import Formal.Timing.Checker
import Formal.Net.Ops
namespace Formal.Net.CapstoneRefine
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Timing

/-! ## Zero-delay evaluation of a netlist -/

/-- The largest `hi` of an arc list. -/
def hmaxL : List Arc → Nat
  | [] => 0
  | a :: l => max a.hi (hmaxL l)

theorem hi_le_hmaxL : ∀ {l : List Arc} {a : Arc}, a ∈ l → a.hi ≤ hmaxL l
  | b :: l, a, h => by
    rcases List.mem_cons.mp h with h | h
    · subst h; exact Nat.le_max_left _ _
    · have := hi_le_hmaxL h; simp only [hmaxL]; omega

/-- The netlist's value with every delay set to zero: launch node at `b`, node `v` = `g v` of
its sources' zero-delay values (arcs not into `v` are read as `false`; `g v` ignores them under
H_LOCAL). -/
def zdEval (net : Netlist) (g : Nat → (Nat → Bool) → Bool) (b : Bool) (v : Nat) : Bool :=
  if v = 0 then b else
  g v (fun k => match net.arcs[k]? with
    | some a => if h : a.src < v then zdEval net g b a.src else false
    | none => false)
termination_by v
decreasing_by exact h

theorem zdEval_zero (net : Netlist) (g : Nat → (Nat → Bool) → Bool) (b : Bool) :
    zdEval net g b 0 = b := by
  rw [zdEval]; simp

theorem zdEval_ne (net : Netlist) (g : Nat → (Nat → Bool) → Bool) (b : Bool) {v : Nat}
    (hv : v ≠ 0) : zdEval net g b v = g v (fun k => match net.arcs[k]? with
      | some a => if a.src < v then zdEval net g b a.src else false
      | none => false) := by
  rw [zdEval]; simp only [hv, dite_false]
  congr 1

/-! ## R2: settling to the zero-delay value -/

/-- **Every node of a run reaches its zero-delay value** by `1 + v * hmaxL net.arcs` and keeps
it (single launch). -/
theorem run_settles {net : Netlist} (hwf : net.WF) {sig : Nat → Trace} (r : Run net sig) :
    ∀ v t, 1 + v * hmaxL net.arcs ≤ t → sig v t = zdEval net r.g (sig 0 1) v := by
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
  intro t ht
  by_cases hv : v = 0
  · subst hv
    rw [zdEval_zero]
    exact const_from (i := sig 0) (c := 1) (fun s hs => by have := r.launch s hs; omega) t
      (by omega)
  · rw [r.node v hv t, zdEval_ne net r.g _ hv]
    apply r.local_ v
    intro k a hk hd
    have hlt : a.src < v := hd ▸ (hwf a (List.mem_of_getElem? hk)).1
    simp only [hk, hlt, ↓reduceIte]
    have hhi : a.hi ≤ hmaxL net.arcs := hi_le_hmaxL (List.mem_of_getElem? hk)
    have hm : a.src * hmaxL net.arcs + hmaxL net.arcs ≤ v * hmaxL net.arcs := by
      have := Nat.mul_le_mul_right (hmaxL net.arcs) (show a.src + 1 ≤ v by omega)
      rw [Nat.succ_mul] at this; exact this
    have hset : stableOn (sig a.src) (t - a.hi) t := by
      intro s h1 _
      rw [ih a.src hlt s (by omega), ih a.src hlt (t - a.hi) (by omega)]
    rw [(r.bd k a hk).settle t (by omega) hset]
    exact ih a.src hlt t (by omega)

/-- **A node that is quiet from `t` on holds its zero-delay value at `t`.** -/
theorem settled_of_quiet {net : Netlist} (hwf : net.WF) {sig : Nat → Trace} (r : Run net sig)
    {v t : Nat} (hq : ∀ s, changes (sig v) s → s < t) :
    sig v t = zdEval net r.g (sig 0 1) v := by
  have hc := const_from hq (max t (1 + v * hmaxL net.arcs)) (Nat.le_max_left _ _)
  rw [← hc]
  exact run_settles hwf r v _ (Nat.le_max_right _ _)

end Formal.Net.CapstoneRefine
