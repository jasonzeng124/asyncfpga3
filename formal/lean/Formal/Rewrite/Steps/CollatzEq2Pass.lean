import Formal.Rewrite.Steps.ScriptSound
import Formal.Rewrite.Rename
import Formal.Net.CollatzHw
import Formal.Rewrite.CollatzPreeq2Hw

/-!
# Formal.Rewrite.Steps.CollatzEq2Pass — research's collatz pre_eq2 as a checked script of local steps (shard A, 2026-11-19)

**Problem, plainly.** research's `pre_eq2.py` changes collatz's loop test from `n' == 1` (on the loop's update
`n'`) to `n == 2` (on the loop's value `n`). Does the rewritten handshake graph return the same as the original on
every input, whatever the schedule, without a per-program proof against the C?

**Proved** (`pass_forward`, `pass_backward`, Lean, standard axioms): on research's original collatz import
(`Formal.Net.CollatzHw`, the fixture of A6) and research's `collatz_preeq2.mlir` import
(`Formal.Rewrite.CollatzPreeq2Hw`): from any store with tokens only on the two input channels (`n`, start), every
complete run of either graph is matched by a complete run of the other, with the same tokens on the result channel
(and on every channel outside the rewrite's private channels, renamed).

**How.** No C, no symbolic execution. Two scripts of local steps, each checked by `runScript` (Lean evaluates it):
* `s1` takes the ORIGINAL to a normal form: fold the step's three regions into one comp (reorder, absorb, reorder,
  absorb, reorder, forkjoin), move the fork after the step before it (forkcomm), fold the test's copy of the step into
  the test (absorb), replace the test `step(n) == 1` by `n == 2` (ident: `colIdent`, the collatz identity, any width
  `w >= 3`), drop the dead sinks;
* `s2` takes the REWRITTEN graph to a normal form (forksplit, the same folding, drops);
* the two normal forms are the same graph up to a channel bijection `fp P` and a rule order `fp T` (`renCheck`,
  found by rules_iso.py, checked here by `decide +kernel`).
`runScript_sound` (any rule list, any accepted script) does the rest. A wrong script makes `runScript` return
`none`.

**Not covered:** token level only (no gates, delays); dfimport (MLIR to rules) is outside Lean.
-/

namespace Formal.Rewrite.Steps.CollatzEq2Pass

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp Formal.Rewrite.Steps

/-- Original collatz (test `n' == 1`) to the normal form. -/
def s1 : List Step := [.reorder 19 [26, 34, 27], .absorb 13 19, .reorder 19 [26, 23, 34], .absorb 18 19,
  .reorder 19 [23, 24, 25, 26], .forkjoin 12 19, .forkcomm 12 20 49 50, .absorb 32 22, .ident 22 32,
  .drop 32, .drop 19, .drop 18, .drop 13]

/-- Rewritten collatz (test `n == 2`) to the normal form. -/
def s2 : List Step := [.forksplit 12 4 48, .reorder 19 [26, 35, 28], .absorb 13 19, .reorder 19 [26, 23, 35],
  .absorb 18 19, .reorder 19 [23, 24, 25, 26], .forkjoin 31 19, .drop 19, .drop 18, .drop 13]

def r1 : Res := (runScript Formal.Net.CollatzHw.rules s1).getD ([], [], [])
def r2 : Res := (runScript Formal.Rewrite.CollatzPreeq2Hw.rules s2).getD ([], [], [])

theorem h1 : runScript Formal.Net.CollatzHw.rules s1 = some r1 := by decide +kernel
theorem h2 : runScript Formal.Rewrite.CollatzPreeq2Hw.rules s2 = some r2 := by decide +kernel

theorem S1 : Sound Formal.Net.CollatzHw.rules r1.1 r1.2.1 r1.2.2 := runScript_sound h1
theorem S2 : Sound Formal.Rewrite.CollatzPreeq2Hw.rules r2.1 r2.2.1 r2.2.2 := runScript_sound h2

def P : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 28, 29, 30, 31, 32, 33, 34, 35, 49, 36, 50, 37, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 27]
def Pi : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 50, 27, 28, 29, 30, 31, 32, 33, 34, 36, 38, 39, 40, 41, 42, 43, 44, 45, 46, 47, 48, 49, 35, 37]
def T : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 28, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27]
def Ti : List Nat := [0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 17]

theorem hP : fpCheck P Pi = true := by decide +kernel
theorem hPi : fpCheck Pi P = true := by decide +kernel
theorem hT : fpCheck T Ti = true := by decide +kernel
theorem hTi : fpCheck Ti T = true := by decide +kernel
theorem hRen : renCheck r1.1 r2.1 P Ti = true := by decide +kernel

/-- Every channel a script needs empty is an internal channel (not an input). -/
theorem pre1_int : ∀ c ∈ r1.2.1, 2 ≤ c := by decide +kernel
theorem pre2_int : ∀ c ∈ r2.2.1, 2 ≤ c := by decide +kernel
/-- The result channel is outside both scripts' private channels and is renamed to research's result channel. -/
theorem out1 : Formal.Net.CollatzHw.chOut ∉ r1.2.2 := by decide +kernel
theorem out2 : Formal.Rewrite.CollatzPreeq2Hw.chOut ∉ r2.2.2 := by decide +kernel
theorem out_maps : fp P Formal.Net.CollatzHw.chOut = Formal.Rewrite.CollatzPreeq2Hw.chOut := by decide +kernel

/-- The renaming fixes the inputs and keeps internal channels internal. -/
theorem fix_in (Q : List Nat) (hQ : (List.range Q.length).all (fun c => if c < 2 then Q.getD c c == c
    else decide (2 ≤ Q.getD c c)) = true) : ∀ c, (c < 2 → fp Q c = c) ∧ (2 ≤ c → 2 ≤ fp Q c) := by
  intro c
  unfold fp
  by_cases hc : c < Q.length
  · rw [if_pos hc]
    have := List.all_eq_true.mp hQ c (List.mem_range.mpr hc)
    by_cases h2 : c < 2
    · simp only [h2, ite_true, beq_iff_eq] at this; exact ⟨fun _ => this, fun h => absurd h (by omega)⟩
    · simp only [h2, ite_false, decide_eq_true_eq] at this; exact ⟨fun h => absurd h h2, fun _ => this⟩
  · rw [if_neg hc]; exact ⟨fun _ => rfl, fun h => h⟩

theorem fixP : ∀ c, (c < 2 → fp P c = c) ∧ (2 ≤ c → 2 ≤ fp P c) := fix_in P (by decide +kernel)
theorem fixPi : ∀ c, (c < 2 → fp Pi c = c) ∧ (2 ≤ c → 2 ≤ fp Pi c) := fix_in Pi (by decide +kernel)

theorem ren_input {Q : List Nat} (hQ : ∀ c, (c < 2 → fp Q c = c) ∧ (2 ≤ c → 2 ≤ fp Q c)) {σ0 : Store Nat Nat}
    (h0 : ∀ ch, 2 ≤ ch → σ0 ch = []) : renS (fp Q) σ0 = σ0 := by
  funext c
  simp only [renS]
  by_cases h : c < 2
  · rw [(hQ c).1 h]
  · rw [h0 _ ((hQ c).2 (by omega)), h0 c (by omega)]

/-- **pre_eq2 forward.** Every complete run of the original collatz graph from the inputs has a complete run of the
rewritten graph from the same inputs with the same result tokens (and the same tokens on every channel outside the
private ones, renamed by `fp P`). -/
theorem pass_forward {σ0 t : Store Nat Nat} {n : Nat} (h0 : ∀ ch, 2 ≤ ch → σ0 ch = [])
    (hr : Run (step (graph Formal.Net.CollatzHw.rules)) σ0 n t) (ht : Terminal (step (graph Formal.Net.CollatzHw.rules)) t) :
    ∃ t' m, Run (step (graph Formal.Rewrite.CollatzPreeq2Hw.rules)) σ0 m t' ∧
      Terminal (step (graph Formal.Rewrite.CollatzPreeq2Hw.rules)) t' ∧
      (∀ ch, ch ∉ r1.2.2 → fp P ch ∉ r2.2.2 → t' (fp P ch) = t ch) ∧
      t' Formal.Rewrite.CollatzPreeq2Hw.chOut = t Formal.Net.CollatzHw.chOut := by
  obtain ⟨t1, m1, run1, term1, a1⟩ := S1.fwd (fun c hc => h0 c (pre1_int c hc)) hr ht
  have run2 := run_ren (fp P) (fp Pi) (fp_inv P Pi hP) (fp_inv Pi P hPi) (fp T) (fp Ti) (fp_inv T Ti hT)
    (renCheck_ok hRen) run1
  have term2 := terminal_ren (fp P) (fp Pi) (fp_inv P Pi hP) (fp_inv Pi P hPi) (fp T) (fp Ti) (fp_inv Ti T hTi)
    (renCheck_ok hRen) term1
  rw [ren_input fixPi h0] at run2
  obtain ⟨t3, m3, run3, term3, a3⟩ := S2.symm.fwd (fun c hc => h0 c (pre2_int c hc)) run2 term2
  have key : ∀ ch, ch ∉ r1.2.2 → fp P ch ∉ r2.2.2 → t3 (fp P ch) = t ch := by
    intro ch h1' h2'
    rw [a3 _ h2']; simp only [renS, fp_inv P Pi hP]; exact a1 ch h1'
  refine ⟨t3, m3, run3, term3, key, ?_⟩
  rw [← out_maps]; exact key _ out1 (by rw [out_maps]; exact out2)

/-- **pre_eq2 backward.** Every complete run of the rewritten graph from the inputs has a complete run of the
original graph from the same inputs with the same result tokens. -/
theorem pass_backward {σ0 t' : Store Nat Nat} {n : Nat} (h0 : ∀ ch, 2 ≤ ch → σ0 ch = [])
    (hr : Run (step (graph Formal.Rewrite.CollatzPreeq2Hw.rules)) σ0 n t')
    (ht : Terminal (step (graph Formal.Rewrite.CollatzPreeq2Hw.rules)) t') :
    ∃ t m, Run (step (graph Formal.Net.CollatzHw.rules)) σ0 m t ∧ Terminal (step (graph Formal.Net.CollatzHw.rules)) t ∧
      (∀ ch, ch ∉ r1.2.2 → fp P ch ∉ r2.2.2 → t ch = t' (fp P ch)) ∧
      t Formal.Net.CollatzHw.chOut = t' Formal.Rewrite.CollatzPreeq2Hw.chOut := by
  obtain ⟨t2, m2, run2, term2, a2⟩ := S2.fwd (fun c hc => h0 c (pre2_int c hc)) hr ht
  have run1 := run_ren_back (fp P) (fp Pi) (fp_inv P Pi hP) (fp_inv Pi P hPi) (fp Ti) (renCheck_ok hRen) run2
  have term1 := terminal_ren_back (fp P) (fp Pi) (fp_inv P Pi hP) (fp_inv Pi P hPi) (fp T) (fp Ti)
    (fp_inv T Ti hT) (renCheck_ok hRen) term2
  rw [ren_input fixP h0] at run1
  obtain ⟨t0, m0, run0, term0, a0⟩ := S1.bwd (fun c hc => h0 c (pre1_int c hc)) run1 term1
  have key : ∀ ch, ch ∉ r1.2.2 → fp P ch ∉ r2.2.2 → t0 ch = t' (fp P ch) := by
    intro ch h1' h2'
    rw [a0 ch h1']; simp only [renS]; exact a2 _ h2'
  refine ⟨t0, m0, run0, term0, key, ?_⟩
  rw [← out_maps]; exact key _ out1 (by rw [out_maps]; exact out2)

end Formal.Rewrite.Steps.CollatzEq2Pass
