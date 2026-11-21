import Formal.Rewrite.Collatz64OrigHwSeg
import Formal.Rewrite.Collatz64Preeq2HwSeg
import Formal.Net.AutoLib
import Formal.Rewrite.Eq2
import Formal.Rewrite.Diverge

/-!
# Formal.Rewrite.Collatz64 — research's collatz64 loop-test rewrite computes the same function (shard A, 2026-11-15)

**Problem, plainly.** research's `pre_eq2.py` replaces collatz64's loop test `n' == 1` (n' the 64-bit update
`(n & 1) == 0 ? n >> 1 : 3 * n + 1`) by `n == 2` in the handshake MLIR. Do the original graph
(`cloud/fixtures/frontend/collatz64/comp/handshake_transformed.mlir`) and the rewritten one
(`research/data/fifteen/collatz64_preeq2.mlir`) compute the same function, for every 64-bit input?

**Proved** (`Orig.computes`, `Preeq2.computes`, `same`): both graphs, imported by C's dfimport unchanged, compute the
C function as transcribed below by hand (`P`, read off `kernels/collatz64/collatz64.c`: `n` is `long long`, so 64-bit
two's complement with an arithmetic shift; `steps` is `int`, 32-bit): for every natural `n` on the input channel
and any fuel on which `kC` returns `r`, each graph has a complete run ending with `[r]` on the output, every complete
run under any schedule ends there, and runs are bounded. So on every input on which the C returns, both graphs
return the same value. The rewrite's own fact is `Eq2.collatz_eq2` at width 64.

**Why by hand.** C's cfront transcribes 32-bit C only; the transcription here is checked by `witness` (27 takes 111
steps, kernel-evaluated) and, more to the point, the equivalence claim does not depend on it: both graphs are proved
against the SAME `P`.

**Inputs on which the C never returns** (e.g. `n = 0`, negative cycles): `same_div`: then neither graph ever
completes a run (both have arbitrarily long runs, `Diverge.sim_div`, and are determinate). So the two graphs agree on
every input. **Not covered:** gates, delays and cells.
-/

set_option linter.unusedVariables false

namespace Formal.Rewrite.Collatz64
open Formal.Net.GcdHw Formal.Net.Auto

/-- `while (n != 1) { if ((n & 1) == 0) n = n >> 1; else n = 3 * n + 1; steps = steps + 1; }`. -/
def ce0 : CEdge := { src := 0, br := true, upd := [(.sel (.bin (.cmpi .eq) 64 (.bin .andi 64 (.var 0) (.lit 1)) (.lit 0))
  (.bin .shrsi 64 (.var 0) (.lit 1)) (.bin .addi 64 (.bin .muli 64 (.lit 3) (.var 0)) (.lit 1))),
  (.bin .addi 32 (.var 1) (.lit 1))], dst := some 0, ret := (.lit 0) }
/-- `return steps;` -/
def ce1 : CEdge := { src := 0, br := false, upd := [(.var 0), (.var 1)], dst := none, ret := (.var 1) }

def P : CProg where
  entry := [(.var 0), (.lit 0)]
  start := 0
  tests := [(.bin (.cmpi .ne) 64 (.var 0) (.lit 1))]
  edges := [ce0, ce1]

/-- `collatz64` as transcribed: `none` = fuel ran out. -/
def kC (fuel n₀ : Nat) : Option Nat := P.call fuel [n₀]

/-- The transcription on the kernel's own vector (27 takes 111 steps), evaluated by the kernel. -/
theorem witness : kC 200 27 = some 111 := by decide +kernel

/-- The graph's parity test (`trunci` to 1 bit, `andi 1`) and the C's (`andi 64`) agree. -/
theorem par_eq (n : Nat) : Ops.cmpi .eq 1 (Ops.andi 1 (Ops.trunci 1 n) 1) 0 % 2 =
    Ops.cmpi .eq 64 (Ops.andi 64 n 1) 0 % 2 := by
  simp only [Ops.cmpi, Ops.andi, Ops.trunci, Nat.and_one_is_mod, Ops.b2n, Nat.reducePow]
  rcases Nat.mod_two_eq_zero_or_one n with h | h <;> simp [h] <;> omega

/-- The graph's `n + (n << 1)` is the C's `3 * n`, mod 2^64. -/
theorem three_eq (n : Nat) : Ops.addi 64 (Ops.addi 64 n (Ops.shli 64 n 1)) 1 = Ops.addi 64 (Ops.muli 64 3 n) 1 := by
  simp only [Ops.addi, Ops.shli, Ops.muli, Nat.shiftLeft_eq, Nat.reducePow, Nat.pow_one]
  omega

/-- The graph's update and the C's update agree. -/
theorem upd_eq (n : Nat) : Ops.select (Ops.cmpi .eq 1 (Ops.andi 1 (Ops.trunci 1 n) 1) 0) (Ops.shrsi 64 n 1)
      (Ops.addi 64 (Ops.addi 64 n (Ops.shli 64 n 1)) 1) =
    Ops.select (Ops.cmpi .eq 64 (Ops.andi 64 n 1) 0) (Ops.shrsi 64 n 1) (Ops.addi 64 (Ops.muli 64 3 n) 1) := by
  simp only [Ops.select, par_eq, three_eq]

theorem eq1_ne (v : Nat) : Ops.cmpi .eq 64 v 1 = Ops.cmpi .eq 64 (Ops.cmpi .ne 64 v 1) 0 := by
  unfold Ops.cmpi Ops.b2n
  by_cases h : v % 2 ^ 64 = 1 % 2 ^ 64 <;> simp [h]

theorem isT_ne_eq (v : Nat) : isT (Ops.cmpi .eq 64 v 1) = !isT (Ops.cmpi .ne 64 v 1) := by
  unfold Ops.cmpi Ops.b2n
  by_cases h : v % 2 ^ 64 = 1 % 2 ^ 64 <;> simp [h, isT]

/-! ## Expressions and their value lemmas -/

/-- The graph's update (as dfimport writes it). -/
def updG (e : E) : E := .sel (.bin (.cmpi .eq) 1 (.bin .andi 1 (.un .trunci 1 e) (.lit 1)) (.lit 0))
  (.bin .shrsi 64 e (.lit 1)) (.bin .addi 64 (.bin .addi 64 e (.bin .shli 64 e (.lit 1))) (.lit 1))
/-- The C's update. -/
def updC (e : E) : E := .sel (.bin (.cmpi .eq) 64 (.bin .andi 64 e (.lit 1)) (.lit 0))
  (.bin .shrsi 64 e (.lit 1)) (.bin .addi 64 (.bin .muli 64 (.lit 3) e) (.lit 1))
def condC (e : E) : E := .bin (.cmpi .eq) 64 (.bin (.cmpi .ne) 64 e (.lit 1)) (.lit 0)
def tC : E := .bin (.cmpi .ne) 64 (.var 0) (.lit 1)
def eq1 (e : E) : E := .bin (.cmpi .eq) 64 e (.lit 1)

theorem ev_upd (σ : List Nat) (e : E) : E.eval σ (updG e) = E.eval σ (updC e) := by
  simp only [updG, updC, E.eval, BOp.ev, UOp.ev]; exact upd_eq _

theorem ev_eq1_upd (σ : List Nat) (e : E) : E.eval σ (eq1 (updG e)) = E.eval σ (condC (updC e)) := by
  simp only [eq1, condC, E.eval, BOp.ev]; rw [← ev_upd]; exact eq1_ne _

theorem ev_eq2 (σ : List Nat) (e : E) : E.eval σ (.bin (.cmpi .eq) 64 e (.lit 2)) = E.eval σ (condC (updC e)) := by
  simp only [condC, updC, E.eval, BOp.ev]; exact (Formal.Rewrite.Eq2.collatz_eq2 64 _ (by decide)).symm

theorem isT_eq1 (σ : List Nat) : isT (E.eval σ (eq1 (.var 0))) = !isT (E.eval σ tC) := by
  simp only [eq1, tC, E.eval, BOp.ev]; exact isT_ne_eq _

/-- The C always has an outgoing edge at its test point (no stuck state). -/
theorem pick_some (σ : List Nat) : P.pick 0 σ ≠ none := by
  unfold CProg.pick
  cases h : isT ((P.tests.getD 0 (.lit 0)).eval σ) <;> simp [P, ce0, ce1, List.find?]

theorem isT_cond (σ : List Nat) : isT (E.eval σ (condC (.var 0))) = !isT (E.eval σ tC) := by
  simp only [condC, tC, E.eval, BOp.ev]; rw [← eq1_ne]; exact isT_ne_eq _

end Formal.Rewrite.Collatz64

namespace Formal.Rewrite.Collatz64.Orig
open Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Auto Formal.Rewrite.Collatz64OrigHw Formal.Rewrite
open Formal.Rewrite.Collatz64 (P ce0 ce1 kC)

abbrev G := graph rules
def St (t : List (List E)) (env : List Nat) : Store Nat Nat := ofL (lmap env t)
def Reach (s t : Store Nat Nat) : Prop := ∃ n, Run (step G) s n t
theorem reach_trans {s u t : Store Nat Nat} (h1 : Reach s u) (h2 : Reach u t) : Reach s t :=
  let ⟨_, a⟩ := h1; let ⟨_, b⟩ := h2; ⟨_, run_trans a b⟩

theorem edge {F : List (E × Bool)} {sched : List Nat} {sig : List E} {Ti Tj : List (List E)}
    (hl : Ti.length = N) (h : execL (symVI F) rules Ti sched = some (Tj.map (List.map (E.subst sig))))
    (env : List Nat) (hF : FactsOK env F) : Reach (St Ti env) (St Tj (sig.map (E.eval env))) := by
  have := sym_run bounded_ok hl sched h env hF
  rw [lmap_subst] at this
  exact ⟨_, this⟩

theorem fact1 {env : List Nat} {e : E} {b : Bool} (h : isT (e.eval env) = b) :
    FactsOK env [(e, b)] := by
  intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact h

theorem lenT0 : T0.length = N := by decide +kernel
theorem lenT2 : T2.length = N := by decide +kernel

def Ts : List (List (List E)) := [T0, T1, T2]
def Tm (k : Nat) (env : List Nat) : Store Nat Nat := St (Ts.getD k []) env

def g0 : GEdge := { src := 0, fact := (.bin (.cmpi .eq) 64 (.var 0) (.lit 1)), br := true, sig := sig0, dst := 1 }
def g1 : GEdge := { src := 0, fact := (.bin (.cmpi .eq) 64 (.var 0) (.lit 1)), br := false, sig := sig1, dst := 2 }
def g2 : GEdge := { src := 2, fact := (.var 2), br := true, sig := sig2, dst := 1 }
def g3 : GEdge := { src := 2, fact := (.var 2), br := false, sig := sig3, dst := 2 }
def GE : List GEdge := [g0, g1, g2, g3]

theorem hG : ∀ g ∈ GE, ∀ env : List Nat, isT (g.fact.eval env) = g.br →
    Reach (Tm g.src env) (Tm g.dst (g.sig.map (E.eval env))) := by
  intro g hg env hf
  simp only [GE, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact edge (Ti := T0) (Tj := T1) lenT0 seg0 env (fact1 hf)
  · exact edge (Ti := T0) (Tj := T2) lenT0 seg1 env (fact1 hf)
  · exact edge (Ti := T2) (Tj := T1) lenT2 seg2 env (fact1 hf)
  · exact edge (Ti := T2) (Tj := T2) lenT2 seg3 env (fact1 hf)

def L : List Nat := [0, 0, 0]
def K : List Nat := [0, 2]
/-- The loop template holds `[n, steps, n == 1]` of the C state after the update (as in C's 32-bit AutoCollatz). -/
def ρ : List (List E) := [[(.var 0)], [], [(.var 0), (.var 1), (.bin (.cmpi .eq) 64 (.bin (.cmpi .ne) 64 (.var 0) (.lit 1)) (.lit 0))]]
def Is : List (List (E × E)) := [[((.var 1), (.lit 0))], [], []]
def M : List Match := [⟨0, ce0, g1⟩, ⟨0, ce1, g0⟩, ⟨2, ce0, g3⟩, ⟨2, ce1, g2⟩]

theorem cover : Cover P L K 1 GE M = true := by decide +kernel

/-! ## The four edge pairs -/

open Formal.Rewrite.Collatz64 (updG updC condC tC eq1 ev_upd ev_eq1_upd ev_eq2 isT_eq1 isT_cond)

theorem o0 : ∀ σ : List Nat, [E.var 1].map (E.eval σ) = [E.lit 0].map (E.eval σ) → isT (tC.eval σ) = true →
    isT ((eq1 (.var 0)).eval σ) = false ∧
    [updG (.var 0), .bin .addi 32 (.un .extui 1 (.lit 0)) (.lit 1), eq1 (updG (.var 0))].map (E.eval σ) =
    [updC (.var 0), .bin .addi 32 (.var 1) (.lit 1), condC (updC (.var 0))].map (E.eval σ) ∧
    ([] : List E).map (E.eval σ) = ([] : List E).map (E.eval σ) := by
  intro σ hI hT
  simp only [List.map, List.cons.injEq, and_true, E.eval] at hI
  refine ⟨by rw [isT_eq1, hT]; rfl, ?_, rfl⟩
  simp only [List.map, List.cons.injEq, and_true]
  refine ⟨ev_upd σ _, ?_, ev_eq1_upd σ _⟩
  simp only [E.eval, BOp.ev, UOp.ev, hI, Ops.addi, Ops.extui]

theorem m0 : MatchSem P ρ Is ⟨0, ce0, g1⟩ :=
  matchSem_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) o0

theorem o1 : ∀ σ : List Nat, [E.var 1].map (E.eval σ) = [E.lit 0].map (E.eval σ) → isT (tC.eval σ) = false →
    isT ((eq1 (.var 0)).eval σ) = true ∧ [E.un .extui 1 (.lit 0)].map (E.eval σ) = [E.var 1].map (E.eval σ) ∧
    ([] : List E).map (E.eval σ) = ([] : List E).map (E.eval σ) := by
  intro σ hI hT
  simp only [List.map, List.cons.injEq, and_true, E.eval] at hI
  refine ⟨by rw [isT_eq1, hT]; rfl, ?_, rfl⟩
  simp only [List.map, E.eval, UOp.ev, Ops.extui, hI]

theorem m1 : MatchSem P ρ Is ⟨0, ce1, g0⟩ :=
  matchSem_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) o1

theorem o2 : ∀ σ : List Nat, ([] : List E).map (E.eval σ) = ([] : List E).map (E.eval σ) → isT (tC.eval σ) = true →
    isT ((condC (.var 0)).eval σ) = false ∧
    [updG (.var 0), .bin .addi 32 (.var 1) (.lit 1), eq1 (updG (.var 0))].map (E.eval σ) =
    [updC (.var 0), .bin .addi 32 (.var 1) (.lit 1), condC (updC (.var 0))].map (E.eval σ) ∧
    ([] : List E).map (E.eval σ) = ([] : List E).map (E.eval σ) := by
  intro σ hI hT
  refine ⟨by rw [isT_cond, hT]; rfl, ?_, rfl⟩
  simp only [List.map, List.cons.injEq, and_true]
  exact ⟨ev_upd σ _, trivial, ev_eq1_upd σ _⟩

theorem m2 : MatchSem P ρ Is ⟨2, ce0, g3⟩ :=
  matchSem_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) o2

theorem o3 : ∀ σ : List Nat, ([] : List E).map (E.eval σ) = ([] : List E).map (E.eval σ) → isT (tC.eval σ) = false →
    isT ((condC (.var 0)).eval σ) = true ∧ [E.var 1].map (E.eval σ) = [E.var 1].map (E.eval σ) ∧
    ([] : List E).map (E.eval σ) = ([] : List E).map (E.eval σ) := by
  intro σ hI hT
  exact ⟨by rw [isT_cond, hT]; rfl, rfl, rfl⟩

theorem m3 : MatchSem P ρ Is ⟨2, ce1, g2⟩ :=
  matchSem_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) o3

theorem hM : ∀ m ∈ M, MatchSem P ρ Is m := by
  intro m hm
  simp only [M, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact m0
  · exact m1
  · exact m2
  · exact m3

theorem hin (n₀ : Nat) : (ρ.getD 0 []).map (E.eval (P.entry.map (E.eval [n₀]))) = [n₀] := rfl
theorem hI0 (n₀ : Nat) : InvH (Is.getD 0 []) (P.entry.map (E.eval [n₀])) := rfl

theorem reach_kC {fuel n₀ r : Nat} (h : kC fuel n₀ = some r) : Reach (St T0 [n₀]) (St T1 [r]) :=
  sim_call Tm Reach reach_trans P L K ρ Is 1 GE M hG cover hM (by decide) rfl (hin n₀) (hI0 n₀) h

theorem cnt_lmap (Q : List Nat) (env : List Nat) (l : List (List E)) :
    cnt Q (ofL (lmap env l)) = (Q.map fun c => (ofL l c).length).sum := by
  unfold cnt; congr 1; apply List.map_congr_left; intro c _; simp [ofL_lmap]

theorem init_inv (n₀ : Nat) : Formal.Net.GcdHw.Inv spine (St T0 [n₀]) := by
  unfold Formal.Net.GcdHw.Inv St; rw [cnt_lmap]; decide +kernel

theorem final_terminal (r : Nat) : Terminal (step G) (St T1 [r]) := by
  apply terminal_of_dead
  rw [List.all_eq_true]; intro x hx
  rw [St, dead_lmap]
  exact List.all_eq_true.mp (by decide +kernel : rules.all (Rule.dead (ofL T1)) = true) x hx

/-- **This graph computes the C function `collatz64`** (as transcribed in `Collatz64.P`). -/
theorem computes {fuel n₀ r : Nat} (h : kC fuel n₀ = some r) :
    (∃ n, Run (step G) (St T0 [n₀]) n (St T1 [r])) ∧
    (∀ m t, Run (step G) (St T0 [n₀]) m t → Terminal (step G) t → t = St T1 [r]) ∧
    (∃ n, ∀ m u, Run (step G) (St T0 [n₀]) m u → m ≤ n) := by
  obtain ⟨n, hn⟩ := reach_kC h
  refine ⟨⟨n, hn⟩, fun m t ht hT => ?_, ⟨n, fun m u hu => ?_⟩⟩
  · exact (determinate spine rules spine_nodup ins_ok outs_ok spine_ok (init_inv n₀)
      hn (final_terminal r) ht hT).1
  · exact no_longer spine rules spine_nodup ins_ok outs_ok spine_ok (init_inv n₀)
      hn (final_terminal r) hu

/-! ## Inputs on which the C never returns -/

theorem edgeN {F : List (E × Bool)} {sched : List Nat} {sig : List E} {Ti Tj : List (List E)}
    (hl : Ti.length = N) (h : execL (symVI F) rules Ti sched = some (Tj.map (List.map (E.subst sig))))
    (hs : 1 ≤ sched.length) (env : List Nat) (hF : FactsOK env F) :
    ∃ n, 1 ≤ n ∧ Run (step G) (St Ti env) n (St Tj (sig.map (E.eval env))) := by
  have := sym_run bounded_ok hl sched h env hF
  rw [lmap_subst] at this
  exact ⟨_, hs, this⟩

theorem hGN : ∀ g ∈ GE, ∀ env : List Nat, isT (g.fact.eval env) = g.br →
    ∃ n, 1 ≤ n ∧ Run (step G) (Tm g.src env) n (Tm g.dst (g.sig.map (E.eval env))) := by
  intro g hg env hf
  simp only [GE, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact edgeN (Ti := T0) (Tj := T1) lenT0 seg0 (by decide) env (fact1 hf)
  · exact edgeN (Ti := T0) (Tj := T2) lenT0 seg1 (by decide) env (fact1 hf)
  · exact edgeN (Ti := T2) (Tj := T1) lenT2 seg2 (by decide) env (fact1 hf)
  · exact edgeN (Ti := T2) (Tj := T2) lenT2 seg3 (by decide) env (fact1 hf)

/-- **Where the C never returns, this graph never finishes**: no run from the input store reaches a terminal store. -/
theorem diverges {n₀ : Nat} (h : ∀ fuel, kC fuel n₀ = none) :
    ∀ m t, Run (step G) (St T0 [n₀]) m t → ¬ Terminal (step G) t := by
  intro m t ht hT
  have hK : ∀ k ∈ K, ∀ σ, P.pick (L.getD k 0) σ ≠ none := by
    intro k hk σ
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> exact Formal.Rewrite.Collatz64.pick_some σ
  obtain ⟨n, hn, u, hu⟩ := Formal.Rewrite.Diverge.sim_div Tm (fun a n b => Run (step G) a n b) (fun a => Run.refl a)
    (fun h1 h2 => run_trans h1 h2) P L K ρ Is 1 GE M hGN cover hM hK (m + 1) 0 (P.entry.map (E.eval [n₀]))
    (by decide) (hI0 n₀) (fun f => h f)
  rw [hin n₀] at hu
  have := no_longer spine rules spine_nodup ins_ok outs_ok spine_ok (init_inv n₀) ht hT hu
  omega

end Formal.Rewrite.Collatz64.Orig

namespace Formal.Rewrite.Collatz64.Preeq2
open Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Auto Formal.Rewrite.Collatz64Preeq2Hw Formal.Rewrite
open Formal.Rewrite.Collatz64 (P ce0 ce1 kC)

abbrev G := graph rules
def St (t : List (List E)) (env : List Nat) : Store Nat Nat := ofL (lmap env t)
def Reach (s t : Store Nat Nat) : Prop := ∃ n, Run (step G) s n t
theorem reach_trans {s u t : Store Nat Nat} (h1 : Reach s u) (h2 : Reach u t) : Reach s t :=
  let ⟨_, a⟩ := h1; let ⟨_, b⟩ := h2; ⟨_, run_trans a b⟩

theorem edge {F : List (E × Bool)} {sched : List Nat} {sig : List E} {Ti Tj : List (List E)}
    (hl : Ti.length = N) (h : execL (symVI F) rules Ti sched = some (Tj.map (List.map (E.subst sig))))
    (env : List Nat) (hF : FactsOK env F) : Reach (St Ti env) (St Tj (sig.map (E.eval env))) := by
  have := sym_run bounded_ok hl sched h env hF
  rw [lmap_subst] at this
  exact ⟨_, this⟩

theorem fact1 {env : List Nat} {e : E} {b : Bool} (h : isT (e.eval env) = b) :
    FactsOK env [(e, b)] := by
  intro p hp; simp only [List.mem_singleton] at hp; subst hp; exact h

theorem lenT0 : T0.length = N := by decide +kernel
theorem lenT2 : T2.length = N := by decide +kernel

def Ts : List (List (List E)) := [T0, T1, T2]
def Tm (k : Nat) (env : List Nat) : Store Nat Nat := St (Ts.getD k []) env

def g0 : GEdge := { src := 0, fact := (.bin (.cmpi .eq) 64 (.var 0) (.lit 1)), br := true, sig := sig0, dst := 1 }
def g1 : GEdge := { src := 0, fact := (.bin (.cmpi .eq) 64 (.var 0) (.lit 1)), br := false, sig := sig1, dst := 2 }
def g2 : GEdge := { src := 2, fact := (.var 2), br := true, sig := sig2, dst := 1 }
def g3 : GEdge := { src := 2, fact := (.var 2), br := false, sig := sig3, dst := 2 }
def GE : List GEdge := [g0, g1, g2, g3]

theorem hG : ∀ g ∈ GE, ∀ env : List Nat, isT (g.fact.eval env) = g.br →
    Reach (Tm g.src env) (Tm g.dst (g.sig.map (E.eval env))) := by
  intro g hg env hf
  simp only [GE, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact edge (Ti := T0) (Tj := T1) lenT0 seg0 env (fact1 hf)
  · exact edge (Ti := T0) (Tj := T2) lenT0 seg1 env (fact1 hf)
  · exact edge (Ti := T2) (Tj := T1) lenT2 seg2 env (fact1 hf)
  · exact edge (Ti := T2) (Tj := T2) lenT2 seg3 env (fact1 hf)

def L : List Nat := [0, 0, 0]
def K : List Nat := [0, 2]
/-- The loop template holds `[n, steps, n == 1]` of the C state after the update (as in C's 32-bit AutoCollatz). -/
def ρ : List (List E) := [[(.var 0)], [], [(.var 0), (.var 1), (.bin (.cmpi .eq) 64 (.bin (.cmpi .ne) 64 (.var 0) (.lit 1)) (.lit 0))]]
def Is : List (List (E × E)) := [[((.var 1), (.lit 0))], [], []]
def M : List Match := [⟨0, ce0, g1⟩, ⟨0, ce1, g0⟩, ⟨2, ce0, g3⟩, ⟨2, ce1, g2⟩]

theorem cover : Cover P L K 1 GE M = true := by decide +kernel

/-! ## The four edge pairs -/

open Formal.Rewrite.Collatz64 (updG updC condC tC eq1 ev_upd ev_eq1_upd ev_eq2 isT_eq1 isT_cond)

theorem o0 : ∀ σ : List Nat, [E.var 1].map (E.eval σ) = [E.lit 0].map (E.eval σ) → isT (tC.eval σ) = true →
    isT ((eq1 (.var 0)).eval σ) = false ∧
    [updG (.var 0), .bin .addi 32 (.un .extui 1 (.lit 0)) (.lit 1), .bin (.cmpi .eq) 64 (.var 0) (.lit 2)].map (E.eval σ) =
    [updC (.var 0), .bin .addi 32 (.var 1) (.lit 1), condC (updC (.var 0))].map (E.eval σ) ∧
    ([] : List E).map (E.eval σ) = ([] : List E).map (E.eval σ) := by
  intro σ hI hT
  simp only [List.map, List.cons.injEq, and_true, E.eval] at hI
  refine ⟨by rw [isT_eq1, hT]; rfl, ?_, rfl⟩
  simp only [List.map, List.cons.injEq, and_true]
  refine ⟨ev_upd σ _, ?_, ev_eq2 σ _⟩
  simp only [E.eval, BOp.ev, UOp.ev, hI, Ops.addi, Ops.extui]

theorem m0 : MatchSem P ρ Is ⟨0, ce0, g1⟩ :=
  matchSem_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) o0

theorem o1 : ∀ σ : List Nat, [E.var 1].map (E.eval σ) = [E.lit 0].map (E.eval σ) → isT (tC.eval σ) = false →
    isT ((eq1 (.var 0)).eval σ) = true ∧ [E.un .extui 1 (.lit 0)].map (E.eval σ) = [E.var 1].map (E.eval σ) ∧
    ([] : List E).map (E.eval σ) = ([] : List E).map (E.eval σ) := by
  intro σ hI hT
  simp only [List.map, List.cons.injEq, and_true, E.eval] at hI
  refine ⟨by rw [isT_eq1, hT]; rfl, ?_, rfl⟩
  simp only [List.map, E.eval, UOp.ev, Ops.extui, hI]

theorem m1 : MatchSem P ρ Is ⟨0, ce1, g0⟩ :=
  matchSem_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) o1

theorem o2 : ∀ σ : List Nat, ([] : List E).map (E.eval σ) = ([] : List E).map (E.eval σ) → isT (tC.eval σ) = true →
    isT ((condC (.var 0)).eval σ) = false ∧
    [updG (.var 0), .bin .addi 32 (.var 1) (.lit 1), .bin (.cmpi .eq) 64 (.var 0) (.lit 2)].map (E.eval σ) =
    [updC (.var 0), .bin .addi 32 (.var 1) (.lit 1), condC (updC (.var 0))].map (E.eval σ) ∧
    ([] : List E).map (E.eval σ) = ([] : List E).map (E.eval σ) := by
  intro σ hI hT
  refine ⟨by rw [isT_cond, hT]; rfl, ?_, rfl⟩
  simp only [List.map, List.cons.injEq, and_true]
  exact ⟨ev_upd σ _, trivial, ev_eq2 σ _⟩

theorem m2 : MatchSem P ρ Is ⟨2, ce0, g3⟩ :=
  matchSem_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) o2

theorem o3 : ∀ σ : List Nat, ([] : List E).map (E.eval σ) = ([] : List E).map (E.eval σ) → isT (tC.eval σ) = false →
    isT ((condC (.var 0)).eval σ) = true ∧ [E.var 1].map (E.eval σ) = [E.var 1].map (E.eval σ) ∧
    ([] : List E).map (E.eval σ) = ([] : List E).map (E.eval σ) := by
  intro σ hI hT
  exact ⟨by rw [isT_cond, hT]; rfl, rfl, rfl⟩

theorem m3 : MatchSem P ρ Is ⟨2, ce1, g2⟩ :=
  matchSem_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) o3

theorem hM : ∀ m ∈ M, MatchSem P ρ Is m := by
  intro m hm
  simp only [M, List.mem_cons, List.not_mem_nil, or_false] at hm
  rcases hm with rfl | rfl | rfl | rfl
  · exact m0
  · exact m1
  · exact m2
  · exact m3

theorem hin (n₀ : Nat) : (ρ.getD 0 []).map (E.eval (P.entry.map (E.eval [n₀]))) = [n₀] := rfl
theorem hI0 (n₀ : Nat) : InvH (Is.getD 0 []) (P.entry.map (E.eval [n₀])) := rfl

theorem reach_kC {fuel n₀ r : Nat} (h : kC fuel n₀ = some r) : Reach (St T0 [n₀]) (St T1 [r]) :=
  sim_call Tm Reach reach_trans P L K ρ Is 1 GE M hG cover hM (by decide) rfl (hin n₀) (hI0 n₀) h

theorem cnt_lmap (Q : List Nat) (env : List Nat) (l : List (List E)) :
    cnt Q (ofL (lmap env l)) = (Q.map fun c => (ofL l c).length).sum := by
  unfold cnt; congr 1; apply List.map_congr_left; intro c _; simp [ofL_lmap]

theorem init_inv (n₀ : Nat) : Formal.Net.GcdHw.Inv spine (St T0 [n₀]) := by
  unfold Formal.Net.GcdHw.Inv St; rw [cnt_lmap]; decide +kernel

theorem final_terminal (r : Nat) : Terminal (step G) (St T1 [r]) := by
  apply terminal_of_dead
  rw [List.all_eq_true]; intro x hx
  rw [St, dead_lmap]
  exact List.all_eq_true.mp (by decide +kernel : rules.all (Rule.dead (ofL T1)) = true) x hx

/-- **This graph computes the C function `collatz64`** (as transcribed in `Collatz64.P`). -/
theorem computes {fuel n₀ r : Nat} (h : kC fuel n₀ = some r) :
    (∃ n, Run (step G) (St T0 [n₀]) n (St T1 [r])) ∧
    (∀ m t, Run (step G) (St T0 [n₀]) m t → Terminal (step G) t → t = St T1 [r]) ∧
    (∃ n, ∀ m u, Run (step G) (St T0 [n₀]) m u → m ≤ n) := by
  obtain ⟨n, hn⟩ := reach_kC h
  refine ⟨⟨n, hn⟩, fun m t ht hT => ?_, ⟨n, fun m u hu => ?_⟩⟩
  · exact (determinate spine rules spine_nodup ins_ok outs_ok spine_ok (init_inv n₀)
      hn (final_terminal r) ht hT).1
  · exact no_longer spine rules spine_nodup ins_ok outs_ok spine_ok (init_inv n₀)
      hn (final_terminal r) hu

/-! ## Inputs on which the C never returns -/

theorem edgeN {F : List (E × Bool)} {sched : List Nat} {sig : List E} {Ti Tj : List (List E)}
    (hl : Ti.length = N) (h : execL (symVI F) rules Ti sched = some (Tj.map (List.map (E.subst sig))))
    (hs : 1 ≤ sched.length) (env : List Nat) (hF : FactsOK env F) :
    ∃ n, 1 ≤ n ∧ Run (step G) (St Ti env) n (St Tj (sig.map (E.eval env))) := by
  have := sym_run bounded_ok hl sched h env hF
  rw [lmap_subst] at this
  exact ⟨_, hs, this⟩

theorem hGN : ∀ g ∈ GE, ∀ env : List Nat, isT (g.fact.eval env) = g.br →
    ∃ n, 1 ≤ n ∧ Run (step G) (Tm g.src env) n (Tm g.dst (g.sig.map (E.eval env))) := by
  intro g hg env hf
  simp only [GE, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact edgeN (Ti := T0) (Tj := T1) lenT0 seg0 (by decide) env (fact1 hf)
  · exact edgeN (Ti := T0) (Tj := T2) lenT0 seg1 (by decide) env (fact1 hf)
  · exact edgeN (Ti := T2) (Tj := T1) lenT2 seg2 (by decide) env (fact1 hf)
  · exact edgeN (Ti := T2) (Tj := T2) lenT2 seg3 (by decide) env (fact1 hf)

/-- **Where the C never returns, this graph never finishes**: no run from the input store reaches a terminal store. -/
theorem diverges {n₀ : Nat} (h : ∀ fuel, kC fuel n₀ = none) :
    ∀ m t, Run (step G) (St T0 [n₀]) m t → ¬ Terminal (step G) t := by
  intro m t ht hT
  have hK : ∀ k ∈ K, ∀ σ, P.pick (L.getD k 0) σ ≠ none := by
    intro k hk σ
    simp only [K, List.mem_cons, List.not_mem_nil, or_false] at hk
    rcases hk with rfl | rfl <;> exact Formal.Rewrite.Collatz64.pick_some σ
  obtain ⟨n, hn, u, hu⟩ := Formal.Rewrite.Diverge.sim_div Tm (fun a n b => Run (step G) a n b) (fun a => Run.refl a)
    (fun h1 h2 => run_trans h1 h2) P L K ρ Is 1 GE M hGN cover hM hK (m + 1) 0 (P.entry.map (E.eval [n₀]))
    (by decide) (hI0 n₀) (fun f => h f)
  rw [hin n₀] at hu
  have := no_longer spine rules spine_nodup ins_ok outs_ok spine_ok (init_inv n₀) ht hT hu
  omega

end Formal.Rewrite.Collatz64.Preeq2

namespace Formal.Rewrite.Collatz64
open Formal.Net.Kahn

/-- **Before and after agree**: on every input on which the C returns `r`, the original collatz64 graph and the
rewritten one both have complete runs ending with `[r]` on the output, and every complete run of either ends there. -/
theorem same {fuel n₀ r : Nat} (h : kC fuel n₀ = some r) :
    ((∃ n, Run (step Orig.G) (Orig.St Collatz64OrigHw.T0 [n₀]) n (Orig.St Collatz64OrigHw.T1 [r])) ∧
      ∀ m t, Run (step Orig.G) (Orig.St Collatz64OrigHw.T0 [n₀]) m t → Terminal (step Orig.G) t →
        t = Orig.St Collatz64OrigHw.T1 [r]) ∧
    ((∃ n, Run (step Preeq2.G) (Preeq2.St Collatz64Preeq2Hw.T0 [n₀]) n (Preeq2.St Collatz64Preeq2Hw.T1 [r])) ∧
      ∀ m t, Run (step Preeq2.G) (Preeq2.St Collatz64Preeq2Hw.T0 [n₀]) m t → Terminal (step Preeq2.G) t →
        t = Preeq2.St Collatz64Preeq2Hw.T1 [r]) :=
  ⟨⟨(Orig.computes h).1, (Orig.computes h).2.1⟩, ⟨(Preeq2.computes h).1, (Preeq2.computes h).2.1⟩⟩

/-- **And where the C never returns, neither graph ever finishes** (no complete run of either). With `same`: the two
graphs agree on EVERY 64-bit input. -/
theorem same_div {n₀ : Nat} (h : ∀ fuel, kC fuel n₀ = none) :
    (∀ m t, Run (step Orig.G) (Orig.St Collatz64OrigHw.T0 [n₀]) m t → ¬ Terminal (step Orig.G) t) ∧
    (∀ m t, Run (step Preeq2.G) (Preeq2.St Collatz64Preeq2Hw.T0 [n₀]) m t → ¬ Terminal (step Preeq2.G) t) :=
  ⟨Orig.diverges h, Preeq2.diverges h⟩

end Formal.Rewrite.Collatz64
