import Formal.Rewrite.XorshiftPredecHwSeg
import Formal.Net.AutoLib
import Formal.Net.AutoXorshift

/-!
# Formal.Rewrite.XorshiftPredec — research's xorshift loop-test rewrite computes the same function (shard A, 2026-11-15)

**Problem, plainly.** research's `pre_dec.py` rewrites xorshift's handshake MLIR: the rounds ring carries
`m = n - 1` (an `addi n, -1` before the loop) and the loop test compares the loop counter `i` with `m` (`i < m`)
instead of `i + 1 < n`, so the compare starts with the add instead of after it. Its argument (docstring): the loop
is entered only when `n >ₛ 0`, so `n - 1` does not wrap, and `i + 1 ≤ n ≤ INT_MAX` inside the loop. Does the
rewritten graph compute the same function as the original, for every 32-bit input, including `n ≤ 0` and
wrap-around?

**Proved** (`computes`): for every pair of naturals `(seed, n)` on the input channels (every bit pattern) and any
fuel on which the C transcription `AutoXorshift.kC` (cfront's reading of `kernels/xorshift/xorshift.c`, the same
transcription C's `AutoXorshift.auto_computes` proves the ORIGINAL graph against) returns `r`, the graph imported
from `research/data/fifteen/xorshift_predec.mlir` (`XorshiftPredecHw`, dfimport, unchanged) has a complete run
ending with `[r]` on the output; every complete run, under any schedule, ends in that store; runs are bounded.
`same_as_original`: both graphs then end in the same store `[r]`. `kC_total`: the C returns on every input (fuel
`2^32 + 1`), so `same_all`: the two graphs agree on EVERY input.

**How.** Shard C's generic simulation `Auto.sim_call` with a hand correspondence: the rewritten loop template's ring
value is `n + (2^32 - 1)` (i.e. `n - 1` mod 2^32) over the C state, its test value `slt(i - 1, n - 1)`, and its
invariant `n >ₛ 0 ∧ 1 ≤ₛ i ∧ i ≤ₛ n` (exactly the facts research's docstring uses). Each of the four C/graph edge
pairs is checked by `omega` on the 32-bit encodings.

**Not covered:** gates, delays and cells (token level only); that cfront's transcription is the C (C's
autoproof tests it against the compiled C).
-/

set_option linter.unusedVariables false

namespace Formal.Rewrite.XorshiftPredec

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Auto Formal.Rewrite.XorshiftPredecHw

/-! ## The C side: C's transcription, reused -/

abbrev P : CProg := Formal.Net.AutoXorshift.P
abbrev ce0 : CEdge := Formal.Net.AutoXorshift.ce0
abbrev ce1 : CEdge := Formal.Net.AutoXorshift.ce1
abbrev kC (fuel seed₀ rounds₀ : Nat) : Option Nat := Formal.Net.AutoXorshift.kC fuel seed₀ rounds₀

/-! ## The graph side (the rewritten graph) -/

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
theorem lenT1 : T1.length = N := by decide +kernel

def Ts : List (List (List E)) := [T0, T1, T2]
def Tm (k : Nat) (env : List Nat) : Store Nat Nat := St (Ts.getD k []) env

def g0 : GEdge := { src := 0, fact := (.bin (.cmpi .sgt) 32 (.var 1) (.lit 0)), br := true, sig := sig0, dst := 1 }
def g1 : GEdge := { src := 0, fact := (.bin (.cmpi .sgt) 32 (.var 1) (.lit 0)), br := false, sig := sig1, dst := 2 }
def g2 : GEdge := { src := 1, fact := (.var 3), br := true, sig := sig2, dst := 1 }
def g3 : GEdge := { src := 1, fact := (.var 3), br := false, sig := sig3, dst := 2 }
def GE : List GEdge := [g0, g1, g2, g3]

theorem hG : ∀ g ∈ GE, ∀ env : List Nat, isT (g.fact.eval env) = g.br →
    Reach (Tm g.src env) (Tm g.dst (g.sig.map (E.eval env))) := by
  intro g hg env hf
  simp only [GE, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with rfl | rfl | rfl | rfl
  · exact edge (Ti := T0) (Tj := T1) lenT0 seg0 env (fact1 hf)
  · exact edge (Ti := T0) (Tj := T2) lenT0 seg1 env (fact1 hf)
  · exact edge (Ti := T1) (Tj := T1) lenT1 seg2 env (fact1 hf)
  · exact edge (Ti := T1) (Tj := T2) lenT1 seg3 env (fact1 hf)

/-! ## The correspondence (by hand) -/

/-- `n - 1` mod 2^32. -/
def dec (e : E) : E := .bin .addi 32 e (.lit 4294967295)

def L : List Nat := [0, 0, 0]
def K : List Nat := [0, 1]
/-- C state `[seed, n, x, i]`. Template 1 holds `[m, x, i, slt(i - 1, m)]` with `m = n - 1`. -/
def ρ : List (List E) := [[(.var 0), (.var 1)],
  [dec (.var 1), (.var 2), (.var 3), (.bin (.cmpi .slt) 32 (dec (.var 3)) (dec (.var 1)))], []]
/-- At the entry: `i = 0`, `x = seed`. In the loop: `n >ₛ 0`, `1 ≤ₛ i`, `i ≤ₛ n`. -/
def Is : List (List (E × E)) := [[((.var 3), (.lit 0)), ((.var 2), (.var 0))],
  [((.bin (.cmpi .sgt) 32 (.var 1) (.lit 0)), (.lit 1)), ((.bin (.cmpi .sle) 32 (.lit 1) (.var 3)), (.lit 1)),
   ((.bin (.cmpi .sle) 32 (.var 3) (.var 1)), (.lit 1))], []]
def M : List Match := [⟨0, ce0, g0⟩, ⟨0, ce1, g1⟩, ⟨1, ce0, g2⟩, ⟨1, ce1, g3⟩]

theorem cover : Cover P L K 2 GE M = true := by decide +kernel

/-! ## The four edge pairs -/

/-- One xorshift round over `e`, as the imported graph and the transcription both write it. -/
def xs (e : E) : E :=
  .bin .xori 32 (.bin .xori 32 (.bin .xori 32 e (.bin .shli 32 e (.lit 13)))
      (.bin .shrui 32 (.bin .xori 32 e (.bin .shli 32 e (.lit 13))) (.lit 17)))
    (.bin .shli 32 (.bin .xori 32 (.bin .xori 32 e (.bin .shli 32 e (.lit 13)))
      (.bin .shrui 32 (.bin .xori 32 e (.bin .shli 32 e (.lit 13))) (.lit 17))) (.lit 5))

theorem xs_congr {σ : List Nat} {a b : E} (h : E.eval σ a = E.eval σ b) : E.eval σ (xs a) = E.eval σ (xs b) := by
  simp only [xs, E.eval, h]

def tC : E := .bin (.cmpi .slt) 32 (.var 3) (.var 1)
def fG0 : E := .bin (.cmpi .sgt) 32 (.var 1) (.lit 0)
def fG1 : E := .bin (.cmpi .slt) 32 (dec (.var 3)) (dec (.var 1))
def inv1 : List E := [.bin (.cmpi .sgt) 32 (.var 1) (.lit 0), .bin (.cmpi .sle) 32 (.lit 1) (.var 3),
  .bin (.cmpi .sle) 32 (.var 3) (.var 1)]
def inc3 : E := .bin .addi 32 (.var 3) (.lit 1)
def inv1' : List E := [.bin (.cmpi .sgt) 32 (.var 1) (.lit 0), .bin (.cmpi .sle) 32 (.lit 1) inc3,
  .bin (.cmpi .sle) 32 inc3 (.var 1)]
def ones : List E := [.lit 1, .lit 1, .lit 1]

/-- The arithmetic: unfold the integer ops of the counter and the compares (never the xorshift round) and `omega`. -/
macro "arith" : tactic => `(tactic| (
  simp only [E.eval, BOp.ev, UOp.ev, Ops.addi, Ops.extui, List.getD_cons_zero, List.getD_cons_succ,
    c_slt32, c_sle32, c_sgt32, isT_ite_t, isT_ite_f, ite_eq1, ite_eq0, Nat.reducePow, Nat.reduceMod] at *
  all_goals revert_props
  all_goals (repeat' ite_case)
  all_goals (intros; omega)))

theorem o0 : ∀ σ : List Nat, [E.var 3, .var 2].map (E.eval σ) = [E.lit 0, .var 0].map (E.eval σ) →
    isT (tC.eval σ) = true → isT (fG0.eval σ) = true ∧
    [dec (.var 1), xs (.var 0), .bin .addi 32 (.un .extui 1 (.lit 0)) (.lit 1),
      .bin (.cmpi .slt) 32 (.un .extui 1 (.lit 0)) (dec (.var 1))].map (E.eval σ) =
    [dec (.var 1), xs (.var 2), inc3, .bin (.cmpi .slt) 32 (dec inc3) (dec (.var 1))].map (E.eval σ) ∧
    inv1'.map (E.eval σ) = ones.map (E.eval σ) := by
  intro σ hI hT
  simp only [List.map, List.cons.injEq, and_true] at hI
  obtain ⟨hi, hx⟩ := hI
  simp only [E.eval] at hi hx
  refine ⟨?_, ?_, ?_⟩
  · simp only [tC, fG0] at hT ⊢; arith
  · simp only [List.map, List.cons.injEq, and_true]
    refine ⟨trivial, xs_congr (by simp only [E.eval]; exact hx.symm), ?_, ?_⟩
    · simp only [inc3]; arith
    · simp only [inc3, dec, tC] at hT ⊢; arith
  · simp only [inv1', ones, inc3, tC, List.map, List.cons.injEq, and_true] at hT ⊢; arith

theorem m0 : MatchSem P ρ Is ⟨0, ce0, g0⟩ :=
  matchSem_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) o0

theorem o1 : ∀ σ : List Nat, [E.var 3, .var 2].map (E.eval σ) = [E.lit 0, .var 0].map (E.eval σ) →
    isT (tC.eval σ) = false → isT (fG0.eval σ) = false ∧
    [E.var 0].map (E.eval σ) = [E.var 2].map (E.eval σ) ∧ ([] : List E).map (E.eval σ) = ([] : List E).map (E.eval σ) := by
  intro σ hI hT
  simp only [List.map, List.cons.injEq, and_true] at hI
  obtain ⟨hi, hx⟩ := hI
  simp only [E.eval] at hi hx
  refine ⟨?_, ?_, rfl⟩
  · simp only [tC, fG0] at hT ⊢; arith
  · simp only [List.map, List.cons.injEq, and_true, E.eval]; exact hx.symm

theorem m1 : MatchSem P ρ Is ⟨0, ce1, g1⟩ :=
  matchSem_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) o1

theorem o2 : ∀ σ : List Nat, inv1.map (E.eval σ) = ones.map (E.eval σ) →
    isT (tC.eval σ) = true → isT (fG1.eval σ) = true ∧
    [dec (.var 1), xs (.var 2), inc3, .bin (.cmpi .slt) 32 (.var 3) (dec (.var 1))].map (E.eval σ) =
    [dec (.var 1), xs (.var 2), inc3, .bin (.cmpi .slt) 32 (dec inc3) (dec (.var 1))].map (E.eval σ) ∧
    inv1'.map (E.eval σ) = ones.map (E.eval σ) := by
  intro σ hI hT
  simp only [inv1, ones, List.map, List.cons.injEq, and_true] at hI
  refine ⟨?_, ?_, ?_⟩
  · simp only [tC, fG1, dec] at hT ⊢; arith
  · simp only [List.map, List.cons.injEq, and_true]
    refine ⟨trivial, trivial, trivial, ?_⟩
    simp only [inc3, dec, tC] at hT ⊢; arith
  · simp only [inv1', ones, inc3, tC, List.map, List.cons.injEq, and_true] at hT ⊢; arith

theorem m2 : MatchSem P ρ Is ⟨1, ce0, g2⟩ :=
  matchSem_of (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel) o2

theorem o3 : ∀ σ : List Nat, inv1.map (E.eval σ) = ones.map (E.eval σ) →
    isT (tC.eval σ) = false → isT (fG1.eval σ) = false ∧
    [E.var 2].map (E.eval σ) = [E.var 2].map (E.eval σ) ∧ ([] : List E).map (E.eval σ) = ([] : List E).map (E.eval σ) := by
  intro σ hI hT
  simp only [inv1, ones, List.map, List.cons.injEq, and_true] at hI
  refine ⟨?_, rfl, rfl⟩
  simp only [tC, fG1, dec] at hT ⊢; arith

theorem m3 : MatchSem P ρ Is ⟨1, ce1, g3⟩ :=
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

theorem hin (seed₀ rounds₀ : Nat) :
    (ρ.getD 0 []).map (E.eval (P.entry.map (E.eval [seed₀, rounds₀]))) = [seed₀, rounds₀] := rfl

theorem hI0 (seed₀ rounds₀ : Nat) : InvH (Is.getD 0 []) (P.entry.map (E.eval [seed₀, rounds₀])) := rfl

/-! ## The whole function, on every schedule -/

theorem reach_kC {fuel seed₀ rounds₀ r : Nat} (h : kC fuel seed₀ rounds₀ = some r) :
    Reach (St T0 [seed₀, rounds₀]) (St T2 [r]) :=
  sim_call Tm Reach reach_trans P L K ρ Is 2 GE M hG cover hM (by decide) rfl
    (hin seed₀ rounds₀) (hI0 seed₀ rounds₀) h

theorem cnt_lmap (Q : List Nat) (env : List Nat) (l : List (List E)) :
    cnt Q (ofL (lmap env l)) = (Q.map fun c => (ofL l c).length).sum := by
  unfold cnt; congr 1; apply List.map_congr_left; intro c _; simp [ofL_lmap]

theorem init_inv (seed₀ rounds₀ : Nat) : Formal.Net.GcdHw.Inv spine (St T0 [seed₀, rounds₀]) := by
  unfold Formal.Net.GcdHw.Inv St; rw [cnt_lmap]; decide +kernel

theorem final_terminal (r : Nat) : Terminal (step G) (St T2 [r]) := by
  apply terminal_of_dead
  rw [List.all_eq_true]; intro x hx
  rw [St, dead_lmap]
  exact List.all_eq_true.mp (by decide +kernel : rules.all (Rule.dead (ofL T2)) = true) x hx

/-- **The rewritten graph computes the C function `xorshift`**: for all naturals on the input channels and any fuel on
which the transcription returns `r`, a complete run reaching `[r]` exists, every complete run under any schedule ends
in that store, and no run is longer. -/
theorem computes {fuel seed₀ rounds₀ r : Nat} (h : kC fuel seed₀ rounds₀ = some r) :
    (∃ n, Run (step G) (St T0 [seed₀, rounds₀]) n (St T2 [r])) ∧
    (∀ m t, Run (step G) (St T0 [seed₀, rounds₀]) m t → Terminal (step G) t → t = St T2 [r]) ∧
    (∃ n, ∀ m u, Run (step G) (St T0 [seed₀, rounds₀]) m u → m ≤ n) := by
  obtain ⟨n, hn⟩ := reach_kC h
  refine ⟨⟨n, hn⟩, fun m t ht hT => ?_, ⟨n, fun m u hu => ?_⟩⟩
  · exact (determinate spine rules spine_nodup ins_ok outs_ok spine_ok (init_inv seed₀ rounds₀)
      hn (final_terminal r) ht hT).1
  · exact no_longer spine rules spine_nodup ins_ok outs_ok spine_ok (init_inv seed₀ rounds₀)
      hn (final_terminal r) hu

/-- **Before and after agree**: on every input on which the C returns `r`, the original graph (C's
`AutoXorshift.auto_computes`) and the rewritten graph both have runs ending with `[r]` on the output, and every
complete run of either ends there. -/
theorem same_as_original {fuel seed₀ rounds₀ r : Nat} (h : kC fuel seed₀ rounds₀ = some r) :
    ((∃ n, Run (step Formal.Net.AutoXorshift.G) (Formal.Net.AutoXorshift.St Formal.Net.XorshiftHw.T0 [seed₀, rounds₀]) n
        (Formal.Net.AutoXorshift.St Formal.Net.XorshiftHw.T2 [r])) ∧
      ∀ m t, Run (step Formal.Net.AutoXorshift.G) (Formal.Net.AutoXorshift.St Formal.Net.XorshiftHw.T0 [seed₀, rounds₀]) m t →
        Terminal (step Formal.Net.AutoXorshift.G) t → t = Formal.Net.AutoXorshift.St Formal.Net.XorshiftHw.T2 [r]) ∧
    ((∃ n, Run (step G) (St T0 [seed₀, rounds₀]) n (St T2 [r])) ∧
      ∀ m t, Run (step G) (St T0 [seed₀, rounds₀]) m t → Terminal (step G) t → t = St T2 [r]) :=
  ⟨⟨(Formal.Net.AutoXorshift.auto_computes h).1, (Formal.Net.AutoXorshift.auto_computes h).2.1⟩,
   ⟨(computes h).1, (computes h).2.1⟩⟩

/-! ## The C returns on every input -/

theorem pick_eq (σ : List Nat) : P.pick 0 σ = some (if isT (tC.eval σ) then ce0 else ce1) := by
  unfold CProg.pick
  have he : P.edges = [ce0, ce1] := rfl
  have ht : P.tests.getD 0 (.lit 0) = tC := rfl
  have s0 : ce0.src = 0 := rfl
  have b0 : ce0.br = true := rfl
  have s1 : ce1.src = 0 := rfl
  have b1 : ce1.br = false := rfl
  rw [he, ht]
  cases h : isT (tC.eval σ) <;> simp only [List.find?_cons, s0, b0, s1, b1, h, beq_self_eq_true, Bool.true_and,
    Bool.and_true, Bool.false_eq_true, if_true, if_false, beq_iff_eq, reduceCtorEq] <;> rfl

/-- The loop measure: signed distance from `i` to `n`. -/
def μ (σ : List Nat) : Nat :=
  (σ.getD 1 0 % 4294967296 + 2147483648) % 4294967296 - (σ.getD 3 0 % 4294967296 + 2147483648) % 4294967296

theorem run_step (f : Nat) (σ : List Nat) (hT : isT (tC.eval σ) = true) :
    P.run (f + 1) 0 σ = P.run f 0 (ce0.upd.map (E.eval σ)) := by
  rw [CProg.run, pick_eq, if_pos hT]; rfl

theorem run_stop (f : Nat) (σ : List Nat) (hT : isT (tC.eval σ) = false) :
    P.run (f + 1) 0 σ = some (ce1.ret.eval (ce1.upd.map (E.eval σ))) := by
  rw [CProg.run, pick_eq, if_neg (by simp [hT])]; rfl

theorem run_ret : ∀ d σ, μ σ ≤ d → ∃ r, P.run (d + 1) 0 σ = some r := by
  intro d
  induction d with
  | zero =>
    intro σ hμ
    cases hT : isT (tC.eval σ)
    · exact ⟨_, run_stop 0 σ hT⟩
    · exfalso
      simp only [tC, E.eval, BOp.ev, c_slt32, isT_ite_t] at hT
      simp only [μ] at hμ
      omega
  | succ d ih =>
    intro σ hμ
    cases hT : isT (tC.eval σ)
    · exact ⟨_, run_stop _ σ hT⟩
    · rw [run_step _ σ hT]
      apply ih
      have hT' := hT
      simp only [tC, E.eval, BOp.ev, c_slt32, isT_ite_t] at hT'
      have u1 : (ce0.upd.map (E.eval σ)).getD 1 0 = σ.getD 1 0 := rfl
      have u3 : (ce0.upd.map (E.eval σ)).getD 3 0 = (σ.getD 3 0 + 1) % 4294967296 := rfl
      simp only [μ, u1, u3] at hμ ⊢
      omega

/-- **The C returns on every input** (at most `2^32` loop iterations; fuel `2^32 + 1` suffices). -/
theorem kC_call (f seed₀ rounds₀ : Nat) : kC f seed₀ rounds₀ = P.run f 0 (P.entry.map (E.eval [seed₀, rounds₀])) := rfl

theorem kC_total (seed₀ rounds₀ : Nat) : ∃ r, kC (2 ^ 32 + 1) seed₀ rounds₀ = some r := by
  rw [kC_call]
  exact run_ret (2 ^ 32) _ (by simp only [μ]; omega)

/-- **Before and after agree on EVERY input**: for every pair of naturals on the input channels there is one value
`r` (the C's) such that both the original and the rewritten graph have complete runs ending with `[r]`, and every
complete run of either ends there. -/
theorem same_all (seed₀ rounds₀ : Nat) : ∃ r,
    ((∃ n, Run (step Formal.Net.AutoXorshift.G) (Formal.Net.AutoXorshift.St Formal.Net.XorshiftHw.T0 [seed₀, rounds₀]) n
        (Formal.Net.AutoXorshift.St Formal.Net.XorshiftHw.T2 [r])) ∧
      ∀ m t, Run (step Formal.Net.AutoXorshift.G) (Formal.Net.AutoXorshift.St Formal.Net.XorshiftHw.T0 [seed₀, rounds₀]) m t →
        Terminal (step Formal.Net.AutoXorshift.G) t → t = Formal.Net.AutoXorshift.St Formal.Net.XorshiftHw.T2 [r]) ∧
    ((∃ n, Run (step G) (St T0 [seed₀, rounds₀]) n (St T2 [r])) ∧
      ∀ m t, Run (step G) (St T0 [seed₀, rounds₀]) m t → Terminal (step G) t → t = St T2 [r]) :=
  let ⟨r, h⟩ := kC_total seed₀ rounds₀
  ⟨r, same_as_original h⟩

end Formal.Rewrite.XorshiftPredec
