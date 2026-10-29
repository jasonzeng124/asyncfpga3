import Formal.Net.GcdHwLib

/-!
# Automatic all-inputs token proofs: the generic part (probe C-vk2)

Core Lean only. `formal/tools/autoproof/autoproof.py` generates, for a loop kernel, a
file `Formal/Net/Auto<K>.lean` that instantiates the theorem `sim_call` below. Nothing
here is kernel-specific.

## The C side: a test-point automaton (`CProg`)
The generator's C front end (`formal/tools/autoproof/cfront.py`) reads the C function
(a small subset: `int`/`unsigned` scalars, `= op= ++ --`, `if`/`else`, `while`, `do`,
`for`, `return`, the operators `+ - * & | ^ ~ << >> == != < <= > >= ! && || ?:` and
casts) and cuts it at its tests. A *test point* is a loop test or an `if` whose arms are
not plain assignments (assignment-only `if`s and `?:` are pure, so they become
`E.sel`). The state is the vector of C variables (`int` = i32 bit pattern as a `Nat`,
arithmetic with wraparound: the hardware's `Ops`, not C's undefined signed overflow).
`CEdge` = from test point `src`, on outcome `br`, run the straight-line code `upd`
(a parallel assignment, over the state at `src`) to the next test point `dst`, or
`dst = none`: return `ret` (over the updated state). `CProg.run` is fuelled;
`none` = fuel ran out or no edge (never claimed to terminate).

## The graph side: the symbolic segments of dfimport (`GEdge`)
dfimport's `--segments` cuts the graph's symbolic run at every pending branch: template
`src` with environment `env` reaches template `dst` with `sig.map (E.eval env)` whenever
the branch fact `fact` has outcome `br` (theorems `seg*`, kernel-checked by
`execL_of_chainOK`).

## The correspondence
`L k` is the C test point of template `k`, `ρ k` expresses template `k`'s variables as
expressions over the C state there (found by the generator by co-simulation; proved here,
not trusted). A `Match` pairs a template, a C edge and a graph edge. `Cover` (a Boolean
check, `decide`d) says every C edge out of every template's test point is matched, the
matched graph edge leaves that template, and it lands on the template of the C edge's
destination (or on the final template for a return). `MatchSem` (proved per match by a
generic tactic, `auto_ops`) says that under the C edge's outcome the graph edge's fact
has the matching outcome and the graph's new environment is `ρ` of the C's new state.

`sim_call`: if the C program returns `r` on inputs `ins`, the graph reaches the final
template with `[r]` from the initial template with `ins`.
-/

namespace Formal.Net.Auto

open Formal.Net.GcdHw

/-! ## C programs as test-point automata -/

structure CEdge where
  src : Nat
  br : Bool
  upd : List E
  dst : Option Nat
  ret : E
  deriving DecidableEq, Repr

structure CProg where
  entry : List E
  start : Nat
  tests : List E
  edges : List CEdge

/-- The branch test of the semantics: bit 0. -/
def isT (v : Nat) : Bool := v % 2 == 1

def CProg.pick (P : CProg) (p : Nat) (σ : List Nat) : Option CEdge :=
  P.edges.find? (fun e => e.src == p && e.br == isT ((P.tests.getD p (.lit 0)).eval σ))

def CProg.run (P : CProg) : Nat → Nat → List Nat → Option Nat
  | 0, _, _ => none
  | f + 1, p, σ =>
    match P.pick p σ with
    | none => none
    | some e =>
      match e.dst with
      | none => some (e.ret.eval (e.upd.map (E.eval σ)))
      | some q => P.run f q (e.upd.map (E.eval σ))

/-- The C function on inputs `ins` (the entry code runs first). -/
def CProg.call (P : CProg) (fuel : Nat) (ins : List Nat) : Option Nat :=
  P.run fuel P.start (P.entry.map (E.eval ins))

/-! ## Graph edges, matches, coverage -/

structure GEdge where
  src : Nat
  fact : E
  br : Bool
  sig : List E
  dst : Nat
  deriving DecidableEq, Repr

structure Match where
  k : Nat
  ce : CEdge
  g : GEdge
  deriving DecidableEq, Repr

/-- What the matched graph edge's new environment must be, over the C's new state. -/
def target (ρ : List (List E)) (m : Match) : List E :=
  match m.ce.dst with
  | none => [m.ce.ret]
  | some _ => ρ.getD m.g.dst []

def MatchSem (P : CProg) (ρ : List (List E)) (m : Match) : Prop :=
  ∀ σ : List Nat, isT ((P.tests.getD m.ce.src (.lit 0)).eval σ) = m.ce.br →
    isT (m.g.fact.eval ((ρ.getD m.k []).map (E.eval σ))) = m.g.br ∧
    m.g.sig.map (E.eval ((ρ.getD m.k []).map (E.eval σ))) =
      (target ρ m).map (E.eval (m.ce.upd.map (E.eval σ)))

def Cover (P : CProg) (L K : List Nat) (fin : Nat) (GE : List GEdge) (M : List Match) : Bool :=
  K.all (fun k => P.edges.all (fun ce =>
    ce.src != L.getD k 0 || M.any (fun m => m.k == k && m.ce == ce))) &&
  M.all (fun m => GE.contains m.g && m.g.src == m.k && m.ce.src == L.getD m.k 0 &&
    match m.ce.dst with
    | none => m.g.dst == fin
    | some q => K.contains m.g.dst && L.getD m.g.dst 0 == q)

theorem map_subst_eval (σ : List Nat) (s l : List E) :
    (l.map (E.subst s)).map (E.eval σ) = l.map (E.eval (s.map (E.eval σ))) := by
  rw [List.map_map]; apply List.map_congr_left; intro e _
  exact eval_subst σ s e

/-- `MatchSem` from an obligation stated on explicit, already-substituted expressions
(this is what the generated file proves with `auto_ops`). -/
theorem matchSem_of {P : CProg} {ρ : List (List E)} {m : Match} {t gf : E} {l1 l2 : List E}
    (ht : P.tests.getD m.ce.src (.lit 0) = t)
    (h1 : m.g.fact.subst (ρ.getD m.k []) = gf)
    (h2 : m.g.sig.map (E.subst (ρ.getD m.k [])) = l1)
    (h3 : (target ρ m).map (E.subst m.ce.upd) = l2)
    (h : ∀ σ : List Nat, isT (t.eval σ) = m.ce.br →
      isT (gf.eval σ) = m.g.br ∧ l1.map (E.eval σ) = l2.map (E.eval σ)) :
    MatchSem P ρ m := by
  intro σ hg
  rw [ht] at hg
  obtain ⟨a, b⟩ := h σ hg
  refine ⟨?_, ?_⟩
  · rw [← h1, eval_subst] at a; exact a
  · rw [← h2, ← h3, map_subst_eval, map_subst_eval] at b
    exact b

/-! ## The simulation theorem -/

theorem pick_spec {P : CProg} {p : Nat} {σ : List Nat} {e : CEdge} (h : P.pick p σ = some e) :
    e ∈ P.edges ∧ e.src = p ∧ isT ((P.tests.getD p (.lit 0)).eval σ) = e.br := by
  unfold CProg.pick at h
  have hm := List.mem_of_find?_eq_some h
  have hp := List.find?_some h
  simp only [Bool.and_eq_true, beq_iff_eq] at hp
  exact ⟨hm, hp.1, hp.2.symm⟩

theorem sim {α : Type} (Tm : Nat → List Nat → α) (Reach : α → α → Prop)
    (trans : ∀ {a b c : α}, Reach a b → Reach b c → Reach a c)
    (P : CProg) (L K : List Nat) (ρ : List (List E)) (fin : Nat) (GE : List GEdge) (M : List Match)
    (hG : ∀ g ∈ GE, ∀ env : List Nat, isT (g.fact.eval env) = g.br →
      Reach (Tm g.src env) (Tm g.dst (g.sig.map (E.eval env))))
    (hC : Cover P L K fin GE M = true)
    (hM : ∀ m ∈ M, MatchSem P ρ m) :
    ∀ f k σ r, k ∈ K → P.run f (L.getD k 0) σ = some r →
      Reach (Tm k ((ρ.getD k []).map (E.eval σ))) (Tm fin [r]) := by
  unfold Cover at hC
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    List.any_eq_true, beq_iff_eq] at hC
  obtain ⟨hcov, hms⟩ := hC
  intro f
  induction f with
  | zero => intro k σ r _ h; simp [CProg.run] at h
  | succ f ih =>
    intro k σ r hk h
    simp only [CProg.run] at h
    cases hp : P.pick (L.getD k 0) σ with
    | none => rw [hp] at h; cases h
    | some ce =>
      rw [hp] at h
      obtain ⟨hce, hsrc, hb⟩ := pick_spec hp
      have hcv := hcov k hk ce hce
      rcases hcv with hne | ⟨m, hmM, hmk, hmce⟩
      · exact absurd hsrc hne
      subst hmk hmce
      have hmo := hms m hmM
      obtain ⟨⟨⟨hgin, hgs⟩, hcs⟩, hdst⟩ := hmo
      have hgin' : m.g ∈ GE := List.contains_iff_mem.mp hgin
      have sem := hM m hmM σ (by rw [hsrc]; exact hb)
      have step := hG m.g hgin' _ sem.1
      rw [hgs, sem.2] at step
      unfold target at step
      cases hd : m.ce.dst with
      | none =>
        simp only [hd, Option.some.injEq, beq_iff_eq] at h step hdst
        subst h
        rw [hdst] at step
        simpa only [List.map] using step
      | some q =>
        simp only [hd, Bool.and_eq_true, beq_iff_eq] at h step hdst
        obtain ⟨hk', hq⟩ := hdst
        have hk'' : m.g.dst ∈ K := List.contains_iff_mem.mp hk'
        rw [← hq] at h
        exact trans step (ih m.g.dst _ r hk'' h)

theorem sim_call {α : Type} (Tm : Nat → List Nat → α) (Reach : α → α → Prop)
    (trans : ∀ {a b c : α}, Reach a b → Reach b c → Reach a c)
    (P : CProg) (L K : List Nat) (ρ : List (List E)) (fin : Nat) (GE : List GEdge) (M : List Match)
    (hG : ∀ g ∈ GE, ∀ env : List Nat, isT (g.fact.eval env) = g.br →
      Reach (Tm g.src env) (Tm g.dst (g.sig.map (E.eval env))))
    (hC : Cover P L K fin GE M = true)
    (hM : ∀ m ∈ M, MatchSem P ρ m)
    (h0 : (0 : Nat) ∈ K) (hstart : L.getD 0 0 = P.start)
    {fuel : Nat} {ins : List Nat} {r : Nat}
    (hin : (ρ.getD 0 []).map (E.eval (P.entry.map (E.eval ins))) = ins)
    (h : P.call fuel ins = some r) : Reach (Tm 0 ins) (Tm fin [r]) := by
  unfold CProg.call at h
  rw [← hstart] at h
  have := sim Tm Reach trans P L K ρ fin GE M hG hC hM fuel 0 _ r h0 h
  rwa [hin] at this

/-! ## The generic tactic for the per-match obligations

Phase 1 turns every `cmpi` into an `if` on a proposition and every `select` on such a
bit into an `if` (before the comparison's operands are unfolded, so that the `if`s keep
the instances these lemmas match). Phase 2 unfolds the integer ops to `Nat` arithmetic
(`% 2^w`, literal shifts as `* 2^k` / `/ 2^k`, `x &&& 1` as `x % 2`; other bitwise terms
stay atoms). Then every `if` is split and `omega` closes each case. No `native_decide`,
no `bv_decide` (which needs `Lean.ofReduceBool` for its SAT certificates). -/

section lemmas
variable (w a b : Nat)
theorem c_eq : Ops.cmpi .eq w a b = if a % 2 ^ w = b % 2 ^ w then 1 else 0 := by
  simp only [Ops.cmpi, Ops.b2n]; by_cases h : a % 2 ^ w = b % 2 ^ w <;> simp [h]
theorem c_ne : Ops.cmpi .ne w a b = if a % 2 ^ w = b % 2 ^ w then 0 else 1 := by
  simp only [Ops.cmpi, Ops.b2n]; by_cases h : a % 2 ^ w = b % 2 ^ w <;> simp [h]
theorem c_ult : Ops.cmpi .ult w a b = if a % 2 ^ w < b % 2 ^ w then 1 else 0 := by
  simp only [Ops.cmpi, Ops.b2n]; by_cases h : a % 2 ^ w < b % 2 ^ w <;> simp [h]
theorem c_ule : Ops.cmpi .ule w a b = if a % 2 ^ w ≤ b % 2 ^ w then 1 else 0 := by
  simp only [Ops.cmpi, Ops.b2n]; by_cases h : a % 2 ^ w ≤ b % 2 ^ w <;> simp [h]
theorem c_ugt : Ops.cmpi .ugt w a b = if b % 2 ^ w < a % 2 ^ w then 1 else 0 := by
  simp only [Ops.cmpi, Ops.b2n]; by_cases h : b % 2 ^ w < a % 2 ^ w <;> simp [h]
theorem c_uge : Ops.cmpi .uge w a b = if b % 2 ^ w ≤ a % 2 ^ w then 1 else 0 := by
  simp only [Ops.cmpi, Ops.b2n]; by_cases h : b % 2 ^ w ≤ a % 2 ^ w <;> simp [h]
theorem c_slt : Ops.cmpi .slt w a b = if Ops.flip w a < Ops.flip w b then 1 else 0 := by
  simp only [Ops.cmpi, Ops.b2n]; by_cases h : Ops.flip w a < Ops.flip w b <;> simp [h]
theorem c_sle : Ops.cmpi .sle w a b = if Ops.flip w a ≤ Ops.flip w b then 1 else 0 := by
  simp only [Ops.cmpi, Ops.b2n]; by_cases h : Ops.flip w a ≤ Ops.flip w b <;> simp [h]
theorem c_sgt : Ops.cmpi .sgt w a b = if Ops.flip w b < Ops.flip w a then 1 else 0 := by
  simp only [Ops.cmpi, Ops.b2n]; by_cases h : Ops.flip w b < Ops.flip w a <;> simp [h]
theorem c_sge : Ops.cmpi .sge w a b = if Ops.flip w b ≤ Ops.flip w a then 1 else 0 := by
  simp only [Ops.cmpi, Ops.b2n]; by_cases h : Ops.flip w b ≤ Ops.flip w a <;> simp [h]
end lemmas

theorem sel_ite (p : Prop) [Decidable p] (a b : Nat) :
    Ops.select (if p then 1 else 0) a b = if p then a else b := by
  by_cases h : p <;> simp [h, Ops.select]
theorem sel_ite' (p : Prop) [Decidable p] (a b : Nat) :
    Ops.select (if p then 0 else 1) a b = if p then b else a := by
  by_cases h : p <;> simp [h, Ops.select]
theorem isT_ite_t (p : Prop) [Decidable p] : (isT (if p then 1 else 0) = true) ↔ p := by
  by_cases h : p <;> simp [h, isT]
theorem isT_ite_f (p : Prop) [Decidable p] : (isT (if p then 1 else 0) = false) ↔ ¬ p := by
  by_cases h : p <;> simp [h, isT]
theorem isT_ite_t' (p : Prop) [Decidable p] : (isT (if p then 0 else 1) = true) ↔ ¬ p := by
  by_cases h : p <;> simp [h, isT]
theorem isT_ite_f' (p : Prop) [Decidable p] : (isT (if p then 0 else 1) = false) ↔ p := by
  by_cases h : p <;> simp [h, isT]
theorem isT_true (v : Nat) : (isT v = true) ↔ v % 2 = 1 := by simp [isT]
theorem isT_false (v : Nat) : (isT v = false) ↔ ¬ v % 2 = 1 := by simp [isT]
theorem select_def (s a b : Nat) : Ops.select s a b = if s % 2 = 1 then a else b := rfl

/-- One obligation: `e1.eval σ = e2.eval σ` or an `isT` outcome, under a hypothesis `h`. -/
macro "auto_ops" : tactic => `(tactic| (
  try simp only [E.eval, BOp.ev, UOp.ev, c_eq, c_ne, c_ult, c_ule, c_ugt, c_uge, c_slt, c_sle,
    c_sgt, c_sge, sel_ite, sel_ite', isT_ite_t, isT_ite_f, isT_ite_t', isT_ite_f'] at *
  try simp only [Ops.addi, Ops.subi, Ops.muli, Ops.andi, Ops.ori, Ops.xori, Ops.shli,
    Ops.shrui, Ops.shrsi, Ops.flip, Ops.trunci, Ops.extui, Ops.extsi, select_def,
    isT_true, isT_false, Nat.and_one_is_mod, Nat.shiftLeft_eq, Nat.shiftRight_eq_div_pow,
    Nat.reducePow, Nat.reduceSub, Nat.reduceMod, Nat.reduceAdd, Nat.reduceMul,
    Nat.pow_one, Nat.pow_zero] at *
  repeat' split
  all_goals omega))

/-- The whole per-match obligation: split the conjunction and the list equality into
components; each closes by `rfl` (syntactically equal) or `auto_ops`. -/
macro "auto_match" : tactic => `(tactic| (
  intro σ h
  simp only [List.map, List.cons.injEq, and_true] at *
  repeat' apply And.intro
  all_goals first | with_reducible rfl | auto_ops))

end Formal.Net.Auto
