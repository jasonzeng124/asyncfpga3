import Formal.Net.GcdHwLib
import Lean.Elab.Tactic

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

set_option linter.unusedSimpArgs false

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

/-- A list of equations `lhs = rhs` over a C state (the invariant of a template). -/
def InvH (I : List (E × E)) (σ : List Nat) : Prop :=
  I.map (fun p => p.1.eval σ) = I.map (fun p => p.2.eval σ)

/-- The invariant the C's new state must satisfy (none after a return). -/
def tinv (Is : List (List (E × E))) (m : Match) : List (E × E) :=
  match m.ce.dst with
  | none => []
  | some _ => Is.getD m.g.dst []

def MatchSem (P : CProg) (ρ : List (List E)) (Is : List (List (E × E))) (m : Match) : Prop :=
  ∀ σ : List Nat, InvH (Is.getD m.k []) σ →
    isT ((P.tests.getD m.ce.src (.lit 0)).eval σ) = m.ce.br →
    isT (m.g.fact.eval ((ρ.getD m.k []).map (E.eval σ))) = m.g.br ∧
    m.g.sig.map (E.eval ((ρ.getD m.k []).map (E.eval σ))) =
      (target ρ m).map (E.eval (m.ce.upd.map (E.eval σ))) ∧
    InvH (tinv Is m) (m.ce.upd.map (E.eval σ))

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

theorem invH_of {I : List (E × E)} {σ : List Nat} {a b : List E}
    (ha : I.map Prod.fst = a) (hb : I.map Prod.snd = b) (h : InvH I σ) :
    a.map (E.eval σ) = b.map (E.eval σ) := by
  unfold InvH at h; subst ha hb
  simp only [List.map_map]; exact h

theorem invH_subst {I : List (E × E)} {σ : List Nat} {s a b : List E}
    (ha : (I.map Prod.fst).map (E.subst s) = a) (hb : (I.map Prod.snd).map (E.subst s) = b)
    (h : a.map (E.eval σ) = b.map (E.eval σ)) : InvH I (s.map (E.eval σ)) := by
  unfold InvH; subst ha hb
  rw [map_subst_eval, map_subst_eval, List.map_map, List.map_map] at h
  exact h

/-- `MatchSem` from an obligation stated on explicit, already-substituted expressions
(this is what the generated file proves, component by component). -/
theorem matchSem_of {P : CProg} {ρ : List (List E)} {Is : List (List (E × E))} {m : Match}
    {t gf : E} {ia ib l1 l2 ja jb : List E}
    (ht : P.tests.getD m.ce.src (.lit 0) = t)
    (hia : (Is.getD m.k []).map Prod.fst = ia) (hib : (Is.getD m.k []).map Prod.snd = ib)
    (h1 : m.g.fact.subst (ρ.getD m.k []) = gf)
    (h2 : m.g.sig.map (E.subst (ρ.getD m.k [])) = l1)
    (h3 : (target ρ m).map (E.subst m.ce.upd) = l2)
    (hja : ((tinv Is m).map Prod.fst).map (E.subst m.ce.upd) = ja)
    (hjb : ((tinv Is m).map Prod.snd).map (E.subst m.ce.upd) = jb)
    (h : ∀ σ : List Nat, ia.map (E.eval σ) = ib.map (E.eval σ) → isT (t.eval σ) = m.ce.br →
      isT (gf.eval σ) = m.g.br ∧ l1.map (E.eval σ) = l2.map (E.eval σ) ∧
      ja.map (E.eval σ) = jb.map (E.eval σ)) :
    MatchSem P ρ Is m := by
  intro σ hI hg
  rw [ht] at hg
  obtain ⟨a, b, c⟩ := h σ (invH_of hia hib hI) hg
  refine ⟨?_, ?_, invH_subst hja hjb c⟩
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
    (P : CProg) (L K : List Nat) (ρ : List (List E)) (Is : List (List (E × E))) (fin : Nat)
    (GE : List GEdge) (M : List Match)
    (hG : ∀ g ∈ GE, ∀ env : List Nat, isT (g.fact.eval env) = g.br →
      Reach (Tm g.src env) (Tm g.dst (g.sig.map (E.eval env))))
    (hC : Cover P L K fin GE M = true)
    (hM : ∀ m ∈ M, MatchSem P ρ Is m) :
    ∀ f k σ r, k ∈ K → InvH (Is.getD k []) σ → P.run f (L.getD k 0) σ = some r →
      Reach (Tm k ((ρ.getD k []).map (E.eval σ))) (Tm fin [r]) := by
  unfold Cover at hC
  simp only [Bool.and_eq_true, List.all_eq_true, Bool.or_eq_true, bne_iff_ne, ne_eq,
    List.any_eq_true, beq_iff_eq] at hC
  obtain ⟨hcov, hms⟩ := hC
  intro f
  induction f with
  | zero => intro k σ r _ _ h; simp [CProg.run] at h
  | succ f ih =>
    intro k σ r hk hI h
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
      have sem := hM m hmM σ hI (by rw [hsrc]; exact hb)
      have step := hG m.g hgin' _ sem.1
      rw [hgs, sem.2.1] at step
      have hI' := sem.2.2
      unfold target at step
      unfold tinv at hI'
      cases hd : m.ce.dst with
      | none =>
        simp only [hd, Option.some.injEq, beq_iff_eq] at h step hdst
        subst h
        rw [hdst] at step
        simpa only [List.map] using step
      | some q =>
        simp only [hd, Bool.and_eq_true, beq_iff_eq] at h step hdst hI'
        obtain ⟨hk', hq⟩ := hdst
        have hk'' : m.g.dst ∈ K := List.contains_iff_mem.mp hk'
        rw [← hq] at h
        exact trans step (ih m.g.dst _ r hk'' hI' h)

theorem sim_call {α : Type} (Tm : Nat → List Nat → α) (Reach : α → α → Prop)
    (trans : ∀ {a b c : α}, Reach a b → Reach b c → Reach a c)
    (P : CProg) (L K : List Nat) (ρ : List (List E)) (Is : List (List (E × E))) (fin : Nat)
    (GE : List GEdge) (M : List Match)
    (hG : ∀ g ∈ GE, ∀ env : List Nat, isT (g.fact.eval env) = g.br →
      Reach (Tm g.src env) (Tm g.dst (g.sig.map (E.eval env))))
    (hC : Cover P L K fin GE M = true)
    (hM : ∀ m ∈ M, MatchSem P ρ Is m)
    (h0 : (0 : Nat) ∈ K) (hstart : L.getD 0 0 = P.start)
    {fuel : Nat} {ins : List Nat} {r : Nat}
    (hin : (ρ.getD 0 []).map (E.eval (P.entry.map (E.eval ins))) = ins)
    (hI0 : InvH (Is.getD 0 []) (P.entry.map (E.eval ins)))
    (h : P.call fuel ins = some r) : Reach (Tm 0 ins) (Tm fin [r]) := by
  unfold CProg.call at h
  rw [← hstart] at h
  have := sim Tm Reach trans P L K ρ Is fin GE M hG hC hM fuel 0 _ r h0 hI0 h
  rwa [hin] at this

/-! ## Abstraction of common subterms

An obligation `X.eval σ = Y.eval σ` whose two sides contain corresponding subterms
`a` (in `X`) and `b` (in `Y`) with `a.eval σ = b.eval σ` is reduced to a smaller one in
which both are replaced by a fresh variable (`X'`, `Y'`, over the extended environment
`θx.map (E.eval σ)`). The generator picks the pairs; these lemmas make the step sound. -/

theorem abs_eq {σ : List Nat} {θx θy : List E} {X Y X' Y' : E}
    (hX : X'.subst θx = X) (hY : Y'.subst θy = Y)
    (hθ : θx.map (E.eval σ) = θy.map (E.eval σ))
    (h : E.eval (θx.map (E.eval σ)) X' = E.eval (θx.map (E.eval σ)) Y') :
    E.eval σ X = E.eval σ Y := by
  rw [← hX, ← hY, eval_subst, eval_subst, ← hθ]; exact h

/-- A 1-bit value as an `if` (so that the bit lemmas of `auto_ops` apply to it). -/
theorem lt2_ite (z : Nat) (h : z < 2 ^ 1) : z = if z = 1 then 1 else 0 := by
  by_cases hz : z = 1 <;> simp [hz] <;> omega

theorem map_cons_eq {σ : List Nat} {a b : E} {l1 l2 : List E} (h1 : E.eval σ a = E.eval σ b)
    (h2 : l1.map (E.eval σ) = l2.map (E.eval σ)) : (a :: l1).map (E.eval σ) = (b :: l2).map (E.eval σ) := by
  simp only [List.map, h1, h2]

theorem tr_list {σ : List Nat} {θ l : List E} (hl : l.map (E.subst θ) = l) :
    l.map (E.eval (θ.map (E.eval σ))) = l.map (E.eval σ) := by
  rw [← map_subst_eval, hl]

theorem tr_one {σ : List Nat} {θ : List E} {e : E} (he : e.subst θ = e) :
    E.eval (θ.map (E.eval σ)) e = E.eval σ e := by
  rw [← eval_subst, he]

theorem tr_hyp {σ : List Nat} {θ ia ib : List E} (ha : ia.map (E.subst θ) = ia)
    (hb : ib.map (E.subst θ) = ib) (h : ia.map (E.eval σ) = ib.map (E.eval σ)) :
    ia.map (E.eval (θ.map (E.eval σ))) = ib.map (E.eval (θ.map (E.eval σ))) := by
  rw [tr_list ha, tr_list hb]; exact h

theorem tr_isT {σ : List Nat} {θ : List E} {t : E} {b : Bool} (ht : t.subst θ = t)
    (h : isT (E.eval σ t) = b) : isT (E.eval (θ.map (E.eval σ)) t) = b := by
  rw [tr_one ht]; exact h

theorem tr_lt {σ : List Nat} {θ : List E} {e : E} {B : Nat} (he : e.subst θ = e)
    (h : E.eval σ e < B) : E.eval (θ.map (E.eval σ)) e < B := by
  rw [tr_one he]; exact h

theorem pow_pos2 (w : Nat) : 0 < 2 ^ w := Nat.two_pow_pos w

theorem b2n_lt2 (b : Bool) : Ops.b2n b < 2 := by cases b <;> decide

theorem bev_lt (o : BOp) (w x y : Nat) (hw : 0 < w) : o.ev w x y < 2 ^ w := by
  have h2 : 2 ≤ 2 ^ w := by
    have : 2 ^ 1 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
    simpa using this
  cases o with
  | addi => exact Nat.mod_lt _ (pow_pos2 w)
  | subi => exact Nat.mod_lt _ (pow_pos2 w)
  | muli => exact Nat.mod_lt _ (pow_pos2 w)
  | andi => exact Nat.mod_lt _ (pow_pos2 w)
  | ori => exact Nat.mod_lt _ (pow_pos2 w)
  | xori => exact Nat.mod_lt _ (pow_pos2 w)
  | shli => exact Nat.mod_lt _ (pow_pos2 w)
  | shrui =>
    show (x % 2 ^ w) >>> y < 2 ^ w
    rw [Nat.shiftRight_eq_div_pow]
    exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) (Nat.mod_lt _ (pow_pos2 w))
  | shrsi =>
    show (if x % 2 ^ w < 2 ^ (w - 1) then (x % 2 ^ w) >>> y
      else (2 ^ w - 1) - ((2 ^ w - 1 - x % 2 ^ w) >>> y)) < 2 ^ w
    have hm := Nat.mod_lt x (pow_pos2 w)
    split
    · rw [Nat.shiftRight_eq_div_pow]; exact Nat.lt_of_le_of_lt (Nat.div_le_self _ _) hm
    · have hp := pow_pos2 w
      have hle : 2 ^ w - 1 - ((2 ^ w - 1 - x % 2 ^ w) >>> y) ≤ 2 ^ w - 1 := Nat.sub_le _ _
      omega
  | cmpi p =>
    show Ops.b2n _ < 2 ^ w
    exact Nat.lt_of_lt_of_le (b2n_lt2 _) h2

/-- The range fact for an abstracted `bin` subterm. -/
theorem abs_lt {σ : List Nat} {θ : List E} {j : Nat} {o : BOp} {w : Nat} {a b : E}
    (hj : θ.getD j (.lit 0) = .bin o w a b) (hw : 0 < w) :
    E.eval (θ.map (E.eval σ)) (.var j) < 2 ^ w := by
  show (θ.map (E.eval σ)).getD j 0 < 2 ^ w
  rw [getD_map_eval, hj]; exact bev_lt o w _ _ hw

/-! ## The generic tactic for the per-match obligations

`auto_ops` unfolds the integer ops to `Nat` arithmetic (`% 2^w`, literal shifts as
`* 2^k` / `/ 2^k`, `x &&& 1` as `x % 2`; other bitwise terms and products of two
variables stay atoms for `omega`), turns comparisons, selects and arithmetic shifts into
`if`s on propositions, splits every `if`, and closes each case with `omega`. No
`native_decide`, no `bv_decide` (whose SAT certificates need `Lean.ofReduceBool`). -/

/-! ### Lemmas for `auto_ops`

Pass A unfolds the plain integer ops (`addi`...`extui`, by their definitions) and
reduces literal powers; it introduces no `if`. Pass B introduces the `if`s (from
`cmpi`, `select`, `shrsi`, `extsi`), using only the PROPOSITIONAL lemmas below, specialised
to widths 1 and 32 with literal moduli. The order matters: a definitional rewrite
(`dsimp`, a simproc) inside the condition of an existing `if` leaves its `Decidable`
instance at the old type, after which neither `split` nor `if_pos` can reduce it;
a propositional rewrite goes through `ite_congr`, which rebuilds the instance. -/

section lemmas
variable (a b : Nat)
theorem c_eq1 : Ops.cmpi .eq 1 a b = if a % 2 = b % 2 then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n Ops.flip; simp only [Nat.reducePow, Nat.reduceSub]
  by_cases h : a % 2 = b % 2 <;> simp [h]
theorem c_ne1 : Ops.cmpi .ne 1 a b = if ¬ a % 2 = b % 2 then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n Ops.flip; simp only [Nat.reducePow, Nat.reduceSub]
  by_cases h : a % 2 = b % 2 <;> simp [h]
theorem c_ult1 : Ops.cmpi .ult 1 a b = if a % 2 < b % 2 then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n Ops.flip; simp only [Nat.reducePow, Nat.reduceSub]
  by_cases h : a % 2 < b % 2 <;> simp [h]
theorem c_ule1 : Ops.cmpi .ule 1 a b = if a % 2 ≤ b % 2 then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n Ops.flip; simp only [Nat.reducePow, Nat.reduceSub]
  by_cases h : a % 2 ≤ b % 2 <;> simp [h]
theorem c_ugt1 : Ops.cmpi .ugt 1 a b = if b % 2 < a % 2 then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n Ops.flip; simp only [Nat.reducePow, Nat.reduceSub]
  by_cases h : b % 2 < a % 2 <;> simp [h]
theorem c_uge1 : Ops.cmpi .uge 1 a b = if b % 2 ≤ a % 2 then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n Ops.flip; simp only [Nat.reducePow, Nat.reduceSub]
  by_cases h : b % 2 ≤ a % 2 <;> simp [h]
theorem c_slt1 : Ops.cmpi .slt 1 a b = if (a % 2 + 1) % 2 < (b % 2 + 1) % 2 then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n Ops.flip; simp only [Nat.reducePow, Nat.reduceSub]
  by_cases h : (a % 2 + 1) % 2 < (b % 2 + 1) % 2 <;> simp [h]
theorem c_sle1 : Ops.cmpi .sle 1 a b = if (a % 2 + 1) % 2 ≤ (b % 2 + 1) % 2 then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n Ops.flip; simp only [Nat.reducePow, Nat.reduceSub]
  by_cases h : (a % 2 + 1) % 2 ≤ (b % 2 + 1) % 2 <;> simp [h]
theorem c_sgt1 : Ops.cmpi .sgt 1 a b = if (b % 2 + 1) % 2 < (a % 2 + 1) % 2 then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n Ops.flip; simp only [Nat.reducePow, Nat.reduceSub]
  by_cases h : (b % 2 + 1) % 2 < (a % 2 + 1) % 2 <;> simp [h]
theorem c_sge1 : Ops.cmpi .sge 1 a b = if (b % 2 + 1) % 2 ≤ (a % 2 + 1) % 2 then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n Ops.flip; simp only [Nat.reducePow, Nat.reduceSub]
  by_cases h : (b % 2 + 1) % 2 ≤ (a % 2 + 1) % 2 <;> simp [h]
theorem c_eq32 : Ops.cmpi .eq 32 a b = if a % 4294967296 = b % 4294967296 then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n Ops.flip; simp only [Nat.reducePow, Nat.reduceSub]
  by_cases h : a % 4294967296 = b % 4294967296 <;> simp [h]
theorem c_ne32 : Ops.cmpi .ne 32 a b = if ¬ a % 4294967296 = b % 4294967296 then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n Ops.flip; simp only [Nat.reducePow, Nat.reduceSub]
  by_cases h : a % 4294967296 = b % 4294967296 <;> simp [h]
theorem c_ult32 : Ops.cmpi .ult 32 a b = if a % 4294967296 < b % 4294967296 then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n Ops.flip; simp only [Nat.reducePow, Nat.reduceSub]
  by_cases h : a % 4294967296 < b % 4294967296 <;> simp [h]
theorem c_ule32 : Ops.cmpi .ule 32 a b = if a % 4294967296 ≤ b % 4294967296 then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n Ops.flip; simp only [Nat.reducePow, Nat.reduceSub]
  by_cases h : a % 4294967296 ≤ b % 4294967296 <;> simp [h]
theorem c_ugt32 : Ops.cmpi .ugt 32 a b = if b % 4294967296 < a % 4294967296 then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n Ops.flip; simp only [Nat.reducePow, Nat.reduceSub]
  by_cases h : b % 4294967296 < a % 4294967296 <;> simp [h]
theorem c_uge32 : Ops.cmpi .uge 32 a b = if b % 4294967296 ≤ a % 4294967296 then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n Ops.flip; simp only [Nat.reducePow, Nat.reduceSub]
  by_cases h : b % 4294967296 ≤ a % 4294967296 <;> simp [h]
theorem c_slt32 : Ops.cmpi .slt 32 a b = if (a % 4294967296 + 2147483648) % 4294967296 < (b % 4294967296 + 2147483648) % 4294967296 then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n Ops.flip; simp only [Nat.reducePow, Nat.reduceSub]
  by_cases h : (a % 4294967296 + 2147483648) % 4294967296 < (b % 4294967296 + 2147483648) % 4294967296 <;> simp [h]
theorem c_sle32 : Ops.cmpi .sle 32 a b = if (a % 4294967296 + 2147483648) % 4294967296 ≤ (b % 4294967296 + 2147483648) % 4294967296 then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n Ops.flip; simp only [Nat.reducePow, Nat.reduceSub]
  by_cases h : (a % 4294967296 + 2147483648) % 4294967296 ≤ (b % 4294967296 + 2147483648) % 4294967296 <;> simp [h]
theorem c_sgt32 : Ops.cmpi .sgt 32 a b = if (b % 4294967296 + 2147483648) % 4294967296 < (a % 4294967296 + 2147483648) % 4294967296 then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n Ops.flip; simp only [Nat.reducePow, Nat.reduceSub]
  by_cases h : (b % 4294967296 + 2147483648) % 4294967296 < (a % 4294967296 + 2147483648) % 4294967296 <;> simp [h]
theorem c_sge32 : Ops.cmpi .sge 32 a b = if (b % 4294967296 + 2147483648) % 4294967296 ≤ (a % 4294967296 + 2147483648) % 4294967296 then 1 else 0 := by
  unfold Ops.cmpi Ops.b2n Ops.flip; simp only [Nat.reducePow, Nat.reduceSub]
  by_cases h : (b % 4294967296 + 2147483648) % 4294967296 ≤ (a % 4294967296 + 2147483648) % 4294967296 <;> simp [h]
theorem shrsi32 (k : Nat) : Ops.shrsi 32 a k =
    if a % 4294967296 < 2147483648 then a % 4294967296 / 2 ^ k
    else 4294967295 - (4294967295 - a % 4294967296) / 2 ^ k := by
  unfold Ops.shrsi; simp only [Nat.reducePow, Nat.reduceSub, Nat.shiftRight_eq_div_pow]
theorem select_ite (s : Nat) : Ops.select s a b = if s % 2 = 1 then a else b := by
  unfold Ops.select; simp only
end lemmas

section bits
variable (p q : Prop) {ip : Decidable p} {iq : Decidable q} (a b : Nat)
theorem sel_ite : Ops.select (@ite Nat p ip 1 0) a b = @ite Nat p ip a b := by
  by_cases h : p <;> simp [h, Ops.select]
theorem isT_ite_t : (isT (@ite Nat p ip 1 0) = true) ↔ p := by
  by_cases h : p <;> simp [h, isT]
theorem isT_ite_f : (isT (@ite Nat p ip 1 0) = false) ↔ ¬ p := by
  by_cases h : p <;> simp [h, isT]
theorem ite_mod2 : @ite Nat p ip 1 0 % 2 = @ite Nat p ip 1 0 := by
  by_cases h : p <;> simp [h]
theorem ite_mod32 : @ite Nat p ip 1 0 % 4294967296 = @ite Nat p ip 1 0 := by
  by_cases h : p <;> simp [h]
theorem ite_eq0 : (@ite Nat p ip 1 0 = 0) ↔ ¬ p := by by_cases h : p <;> simp [h]
theorem ite_eq1 : (@ite Nat p ip 1 0 = 1) ↔ p := by by_cases h : p <;> simp [h]
theorem ite_eq0m2 : (@ite Nat p ip 1 0 = 0 % 2) ↔ ¬ p := by by_cases h : p <;> simp [h]
theorem ite_eq1m2 : (@ite Nat p ip 1 0 = 1 % 2) ↔ p := by by_cases h : p <;> simp [h]
theorem ite_eq0m32 : (@ite Nat p ip 1 0 = 0 % 4294967296) ↔ ¬ p := by by_cases h : p <;> simp [h]
theorem ite_eq1m32 : (@ite Nat p ip 1 0 = 1 % 4294967296) ↔ p := by by_cases h : p <;> simp [h]
theorem ite_or : (@ite Nat p ip 1 0 ||| @ite Nat q iq 1 0) = if p ∨ q then 1 else 0 := by
  by_cases h : p <;> by_cases h' : q <;> simp [h, h']
theorem ite_and : (@ite Nat p ip 1 0 &&& @ite Nat q iq 1 0) = if p ∧ q then 1 else 0 := by
  by_cases h : p <;> by_cases h' : q <;> simp [h, h']
theorem ite_xor : (@ite Nat p ip 1 0 ^^^ @ite Nat q iq 1 0) = if ¬ (p ↔ q) then 1 else 0 := by
  by_cases h : p <;> by_cases h' : q <;> simp [h, h']
end bits
theorem isT_true (v : Nat) : (isT v = true) ↔ v % 2 = 1 := by simp [isT]
theorem isT_false (v : Nat) : (isT v = false) ↔ ¬ v % 2 = 1 := by simp [isT]

open Lean Meta Elab Tactic in
/-- Revert every hypothesis that is a proposition (so that `ite_case` sees them in the goal). -/
elab "revert_props" : tactic => withMainContext do
  let mut fs : Array FVarId := #[]
  for d in ← getLCtx do
    if !d.isImplementationDetail && (← isProp d.type) then fs := fs.push d.fvarId
  let (_, g) ← (← getMainGoal).revert fs
  replaceMainGoal [g]

open Lean Meta Elab Tactic in
/-- Case on the condition of one `if` in the goal (one whose condition contains no `if`)
and reduce it. -/
elab "ite_case" : tactic => withMainContext do
  let isIte (e : Expr) : Bool := e.isAppOfArity ``ite 5
  let t ← instantiateMVars (← getMainTarget)
  let some e := t.find? (fun e => isIte e && !(e.getArg! 1).hasLooseBVars &&
      ((e.getArg! 1).find? isIte).isNone) | throwError "ite_case: no if"
  let stx ← Term.exprToSyntax (e.getArg! 1)
  evalTactic (← `(tactic| (by_cases hc : $stx <;>
    simp only [hc, ↓reduceIte, ite_mod2, ite_mod32, not_false_eq_true, not_true_eq_false,
      true_implies, false_implies, implies_true])))

/-- One obligation (an equality of two evaluated expressions, or an `isT` outcome),
under hypotheses in the context. Fails (does not prove) when the tactic cannot. -/
macro "auto_ops" : tactic => `(tactic| (
  try simp only [E.eval, BOp.ev, UOp.ev, Ops.addi, Ops.subi, Ops.muli, Ops.andi, Ops.ori,
    Ops.xori, Ops.shli, Ops.shrui, Ops.trunci, Ops.extui, Nat.shiftLeft_eq,
    Nat.shiftRight_eq_div_pow, Nat.and_one_is_mod, Nat.reducePow, Nat.reduceMod, Nat.pow_one] at *
  try simp only [c_eq1, c_ne1, c_ult1, c_ule1, c_ugt1, c_uge1, c_slt1, c_sle1, c_sgt1, c_sge1, c_eq32, c_ne32, c_ult32, c_ule32, c_ugt32, c_uge32, c_slt32, c_sle32, c_sgt32, c_sge32, shrsi32, sel_ite, select_ite, isT_ite_t, isT_ite_f, ite_mod2, ite_mod32,
    ite_eq0, ite_eq1, ite_eq0m2, ite_eq1m2, ite_eq0m32, ite_eq1m32, ite_or, ite_and, ite_xor,
    isT_true, isT_false] at *
  all_goals revert_props
  all_goals (repeat' ite_case)
  all_goals (intros; omega)))

end Formal.Net.Auto
