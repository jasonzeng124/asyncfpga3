import Formal.Rewrite.Steps.Absorb
import Formal.Rewrite.Steps.ForkJoin
import Formal.Rewrite.Steps.ForkSplit
import Formal.Rewrite.Steps.ForkComm
import Formal.Rewrite.Steps.Cong
import Formal.Rewrite.Steps.Dedupe
import Formal.Rewrite.Steps.Wire
import Formal.Rewrite.Steps.ConstData
import Formal.Rewrite.Eq2

/-!
# Formal.Rewrite.Steps.Script — a checked rewrite script: any sequence of proved local steps (shard A, 2026-11-19)

**Problem, plainly.** A compiler pass rewrites a handshake graph. If the rewrite can be written as a sequence of
local steps, each of which preserves every complete run whatever surrounds it, then the whole rewrite does. Can Lean
check such a sequence on a real graph, so that the pass needs no per-program proof?

**Proved** (`runScript_sound`): for ANY rule list `rs` and ANY script `ss`, if `runScript rs ss = some (rs', pre,
chg)` then `Sound rs rs' pre chg`: from any store with the channels `pre` empty, every complete run of `rs` is
matched by a complete run of `rs'` ending in the same store outside `chg`, and vice versa. `runScript` is a function
Lean evaluates: it checks each step's side conditions (Bool) and applies it. The steps:
* `absorb lp lq`: fold the comp at `lp` into its only reader at `lq`, which reads it last (`Absorb`);
* `forkjoin lf lc`: a fork whose outputs are exactly the inputs of one comp becomes that comp (`ForkJoin`);
* `forksplit lf k e`: split a fork's outputs after the k-th through a new fork on the fresh channel `e` (`ForkSplit`);
* `forkcomm lc lf x0 x1`: a fork after a single-input comp moves before two copies of it (`ForkComm`);
* `reorder l ins'`: a comp reads its inputs in another order (`Cong`);
* `forder l os'`: a fork lists its outputs in another order (`Cong`);
* `ident l w`: a comp's expression is replaced by an equal one from the identity library (`Cong`; today one
  identity, the collatz loop test, `colIdent`, any width `w ≥ 3`);
* `drop l`: delete a `sink c` that nothing writes (`Cong`);
* `dedupe lf lc a b`: a comp reading two outputs `a, b` of one fork reads `a` twice instead (`Dedupe`);
* `wire lf lc`: a one-output fork feeding a comp is removed, the comp reads the fork's input (`Wire`);
* `constdata lc i v C`: input `i` of the comp at `lc` is a channel of `C`, a class written only by constant comps of
  value `v` and forks of `C`: the comp reads it as the literal `v` (`ConstData`; bdc's BDC_CONST_DATA).
A wrong script makes `runScript` return `none` (a check fails); it cannot prove a wrong theorem.

**Not covered:** token level only; the identity library has one entry.
-/

namespace Formal.Rewrite.Steps

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp

/-! ## Soundness of a rewrite and its composition -/

structure Sound (rs rs' : List Rule) (pre chg : List Nat) : Prop where
  fwd : ∀ {σ0 t : Store Nat Nat} {n : Nat}, (∀ c ∈ pre, σ0 c = []) → Run (step (graph rs)) σ0 n t →
    Terminal (step (graph rs)) t →
    ∃ t' m, Run (step (graph rs')) σ0 m t' ∧ Terminal (step (graph rs')) t' ∧ Agree chg t t'
  bwd : ∀ {σ0 t' : Store Nat Nat} {n : Nat}, (∀ c ∈ pre, σ0 c = []) → Run (step (graph rs')) σ0 n t' →
    Terminal (step (graph rs')) t' →
    ∃ t m, Run (step (graph rs)) σ0 m t ∧ Terminal (step (graph rs)) t ∧ Agree chg t' t

theorem Sound.refl (rs : List Rule) : Sound rs rs [] [] :=
  ⟨fun _ hr ht => ⟨_, _, hr, ht, fun _ _ => rfl⟩, fun _ hr ht => ⟨_, _, hr, ht, fun _ _ => rfl⟩⟩

theorem Sound.symm {rs rs' : List Rule} {p c : List Nat} (h : Sound rs rs' p c) : Sound rs' rs p c :=
  ⟨h.bwd, h.fwd⟩

theorem Sound.trans {rs1 rs2 rs3 : List Rule} {p1 c1 p2 c2 : List Nat} (h1 : Sound rs1 rs2 p1 c1)
    (h2 : Sound rs2 rs3 p2 c2) : Sound rs1 rs3 (p1 ++ p2) (c1 ++ c2) := by
  constructor
  · intro σ0 t n h0 hr ht
    obtain ⟨t2, m2, r2, ht2, a2⟩ := h1.fwd (fun c hc => h0 c (List.mem_append_left _ hc)) hr ht
    obtain ⟨t3, m3, r3, ht3, a3⟩ := h2.fwd (fun c hc => h0 c (List.mem_append_right _ hc)) r2 ht2
    exact ⟨t3, m3, r3, ht3, a2.trans a3⟩
  · intro σ0 t n h0 hr ht
    obtain ⟨t2, m2, r2, ht2, a2⟩ := h2.bwd (fun c hc => h0 c (List.mem_append_right _ hc)) hr ht
    obtain ⟨t1, m1, r1, ht1, a1⟩ := h1.bwd (fun c hc => h0 c (List.mem_append_left _ hc)) r2 ht2
    exact ⟨t1, m1, r1, ht1, (a2.trans a1).mono (fun c hc => by
      rcases List.mem_append.mp hc with h | h
      · exact List.mem_append_right _ h
      · exact List.mem_append_left _ h)⟩

theorem Sound.of_steps {rs rs' : List Rule} (h : ∀ l σ, step (graph rs') σ l = step (graph rs) σ l) :
    Sound rs rs' [] [] :=
  ⟨fun _ hr ht => ⟨_, _, cong_run h hr, cong_terminal h ht, fun _ _ => rfl⟩,
   fun _ hr ht => ⟨_, _, cong_run (fun l σ => (h l σ).symm) hr, cong_terminal (fun l σ => (h l σ).symm) ht,
     fun _ _ => rfl⟩⟩

/-! ## Bool helpers -/

def allL (rs : List Rule) (p : Nat → Rule → Bool) : Bool :=
  (List.range rs.length).all (fun l => match rs[l]? with | some r => p l r | none => true)

theorem of_allL {rs : List Rule} {p : Nat → Rule → Bool} (h : allL rs p = true) :
    ∀ l r, rs[l]? = some r → p l r = true := by
  intro l r hr
  have hl : l < rs.length := by
    rcases Nat.lt_or_ge l rs.length with h | h
    · exact h
    · rw [List.getElem?_eq_none h] at hr; cases hr
  have := List.all_eq_true.mp h l (List.mem_range.mpr hl)
  simp only [hr] at this; exact this

/-- No channel of `r.insL` is in `D`. -/
def readsNone (D : List Nat) (r : Rule) : Bool := r.insL.all (fun c => !decide (c ∈ D))
def writesNone (D : List Nat) (r : Rule) : Bool := r.outsL.all (fun c => !decide (c ∈ D))

theorem of_readsNone {D : List Nat} {r : Rule} (h : readsNone D r = true) : ∀ c ∈ r.insL, c ∉ D := by
  intro c hc hD
  have := List.all_eq_true.mp h c hc
  simp [hD] at this

theorem of_writesNone {D : List Nat} {r : Rule} (h : writesNone D r = true) : ∀ c ∈ r.outsL, c ∉ D := by
  intro c hc hD
  have := List.all_eq_true.mp h c hc
  simp [hD] at this

theorem lt_of_some {rs : List Rule} {l : Nat} {r : Rule} (h : rs[l]? = some r) : l < rs.length := by
  rcases Nat.lt_or_ge l rs.length with h' | h'
  · exact h'
  · rw [List.getElem?_eq_none h'] at h; cases h

theorem set_self {rs : List Rule} {l : Nat} {r a : Rule} (h : rs[l]? = some r) : (rs.set l a)[l]? = some a :=
  List.getElem?_set_self (lt_of_some h)

theorem set_ne {rs : List Rule} {l k : Nat} {a : Rule} (h : l ≠ k) : (rs.set l a)[k]? = rs[k]? :=
  List.getElem?_set_ne h

theorem app_lt {rs : List Rule} {k : Nat} {a : Rule} (h : k < rs.length) : (rs ++ [a])[k]? = rs[k]? :=
  List.getElem?_append_left h

theorem app_len {rs : List Rule} {a : Rule} : (rs ++ [a])[rs.length]? = some a := by simp

theorem app_gt {rs : List Rule} {k : Nat} {a : Rule} (h : rs.length < k) : (rs ++ [a])[k]? = none :=
  List.getElem?_eq_none (by simp; omega)

theorem none_gt {rs : List Rule} {k : Nat} (h : rs.length ≤ k) : rs[k]? = none := List.getElem?_eq_none h

/-! ## The identity library -/

/-- The loop test of bdc's collatz step after the test reads the step's input (`n' == 1` with `n'` the step). -/
def colLhs (w : Nat) : E :=
  .bin (.cmpi .eq) w (.sel (.bin (.cmpi .eq) 1 (.bin .andi 1 (.un .trunci 1 (.var 0)) (.lit 1)) (.lit 0))
    (.bin .shrsi w (.var 0) (.lit 1)) (.bin .addi w (.bin .addi w (.var 0) (.bin .shli w (.var 0) (.lit 1))) (.lit 1)))
    (.lit 1)

def colRhs (w : Nat) : E := .bin (.cmpi .eq) w (.var 0) (.lit 2)

theorem par_bridge (w v : Nat) (hw : 1 ≤ w) :
    Ops.cmpi .eq 1 (Ops.andi 1 (Ops.trunci 1 v) 1) 0 = Ops.cmpi .eq w (Ops.andi w v 1) 0 := by
  have h2 : 2 ≤ 2 ^ w := by
    have : 2 ^ 1 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) hw
    simpa using this
  have a1 : Ops.andi 1 (Ops.trunci 1 v) 1 = v % 2 := by
    simp only [Ops.andi, Ops.trunci, Nat.and_one_is_mod, Nat.pow_one, Nat.mod_mod]
  have a2 : Ops.andi w v 1 = v % 2 := by
    simp only [Ops.andi, Nat.and_one_is_mod]; exact Nat.mod_eq_of_lt (by omega)
  rw [a1, a2]
  simp only [Ops.cmpi, Nat.pow_one, Nat.zero_mod, Nat.mod_mod]
  rw [Nat.mod_eq_of_lt (show v % 2 < 2 ^ w by omega)]

theorem mul3_bridge (w v : Nat) :
    Ops.addi w (Ops.addi w v (Ops.shli w v 1)) 1 = Ops.addi w (Ops.muli w 3 v) 1 := by
  simp only [Ops.addi, Ops.shli, Ops.muli, Nat.shiftLeft_eq, Nat.pow_one]
  rw [Nat.add_mod_mod, show v + v * 2 = 3 * v by omega]

theorem eq1_bridge (w n : Nat) (hw : 2 ≤ w) : Ops.cmpi .eq w n 1 = Ops.cmpi .eq w (Ops.cmpi .ne w n 1) 0 := by
  rw [Formal.Rewrite.Eq2.eqne1 w n hw]
  have h4 : 2 ≤ 2 ^ w := by
    have : 2 ^ 1 ≤ 2 ^ w := Nat.pow_le_pow_right (by decide) (by omega)
    simpa using this
  simp only [Ops.cmpi, Nat.mod_eq_of_lt (show 1 < 2 ^ w by omega)]

theorem colIdent (w : Nat) (hw : 3 ≤ w) (vs : List Nat) : (colRhs w).eval vs = (colLhs w).eval vs := by
  simp only [colRhs, colLhs, E.eval, BOp.ev, UOp.ev]
  rw [par_bridge w _ (by omega), mul3_bridge, eq1_bridge w _ (by omega),
    Formal.Rewrite.Eq2.collatz_eq2 w _ hw]

/-! ## Steps -/

inductive Step
  | absorb (lp lq : Nat)
  | forkjoin (lf lc : Nat)
  | forksplit (lf k e : Nat)
  | forkcomm (lc lf x0 x1 : Nat)
  | reorder (l : Nat) (ins' : List Nat)
  | forder (l : Nat) (os' : List Nat)
  | ident (l w : Nat)
  | drop (l : Nat)
  | dedupe (lf lc a b : Nat)
  | wire (lf lc : Nat)
  | constdata (lc i v : Nat) (C : List Nat)
  deriving Repr

/-- The result of a step: new rules, channels that must start empty, channels the rewrite may leave different. -/
abbrev Res := List Rule × List Nat × List Nat

def applyAB (rs : List Rule) (lp lq : Nat) : Option Res :=
  match rs[lp]?, rs[lq]? with
  | some (.comp (a0 :: ar) p f), some (.comp ins q g) =>
    if ins = ins.dropLast ++ [p] ∧ lp ≠ lq ∧ (p :: (ins.dropLast ++ a0 :: ar)).Nodup ∧
        q ∉ p :: (ins.dropLast ++ a0 :: ar) ∧
        allL rs (fun l r => l == lp || l == lq || readsNone (p :: a0 :: ar) r) = true ∧
        allL rs (fun l r => l == lp || writesNone [p] r) = true then
      some ((rs.set lp (.sink p)).set lq
        (.comp (ins.dropLast ++ a0 :: ar) q (absorbE ins.dropLast.length (a0 :: ar).length f g)), [p], p :: a0 :: ar)
    else none
  | _, _ => none

def applyFJ (rs : List Rule) (lf lc : Nat) : Option Res :=
  match rs[lf]?, rs[lc]? with
  | some (.fork x (c0 :: cr)), some (.comp ins y g) =>
    if ins = c0 :: cr ∧ lf ≠ lc ∧ (x :: c0 :: cr).Nodup ∧ y ∉ x :: c0 :: cr ∧
        allL rs (fun l r => l == lf || l == lc || readsNone (x :: c0 :: cr) r) = true ∧
        allL rs (fun l r => l == lf || writesNone (c0 :: cr) r) = true then
      some ((rs.set lf (.comp [x] y (allZero (c0 :: cr) g))).set lc (.sink c0), c0 :: cr, c0 :: cr)
    else none
  | _, _ => none

def applyFS (rs : List Rule) (lf k e : Nat) : Option Res :=
  match rs[lf]? with
  | some (.fork x os) =>
    if (x :: e :: (os.take k ++ os.drop k)).Nodup ∧
        allL rs (fun l r => l == lf || readsNone [e] r) = true ∧
        allL rs (fun l r => l == lf || writesNone (e :: os.take k) r) = true then
      some (rs.set lf (.fork x (e :: os.drop k)) ++ [.fork e (os.take k)], [e], [e])
    else none
  | _ => none

def applyFC (rs : List Rule) (lc lf x0 x1 : Nat) : Option Res :=
  match rs[lc]?, rs[lf]? with
  | some (.comp [x] y G), some (.fork y' [y0, y1]) =>
    if y' = y ∧ [x, y, x0, x1, y0, y1].Nodup ∧
        allL rs (fun l r => l == lc || l == lf || readsNone [x, y, x0, x1] r) = true ∧
        allL rs (fun l r => l == lc || l == lf || writesNone [y, x0, x1, y0, y1] r) = true then
      some (((rs.set lc (.fork x [x0, x1])).set lf (.comp [x0] y0 G)) ++ [.comp [x1] y1 G], [y, x0, x1], [y, x0, x1])
    else none
  | _, _ => none

def applyRO (rs : List Rule) (l : Nat) (ins' : List Nat) : Option Res :=
  match rs[l]? with
  | some (.comp ins o F) =>
    if ins.all (fun c => decide (c ∈ ins')) = true ∧ ins'.all (fun c => decide (c ∈ ins)) = true then
      some (rs.set l (.comp ins' o (reindex ins ins' F)), [], [])
    else none
  | _ => none

def applyFO (rs : List Rule) (l : Nat) (os' : List Nat) : Option Res :=
  match rs[l]? with
  | some (.fork i os) =>
    if os.all (fun c => decide (c ∈ os')) = true ∧ os'.all (fun c => decide (c ∈ os)) = true then
      some (rs.set l (.fork i os'), [], [])
    else none
  | _ => none

def applyID (rs : List Rule) (l w : Nat) : Option Res :=
  match rs[l]? with
  | some (.comp ins o F) =>
    if F = colLhs w ∧ 3 ≤ w then some (rs.set l (.comp ins o (colRhs w)), [], []) else none
  | _ => none

def applyDR (rs : List Rule) (l : Nat) : Option Res :=
  match rs[l]? with
  | some (.sink c) =>
    if allL rs (fun _ r => writesNone [c] r) = true then some (rs.eraseIdx l, [c], []) else none
  | _ => none

def applyDD (rs : List Rule) (lf lc a b : Nat) : Option Res :=
  match rs[lf]?, rs[lc]? with
  | some (.fork x os), some (.comp ins y F) =>
    if a ∈ os ∧ b ∈ os ∧ a ∈ ins ∧ b ∈ ins ∧ a ≠ b ∧ os.Nodup ∧ ins.Nodup ∧ x ∉ os ∧ y ∉ ins ∧
        allL rs (fun l r => l == lc || readsNone [a, b] r) = true ∧
        allL rs (fun l r => l == lf || writesNone [a, b] r) = true then
      some ((rs.set lf (.fork x (os.erase b))).set lc (.comp (ins.erase b) y (dedupE ins a b F)), [a, b], [b])
    else none
  | _, _ => none

def applyW (rs : List Rule) (lf lc : Nat) : Option Res :=
  match rs[lf]?, rs[lc]? with
  | some (.fork x [a]), some (.comp ins y F) =>
    if a ∈ ins ∧ ins.Nodup ∧ x ∉ ins ∧ x ≠ a ∧ y ∉ x :: ins ∧
        allL rs (fun l r => l == lf || l == lc || readsNone [x, a] r) = true ∧
        allL rs (fun l r => l == lf || writesNone [a] r) = true then
      some ((rs.set lf (.sink a)).set lc (.comp (ins.map (swA a x)) y F), [a], [x, a])
    else none
  | _, _ => none

def constWriterB (C : List Nat) (v : Nat) (r : Rule) : Bool :=
  r.outsL.all fun c => !decide (c ∈ C) || match r with
    | .comp _ _ (.lit w) => w == v
    | .fork k _ => decide (k ∈ C)
    | _ => false

theorem of_constWriterB {C : List Nat} {v : Nat} {r : Rule} (h : constWriterB C v r = true) : ConstWriter C v r := by
  intro c hc ho
  have := List.all_eq_true.mp h c ho
  simp only [hc, decide_true, Bool.not_true, Bool.false_or] at this
  cases r with
  | comp ins o e =>
    cases e with
    | lit w =>
      simp only [beq_iff_eq] at this; subst this
      simp only [Rule.outsL, List.mem_singleton] at ho; subst ho
      exact Or.inl ⟨ins, rfl⟩
    | _ => simp at this
  | fork k os => simp only [decide_eq_true_eq] at this; exact Or.inr ⟨k, os, rfl, this⟩
  | _ => simp at this

def applyCD (rs : List Rule) (lc i v : Nat) (C : List Nat) : Option Res :=
  match rs[lc]? with
  | some (.comp ins y F) =>
    if i < ins.length ∧ ins.getD i 0 ∈ C ∧ y ∉ C ∧ allL rs (fun _ r => constWriterB C v r) = true then
      some (rs.set lc (.comp ins y (constE ins.length i v F)), C, [])
    else none
  | _ => none

def applyStep (rs : List Rule) : Step → Option Res
  | .absorb lp lq => applyAB rs lp lq
  | .forkjoin lf lc => applyFJ rs lf lc
  | .forksplit lf k e => applyFS rs lf k e
  | .forkcomm lc lf x0 x1 => applyFC rs lc lf x0 x1
  | .reorder l ins' => applyRO rs l ins'
  | .forder l os' => applyFO rs l os'
  | .ident l w => applyID rs l w
  | .drop l => applyDR rs l
  | .dedupe lf lc a b => applyDD rs lf lc a b
  | .wire lf lc => applyW rs lf lc
  | .constdata lc i v C => applyCD rs lc i v C

def runScript : List Rule → List Step → Option Res
  | rs, [] => some (rs, [], [])
  | rs, s :: ss =>
    match applyStep rs s with
    | some (rs1, p1, c1) =>
      match runScript rs1 ss with
      | some (rs2, p2, c2) => some (rs2, p1 ++ p2, c1 ++ c2)
      | none => none
    | none => none

end Formal.Rewrite.Steps
