import Formal.Net.Kahn

/-!
# Imported handshake graphs: op semantics, rule library, checkers (probe C-8i)

Core Lean only. This is the target language of `formal/tools/dfimport/mlir2lean.py`,
which exports the graph bdc ACTUALLY emits (bdc's parser + its op-fusion plan:
fused regions, absorbed (source, constant) pairs, absorbed forks, `br` and
1-input `merge` as wires) as a `List Rule`.

* Values are `Nat`, every channel of width `w` carrying a value in `[0, 2^w)`.
  `Ops` gives each op the integer semantics of the Verilog bdc emits for it
  (`bdc/compute.py` BINARY/CMPI, `bdc/emit.py` reshape/select), which is MLIR's
  `arith` semantics at width `w` (two's complement wraparound) wherever MLIR
  defines it; differences (shift amounts `>= w`, which MLIR makes poison) are
  listed in `formal/notes/C-8i-gcdhw.md`.
* A `Rule` is one firing rule (one Kahn node, or one input of a `control_merge`).
  `Rule.fire` is generic over a value interface `VI V`: `V = Nat` is the real
  semantics, `V = E` (expressions) is symbolic execution. `hom_fire` says
  symbolic firing maps to Nat firing under `eval env` whenever the branch
  facts the symbolic run assumed hold.
* `graph rs : Nat → Node Nat Nat` is the Kahn graph (8b's `Node`).
  `wfOn_of_check` derives 8b's `WFOn` from two Boolean checks plus the
  one-token-on-the-control-spine invariant `Inv P`; `closed_of_check` proves
  `Inv P` closed under every firing from a per-rule Boolean check.
-/

namespace Formal.Net.GcdHw

open Formal.Net.Kahn

/-! ## Integer semantics of the ops, at width `w` -/

namespace Ops
def addi (w a b : Nat) : Nat := (a + b) % 2 ^ w
def subi (w a b : Nat) : Nat := (a % 2 ^ w + 2 ^ w - b % 2 ^ w) % 2 ^ w
def muli (w a b : Nat) : Nat := (a * b) % 2 ^ w
def andi (w a b : Nat) : Nat := (a &&& b) % 2 ^ w
def ori  (w a b : Nat) : Nat := (a ||| b) % 2 ^ w
def xori (w a b : Nat) : Nat := (a ^^^ b) % 2 ^ w
/-- Verilog `a << b` truncated to `w` bits (0 once `b >= w`). -/
def shli (w a b : Nat) : Nat := (a <<< b) % 2 ^ w
/-- Verilog `a >> b` (logical). -/
def shrui (w a b : Nat) : Nat := (a % 2 ^ w) >>> b
/-- Verilog `$signed(a) >>> b`: arithmetic shift; a negative `x` shifts as
`~((~x) >> b)`, so `b >= w` gives all sign bits. -/
def shrsi (w a b : Nat) : Nat :=
  if a % 2 ^ w < 2 ^ (w - 1) then (a % 2 ^ w) >>> b
  else (2 ^ w - 1) - ((2 ^ w - 1 - a % 2 ^ w) >>> b)
/-- Signed order as bdc builds it: flip the sign bit, compare unsigned. -/
def flip (w a : Nat) : Nat := (a % 2 ^ w + 2 ^ (w - 1)) % 2 ^ w
def b2n (b : Bool) : Nat := if b then 1 else 0
end Ops

inductive Pred | eq | ne | ult | ule | ugt | uge | slt | sle | sgt | sge
  deriving DecidableEq, Repr

namespace Ops
def cmpi (p : Pred) (w a b : Nat) : Nat :=
  let x := a % 2 ^ w; let y := b % 2 ^ w
  let sx := flip w a; let sy := flip w b
  b2n <| match p with
    | .eq => x == y | .ne => x != y
    | .ult => decide (x < y) | .ule => decide (x ≤ y)
    | .ugt => decide (y < x) | .uge => decide (y ≤ x)
    | .slt => decide (sx < sy) | .sle => decide (sx ≤ sy)
    | .sgt => decide (sy < sx) | .sge => decide (sy ≤ sx)
/-- Verilog `s ? a : b` with a 1-bit `s`. -/
def select (s a b : Nat) : Nat := if s % 2 = 1 then a else b
def trunci (w a : Nat) : Nat := a % 2 ^ w
/-- zero extension from `sw` bits. -/
def extui (sw a : Nat) : Nat := a % 2 ^ sw
/-- sign extension from `sw` to `dw` bits. -/
def extsi (sw dw a : Nat) : Nat :=
  if a % 2 ^ sw < 2 ^ (sw - 1) then a % 2 ^ sw else a % 2 ^ sw + 2 ^ dw - 2 ^ sw
end Ops

inductive UOp | trunci | extui | extsi (dw : Nat)
  deriving DecidableEq, Repr

inductive BOp | addi | subi | muli | andi | ori | xori | shli | shrsi | shrui | cmpi (p : Pred)
  deriving DecidableEq, Repr

/-- Expressions: the body of a (fused) compute region, and symbolic token values.
`var k` is region input `k` (or environment variable `k` in a symbolic store).
For `un o w a`, `w` is the result width for `trunci` and the SOURCE width for
`extui`/`extsi`. For `bin o w a b`, `w` is the operand width. -/
inductive E
  | var (k : Nat)
  | lit (v : Nat)
  | un (o : UOp) (w : Nat) (a : E)
  | bin (o : BOp) (w : Nat) (a b : E)
  | sel (s a b : E)
  deriving DecidableEq, Repr

def UOp.ev : UOp → Nat → Nat → Nat
  | .trunci, w, a => Ops.trunci w a
  | .extui, w, a => Ops.extui w a
  | .extsi dw, w, a => Ops.extsi w dw a

def BOp.ev : BOp → Nat → Nat → Nat → Nat
  | .addi => Ops.addi | .subi => Ops.subi | .muli => Ops.muli | .andi => Ops.andi
  | .ori => Ops.ori | .xori => Ops.xori | .shli => Ops.shli | .shrsi => Ops.shrsi
  | .shrui => Ops.shrui | .cmpi p => Ops.cmpi p

def E.eval (env : List Nat) : E → Nat
  | .var k => env.getD k 0
  | .lit v => v
  | .un o w a => o.ev w (a.eval env)
  | .bin o w a b => o.ev w (a.eval env) (b.eval env)
  | .sel s a b => Ops.select (s.eval env) (a.eval env) (b.eval env)

def E.subst (σ : List E) : E → E
  | .var k => σ.getD k (.lit 0)
  | .lit v => .lit v
  | .un o w a => .un o w (a.subst σ)
  | .bin o w a b => .bin o w (a.subst σ) (b.subst σ)
  | .sel s a b => .sel (s.subst σ) (a.subst σ) (b.subst σ)

theorem getD_map_eval (env : List Nat) (σ : List E) (k : Nat) :
    (σ.map (E.eval env)).getD k 0 = (σ.getD k (.lit 0)).eval env := by
  rw [List.getD_eq_getElem?_getD, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases σ[k]? <;> rfl

theorem eval_subst (env : List Nat) (σ : List E) :
    ∀ e : E, (e.subst σ).eval env = e.eval (σ.map (E.eval env))
  | .var k => (getD_map_eval env σ k).symm
  | .lit _ => rfl
  | .un o w a => by simp only [E.subst, E.eval, eval_subst env σ a]
  | .bin o w a b => by simp only [E.subst, E.eval, eval_subst env σ a, eval_subst env σ b]
  | .sel s a b => by
    simp only [E.subst, E.eval, eval_subst env σ s, eval_subst env σ a, eval_subst env σ b]

/-! ## Value interfaces -/

structure VI (V : Type) where
  comp : E → List V → V
  test : V → Option Bool
  idx  : V → Option Nat
  lit  : Nat → V

/-- The real semantics. A condition token is true iff its bit 0 is set
(`bd_steer .s(cond_data[0])`); a mux index is the token value. -/
def natVI : VI Nat where
  comp e vs := e.eval vs
  test v := some (v % 2 == 1)
  idx v := some v
  lit v := v

/-- Symbolic execution: values are expressions; a condition is decided only by
an assumed fact; an index only if it is a literal. -/
def findFact : List (E × Bool) → E → Option Bool
  | [], _ => none
  | (e, b) :: fs, v => if e = v then some b else findFact fs v

def symVI (facts : List (E × Bool)) : VI E where
  comp e vs := e.subst vs
  test v := findFact facts v
  idx v := match v with | .lit n => some n | _ => none
  lit v := .lit v

/-! ## Rules -/

/-- One firing rule. Channels are `Nat`.
* `comp ins o e`: strict; `o ← e(ins)` (a fused region, a single op, a reshape,
  or a constant triggered by a live control token).
* `fork i os`, `sink i`.
* `branch c d t f`: `cond_br`, data `d` to `t` if `c` is true else `f`.
* `mux s ds o iw`: read select `s` (an `iw`-bit index), forward the front of the
  selected input only.
* `cm i res idx k`: input `k` of a `control_merge` (or the only input of a
  1-input one): forward the control token to `res`, emit `k` on `idx`. -/
inductive Rule
  | comp (ins : List Nat) (o : Nat) (e : E)
  | fork (i : Nat) (os : List Nat)
  | branch (c d t f : Nat)
  | mux (s : Nat) (ds : List Nat) (o : Nat) (iw : Nat)
  | cm (i res idx k : Nat)
  | sink (i : Nat)
  deriving DecidableEq, Repr

def Rule.insL : Rule → List Nat
  | .comp ins _ _ => ins
  | .fork i _ => [i]
  | .branch c d _ _ => [c, d]
  | .mux s ds _ _ => s :: ds
  | .cm i _ _ _ => [i]
  | .sink i => [i]

def Rule.outsL : Rule → List Nat
  | .comp _ o _ => [o]
  | .fork _ os => os
  | .branch _ _ t f => [t, f]
  | .mux _ _ o _ => [o]
  | .cm _ res idx _ => [res, idx]
  | .sink _ => []

section Fire
variable {V : Type}

def popOf (ins : List Nat) : Nat → Nat := fun c => if c ∈ ins then 1 else 0

/-- Strict firing: all listed inputs present, pop one from each. -/
def strictF (ins : List Nat) (g : List V → Option (Nat → List V)) (s : Store Nat V) :
    Option (Fire Nat V) :=
  (heads s ins).bind fun vs => (g vs).map fun out => (popOf ins, out)

def Rule.out (I : VI V) : Rule → List V → Option (Nat → List V)
  | .comp _ o e, vs => some fun c => if c = o then [I.comp e vs] else []
  | .fork _ os, vs => some fun c => if c ∈ os then vs.take 1 else []
  | .branch _ _ t f, vs => match vs with
    | [v, x] => (I.test v).map fun b => fun c => if c = (if b then t else f) then [x] else []
    | _ => none
  | .cm _ res idx k, vs => some fun c =>
      (if c = res then vs.take 1 else []) ++ (if c = idx then [I.lit k] else [])
  | .sink _, _ => some fun _ => []
  | .mux .., _ => none

def muxF (I : VI V) (s : Nat) (ds : List Nat) (o iw : Nat) (st : Store Nat V) :
    Option (Fire Nat V) :=
  match st s with
  | [] => none
  | v :: _ => match I.idx v with
    | none => none
    | some j => match ds[j % 2 ^ iw]? with
      | none => none
      | some d => if d = s then none else match st d with
        | [] => none
        | x :: _ => some (fun y => (if y = s then 1 else 0) + (if y = d then 1 else 0),
                          fun y => if y = o then [x] else [])

def Rule.fire (I : VI V) : Rule → Store Nat V → Option (Fire Nat V)
  | .mux s ds o iw => muxF I s ds o iw
  | r => strictF r.insL (r.out I)

theorem Rule.out_outs (I : VI V) (r : Rule) (vs : List V) (out : Nat → List V)
    (h : r.out I vs = some out) (c : Nat) (hc : c ∉ r.outsL) : out c = [] := by
  cases r with
  | comp ins o e =>
    simp only [Rule.out, Option.some.injEq] at h; subst h
    simp only [Rule.outsL, List.mem_singleton] at hc; simp [hc]
  | fork i os =>
    simp only [Rule.out, Option.some.injEq] at h; subst h
    simp only [Rule.outsL] at hc; simp [hc]
  | branch c' d t f =>
    simp only [Rule.out] at h
    split at h
    · cases ht : I.test _ with
      | none => rw [ht] at h; cases h
      | some b =>
        rw [ht] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
        simp only [Rule.outsL, List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
        cases b <;> simp [hc.1, hc.2]
    · cases h
  | mux => simp [Rule.out] at h
  | cm i res idx k =>
    simp only [Rule.out, Option.some.injEq] at h; subst h
    simp only [Rule.outsL, List.mem_cons, List.not_mem_nil, or_false, not_or] at hc
    simp [hc.1, hc.2]
  | sink i => simp only [Rule.out, Option.some.injEq] at h; subst h; rfl

theorem strictF_some {ins : List Nat} {g : List V → Option (Nat → List V)} {s : Store Nat V}
    {r : Fire Nat V} (h : strictF ins g s = some r) :
    ∃ vs out, heads s ins = some vs ∧ g vs = some out ∧ r = (popOf ins, out) := by
  unfold strictF at h
  cases hh : heads s ins with
  | none => rw [hh] at h; cases h
  | some vs =>
    rw [hh] at h
    cases hg : g vs with
    | none => simp [hg] at h
    | some out => simp [hg] at h; exact ⟨vs, out, rfl, hg, h.symm⟩

theorem muxF_some {I : VI V} {s : Nat} {ds : List Nat} {o iw : Nat} {st : Store Nat V}
    {r : Fire Nat V} (h : muxF I s ds o iw st = some r) :
    ∃ v vs j d x xs, st s = v :: vs ∧ I.idx v = some j ∧ ds[j % 2 ^ iw]? = some d ∧ d ≠ s ∧
      st d = x :: xs ∧
      r = (fun y => (if y = s then 1 else 0) + (if y = d then 1 else 0),
           fun y => if y = o then [x] else []) := by
  unfold muxF at h
  split at h
  · cases h
  · rename_i v vs hs
    split at h
    · cases h
    · rename_i j hj
      split at h
      · cases h
      · rename_i d hd
        split at h
        · cases h
        · rename_i hne
          split at h
          · cases h
          · rename_i x xs hx
            cases h
            exact ⟨v, vs, j, d, x, xs, hs, hj, hd, hne, hx, rfl⟩

/-- The Kahn node of a rule. -/
def Rule.node (I : VI V) (r : Rule) : Node Nat V where
  ins := fun c => c ∈ r.insL
  outs := fun c => c ∈ r.outsL
  fire := r.fire I
  pop_ins s res c h hc := by
    cases r with
    | mux s' ds o iw =>
      obtain ⟨v, vs, j, d, x, xs, -, -, hd, -, -, rfl⟩ := muxF_some h
      have h1 : c ≠ s' := fun e => hc (by simp [Rule.insL, e])
      have h2 : c ≠ d := fun e => hc (by
        simp only [Rule.insL, List.mem_cons]; exact Or.inr (e ▸ List.mem_of_getElem? hd))
      simp [h1, h2]
    | _ =>
      obtain ⟨vs, out, -, -, rfl⟩ := strictF_some h
      simp [popOf, hc]
  push_outs s res c h hc := by
    cases r with
    | mux s' ds o iw =>
      obtain ⟨v, vs, j, d, x, xs, -, -, -, -, -, rfl⟩ := muxF_some h
      simp only [Rule.outsL, List.mem_singleton] at hc; simp [hc]
    | _ =>
      obtain ⟨vs, out, -, hg, rfl⟩ := strictF_some h
      exact Rule.out_outs I _ vs out hg c hc
  pop_le s res c h := by
    cases r with
    | mux s' ds o iw =>
      obtain ⟨v, vs, j, d, x, xs, hs, -, -, hne, hx, rfl⟩ := muxF_some h
      simp only
      by_cases e1 : c = s'
      · subst e1; simp [Ne.symm hne, hs]
      · by_cases e2 : c = d
        · subst e2; simp [e1, hx]
        · simp [e1, e2]
    | _ =>
      obtain ⟨vs, out, hh, -, rfl⟩ := strictF_some h
      simp only [popOf]
      split
      · rename_i hc
        have := heads_nonempty hh c hc
        cases hs : s c with
        | nil => exact absurd hs this
        | cons _ _ => simp
      · exact Nat.zero_le _
  mono s s' res h hx := by
    cases r with
    | mux s0 ds o iw =>
      obtain ⟨v, vs, j, d, x, xs, hs, hj, hd, hne, hxd, rfl⟩ := muxF_some h
      obtain ⟨x1, e1⟩ := hx s0 (by simp [Rule.insL])
      obtain ⟨x2, e2⟩ := hx d (by
        simp only [Rule.insL, List.mem_cons]; exact Or.inr (List.mem_of_getElem? hd))
      show muxF I s0 ds o iw s' = _
      unfold muxF
      rw [e1, hs]
      simp only [List.cons_append, hj, hd, hne, ↓reduceIte, e2, hxd]
    | _ =>
      show strictF _ _ s' = some res
      change strictF _ _ s = some res at h
      unfold strictF at h ⊢
      cases hh : heads s _ with
      | none => rw [hh] at h; cases h
      | some vs => rw [hh] at h; rw [heads_mono hh hx]; exact h

end Fire

/-- The always-disabled node (labels beyond the rule list). -/
def inert {V : Type} : Node Nat V where
  ins := fun _ => False
  outs := fun _ => False
  fire := fun _ => none
  pop_ins := by intros; contradiction
  push_outs := by intros; contradiction
  pop_le := by intros; contradiction
  mono := by intros; contradiction

def graphV {V : Type} (I : VI V) (rs : List Rule) (l : Nat) : Node Nat V :=
  match rs[l]? with
  | some r => r.node I
  | none => inert

/-- The imported graph, with its real (Nat) semantics. -/
abbrev graph (rs : List Rule) : Nat → Node Nat Nat := graphV natVI rs

/-! ## Well-formedness from Boolean checks -/

theorem flatten_disj {L : List (List Nat)} (h : L.flatten.Nodup) :
    ∀ {i j : Nat} {a b : List Nat} {c : Nat}, L[i]? = some a → L[j]? = some b → i ≠ j → c ∈ a → c ∈ b → False := by
  induction L with
  | nil => intro i j a b c ha; simp at ha
  | cons x L ih =>
    intro i j a b c ha hb hij hca hcb
    simp only [List.flatten_cons] at h
    have hn := List.nodup_append.mp h
    cases i with
    | zero =>
      cases j with
      | zero => exact hij rfl
      | succ j =>
        simp at ha hb; subst ha
        exact hn.2.2 c hca c (List.mem_flatten.mpr ⟨b, List.mem_of_getElem? hb, hcb⟩) rfl
    | succ i =>
      cases j with
      | zero =>
        simp at ha hb; subst hb
        exact hn.2.2 c hcb c (List.mem_flatten.mpr ⟨a, List.mem_of_getElem? ha, hca⟩) rfl
      | succ j =>
        simp at ha hb
        exact ih hn.2.1 ha hb (by omega) hca hcb

def Rule.isCmP (P : List Nat) : Rule → Bool
  | .cm i _ _ _ => decide (i ∈ P)
  | _ => false

def Rule.outsO (P : List Nat) (r : Rule) : List Nat := if r.isCmP P then [] else r.outsL

/-- Unique consumer per channel. -/
def checkIns (rs : List Rule) : Bool := decide (rs.map Rule.insL).flatten.Nodup

/-- Unique producer per channel, except outputs shared by `control_merge`
inputs whose input channel lies on the control spine `P`. -/
def checkOuts (P : List Nat) (rs : List Rule) : Bool :=
  decide ((rs.map (Rule.outsO P)).flatten.Nodup) &&
  rs.all fun r => !r.isCmP P || r.outsL.all fun c => !((rs.map (Rule.outsO P)).flatten.contains c)

/-- Tokens on the control spine. -/
def cnt (P : List Nat) (s : Store Nat Nat) : Nat := (P.map fun c => (s c).length).sum

/-- H_ONE_INVOCATION, for the whole function: at most one token on the spine. -/
def Inv (P : List Nat) (s : Store Nat Nat) : Prop := cnt P s ≤ 1

theorem le_sum_of_mem {f : Nat → Nat} : ∀ {P : List Nat} {c : Nat}, c ∈ P → f c ≤ (P.map f).sum
  | [], _, h => by simp at h
  | d :: P, c, h => by
    simp only [List.map_cons, List.sum_cons]
    rcases List.mem_cons.mp h with rfl | h
    · omega
    · have := le_sum_of_mem (f := f) h; omega

theorem two_le_sum {f : Nat → Nat} : ∀ {P : List Nat}, P.Nodup → ∀ {a b : Nat}, a ∈ P → b ∈ P →
    a ≠ b → 1 ≤ f a → 1 ≤ f b → 2 ≤ (P.map f).sum
  | [], _, _, _, h, _, _, _, _ => by simp at h
  | d :: P, hP, a, b, ha, hb, hab, fa, fb => by
    simp only [List.map_cons, List.sum_cons]
    have hP' := List.nodup_cons.mp hP
    rcases List.mem_cons.mp ha with h1 | ha' <;> rcases List.mem_cons.mp hb with h2 | hb'
    · exact absurd (h1.trans h2.symm) hab
    · subst h1; have := le_sum_of_mem (f := f) hb'; omega
    · subst h2; have := le_sum_of_mem (f := f) ha'; omega
    · have := two_le_sum hP'.2 ha' hb' hab fa fb; omega

theorem graph_ins {rs : List Rule} {l c} (h : (graph rs l).ins c) :
    ∃ r, rs[l]? = some r ∧ c ∈ r.insL := by
  unfold graph graphV at h
  split at h
  · rename_i r hr; exact ⟨r, hr, h⟩
  · exact h.elim

theorem graph_outs {rs : List Rule} {l c} (h : (graph rs l).outs c) :
    ∃ r, rs[l]? = some r ∧ c ∈ r.outsL := by
  unfold graph graphV at h
  split at h
  · rename_i r hr; exact ⟨r, hr, h⟩
  · exact h.elim

theorem graph_fire {rs : List Rule} {l r s} (hr : rs[l]? = some r) :
    (graph rs l).fire s = r.fire natVI s := by
  unfold graph graphV; rw [hr]; rfl

theorem mem_outsO_flatten {P : List Nat} {rs : List Rule} {l : Nat} {r : Rule} {c : Nat} (hr : rs[l]? = some r)
    (hc : c ∈ r.outsL) (hn : r.isCmP P = false) : c ∈ (rs.map (Rule.outsO P)).flatten :=
  List.mem_flatten.mpr ⟨r.outsO P, List.mem_map.mpr ⟨r, List.mem_of_getElem? hr, rfl⟩,
    by simp [Rule.outsO, hn, hc]⟩

theorem wfOn_of_check (P : List Nat) (rs : List Rule) (hP : P.Nodup)
    (hI : checkIns rs = true) (hO : checkOuts P rs = true) : WFOn (graph rs) (Inv P) := by
  have hI' := of_decide_eq_true hI
  simp only [checkOuts, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true] at hO
  obtain ⟨hO1, hO2⟩ := hO
  have insD : ∀ l₁ l₂ c, l₁ ≠ l₂ → (graph rs l₁).ins c → (graph rs l₂).ins c → False := by
    intro l₁ l₂ c hne h1 h2
    obtain ⟨r1, hr1, hc1⟩ := graph_ins h1
    obtain ⟨r2, hr2, hc2⟩ := graph_ins h2
    exact flatten_disj (a := r1.insL) (b := r2.insL) hI' (by simp [hr1]) (by simp [hr2]) hne hc1 hc2
  refine ⟨insD, ?_⟩
  intro s l₁ l₂ c hInv hne e1 e2 h1 h2
  obtain ⟨r1, hr1, hc1⟩ := graph_outs h1
  obtain ⟨r2, hr2, hc2⟩ := graph_outs h2
  have cross : ∀ ra rb : Rule, ra.isCmP P = true → rb.isCmP P = false → ra ∈ rs → c ∈ ra.outsL →
      c ∈ (rs.map (Rule.outsO P)).flatten → False := by
    intro ra rb ha _ hmem hc hcO
    have := hO2 ra hmem
    simp only [ha, Bool.not_true, Bool.false_or, List.all_eq_true] at this
    have := this c hc
    simp [hcO] at this
  cases h1c : r1.isCmP P <;> cases h2c : r2.isCmP P
  · exact flatten_disj (a := r1.outsO P) (b := r2.outsO P) (c := c) hO1 (by simp [hr1]) (by simp [hr2]) hne
      (by simp [Rule.outsO, h1c, hc1]) (by simp [Rule.outsO, h2c, hc2])
  · exact cross r2 r1 h2c h1c (List.mem_of_getElem? hr2) hc2 (mem_outsO_flatten hr1 hc1 h1c)
  · exact cross r1 r2 h1c h2c (List.mem_of_getElem? hr1) hc1 (mem_outsO_flatten hr2 hc2 h2c)
  · -- two control_merge inputs on the spine: both enabled contradicts `Inv`
    cases r1 <;> simp [Rule.isCmP] at h1c
    cases r2 <;> simp [Rule.isCmP] at h2c
    rename_i i1 _ _ _ i2 _ _ _
    rw [graph_fire hr1] at e1; rw [graph_fire hr2] at e2
    have n1 : s i1 ≠ [] := by
      intro he; apply e1; simp [Rule.fire, strictF, Rule.insL, heads, he]
    have n2 : s i2 ≠ [] := by
      intro he; apply e2; simp [Rule.fire, strictF, Rule.insL, heads, he]
    have hii : i1 ≠ i2 := by
      intro e; subst e
      exact insD l₁ l₂ i1 hne (by simp [graph, graphV, hr1, Rule.node, Rule.insL])
        (by simp [graph, graphV, hr2, Rule.node, Rule.insL])
    have := two_le_sum (f := fun c => (s c).length) hP h1c h2c hii
      (by cases h : s i1 <;> simp_all) (by cases h : s i2 <;> simp_all)
    unfold Inv cnt at hInv
    omega

/-! ## The spine invariant is closed -/

theorem cnt_apply (P : List Nat) (s : Store Nat Nat) (r : Fire Nat Nat)
    (hle : ∀ c, r.1 c ≤ (s c).length) :
    cnt P (applyF s r) + (P.map r.1).sum = cnt P s + (P.map fun c => (r.2 c).length).sum := by
  unfold cnt
  induction P with
  | nil => rfl
  | cons c P ih =>
    simp only [List.map_cons, List.sum_cons, applyF, List.length_append, List.length_drop] at ih ⊢
    have := hle c
    omega

/-- Per-rule condition for `Inv` to be closed: a rule that can put a token on
the spine also takes one off it. -/
def Rule.okP (P : List Nat) : Rule → Bool
  | .comp ins o _ => !(decide (o ∈ P)) || ins.any fun c => decide (c ∈ P)
  | .fork i os => decide ((P.filter fun c => decide (c ∈ os)).length ≤ (if i ∈ P then 1 else 0))
  | .branch c d t f => !(decide (t ∈ P) || decide (f ∈ P)) || decide (c ∈ P) || decide (d ∈ P)
  | .mux _ _ o _ => !(decide (o ∈ P))
  | .cm i res idx _ => !(decide (idx ∈ P)) && (!(decide (res ∈ P)) || decide (i ∈ P)) &&
      decide (res ≠ idx)
  | .sink _ => true

theorem sum_ite_eq : ∀ {P : List Nat}, P.Nodup → ∀ (o : Nat) (f : Nat → Nat),
    (P.map fun c => if c = o then f c else 0).sum = if o ∈ P then f o else 0
  | [], _, _, _ => by simp
  | d :: P, hP, o, f => by
    have hP' := List.nodup_cons.mp hP
    simp only [List.map_cons, List.sum_cons, sum_ite_eq hP'.2 o f, List.mem_cons]
    by_cases h : d = o
    · subst h; simp [hP'.1]
    · by_cases h2 : o ∈ P <;> simp [h, h2, Ne.symm h]

theorem sum_zero : ∀ {P : List Nat} {f : Nat → Nat}, (∀ c ∈ P, f c = 0) → (P.map f).sum = 0
  | [], _, _ => rfl
  | d :: P, f, h => by
    simp only [List.map_cons, List.sum_cons, h d (by simp),
      sum_zero (fun c hc => h c (List.mem_cons_of_mem _ hc))]

theorem sum_ind_filter : ∀ (P : List Nat) (os : List Nat),
    (P.map fun c => if c ∈ os then 1 else 0).sum = (P.filter fun c => decide (c ∈ os)).length
  | [], _ => rfl
  | d :: P, os => by
    simp only [List.map_cons, List.sum_cons, sum_ind_filter P os, List.filter_cons]
    by_cases h : d ∈ os <;> simp [h]; omega

theorem popOf_sum {P : List Nat} {ins : List Nat} {c : Nat} (hc : c ∈ ins) (hcP : c ∈ P) :
    1 ≤ (P.map (popOf ins)).sum := by
  have := le_sum_of_mem (f := popOf ins) hcP
  simp [popOf, hc] at this; omega

theorem sum_le : ∀ {P : List Nat} {f g : Nat → Nat}, (∀ c, f c ≤ g c) →
    (P.map f).sum ≤ (P.map g).sum
  | [], _, _, _ => Nat.le_refl _
  | d :: P, f, g, h => by
    simp only [List.map_cons, List.sum_cons]
    have := sum_le (P := P) h; have := h d; omega

theorem sum_le_mem : ∀ {P : List Nat} {f g : Nat → Nat}, (∀ c ∈ P, f c ≤ g c) →
    (P.map f).sum ≤ (P.map g).sum
  | [], _, _, _ => Nat.le_refl _
  | d :: P, f, g, h => by
    simp only [List.map_cons, List.sum_cons]
    have := sum_le_mem (P := P) (fun c hc => h c (List.mem_cons_of_mem _ hc))
    have := h d (by simp); omega

theorem sum_one (P : List Nat) (hP : P.Nodup) (o : Nat) :
    (P.map fun c => if c = o then 1 else 0).sum = if o ∈ P then 1 else 0 :=
  sum_ite_eq hP o (fun _ => 1)

theorem take1_len {α} (vs : List α) : (vs.take 1).length ≤ 1 := by cases vs <;> simp

theorem closed_of_check (P : List Nat) (rs : List Rule) (hP : P.Nodup)
    (h : rs.all (Rule.okP P) = true) : Closed (step (graph rs)) (Inv P) := by
  intro s l s' hInv hs
  obtain ⟨res, hres, rfl⟩ := step_some hs
  have hle := (graph rs l).pop_le s res
  unfold Inv at hInv ⊢
  have key := cnt_apply P s res (fun c => hle c hres)
  suffices hpp : (P.map fun c => (res.2 c).length).sum ≤ (P.map res.1).sum by omega
  unfold graph graphV at hres
  split at hres
  · rename_i r hr
    have hok : r.okP P = true := List.all_eq_true.mp h r (List.mem_of_getElem? hr)
    change Rule.fire natVI r s = some res at hres
    cases r with
    | mux s0 ds o iw =>
      change muxF natVI s0 ds o iw s = some res at hres
      obtain ⟨v, vs, j, d, x, xs, -, -, -, -, -, rfl⟩ := muxF_some hres
      simp only [Rule.okP, Bool.not_eq_true', decide_eq_false_iff_not] at hok
      have h1 := sum_one P hP o
      simp only [hok, ↓reduceIte] at h1
      have : (P.map fun c => ((fun y => if y = o then [x] else []) c).length).sum ≤
          (P.map fun c => if c = o then 1 else 0).sum :=
        sum_le (fun c => by simp only; split <;> simp)
      simp only at this ⊢; omega
    | comp ins o e =>
      change strictF _ _ s = some res at hres
      obtain ⟨vs, out, hh, hg, rfl⟩ := strictF_some hres
      simp only [Rule.out, Option.some.injEq] at hg; subst hg
      dsimp only [Rule.insL]
      have h1 := sum_one P hP o
      have : (P.map fun c => ((fun c => if c = o then [natVI.comp e vs] else []) c).length).sum ≤
          (P.map fun c => if c = o then 1 else 0).sum :=
        sum_le (fun c => by simp only; split <;> simp)
      simp only at this ⊢
      by_cases ho : o ∈ P
      · simp only [Rule.okP, ho, decide_true, Bool.not_true, Bool.false_or, List.any_eq_true,
          decide_eq_true_eq] at hok
        obtain ⟨c, hc, hcP⟩ := hok
        have := popOf_sum hc hcP; simp [ho] at h1; omega
      · simp [ho] at h1; omega
    | fork i os =>
      change strictF _ _ s = some res at hres
      obtain ⟨vs, out, hh, hg, rfl⟩ := strictF_some hres
      simp only [Rule.out, Option.some.injEq] at hg; subst hg
      show (P.map fun c => (if c ∈ os then vs.take 1 else []).length).sum ≤ (P.map (popOf [i])).sum
      simp only [Rule.okP, decide_eq_true_eq] at hok
      have a : (P.map fun c => (if c ∈ os then vs.take 1 else []).length).sum ≤
          (P.map fun c => if c ∈ os then 1 else 0).sum :=
        sum_le (fun c => by split; exact take1_len vs; simp)
      rw [sum_ind_filter] at a
      by_cases hi : i ∈ P
      · have := popOf_sum (ins := [i]) (by simp) hi; rw [if_pos hi] at hok; omega
      · rw [if_neg hi] at hok; omega
    | branch c d t f =>
      change strictF _ _ s = some res at hres
      obtain ⟨vs, out, hh, hg, rfl⟩ := strictF_some hres
      simp only [Rule.out] at hg
      split at hg
      · rename_i v x
        simp only [natVI, Option.map_some, Option.some.injEq] at hg; subst hg
        have htf : ∀ tgt, (tgt = t ∨ tgt = f) →
            (P.map fun y => (if y = tgt then [x] else []).length).sum ≤ (P.map (popOf [c, d])).sum := by
          intro tgt htg
          have h1 := sum_one P hP tgt
          have a : (P.map fun y => (if y = tgt then [x] else []).length).sum ≤
              (P.map fun y => if y = tgt then 1 else 0).sum :=
            sum_le (fun y => by split <;> simp)
          by_cases hp : tgt ∈ P
          · have htf : t ∈ P ∨ f ∈ P := by rcases htg with rfl | rfl <;> simp [hp]
            simp only [Rule.okP, Bool.or_eq_true, Bool.not_eq_true', decide_eq_true_eq] at hok
            have hcd : c ∈ P ∨ d ∈ P := by
              rcases hok with (h0 | h0) | h0
              · simp only [Bool.or_eq_false_iff, decide_eq_false_iff_not] at h0
                exact False.elim (htf.elim (fun h => h0.1 h) (fun h => h0.2 h))
              · exact Or.inl h0
              · exact Or.inr h0
            rcases hcd with hc | hd
            · have := popOf_sum (ins := [c, d]) (by simp) hc; rw [if_pos hp] at h1; omega
            · have := popOf_sum (ins := [c, d]) (by simp) hd; rw [if_pos hp] at h1; omega
          · rw [if_neg hp] at h1; omega
        exact htf _ (by split <;> simp)
      · cases hg
    | cm i r0 idx k =>
      change strictF _ _ s = some res at hres
      obtain ⟨vs, out, hh, hg, rfl⟩ := strictF_some hres
      simp only [Rule.out, Option.some.injEq] at hg; subst hg
      show (P.map fun c => ((if c = r0 then vs.take 1 else []) ++
            (if c = idx then [natVI.lit k] else [])).length).sum ≤ (P.map (popOf [i])).sum
      simp only [Rule.okP, Bool.and_eq_true, Bool.or_eq_true, Bool.not_eq_true',
        decide_eq_false_iff_not, decide_eq_true_eq] at hok
      obtain ⟨⟨hidx, hres'⟩, hne⟩ := hok
      have h1 := sum_one P hP r0
      have a : (P.map fun c => ((if c = r0 then vs.take 1 else []) ++
            (if c = idx then [natVI.lit k] else [])).length).sum ≤
          (P.map fun c => if c = r0 then 1 else 0).sum := by
        apply sum_le_mem; intro c hc
        have e2 : c ≠ idx := fun e => hidx (e ▸ hc)
        simp only [e2, ↓reduceIte, List.append_nil]; split; exact take1_len vs; simp
      by_cases hp : r0 ∈ P
      · have := popOf_sum (ins := [i]) (by simp) (hres'.resolve_left (fun h => h hp)); rw [if_pos hp] at h1; omega
      · rw [if_neg hp] at h1; omega
    | sink i =>
      change strictF _ _ s = some res at hres
      obtain ⟨vs, out, hh, hg, rfl⟩ := strictF_some hres
      simp only [Rule.out, Option.some.injEq] at hg; subst hg
      show (P.map fun _ => ([] : List Nat).length).sum ≤ _
      exact Nat.le_trans (Nat.le_of_eq (sum_zero (fun _ _ => rfl))) (Nat.zero_le _)
  · cases hres

/-! ## Determinacy of an imported graph -/

/-- Strong determinacy for an imported graph that passes the checks: from any
state with at most one token on the control spine, every complete run ends in
the same state after the same number of firings, and no run is longer. -/
theorem determinate (P : List Nat) (rs : List Rule) (hP : P.Nodup)
    (hI : checkIns rs = true) (hO : checkOuts P rs = true) (hC : rs.all (Rule.okP P) = true)
    {s t t' : Store Nat Nat} {n m : Nat} (hs : Inv P s)
    (h1 : Run (step (graph rs)) s n t) (ht : Terminal (step (graph rs)) t)
    (h2 : Run (step (graph rs)) s m t') (ht' : Terminal (step (graph rs)) t') :
    t' = t ∧ m = n :=
  terminal_unique (closed_of_check P rs hP hC) (wfOn_diamond (wfOn_of_check P rs hP hI hO)) hs
    h1 ht h2 ht'

theorem no_longer (P : List Nat) (rs : List Rule) (hP : P.Nodup)
    (hI : checkIns rs = true) (hO : checkOuts P rs = true) (hC : rs.all (Rule.okP P) = true)
    {s t u : Store Nat Nat} {n m : Nat} (hs : Inv P s)
    (h1 : Run (step (graph rs)) s n t) (ht : Terminal (step (graph rs)) t)
    (h2 : Run (step (graph rs)) s m u) : m ≤ n :=
  no_divergence (closed_of_check P rs hP hC) (wfOn_diamond (wfOn_of_check P rs hP hI hO)) hs
    h1 ht h2

/-! ## List-form stores, and symbolic execution -/

section ListForm
variable {V : Type}

def ofL (l : List (List V)) : Store Nat V := fun c => l.getD c []

/-- Structural (not `List.mapIdx`, whose `Array` accumulator is slow to reduce
in the kernel). -/
def applyGo (r : Fire Nat V) : Nat → List (List V) → List (List V)
  | _, [] => []
  | c, x :: xs => (x.drop (r.1 c) ++ r.2 c) :: applyGo r (c + 1) xs

def applyL (l : List (List V)) (r : Fire Nat V) : List (List V) := applyGo r 0 l

theorem applyGo_eq (r : Fire Nat V) : ∀ (c : Nat) (l : List (List V)),
    applyGo r c l = l.mapIdx fun i x => x.drop (r.1 (c + i)) ++ r.2 (c + i)
  | _, [] => rfl
  | c, x :: xs => by
    simp only [applyGo, List.mapIdx_cons, Nat.add_zero, applyGo_eq r (c + 1) xs]
    congr 1; congr 1; funext i y; rw [Nat.add_assoc, Nat.add_comm 1 i]

theorem applyL_eq (l : List (List V)) (r : Fire Nat V) :
    applyL l r = l.mapIdx fun c x => x.drop (r.1 c) ++ r.2 c := by
  simp [applyL, applyGo_eq]

def stepL (I : VI V) (rs : List Rule) (l : List (List V)) (i : Nat) : Option (List (List V)) :=
  match rs[i]? with
  | some r => (r.fire I (ofL l)).map (applyL l)
  | none => none

def execL (I : VI V) (rs : List Rule) : List (List V) → List Nat → Option (List (List V))
  | l, [] => some l
  | l, i :: is => (stepL I rs l i).bind fun l' => execL I rs l' is

/-- Every output channel is below `N` (the store length). -/
def bounded (N : Nat) (rs : List Rule) : Bool := rs.all fun r => r.outsL.all (· < N)

theorem ofL_applyL {I : VI V} {rs : List Rule} {N : Nat} (hb : bounded N rs = true)
    {l : List (List V)} (hl : l.length = N) {i : Nat} {r : Rule} (hr : rs[i]? = some r)
    {res : Fire Nat V} (hf : r.fire I (ofL l) = some res) :
    ofL (applyL l res) = applyF (ofL l) res := by
  funext c
  simp only [ofL, applyL_eq, applyF, List.getD_eq_getElem?_getD, List.getElem?_mapIdx]
  by_cases hc : c < l.length
  · rw [List.getElem?_eq_getElem hc]; rfl
  · have h1 : l[c]? = none := List.getElem?_eq_none (by omega)
    rw [h1]
    have hout : c ∉ r.outsL := by
      intro hm
      have := List.all_eq_true.mp (List.all_eq_true.mp hb r (List.mem_of_getElem? hr)) c hm
      simp at this; omega
    have := (r.node I).push_outs (ofL l) res c hf hout
    simp [this]

theorem length_applyL (l : List (List V)) (r : Fire Nat V) : (applyL l r).length = l.length := by
  simp [applyL_eq]

end ListForm

theorem stepL_step {rs : List Rule} {N : Nat} (hb : bounded N rs = true)
    {l l' : List (List Nat)} (hl : l.length = N) {i : Nat} (h : stepL natVI rs l i = some l') :
    step (graph rs) (ofL l) i = some (ofL l') ∧ l'.length = N := by
  unfold stepL at h
  split at h
  · rename_i r hr
    cases hf : r.fire natVI (ofL l) with
    | none => rw [hf] at h; cases h
    | some res =>
      rw [hf] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
      refine ⟨?_, by rw [length_applyL, hl]⟩
      unfold step
      rw [graph_fire hr, hf, Option.map_some, ofL_applyL hb hl hr hf]
  · cases h

theorem execL_run {rs : List Rule} {N : Nat} (hb : bounded N rs = true) :
    ∀ (is : List Nat) {l l' : List (List Nat)}, l.length = N → execL natVI rs l is = some l' →
      Run (step (graph rs)) (ofL l) is.length (ofL l')
  | [], l, l', _, h => by simp only [execL, Option.some.injEq] at h; subst h; exact Run.refl _
  | i :: is, l, l', hl, h => by
    simp only [execL] at h
    cases hs : stepL natVI rs l i with
    | none => rw [hs] at h; cases h
    | some m =>
      rw [hs] at h
      obtain ⟨h1, h2⟩ := stepL_step hb hl hs
      exact Run.cons i h1 (execL_run hb is h2 h)

/-! ### Symbolic to concrete -/

/-- The branch facts a symbolic run assumed hold for `env`. -/
def FactsOK (env : List Nat) (F : List (E × Bool)) : Prop :=
  ∀ p ∈ F, (p.1.eval env % 2 == 1) = p.2

theorem findFact_ok {env : List Nat} : ∀ {F : List (E × Bool)} {v : E} {b : Bool},
    FactsOK env F → findFact F v = some b → (v.eval env % 2 == 1) = b
  | [], _, _, _, h => by simp [findFact] at h
  | (e, b') :: fs, v, b, hF, h => by
    simp only [findFact] at h
    split at h
    · rename_i he; subst he; cases h; exact hF (_, _) (List.mem_cons.mpr (Or.inl rfl))
    · exact findFact_ok (fun p hp => hF p (List.mem_cons_of_mem _ hp)) h

def lmap (env : List Nat) (l : List (List E)) : List (List Nat) := l.map (List.map (E.eval env))

theorem ofL_lmap (env : List Nat) (l : List (List E)) (c : Nat) :
    ofL (lmap env l) c = (ofL l c).map (E.eval env) := by
  simp only [ofL, lmap, List.getD_eq_getElem?_getD, List.getElem?_map]
  cases l[c]? <;> rfl

theorem heads_map {V W : Type} (h : V → W) (s : Store Nat V) :
    ∀ cs : List Nat, heads (fun c => (s c).map h) cs = (heads s cs).map (List.map h)
  | [] => rfl
  | c :: cs => by
    simp only [heads]
    cases hs : s c with
    | nil => simp
    | cons v vs =>
      simp only [List.map_cons, heads_map h s cs]
      cases heads s cs <;> rfl

theorem out_hom {env : List Nat} {F : List (E × Bool)} (hF : FactsOK env F) (r : Rule)
    (vs : List E) (out : Nat → List E) (h : r.out (symVI F) vs = some out) :
    r.out natVI (vs.map (E.eval env)) = some fun c => (out c).map (E.eval env) := by
  cases r with
  | comp ins o e =>
    simp only [Rule.out, Option.some.injEq] at h ⊢; subst h
    funext c; by_cases hc : c = o <;> simp [hc, symVI, natVI, eval_subst]
  | fork i os =>
    simp only [Rule.out, Option.some.injEq] at h ⊢; subst h
    funext c; by_cases hc : c ∈ os <;> simp [hc, List.map_take]
  | branch c d t f =>
    simp only [Rule.out] at h
    match vs, h with
    | [v, x], h =>
      cases hb : findFact F v with
      | none => simp [symVI, hb] at h
      | some b =>
        simp only [symVI, hb, Option.map_some, Option.some.injEq] at h; subst h
        have := findFact_ok hF hb
        simp only [Rule.out, List.map_cons, List.map_nil, natVI, Option.map_some, this]
        congr 1; funext y; by_cases hy : y = (if b then t else f) <;> simp [hy]
  | mux => simp [Rule.out] at h
  | cm i res idx k =>
    simp only [Rule.out, Option.some.injEq] at h ⊢; subst h
    funext c; simp only [List.map_append, symVI, natVI]
    rw [apply_ite (List.map (E.eval env)), apply_ite (List.map (E.eval env))]
    simp only [List.map_take, List.map_cons, List.map_nil, E.eval]
  | sink i =>
    simp only [Rule.out, Option.some.injEq] at h ⊢; subst h; rfl

theorem fire_hom {env : List Nat} {F : List (E × Bool)} (hF : FactsOK env F) (r : Rule)
    (l : List (List E)) (res : Fire Nat E) (h : r.fire (symVI F) (ofL l) = some res) :
    r.fire natVI (ofL (lmap env l)) = some (res.1, fun c => (res.2 c).map (E.eval env)) := by
  have hs : ofL (lmap env l) = fun c => (ofL l c).map (E.eval env) := funext (ofL_lmap env l)
  rw [hs]
  cases r with
  | mux s0 ds o iw =>
    change muxF _ s0 ds o iw (ofL l) = some res at h
    obtain ⟨v, vs, j, d, x, xs, hs0, hj, hd, hne, hx, rfl⟩ := muxF_some h
    have hv : v = .lit j := by
      cases v <;> simp [symVI] at hj; subst hj; rfl
    subst hv
    simp only [Rule.fire]
    unfold muxF
    simp only [hs0, List.map_cons, natVI, E.eval, hd, hne, ↓reduceIte, hx]
    congr 2; funext y; split <;> simp
  | _ =>
    change strictF _ _ _ = some res at h
    obtain ⟨vs, out, hh, hg, rfl⟩ := strictF_some h
    show strictF _ _ _ = _
    unfold strictF
    rw [heads_map, hh, Option.map_some, Option.bind_some, out_hom hF _ vs out hg, Option.map_some]

theorem stepL_hom {env : List Nat} {F : List (E × Bool)} (hF : FactsOK env F) (rs : List Rule)
    {l l' : List (List E)} {i : Nat} (h : stepL (symVI F) rs l i = some l') :
    stepL natVI rs (lmap env l) i = some (lmap env l') := by
  unfold stepL at h ⊢
  split at h
  · rename_i r hr
    cases hf : r.fire (symVI F) (ofL l) with
    | none => rw [hf] at h; cases h
    | some res =>
      rw [hf] at h; simp only [Option.map_some, Option.some.injEq] at h; subst h
      rw [fire_hom hF r l res hf, Option.map_some]
      congr 1
      apply List.ext_getElem?; intro c
      simp only [lmap, applyL_eq, List.getElem?_mapIdx, List.getElem?_map]
      cases l[c]? <;> simp [List.map_drop]
  · cases h

theorem execL_hom {env : List Nat} {F : List (E × Bool)} (hF : FactsOK env F) (rs : List Rule) :
    ∀ (is : List Nat) {l l' : List (List E)}, execL (symVI F) rs l is = some l' →
      execL natVI rs (lmap env l) is = some (lmap env l')
  | [], l, l', h => by simp only [execL, Option.some.injEq] at h ⊢; rw [h]
  | i :: is, l, l', h => by
    simp only [execL] at h ⊢
    cases hs : stepL (symVI F) rs l i with
    | none => rw [hs] at h; cases h
    | some m => rw [hs] at h; rw [stepL_hom hF rs hs]; exact execL_hom hF rs is h

/-- A checked symbolic segment is a real run, for every environment satisfying
its facts. This is how every schedule lemma about the imported graph is proved:
the symbolic run is a closed computation decided by the kernel. -/
theorem sym_run {rs : List Rule} {N : Nat} (hb : bounded N rs = true) {F : List (E × Bool)}
    {l l' : List (List E)} (hl : l.length = N) (is : List Nat)
    (h : execL (symVI F) rs l is = some l') (env : List Nat) (hF : FactsOK env F) :
    Run (step (graph rs)) (ofL (lmap env l)) is.length (ofL (lmap env l')) :=
  execL_run hb is (by simp [lmap, hl]) (execL_hom hF rs is h)

/-! ### Quiescence by emptiness -/

/-- A rule is dead in a store if an input it needs is empty (for a mux: its select). -/
def Rule.dead {V : Type} (st : Store Nat V) : Rule → Bool
  | .mux s _ _ _ => (st s).isEmpty
  | .comp ins _ _ => ins.any fun c => (st c).isEmpty
  | .fork i _ => (st i).isEmpty
  | .branch c d _ _ => (st c).isEmpty || (st d).isEmpty
  | .cm i _ _ _ => (st i).isEmpty
  | .sink i => (st i).isEmpty

theorem heads_none {V : Type} {s : Store Nat V} :
    ∀ {cs : List Nat} {c : Nat}, c ∈ cs → s c = [] → heads s cs = none
  | [], _, h, _ => by simp at h
  | d :: cs, c, h, hc => by
    simp only [heads]
    rcases List.mem_cons.mp h with rfl | h
    · rw [hc]
    · split
      · rfl
      · rw [heads_none h hc]; rfl

theorem fire_none_of_dead {V : Type} (I : VI V) (r : Rule) (st : Store Nat V)
    (h : r.dead st = true) : r.fire I st = none := by
  cases r with
  | mux s0 ds o iw =>
    simp only [Rule.dead, List.isEmpty_iff] at h
    show muxF I s0 ds o iw st = none
    unfold muxF; rw [h]
  | comp ins o e =>
    simp only [Rule.dead, List.any_eq_true, List.isEmpty_iff] at h
    obtain ⟨c, hc, he⟩ := h
    show strictF _ _ st = none
    simp [strictF, Rule.insL, heads_none hc he]
  | fork i os =>
    simp only [Rule.dead, List.isEmpty_iff] at h
    show strictF _ _ st = none
    simp [strictF, Rule.insL, heads_none (List.mem_singleton_self i) h]
  | branch c d t f =>
    simp only [Rule.dead, Bool.or_eq_true, List.isEmpty_iff] at h
    show strictF _ _ st = none
    rcases h with h | h
    · simp [strictF, Rule.insL, heads_none (by simp : c ∈ [c, d]) h]
    · simp [strictF, Rule.insL, heads_none (by simp : d ∈ [c, d]) h]
  | cm i r0 idx k =>
    simp only [Rule.dead, List.isEmpty_iff] at h
    show strictF _ _ st = none
    simp [strictF, Rule.insL, heads_none (List.mem_singleton_self i) h]
  | sink i =>
    simp only [Rule.dead, List.isEmpty_iff] at h
    show strictF _ _ st = none
    simp [strictF, Rule.insL, heads_none (List.mem_singleton_self i) h]

theorem terminal_of_dead (rs : List Rule) (st : Store Nat Nat)
    (h : rs.all (Rule.dead st) = true) : Terminal (step (graph rs)) st := by
  intro l
  unfold step
  cases hr : rs[l]? with
  | none => simp [graph, graphV, hr, inert]
  | some r =>
    rw [graph_fire hr, fire_none_of_dead natVI r st (List.all_eq_true.mp h r (List.mem_of_getElem? hr))]
    rfl

theorem dead_lmap (env : List Nat) (l : List (List E)) (r : Rule) :
    r.dead (ofL (lmap env l)) = r.dead (ofL l) := by
  have e : ∀ c, (ofL (lmap env l) c).isEmpty = (ofL l c).isEmpty := by
    intro c; rw [ofL_lmap]; cases ofL l c <;> rfl
  cases r <;> simp only [Rule.dead, e]

/-! ### Step-by-step certificates

Checking a whole symbolic run in one kernel reduction re-evaluates the lazily
built intermediate stores and grows superlinearly (an 11-firing run exceeded
4 GB). A certificate therefore lists every intermediate store; each step is
checked against a literal, which is linear in the run length. -/

/-- A store given by its non-empty channels. -/
def sp {V : Type} (n : Nat) (entries : List (Nat × List V)) : List (List V) :=
  (List.range n).map fun c => (entries.lookup c).getD []

def chainOK {V : Type} [DecidableEq V] (I : VI V) (rs : List Rule) :
    List (List V) → List (List (List V)) → List Nat → List (List V) → Bool
  | l, [], [], l' => decide (l = l')
  | l, m :: ms, i :: is, l' => decide (stepL I rs l i = some m) && chainOK I rs m ms is l'
  | _, _, _, _ => false

theorem execL_of_chainOK {V : Type} [DecidableEq V] {I : VI V} {rs : List Rule} :
    ∀ {l : List (List V)} {ms : List (List (List V))} {is : List Nat} {l' : List (List V)},
      chainOK I rs l ms is l' = true → execL I rs l is = some l'
  | l, [], [], l', h => by simp only [chainOK, decide_eq_true_eq] at h; subst h; rfl
  | l, m :: ms, i :: is, l', h => by
    simp only [chainOK, Bool.and_eq_true, decide_eq_true_eq] at h
    simp only [execL, h.1, Option.bind_some]
    exact execL_of_chainOK h.2
  | _, [], _ :: _, _, h => by simp [chainOK] at h
  | _, _ :: _, [], _, h => by simp [chainOK] at h

theorem lmap_subst (env : List Nat) (σ : List E) (l : List (List E)) :
    lmap env (l.map (List.map (E.subst σ))) = lmap (σ.map (E.eval env)) l := by
  simp only [lmap, List.map_map]
  congr 1; funext x; simp only [Function.comp_def, List.map_map]
  congr 1; funext e; exact eval_subst env σ e

end Formal.Net.GcdHw
