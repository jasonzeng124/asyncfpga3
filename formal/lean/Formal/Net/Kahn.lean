import Formal.Net.KahnLTS

/-!
# Token-level dataflow semantics and its determinacy (probe C-8b)

Core Lean only. The model is the untimed token game that Dynamatic's handshake
dialect denotes (and that bdc's bundled-data cells are meant to implement):

* A channel is an unbounded FIFO of values: `Store C V := C → List V`.
* A node, when it fires, pops `k c` tokens from the front of some of its input
  channels and appends `p c` to the back of some of its output channels.
  Whether it can fire, and what it pops and pushes, depends only on its input
  channels and only on a prefix of them (`Node.mono`): adding tokens behind the
  ones a firing reads never disables or changes that firing. This is Kahn's
  sequentiality condition stated per firing.
* A graph `G : L → Node C V` is well-formed (`WF`) if every channel has at most
  one consumer node and at most one producer node.
* `step G s l` fires node `l`. Which enabled node fires is free (an arbitrary
  schedule: this is the "any interleaving" of an asynchronous circuit).

Main result `wf_diamond`: a well-formed graph has the one-step diamond, so by
`Formal.Net.Kahn.terminal_unique` every complete firing sequence from a given
state ends in the SAME state (so the same output tokens), after the same number
of firings, and by `no_divergence` no schedule runs longer than a terminating one.

Node library (`strict`, `op1`, `op2`, `fork`, `branch`, `sink`, `mux`): these
are Dynamatic's deterministic handshake ops (`constant` is `op1` of a trigger,
`cond_br` is `branch`, `mux` is `mux`). All are proved to be `Node`s.

The nondeterministic `merge` is NOT a node: it is two nodes (`mergeL`,
`mergeR`, each a valid deterministic `Node`) that share an output channel, so
the graph violates `WF.outs_disj`. `merge_not_determinate` shows that with it
two complete runs end in different states.

Untimed, unbounded FIFOs: there is no handshake, no capacity, no delay here. See
`formal/notes/C-8b-kahn.md` for the gap to the bundled-data circuit.
-/

namespace Formal.Net.Kahn

abbrev Store (C V : Type) := C → List V

/-- A firing result: how many tokens to pop from each channel, what to push. -/
abbrev Fire (C V : Type) := (C → Nat) × (C → List V)

structure Node (C V : Type) where
  ins  : C → Prop
  outs : C → Prop
  fire : Store C V → Option (Fire C V)
  pop_ins   : ∀ s r c, fire s = some r → ¬ ins c → r.1 c = 0
  push_outs : ∀ s r c, fire s = some r → ¬ outs c → r.2 c = []
  pop_le    : ∀ s r c, fire s = some r → r.1 c ≤ (s c).length
  mono : ∀ s s' r, fire s = some r → (∀ c, ins c → ∃ x, s' c = s c ++ x) → fire s' = some r

variable {C V L : Type}

def applyF (s : Store C V) (r : Fire C V) : Store C V := fun c => (s c).drop (r.1 c) ++ r.2 c

def step (G : L → Node C V) (s : Store C V) (l : L) : Option (Store C V) :=
  ((G l).fire s).map (applyF s)

/-- Fire a given schedule; `none` if some label in it is not enabled. -/
def exec (G : L → Node C V) (s : Store C V) : List L → Option (Store C V)
  | [] => some s
  | l :: ls => (step G s l).bind (fun s' => exec G s' ls)

/-- A schedule that fires completely is a run (to any store equal pointwise). -/
theorem exec_run {G : L → Node C V} {s t t' : Store C V} {ls : List L}
    (h : exec G s ls = some t) (he : ∀ c, t c = t' c) : Run (step G) s ls.length t' := by
  induction ls generalizing s with
  | nil => simp only [exec, Option.some.injEq] at h; subst h; exact run_refl_eq (funext he)
  | cons l ls ih =>
    simp only [exec] at h
    cases hs : step G s l with
    | none => rw [hs] at h; cases h
    | some s' => rw [hs] at h; exact Run.cons l hs (ih h)

/-- Unique consumer and unique producer per channel. -/
structure WF (G : L → Node C V) : Prop where
  ins_disj  : ∀ l₁ l₂ c, l₁ ≠ l₂ → (G l₁).ins c → (G l₂).ins c → False
  outs_disj : ∀ l₁ l₂ c, l₁ ≠ l₂ → (G l₁).outs c → (G l₂).outs c → False

theorem step_some {G : L → Node C V} {s s' : Store C V} {l : L} (h : step G s l = some s') :
    ∃ r, (G l).fire s = some r ∧ s' = applyF s r := by
  unfold step at h
  cases hf : (G l).fire s with
  | none => rw [hf] at h; cases h
  | some r => rw [hf] at h; cases h; exact ⟨r, rfl, rfl⟩

/-- Unique consumer per channel (static), unique producer only among labels
that can be enabled together in an `Inv`-state. This admits a `merge` (two
labels sharing an output) whose inputs `Inv` keeps mutually exclusive: the
`control_merge` of a loop header with one invocation in flight. -/
structure WFOn (G : L → Node C V) (Inv : Store C V → Prop) : Prop where
  ins_disj  : ∀ l₁ l₂ c, l₁ ≠ l₂ → (G l₁).ins c → (G l₂).ins c → False
  outs_disj : ∀ s l₁ l₂ c, Inv s → l₁ ≠ l₂ → (G l₁).fire s ≠ none → (G l₂).fire s ≠ none →
    (G l₁).outs c → (G l₂).outs c → False

theorem WF.toWFOn {G : L → Node C V} (hG : WF G) : WFOn G (fun _ => True) :=
  ⟨hG.ins_disj, fun _ l₁ l₂ c _ hne _ _ a b => hG.outs_disj l₁ l₂ c hne a b⟩

/-- Firing `l₁` leaves `l₂`'s inputs extended at the back (they are not `l₁`'s). -/
theorem other_extends {G : L → Node C V}
    (hI : ∀ l₁ l₂ c, l₁ ≠ l₂ → (G l₁).ins c → (G l₂).ins c → False) {l₁ l₂ : L} (hne : l₁ ≠ l₂)
    {s : Store C V} {r : Fire C V} (hr : (G l₁).fire s = some r) :
    ∀ c, (G l₂).ins c → ∃ x, applyF s r c = s c ++ x := by
  intro c hc
  have h0 : r.1 c = 0 :=
    (G l₁).pop_ins s r c hr (fun h1 => hI l₁ l₂ c hne h1 hc)
  exact ⟨r.2 c, by simp [applyF, h0]⟩

theorem wfOn_diamond {G : L → Node C V} {Inv : Store C V → Prop} (hG : WFOn G Inv) :
    DiamondOn (step G) Inv := by
  intro s l₁ l₂ s₁ s₂ hInv hne h1 h2
  obtain ⟨r₁, hr₁, rfl⟩ := step_some h1
  obtain ⟨r₂, hr₂, rfl⟩ := step_some h2
  have f2 : (G l₂).fire (applyF s r₁) = some r₂ :=
    (G l₂).mono s _ r₂ hr₂ (other_extends hG.ins_disj hne hr₁)
  have f1 : (G l₁).fire (applyF s r₂) = some r₁ :=
    (G l₁).mono s _ r₁ hr₁ (other_extends hG.ins_disj (Ne.symm hne) hr₂)
  refine ⟨applyF (applyF s r₁) r₂, by simp [step, f2], ?_⟩
  simp only [step, f1, Option.map_some]
  congr 1
  funext c
  have hp : r₁.1 c = 0 ∨ r₂.1 c = 0 := by
    by_cases a : (G l₁).ins c
    · exact Or.inr ((G l₂).pop_ins s r₂ c hr₂ (fun b => hG.ins_disj l₁ l₂ c hne a b))
    · exact Or.inl ((G l₁).pop_ins s r₁ c hr₁ a)
  have hq : r₁.2 c = [] ∨ r₂.2 c = [] := by
    by_cases a : (G l₁).outs c
    · exact Or.inr ((G l₂).push_outs s r₂ c hr₂ (fun b =>
        hG.outs_disj s l₁ l₂ c hInv hne (by simp [hr₁]) (by simp [hr₂]) a b))
    · exact Or.inl ((G l₁).push_outs s r₁ c hr₁ a)
  have le1 := (G l₁).pop_le s r₁ c hr₁
  have le2 := (G l₂).pop_le s r₂ c hr₂
  simp only [applyF]
  rcases hp with hp | hp <;> rcases hq with hq | hq <;>
    simp [hp, hq, List.drop_append_of_le_length, le1, le2]

theorem wf_diamond {G : L → Node C V} (hG : WF G) : DiamondOn (step G) (fun _ => True) :=
  wfOn_diamond hG.toWFOn

/-- Determinacy for well-formed graphs (`terminal_unique` + `wf_diamond`). -/
theorem wf_determinate {G : L → Node C V} (hG : WF G) {s t t' : Store C V} {n m : Nat}
    (h1 : Run (step G) s n t) (ht : Terminal (step G) t)
    (h2 : Run (step G) s m t') (ht' : Terminal (step G) t') : t' = t ∧ m = n :=
  terminal_unique closed_true (wf_diamond hG) trivial h1 ht h2 ht'

theorem wf_no_divergence {G : L → Node C V} (hG : WF G) {s t u : Store C V} {n m : Nat}
    (h1 : Run (step G) s n t) (ht : Terminal (step G) t) (h2 : Run (step G) s m u) : m ≤ n :=
  no_divergence closed_true (wf_diamond hG) trivial h1 ht h2

/-! ## Node library -/

section Lib

/-- Front tokens of the listed channels, if all are non-empty. -/
def heads (s : Store C V) : List C → Option (List V)
  | [] => some []
  | c :: cs => match s c with
    | [] => none
    | v :: _ => (heads s cs).map (v :: ·)

theorem heads_nonempty {s : Store C V} :
    ∀ {cs : List C} {vs}, heads s cs = some vs → ∀ c, c ∈ cs → s c ≠ [] := by
  intro cs
  induction cs with
  | nil => intro _ _ c hc; cases hc
  | cons d ds ih =>
    intro vs h c hc
    simp only [heads] at h
    split at h
    · cases h
    · rename_i v rest hd
      cases hh : heads s ds with
      | none => rw [hh] at h; cases h
      | some ws =>
        rcases List.mem_cons.mp hc with rfl | hc
        · rw [hd]; simp
        · exact ih hh c hc

theorem heads_mono {s s' : Store C V} :
    ∀ {cs : List C} {vs}, heads s cs = some vs → (∀ c, c ∈ cs → ∃ x, s' c = s c ++ x) →
      heads s' cs = some vs := by
  intro cs
  induction cs with
  | nil => intro vs h _; exact h
  | cons d ds ih =>
    intro vs h hx
    simp only [heads] at h ⊢
    split at h
    · cases h
    · rename_i v rest hd
      cases hh : heads s ds with
      | none => rw [hh] at h; cases h
      | some ws =>
        rw [hh] at h
        obtain ⟨x, hx'⟩ := hx d (List.mem_cons_self ..)
        rw [hx', hd]
        simp only [List.cons_append]
        rw [ih hh (fun c hc => hx c (List.mem_cons_of_mem _ hc))]
        exact h

variable [DecidableEq C]

/-- A strict node: fires when every listed input has a token, pops one from each,
pushes `f vs` (which may only touch `outs`). Ops, fork, branch, sink, constant. -/
def strict (ins : List C) (outs : C → Prop) (f : List V → C → List V)
    (hf : ∀ vs c, ¬ outs c → f vs c = []) : Node C V where
  ins := fun c => c ∈ ins
  outs := outs
  fire s := (heads s ins).map fun vs => (fun c => if c ∈ ins then 1 else 0, f vs)
  pop_ins s r c h hc := by
    cases hh : heads s ins with
    | none => rw [hh] at h; cases h
    | some vs => rw [hh] at h; cases h; simp [hc]
  push_outs s r c h hc := by
    cases hh : heads s ins with
    | none => rw [hh] at h; cases h
    | some vs => rw [hh] at h; cases h; exact hf vs c hc
  pop_le s r c h := by
    cases hh : heads s ins with
    | none => rw [hh] at h; cases h
    | some vs =>
      rw [hh] at h; cases h
      by_cases hc : c ∈ ins
      · have := heads_nonempty hh c hc
        simp only [hc, ite_true]
        cases hs : s c with
        | nil => exact absurd hs this
        | cons _ _ => simp
      · simp [hc]
  mono s s' r h hx := by
    cases hh : heads s ins with
    | none => rw [hh] at h; cases h
    | some vs => rw [hh] at h; simp only [heads_mono hh hx]; exact h

/-- `o ← g(a)` (also `constant`: `g` ignores its trigger token). -/
def op1 (a o : C) (g : V → V) : Node C V :=
  strict [a] (· = o) (fun vs c => if c = o then (match vs with | [x] => [g x] | _ => []) else [])
    (fun _ _ h => by simp [h])

/-- `o ← g(a, b)`. -/
def op2 (a b o : C) (g : V → V → V) : Node C V :=
  strict [a, b] (· = o)
    (fun vs c => if c = o then (match vs with | [x, y] => [g x y] | _ => []) else [])
    (fun _ _ h => by simp [h])

/-- `fork`: copy the token of `a` to every channel in `os`. -/
def fork (a : C) (os : List C) : Node C V :=
  strict [a] (· ∈ os) (fun vs c => if c ∈ os then vs.take 1 else []) (fun _ _ h => by simp [h])

/-- `cond_br`: data token of `d` goes to `oT` if `test` of the condition token, else `oF`. -/
def branch (c d oT oF : C) (test : V → Bool) : Node C V :=
  strict [c, d] (fun x => x = oT ∨ x = oF)
    (fun vs x => match vs with
      | [v, y] => if x = (if test v then oT else oF) then [y] else []
      | _ => [])
    (fun vs x h => by
      match vs with
      | [v, y] =>
        simp only
        split <;> simp_all
      | [] => rfl
      | [_] => rfl
      | _ :: _ :: _ :: _ => rfl)

/-- `sink`: consume and discard. -/
def sink (a : C) : Node C V :=
  strict [a] (fun _ => False) (fun _ _ => []) (fun _ _ _ => rfl)

/-- `mux`: read the select token on `c`; if `test` it, take the front of `d1`,
else of `d0`, and forward it to `o`. The unselected input is NOT read: a token
waiting there stays. Deterministic: which input is read is a function of data
already in the select FIFO, never of arrival order. -/
def mux (c d0 d1 o : C) (test : V → Bool) (h0 : c ≠ d0) (h1 : c ≠ d1) : Node C V where
  ins := fun x => x = c ∨ x = d0 ∨ x = d1
  outs := (· = o)
  fire s := match s c with
    | [] => none
    | v :: _ => match s (if test v then d1 else d0) with
      | [] => none
      | x :: _ => some (fun y => (if y = c then 1 else 0) +
                          (if y = (if test v then d1 else d0) then 1 else 0),
                        fun y => if y = o then [x] else [])
  pop_ins s r y h hy := by
    split at h
    · cases h
    · split at h
      · cases h
      · cases h
        rename_i _ v _ _ _ _ _ _
        have a : y ≠ c := fun e => hy (Or.inl e)
        have b : y ≠ (if test v then d1 else d0) := by
          split <;> exact fun e => hy (by simp [e])
        simp [a, b]
  push_outs s r y h hy := by
    split at h
    · cases h
    · split at h
      · cases h
      · cases h; simp [hy]
  pop_le s r y h := by
    split at h
    · cases h
    · rename_i v vs hc
      split at h
      · cases h
      · rename_i x xs hd
        cases h
        have hne : c ≠ (if test v then d1 else d0) := by split <;> assumption
        simp only
        by_cases e1 : y = c
        · subst e1; simp [hne, hc]
        · by_cases e2 : y = (if test v then d1 else d0)
          · rw [e2, hd]; simp [Ne.symm hne]
          · simp [e1, e2]
  mono s s' r h hx := by
    split at h
    · cases h
    · rename_i v vs hc
      obtain ⟨x1, e1⟩ := hx c (Or.inl rfl)
      rw [e1, hc]
      simp only [List.cons_append]
      split at h
      · cases h
      · rename_i x xs hd
        have hm : (fun y => y = c ∨ y = d0 ∨ y = d1) (if test v then d1 else d0) := by
          split <;> simp
        obtain ⟨x2, e2⟩ := hx _ hm
        rw [e2, hd]
        exact h

end Lib

/-! ## Why `merge` is excluded: a counterexample -/

/-- Three channels: two inputs and the merged output. -/
inductive MC | a | b | o
  deriving DecidableEq

/-- The nondeterministic `merge` of channels `a`, `b` into `o`, as two labels. -/
inductive ML | left | right
  deriving DecidableEq

def mergeG : ML → Node MC Nat
  | .left  => op1 .a .o id
  | .right => op1 .b .o id

def mergeInit : Store MC Nat := fun | .a => [1] | .b => [2] | .o => []
def mergeEndLR : Store MC Nat := fun | .o => [1, 2] | _ => []
def mergeEndRL : Store MC Nat := fun | .o => [2, 1] | _ => []

theorem mergeEnd_terminal_LR : Terminal (step mergeG) mergeEndLR := by
  intro l; cases l <;> rfl
theorem mergeEnd_terminal_RL : Terminal (step mergeG) mergeEndRL := by
  intro l; cases l <;> rfl

theorem merge_run_LR : Run (step mergeG) mergeInit 2 mergeEndLR :=
  exec_run (ls := [.left, .right]) rfl (fun c => by cases c <;> rfl)

theorem merge_run_RL : Run (step mergeG) mergeInit 2 mergeEndRL :=
  exec_run (ls := [.right, .left]) rfl (fun c => by cases c <;> rfl)

/-- With a merge, two complete runs from one state end in different states
(output `[1,2]` versus `[2,1]`): token-level determinacy fails. -/
theorem merge_not_determinate :
    ∃ s t t' n m, Run (step mergeG) s n t ∧ Terminal (step mergeG) t ∧
      Run (step mergeG) s m t' ∧ Terminal (step mergeG) t' ∧ t ≠ t' :=
  ⟨_, _, _, _, _, merge_run_LR, mergeEnd_terminal_LR, merge_run_RL, mergeEnd_terminal_RL,
    fun h => by have := congrFun h .o; simp [mergeEndLR, mergeEndRL] at this⟩

/-- ... and the only `WF` condition it breaks is unique-producer. -/
theorem merge_not_wf : ¬ WF mergeG := fun h =>
  h.outs_disj .left .right .o (by decide) rfl rfl

end Formal.Net.Kahn
