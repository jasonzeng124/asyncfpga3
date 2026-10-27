import Formal.Cells.Prelim

/-!
# Fidelity of H_KLEENE_LUT: one Kleene 2:1 mux gives the closure semantics

`Prelim.lutK` is the *closure* (Kleene) semantics of a LUT: `t`/`f` if every
INIT entry consistent with the inputs is 1/0, else `x`. Physically a 7-series
LUT is a tree of 2:1 pass-transistor muxes behind input buffers. Here we show
that the closure semantics is exactly what you get if you assume, for ONE
2:1 mux only, the Kleene behaviour `K3.mux` (select `x` passes a value iff both
legs carry it), and evaluate the tree level by level:

* `muxTree_eq_lutK`: Prelim's `muxTree init.testBit ins = lutK init ins`
  (I0 at the root, the order Prelim fixes).
* `Tree.evalK_eq_cloF`: for ANY read-once decision tree (each input tested at
  most once on every root-leaf path, inputs tested in any order, the order may
  even differ between subtrees) whose Boolean function is `G`, its Kleene
  evaluation equals the closure of `G`. So the result does not depend on which
  input sits at the root (`Tree.evalK_eq_lutK`), and in particular any two
  trees for the same table agree on every K3 input (`Tree.evalK_order_indep`).
* `build_evalK_eq_lutK`: the concrete tree that splits on the inputs in an
  arbitrary order (a permutation of `0..n-1`, e.g. A6 at the output mux as on
  silicon, or A1 at the output mux as in the research GLS `prims.v`) equals
  `lutK`.

Core Lean only.
-/

namespace Formal.Cells
namespace MuxTree

open K3

/-! ## Closure over a list of readings -/

/-- Closure verdict over the list of values of all completions. -/
def clo (vs : List Bool) : K3 :=
  if vs.all id then .t else if vs.all (!·) then .f else .x

/-- Closure semantics of a function table on Boolean vectors. -/
def cloF (G : List Bool → Bool) (ins : List K3) : K3 :=
  clo ((completions ins).map G)

/-- Closure semantics of a `Nat`-indexed table (entry `lutIdx v`). -/
def cloN (g : Nat → Bool) (ins : List K3) : K3 :=
  cloF (fun v => g (lutIdx v)) ins

theorem lutK_eq_cloF (init : Nat) (ins : List K3) :
    lutK init ins = cloF (lutB init) ins := rfl

theorem lutK_eq_cloN (init : Nat) (ins : List K3) :
    lutK init ins = cloN init.testBit ins := rfl

theorem clo_append {vs ws : List Bool} (hv : vs ≠ []) (hw : ws ≠ []) :
    clo (vs ++ ws) = K3.join (clo vs) (clo ws) := by
  match vs, ws, hv, hw with
  | a :: vs, b :: ws, _, _ =>
    unfold clo K3.join
    cases a <;> cases b <;>
      cases h1 : vs.all id <;> cases h2 : vs.all (!·) <;>
      cases h3 : ws.all id <;> cases h4 : ws.all (!·) <;>
      simp_all

theorem completions_ne_nil (ins : List K3) : completions ins ≠ [] := by
  induction ins with
  | nil => simp [completions]
  | cons a as ih =>
    cases a <;> simp [completions, K3.admits, ih]

/-- Splitting the closure at the head input: exactly one Kleene 2:1 mux. -/
theorem cloF_cons (G : List Bool → Bool) (a : K3) (as : List K3) :
    cloF G (a :: as) =
      K3.mux a (cloF (fun v => G (false :: v)) as) (cloF (fun v => G (true :: v)) as) := by
  have hne := completions_ne_nil as
  cases a with
  | f => simp [cloF, completions, K3.admits, K3.mux, Function.comp_def]
  | t => simp [cloF, completions, K3.admits, K3.mux, Function.comp_def]
  | x =>
    simp only [cloF, completions, K3.admits, K3.mux, ite_true, List.map_append,
      List.map_map]
    apply clo_append <;> simpa [Function.comp_def] using hne

/-! ## Part 1: Prelim's `muxTree` (I0 at the root) equals `lutK` -/

theorem cloN_cons (g : Nat → Bool) (a : K3) (as : List K3) :
    cloN g (a :: as) =
      K3.mux a (cloN (fun j => g (2 * j)) as) (cloN (fun j => g (2 * j + 1)) as) := by
  unfold cloN
  rw [cloF_cons]
  simp [lutIdx, Nat.add_comm]

theorem muxTree_eq_cloN (g : Nat → Bool) (ins : List K3) :
    muxTree g ins = cloN g ins := by
  induction ins generalizing g with
  | nil =>
    cases h : g 0 <;>
      simp [muxTree, cloN, cloF, completions, clo, lutIdx, h, K3.ofBool]
  | cons a as ih =>
    rw [muxTree, cloN_cons, ih, ih]

/-- **Main theorem (Prelim order).** A tree of Kleene 2:1 muxes over the INIT
bits, I0 at the output mux, computes the closure semantics `lutK`. -/
theorem muxTree_eq_lutK (init : Nat) (ins : List K3) :
    muxTree init.testBit ins = lutK init ins := by
  rw [muxTree_eq_cloN, lutK_eq_cloN]

/-! ## Part 2: any input order -/

/-- `K3.mux` commutes with itself: swapping two adjacent tree levels does
not change the output (join is associative and commutative). -/
theorem mux_mux_comm (a s p q r w : K3) :
    K3.mux a (K3.mux s p q) (K3.mux s r w) = K3.mux s (K3.mux a p r) (K3.mux a q w) := by
  cases a <;> cases s <;> cases p <;> cases q <;> cases r <;> cases w <;> rfl

/-- Splitting the closure at an arbitrary input position `i`: the closure is
one Kleene 2:1 mux, selected by input `i`, over the two closures with input
`i` fixed to 0 and to 1. -/
theorem cloF_split (G : List Bool → Bool) (ins : List K3) (i : Nat)
    (hi : i < ins.length) :
    cloF G ins = K3.mux ins[i] (cloF G (ins.set i .f)) (cloF G (ins.set i .t)) := by
  induction ins generalizing G i with
  | nil => simp at hi
  | cons a as ih =>
    cases i with
    | zero =>
      simp only [List.set_cons_zero, List.getElem_cons_zero]
      rw [cloF_cons, cloF_cons, cloF_cons]
      cases a <;> simp only [K3.mux, K3.join] <;> first | rfl | simp
    | succ k =>
      have hk : k < as.length := by simpa using hi
      simp only [List.set_cons_succ, List.getElem_cons_succ]
      rw [cloF_cons, cloF_cons, cloF_cons, ih _ k hk, ih _ k hk]
      exact mux_mux_comm _ _ _ _ _ _

/-- Completions have the right length and are consistent position-wise. -/
theorem mem_completions {ins : List K3} {v : List Bool} (h : v ∈ completions ins) :
    v.length = ins.length ∧
      ∀ (i : Nat) (hi : i < ins.length), K3.admits ins[i] (v.getD i false) = true := by
  induction ins generalizing v with
  | nil =>
    simp [completions] at h
    subst h
    simp
  | cons a as ih =>
    simp only [completions, List.mem_append] at h
    rcases h with h | h <;>
    · split at h
      · next hadm =>
        obtain ⟨w, hw, rfl⟩ := List.mem_map.1 h
        obtain ⟨hl, hc⟩ := ih hw
        refine ⟨by simp [hl], ?_⟩
        intro i hi
        cases i with
        | zero => simpa using hadm
        | succ k => simpa using hc k (by simpa using hi)
      · simp at h

theorem cloF_congr {G G' : List Bool → Bool} {ins : List K3}
    (h : ∀ v ∈ completions ins, G v = G' v) : cloF G ins = cloF G' ins := by
  unfold cloF
  rw [List.map_congr_left h]

/-- A decision tree of 2:1 muxes: `node i lo hi` is a mux selected by input
`i`, `lo` on select 0, `hi` on select 1; leaves are SRAM (INIT) bits. -/
inductive Tree where
  | leaf (b : Bool)
  | node (i : Nat) (lo hi : Tree)
  deriving Repr

namespace Tree

/-- Kleene evaluation: every mux is a Kleene 2:1 mux (H_KLEENE_LUT per mux). -/
def evalK (ins : List K3) : Tree → K3
  | leaf b => K3.ofBool b
  | node i lo hi => K3.mux (ins.getD i .x) (evalK ins lo) (evalK ins hi)

/-- Boolean evaluation. -/
def evalB (v : List Bool) : Tree → Bool
  | leaf b => b
  | node i lo hi => if v.getD i false then evalB v hi else evalB v lo

/-- Read-once: every mux selects on an input in `S`, and no input is tested
twice on a root-leaf path. This is the shape of a physical LUT tree (each
input buffer drives the selects of exactly one level). -/
def Free : (Nat → Bool) → Tree → Prop
  | _, leaf _ => True
  | S, node i lo hi =>
    S i = true ∧ Free (fun j => S j && j != i) lo ∧ Free (fun j => S j && j != i) hi

theorem evalK_set {S : Nat → Bool} {T : Tree} (hT : Free S T) {j : Nat}
    (hj : S j = false) (ins : List K3) (c : K3) :
    T.evalK (ins.set j c) = T.evalK ins := by
  induction T generalizing S with
  | leaf b => rfl
  | node i lo hi ihl ihh =>
    obtain ⟨hi, hl, hh⟩ := hT
    have hij : i ≠ j := by
      intro e; subst e; simp [hi] at hj
    have hj' : (S j && j != i) = false := by simp [hj]
    simp only [evalK]
    rw [ihl hl hj', ihh hh hj']
    simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hij)]

theorem evalB_set {S : Nat → Bool} {T : Tree} (hT : Free S T) {j : Nat}
    (hj : S j = false) (v : List Bool) (c : Bool) :
    T.evalB (v.set j c) = T.evalB v := by
  induction T generalizing S with
  | leaf b => rfl
  | node i lo hi ihl ihh =>
    obtain ⟨hi, hl, hh⟩ := hT
    have hij : i ≠ j := by
      intro e; subst e; simp [hi] at hj
    have hj' : (S j && j != i) = false := by simp [hj]
    simp only [evalB]
    rw [ihl hl hj', ihh hh hj']
    simp [List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hij)]

/-- **Main theorem (any order).** A read-once tree of Kleene 2:1 muxes over
inputs in range evaluates to the closure of its own Boolean function. -/
theorem evalK_eq_cloF {S : Nat → Bool} {T : Tree} (hT : Free S T)
    (ins : List K3) (hS : ∀ j, S j = true → j < ins.length) :
    T.evalK ins = cloF T.evalB ins := by
  induction T generalizing S ins with
  | leaf b =>
    simp only [evalK, cloF, evalB]
    have hne := completions_ne_nil ins
    generalize completions ins = cs at hne
    match cs, hne with
    | c :: cs, _ =>
      cases b <;> simp [clo, K3.ofBool, List.all_map, Function.comp_def]
  | node i lo hi ihl ihh =>
    obtain ⟨hiS, hl, hh⟩ := hT
    have hil : i < ins.length := hS i hiS
    have hS' : ∀ (c : K3) j, (S j && j != i) = true → j < (ins.set i c).length := by
      intro c j h
      simp only [Bool.and_eq_true] at h
      simpa using hS j h.1
    have hni : (S i && i != i) = false := by simp
    -- each subtree, evaluated with input i pinned, is the closure of the
    -- whole tree's function with input i pinned
    have hlo : lo.evalK ins = cloF (node i lo hi).evalB (ins.set i .f) := by
      rw [← evalK_set hl hni ins .f, ihl hl _ (hS' .f)]
      apply cloF_congr
      intro v hv
      obtain ⟨hlen, hc⟩ := mem_completions hv
      have := hc i (by simpa using hil)
      simp only [List.getElem_set_self, K3.admits] at this
      have h0 : v.getD i false = false := by simpa using this
      show lo.evalB v = (if v.getD i false then hi.evalB v else lo.evalB v)
      rw [h0]; rfl
    have hhi : hi.evalK ins = cloF (node i lo hi).evalB (ins.set i .t) := by
      rw [← evalK_set hh hni ins .t, ihh hh _ (hS' .t)]
      apply cloF_congr
      intro v hv
      obtain ⟨hlen, hc⟩ := mem_completions hv
      have := hc i (by simpa using hil)
      simp only [List.getElem_set_self, K3.admits] at this
      show hi.evalB v = (if v.getD i false then hi.evalB v else lo.evalB v)
      rw [this]; rfl
    rw [cloF_split _ ins i hil]
    simp only [evalK, hlo, hhi, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hil,
      Option.getD_some]

/-- Any read-once tree that implements the LUT's Boolean function on vectors of
the right length computes `lutK`, whatever input sits at the root. -/
theorem evalK_eq_lutK {S : Nat → Bool} {T : Tree} (hT : Free S T) (init : Nat)
    (ins : List K3) (hS : ∀ j, S j = true → j < ins.length)
    (himpl : ∀ v : List Bool, v.length = ins.length → T.evalB v = lutB init v) :
    T.evalK ins = lutK init ins := by
  rw [evalK_eq_cloF hT ins hS, lutK_eq_cloF]
  apply cloF_congr
  intro v hv
  exact himpl v (mem_completions hv).1

/-- Order independence: two read-once trees with the same Boolean function
(on vectors of the input length) give the same K3 output on every input. -/
theorem evalK_order_indep {S S' : Nat → Bool} {T T' : Tree} (hT : Free S T)
    (hT' : Free S' T') (ins : List K3) (hS : ∀ j, S j = true → j < ins.length)
    (hS' : ∀ j, S' j = true → j < ins.length)
    (heq : ∀ v : List Bool, v.length = ins.length → T.evalB v = T'.evalB v) :
    T.evalK ins = T'.evalK ins := by
  rw [evalK_eq_cloF hT ins hS, evalK_eq_cloF hT' ins hS']
  apply cloF_congr
  intro v hv
  exact heq v (mem_completions hv).1

end Tree

/-! ## The concrete tree for an arbitrary split order -/

/-- The full mux tree that splits on `order` (head = output mux), leaves read
`G` at the partial assignment `acc` with the tested positions filled in. -/
def build (G : List Bool → Bool) : List Nat → List Bool → Tree
  | [], acc => .leaf (G acc)
  | i :: o, acc => .node i (build G o (acc.set i false)) (build G o (acc.set i true))

/-- Fill the positions in `order` of `acc` from `v`. -/
def fill (v : List Bool) : List Nat → List Bool → List Bool
  | [], acc => acc
  | i :: o, acc => fill v o (acc.set i (v.getD i false))

theorem build_evalB (G : List Bool → Bool) (v : List Bool) (order : List Nat)
    (acc : List Bool) : (build G order acc).evalB v = G (fill v order acc) := by
  induction order generalizing acc with
  | nil => rfl
  | cons i o ih =>
    simp only [build, Tree.evalB, fill]
    cases h : v.getD i false <;> simp [ih]

theorem fill_length (v : List Bool) (order : List Nat) (acc : List Bool) :
    (fill v order acc).length = acc.length := by
  induction order generalizing acc with
  | nil => rfl
  | cons i o ih => simp [fill, ih]

theorem fill_getD (v : List Bool) (order : List Nat) (acc : List Bool) (j : Nat)
    (hj : j < acc.length) :
    (fill v order acc).getD j false = if j ∈ order then v.getD j false else acc.getD j false := by
  induction order generalizing acc with
  | nil => simp [fill]
  | cons i o ih =>
    simp only [fill]
    rw [ih _ (by simpa using hj)]
    by_cases hjo : j ∈ o
    · simp [hjo]
    · by_cases hji : j = i
      · subst hji
        simp [hjo, List.getD_eq_getElem?_getD, List.getElem?_set_self hj]
      · simp [hjo, hji, List.getD_eq_getElem?_getD, List.getElem?_set_ne (Ne.symm hji)]

theorem build_free (G : List Bool → Bool) (order : List Nat) (hnd : order.Nodup)
    (S : Nat → Bool) (hS : ∀ i ∈ order, S i = true) (acc : List Bool) :
    Tree.Free S (build G order acc) := by
  induction order generalizing S acc with
  | nil => trivial
  | cons i o ih =>
    have hnd' := List.nodup_cons.1 hnd
    have hsub : ∀ j ∈ o, (S j && j != i) = true := by
      intro j hj
      have hji : j ≠ i := fun e => hnd'.1 (e ▸ hj)
      simp [hS j (List.mem_cons_of_mem _ hj), hji]
    exact ⟨hS i (by simp), ih hnd'.2 _ hsub _, ih hnd'.2 _ hsub _⟩

/-- **Any split order.** If `order` lists every input position `0..n-1` exactly
once (any permutation: A6 at the output mux as on silicon, A1 at the output mux
as in the research GLS model, or anything else), the Kleene evaluation of the
mux tree built in that order is `lutK`. -/
theorem build_evalK_eq_lutK (init : Nat) (ins : List K3) (order : List Nat)
    (hnd : order.Nodup) (hcov : ∀ j, j ∈ order ↔ j < ins.length) :
    (build (lutB init) order (List.replicate ins.length false)).evalK ins =
      lutK init ins := by
  apply Tree.evalK_eq_lutK
    (build_free _ order hnd (fun j => decide (j ∈ order)) (by simp) _) init ins
  · intro j h; exact (hcov j).1 (by simpa using h)
  · intro v hv
    rw [build_evalB]
    congr 1
    apply List.ext_getElem
    · simp [fill_length, hv]
    · intro j h1 h2
      have hj : j < (List.replicate ins.length false).length := by simpa [hv] using h2
      have := fill_getD v order _ j hj
      have hjo : j ∈ order := (hcov j).2 (by simpa [hv] using h2)
      simp only [hjo, ite_true, List.getD_eq_getElem?_getD,
        List.getElem?_eq_getElem h1, List.getElem?_eq_getElem h2, Option.getD_some] at this
      exact this

/-- Example: the physical 7-series order (A6 = I5 at the output mux, A1 = I0 at
the SRAM end) on a 6-input LUT. -/
theorem lut6_silicon_order (init : Nat) (ins : List K3) (h6 : ins.length = 6) :
    (build (lutB init) [5, 4, 3, 2, 1, 0] (List.replicate ins.length false)).evalK ins =
      lutK init ins := by
  apply build_evalK_eq_lutK
  · decide
  · intro j; rw [h6]; simp; omega

/-- The research GLS order (`prims.v`: A1 = I0 at the output mux, A6 at the
SRAM end, Verilog `?:` merging bitwise on an `x` select) is Prelim's order. -/
theorem lut6_gls_order (init : Nat) (ins : List K3) (h6 : ins.length = 6) :
    (build (lutB init) [0, 1, 2, 3, 4, 5] (List.replicate ins.length false)).evalK ins =
      lutK init ins := by
  apply build_evalK_eq_lutK
  · decide
  · intro j; rw [h6]; simp; omega

/-- Read-once is necessary: a tree that tests input 0 twice on one path
computes the constant 1, but its Kleene evaluation on `x` is `x`, not `t`. -/
theorem not_free_counterexample :
    let T := Tree.node 0 (Tree.node 0 (.leaf true) (.leaf false)) (.leaf true)
    (∀ b : Bool, T.evalB [b] = true) ∧ T.evalK [K3.x] = K3.x ∧
      cloF T.evalB [K3.x] = K3.t := by
  refine ⟨?_, rfl, rfl⟩
  intro b; cases b <;> rfl

end MuxTree
end Formal.Cells
