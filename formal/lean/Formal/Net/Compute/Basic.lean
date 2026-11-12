import Formal.Core.LutList
import Formal.Core.Prims.Carry

/-!
# H_COMPUTE_FN, part 1: combinational Xilinx netlists, support and cut points

Problem statement. The capstone treats each bdc compute unit (`bdc_fused_*`: `+`, `-`, compares,
shifts, `?:`, as inferred by yosys) as an ideal zero-time function of its input tokens
(`OpsJoin`): hypothesis **H_COMPUTE_FN**, "the synthesized LUT/CARRY4 netlist equals the MLIR
op", open until now. This file is the generic machinery to discharge it per unit from the
yosys netlist itself:

* `Cell`: the combinational primitives yosys' `synth_xilinx` emits in those units: LUT1..LUT6
  (`lutB INIT`, the same LUT semantics as the generated library cells), MUXF7/MUXF8 (`bmux`,
  `O = S ? I1 : I0`), INV, CARRY4 (`Formal.Core.Prims.bout`, shard A's MUXCY/XORCY chain, with
  `c0 = CI | CYINIT` as in the UNISIM model). Boolean values: this is the FUNCTION of the unit
  (what it settles to), not its timing; timing is H_COMPUTE_DELAY (rule A), untouched here.
* `run env C cells`: evaluate the cells in list order; a net in the CUT list `C` takes a free
  leaf value `env (.cut n)` instead of its computed value.
* `support_sound`: a wire's value depends only on the leaves in its computed support `swOf`.
* `cut_sound`: if every cut leaf carries the net's real value (and no net has two drivers),
  the cut evaluation IS the real evaluation (`C = []`).
* `local_sound`: a decidable check over all `2^|S|` assignments of a leaf list `S` covering the
  support proves `eval = spec` for EVERY environment. With cut points this turns a 64-input
  arithmetic unit into per-stage checks of 9 leaves plus a generic composition lemma.

Not covered here: which units meet which spec (`Compute/Gcd*.lean`), the netlist extraction
(`formal/tools/compute/`), timing, glitches, X values.
-/

namespace Formal.Net.Compute
open Formal.Core.Prims (COut bout bmux)

/-- A leaf of an evaluation: input port `p`, bit `k`; or a cut net `n`. -/
inductive Leaf where
  | inp (p k : Nat)
  | cut (n : Nat)
  deriving DecidableEq, Repr

/-- A cell input: an input bit, an internal net, or a constant. -/
inductive W where
  | inp (p k : Nat)
  | net (n : Nat)
  | c0
  | c1
  deriving DecidableEq, Repr

/-- yosys `synth_xilinx` combinational cells. A CARRY4 always lists its 8 output nets
(`O0..O3`, `CO0..CO3`; the extractor gives unconnected outputs fresh ids). -/
inductive Cell where
  | lut (init : Nat) (ins : List W) (o : Nat)
  | muxf (i0 i1 s : W) (o : Nat)
  | inv (i : W) (o : Nat)
  | carry4 (ci cyinit : W) (di s : List W) (o0 o1 o2 o3 co0 co1 co2 co3 : Nat)
  deriving Repr

def Cell.ins : Cell → List W
  | .lut _ is _ => is
  | .muxf a b s _ => [a, b, s]
  | .inv i _ => [i]
  | .carry4 ci cy di s _ _ _ _ _ _ _ _ => ci :: cy :: (di ++ s)

def Cell.outs : Cell → List Nat
  | .lut _ _ o => [o]
  | .muxf _ _ _ o => [o]
  | .inv _ o => [o]
  | .carry4 _ _ _ _ o0 o1 o2 o3 co0 co1 co2 co3 => [o0, o1, o2, o3, co0, co1, co2, co3]

/-- The value of a wire. -/
def wv (env : Leaf → Bool) (v : Nat → Bool) : W → Bool
  | .inp p k => env (.inp p k)
  | .net n => v n
  | .c0 => false
  | .c1 => true

/-- CARRY4 pin vector (`Formal.Core.Prims` order: `c0`, `DI0..3`, `S0..3`). -/
def c4vec (r : W → Bool) (ci cy : W) (di s : List W) : Fin 9 → Bool := fun j =>
  if j.val = 0 then (r ci || r cy)
  else if j.val ≤ 4 then r (di.getD (j.val - 1) .c0) else r (s.getD (j.val - 5) .c0)

/-- Output values, in `outs` order. -/
def Cell.vals (r : W → Bool) : Cell → List Bool
  | .lut init is _ => [Formal.Core.LutList.lutB init (is.map r)]
  | .muxf a b s _ => [bmux (r s) (r a) (r b)]
  | .inv i _ => [!(r i)]
  | .carry4 ci cy di s _ _ _ _ _ _ _ _ =>
    let x := c4vec r ci cy di s
    [bout x .o0, bout x .o1, bout x .o2, bout x .o3, bout x .co0, bout x .co1, bout x .co2,
     bout x .co3]

/-- A cut net takes its leaf value. -/
def cutv (env : Leaf → Bool) (C : List Nat) (n : Nat) (b : Bool) : Bool :=
  if n ∈ C then env (.cut n) else b

/-- One cell: each output net gets its value (first occurrence in `outs`), or its cut leaf. -/
def step (env : Leaf → Bool) (C : List Nat) (v : Nat → Bool) (c : Cell) : Nat → Bool :=
  fun m => if m ∈ c.outs then cutv env C m ((c.vals (wv env v)).getD (c.outs.idxOf m) false)
    else v m

def run (env : Leaf → Bool) (C : List Nat) : List Cell → (Nat → Bool) → (Nat → Bool)
  | [], v => v
  | c :: cs, v => run env C cs (step env C v c)

/-- The value of wire `w` after evaluating `cells` from all-zero nets. -/
def eval (env : Leaf → Bool) (C : List Nat) (cells : List Cell) (w : W) : Bool :=
  wv env (run env C cells (fun _ => false)) w

/-! ## Supports -/

def sw (s : Nat → List Leaf) : W → List Leaf
  | .inp p k => [.inp p k]
  | .net n => s n
  | .c0 => []
  | .c1 => []

def sstep (C : List Nat) (s : Nat → List Leaf) (c : Cell) : Nat → List Leaf :=
  fun m => if m ∈ c.outs then (if m ∈ C then [.cut m] else c.ins.flatMap (sw s)) else s m

def srun (C : List Nat) : List Cell → (Nat → List Leaf) → (Nat → List Leaf)
  | [], s => s
  | c :: cs, s => srun C cs (sstep C s c)

/-- The support of wire `w`. -/
def swOf (C : List Nat) (cells : List Cell) (w : W) : List Leaf :=
  sw (srun C cells (fun _ => [])) w

theorem c4vec_congr {r1 r2 : W → Bool} {ci cy : W} {di s : List W}
    (h : ∀ w ∈ ci :: cy :: (di ++ s), r1 w = r2 w) (h0 : r1 .c0 = r2 .c0) :
    c4vec r1 ci cy di s = c4vec r2 ci cy di s := by
  funext j
  simp only [c4vec]
  have hci := h ci (by simp)
  have hcy := h cy (by simp)
  have hg : ∀ (l : List W) (k : Nat), (∀ w ∈ l, r1 w = r2 w) → r1 (l.getD k .c0) = r2 (l.getD k .c0) := by
    intro l k hl
    rw [List.getD_eq_getElem?_getD]
    cases hk : l[k]? with
    | none => simpa using h0
    | some w => exact hl w (List.mem_of_getElem? hk)
  rw [hci, hcy, hg di (j.val - 1) (fun w hw => h w (by simp [hw])),
    hg s (j.val - 5) (fun w hw => h w (by simp [hw]))]

theorem vals_congr {r1 r2 : W → Bool} (c : Cell) (h : ∀ w ∈ c.ins, r1 w = r2 w)
    (h0 : r1 .c0 = r2 .c0) : c.vals r1 = c.vals r2 := by
  cases c with
  | lut init is o =>
    simp only [Cell.vals, Cell.ins] at h ⊢
    rw [List.map_congr_left (fun w hw => h w hw)]
  | muxf a b s o =>
    simp only [Cell.vals, Cell.ins] at h ⊢
    rw [h a (by simp), h b (by simp), h s (by simp)]
  | inv i o =>
    simp only [Cell.vals, Cell.ins] at h ⊢
    rw [h i (by simp)]
  | carry4 ci cy di s o0 o1 o2 o3 co0 co1 co2 co3 =>
    simp only [Cell.vals]
    rw [c4vec_congr h h0]

/-- The support invariant: nets agree wherever their supports' leaves agree. -/
def SInv (env1 env2 : Leaf → Bool) (s : Nat → List Leaf) (v1 v2 : Nat → Bool) : Prop :=
  ∀ m, (∀ l ∈ s m, env1 l = env2 l) → v1 m = v2 m

theorem wv_agree {env1 env2 : Leaf → Bool} {s : Nat → List Leaf} {v1 v2 : Nat → Bool}
    (hI : SInv env1 env2 s v1 v2) (w : W) (h : ∀ l ∈ sw s w, env1 l = env2 l) :
    wv env1 v1 w = wv env2 v2 w := by
  cases w with
  | inp p k => exact h _ (by simp [sw])
  | net n => exact hI n h
  | c0 => rfl
  | c1 => rfl

theorem sinv_step {env1 env2 : Leaf → Bool} {C : List Nat} {s : Nat → List Leaf}
    {v1 v2 : Nat → Bool} (hI : SInv env1 env2 s v1 v2) (c : Cell) :
    SInv env1 env2 (sstep C s c) (step env1 C v1 c) (step env2 C v2 c) := by
  intro m hm
  simp only [step, sstep] at hm ⊢
  by_cases ho : m ∈ c.outs
  · simp only [ho, if_true] at hm ⊢
    by_cases hc : m ∈ C
    · simp only [hc, if_true] at hm
      simp only [cutv, hc, if_true]
      exact hm (.cut m) (List.mem_singleton_self _)
    · simp only [hc, if_false] at hm
      simp only [cutv, hc, if_false]
      rw [vals_congr c (fun w hw => wv_agree hI w (fun l hl => hm l
        (List.mem_flatMap.mpr ⟨w, hw, hl⟩))) rfl]
  · simp only [ho, if_false] at hm ⊢
    exact hI m hm

theorem sinv_run {env1 env2 : Leaf → Bool} {C : List Nat} :
    ∀ (cells : List Cell) {s : Nat → List Leaf} {v1 v2 : Nat → Bool}, SInv env1 env2 s v1 v2 →
      SInv env1 env2 (srun C cells s) (run env1 C cells v1) (run env2 C cells v2)
  | [], _, _, _, h => h
  | c :: cs, _, _, _, h => sinv_run cs (sinv_step h c)

/-- **Support soundness.** Two environments that agree on the support of `w` give `w` the same
value. -/
theorem support_sound (env1 env2 : Leaf → Bool) (C : List Nat) (cells : List Cell) (w : W)
    (h : ∀ l ∈ swOf C cells w, env1 l = env2 l) : eval env1 C cells w = eval env2 C cells w := by
  have hI : SInv env1 env2 (srun C cells (fun _ => [])) (run env1 C cells (fun _ => false))
      (run env2 C cells (fun _ => false)) := sinv_run cells (fun _ _ => rfl)
  exact wv_agree hI w h

/-! ## Cut points -/

theorem run_preserve {env : Leaf → Bool} {C : List Nat} :
    ∀ (cells : List Cell) (v : Nat → Bool) (m : Nat), m ∉ cells.flatMap Cell.outs →
      run env C cells v m = v m
  | [], _, _, _ => rfl
  | c :: cs, v, m, h => by
    simp only [List.flatMap_cons, List.mem_append, not_or] at h
    rw [run, run_preserve cs _ m h.2]
    simp [step, h.1]

/-- **Cut soundness.** Let `env'` agree with `env` on input bits and give each cut leaf the
REAL (uncut) value of its net. If no net has two drivers, evaluating with the cuts gives the
real value of every net. -/
theorem cut_sound (env env' : Leaf → Bool) (C : List Nat)
    (hin : ∀ p k, env' (.inp p k) = env (.inp p k)) :
    ∀ (cells : List Cell) (v : Nat → Bool), (cells.flatMap Cell.outs).Nodup →
      (∀ n ∈ C, env' (.cut n) = run env [] cells v n) →
      ∀ m, run env' C cells v m = run env [] cells v m
  | [], _, _, _, _ => rfl
  | c :: cs, v, hnd, hcut, m => by
    simp only [List.flatMap_cons, List.nodup_append] at hnd
    have hw : ∀ w, wv env' v w = wv env v w := by
      intro w; cases w <;> simp [wv, hin]
    have hvals : c.vals (wv env' v) = c.vals (wv env v) := vals_congr c (fun w _ => hw w) rfl
    have hs : step env' C v c = step env [] v c := by
      funext m'
      simp only [step]
      by_cases ho : m' ∈ c.outs
      · rw [if_pos ho, if_pos ho, hvals]
        by_cases hc : m' ∈ C
        · simp only [cutv, if_pos hc, List.not_mem_nil, if_false]
          rw [hcut m' hc]
          show run env [] cs (step env [] v c) m' = _
          rw [run_preserve cs _ m' (fun hm => hnd.2.2 m' ho m' hm rfl)]
          simp [step, ho, cutv]
        · simp [cutv, hc]
      · rw [if_neg ho, if_neg ho]
    show run env' C cs (step env' C v c) m = run env [] cs (step env [] v c) m
    rw [hs]
    exact cut_sound env env' C hin cs _ hnd.2.1 (fun n hn => hcut n hn) m

/-! ## Exhaustive local checks -/

/-- Environment number `m` over the leaf list `S`: leaf `S[i]` is bit `i` of `m`. -/
def envOf (S : List Leaf) (m : Nat) : Leaf → Bool := fun l => m.testBit (S.idxOf l)

/-- Encode an environment's values on `S`. -/
def enc : List Leaf → (Leaf → Bool) → Nat
  | [], _ => 0
  | l :: S, env => (if env l then 1 else 0) + 2 * enc S env

theorem testBit_enc (env : Leaf → Bool) : ∀ (S : List Leaf), S.Nodup → ∀ l ∈ S,
    (enc S env).testBit (S.idxOf l) = env l
  | [], _, l, hl => by simp at hl
  | x :: S, hnd, l, hl => by
    simp only [List.nodup_cons] at hnd
    by_cases hx : l = x
    · subst hx
      simp only [List.idxOf_cons_self, enc]
      cases env l <;> simp [Nat.testBit_zero]
    · have hlS : l ∈ S := by simpa [hx] using hl
      have hi : (x :: S).idxOf l = S.idxOf l + 1 := by
        simp [List.idxOf_cons, Ne.symm hx]
      rw [hi, enc]
      have := testBit_enc env S hnd.2 l hlS
      rw [← this]
      cases env x
      · simp only [Bool.false_eq_true, if_false, Nat.zero_add]
        rw [Nat.testBit_succ, Nat.mul_div_cancel_left _ (by decide)]
      · simp only [if_true]
        rw [Nat.testBit_succ]
        congr 1
        omega

theorem enc_lt (env : Leaf → Bool) : ∀ S : List Leaf, enc S env < 2 ^ S.length
  | [] => by simp [enc]
  | l :: S => by
    have := enc_lt env S
    simp only [enc, List.length_cons, Nat.pow_succ]
    cases env l <;> simp <;> omega

/-- The decidable local check: for every assignment of `S`, `w` evaluates to `spec`. -/
def LocalOK (C : List Nat) (cells : List Cell) (w : W) (S : List Leaf)
    (spec : List Bool → Bool) : Prop :=
  ∀ m, m < 2 ^ S.length → eval (envOf S m) C cells w = spec (S.map (envOf S m))

instance (C : List Nat) (cells : List Cell) (w : W) (S : List Leaf) (spec : List Bool → Bool) :
    Decidable (LocalOK C cells w S spec) := by
  unfold LocalOK; exact Nat.decidableBallLT _ _

/-- **Local soundness.** A passing exhaustive check over a duplicate-free leaf list covering
the support proves `eval = spec` for every environment. -/
theorem local_sound {C : List Nat} {cells : List Cell} {w : W} {S : List Leaf}
    {spec : List Bool → Bool} (hok : LocalOK C cells w S spec) (hnd : S.Nodup)
    (hsup : ∀ l ∈ swOf C cells w, l ∈ S) (env : Leaf → Bool) :
    eval env C cells w = spec (S.map env) := by
  have hag : ∀ l ∈ S, envOf S (enc S env) l = env l := fun l hl => testBit_enc env S hnd l hl
  have h1 := support_sound env (envOf S (enc S env)) C cells w
    (fun l hl => (hag l (hsup l hl)).symm)
  have h2 : S.map env = S.map (envOf S (enc S env)) :=
    List.map_congr_left (fun l hl => (hag l hl).symm)
  rw [h1, h2]
  exact hok _ (enc_lt env S)

end Formal.Net.Compute

/-! ## Cone restriction (speed: evaluate only what a wire needs) -/

namespace Formal.Net.Compute

/-- Nets read by a cell. -/
def insNets (c : Cell) : List Nat := c.ins.filterMap fun w => match w with | .net n => some n | _ => none

/-- Right-to-left pass: keep a cell iff one of its outputs is needed later; then its input nets
are needed. Returns the kept cells (in order) and the nets needed before them. -/
def filt : List Cell → List Nat → List Cell × List Nat
  | [], N => ([], N)
  | c :: cs, N =>
    let r := filt cs N
    if c.outs.any (fun n => decide (n ∈ r.2)) then (c :: r.1, insNets c ++ r.2) else r

theorem filt_mono : ∀ (cells : List Cell) (N : List Nat), ∀ n ∈ N, n ∈ (filt cells N).2
  | [], _, _, h => h
  | c :: cs, N, n, h => by
    simp only [filt]
    split
    · exact List.mem_append_right _ (filt_mono cs N n h)
    · exact filt_mono cs N n h

theorem run_filt (env : Leaf → Bool) (C : List Nat) :
    ∀ (cells : List Cell) (N : List Nat) (v1 v2 : Nat → Bool),
      (∀ n ∈ (filt cells N).2, v1 n = v2 n) →
      ∀ n ∈ N, run env C cells v1 n = run env C (filt cells N).1 v2 n
  | [], _, _, _, h, n, hn => h n hn
  | c :: cs, N, v1, v2, h, n, hn => by
    by_cases hk : (c.outs.any fun n => decide (n ∈ (filt cs N).2)) = true
    · have e : filt (c :: cs) N = (c :: (filt cs N).1, insNets c ++ (filt cs N).2) := by
        simp only [filt, hk, if_true]
      rw [e] at h ⊢
      simp only [run]
      apply run_filt env C cs N _ _ _ n hn
      intro m hm
      simp only [step]
      by_cases ho : m ∈ c.outs
      · simp only [ho, if_true]
        have hv : c.vals (wv env v1) = c.vals (wv env v2) := by
          refine vals_congr (r1 := wv env v1) (r2 := wv env v2) c ?_ rfl
          intro w hw
          cases w with
          | inp p k => rfl
          | net k =>
            apply h k
            apply List.mem_append_left
            simp only [insNets, List.mem_filterMap]
            exact ⟨.net k, hw, rfl⟩
          | c0 => rfl
          | c1 => rfl
        rw [hv]
      · simp only [ho, if_false]
        exact h m (List.mem_append_right _ hm)
    · have e : filt (c :: cs) N = filt cs N := by
        simp only [filt, hk, Bool.false_eq_true, if_false]
      rw [e] at h ⊢
      simp only [run]
      apply run_filt env C cs N _ _ _ n hn
      intro m hm
      simp only [step]
      have ho : m ∉ c.outs := by
        intro ho
        apply hk
        exact List.any_eq_true.mpr ⟨m, ho, by simpa using hm⟩
      simp only [ho, if_false]
      exact h m hm

/-- **Cone restriction.** A net's value is the same when only its cone is evaluated. -/
theorem eval_filt (env : Leaf → Bool) (C : List Nat) (cells : List Cell) (n : Nat) :
    eval env C cells (.net n) = eval env C (filt cells [n]).1 (.net n) :=
  run_filt env C cells [n] _ _ (fun _ _ => rfl) n (List.mem_singleton_self n)

end Formal.Net.Compute
