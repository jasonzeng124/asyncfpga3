import Formal.Cells.Prelim

/-!
# Probe Cm, part 0: a finite speed-independence checker with excitation masks

This is `MergeMuxSI`'s `Sys` checker (probe Lib3), copied and changed in two
ways so that the 20-25 variable models of the generated `bdc_amerge2_0`,
`bdc_amerge3_0` and `bdc_muxn3_32` check in reasonable kernel time:

* the reachable-set certificate is a search tree of `(state, excitation mask)`
  pairs, so each state's excitation vector is evaluated ONCE (the kernel checks
  `e = exm s`), and the hazard check of a successor reads the successor's
  stored mask instead of re-evaluating every gate (O(N V) gate evaluations
  instead of O(N V^2));
* liveness is a state predicate: in every reachable state in which a client is
  waiting (`waiting s`), some allowed step of a `live` variable (a gate, wire
  or server, not a client) exists. With clients that never move unless their
  protocol lets them, this says a waiting token is never stranded in a
  quiescent circuit ("no token loss"), not merely "something can move".

Everything else is as in `MergeMuxSI` (whose module doc explains the
interleaving model): one variable changes per step, gates fire atomically to
their LUT value, named environment and timing hypotheses are scheduling
filters (`allow`). Lean trusts nothing computed outside: the trees are
produced by an explorer run with `#eval` in a scratch file (not in the tree)
and only checked here with `decide +kernel`.

Imports only `Formal.Cells.Prelim` (no other cell file), so a concurrent port
of the other cell files cannot break it.
-/

namespace Formal.Cells.AMergeSys

/-! ## Bit helpers -/

def tb (s i : Nat) : Bool := s.testBit i
/-- Overwrite bit `i` with `b`. -/
def setB (t i : Nat) (b : Bool) : Nat := if t.testBit i == b then t else t ^^^ 2 ^ i
/-- The 2-bit field at bit `p`. -/
def getO (p s : Nat) : Nat := (s >>> p) % 4
def setO (p t o : Nat) : Nat := t - getO p t * 2 ^ p + o * 2 ^ p

/-- Every `k < n` satisfies `p`. -/
def allBelow (p : Nat → Bool) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) true (fun k ih => ih && p k) n

theorem allBelow_succ (p : Nat → Bool) (n : Nat) : allBelow p (n + 1) = (allBelow p n && p n) := rfl

theorem allBelow_spec {p : Nat → Bool} : ∀ {n k}, allBelow p n = true → k < n → p k = true
  | n + 1, k, h, hk => by
    simp only [allBelow_succ, Bool.and_eq_true] at h
    by_cases hkn : k = n
    · subst hkn; exact h.2
    · exact allBelow_spec h.1 (by omega)

/-- Some `k < n` satisfies `p`. -/
def anyBelow (p : Nat → Bool) (n : Nat) : Bool :=
  Nat.rec (motive := fun _ => Bool) false (fun k ih => ih || p k) n

theorem anyBelow_succ (p : Nat → Bool) (n : Nat) : anyBelow p (n + 1) = (anyBelow p n || p n) := rfl

theorem anyBelow_spec {p : Nat → Bool} : ∀ {n}, anyBelow p n = true → ∃ k, k < n ∧ p k = true
  | 0, h => by simp [anyBelow] at h
  | n + 1, h => by
    simp only [anyBelow_succ, Bool.or_eq_true] at h
    rcases h with h | h
    · obtain ⟨k, hk, hp⟩ := anyBelow_spec h; exact ⟨k, by omega, hp⟩
    · exact ⟨n, by omega, h⟩

/-! ## Search tree of (state, mask) pairs -/

inductive KTree where
  | leaf
  | node (l : KTree) (k e : Nat) (r : KTree)

namespace KTree
def find : KTree → Nat → Option Nat
  | leaf, _ => none
  | node l k e r, s => if s < k then find l s else if k < s then find r s else some e

def all (p : Nat → Nat → Bool) : KTree → Bool
  | leaf => true
  | node l k e r => all p l && p k e && all p r

@[simp] theorem find_leaf (s : Nat) : find leaf s = none := rfl
@[simp] theorem find_node (l : KTree) (k e : Nat) (r : KTree) (s : Nat) :
    find (node l k e r) s = if s < k then find l s else if k < s then find r s else some e := rfl
@[simp] theorem all_leaf (p : Nat → Nat → Bool) : all p leaf = true := rfl
@[simp] theorem all_node' (p : Nat → Nat → Bool) (l : KTree) (k e : Nat) (r : KTree) :
    all p (node l k e r) = (all p l && p k e && all p r) := rfl

theorem all_find {p : Nat → Nat → Bool} {t : KTree} {s e : Nat} (ha : all p t = true)
    (hm : find t s = some e) : p s e = true := by
  induction t with
  | leaf => simp at hm
  | node l k e' r ihl ihr =>
    simp only [all_node', Bool.and_eq_true] at ha
    simp only [find_node] at hm
    by_cases h1 : s < k
    · simp only [h1, ite_true] at hm; exact ihl ha.1.1 hm
    · by_cases h2 : k < s
      · simp only [h1, h2, ite_true, ite_false] at hm; exact ihr ha.2 hm
      · have : s = k := by omega
        subst this
        simp only [h1, ite_false, Option.some.injEq] at hm
        subst hm; exact ha.1.2

theorem all_node {p : Nat → Nat → Bool} {l r : KTree} {k e : Nat} (hl : all p l = true)
    (hk : p k e = true) (hr : all p r = true) : all p (node l k e r) = true := by
  simp [hl, hk, hr]

def size : KTree → Nat
  | leaf => 0
  | node l _ _ r => size l + 1 + size r
end KTree

/-! ## Models -/

/-- A finite interleaving model. Variables `0 .. V-1` are wires/gates/clients;
bits above are ghost state written only by `fire`. -/
structure Sys where
  V : Nat
  /-- The next-value vector: bit `v` is what variable `v` would become if it
  fired now (its gate/wire/environment function of the current state). -/
  nxv : Nat → Nat
  /-- The scheduling filter (named hypotheses): `allow e s v`, where `e` is
  the excitation mask of `s` (`exm s`), through which filters read which
  gates are excited without re-evaluating them. -/
  allow : Nat → Nat → Nat → Bool
  fire : Nat → Nat → Nat
  spec : Nat → Nat → Bool
  good : Nat → Bool
  /-- Mask of the variables whose excitation must persist (gates and control
  wires; the arbiters' decision nodes and the data-path LUTs are exempt and
  covered by `good`, the bundling filters and H_ARB_RESOLVED). -/
  hzM : Nat
  /-- Variables that count as progress for liveness (not the clients). -/
  live : Nat → Bool
  /-- Some client is waiting for the circuit. -/
  waiting : Nat → Bool

namespace Sys
def nx (m : Sys) (s v : Nat) : Bool := (m.nxv s).testBit v
def ex (m : Sys) (s v : Nat) : Bool := m.nx s v != s.testBit v

/-- Excitation mask: all variables at once. -/
def exm (m : Sys) (s : Nat) : Nat := (m.nxv s ^^^ s) % 2 ^ m.V

def can (m : Sys) (s v : Nat) : Bool := decide (v < m.V) && m.ex s v && m.allow (m.exm s) s v

theorem exm_bit (m : Sys) (s v : Nat) : (m.exm s).testBit v = (decide (v < m.V) && m.ex s v) := by
  simp only [exm, Nat.testBit_mod_two_pow, Nat.testBit_xor, ex, nx]

/-- Little-endian bit vector of a list of Booleans (variable 0 first). -/
def bits : List Bool → Nat
  | [] => 0
  | b :: bs => (if b then 1 else 0) + 2 * bits bs

/-- Clear bit `u`. -/
def clr (x u : Nat) : Nat := x ^^^ (x &&& 2 ^ u)
/-- `x` is a sub-mask of `y`. -/
def subM (x y : Nat) : Bool := x &&& y == x

theorem clr_bit (x u v : Nat) (h : u ≠ v) : (clr x u).testBit v = x.testBit v := by
  simp [clr, Nat.testBit_xor, Nat.testBit_and, h]

theorem subM_bit {x y v : Nat} (h : subM x y = true) (hx : x.testBit v = true) :
    y.testBit v = true := by
  simp only [subM, beq_iff_eq] at h
  have := congrArg (fun n => Nat.testBit n v) h
  simp only [Nat.testBit_and, hx, Bool.true_and] at this
  exact this

/-- Reachable from reset (state `0`). -/
inductive Reach (m : Sys) : Nat → Prop
  | init : Reach m 0
  | step {s v} : Reach m s → m.can s v = true → Reach m (m.fire s v)

/-- The per-successor obligation: the successor is in the tree, the step is a
spec step, and every other excited hazard-checked variable is still excited
(read from the successor's stored mask `e'`). -/
def okU (m : Sys) (T : KTree) (s e u : Nat) : Bool :=
  match T.find (m.fire s u) with
  | none => false
  | some e' => m.spec s u && subM (clr (e &&& m.hzM) u) e'

def okSt (m : Sys) (T : KTree) (s e : Nat) : Bool :=
  e == m.exm s &&
  allBelow (fun u => !e.testBit u || !m.allow e s u || okU m T s e u) m.V &&
  (!m.waiting s || anyBelow (fun v => m.live v && e.testBit v && m.allow e s v) m.V) &&
  m.good s

def check (m : Sys) (T : KTree) : Bool := (T.find 0).isSome && T.all (m.okSt T)

/-- The properties a successful check gives in a reachable state. -/
structure Props (m : Sys) (s : Nat) : Prop where
  /-- Every allowed step is a step of the specification automaton. -/
  spec : ∀ u, m.can s u = true → m.spec s u = true
  /-- No hazard: firing `u` never withdraws the excitation of another
  hazard-checked variable. -/
  persist : ∀ u v, m.can s u = true → v < m.V → u ≠ v → m.hzM.testBit v = true →
    m.ex s v = true → m.ex (m.fire s u) v = true
  /-- No stranded token: if a client waits, some circuit/server step is allowed. -/
  live : m.waiting s = true → ∃ v, m.live v = true ∧ m.can s v = true
  /-- The data invariant. -/
  good : m.good s = true

theorem sound {m : Sys} {T : KTree} (hc : m.check T = true) {s} (h : Reach m s) :
    (∃ e, T.find s = some e) ∧ Props m s := by
  simp only [check, Bool.and_eq_true] at hc
  obtain ⟨h0, hall⟩ := hc
  have key : ∀ {s e}, T.find s = some e → e = m.exm s ∧ Props m s ∧
      (∀ u, m.can s u = true → ∃ e', T.find (m.fire s u) = some e') := by
    intro s e hm
    have hok := KTree.all_find hall hm
    simp only [okSt, Bool.and_eq_true, beq_iff_eq] at hok
    obtain ⟨⟨⟨hE, hA⟩, hL⟩, hG⟩ := hok
    subst hE
    have bit : ∀ v, v < m.V → (m.exm s).testBit v = m.ex s v := by
      intro v hv; simp [exm_bit, hv]
    have per : ∀ u, m.can s u = true → okU m T s (m.exm s) u = true := by
      intro u hu
      simp only [can, Bool.and_eq_true, decide_eq_true_eq] at hu
      have := allBelow_spec hA hu.1.1
      simpa [bit u hu.1.1, hu.1.2, hu.2] using this
    refine ⟨rfl, ⟨?_, ?_, ?_, hG⟩, ?_⟩
    · intro u hu
      have := per u hu
      simp only [okU] at this
      split at this
      · simp at this
      · simp only [Bool.and_eq_true] at this; exact this.1
    · intro u v hu hv huv hz hex
      have hp := per u hu
      simp only [okU] at hp
      split at hp
      · simp at hp
      · rename_i e' hf
        simp only [Bool.and_eq_true] at hp
        have hE' := (KTree.all_find hall hf)
        simp only [okSt, Bool.and_eq_true, beq_iff_eq] at hE'
        have he' : e' = m.exm (m.fire s u) := hE'.1.1.1
        subst he'
        have hx : (clr (m.exm s &&& m.hzM) u).testBit v = true := by
          rw [clr_bit _ _ _ huv, Nat.testBit_and, bit v hv, hex, hz]; rfl
        have h1 := subM_bit hp.2 hx
        rw [exm_bit] at h1
        simpa [hv] using h1
    · intro hw
      simp only [hw, Bool.not_true, Bool.false_or] at hL
      obtain ⟨v, hv, hp⟩ := anyBelow_spec hL
      simp only [Bool.and_eq_true] at hp
      refine ⟨v, hp.1.1, ?_⟩
      simp only [can, Bool.and_eq_true, decide_eq_true_eq]
      exact ⟨⟨hv, by rw [← bit v hv]; exact hp.1.2⟩, hp.2⟩
    · intro u hu
      have := per u hu
      simp only [okU] at this
      split at this
      · simp at this
      · rename_i e' hf; exact ⟨e', hf⟩
  obtain ⟨e0, he0⟩ := Option.isSome_iff_exists.1 h0
  induction h with
  | init => exact ⟨⟨e0, he0⟩, (key he0).2.1⟩
  | step _ hc ih =>
    obtain ⟨⟨e, he⟩, _⟩ := ih
    obtain ⟨e', he'⟩ := (key he).2.2 _ hc
    exact ⟨⟨e', he'⟩, (key he').2.1⟩

/-- Replay a run (a list of fired variables) from a state; `none` if some
step is not allowed. -/
def run (m : Sys) : List Nat → Nat → Option Nat
  | [], s => some s
  | v :: vs, s => if m.can s v then run m vs (m.fire s v) else none

theorem run_reach {m : Sys} : ∀ (p : List Nat) {s t}, Reach m s → run m p s = some t → Reach m t
  | [], _, _, h, hr => by simp [run] at hr; exact hr ▸ h
  | v :: vs, s, t, h, hr => by
    simp only [run] at hr
    by_cases hc : m.can s v = true
    · simp only [hc, ite_true] at hr; exact run_reach vs (Reach.step h hc) hr
    · simp [hc] at hr

end Sys

end Formal.Cells.AMergeSys
