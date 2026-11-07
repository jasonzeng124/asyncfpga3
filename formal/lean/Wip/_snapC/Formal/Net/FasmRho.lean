import Formal.Net.FasmDesign.Basic

/-!
# Probe C-11g: the renaming of a bitstream import is a bijection on nets

Generic half (hand-written). `Formal.Net.FasmDesign` (probe C-11f) proves, for a
routed design, `∀ i ∈ insts, i.Sound rho`, for a renaming `rho : Trie` from
physical nets to logical sources. That statement leaves open that `rho` could
send two physical nets to one logical net (a merge). This file gives a
certificate check that pins down exactly where `rho` merges nets:

* `IsRtOut insts k` -- physical net `k` is an output of an instance with no
  logical cell (a route-through or constant LUT/buffer added by nextpnr).
  Those outputs rename to their *source* by `Inst.Sound`, so they share a
  logical net with the net they pass on: such merges are intended.
* `NonRt insts rho k v` -- `rho` sends `k` to the logical net `v` and `k` is
  not a route-through output.
* `LNet insts v` -- `v` is on a pin of some instance's logical cell.

`bij_of_checks`: if four Boolean checks hold (run by `decide +kernel` on the
generated certificates `inv`, `occ`, `mark`), then

1. (injective) `NonRt k v → NonRt k' v → k = k'`;
2. (into) `NonRt k v → LNet v`;
3. (onto) `LNet v → ∃ k, NonRt k v`.

So `k ↦ v` is a bijection from the non-route-through physical nets that `rho`
sends to a logical net, onto the logical nets used by the instances' logical
cells. Every other `rho` entry is either a route-through output or a constant.

The certificates are hints: `inv` (logical net -> physical net), `occ` (logical
net -> index of an instance whose logical cell has it), `mark` (route-through
output net -> index of its instance). Indices are `1000 * chunk + position`.
Nothing is assumed about them: a wrong hint makes a check fail.
-/

namespace Formal.Net.FasmRho
open Formal.Gen Formal.Net.FasmDesign

/-! ## Visiting every entry of a trie -/

/-- `p key value` for every stored entry of `t`, where the subtree's local key
`j` is the global key `a * j + b` (start with `a = 1`, `b = 0`). -/
def kvAll (p : Nat → Src → Bool) : Trie → Nat → Nat → Bool
  | .leaf, _, _ => true
  | .node v l r, a, b =>
    (match v with
     | some x => p b x
     | none => true) && kvAll p l (2 * a) (a + b) && kvAll p r (2 * a) (2 * a + b)

theorem kvAll_sound (p : Nat → Src → Bool) : ∀ (t : Trie) (a b : Nat),
    kvAll p t a b = true → ∀ j x, t.find j = some x → p (a * j + b) x = true := by
  intro t
  induction t with
  | leaf => intro a b _ j x h; simp [Trie.find] at h
  | node v l r ihl ihr =>
    intro a b h j x hj
    simp only [kvAll, Bool.and_eq_true] at h
    obtain ⟨⟨hv, hl⟩, hr⟩ := h
    cases j with
    | zero =>
      simp only [Trie.find] at hj
      subst hj
      simpa using hv
    | succ k =>
      simp only [Trie.find] at hj
      by_cases hk : k % 2 = 0
      · simp only [hk, ite_true] at hj
        have := ihl _ _ hl _ _ hj
        have e : 2 * a * (k / 2) + (a + b) = a * (k + 1) + b := by
          have hk2 : k = 2 * (k / 2) := by omega
          rw [Nat.mul_assoc, ← Nat.mul_left_comm, ← hk2, Nat.mul_succ]; omega
        rwa [e] at this
      · simp only [hk, ite_false] at hj
        have := ihr _ _ hr _ _ hj
        have e : 2 * a * (k / 2) + (2 * a + b) = a * (k + 1) + b := by
          have hk2 : k + 1 = 2 * (k / 2) + 2 := by omega
          rw [hk2, Nat.mul_add, Nat.mul_assoc, Nat.mul_left_comm a 2]; omega
        rwa [e] at this

/-- Assemble a `kvAll` check from checks of the subtrees (the generated files split
a big trie this way, one `decide` per subtree, to bound the kernel's memory). -/
theorem kvAll_node (p : Nat → Src → Bool) (v : Option Src) (l r : Trie) (a b : Nat)
    (hv : (match v with
     | some x => p b x
     | none => true) = true)
    (hl : kvAll p l (2 * a) (a + b) = true) (hr : kvAll p r (2 * a) (2 * a + b) = true) :
    kvAll p (.node v l r) a b = true := by
  simp only [kvAll, hv, hl, hr, Bool.and_self]

theorem kvAll_leaf (p : Nat → Src → Bool) (a b : Nat) : kvAll p .leaf a b = true := rfl

theorem kvAll_sound1 (p : Nat → Src → Bool) (t : Trie) (h : kvAll p t 1 0 = true) :
    ∀ j x, t.find j = some x → p j x = true := by
  intro j x hj
  have := kvAll_sound p t 1 0 h j x hj
  simpa using this

/-! ## The statement -/

def IsRtOut (insts : List Inst) (k : Nat) : Prop :=
  ∃ i ∈ insts, i.log = none ∧ ∃ o ∈ i.outs, i.phys.conn.lookup o.1 = some (.net k)

def NonRt (insts : List Inst) (rho : Trie) (k v : Nat) : Prop :=
  rho.find k = some (.net v) ∧ ¬ IsRtOut insts k

def LNet (insts : List Inst) (v : Nat) : Prop :=
  ∃ i ∈ insts, ∃ l, i.log = some l ∧ ∃ q, (q, Src.net v) ∈ l.conn

/-! ## The checks -/

/-- The instance at index `1000 * c + j` of the chunk list `cs`. -/
def at? (cs : List (List Inst)) (n : Nat) : Option Inst :=
  (cs[n / 1000]?).bind fun c => c[n % 1000]?

/-- Every `mark` entry `k ↦ n` points at an instance without a logical cell that
has `k` on an output pin. -/
def markP (cs : List (List Inst)) (k : Nat) : Src → Bool
  | .net n => match at? cs n with
    | some i => i.log.isNone && i.outs.any (fun o => i.phys.conn.lookup o.1 == some (.net k))
    | none => false
  | .const _ => false

def markOk (cs : List (List Inst)) (mark : Trie) : Bool := kvAll (markP cs) mark 1 0

/-- Every route-through output is marked, and every logical pin net has an `inv` entry. -/
def coverOk (mark inv : Trie) (insts : List Inst) : Bool :=
  insts.all fun i => match i.log with
    | none => i.outs.all fun o => match i.phys.conn.lookup o.1 with
      | some (.net k) => (mark.find k).isSome
      | _ => true
    | some l => l.conn.all fun x => match x.2 with
      | .net v => (inv.find v).isSome
      | .const _ => true

theorem coverOk_flatten (mark inv : Trie) (cs : List (List Inst))
    (h : cs.all (coverOk mark inv) = true) : coverOk mark inv cs.flatten = true := by
  unfold coverOk at *
  simp only [List.all_eq_true, List.mem_flatten] at *
  intro i ⟨c, hc, hi⟩
  exact h c hc i hi

/-- Every `rho` entry to a logical net is marked, or `inv` sends that net back to it. -/
def keysP (inv mark : Trie) (k : Nat) : Src → Bool
  | .net v => (mark.find k).isSome || inv.find v == some (.net k)
  | .const _ => true

def keysOk (rho inv mark : Trie) : Bool := kvAll (keysP inv mark) rho 1 0

/-- Every `inv` entry `v ↦ k`: `rho` sends `k` to `v`, `k` is not marked, and
`occ` names an instance whose logical cell has `v` on a pin. -/
def invP (cs : List (List Inst)) (rho mark occ : Trie) (v : Nat) : Src → Bool
  | .net k => rho.find k == some (.net v) && (mark.find k).isNone &&
    (match occ.find v with
     | some (.net n) => match at? cs n with
       | some i => match i.log with
         | some l => l.conn.any (fun y => y.2 == .net v)
         | none => false
       | none => false
     | _ => false)
  | .const _ => false

def invOk (cs : List (List Inst)) (rho inv mark occ : Trie) : Bool := kvAll (invP cs rho mark occ) inv 1 0

/-! ## Soundness -/

theorem at?_mem {cs : List (List Inst)} {n : Nat} {i : Inst} (h : at? cs n = some i) :
    i ∈ cs.flatten := by
  unfold at? at h
  cases hc : cs[n / 1000]? with
  | none => simp [hc] at h
  | some c =>
    simp only [hc, Option.bind_some] at h
    have hcm : c ∈ cs := List.mem_of_getElem? hc
    have him : i ∈ c := List.mem_of_getElem? h
    exact List.mem_flatten.2 ⟨c, hcm, him⟩

theorem mark_sound (cs : List (List Inst)) (mark : Trie) (h : markOk cs mark = true) :
    ∀ k, (mark.find k).isSome → IsRtOut cs.flatten k := by
  intro k hk
  obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 hk
  have := kvAll_sound1 _ mark h k x hx
  unfold markP at this
  cases x with
  | const b => simp at this
  | net n =>
    simp only at this
    split at this
    · rename_i i hi
      simp only [Bool.and_eq_true, Option.isNone_iff_eq_none, List.any_eq_true, beq_iff_eq] at this
      obtain ⟨hl, o, ho, hk⟩ := this
      exact ⟨i, at?_mem hi, hl, o, ho, hk⟩
    · simp at this

theorem cover_rt (mark inv : Trie) (insts : List Inst) (h : coverOk mark inv insts = true) :
    ∀ k, IsRtOut insts k → (mark.find k).isSome := by
  intro k ⟨i, hi, hl, o, ho, hk⟩
  simp only [coverOk, List.all_eq_true] at h
  have h1 := h i hi
  rw [hl] at h1
  simp only [List.all_eq_true] at h1
  have h2 := h1 o ho
  rw [hk] at h2
  exact h2

theorem cover_inv (mark inv : Trie) (insts : List Inst) (h : coverOk mark inv insts = true) :
    ∀ v, LNet insts v → (inv.find v).isSome := by
  intro v ⟨i, hi, l, hl, q, hq⟩
  simp only [coverOk, List.all_eq_true] at h
  have h1 := h i hi
  rw [hl] at h1
  simp only [List.all_eq_true] at h1
  exact h1 _ hq

/-- **The renaming is a bijection on nets, outside route-throughs.** -/
theorem bij_of_checks (cs : List (List Inst)) (rho inv mark occ : Trie)
    (hm : markOk cs mark = true) (hc : coverOk mark inv cs.flatten = true)
    (hk : keysOk rho inv mark = true) (hi : invOk cs rho inv mark occ = true) :
    (∀ k k' v, NonRt cs.flatten rho k v → NonRt cs.flatten rho k' v → k = k') ∧
    (∀ k v, NonRt cs.flatten rho k v → LNet cs.flatten v) ∧
    (∀ v, LNet cs.flatten v → ∃ k, NonRt cs.flatten rho k v) := by
  -- an unmarked key to a logical net is `inv`'s preimage
  have back : ∀ k v, NonRt cs.flatten rho k v → inv.find v = some (.net k) := by
    intro k v ⟨hr, hn⟩
    have h1 := kvAll_sound1 _ rho hk k _ hr
    unfold keysP at h1
    simp only [Bool.or_eq_true, beq_iff_eq] at h1
    rcases h1 with h1 | h1
    · exact absurd (mark_sound cs mark hm k h1) hn
    · exact h1
  have invE : ∀ v x, inv.find v = some x → ∃ k, x = .net k ∧ rho.find k = some (.net v) ∧
      mark.find k = none ∧ LNet cs.flatten v := by
    intro v x hx
    have h1 := kvAll_sound1 _ inv hi v x hx
    unfold invP at h1
    cases x with
    | const b => simp at h1
    | net k =>
      simp only [Bool.and_eq_true, beq_iff_eq, Option.isNone_iff_eq_none] at h1
      obtain ⟨⟨hr, hmk⟩, ho⟩ := h1
      refine ⟨k, rfl, hr, hmk, ?_⟩
      split at ho
      · rename_i n _
        split at ho
        · rename_i i hat
          split at ho
          · rename_i l hl
            simp only [List.any_eq_true, beq_iff_eq] at ho
            obtain ⟨y, hy, hyv⟩ := ho
            exact ⟨i, at?_mem hat, l, hl, y.1, by rw [← hyv]; exact hy⟩
          · simp at ho
        · simp at ho
      · simp at ho
  refine ⟨?_, ?_, ?_⟩
  · intro k k' v h h'
    have e := (back k v h).symm.trans (back k' v h')
    simpa using e
  · intro k v h
    obtain ⟨_, _, _, _, hl⟩ := invE v _ (back k v h)
    exact hl
  · intro v hv
    obtain ⟨x, hx⟩ := Option.isSome_iff_exists.1 (cover_inv mark inv _ hc v hv)
    obtain ⟨k, rfl, hr, hmk, _⟩ := invE v _ hx
    refine ⟨k, hr, fun hrt => ?_⟩
    have := cover_rt mark inv _ hc k hrt
    rw [hmk] at this
    simp at this

end Formal.Net.FasmRho
