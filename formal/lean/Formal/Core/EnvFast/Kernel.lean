import Formal.Core.EnvFast

/-!
# Formal.Core.EnvFast.Kernel — the checker in kernel-friendly form

Measured (see `formal/notes/A-envfast.md`): in `decide +kernel`, every `Nat`
operation reached through the instance chain (`HAnd.hAnd` → `AndOp.and` →
`Nat.land`, `==` → `instBEqOfDecidableEq` → `Nat.decEq` …) costs several
kernel steps, and every structurally recursive function (`List.foldl`,
`List.map`, …) is unfolded through `brecOn`. On bd_link W = 2 a 5-pin address
computation `addrOf (pinVec s pins)` cost 2.3 ms per state; the same with raw
`Nat.land`/`Nat.shiftRight`/`Nat.add` and a direct `List.rec` costs 0.17 ms.

So this file re-implements the hot path of `EnvFast.check` with:
* raw GMP-accelerated `Nat` functions (`Nat.land`, `Nat.shiftRight`,
  `Nat.beq`, `Nat.blt`, `Nat.add`, `Nat.sub`, `Nat.pow`, `Nat.mod`, `Nat.mul`),
* `cond` instead of `if`,
* folds / `all` / BST search written directly with the recursors (`kfoldl`,
  `kall`, `kcontains`, `kinsert`),
and proves each piece equal to the `EnvFast` (hence `Env`) function it replaces.
The soundness theorem `kcheck_sound` is stated against `Env.Reach`/`Env.stepOK`
directly. The certificate may be split into chunks, each checked by its own
`decide +kernel` (`kchunk`), so that kernel memory is bounded by the chunk size
(the kernel's caches are per declaration).

These definitions use recursors directly, so they are `noncomputable` (no
compiled code); they are only ever evaluated by the kernel.
-/

namespace Formal.Core.EnvFast

set_option linter.unusedSimpArgs false

open Formal.Core.LutTree Formal.Core.LutCells Formal.Core.LutAudit Formal.Core.Env

/-! ## 1. Primitives -/

/-- `Nat.testBit` with raw operations. -/
def kb (s i : Nat) : Bool := Nat.beq (Nat.land (Nat.shiftRight s i) 1) 1

theorem kb_eq (s i : Nat) : kb s i = bit s i := by
  have h1 : Nat.land (Nat.shiftRight s i) 1 = (s >>> i) % 2 := Nat.and_one_is_mod _
  have h2 : (1 &&& (s >>> i)) = (s >>> i) % 2 := by
    rw [Nat.and_comm]; exact Nat.and_one_is_mod _
  simp only [kb, bit, Nat.testBit, h1, h2]
  rcases Nat.mod_two_eq_zero_or_one (s >>> i) with h | h <;> simp [h] <;> rfl

theorem beq_eq_nat (a b : Nat) : Nat.beq a b = (a == b) := by
  cases h : Nat.beq a b
  · have : a ≠ b := Nat.ne_of_beq_eq_false h
    simp [this]
  · have : a = b := Nat.eq_of_beq_eq_true h
    simp [this]

noncomputable def kfoldl {α β : Type} (f : β → α → β) (l : List α) (b : β) : β :=
  List.rec (motive := fun _ => β → β) (fun b => b) (fun a _ ih b => ih (f b a)) l b

theorem kfoldl_eq {α β : Type} (f : β → α → β) : ∀ (l : List α) (b : β),
    kfoldl f l b = l.foldl f b
  | [], _ => rfl
  | a :: l, b => kfoldl_eq f l (f b a)

noncomputable def kall {α : Type} (p : α → Bool) (l : List α) : Bool :=
  List.rec (motive := fun _ => Bool) true (fun a _ ih => p a && ih) l

theorem kall_eq {α : Type} (p : α → Bool) : ∀ (l : List α), kall p l = l.all p
  | [] => rfl
  | a :: l => by
      show (p a && kall p l) = (p a && l.all p)
      rw [kall_eq p l]

/-- Two environment lists agree: same signals, extensionally equal guards. -/
inductive EnvAgree : List (Nat × (Nat → Bool)) → List (Nat × (Nat → Bool)) → Prop
  | nil : EnvAgree [] []
  | cons {a b : Nat × (Nat → Bool)} {l1 l2 : List (Nat × (Nat → Bool))} :
      a.1 = b.1 → (∀ s, a.2 s = b.2 s) → EnvAgree l1 l2 → EnvAgree (a :: l1) (b :: l2)

theorem foldl_envAgree {γ : Type} {f g : γ → Nat × (Nat → Bool) → γ}
    (hfg : ∀ a b : Nat × (Nat → Bool), a.1 = b.1 → (∀ s, a.2 s = b.2 s) → ∀ c, f c a = g c b) :
    ∀ {l1 l2 : List (Nat × (Nat → Bool))}, EnvAgree l1 l2 → ∀ c, l1.foldl f c = l2.foldl g c
  | [], [], .nil, _ => rfl
  | _ :: _, _ :: _, .cons h1 h2 hs, c => by
      simp only [List.foldl_cons]
      rw [hfg _ _ h1 h2 c]
      exact foldl_envAgree hfg hs _

def ksetBit (m i : Nat) : Nat := cond (kb m i) m (Nat.add m (Nat.pow 2 i))
def kclrBit (m i : Nat) : Nat := cond (kb m i) (Nat.sub m (Nat.pow 2 i)) m

theorem ksetBit_eq (m i : Nat) : ksetBit m i = setBit m i := by
  simp only [ksetBit, setBit, kb_eq]; cases bit m i <;> rfl

theorem kclrBit_eq (m i : Nat) : kclrBit m i = clrBit m i := by
  simp only [kclrBit, clrBit, kb_eq]; cases bit m i <;> rfl

/-- Bool inequality without `BEq`. -/
def kne (a b : Bool) : Bool := cond a (!b) b

theorem kne_eq (a b : Bool) : kne a b = (a != b) := by cases a <;> cases b <;> rfl

/-- Bool equality without `BEq`. -/
def keq (a b : Bool) : Bool := cond a b (!b)

theorem keq_eq (a b : Bool) : keq a b = (a == b) := by cases a <;> cases b <;> rfl

/-! ## 2. Compiled model -/

/-- A compiled model: the gates with their tables, the environment guards
re-written in kernel-friendly form (`kb` instead of `bit`), the rest copied. -/
structure CModel where
  n : Nat
  settle : Bool
  gates : List CGate
  env : List (Nat × (Nat → Bool))
  prio : List (Nat × Nat)

structure KCompiled (M : Model) (C : CModel) : Prop where
  n : C.n = M.n
  settle : C.settle = M.settle
  comp : Compiled M C.gates
  env : EnvAgree C.env M.env
  prio : C.prio = M.prio

/-! ## 3. Excitation and enable masks -/

/-- `addrOf (pinVec s pins)` with raw operations. -/
noncomputable def kaddr (s : Nat) (pins : List Nat) : Nat :=
  kfoldl (fun a p => Nat.add (Nat.add a a) (Nat.land (Nat.shiftRight s p) 1)) pins 0

theorem land_one_eq (s p : Nat) : Nat.land (Nat.shiftRight s p) 1 = if bit s p then 1 else 0 := by
  rw [← kb_eq]
  have h1 : Nat.land (Nat.shiftRight s p) 1 = (s >>> p) % 2 := Nat.and_one_is_mod _
  simp only [kb, h1]
  rcases Nat.mod_two_eq_zero_or_one (s >>> p) with h | h <;> simp [h]

theorem kaddr_aux (s : Nat) : ∀ (pins : List Nat) (a : Nat),
    pins.foldl (fun a p => Nat.add (Nat.add a a) (Nat.land (Nat.shiftRight s p) 1)) a =
      a * 2 ^ pins.length + addrOf (pinVec s pins)
  | [], a => by simp [pinVec, addrOf]
  | p :: ps, a => by
      simp only [List.foldl_cons]
      rw [kaddr_aux s ps]
      simp only [pinVec, List.map_cons, addrOf, List.length_cons, List.length_map, land_one_eq,
        Nat.add_eq, Nat.pow_succ]
      cases bit s p
      · simp only [Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.zero_add]
        simp only [Nat.mul_two, Nat.add_assoc, Nat.add_mul, Nat.mul_add, Nat.one_mul]
      · simp only [↓reduceIte]
        simp only [Nat.mul_two, Nat.add_assoc, Nat.add_mul, Nat.mul_add, Nat.one_mul]

theorem kaddr_eq (s : Nat) (pins : List Nat) : kaddr s pins = addrOf (pinVec s pins) := by
  rw [kaddr, kfoldl_eq, kaddr_aux]; simp

noncomputable def kval (s : Nat) : CGate → Bool
  | .lut _ _ _ pins tt _ => kb tt (kaddr s pins)
  | .wire _ src => kb s src

theorem kval_eq (s : Nat) (c : CGate) : kval s c = cval s c := by
  cases c <;> simp [kval, cval, kb_eq, kaddr_eq, bit]

noncomputable def kexc (C : CModel) (s : Nat) : Nat :=
  kfoldl (fun m e => cond (e.2 s) (ksetBit m e.1) m) C.env
    (kfoldl (fun m c => cond (kne (kval s c) (kb s c.out)) (ksetBit m c.out) m) C.gates 0)

theorem cond_eq_ite {α : Type} (b : Bool) (x y : α) : cond b x y = if b then x else y := by
  cases b <;> rfl

theorem kexc_eq {M : Model} {C : CModel} (hc : KCompiled M C) (s : Nat) :
    kexc C s = excMask M s := by
  rw [← excMaskF_eq hc.comp]
  unfold kexc excMaskF
  rw [kfoldl_eq, kfoldl_eq]
  have hg : C.gates.foldl (fun m c => cond (kne (kval s c) (kb s c.out)) (ksetBit m c.out) m) 0 =
      C.gates.foldl (fun m c => if (cval s c != bit s c.out) then setBit m c.out else m) 0 := by
    apply foldl_congr_mem
    intro c _ m
    rw [cond_eq_ite, kne_eq, kval_eq, kb_eq, ksetBit_eq]
  rw [hg]
  apply foldl_envAgree _ hc.env
  intro a b h1 h2 m
  rw [cond_eq_ite, h2 s, h1, ksetBit_eq]

noncomputable def kenOf (C : CModel) (ex : Nat) : Nat :=
  kfoldl (fun m p => cond (kb ex p.1 && !Nat.beq p.1 p.2) (kclrBit m p.2) m) C.prio ex

theorem kenOf_eq {M : Model} {C : CModel} (hc : KCompiled M C) (ex : Nat) :
    kenOf C ex = enOf M ex := by
  unfold kenOf enOf
  rw [kfoldl_eq, hc.prio]
  apply foldl_congr_mem
  intro p _ m
  rw [cond_eq_ite, kb_eq, beq_eq_nat, kclrBit_eq]
  rfl

/-! ## 4. Successor state -/

def koff (C : CModel) (gi j : Nat) : Nat := Nat.mul C.n (Nat.add (Nat.add 1 (Nat.mul 6 gi)) j)
def kslot (C : CModel) (s gi j : Nat) : Nat := Nat.mod (Nat.shiftRight s (koff C gi j)) (Nat.pow 2 C.n)

theorem kslot_eq {M : Model} {C : CModel} (hc : KCompiled M C) (s gi j : Nat) :
    kslot C s gi j = slot M s gi j := by
  simp only [kslot, koff, slot, off, hc.n]; rfl

def knewPend (C : CModel) (e0 e1 s t gi j p : Nat) : Nat :=
  cond C.settle
    (cond (Nat.beq p t) (Nat.land (kclrBit e0 t) e1)
      (cond (kb (kslot C s gi j) t) (Nat.land (kclrBit (kslot C s gi j) t) e1) 0))
    (cond (Nat.beq p t || !Nat.beq (kslot C s gi j) 0) (Nat.sub (Nat.pow 2 C.n) 1) 0)

theorem knewPend_eq {M : Model} {C : CModel} (hc : KCompiled M C) (e0 e1 s t gi j p : Nat) :
    knewPend C e0 e1 s t gi j p = newPendF M e0 e1 s t gi j p := by
  simp only [knewPend, newPendF, kslot_eq hc, hc.settle, hc.n, kclrBit_eq, kb_eq, beq_eq_nat]
  cases M.settle <;> simp only [cond_eq_ite] <;> rfl

noncomputable def kpinSlots (C : CModel) (e0 e1 s t gi : Nat) (pins : List Nat) : Nat :=
  kfoldl (fun acc pj => Nat.add acc (Nat.shiftLeft (knewPend C e0 e1 s t gi pj.2 pj.1)
    (koff C gi pj.2))) (idxd pins 0) 0

noncomputable def kslotsOf (C : CModel) (e0 e1 s t : Nat) : Nat :=
  kfoldl (fun acc ggi =>
    match ggi.1 with
    | .lut q _ _ pins _ _ => cond (Nat.beq q t) acc (Nat.add acc (kpinSlots C e0 e1 s t ggi.2 pins))
    | .wire _ _ => acc) (idxd C.gates 0) 0

noncomputable def kpost (C : CModel) (e0 e1 s t : Nat) : Nat :=
  Nat.add (Nat.mod (Nat.xor s (Nat.pow 2 t)) (Nat.pow 2 C.n)) (kslotsOf C e0 e1 s t)

theorem kpinSlots_eq {M : Model} {C : CModel} (hc : KCompiled M C) (e0 e1 s t gi : Nat)
    (pins : List Nat) : kpinSlots C e0 e1 s t gi pins = pinSlotsF M e0 e1 s t gi pins := by
  unfold kpinSlots pinSlotsF
  rw [kfoldl_eq]
  apply foldl_congr_mem
  intro pj _ acc
  rw [knewPend_eq hc]
  simp only [koff, off, hc.n]
  rfl

theorem kslotsOf_eq {M : Model} {C : CModel} (hc : KCompiled M C) (e0 e1 s t : Nat) :
    kslotsOf C e0 e1 s t = slotsOfF M e0 e1 s t := by
  unfold kslotsOf slotsOfF
  rw [kfoldl_eq, ← hc.comp.gates, idxd_map, List.foldl_map]
  apply foldl_congr_mem
  intro ggi _ acc
  obtain ⟨c, i⟩ := ggi
  cases c with
  | lut q L o pins tt hz =>
      simp only [CGate.g, cond_eq_ite, beq_eq_nat, kpinSlots_eq hc]; rfl
  | wire q src => rfl

theorem kpost_eq {M : Model} {C : CModel} (hc : KCompiled M C) (e0 e1 s t : Nat) :
    kpost C e0 e1 s t = postF M e0 e1 s t := by
  simp only [kpost, postF, kslotsOf_eq hc, hc.n]; rfl

/-! ## 5. Step checks -/

noncomputable def kisEnv (C : CModel) (i : Nat) : Bool := kall (fun e => !Nat.beq e.1 i) C.env

theorem kisEnv_eq {M : Model} {C : CModel} (hc : KCompiled M C) (i : Nat) :
    kisEnv C i = !isEnv M i := by
  unfold kisEnv isEnv
  rw [kall_eq]
  have := hc.env
  clear hc
  generalize C.env = l1 at this ⊢
  generalize M.env = l2 at this ⊢
  induction this with
  | nil => rfl
  | cons h1 _ _ ih =>
      simp only [beq_eq_nat] at ih
      simp only [List.all_cons, List.any_cons, ih, beq_eq_nat, h1, Bool.not_or]

noncomputable def krange (n : Nat) : List Nat := List.range n

noncomputable def kpersist (C : CModel) (x0 x1 t : Nat) : Bool :=
  let et := kisEnv C t
  kall (fun u => Nat.beq u t || !kb x0 u || kb x1 u || (!et && !kisEnv C u)) (List.range C.n)

theorem kpersist_eq {M : Model} {C : CModel} (hc : KCompiled M C) (x0 x1 s t : Nat) :
    kpersist C x0 x1 t = persistOKF M x0 x1 s t := by
  unfold kpersist persistOKF
  rw [kall_eq, hc.n]
  apply all_congr_mem
  intro u _
  simp only [kisEnv_eq hc, kb_eq, beq_eq_nat, Bool.not_not]

/-- The packed old pin vector (`addrOf (oldVec …)`). -/
noncomputable def koldAddr (C : CModel) (s t gi : Nat) (pins : List Nat) : Nat :=
  kfoldl (fun a pj => Nat.add (Nat.add a a)
      (cond (kne (kb (Nat.xor s (Nat.pow 2 t)) pj.1) (Nat.beq pj.1 t || kb (kslot C s gi pj.2) t)) 1 0))
    (idxd pins 0) 0

theorem kold_aux {M : Model} {C : CModel} (hc : KCompiled M C) (s t gi : Nat) :
    ∀ (l : List (Nat × Nat)) (a : Nat),
    l.foldl (fun a pj => Nat.add (Nat.add a a)
      (cond (kne (kb (Nat.xor s (Nat.pow 2 t)) pj.1) (Nat.beq pj.1 t || kb (kslot C s gi pj.2) t)) 1 0)) a =
      a * 2 ^ l.length + addrOf (l.map fun pj => bit (s ^^^ 2 ^ t) pj.1 ^^ inflight M s t gi pj.2 pj.1)
  | [], a => by simp [addrOf]
  | pj :: l, a => by
      simp only [List.foldl_cons]
      rw [kold_aux hc s t gi l]
      have hb : kne (kb (Nat.xor s (Nat.pow 2 t)) pj.1) (Nat.beq pj.1 t || kb (kslot C s gi pj.2) t) =
          (bit (s ^^^ 2 ^ t) pj.1 ^^ inflight M s t gi pj.2 pj.1) := by
        rw [kne_eq, kb_eq, beq_eq_nat, kslot_eq hc, kb_eq, inflight]
        have hx : Nat.xor s (Nat.pow 2 t) = s ^^^ 2 ^ t := rfl
        rw [hx]
      rw [hb]
      simp only [List.map_cons, addrOf, List.length_cons, List.length_map, Nat.add_eq, Nat.pow_succ]
      cases (bit (s ^^^ 2 ^ t) pj.1 ^^ inflight M s t gi pj.2 pj.1)
      · simp only [Bool.cond_false, Bool.false_eq_true, ↓reduceIte, Nat.add_zero, Nat.zero_add]
        simp only [Nat.mul_two, Nat.add_assoc, Nat.add_mul, Nat.mul_add, Nat.one_mul]
      · simp only [Bool.cond_true, ↓reduceIte]
        simp only [Nat.mul_two, Nat.add_assoc, Nat.add_mul, Nat.mul_add, Nat.one_mul]

theorem koldAddr_eq {M : Model} {C : CModel} (hc : KCompiled M C) (s t gi : Nat) (pins : List Nat) :
    koldAddr C s t gi pins = addrOf (oldVec M s t gi pins) := by
  rw [koldAddr, kfoldl_eq, kold_aux hc]; simp [oldVec]

noncomputable def klutOK (C : CModel) (s t : Nat) (c : CGate) (gi : Nat) : Bool :=
  match c with
  | .lut q _ _ pins tt hz =>
      Nat.beq q t ||
        (let a := koldAddr C s t gi pins
         let b := kaddr (Nat.xor s (Nat.pow 2 t)) pins
         let v := kb (Nat.xor s (Nat.pow 2 t)) q
         kb hz (Nat.add (Nat.mul a (Nat.pow 2 pins.length)) b) &&
           !(kne (kb tt a) v && !kne (kb tt b) v))
  | .wire _ _ => true

theorem klutOK_eq {M : Model} {C : CModel} (hc : KCompiled M C) (s t : Nat) (c : CGate) (gi : Nat) :
    klutOK C s t c gi = lutOKF M s t c gi := by
  cases c with
  | lut q L o pins tt hz =>
      simp only [klutOK, lutOKF, koldAddr_eq hc, kaddr_eq, kb_eq, kne_eq, beq_eq_nat]
      have hx : Nat.xor s (Nat.pow 2 t) = s ^^^ 2 ^ t := rfl
      have hm : Nat.add (Nat.mul (addrOf (oldVec M s t gi pins)) (Nat.pow 2 pins.length))
          (addrOf (pinVec (s ^^^ 2 ^ t) pins)) =
          addrOf (oldVec M s t gi pins) * 2 ^ pins.length + addrOf (pinVec (s ^^^ 2 ^ t) pins) := rfl
      rw [hx, hm]
      cases (bit (s ^^^ 2 ^ t) q) <;> simp [bit]
  | wire q src => rfl

noncomputable def kstepOK (C : CModel) (x0 x1 s t : Nat) : Bool :=
  kpersist C x0 x1 t && kall (fun ci => klutOK C s t ci.1 ci.2) (idxd C.gates 0)

theorem kstepOK_eq {M : Model} {C : CModel} (hc : KCompiled M C) (x0 x1 s t : Nat) :
    kstepOK C x0 x1 s t = stepOKF M C.gates x0 x1 s t := by
  unfold kstepOK stepOKF
  rw [kpersist_eq hc x0 x1 s t, kall_eq]
  congr 1
  apply all_congr_mem
  intro ci _
  exact klutOK_eq hc s t ci.1 ci.2

/-! ## 6. Certificate tree -/

noncomputable def kcontains (T : Tree) (x : Nat) : Bool :=
  Tree.rec (motive := fun _ => Bool) false
    (fun _ k _ il ir => cond (Nat.beq x k) true (cond (Nat.blt x k) il ir)) T

theorem kcontains_eq : ∀ (T : Tree) (x : Nat), kcontains T x = T.contains x
  | .leaf, _ => rfl
  | .node l k r, x => by
      show cond (Nat.beq x k) true (cond (Nat.blt x k) (kcontains l x) (kcontains r x)) = _
      rw [kcontains_eq l x, kcontains_eq r x, beq_eq_nat]
      simp only [Tree.contains, cond_eq_ite]

noncomputable def kinsert (T : Tree) (x : Nat) : Tree :=
  Tree.rec (motive := fun _ => Tree) (.node .leaf x .leaf)
    (fun l k r il ir => cond (Nat.beq x k) (.node l k r) (cond (Nat.blt x k) (.node il k r) (.node l k ir))) T

theorem kinsert_eq : ∀ (T : Tree) (x : Nat), kinsert T x = T.insert x
  | .leaf, _ => rfl
  | .node l k r, x => by
      show cond (Nat.beq x k) (Tree.node l k r)
        (cond (Nat.blt x k) (Tree.node (kinsert l x) k r) (Tree.node l k (kinsert r x))) = _
      rw [kinsert_eq l x, kinsert_eq r x, beq_eq_nat]
      simp only [Tree.insert, cond_eq_ite]

noncomputable def kmkTree (cert : List Nat) : Tree := kfoldl kinsert cert .leaf

theorem kmkTree_eq (cert : List Nat) : kmkTree cert = mkTree cert := by
  unfold kmkTree mkTree
  rw [kfoldl_eq]
  have : kinsert = Tree.insert := funext fun T => funext fun x => kinsert_eq T x
  rw [this]

/-! ## 7. The chunked checker and its soundness -/

/-- Per-state check (kernel form of `EnvFast.stateOK`). -/
noncomputable def kstateOK (C : CModel) (T : Tree) (s : Nat) : Bool :=
  let x0 := kexc C s
  let e0 := kenOf C x0
  kall (fun t => !kb e0 t ||
    (let x1 := kexc C (Nat.xor s (Nat.pow 2 t))
     kcontains T (kpost C e0 (kenOf C x1) s t) && kstepOK C x0 x1 s t)) (List.range C.n)

theorem kstateOK_eq {M : Model} {C : CModel} (hc : KCompiled M C) (T : Tree) (s : Nat) :
    kstateOK C T s = stateOK M C.gates T s := by
  unfold kstateOK stateOK
  rw [kall_eq, hc.n]
  apply all_congr_mem
  intro t _
  have hx : Nat.xor s (Nat.pow 2 t) = s ^^^ 2 ^ t := rfl
  simp only [hx, kexc_eq hc, kenOf_eq hc, kb_eq, kcontains_eq, kpost_eq hc, kstepOK_eq hc,
    ← excMaskF_eq hc.comp]

/-- Fast liveness (kernel form). -/
noncomputable def klive (C : CModel) (s : Nat) : Bool := !Nat.beq (kenOf C (kexc C s)) 0

theorem klive_eq {M : Model} {C : CModel} (hc : KCompiled M C) (s : Nat) : klive C s = live M s := by
  simp only [klive, live, kexc_eq hc, kenOf_eq hc, beq_eq_nat, enMask_eq_enOf]
  rfl

/-- One chunk of the certificate: every state in `chunk` satisfies `Q'` and
`kstateOK` against the tree of the WHOLE certificate. -/
noncomputable def kchunk (C : CModel) (Q' : Nat → Bool) (T : Tree) (chunk : List Nat) : Bool :=
  kall (fun s => Q' s && kstateOK C T s) chunk

/-- The initial states are in the certificate. -/
noncomputable def kinit (M : Model) (T : Tree) : Bool := kall (kcontains T) M.inits

/-- **Soundness of the chunked kernel checker** (proved once, for every model).
`cert` is the list of chunks; `T = kmkTree cert.flatten` is computed in each
chunk's kernel run (any insertion order is sound). -/
theorem kcheck_sound {M : Model} {C : CModel} {Q Q' : Nat → Bool} {cert : List (List Nat)}
    (hc : KCompiled M C) (hQ : ∀ s, Q' s = Q s)
    (hinit : kinit M (kmkTree cert.flatten) = true)
    (hch : ∀ c ∈ cert, kchunk C Q' (kmkTree cert.flatten) c = true) :
    ∀ s, Reach M s → s ∈ cert.flatten ∧ Q s = true ∧
      ∀ p ∈ succs M s, stepOK M s p.1 = true := by
  apply check_sound hc.comp hQ
  simp only [check, Bool.and_eq_true, List.all_eq_true]
  rw [kmkTree_eq] at hinit hch
  refine ⟨?_, ?_⟩
  · intro x hx
    simp only [kinit, kall_eq, List.all_eq_true] at hinit
    rw [← kcontains_eq]; exact hinit x hx
  · intro s hs
    obtain ⟨c, hc', hsc⟩ := List.mem_flatten.1 hs
    have := hch c hc'
    simp only [kchunk, kall_eq, List.all_eq_true, Bool.and_eq_true] at this
    obtain ⟨h1, h2⟩ := this s hsc
    exact ⟨h1, (kstateOK_eq hc _ s) ▸ h2⟩

theorem kcheck_Sound {M : Model} {C : CModel} {Q Q' : Nat → Bool} {cert : List (List Nat)}
    (hc : KCompiled M C) (hQ : ∀ s, Q' s = Q s)
    (hinit : kinit M (kmkTree cert.flatten) = true)
    (hch : ∀ c ∈ cert, kchunk C Q' (kmkTree cert.flatten) c = true) : Sound M Q :=
  fun s hs => let r := kcheck_sound hc hQ hinit hch s hs; ⟨r.2.1, r.2.2⟩

end Formal.Core.EnvFast
