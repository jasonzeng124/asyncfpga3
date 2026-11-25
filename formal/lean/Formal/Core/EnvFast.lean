import Formal.Core.Env

/-!
# Formal.Core.EnvFast — a scalable, proved-once checker for `Env` certificates

Shard A. Notes: `formal/notes/A-envfast.md`.

`Formal.Core.Env` states its results as `Sound M Q` and proves them by
`decide +kernel` on `certify M Q (reachTree M fuel)`. That run makes the kernel
(a) do the reachability search itself, and (b) evaluate, on every reachable
transition and for every LUT, `LutAudit.classify` (a Kleene mux-tree evaluation
over every vertex of the transition cube, on `List Bool` / `List K3`), plus
`outB` on lists. Its memory grows with total work: bd_link with a W = 2 latch
pair (1048 states) went past 6 GB.

This file keeps `Env`'s semantics as the specification (`Env.Reach`,
`Env.succs`, `Env.stepOK`, `Env.Sound`, unchanged and imported) and gives a
second, cheap evaluation of the same functions, proved equal to them once:

* **LUT tables.** Each LUT output is compiled to two Nats: `tt` (bit `addrOf w`
  = `outB L o w`) and `hz` (bit `addrOf a * 2^k + addrOf b` =
  `okCls (classify L o a b)`). A table is untrusted data: `ttOK`/`hzOK` check it
  against `outB`/`classify` on every vector of the right length, once per LUT
  output (`EnvFast/Tables.lean`). A lookup is `Nat.testBit`, which the kernel
  evaluates with GMP (`1 &&& (m >>> n)`).
* **Shared masks.** The excitation / enable masks of a state and of each
  successor are computed once per (state, transition) and passed down
  (`postF`, `persistOKF`) instead of being recomputed per in-flight slot.
* **External certificate.** The reachable set is untrusted data (`cert : List
  Nat`, computed outside the kernel by `formal/tools-A/envfast/Gen.lean`); the
  kernel only checks it. It is loaded into a BST (`mkTree`, insertion order
  chosen by the generator so the tree is balanced; the order affects speed only).

The state encoding is `Env`'s own (one `Nat`: signal bits, then the in-flight
`pend` records), so there is nothing to translate on states; the equivalence
theorems are about the evaluation: `cval_eq` (table lookup = `Gate.val`,
i.e. decode ∘ encode of the pin vector through `addrOf`), `excMaskF_eq`,
`enMaskF_eq`, `postF_eq`, `succsF_eq` (the fast successor function IS
`Env.succs`), `lutOKF_eq`, `stepOKF_eq`.

Soundness, proved once for every model: `check_sound` — if `check M cg Q' cert
= true`, the compiled gates `cg` are valid for `M`, and `Q'` agrees with `Q`,
then every `Env.Reach`-able state is in `cert`, satisfies `Q`, and every one of
its transitions passes `Env.stepOK` (hazard-free MICs at every LUT, persistence);
`check_Sound` packages this as `Env.Sound M Q`. No new semantics is trusted:
only `Env`'s definitions and this file's proofs.
-/

namespace Formal.Core.EnvFast

open Formal.Core.LutTree Formal.Core.LutCells Formal.Core.LutAudit Formal.Core.Env

/-! ## 1. Compiled gates and their validity -/

/-- A gate with its LUT tables. -/
inductive CGate where
  | lut (out : Nat) (L : LutInst) (o : OutSel) (pins : List Nat) (tt hz : Nat)
  | wire (out src : Nat)

def CGate.g : CGate → Gate
  | .lut q L o pins _ _ => .lut q L o pins
  | .wire q src => .wire q src

/-- Truth-table check: bit `addrOf w` of `tt` is `outB L o w`, for every `w` of
length `k`. -/
def ttOK (L : LutInst) (o : OutSel) (k tt : Nat) : Bool :=
  (vecs k).all fun w => outB L o w == tt.testBit (addrOf w)

/-- Hazard-table check: bit `addrOf a * 2^k + addrOf b` of `hz` is
`okCls (classify L o a b)`, for every `a`, `b` of length `k`. -/
def hzOK (L : LutInst) (o : OutSel) (k hz : Nat) : Bool :=
  (vecs k).all fun a => (vecs k).all fun b =>
    okCls (classify L o a b) == hz.testBit (addrOf a * 2 ^ k + addrOf b)

def CGate.valid : CGate → Bool
  | .lut _ L o pins tt hz => ttOK L o pins.length tt && hzOK L o pins.length hz
  | .wire _ _ => true

/-- `cg` compiles the gates of `M`. -/
structure Compiled (M : Model) (cg : List CGate) : Prop where
  gates : cg.map CGate.g = M.gates
  valid : cg.all CGate.valid = true

theorem consistent_replicate_X : ∀ (k : Nat) (w : List Bool),
    Consistent (List.replicate k K3.X) w ↔ w.length = k
  | 0, [] => by simp [Consistent]
  | 0, _ :: _ => by simp [Consistent]
  | _ + 1, [] => by simp [Consistent]
  | k + 1, _ :: w => by
      simp only [List.replicate_succ, Consistent, true_or, true_and, List.length_cons,
        Nat.add_right_cancel_iff]
      exact consistent_replicate_X k w

theorem mem_vecs {k : Nat} {w : List Bool} : w ∈ vecs k ↔ w.length = k := by
  unfold vecs; rw [mem_addrs_iff]; exact consistent_replicate_X k w

theorem ttOK_spec {L : LutInst} {o : OutSel} {k tt : Nat} (h : ttOK L o k tt = true)
    {w : List Bool} (hw : w.length = k) : tt.testBit (addrOf w) = outB L o w := by
  unfold ttOK at h
  rw [List.all_eq_true] at h
  exact (beq_iff_eq.1 (h w (mem_vecs.2 hw))).symm

theorem hzOK_spec {L : LutInst} {o : OutSel} {k hz : Nat} (h : hzOK L o k hz = true)
    {a b : List Bool} (ha : a.length = k) (hb : b.length = k) :
    hz.testBit (addrOf a * 2 ^ k + addrOf b) = okCls (classify L o a b) := by
  unfold hzOK at h
  rw [List.all_eq_true] at h
  have h2 := h a (mem_vecs.2 ha)
  rw [List.all_eq_true] at h2
  exact (beq_iff_eq.1 (h2 b (mem_vecs.2 hb))).symm

theorem Compiled.valid_of_mem {M : Model} {cg : List CGate} (hc : Compiled M cg) {c : CGate}
    (h : c ∈ cg) : c.valid = true := by
  have := hc.valid
  rw [List.all_eq_true] at this
  exact this c h

/-! ## 2. Fast evaluation, and its equality with `Env` -/

/-- Value an element drives towards, by table lookup. -/
def cval (s : Nat) : CGate → Bool
  | .lut _ _ _ pins tt _ => tt.testBit (addrOf (pinVec s pins))
  | .wire _ src => bit s src

def CGate.out : CGate → Nat
  | .lut q _ _ _ _ _ => q
  | .wire q _ => q

theorem CGate.out_g (c : CGate) : c.g.out = c.out := by cases c <;> rfl

theorem length_pinVec (s : Nat) (pins : List Nat) : (pinVec s pins).length = pins.length := by
  simp [pinVec]

/-- **decode ∘ encode**: the table lookup on the packed pin vector is the
LUT's Boolean function on the pin vector (`Gate.val`). -/
theorem cval_eq {c : CGate} (hc : c.valid = true) (s : Nat) : cval s c = c.g.val s := by
  cases c with
  | lut q L o pins tt hz =>
      simp only [CGate.valid, Bool.and_eq_true] at hc
      exact ttOK_spec hc.1 (length_pinVec s pins)
  | wire q src => rfl

def excMaskF (M : Model) (cg : List CGate) (s : Nat) : Nat :=
  M.env.foldl (fun m e => if e.2 s then setBit m e.1 else m)
    (cg.foldl (fun m c => if (cval s c != bit s c.out) then setBit m c.out else m) 0)

/-- `Env.enMask` with the excitation mask given. -/
def enOf (M : Model) (ex : Nat) : Nat :=
  M.prio.foldl (fun m p => if bit ex p.1 && p.1 != p.2 then clrBit m p.2 else m) ex

theorem enMask_eq_enOf (M : Model) (s : Nat) : enMask M s = enOf M (excMask M s) := rfl

theorem foldl_congr_mem {α β : Type} {f g : β → α → β} :
    ∀ (l : List α) (b : β), (∀ a ∈ l, ∀ b, f b a = g b a) → l.foldl f b = l.foldl g b
  | [], _, _ => rfl
  | a :: l, b, h => by
      simp only [List.foldl_cons]
      rw [h a (List.mem_cons_self) b]
      exact foldl_congr_mem l _ (fun x hx => h x (List.mem_cons_of_mem _ hx))

theorem excMaskF_eq {M : Model} {cg : List CGate} (hc : Compiled M cg) (s : Nat) :
    excMaskF M cg s = excMask M s := by
  unfold excMaskF excMask
  congr 1
  rw [← hc.gates, List.foldl_map]
  apply foldl_congr_mem
  intro c hm m
  simp only [Gate.exc, cval_eq (hc.valid_of_mem hm), CGate.out_g]

theorem enMaskF_eq {M : Model} {cg : List CGate} (hc : Compiled M cg) (s : Nat) :
    enOf M (excMaskF M cg s) = enMask M s := by
  rw [excMaskF_eq hc]; rfl

/-- `Env.newPend` with the enable masks of `s` (`e0`) and of the successor (`e1`)
given. -/
def newPendF (M : Model) (e0 e1 s t gi j p : Nat) : Nat :=
  if !M.settle then (if p == t || slot M s gi j != 0 then 2 ^ M.n - 1 else 0) else
  if p == t then clrBit e0 t &&& e1
  else
    let pd := slot M s gi j
    if bit pd t then clrBit pd t &&& e1 else 0

def pinSlotsF (M : Model) (e0 e1 s t gi : Nat) (pins : List Nat) : Nat :=
  (idxd pins 0).foldl (fun acc pj => acc + (newPendF M e0 e1 s t gi pj.2 pj.1 <<< off M gi pj.2)) 0

def slotsOfF (M : Model) (e0 e1 s t : Nat) : Nat :=
  (idxd M.gates 0).foldl (fun acc ggi =>
    match ggi.1 with
    | .lut q _ _ pins => if q == t then acc else acc + pinSlotsF M e0 e1 s t ggi.2 pins
    | .wire _ _ => acc) 0

def postF (M : Model) (e0 e1 s t : Nat) : Nat := (s ^^^ 2 ^ t) % 2 ^ M.n + slotsOfF M e0 e1 s t

/-- **Transitions commute**: `postF` with the shared masks is `Env.post`. -/
theorem postF_eq (M : Model) (s t : Nat) :
    postF M (enMask M s) (enMask M (s ^^^ 2 ^ t)) s t = post M s t := rfl

def persistOKF (M : Model) (x0 x1 _s t : Nat) : Bool :=
  (List.range M.n).all fun u =>
    u == t || !bit x0 u || bit x1 u || (isEnv M t && isEnv M u)

theorem persistOKF_eq (M : Model) (s t : Nat) :
    persistOKF M (excMask M s) (excMask M (s ^^^ 2 ^ t)) s t = persistOK M s t := rfl

/-- `Env.lutOK` with `classify`/`outB` replaced by table lookups. -/
def lutOKF (M : Model) (s t : Nat) (c : CGate) (gi : Nat) : Bool :=
  match c with
  | .lut q _ _ pins tt hz =>
      q == t ||
        (hz.testBit (addrOf (oldVec M s t gi pins) * 2 ^ pins.length +
            addrOf (pinVec (s ^^^ 2 ^ t) pins)) &&
          !(tt.testBit (addrOf (oldVec M s t gi pins)) != bit (s ^^^ 2 ^ t) q &&
            tt.testBit (addrOf (pinVec (s ^^^ 2 ^ t) pins)) == bit (s ^^^ 2 ^ t) q))
  | .wire _ _ => true

theorem length_idxd {α : Type} : ∀ (l : List α) (i : Nat), (idxd l i).length = l.length
  | [], _ => rfl
  | _ :: l, i => by simp [idxd, length_idxd l (i + 1)]

theorem length_oldVec (M : Model) (s t gi : Nat) (pins : List Nat) :
    (oldVec M s t gi pins).length = pins.length := by
  simp [oldVec, length_idxd]

theorem lutOKF_eq {c : CGate} (hc : c.valid = true) (M : Model) (s t gi : Nat) :
    lutOKF M s t c gi = lutOK M s t c.g gi := by
  cases c with
  | lut q L o pins tt hz =>
      simp only [CGate.valid, Bool.and_eq_true] at hc
      simp only [lutOKF, lutOK, CGate.g]
      rw [hzOK_spec hc.2 (length_oldVec M s t gi pins) (length_pinVec _ pins),
        ttOK_spec hc.1 (length_oldVec M s t gi pins), ttOK_spec hc.1 (length_pinVec _ pins)]
  | wire q src => rfl

theorem idxd_map {α β : Type} (f : α → β) : ∀ (l : List α) (i : Nat),
    idxd (l.map f) i = (idxd l i).map fun p => (f p.1, p.2)
  | [], _ => rfl
  | a :: l, i => by simp [idxd, idxd_map f l (i + 1)]

theorem mem_idxd {α : Type} : ∀ {l : List α} {i : Nat} {a : α} {j : Nat}, (a, j) ∈ idxd l i → a ∈ l
  | [], _, _, _, h => by simp [idxd] at h
  | b :: l, i, a, j, h => by
      simp only [idxd, List.mem_cons, Prod.mk.injEq] at h
      rcases h with ⟨rfl, _⟩ | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (mem_idxd h)

theorem all_congr_mem {α : Type} {f g : α → Bool} :
    ∀ (l : List α), (∀ a ∈ l, f a = g a) → l.all f = l.all g
  | [], _ => rfl
  | a :: l, h => by
      simp only [List.all_cons]
      rw [h a List.mem_cons_self, all_congr_mem l (fun x hx => h x (List.mem_cons_of_mem _ hx))]

def stepOKF (M : Model) (cg : List CGate) (x0 x1 s t : Nat) : Bool :=
  persistOKF M x0 x1 s t && (idxd cg 0).all fun ci => lutOKF M s t ci.1 ci.2

theorem stepOKF_eq {M : Model} {cg : List CGate} (hc : Compiled M cg) (s t : Nat) :
    stepOKF M cg (excMaskF M cg s) (excMaskF M cg (s ^^^ 2 ^ t)) s t = stepOK M s t := by
  unfold stepOKF stepOK
  rw [excMaskF_eq hc, excMaskF_eq hc, persistOKF_eq, ← hc.gates, idxd_map, List.all_map]
  congr 1
  apply all_congr_mem
  intro ci hci
  exact lutOKF_eq (hc.valid_of_mem (mem_idxd hci)) M s t ci.2

/-- The fast successor function. -/
def succsF (M : Model) (cg : List CGate) (s : Nat) : List (Nat × Nat) :=
  let e0 := enOf M (excMaskF M cg s)
  ((List.range M.n).filter (bit e0)).map fun t =>
    (t, postF M e0 (enOf M (excMaskF M cg (s ^^^ 2 ^ t))) s t)

/-- **The fast successor function is `Env.succs`.** -/
theorem succsF_eq {M : Model} {cg : List CGate} (hc : Compiled M cg) (s : Nat) :
    succsF M cg s = succs M s := by
  simp only [succsF, succs, enMaskF_eq hc, postF_eq]

/-! ## 3. The certificate checker and its soundness (proved once) -/

theorem Tree.contains_insert : ∀ (T : Tree) (y x : Nat),
    (T.insert y).contains x = true → x = y ∨ T.contains x = true
  | .leaf, y, x, h => by
      simp only [Tree.insert, Tree.contains] at h
      by_cases hx : (x == y) = true
      · exact Or.inl (beq_iff_eq.1 hx)
      · simp only [hx, Bool.false_eq_true, ↓reduceIte] at h
        split at h <;> cases h
  | .node l k r, y, x, h => by
      simp only [Tree.insert] at h
      by_cases hy : (y == k) = true
      · simp only [hy, ↓reduceIte] at h; exact Or.inr h
      · simp only [hy, Bool.false_eq_true, ↓reduceIte] at h
        split at h
        · simp only [Tree.contains] at h ⊢
          by_cases hx : (x == k) = true
          · simp [hx]
          · simp only [hx, Bool.false_eq_true, ↓reduceIte] at h ⊢
            split at h
            · rcases Tree.contains_insert l y x h with h' | h'
              · exact Or.inl h'
              · right; simp [*]
            · right; simp [*]
        · simp only [Tree.contains] at h ⊢
          by_cases hx : (x == k) = true
          · simp [hx]
          · simp only [hx, Bool.false_eq_true, ↓reduceIte] at h ⊢
            split at h
            · right; simp [*]
            · rcases Tree.contains_insert r y x h with h' | h'
              · exact Or.inl h'
              · right; simp [*]

/-- The certificate as a BST (any insertion order is sound; the generator orders
the list so that the tree is balanced). -/
def mkTree (cert : List Nat) : Tree := cert.foldl Tree.insert .leaf

theorem contains_foldl_insert : ∀ (cert : List Nat) (T : Tree) (x : Nat),
    (cert.foldl Tree.insert T).contains x = true → x ∈ cert ∨ T.contains x = true
  | [], _, _, h => Or.inr h
  | y :: ys, T, x, h => by
      rcases contains_foldl_insert ys (T.insert y) x h with h' | h'
      · exact Or.inl (List.mem_cons_of_mem _ h')
      · rcases Tree.contains_insert T y x h' with rfl | h''
        · exact Or.inl List.mem_cons_self
        · exact Or.inr h''

theorem mem_of_mkTree {cert : List Nat} {x : Nat} (h : (mkTree cert).contains x = true) :
    x ∈ cert := by
  rcases contains_foldl_insert cert .leaf x h with h | h
  · exact h
  · simp [Tree.contains] at h

/-- Per-state check: every enabled transition leads into `T` and passes the
step checks. Masks are computed once per state and once per successor. -/
def stateOK (M : Model) (cg : List CGate) (T : Tree) (s : Nat) : Bool :=
  let x0 := excMaskF M cg s
  let e0 := enOf M x0
  (List.range M.n).all fun t => !bit e0 t ||
    (let x1 := excMaskF M cg (s ^^^ 2 ^ t)
     T.contains (postF M e0 (enOf M x1) s t) && stepOKF M cg x0 x1 s t)

/-- **The checker.** `Q'` is the per-state property, evaluated fast (see
`liveF_eq` for liveness). -/
def check (M : Model) (cg : List CGate) (Q' : Nat → Bool) (cert : List Nat) : Bool :=
  M.inits.all (mkTree cert).contains && cert.all fun s => Q' s && stateOK M cg (mkTree cert) s

theorem stateOK_sound {M : Model} {cg : List CGate} (hc : Compiled M cg) {T : Tree} {s : Nat}
    (h : stateOK M cg T s = true) :
    ∀ p ∈ succs M s, T.contains p.2 = true ∧ stepOK M s p.1 = true := by
  intro p hp
  simp only [succs, List.mem_map, List.mem_filter, List.mem_range] at hp
  obtain ⟨t, ⟨ht, he⟩, rfl⟩ := hp
  simp only [stateOK, List.all_eq_true, List.mem_range, Bool.or_eq_true, Bool.not_eq_true',
    Bool.and_eq_true] at h
  rw [← enMaskF_eq hc] at he
  rcases h t ht with h1 | h1
  · rw [h1] at he; cases he
  · refine ⟨?_, ?_⟩
    · have := h1.1
      rw [enMaskF_eq hc, enMaskF_eq hc, postF_eq] at this
      exact this
    · rw [← stepOKF_eq hc]; exact h1.2

/-- **Soundness of the checker** (proved once, for every model): a passing
certificate contains every reachable state, and every reachable state satisfies
`Q` and every step check (`Env.stepOK`: hazard-free MIC at every non-firing LUT,
persistence). -/
theorem check_sound {M : Model} {cg : List CGate} {Q : Nat → Bool} {Q' : Nat → Bool}
    {cert : List Nat} (hc : Compiled M cg) (hQ : ∀ s, Q' s = Q s)
    (h : check M cg Q' cert = true) :
    ∀ s, Reach M s → s ∈ cert ∧ Q s = true ∧ ∀ p ∈ succs M s, stepOK M s p.1 = true := by
  simp only [check, Bool.and_eq_true, List.all_eq_true] at h
  obtain ⟨hinit, hall⟩ := h
  have key : ∀ s, (mkTree cert).contains s = true → s ∈ cert ∧ Q s = true ∧
      ∀ p ∈ succs M s, (mkTree cert).contains p.2 = true ∧ stepOK M s p.1 = true := by
    intro s hs
    have hm := mem_of_mkTree hs
    obtain ⟨hq, hst⟩ := hall s hm
    exact ⟨hm, hQ s ▸ hq, stateOK_sound hc hst⟩
  have inv : ∀ s, Reach M s → (mkTree cert).contains s = true := by
    intro s hs
    induction hs with
    | init h => exact hinit _ h
    | step _ hp ih => exact ((key _ ih).2.2 _ hp).1
  intro s hs
  obtain ⟨hm, hq, hp⟩ := key s (inv s hs)
  exact ⟨hm, hq, fun p hpm => (hp p hpm).2⟩

theorem check_Sound {M : Model} {cg : List CGate} {Q Q' : Nat → Bool} {cert : List Nat}
    (hc : Compiled M cg) (hQ : ∀ s, Q' s = Q s) (h : check M cg Q' cert = true) : Sound M Q :=
  fun s hs => let r := check_sound hc hQ h s hs; ⟨r.2.1, r.2.2⟩

/-- Fast liveness. -/
def liveF (M : Model) (cg : List CGate) (s : Nat) : Bool := enOf M (excMaskF M cg s) != 0

theorem liveF_eq {M : Model} {cg : List CGate} (hc : Compiled M cg) (s : Nat) :
    liveF M cg s = live M s := by
  simp only [liveF, live, enMaskF_eq hc]

end Formal.Core.EnvFast
