import Formal.Net.AO.UnrollClaimU
import Formal.Net.AO.UnrollUX
import Formal.Net.AO.Dec

/-!
# A toy instance of the every-word reduction: a two-node handshake, `n` rounds, every `n` (shard C, non-vacuity)

**Problem, plainly.** `Unroll*` / `UnrollRest` / `UnrollClaimU` / `UnrollUX` reduce every certificate-wide hypothesis
of the timed AND-OR theorem, for the certificate of ANY word of window kinds, to checks on single kinds, consecutive
kinds and sub-words of at most 2 or 3 kinds. Can all those checks actually hold, for an infinite family of words, so
that the reduced theorems say something? A toy with one kind and the words `K^n` (every `n`) answers this.

**The toy.** Node 0 is a free environment node (the request), toggling when the acknowledge has caught up
(`envEn`); node 1 is a buffer gate (the acknowledge) reading node 0 with read delay in `[1, 2]`. The kind `K` is one
handshake: request, acknowledge, request, acknowledge (two events per node). The acknowledge's `k`-th event is caused
by the request's `k`-th, the request's `k`-th by the acknowledge's `(k-1)`-th (one window back for `k = 0`).
No data nodes, so no claims and no guards; empty separation and upper-bound tables.

**Proved**, for every `n`:
* the finite checks, by `decide` or short case splits: the four window local checks `lcW` (sub-words `K^0..K^3`, by
  enumeration `lcheckXA_of_enum`), the skew-row window check `toWin` on the three sub-words (`[K]` and `[K, K]` at
  window 0, `[K, K]` at window 1) -- non-trivial: the gate's own row against its input (input `hi` 2 > own bound 1)
  is met by the cause of each acknowledge event --, `KindTm`, `KindLStep`, `PairChain`, `BackChain`, `KindRT`,
  `KindSub`, `KindNe`, and the trivial `SepWin`, `UpWin`, `GdWin`, `GcWinU`, `hIk`;
* `hloc_toy`: the long local check at the gate for every word length, via `UnrollAsm.lcheckXA_unroll3`;
* `toy_follows`: the conclusion of `UnrollClaimU.timedA_follows_unrollUXC` (ideals of the full order, every change a
  certified event, separations sound) for every behaviour from the all-low state, given `hEnvE` for the request;
  `toy_live`: the conclusion of `UnrollUX.timedA_live_unrollUX`, given also the environment's progress;
* `hEnv_of_stop`, `henv_of`: those two environment hypotheses from plain ones (the request toggles at most `2n` times;
  while fewer and the acknowledge has caught up, it toggles again), giving `toy_follows_plain`, `toy_live_plain`;
* `toy_nonvacuous`: a concrete behaviour `xb n` (all reads one step late) meets every hypothesis, for every `n`.

**Not shown.** This is a toy, not THE target: one kind, two nodes, no data nodes (so the claim, guard, `ChainUOK`
and external-claim machinery is instantiated only with empty lists), empty separation and upper-bound tables (so
`SepOKA`/`UpOKA` hold vacuously), one dependency set per reader with a single input. It shows only that the
every-word reduction can be discharged by finite checks for an infinite family of words; nothing about the kinds,
words or checks of THE target.
-/
namespace Formal.Net.AO.UnrollToy
open Formal.Net.AO Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX Formal.Net.OccNet.TimedR
  Formal.Net.OccNet.TimedU
open Formal.Net.OccNet (st)

/-- Node 0: the environment's request; node 1: a buffer gate (the acknowledge) reading node 0 with delay in
`[1, 2]`. -/
def N : TNet (Fin 2) := ⟨fun v => v == 1, fun v => if v = 1 then [0] else [], fun _ l => l.getD 0 false,
  fun _ _ => 1, fun _ _ => 2⟩
def dat : Fin 2 → Bool := fun _ => false
/-- The environment toggles the request when the acknowledge has caught up. -/
def envEn : Fin 2 → (Fin 2 → Bool) → Bool := fun v s => v == 0 && (s 0 == s 1)

def cs : Fin 2 → Nat → List (List (Fin 2 × Int)) := fun u k =>
  if u = 0 then [[(1, (k : Int) - 1)]] else [[(0, (k : Int))]]

/-- The one kind: one handshake (request, acknowledge, request, acknowledge). -/
def K : WKindF (Fin 2) :=
  { len := fun _ => 2
    causes := cs
    s0 := fun _ => false
    Lr := fun a k c => if a = c then (k : Int) + 1 else if a = 1 then (k : Int) + 1 else (k : Int)
    cl := []
    gd := fun _ _ => []
    sep := fun _ _ _ _ => none
    up := fun _ _ => none
    rk := fun u k => 2 * k + u.val
    fc := cs }

def BIG : Nat := 4
def D : Fin 2 → List (Fin 2) := fun v => if v = 1 then [1, 0] else [0, 1]

abbrev KT : WKindT (Fin 2) := K.toWKindT
abbrev KW : WKind (Fin 2) := K.toWKindT.toWKind

/-! ## Words and sub-words -/

theorem wP_rep (n : Nat) : wP (List.replicate n K) = List.replicate n KT := by simp [wP, List.map_replicate]
theorem wF_rep (n : Nat) : wF (List.replicate n K) = List.replicate n K.full := by simp [wF, List.map_replicate]
theorem wk_rep (n : Nat) : wk (List.replicate n KT) = List.replicate n KW := by simp [wk, List.map_replicate]

/-- The sub-words of two kinds `timing_unroll` checks are three: `[K]` or `[K, K]` at window 0, `[K, K]` at 1. -/
theorem sub2 {β : Type} (X : β) (n i : Nat) (hi : i < n) (P : List β → Nat → Prop) (h1 : P [X] 0)
    (h2 : P [X, X] 0) (h3 : P [X, X] 1) : P (((List.replicate n X).drop (i - 1)).take 2) (i - (i - 1)) := by
  rw [List.drop_replicate, List.take_replicate]
  cases i with
  | zero =>
    rcases (show min 2 (n - (0 - 1)) = 1 ∨ min 2 (n - (0 - 1)) = 2 by omega) with h | h <;> rw [h]
    · exact h1
    · exact h2
  | succ i =>
    rw [show min 2 (n - (i + 1 - 1)) = 2 by omega, show i + 1 - (i + 1 - 1) = 1 by omega]
    exact h3

/-- The sub-words of three kinds the local check reads: `K` repeated 0 to 3 times. -/
theorem sub3 {β : Type} (X : β) (n j : Nat) (P : List β → Prop) (h0 : P []) (h1 : P [X]) (h2 : P [X, X])
    (h3 : P [X, X, X]) : P (((List.replicate n X).drop j).take 3) := by
  rw [List.drop_replicate, List.take_replicate]
  rcases (show min 3 (n - j) = 0 ∨ min 3 (n - j) = 1 ∨ min 3 (n - j) = 2 ∨ min 3 (n - j) = 3 by omega)
    with h | h | h | h <;> rw [h]
  · exact h0
  · exact h1
  · exact h2
  · exact h3

theorem off_even (n : Nat) : ∀ j u, off (wcs (List.replicate n KW)) j u % 2 = 0 := by
  induction n with
  | zero => intro j u; simp [wcs, off]
  | succ n ih =>
    intro j u
    cases j with
    | zero => simp [off_zero]
    | succ j =>
      rw [List.replicate_succ]
      show (KW.len u + off (wcs (List.replicate n KW)) j u) % 2 = 0
      have := ih j u
      have e : KW.len u = 2 := rfl
      omega

theorem st_false (n j : Nat) : st (fun _ => false) (off (wcs (List.replicate n KW)) j) = fun _ => false := by
  funext u
  simp only [st]
  have := off_even n j u
  simp [this]

/-! ## The local check -/

def Fx : Fin 2 → List Bool → List Bool → Bool := fun v l _ =>
  if v = 1 then (l.getD 1 false != l.getD 0 false) else (l.getD 0 false == l.getD 1 false)

theorem hF : ∀ v s, tEn N envEn v s = Fx v ((D v).map s) (([] : List (Fin 2)).map s) := by
  intro v s
  rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl
  · simp [tEn, N, envEn, D, Fx]
  · simp [tEn, N, D, Fx]

/-- The window local check at the gate, for each of the four sub-words of three kinds (by enumeration). -/
theorem memD (v y : Fin 2) : y ∈ D v := by revert v y; decide

theorem lcW (s : List (WKind (Fin 2))) (hs : s = [] ∨ s = [KW] ∨ s = [KW, KW] ∨ s = [KW, KW, KW]) :
    LCheckXA N dat envEn (fun _ => false) (unroll (wcs s) (fun _ _ => 0)) (uL s (fun _ => 0)) D (ucl s)
      (fun v z => ugd v z s (fun _ => 0) 0) 1 := by
  rcases hs with rfl | rfl | rfl | rfl <;>
  exact lcheckXA_of_enum (Z := fun _ => []) N dat envEn _ _ _ _ hF 1 (by decide) (by decide) (by decide)
      (fun _ _ _ _ p _ => memD 1 p.1) (by decide) (by decide) (by decide) (by decide) (by decide)

theorem lcW3 (n j : Nat) :
    LCheckXA N dat envEn (fun _ => false) (unroll (wcs (((List.replicate n KW).drop j).take 3)) (fun _ _ => 0))
      (uL (((List.replicate n KW).drop j).take 3) (fun _ => 0)) D (ucl (((List.replicate n KW).drop j).take 3))
      (fun v z => ugd v z (((List.replicate n KW).drop j).take 3) (fun _ => 0) 0) 1 :=
  sub3 KW n j (fun s => LCheckXA N dat envEn (fun _ => false) (unroll (wcs s) (fun _ _ => 0)) (uL s (fun _ => 0)) D
      (ucl s) (fun v z => ugd v z s (fun _ => 0) 0) 1)
    (lcW _ (Or.inl rfl)) (lcW _ (Or.inr (Or.inl rfl))) (lcW _ (Or.inr (Or.inr (Or.inl rfl))))
    (lcW _ (Or.inr (Or.inr (Or.inr rfl))))

theorem pairChain_rep : ∀ n, PairChain (D 1) (List.replicate n KW)
  | 0 => trivial
  | 1 => trivial
  | n + 2 => by
    show PairChain (D 1) (KW :: KW :: List.replicate n KW)
    exact ⟨by decide, pairChain_rep (n + 1)⟩

theorem backChain_rep : ∀ n, BackChain (List.replicate n KT)
  | 0 => trivial
  | 1 => trivial
  | n + 2 => by
    show BackChain (KT :: KT :: List.replicate n KT)
    exact ⟨by decide, backChain_rep (n + 1)⟩

/-- **The long local check at the gate, for every word length `n`**, in the form `hloc` of
`timedA_follows_unroll*` takes, from the four window checks `lcW` via `UnrollAsm.lcheckXA_unroll3`. -/
theorem hloc_toy (n : Nat) (s0 : Fin 2 → Bool) (hs0 : ∀ w, s0 w = false) :
    ∀ v, N.gate v = true → dat v = false → v ∈ D v ∧
      LCheckXA N dat envEn s0 (LC BIG (wP (List.replicate n K))) (uL (wk (wP (List.replicate n K))) (fun _ => 0)) D
        (uclT (wk (wP (List.replicate n K))) (fun _ => 0))
        (fun v z => ugd v z (wk (wP (List.replicate n K))) (fun _ => 0) 0) v := by
  intro v hg _
  have hv : v = 1 := by
    rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl
    · simp [N] at hg
    · rfl
  subst hv
  refine ⟨by decide, ?_⟩
  have e : s0 = fun _ => false := funext hs0
  subst e
  simp only [LC, wt]
  rw [wP_rep, wk_rep]
  apply (lcheckXA_uclT (List.replicate n KW) (fun _ => 0)).mpr
  refine lcheckXA_unroll3 (by decide) ?_ (List.replicate n KW) _ (fun _ _ => 0)
    (fun _ _ _ _ _ q _ => memD 1 q.1) (fun z hz => by simp [dat] at hz) (fun z hz => by simp [dat] at hz)
    (fun z hz => by simp [dat] at hz) (pairChain_rep n) (fun w hw => by rw [List.eq_of_mem_replicate hw]; decide) ?_
  · intro s s' h _
    have h0 := h 0 (by decide)
    have h1 := h 1 (by decide)
    simp [tEn, N, h0, h1]
  · intro j _
    rw [st_false]
    simp only [win]
    rw [← wcs_drop, ← wcs_take]
    exact lcW3 n j

/-! ## The timing tables -/

theorem usep_KT : ∀ (s : List (WKindT (Fin 2))), (∀ w ∈ s, w = KT) → ∀ b m a k, usep s b m a k = none
  | [], _, _, _, _, _ => rfl
  | w :: s, h, b, m, a, k => by
    have hw := h w (by simp)
    subst hw
    simp only [usep]
    split
    · rfl
    · exact usep_KT s (fun w' hw' => h w' (by simp [hw'])) _ _ _ _

theorem uup_KT : ∀ (s : List (WKindT (Fin 2))), (∀ w ∈ s, w = KT) → ∀ e0 e, uup s e0 e = none
  | [], _, _, _ => rfl
  | w :: s, h, e0, e => by
    have hw := h w (by simp)
    subst hw
    simp only [uup]
    split
    · rfl
    · exact uup_KT s (fun w' hw' => h w' (by simp [hw'])) _ _

theorem sepWin_KT (s : List (WKindT (Fin 2))) (hs : ∀ w ∈ s, w = KT) (t : Nat) : SepWin N BIG s t := by
  intro b m a k d _ h
  rw [usep_KT s hs] at h
  cases h

theorem upWin_KT (s : List (WKindT (Fin 2))) (hs : ∀ w ∈ s, w = KT) (t : Nat) : UpWin N dat BIG s t := by
  intro e0 e d _ h
  rw [uup_KT s hs] at h
  cases h

theorem gdWin_KT (s : List (WKindT (Fin 2))) (hs : ∀ w ∈ s, w = KT) (t : Nat) : GdWin N s t := by
  intro h v z _ _ g hg
  rw [hs _ (List.getElem_mem h)] at hg
  simp [KT, K] at hg

/-- **The skew rows of the sub-words** (non-trivial: the gate's own row against its input, whose `hi` is 2 while the
gate's own delay bound is 1, is met by the cause `(0, k)` of every acknowledge event `(1, k)`). -/
theorem toWin (s : List (WKindT (Fin 2))) (t : Nat)
    (hs : (s = [KT] ∧ t = 0) ∨ (s = [KT, KT] ∧ t = 0) ∨ (s = [KT, KT] ∧ t = 1)) : TOWin N BIG D s t := by
  have key : ∀ k, k < off (wt s) (t + 1) 1 →
      0 < uL (wk s) (fun _ => 0) 1 k 0 ∧ uL (wk s) (fun _ => 0) 1 k 0 - 1 < tot (wt s) 0 ∧
        ∀ alt ∈ (WC BIG s).causes 1 k, ∃ p ∈ alt, p.1 = 0 ∧ uL (wk s) (fun _ => 0) 1 k 0 ≤ p.2 + 1 := by
    rcases hs with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩ <;> decide
  have hrow : ∀ v a b : Fin 2, a ≠ b → lo' N v a < hi' N v b → v = 1 ∧ a = 1 ∧ b = 0 := by decide
  intro v a b k _ _ hab hin hlo _
  obtain ⟨rfl, rfl, rfl⟩ := hrow v a b hab hlo
  obtain ⟨h1, h2, h4⟩ := key k hin.2
  exact ⟨h1, h2, Or.inr ⟨rfl, k, Nat.le_refl _, h4⟩⟩

theorem mem_sub_rep {β : Type} {X : β} {n j r : Nat} : ∀ w ∈ ((List.replicate n X).drop j).take r, w = X :=
  fun _ hw => List.eq_of_mem_replicate (List.mem_of_mem_drop (List.mem_of_mem_take hw))

/-! ## Per-kind checks -/

theorem kindTm (w : WKindT (Fin 2)) (hw : w = KT ∨ w = K.full) : KindTm BIG w := by
  rcases hw with rfl | rfl
  · refine ⟨fun u k hk => ?_, by decide, by decide⟩
    have : k = 0 := by simp [KT, K] at hk; omega
    subst this; revert u; decide
  · refine ⟨fun u k hk => ?_, by decide, by decide⟩
    have : k = 0 := by simp [WKindF.full, K] at hk; omega
    subst this; revert u; decide

/-- The bound check, in a form decidable on the kind: through the node itself or through a cause on the target node
(pv-independent). -/
theorem lstep_strong : ∀ u : Fin 2, ∀ k, k < K.full.len u → ∀ c : Fin 2,
    (u = c ∧ K.full.Lr u k c ≤ k + 1) ∨
    (∀ alt ∈ K.full.causes u k, ∃ q ∈ alt, q.1 = c ∧ K.full.Lr u k c ≤ q.2 + 1) := by decide

theorem kindLStep (pv : Option (WKindT (Fin 2))) : KindLStep pv K.full := by
  intro u k c hk
  rcases lstep_strong u k hk c with h | h
  · exact Or.inl h
  · refine Or.inr (Or.inr (Or.inr (Or.inr fun alt halt => ?_)))
    obtain ⟨q, hq, h1, h2⟩ := h alt halt
    exact ⟨q, hq, Or.inl ⟨h1, h2⟩⟩

theorem kindRT : KindRT K := fun _ _ _ aP h => ⟨aP, h, fun _ hq => Or.inl hq⟩
theorem kindSub : KindSub K := fun _ _ _ aF h => ⟨aF, h, fun _ hq => hq⟩
theorem kindNe : KindNe K := by
  intro u k _
  show cs u k ≠ []
  unfold cs; split <;> simp

/-! ## Claims and guards: none -/

theorem uclT_rep : ∀ (n : Nat) (b : Fin 2 → Nat), uclT (List.replicate n KW) b = []
  | 0, _ => rfl
  | n + 1, b => by
    show KW.cl.map (shC b) ++ uclT (List.replicate n KW) _ = []
    rw [uclT_rep n]; rfl

theorem ugd_rep (v z : Fin 2) : ∀ (n : Nat) (b : Fin 2 → Nat) (c : Nat), ugd v z (List.replicate n KW) b c = []
  | 0, _, _ => rfl
  | n + 1, b, c => by
    show (KW.gd v z).map (shiftG b c) ++ ugd v z (List.replicate n KW) _ _ = []
    rw [ugd_rep v z n]; rfl

theorem uclT_toy (n : Nat) : uclT (wk (wP (List.replicate n K))) (fun _ => 0) = [] := by
  rw [wP_rep, wk_rep, uclT_rep]

/-! ## The long certificate in closed form (for the environment hypotheses) -/

theorem wkF_rep (n : Nat) : wk (wF (List.replicate n K)) = List.replicate n KW := by
  simp only [wF, wk, List.map_replicate]; rfl

theorem tot_rep : ∀ (n : Nat) (u : Fin 2), tot (wcs (List.replicate n KW)) u = 2 * n
  | 0, _ => rfl
  | n + 1, u => by
    show KW.len u + tot (wcs (List.replicate n KW)) u = 2 * (n + 1)
    rw [tot_rep n u]
    have e : KW.len u = 2 := rfl
    omega

/-- The long bounds: event `k` of `a` needs `k + 1` events of `c` if `c = a` or `a` is the gate, else `k`. -/
theorem uL_rep : ∀ (n B k : Nat) (a c : Fin 2), k < 2 * n →
    uL (List.replicate n KW) (fun _ => B) a k c = B + k + (if a = c ∨ a = 1 then 1 else 0)
  | 0, _, _, _, _, h => by omega
  | n + 1, B, k, a, c, h => by
    have hlen : ∀ u, KW.len u = 2 := fun _ => rfl
    simp only [List.replicate_succ, uL, hlen]
    split
    · show ((B : Int) + (if a = c then (k : Int) + 1 else if a = 1 then (k : Int) + 1 else (k : Int))).toNat = _
      by_cases h1 : a = c <;> by_cases h2 : a = 1 <;> simp [h1, h2] <;> omega
    · rw [uL_rep n (B + 2) (k - 2) a c (by omega)]
      omega

/-- The long causes of the request's `k`-th event: exactly the acknowledge's previous event. -/
theorem uc_rep : ∀ (n B k : Nat), k < 2 * n → ∃ alt, uc (wcs (List.replicate n KW)) (fun _ => B) 0 k = [alt] ∧
    ∀ p, p ∈ alt ↔ (p = (1, B + k - 1) ∧ 1 ≤ B + k)
  | 0, _, _, h => by omega
  | n + 1, B, k, h => by
    have hlen : ∀ u, KW.len u = 2 := fun _ => rfl
    simp only [List.replicate_succ, wcs, List.map_cons, uc]
    split
    · refine ⟨absAlt (fun _ => B) [(1, (k : Int) - 1)], by simp [KW, K, cs], fun p => ?_⟩
      constructor
      · intro hp
        obtain ⟨q, hq, h0, rfl⟩ := mem_absAlt.mp hp
        simp only [List.mem_singleton] at hq
        subst hq
        simp only at h0 ⊢
        refine ⟨?_, by omega⟩
        simp only [Prod.mk.injEq, true_and]
        omega
      · rintro ⟨rfl, h1⟩
        refine mem_absAlt.mpr ⟨(1, (k : Int) - 1), by simp, by simp only; omega, ?_⟩
        simp only [Prod.mk.injEq, true_and]
        omega
    · have e : (fun p => B + (KW.toWCert).len p) = fun _ => B + 2 := rfl
      obtain ⟨alt, h1, h2⟩ := uc_rep n (B + 2) (k - (KW.toWCert).len 0) (by simp only [hlen] at *; omega)
      refine ⟨alt, ?_, fun p => ?_⟩
      · rw [e]; exact h1
      · rw [h2 p]
        have : (KW.toWCert).len 0 = 2 := rfl
        constructor
        · rintro ⟨rfl, h3⟩; refine ⟨?_, by omega⟩; simp only [Prod.mk.injEq, true_and]; omega
        · rintro ⟨rfl, h3⟩; refine ⟨?_, by omega⟩; simp only [Prod.mk.injEq, true_and]; omega

theorem x_cnt {x : Fin 2 → Nat → Bool} {t0 : Nat} (u : Fin 2) :
    ∀ d, x u (t0 + d) = xor (x u t0) (cnt x t0 u (t0 + d) % 2 == 1)
  | 0 => by simp [cnt_le_t0 u t0 (Nat.le_refl _)]
  | d + 1 => by
    have ih := x_cnt (x := x) (t0 := t0) u d
    rw [show t0 + (d + 1) = t0 + d + 1 by omega, cnt_succ u (t0 + d) (by omega), xor_par, ← ih]
    generalize x u (t0 + d + 1) = a
    generalize x u (t0 + d) = b
    cases a <;> cases b <;> rfl

/-! ## Every word: the theorems -/

section main
variable {x : Fin 2 → Nat → Bool} {r : Fin 2 → Fin 2 → Nat → Nat} {t0 H : Nat}

theorem hKP (n : Nat) : ∀ w ∈ List.replicate n K, KindTm BIG w.toWKindT := fun w hw => by
  rw [List.eq_of_mem_replicate hw]; exact kindTm _ (Or.inl rfl)

theorem hKF (n : Nat) : ∀ w ∈ List.replicate n K, KindTm BIG w.full := fun w hw => by
  rw [List.eq_of_mem_replicate hw]; exact kindTm _ (Or.inr rfl)

theorem hS (n : Nat) : ∀ i, i < (wP (List.replicate n K)).length →
    SepWin N BIG (((wP (List.replicate n K)).drop (i - 1)).take 2) (i - (i - 1)) := fun i _ => by
  rw [wP_rep]; exact sepWin_KT _ mem_sub_rep _

theorem hU (n : Nat) : ∀ i, i < (wP (List.replicate n K)).length →
    UpWin N dat BIG (((wP (List.replicate n K)).drop (i - 1)).take 2) (i - (i - 1)) := fun i _ => by
  rw [wP_rep]; exact upWin_KT _ mem_sub_rep _

theorem hG (n : Nat) : ∀ i, i < (wP (List.replicate n K)).length →
    GdWin N (((wP (List.replicate n K)).drop (i - 1)).take 2) (i - (i - 1)) := fun i _ => by
  rw [wP_rep]; exact gdWin_KT _ mem_sub_rep _

theorem hT (n : Nat) : ∀ i, i < (wP (List.replicate n K)).length →
    TOWin N BIG D (((wP (List.replicate n K)).drop (i - 1)).take 2) (i - (i - 1)) := fun i hi => by
  rw [wP_rep] at hi ⊢
  rw [List.length_replicate] at hi
  exact sub2 KT n i hi (fun s t => TOWin N BIG D s t) (toWin _ _ (Or.inl ⟨rfl, rfl⟩))
    (toWin _ _ (Or.inr (Or.inl ⟨rfl, rfl⟩))) (toWin _ _ (Or.inr (Or.inr ⟨rfl, rfl⟩)))

theorem hL (n : Nat) : ∀ i (hi : i < (wF (List.replicate n K)).length),
    KindLStep (if i = 0 then none else (wF (List.replicate n K))[i - 1]?) (wF (List.replicate n K))[i] := by
  intro i hi
  have e : (wF (List.replicate n K))[i] = K.full := by simp [wF]
  rw [e]; exact kindLStep _

theorem hgdF (n : Nat) : ∀ v z, N.gate v = false → ugd v z (wk (wP (List.replicate n K))) (fun _ => 0) 0 = [] := by
  intro v z _; rw [wP_rep, wk_rep, ugd_rep]

theorem hEnvE_of (n : Nat)
    (hEnv : ∀ s, t0 < s → x 0 s ≠ x 0 (s - 1) → Ideal (CFu BIG (List.replicate n K)) (fun u => cntE dat x t0 u (s - 1)) →
      Enabled (CPu BIG (List.replicate n K)) (fun w => cnt x t0 w (s - 1)) 0) :
    ∀ v s, N.gate v = false → dat v = false → t0 < s → x v s ≠ x v (s - 1) →
      Ideal (CFu BIG (List.replicate n K)) (fun u => cntE dat x t0 u (s - 1)) →
      Enabled (CPu BIG (List.replicate n K)) (fun w => cnt x t0 w (s - 1)) v := by
  intro v s hg _ hs hch hI
  rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl
  · exact hEnv s hs hch hI
  · simp [N] at hg

theorem lenCF (n : Nat) (u : Fin 2) : (CFu BIG (List.replicate n K)).len u = 2 * n := by
  rw [← lenEq_unroll]
  show tot (wcs (wk (wP (List.replicate n K)))) u = 2 * n
  rw [wP_rep, wk_rep, tot_rep]

theorem lenCP (n : Nat) (u : Fin 2) : (CPu BIG (List.replicate n K)).len u = 2 * n := by
  rw [lenEq_unroll]; exact lenCF n u

/-- **The environment hypothesis `hEnvE` from a plain one**: the request toggles at most `2n` times (`hstop`). Its
toggles are then exactly the certificate's: a toggle needs the acknowledge caught up (`envEn`), which, in an ideal
of the certificate, makes the request's next event enabled. -/
theorem hEnv_of_stop (n : Nat) (hb : TBehX N dat envEn x r t0 H) (hx0 : ∀ w, x w t0 = false)
    (hstop : ∀ s, t0 < s → x 0 s ≠ x 0 (s - 1) → cnt x t0 0 (s - 1) < 2 * n) :
    ∀ s, t0 < s → x 0 s ≠ x 0 (s - 1) → Ideal (CFu BIG (List.replicate n K)) (fun u => cntE dat x t0 u (s - 1)) →
      Enabled (CPu BIG (List.replicate n K)) (fun w => cnt x t0 w (s - 1)) 0 := by
  intro s hs hch hI
  have hcE : (fun u => cntE dat x t0 u (s - 1)) = (fun u => cnt x t0 u (s - 1)) := by
    funext u; simp [cntE, dat]
  rw [hcE] at hI
  have hen := hb.env 0 s rfl rfl hs hch
  have hx : ∀ u, x u (s - 1) = (cnt x t0 u (s - 1) % 2 == 1) := by
    intro u
    have := x_cnt (x := x) (t0 := t0) u (s - 1 - t0)
    rw [show t0 + (s - 1 - t0) = s - 1 by omega, hx0] at this
    simpa using this
  simp only [envEn, hx] at hen
  have hpar : cnt x t0 0 (s - 1) % 2 = cnt x t0 1 (s - 1) % 2 := by
    rcases Nat.mod_two_eq_zero_or_one (cnt x t0 0 (s - 1)) with h0 | h0 <;>
    rcases Nat.mod_two_eq_zero_or_one (cnt x t0 1 (s - 1)) with h1 | h1 <;> simp [h0, h1] at hen ⊢
  have hLs := lsound_PF BIG (List.replicate n K) (hKF n) (hL n) 0 _ hI
  rw [wP_rep, wk_rep] at hLs
  have hl0 := (hI 0).1
  have hl1 := (hI 1).1
  rw [lenCF] at hl0 hl1
  simp only at hl0 hl1
  have h10 : cnt x t0 1 (s - 1) ≤ cnt x t0 0 (s - 1) := by
    by_cases hz : cnt x t0 1 (s - 1) = 0
    · omega
    · have := hLs 1 (cnt x t0 1 (s - 1) - 1) 0 (by omega)
      rw [uL_rep n 0 _ 1 0 (by omega)] at this
      simp at this; omega
  have h01 : cnt x t0 0 (s - 1) ≤ cnt x t0 1 (s - 1) + 1 := by
    by_cases hz : cnt x t0 0 (s - 1) = 0
    · omega
    · have := hLs 0 (cnt x t0 0 (s - 1) - 1) 1 (by omega)
      rw [uL_rep n 0 _ 0 1 (by omega)] at this
      simp at this; omega
  have heq : cnt x t0 0 (s - 1) = cnt x t0 1 (s - 1) := by omega
  have hst := hstop s hs hch
  apply enabled_padC.mpr
  refine ⟨?_, ?_⟩
  · show cnt x t0 0 (s - 1) < tot (wcs (wk (wP (List.replicate n K)))) 0
    rw [wP_rep, wk_rep, tot_rep]; exact hst
  · show ∃ alt ∈ uc (wcs (wk (wP (List.replicate n K)))) (fun _ => 0) 0 (cnt x t0 0 (s - 1)), AltIn _ alt
    rw [wP_rep, wk_rep]
    obtain ⟨alt, h1, h2⟩ := uc_rep n 0 _ hst
    refine ⟨alt, by rw [h1]; simp, fun p hp => ?_⟩
    obtain ⟨rfl, h3⟩ := (h2 p).mp hp
    simp only; omega

/-- **The environment's progress `henv` from a plain one**: while the request has toggled fewer than `2n` times and
the acknowledge has caught up in count, the request toggles again. -/
theorem henv_of (n : Nat)
    (hprog : ∀ t, t0 ≤ t → cnt x t0 0 t < 2 * n → cnt x t0 0 t ≤ cnt x t0 1 t →
      ∃ t', t < t' ∧ cnt x t0 0 t < cnt x t0 0 t') :
    ∀ t, t0 ≤ t → Enabled (CFu BIG (List.replicate n K)) (fun w => cntE dat x t0 w t) 0 →
      ∃ t', t < t' ∧ cnt x t0 0 t < cnt x t0 0 t' := by
  intro t ht hen
  have hcE : (fun u => cntE dat x t0 u t) = (fun u => cnt x t0 u t) := by funext u; simp [cntE, dat]
  rw [hcE] at hen
  obtain ⟨hlt, alt, ha, hin⟩ := enabled_padC.mp hen
  have hlt' : cnt x t0 0 t < 2 * n := by
    have := hlt
    change cnt x t0 0 t < tot (wcs (wk (wF (List.replicate n K)))) 0 at this
    rw [wkF_rep, tot_rep] at this; exact this
  refine hprog t ht hlt' ?_
  change alt ∈ uc (wcs (wk (wF (List.replicate n K)))) (fun _ => 0) 0 (cnt x t0 0 t) at ha
  rw [wkF_rep] at ha
  obtain ⟨alt', h1, h2⟩ := uc_rep n 0 _ hlt'
  rw [h1] at ha
  simp only [List.mem_singleton] at ha
  subst ha
  by_cases hz : cnt x t0 0 t = 0
  · omega
  · have := hin (1, 0 + cnt x t0 0 t - 1) ((h2 _).mpr ⟨rfl, by omega⟩)
    simp only at this; omega

/-- **Safety of the toy for every word length `n`** (the conclusion of `UnrollClaimU.timedA_follows_unrollUXC`,
every certificate-wide hypothesis discharged by the per-kind and sub-word checks above): every bounded-delay
behaviour `x` of the handshake net from the all-low state, whose environment toggles only as the certificate of
`n` handshakes allows (`hEnv`), follows that certificate. -/
theorem toy_follows (n : Nat) (hb : TBehX N dat envEn x r t0 H) (hx0 : ∀ w, x w t0 = false)
    (hEnv : ∀ s, t0 < s → x 0 s ≠ x 0 (s - 1) → Ideal (CFu BIG (List.replicate n K)) (fun u => cntE dat x t0 u (s - 1)) →
      Enabled (CPu BIG (List.replicate n K)) (fun w => cnt x t0 w (s - 1)) 0) :
    ∀ t, (∀ τ, τ ≤ t → Ideal (CFu BIG (List.replicate n K)) (fun u => cntE dat x t0 u τ)) ∧
      (∀ v s, dat v = false → t0 < s → s ≤ t → x v s ≠ x v (s - 1) →
        ChangeOKA N (CPu BIG (List.replicate n K)) x t0 r v s) ∧
      (∀ c ∈ uclT (wk (wP (List.replicate n K))) (fun _ => 0), ∀ s, s ≤ t → Holds x t0 H c s) ∧
      SepSound x t0 (LSep (wP (List.replicate n K))) t :=
  timedA_follows_unrollUXC (fun _ => False) (fun _ _ h => h) BIG 2 (Nat.le_refl _) (List.replicate n K)
    (fun _ => D 0) (hKP n) (hKF n) (fun _ _ _ _ _ _ q _ => memD 0 q.1) (by rw [wP_rep]; exact backChain_rep n)
    (hS n) (hU n) (hT n) (hG n) (hL n)
    (fun w hw => by rw [List.eq_of_mem_replicate hw]; exact kindRT)
    (fun w hw b m a k d h => by rw [List.eq_of_mem_replicate hw] at h; cases h)
    (fun _ _ u h => by simp [dat] at h) hb (fun _ _ _ => rfl) (hloc_toy n _ hx0) (hEnvE_of n hEnv) (hgdF n)
    (fun i _ => by
      rw [wP_rep]
      intro h c0 hc0
      rw [mem_sub_rep _ (List.getElem_mem h)] at hc0
      simp [KT, K] at hc0)
    (fun _ _ h => h.elim)
    (fun c hc => by rw [uclT_toy] at hc; simp at hc)
    (fun i hi c0 hc0 => by
      have hall : ∀ w ∈ wP (List.replicate n K), w = KT := by
        rw [wP_rep]; exact fun w hw => List.eq_of_mem_replicate hw
      rw [hall _ (List.getElem_mem hi)] at hc0
      simp [KT, K] at hc0)

/-- **Liveness of the toy for every word length `n`** (`UnrollUX.timedA_live_unrollUX`): with also the
environment's progress `henv` (an enabled request toggle eventually happens), all `2n` events of each node happen
and then the net is quiet. -/
theorem toy_live (n : Nat) (hb : TBehX N dat envEn x r t0 H) (hx0 : ∀ w, x w t0 = false)
    (hEnv : ∀ s, t0 < s → x 0 s ≠ x 0 (s - 1) → Ideal (CFu BIG (List.replicate n K)) (fun u => cntE dat x t0 u (s - 1)) →
      Enabled (CPu BIG (List.replicate n K)) (fun w => cnt x t0 w (s - 1)) 0)
    (henv : ∀ t, t0 ≤ t → Enabled (CFu BIG (List.replicate n K)) (fun w => cntE dat x t0 w t) 0 →
      ∃ t', t < t' ∧ cnt x t0 0 t < cnt x t0 0 t') :
    ∃ T, t0 ≤ T ∧ (∀ u, cntE dat x t0 u T = (CFu BIG (List.replicate n K)).len u) ∧
      ∀ u s, dat u = false → T ≤ s → x u s = x u T :=
  timedA_live_unrollUX (fun _ => False) BIG 2 (Nat.le_refl _) (List.replicate n K)
    (fun _ => D 0) (hKP n) (hKF n) (fun _ _ _ _ _ _ q _ => memD 0 q.1) (by rw [wP_rep]; exact backChain_rep n)
    (hS n) (hU n) (hT n) (hG n) (hL n)
    (fun w hw => by rw [List.eq_of_mem_replicate hw]; exact kindRT)
    (fun w hw b m a k d h => by rw [List.eq_of_mem_replicate hw] at h; cases h)
    (fun _ _ u h => by simp [dat] at h)
    (fun w hw => by rw [List.eq_of_mem_replicate hw]; exact kindSub)
    (fun w hw => by rw [List.eq_of_mem_replicate hw]; exact kindNe)
    (D 0) (fun _ _ u _ => memD 0 u)
    hb (fun _ _ _ => rfl) (hloc_toy n _ hx0) (hEnvE_of n hEnv) (hgdF n)
    (fun c hc => by rw [uclT_toy] at hc; simp at hc)
    (fun _ _ h => h.elim)
    (fun c hc => by rw [uclT_toy] at hc; simp at hc)
    (fun c hc => by rw [uclT_toy] at hc; simp at hc)
    (fun _ => 3) (fun v _ => ⟨by decide, fun w _ => by simp [N]⟩)
    (fun u t hg _ ht hen => by
      rcases (show u = 0 ∨ u = 1 by omega) with rfl | rfl
      · exact henv t ht hen
      · simp [N] at hg)

/-- **Safety of the toy for every `n`, plain hypotheses**: every bounded-delay behaviour of the handshake net from the
all-low state whose request toggles at most `2n` times follows the certificate of the word `K^n`. -/
theorem toy_follows_plain (n : Nat) (hb : TBehX N dat envEn x r t0 H) (hx0 : ∀ w, x w t0 = false)
    (hstop : ∀ s, t0 < s → x 0 s ≠ x 0 (s - 1) → cnt x t0 0 (s - 1) < 2 * n) :
    ∀ t, (∀ τ, τ ≤ t → Ideal (CFu BIG (List.replicate n K)) (fun u => cntE dat x t0 u τ)) ∧
      (∀ v s, dat v = false → t0 < s → s ≤ t → x v s ≠ x v (s - 1) →
        ChangeOKA N (CPu BIG (List.replicate n K)) x t0 r v s) ∧
      SepSound x t0 (LSep (wP (List.replicate n K))) t := fun t =>
  have h := toy_follows n hb hx0 (hEnv_of_stop n hb hx0 hstop) t
  ⟨h.1, h.2.1, h.2.2.2⟩

/-- **Liveness of the toy for every `n`, plain hypotheses**: if moreover the environment answers (while fewer than
`2n` request toggles and the acknowledge caught up, the request toggles again), then every node makes exactly its
`2n` certified changes and the net is quiet afterwards. -/
theorem toy_live_plain (n : Nat) (hb : TBehX N dat envEn x r t0 H) (hx0 : ∀ w, x w t0 = false)
    (hstop : ∀ s, t0 < s → x 0 s ≠ x 0 (s - 1) → cnt x t0 0 (s - 1) < 2 * n)
    (hprog : ∀ t, t0 ≤ t → cnt x t0 0 t < 2 * n → cnt x t0 0 t ≤ cnt x t0 1 t →
      ∃ t', t < t' ∧ cnt x t0 0 t < cnt x t0 0 t') :
    ∃ T, t0 ≤ T ∧ (∀ u, cnt x t0 u T = 2 * n) ∧ ∀ u s, T ≤ s → x u s = x u T := by
  obtain ⟨T, h1, h2, h3⟩ := toy_live n hb hx0 (hEnv_of_stop n hb hx0 hstop) (henv_of n hprog)
  refine ⟨T, h1, fun u => ?_, fun u s hs => h3 u s rfl hs⟩
  have := h2 u
  rw [lenCF] at this
  simpa [cntE, dat] using this

end main

/-! ## The hypotheses are satisfiable: a behaviour for every `n` -/

/-- The request toggles at times `2, 4, ..., 4n`; the acknowledge copies it one step later. -/
def xb (n : Nat) : Fin 2 → Nat → Bool := fun u t =>
  if u = 0 then (min t (4 * n) / 2 % 2 == 1) else if t = 0 then false else (min (t - 1) (4 * n) / 2 % 2 == 1)
def rb : Fin 2 → Fin 2 → Nat → Nat := fun _ _ t => t - 1

theorem par_step (a : Nat) : (((a + 1) % 2 == 1) != (a % 2 == 1)) = true := by
  rcases Nat.mod_two_eq_zero_or_one a with h | h
  · have : (a + 1) % 2 = 1 := by omega
    simp [h, this]
  · have : (a + 1) % 2 = 0 := by omega
    simp [h, this]

theorem cnt_xb (n : Nat) : ∀ t, cnt (xb n) 0 0 t = min t (4 * n) / 2
  | 0 => by simp [cnt]
  | t + 1 => by
    rw [cnt_succ 0 t (Nat.zero_le _), cnt_xb n t]
    simp only [xb, ite_true]
    by_cases hab : min (t + 1) (4 * n) / 2 = min t (4 * n) / 2
    · rw [hab]; simp
    · have e : min (t + 1) (4 * n) / 2 = min t (4 * n) / 2 + 1 := by omega
      rw [e, par_step]; simp

theorem beh_xb (n : Nat) : TBehX N dat envEn (xb n) rb 0 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro u s _ _ hs
    have : s = 0 := by omega
    subst this; rfl
  · intro v w t hv hw ht
    have h1 : v = 1 := by
      rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl
      · simp [N] at hv
      · rfl
    subst h1
    simp only [N, rb]; omega
  · intro v w _ _; simp [N]
  · intro v w t t' _ _ _ h; simp only [rb]; omega
  · intro v t hv ht
    rcases (show v = 0 ∨ v = 1 by omega) with rfl | rfl
    · simp [N] at hv
    · have : t ≠ 0 := by omega
      simp [xb, N, rb, this]
  · intro u t hu _ ht hch
    rcases (show u = 0 ∨ u = 1 by omega) with rfl | rfl
    · simp only [xb, ite_true] at hch
      have hab : min t (4 * n) / 2 ≠ min (t - 1) (4 * n) / 2 := by
        intro h; apply hch; rw [h]
      have e : min (t - 1) (4 * n) / 2 = min (t - 1 - 1) (4 * n) / 2 := by omega
      have ht1 : t - 1 ≠ 0 := by omega
      simp [envEn, xb, ht1, e]
    · simp [N] at hu

theorem hstop_xb (n : Nat) : ∀ s, 0 < s → xb n 0 s ≠ xb n 0 (s - 1) → cnt (xb n) 0 0 (s - 1) < 2 * n := by
  intro s _ hch
  rw [cnt_xb]
  simp only [xb, ite_true] at hch
  have hab : min s (4 * n) / 2 ≠ min (s - 1) (4 * n) / 2 := by
    intro h; apply hch; rw [h]
  omega

theorem hprog_xb (n : Nat) : ∀ t, 0 ≤ t → cnt (xb n) 0 0 t < 2 * n → cnt (xb n) 0 0 t ≤ cnt (xb n) 0 1 t →
    ∃ t', t < t' ∧ cnt (xb n) 0 0 t < cnt (xb n) 0 0 t' := by
  intro t _ h _
  rw [cnt_xb] at h
  refine ⟨4 * n, by omega, ?_⟩
  rw [cnt_xb, cnt_xb]; omega

/-- **The theorems are not vacuous**: for every `n` the behaviour `xb n` (`n` handshakes, all reads one step late)
meets every hypothesis of `toy_follows_plain` and `toy_live_plain`, so both conclusions hold for it. -/
theorem toy_nonvacuous (n : Nat) :
    (∀ t, (∀ τ, τ ≤ t → Ideal (CFu BIG (List.replicate n K)) (fun u => cntE dat (xb n) 0 u τ)) ∧
      (∀ v s, dat v = false → 0 < s → s ≤ t → xb n v s ≠ xb n v (s - 1) →
        ChangeOKA N (CPu BIG (List.replicate n K)) (xb n) 0 rb v s) ∧
      SepSound (xb n) 0 (LSep (wP (List.replicate n K))) t) ∧
    ∃ T, (∀ u, cnt (xb n) 0 u T = 2 * n) ∧ ∀ u s, T ≤ s → xb n u s = xb n u T := by
  have hx0 : ∀ w, xb n w 0 = false := by
    intro w; rcases (show w = 0 ∨ w = 1 by omega) with rfl | rfl <;> simp [xb]
  refine ⟨toy_follows_plain n (beh_xb n) hx0 (hstop_xb n), ?_⟩
  obtain ⟨T, _, h2, h3⟩ := toy_live_plain n (beh_xb n) hx0 (hstop_xb n) (hprog_xb n)
  exact ⟨T, h2, h3⟩

end Formal.Net.AO.UnrollToy
