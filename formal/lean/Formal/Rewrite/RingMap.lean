import Formal.Rewrite.IncCmpGraph

/-!
# Formal.Rewrite.RingMap — storing `g(n)` instead of `n` on a loop-invariant ring preserves every complete run (shard A, 2026-11-18)

**Problem, plainly.** A loop-invariant value `n` enters a loop on `ne` and circulates on a ring of data-oblivious
rules: a 2-input `mux sel [ne, nb] → r` (input 0 is the entry, input 1 the back edge), a `fork r → r0, k`, a
`cond_br cnd r0 → nb (true) / nx (false)` and a `sink nx`. Each iteration a compare `c ← fC(y, k)` reads it. The
rewrite stores `m = g(n)` on the ring instead (e.g. `g = n - 1`): one conversion `ne' ← g(ne)` on the entry, the
mux reads `ne'`, and the compare becomes `c ← fC2(y, k)` with `fC2(v, g w) = fC(v, w)`. Is the rewritten graph's
behaviour the same, whatever the rest of the graph is?

**Proved** (`forward`, `backward`), for ANY imported graph `rs` that has the five rules at labels `M F B S C`, a
free label `D` (`rs[D]? = none`), and `rs'` equal to `rs` except for the rewritten mux and compare and the new
conversion at `D`; with the seven channels `ne ne' r r0 k nb nx` distinct (and distinct from `sel cnd y c`), no
other rule reading or writing `ne' r r0 k nb nx` or reading `ne` (any rule may produce `ne`), and the identity
`hH : ∀ v w, fC2.eval [v, g.eval [w]] = fC.eval [v, w]`: from any store whose channels `ne' r r0 k nb nx` are
empty (`ne` may hold tokens), every complete run of `rs` is matched by a complete run of `rs'` that ends in the
same store on every channel except those seven, and vice versa. The mux's select is data, so both graphs make the
same choices. `ne` is not observed because a terminal store may hold entry tokens the mux never selected, which the
rewritten graph has already converted onto `ne'`. The simulation is lockstep: every rule fires in both graphs, the
conversion `D` is a stutter (the forward direction runs it to completion before each mux firing), and the
relation says the ring channels of `rs'` hold the `g`-images of those of `rs`.

**Not covered:** token level only (no gates, delays or cells); that the rewrite tool's MLIR output imports to
exactly `rs'` (checked per kernel, not here); proving `hH` for a concrete `g`/`fC` (wraparound arithmetic is
the instance's job); rings of any other shape (more forks, more readers, more than one compare).
-/

namespace Formal.Rewrite.RingMap

open Formal.Net.Kahn Formal.Net.GcdHw Formal.Rewrite.IncCmp

/-! ## More single-rule firings -/

/-- `push σ o x`: append `x` to channel `o`. -/
def push (σ : Store Nat Nat) (o x : Nat) : Store Nat Nat := upd σ o (σ o ++ [x])

theorem heads_none {σ : Store Nat Nat} : ∀ {cs : List Nat} {ch : Nat}, ch ∈ cs → σ ch = [] → heads σ cs = none
  | [], _, h, _ => by simp at h
  | d :: cs, ch, h, he => by
    simp only [heads]
    rcases List.mem_cons.mp h with rfl | h
    · rw [he]
    · split
      · rfl
      · rw [heads_none h he]; rfl

/-- A non-`mux` rule with an empty input channel is disabled. -/
theorem step_none_strict {rs : List Rule} {l : Nat} {ru : Rule} (hr : rs[l]? = some ru)
    (hnm : ∀ s ds o iw, ru ≠ .mux s ds o iw) {σ : Store Nat Nat} {ch : Nat} (hch : ch ∈ ru.insL)
    (he : σ ch = []) : step (graph rs) σ l = none := by
  rw [step_graph hr]
  cases ru with
  | mux s ds o iw => exact absurd rfl (hnm s ds o iw)
  | _ => simp only [Rule.fire, strictF, heads_none hch he]; rfl

theorem step_mux {rs : List Rule} {l s o iw : Nat} {ds : List Nat} (hr : rs[l]? = some (.mux s ds o iw))
    {σ : Store Nat Nat} {v d x : Nat} {vs xs : List Nat} (hs : σ s = v :: vs)
    (hd : ds[v % 2 ^ iw]? = some d) (hds : d ≠ s) (hx : σ d = x :: xs) :
    step (graph rs) σ l = some (push (upd (upd σ s vs) d xs) o x) := by
  rw [step_graph hr]
  simp only [Rule.fire, muxF, hs, natVI, hd, hds, ↓reduceIte, hx, Option.map_some, Option.some.injEq]
  funext ch
  simp only [applyF, push, upd]
  by_cases h1 : ch = o
  · subst h1
    by_cases h2 : ch = d
    · subst h2; simp [hds, hx]
    · by_cases h3 : ch = s
      · subst h3; simp [hs, h2]
      · simp [h2, h3]
  · by_cases h2 : ch = d
    · subst h2; simp [hds, hx, h1]
    · by_cases h3 : ch = s
      · subst h3; simp [hs, h2, h1]
      · simp [h1, h2, h3]

theorem step_mux_inv {rs : List Rule} {l s o iw : Nat} {ds : List Nat} (hr : rs[l]? = some (.mux s ds o iw))
    {σ σ1 : Store Nat Nat} (h : step (graph rs) σ l = some σ1) :
    ∃ v vs d x xs, σ s = v :: vs ∧ ds[v % 2 ^ iw]? = some d ∧ d ≠ s ∧ σ d = x :: xs ∧
      σ1 = push (upd (upd σ s vs) d xs) o x := by
  obtain ⟨ru, fr, hr', hf, rfl⟩ := step_some_rule h
  rw [hr] at hr'; cases hr'
  obtain ⟨v, vs, j, d, x, xs, hs, hj, hd, hne, hx, -⟩ := muxF_some (I := natVI) hf
  simp only [natVI, Option.some.injEq] at hj; subst hj
  refine ⟨v, vs, d, x, xs, hs, hd, hne, hx, ?_⟩
  have := step_mux hr hs hd hne hx
  rw [step_graph hr, hf] at this
  exact Option.some.inj this

theorem step_branch {rs : List Rule} {l cc d t f : Nat} (hr : rs[l]? = some (.branch cc d t f))
    {σ : Store Nat Nat} {b x o : Nat} {bs xs : List Nat} (hcd : cc ≠ d) (hb : σ cc = b :: bs)
    (hx : σ d = x :: xs) (ho : (if b % 2 = 1 then t else f) = o) :
    step (graph rs) σ l = some (push (upd (upd σ cc bs) d xs) o x) := by
  rw [step_graph hr]
  simp only [Rule.fire, strictF, heads, hb, hx, Rule.out, natVI, Rule.insL, Option.map_some,
    Option.bind_some, Option.some.injEq]
  funext ch
  simp only [applyF, popOf, push, upd, List.mem_cons, List.not_mem_nil, or_false, beq_iff_eq]
  rw [ho]
  by_cases h1 : ch = o
  · subst h1
    by_cases h2 : ch = d
    · subst h2; simp [hx]
    · by_cases h3 : ch = cc
      · subst h3; simp [hb, h2]
      · simp [h2, h3]
  · by_cases h2 : ch = d
    · subst h2; simp [hx, h1]
    · by_cases h3 : ch = cc
      · subst h3; simp [hb, h2, h1]
      · simp [h1, h2, h3]

theorem step_sink {rs : List Rule} {l i : Nat} (hr : rs[l]? = some (.sink i))
    {σ : Store Nat Nat} {v : Nat} {vs : List Nat} (hv : σ i = v :: vs) :
    step (graph rs) σ l = some (upd σ i vs) := by
  rw [step_graph hr]
  simp only [Rule.fire, strictF, heads, hv, Rule.out, Rule.insL, Option.map_some,
    Option.bind_some, Option.some.injEq]
  funext ch
  simp only [applyF, popOf, upd, List.mem_singleton, List.append_nil]
  by_cases h : ch = i
  · subst h; simp [hv]
  · simp [h]

theorem step_comp2 {rs : List Rule} {l a b o : Nat} {fe : E} (hr : rs[l]? = some (.comp [a, b] o fe))
    {σ : Store Nat Nat} {v w : Nat} {vs ws : List Nat} (hab : a ≠ b) (hv : σ a = v :: vs)
    (hw : σ b = w :: ws) :
    step (graph rs) σ l = some (push (upd (upd σ a vs) b ws) o (fe.eval [v, w])) := by
  rw [step_graph hr]
  simp only [Rule.fire, strictF, heads, hv, hw, Rule.out, natVI, Rule.insL, Option.map_some,
    Option.bind_some, Option.some.injEq]
  funext ch
  simp only [applyF, popOf, push, upd, List.mem_cons, List.not_mem_nil, or_false]
  by_cases h1 : ch = o
  · subst h1
    by_cases h2 : ch = b
    · subst h2; simp [Ne.symm hab, hw]
    · by_cases h3 : ch = a
      · subst h3; simp [hv, h2]
      · simp [h2, h3]
  · by_cases h2 : ch = b
    · subst h2; simp [Ne.symm hab, hw, h1]
    · by_cases h3 : ch = a
      · subst h3; simp [hv, h2, h1]
      · simp [h1, h2, h3]


/-! ## The relation, generically -/

/-- `g` as a function on token values. -/
def G (g : E) (v : Nat) : Nat := g.eval [v]

/-- How a token on channel `ch` of the original graph is seen in the rewritten one: mapped by `g` on the five
ring channels, unchanged elsewhere. -/
def phi (r r0 k nb nx : Nat) (g : E) (ch : Nat) : Nat → Nat :=
  if ch = r ∨ ch = r0 ∨ ch = k ∨ ch = nb ∨ ch = nx then G g else id

/-- Channelwise part of the relation: away from `A` and `B`, the rewritten store is the original mapped by `φ`. -/
def RelC (A B : Nat) (φ : Nat → Nat → Nat) (σ σ' : Store Nat Nat) : Prop :=
  ∀ ch, ch ≠ A → ch ≠ B → σ' ch = (σ ch).map (φ ch)

section RelC
variable {A B o : Nat} {φ : Nat → Nat → Nat} {σ σ' : Store Nat Nat}

theorem relc_upd {l l' : List Nat} (h : RelC A B φ σ σ') (hA : o ≠ A) (hB : o ≠ B) (hl : l' = l.map (φ o)) :
    RelC A B φ (upd σ o l) (upd σ' o l') := by
  intro ch k1 k2
  by_cases e : ch = o
  · subst e; simp [hl]
  · simp [upd, e, h ch k1 k2]

theorem relc_updL {l : List Nat} (h : RelC A B φ σ σ') (ho : o = A ∨ o = B) : RelC A B φ (upd σ o l) σ' := by
  intro ch k1 k2
  have e : ch ≠ o := by rcases ho with rfl | rfl <;> assumption
  simp [upd, e, h ch k1 k2]

theorem relc_updR {l : List Nat} (h : RelC A B φ σ σ') (ho : o = A ∨ o = B) : RelC A B φ σ (upd σ' o l) := by
  intro ch k1 k2
  have e : ch ≠ o := by rcases ho with rfl | rfl <;> assumption
  simp [upd, e, h ch k1 k2]

theorem relc_push {x x' : Nat} (h : RelC A B φ σ σ') (hA : o ≠ A) (hB : o ≠ B) (hx : x' = φ o x) :
    RelC A B φ (push σ o x) (push σ' o x') :=
  relc_upd h hA hB (by rw [h o hA hB, hx]; simp)

theorem relc_applyF {fr : Fire Nat Nat} (h : RelC A B φ σ σ')
    (hfr : ∀ ch, ch ≠ A → ch ≠ B → (fr.2 ch).map (φ ch) = fr.2 ch) :
    RelC A B φ (applyF σ fr) (applyF σ' fr) := by
  intro ch k1 k2
  simp only [applyF]
  rw [h ch k1 k2, List.map_append, hfr ch k1 k2, List.map_drop]

end RelC

/-- The simulation relation between a store `σ` of the original graph and `σ'` of the rewritten one: equal
outside the pattern, `g`-mapped on the ring, nothing on `ne'` in the original, and the original's entry tokens
are, mapped by `g`, the rewritten graph's `ne'` tokens followed by its (not yet converted) `ne` tokens. -/
def Rel (ne ne' r r0 k nb nx : Nat) (g : E) (σ σ' : Store Nat Nat) : Prop :=
  RelC ne ne' (phi r r0 k nb nx g) σ σ' ∧ σ ne' = [] ∧
  (σ ne).map (G g) = σ' ne' ++ (σ' ne).map (G g)

theorem relc_out {ne ne' r r0 k nb nx ch : Nat} {g : E} {σ σ' : Store Nat Nat}
    (h : RelC ne ne' (phi r r0 k nb nx g) σ σ') (hch : ch ∉ [ne, ne', r, r0, k, nb, nx]) : σ' ch = σ ch := by
  simp only [List.mem_cons, List.not_mem_nil, or_false, not_or] at hch
  obtain ⟨a1, a2, a3, a4, a5, a6, a7⟩ := hch
  rw [h ch a1 a2]; simp [phi, a3, a4, a5, a6, a7]

/-! ## The pattern -/

/-- Distinctness of the pattern's channels, unpacked. -/
structure Ne11 (ne ne' r r0 k nb nx sel cnd y c : Nat) : Prop where
  ne_nep : ne ≠ ne'
  ne_r : ne ≠ r
  ne_r0 : ne ≠ r0
  ne_k : ne ≠ k
  ne_nb : ne ≠ nb
  ne_nx : ne ≠ nx
  nep_r : ne' ≠ r
  nep_r0 : ne' ≠ r0
  nep_k : ne' ≠ k
  nep_nb : ne' ≠ nb
  nep_nx : ne' ≠ nx
  r_r0 : r ≠ r0
  r_k : r ≠ k
  r_nb : r ≠ nb
  r_nx : r ≠ nx
  r0_k : r0 ≠ k
  r0_nb : r0 ≠ nb
  r0_nx : r0 ≠ nx
  k_nb : k ≠ nb
  k_nx : k ≠ nx
  nb_nx : nb ≠ nx
  sel_ne : sel ≠ ne
  sel_nep : sel ≠ ne'
  sel_r : sel ≠ r
  sel_r0 : sel ≠ r0
  sel_k : sel ≠ k
  sel_nb : sel ≠ nb
  sel_nx : sel ≠ nx
  cnd_ne : cnd ≠ ne
  cnd_nep : cnd ≠ ne'
  cnd_r : cnd ≠ r
  cnd_r0 : cnd ≠ r0
  cnd_k : cnd ≠ k
  cnd_nb : cnd ≠ nb
  cnd_nx : cnd ≠ nx
  y_ne : y ≠ ne
  y_nep : y ≠ ne'
  y_r : y ≠ r
  y_r0 : y ≠ r0
  y_k : y ≠ k
  y_nb : y ≠ nb
  y_nx : y ≠ nx
  c_ne : c ≠ ne
  c_nep : c ≠ ne'
  c_r : c ≠ r
  c_r0 : c ≠ r0
  c_k : c ≠ k
  c_nb : c ≠ nb
  c_nx : c ≠ nx

set_option hygiene false in
/-- Evaluate nested `upd`/`push` and `phi` at a channel, using every distinctness fact of `N`. -/
macro "rsimp" " [" ts:term,* "]" : tactic => `(tactic| simp [upd, push, phi, N.ne_nep, N.ne_r, N.ne_r0, N.ne_k, N.ne_nb, N.ne_nx, N.nep_r, N.nep_r0, N.nep_k, N.nep_nb, N.nep_nx, N.r_r0, N.r_k, N.r_nb, N.r_nx, N.r0_k, N.r0_nb, N.r0_nx, N.k_nb, N.k_nx, N.nb_nx, N.sel_ne, N.sel_nep, N.sel_r, N.sel_r0, N.sel_k, N.sel_nb, N.sel_nx, N.cnd_ne, N.cnd_nep, N.cnd_r, N.cnd_r0, N.cnd_k, N.cnd_nb, N.cnd_nx, N.y_ne, N.y_nep, N.y_r, N.y_r0, N.y_k, N.y_nb, N.y_nx, N.c_ne, N.c_nep, N.c_r, N.c_r0, N.c_k, N.c_nb, N.c_nx, N.ne_nep.symm, N.ne_r.symm, N.ne_r0.symm, N.ne_k.symm, N.ne_nb.symm, N.ne_nx.symm, N.nep_r.symm, N.nep_r0.symm, N.nep_k.symm, N.nep_nb.symm, N.nep_nx.symm, N.r_r0.symm, N.r_k.symm, N.r_nb.symm, N.r_nx.symm, N.r0_k.symm, N.r0_nb.symm, N.r0_nx.symm, N.k_nb.symm, N.k_nx.symm, N.nb_nx.symm, N.sel_ne.symm, N.sel_nep.symm, N.sel_r.symm, N.sel_r0.symm, N.sel_k.symm, N.sel_nb.symm, N.sel_nx.symm, N.cnd_ne.symm, N.cnd_nep.symm, N.cnd_r.symm, N.cnd_r0.symm, N.cnd_k.symm, N.cnd_nb.symm, N.cnd_nx.symm, N.y_ne.symm, N.y_nep.symm, N.y_r.symm, N.y_r0.symm, N.y_k.symm, N.y_nb.symm, N.y_nx.symm, N.c_ne.symm, N.c_nep.symm, N.c_r.symm, N.c_r0.symm, N.c_k.symm, N.c_nb.symm, N.c_nx.symm, $[$ts:term],*])

theorem ne11 {ne ne' r r0 k nb nx sel cnd y c : Nat} (h : [ne, ne', r, r0, k, nb, nx].Nodup)
    (he : ∀ ch ∈ [sel, cnd, y, c], ch ∉ [ne, ne', r, r0, k, nb, nx]) : Ne11 ne ne' r r0 k nb nx sel cnd y c := by
  simp only [List.nodup_cons, List.mem_cons, List.not_mem_nil, not_or, or_false, List.nodup_nil] at h
  have he' : ∀ ch, ch = sel ∨ ch = cnd ∨ ch = y ∨ ch = c →
      ¬ch = ne ∧ ¬ch = ne' ∧ ¬ch = r ∧ ¬ch = r0 ∧ ¬ch = k ∧ ¬ch = nb ∧ ¬ch = nx := by
    intro ch hch
    have := he ch (by simp only [List.mem_cons, List.not_mem_nil, or_false]; exact hch)
    simpa only [List.mem_cons, List.not_mem_nil, or_false, not_or] using this
  obtain ⟨⟨a1, a2, a3, a4, a5, a6⟩, ⟨b1, b2, b3, b4, b5⟩, ⟨c1, c2, c3, c4⟩, ⟨d1, d2, d3⟩, ⟨e1, e2⟩, f1, -⟩ := h
  obtain ⟨⟨s1, s2, s3, s4, s5, s6, s7⟩, ⟨t1, t2, t3, t4, t5, t6, t7⟩, ⟨u1, u2, u3, u4, u5, u6, u7⟩,
    ⟨v1, v2, v3, v4, v5, v6, v7⟩⟩ :=
    (⟨he' sel (by simp), he' cnd (by simp), he' y (by simp), he' c (by simp)⟩ : _ ∧ _ ∧ _ ∧ _)
  exact ⟨a1, a2, a3, a4, a5, a6, b1, b2, b3, b4, b5, c1, c2, c3, c4, d1, d2, d3, e1, e2, f1,
    s1, s2, s3, s4, s5, s6, s7, t1, t2, t3, t4, t5, t6, t7, u1, u2, u3, u4, u5, u6, u7, v1, v2, v3, v4, v5, v6, v7⟩

/-- The hypotheses. `rs` is any imported graph containing the ring (mux `M`, fork `F`, branch `B`, sink `S`) and
the compare `C`; `rs'` is `rs` with the entry conversion `D` added, the mux reading `ne'`, and the compare
`fC2`; nothing else touches the ring channels or `ne'`, and nothing else reads `ne`. -/
structure Pat (rs rs' : List Rule) (M F B S C D sel ne ne' r r0 k nb nx cnd y c iw : Nat) (fC fC2 g : E) :
    Prop where
  hM : rs[M]? = some (.mux sel [ne, nb] r iw)
  hM' : rs'[M]? = some (.mux sel [ne', nb] r iw)
  hF : rs[F]? = some (.fork r [r0, k])
  hF' : rs'[F]? = some (.fork r [r0, k])
  hB : rs[B]? = some (.branch cnd r0 nb nx)
  hB' : rs'[B]? = some (.branch cnd r0 nb nx)
  hS : rs[S]? = some (.sink nx)
  hS' : rs'[S]? = some (.sink nx)
  hC : rs[C]? = some (.comp [y, k] c fC)
  hC' : rs'[C]? = some (.comp [y, k] c fC2)
  hD : rs[D]? = none
  hD' : rs'[D]? = some (.comp [ne] ne' g)
  hsame : ∀ l, l ≠ M → l ≠ F → l ≠ B → l ≠ S → l ≠ C → l ≠ D → rs'[l]? = rs[l]?
  hins : ∀ l ru, l ≠ M → l ≠ F → l ≠ B → l ≠ S → l ≠ C → rs[l]? = some ru →
    ∀ ch ∈ ru.insL, ch ∉ [ne, ne', r, r0, k, nb, nx]
  houts : ∀ l ru, l ≠ M → l ≠ F → l ≠ B → l ≠ S → l ≠ C → rs[l]? = some ru →
    ∀ ch ∈ ru.outsL, ch ∉ [ne', r, r0, k, nb, nx]
  hnd : [ne, ne', r, r0, k, nb, nx].Nodup
  hext : ∀ ch ∈ [sel, cnd, y, c], ch ∉ [ne, ne', r, r0, k, nb, nx]
  hH : ∀ v w, fC2.eval [v, g.eval [w]] = fC.eval [v, w]

section Pattern

variable {rs rs' : List Rule} {M F B S C D sel ne ne' r r0 k nb nx cnd y c iw : Nat} {fC fC2 g : E}

theorem rel_ring (N : Ne11 ne ne' r r0 k nb nx sel cnd y c) {σ σ' : Store Nat Nat}
    (hR : RelC ne ne' (phi r r0 k nb nx g) σ σ') :
    σ' r = (σ r).map (G g) ∧ σ' r0 = (σ r0).map (G g) ∧ σ' k = (σ k).map (G g) ∧
    σ' nb = (σ nb).map (G g) ∧ σ' nx = (σ nx).map (G g) ∧
    σ' sel = σ sel ∧ σ' cnd = σ cnd ∧ σ' y = σ y ∧ σ' c = σ c := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hR r N.ne_r.symm N.nep_r.symm]; rsimp []
  · rw [hR r0 N.ne_r0.symm N.nep_r0.symm]; rsimp []
  · rw [hR k N.ne_k.symm N.nep_k.symm]; rsimp []
  · rw [hR nb N.ne_nb.symm N.nep_nb.symm]; rsimp []
  · rw [hR nx N.ne_nx.symm N.nep_nx.symm]; rsimp []
  · rw [hR sel N.sel_ne N.sel_nep]; rsimp []
  · rw [hR cnd N.cnd_ne N.cnd_nep]; rsimp []
  · rw [hR y N.y_ne N.y_nep]; rsimp []
  · rw [hR c N.c_ne N.c_nep]; rsimp []

/-! ## The ring and compare rules fire in lockstep -/

/-- Either the rule at `l` is disabled in both graphs, or it fires in both and the relation is kept. -/
def Lock (rs rs' : List Rule) (Rl : Store Nat Nat → Store Nat Nat → Prop) (l : Nat) (σ σ' : Store Nat Nat) :
    Prop :=
  (step (graph rs) σ l = none ∧ step (graph rs') σ' l = none) ∨
  ∃ σ1 σ1', step (graph rs) σ l = some σ1 ∧ step (graph rs') σ' l = some σ1' ∧ Rl σ1 σ1'

theorem lockF (P : Pat rs rs' M F B S C D sel ne ne' r r0 k nb nx cnd y c iw fC fC2 g) {σ σ' : Store Nat Nat}
    (hRel : Rel ne ne' r r0 k nb nx g σ σ') : Lock rs rs' (Rel ne ne' r r0 k nb nx g) F σ σ' := by
  have N := ne11 P.hnd P.hext
  obtain ⟨hR, h0, hE⟩ := hRel
  obtain ⟨er, er0, ek, enb, enx, esel, ecnd, ey, ec⟩ := rel_ring N hR
  cases hv : σ r with
  | nil =>
    exact Or.inl ⟨step_none_strict P.hF (by intro _ _ _ _ h; cases h) (ch := r) (by simp [Rule.insL]) hv,
      step_none_strict P.hF' (by intro _ _ _ _ h; cases h) (ch := r) (by simp [Rule.insL]) (by rw [er, hv]; rfl)⟩
  | cons v vs =>
    have hv' : σ' r = G g v :: vs.map (G g) := by rw [er, hv]; rfl
    exact Or.inr ⟨_, _, step_fork2 P.hF N.r_r0 N.r_k N.r0_k hv, step_fork2 P.hF' N.r_r0 N.r_k N.r0_k hv',
      relc_upd (relc_upd (relc_upd hR N.ne_r.symm N.nep_r.symm (by rsimp []))
        N.ne_r0.symm N.nep_r0.symm (by rsimp [er0])) N.ne_k.symm N.nep_k.symm (by rsimp [ek]),
      by rsimp [h0], by rsimp [hE]⟩

theorem lockB (P : Pat rs rs' M F B S C D sel ne ne' r r0 k nb nx cnd y c iw fC fC2 g) {σ σ' : Store Nat Nat}
    (hRel : Rel ne ne' r r0 k nb nx g σ σ') : Lock rs rs' (Rel ne ne' r r0 k nb nx g) B σ σ' := by
  have N := ne11 P.hnd P.hext
  obtain ⟨hR, h0, hE⟩ := hRel
  obtain ⟨er, er0, ek, enb, enx, esel, ecnd, ey, ec⟩ := rel_ring N hR
  cases hb : σ cnd with
  | nil =>
    exact Or.inl ⟨step_none_strict P.hB (by intro _ _ _ _ h; cases h) (ch := cnd) (by simp [Rule.insL]) hb,
      step_none_strict P.hB' (by intro _ _ _ _ h; cases h) (ch := cnd) (by simp [Rule.insL]) (by rw [ecnd, hb])⟩
  | cons b bs =>
  cases hx : σ r0 with
  | nil =>
    exact Or.inl ⟨step_none_strict P.hB (by intro _ _ _ _ h; cases h) (ch := r0) (by simp [Rule.insL]) hx,
      step_none_strict P.hB' (by intro _ _ _ _ h; cases h) (ch := r0) (by simp [Rule.insL]) (by rw [er0, hx]; rfl)⟩
  | cons x xs =>
    have hb' : σ' cnd = b :: bs := by rw [ecnd, hb]
    have hx' : σ' r0 = G g x :: xs.map (G g) := by rw [er0, hx]; rfl
    obtain ⟨o, ho, hoo⟩ : ∃ o, (if b % 2 = 1 then nb else nx) = o ∧ (o = nb ∨ o = nx) :=
      ⟨_, rfl, by split <;> simp⟩
    refine Or.inr ⟨_, _, step_branch P.hB N.cnd_r0 hb hx ho, step_branch P.hB' N.cnd_r0 hb' hx' ho, ?_⟩
    rcases hoo with rfl | rfl
    · exact ⟨relc_push (relc_upd (relc_upd hR N.cnd_ne N.cnd_nep (by rsimp []))
        N.ne_r0.symm N.nep_r0.symm (by rsimp [])) N.ne_nb.symm N.nep_nb.symm (by rsimp []),
        by rsimp [h0], by rsimp [hE]⟩
    · exact ⟨relc_push (relc_upd (relc_upd hR N.cnd_ne N.cnd_nep (by rsimp []))
        N.ne_r0.symm N.nep_r0.symm (by rsimp [])) N.ne_nx.symm N.nep_nx.symm (by rsimp []),
        by rsimp [h0], by rsimp [hE]⟩

theorem lockS (P : Pat rs rs' M F B S C D sel ne ne' r r0 k nb nx cnd y c iw fC fC2 g) {σ σ' : Store Nat Nat}
    (hRel : Rel ne ne' r r0 k nb nx g σ σ') : Lock rs rs' (Rel ne ne' r r0 k nb nx g) S σ σ' := by
  have N := ne11 P.hnd P.hext
  obtain ⟨hR, h0, hE⟩ := hRel
  obtain ⟨er, er0, ek, enb, enx, esel, ecnd, ey, ec⟩ := rel_ring N hR
  cases hv : σ nx with
  | nil =>
    exact Or.inl ⟨step_none_strict P.hS (by intro _ _ _ _ h; cases h) (ch := nx) (by simp [Rule.insL]) hv,
      step_none_strict P.hS' (by intro _ _ _ _ h; cases h) (ch := nx) (by simp [Rule.insL]) (by rw [enx, hv]; rfl)⟩
  | cons v vs =>
    have hv' : σ' nx = G g v :: vs.map (G g) := by rw [enx, hv]; rfl
    exact Or.inr ⟨_, _, step_sink P.hS hv, step_sink P.hS' hv',
      relc_upd hR N.ne_nx.symm N.nep_nx.symm (by rsimp []), by rsimp [h0], by rsimp [hE]⟩

theorem lockC (P : Pat rs rs' M F B S C D sel ne ne' r r0 k nb nx cnd y c iw fC fC2 g) {σ σ' : Store Nat Nat}
    (hRel : Rel ne ne' r r0 k nb nx g σ σ') : Lock rs rs' (Rel ne ne' r r0 k nb nx g) C σ σ' := by
  have N := ne11 P.hnd P.hext
  obtain ⟨hR, h0, hE⟩ := hRel
  obtain ⟨er, er0, ek, enb, enx, esel, ecnd, ey, ec⟩ := rel_ring N hR
  cases ha : σ y with
  | nil =>
    exact Or.inl ⟨step_none_strict P.hC (by intro _ _ _ _ h; cases h) (ch := y) (by simp [Rule.insL]) ha,
      step_none_strict P.hC' (by intro _ _ _ _ h; cases h) (ch := y) (by simp [Rule.insL]) (by rw [ey, ha])⟩
  | cons a as =>
  cases hw : σ k with
  | nil =>
    exact Or.inl ⟨step_none_strict P.hC (by intro _ _ _ _ h; cases h) (ch := k) (by simp [Rule.insL]) hw,
      step_none_strict P.hC' (by intro _ _ _ _ h; cases h) (ch := k) (by simp [Rule.insL]) (by rw [ek, hw]; rfl)⟩
  | cons w ws =>
    have ha' : σ' y = a :: as := by rw [ey, ha]
    have hw' : σ' k = G g w :: ws.map (G g) := by rw [ek, hw]; rfl
    exact Or.inr ⟨_, _, step_comp2 P.hC N.y_k ha hw, step_comp2 P.hC' N.y_k ha' hw',
      relc_push (relc_upd (relc_upd hR N.y_ne N.y_nep (by rsimp [])) N.ne_k.symm N.nep_k.symm (by rsimp []))
        N.c_ne N.c_nep (by rsimp [G, P.hH]), by rsimp [h0], by rsimp [hE]⟩

/-- Any other rule reads only channels on which the two stores agree, and fires the same way in both. -/
theorem lockO (P : Pat rs rs' M F B S C D sel ne ne' r r0 k nb nx cnd y c iw fC fC2 g) {σ σ' : Store Nat Nat}
    {l : Nat} (lM : l ≠ M) (lF : l ≠ F) (lB : l ≠ B) (lS : l ≠ S) (lC : l ≠ C) (lD : l ≠ D)
    (hRel : Rel ne ne' r r0 k nb nx g σ σ') : Lock rs rs' (Rel ne ne' r r0 k nb nx g) l σ σ' := by
  obtain ⟨hR, h0, hE⟩ := hRel
  have hs := P.hsame l lM lF lB lS lC lD
  cases hr : rs[l]? with
  | none => exact Or.inl ⟨step_graph_none hr σ, step_graph_none (by rw [hs, hr]) σ'⟩
  | some ru =>
    have hr' : rs'[l]? = some ru := by rw [hs]; exact hr
    have hin := P.hins l ru lM lF lB lS lC hr
    have hout := P.houts l ru lM lF lB lS lC hr
    have hag : ∀ ch ∈ ru.insL, σ ch = σ' ch := fun ch hch => (relc_out hR (hin ch hch)).symm
    have nin : ∀ ch ∈ [ne, ne', r, r0, k, nb, nx], ch ∉ ru.insL := fun ch hc hm => hin ch hm hc
    have nout : ∀ ch ∈ [ne', r, r0, k, nb, nx], ch ∉ ru.outsL := fun ch hc hm => hout ch hm hc
    cases hf : ru.fire natVI σ with
    | none =>
      exact Or.inl ⟨by rw [step_graph hr, hf]; rfl, by rw [step_graph hr', ← fire_congr ru hag, hf]; rfl⟩
    | some fr =>
      have hf' : ru.fire natVI σ' = some fr := by rw [← fire_congr ru hag, hf]
      refine Or.inr ⟨_, _, by rw [step_graph hr, hf]; rfl, by rw [step_graph hr', hf']; rfl,
        relc_applyF hR ?_, ?_, ?_⟩
      · intro ch k1 k2
        by_cases hring : ch = r ∨ ch = r0 ∨ ch = k ∨ ch = nb ∨ ch = nx
        · have : ch ∉ ru.outsL := nout ch (by rcases hring with rfl | rfl | rfl | rfl | rfl <;> simp)
          rw [(ru.node natVI).push_outs σ fr ch hf this]; rfl
        · simp [phi, hring]
      · rw [applyF_keep hf (nin ne' (by simp)) (nout ne' (by simp)), h0]
      · have p0 : fr.1 ne = 0 := (ru.node natVI).pop_ins σ fr ne hf (nin ne (by simp))
        rw [applyF_keep hf' (nin ne' (by simp)) (nout ne' (by simp))]
        simp only [applyF, p0, List.drop_zero, List.map_append, hE, List.append_assoc]

/-- Every rule but the mux and the entry conversion fires in lockstep. -/
theorem lockAll (P : Pat rs rs' M F B S C D sel ne ne' r r0 k nb nx cnd y c iw fC fC2 g) {σ σ' : Store Nat Nat}
    {l : Nat} (lM : l ≠ M) (lD : l ≠ D) (hRel : Rel ne ne' r r0 k nb nx g σ σ') :
    Lock rs rs' (Rel ne ne' r r0 k nb nx g) l σ σ' := by
  by_cases lF : l = F
  · subst lF; exact lockF P hRel
  by_cases lB : l = B
  · subst lB; exact lockB P hRel
  by_cases lS : l = S
  · subst lS; exact lockS P hRel
  by_cases lC : l = C
  · subst lC; exact lockC P hRel
  exact lockO P lM lF lB lS lC lD hRel

/-! ## The mux, and the entry conversion -/

/-- The original mux fires; once the rewritten graph has converted every entry token (`σ' ne = []`), its mux
fires the same way (on `ne'` where the original read `ne`). -/
theorem mux_fwd (P : Pat rs rs' M F B S C D sel ne ne' r r0 k nb nx cnd y c iw fC fC2 g) {σ σ' σ1 : Store Nat Nat}
    (hRel : Rel ne ne' r r0 k nb nx g σ σ') (hne : σ' ne = []) (h : step (graph rs) σ M = some σ1) :
    ∃ σ1', step (graph rs') σ' M = some σ1' ∧ Rel ne ne' r r0 k nb nx g σ1 σ1' := by
  have N := ne11 P.hnd P.hext
  obtain ⟨hR, h0, hE⟩ := hRel
  obtain ⟨er, er0, ek, enb, enx, esel, ecnd, ey, ec⟩ := rel_ring N hR
  obtain ⟨v, vs, d, x, xs, hs, hd, -, hx, rfl⟩ := step_mux_inv P.hM h
  have hs' : σ' sel = v :: vs := by rw [esel, hs]
  have hne' : σ' ne' = (σ ne).map (G g) := by rw [hE, hne]; simp
  generalize hj : v % 2 ^ iw = j at hd
  rcases j with _ | _ | j
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hd; subst hd
    have hx' : σ' ne' = G g x :: xs.map (G g) := by rw [hne', hx]; rfl
    exact ⟨_, step_mux P.hM' hs' (by rw [hj]; rfl) N.sel_nep.symm hx',
      relc_push (relc_updR (relc_updL (relc_upd hR N.sel_ne N.sel_nep (by rsimp [])) (Or.inl rfl)) (Or.inr rfl))
        N.ne_r.symm N.nep_r.symm (by rsimp []), by rsimp [h0], by rsimp [hne]⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hd; subst hd
    have hx' : σ' nb = G g x :: xs.map (G g) := by rw [enb, hx]; rfl
    exact ⟨_, step_mux P.hM' hs' (by rw [hj]; rfl) N.sel_nb.symm hx',
      relc_push (relc_upd (relc_upd hR N.sel_ne N.sel_nep (by rsimp [])) N.ne_nb.symm N.nep_nb.symm (by rsimp []))
        N.ne_r.symm N.nep_r.symm (by rsimp []), by rsimp [h0], by rsimp [hE]⟩
  · simp at hd

/-- The rewritten mux fires; the original's fires the same way. -/
theorem mux_bwd (P : Pat rs rs' M F B S C D sel ne ne' r r0 k nb nx cnd y c iw fC fC2 g) {σ σ' σ1' : Store Nat Nat}
    (hRel : Rel ne ne' r r0 k nb nx g σ σ') (h : step (graph rs') σ' M = some σ1') :
    ∃ σ1, step (graph rs) σ M = some σ1 ∧ Rel ne ne' r r0 k nb nx g σ1 σ1' := by
  have N := ne11 P.hnd P.hext
  obtain ⟨hR, h0, hE⟩ := hRel
  obtain ⟨er, er0, ek, enb, enx, esel, ecnd, ey, ec⟩ := rel_ring N hR
  obtain ⟨v, vs, d, x, xs, hs', hd, -, hx, rfl⟩ := step_mux_inv P.hM' h
  have hs : σ sel = v :: vs := by rw [← esel, hs']
  generalize hj : v % 2 ^ iw = j at hd
  rcases j with _ | _ | j
  · simp only [List.getElem?_cons_zero, Option.some.injEq] at hd; subst hd
    cases hn : σ ne with
    | nil => rw [hn, hx] at hE; simp at hE
    | cons x0 xs0 =>
      rw [hn, hx] at hE
      simp only [List.map_cons, List.cons_append, List.cons.injEq] at hE
      obtain ⟨hx0, hxs0⟩ := hE
      subst hx0
      exact ⟨_, step_mux P.hM hs (by rw [hj]; rfl) N.sel_ne.symm hn,
        relc_push (relc_updR (relc_updL (relc_upd hR N.sel_ne N.sel_nep (by rsimp [])) (Or.inl rfl)) (Or.inr rfl))
          N.ne_r.symm N.nep_r.symm (by rsimp []), by rsimp [h0], by rsimp [hxs0]⟩
  · simp only [List.getElem?_cons_succ, List.getElem?_cons_zero, Option.some.injEq] at hd; subst hd
    cases hn : σ nb with
    | nil => rw [enb, hn] at hx; simp at hx
    | cons x0 xs0 =>
      rw [enb, hn] at hx
      simp only [List.map_cons, List.cons.injEq] at hx
      obtain ⟨hx0, hxs0⟩ := hx
      subst hx0 hxs0
      exact ⟨_, step_mux P.hM hs (by rw [hj]; rfl) N.sel_nb.symm hn,
        relc_push (relc_upd (relc_upd hR N.sel_ne N.sel_nep (by rsimp [])) N.ne_nb.symm N.nep_nb.symm (by rsimp []))
          N.ne_r.symm N.nep_r.symm (by rsimp []), by rsimp [h0], by rsimp [hE]⟩
  · simp at hd

/-- The rewritten graph's flush: convert every entry token. -/
theorem flush (P : Pat rs rs' M F B S C D sel ne ne' r r0 k nb nx cnd y c iw fC fC2 g) {σ σ' : Store Nat Nat}
    (hRel : Rel ne ne' r r0 k nb nx g σ σ') :
    ∃ τ n, Run (step (graph rs')) σ' n τ ∧ Rel ne ne' r r0 k nb nx g σ τ ∧ τ ne = [] := by
  have N := ne11 P.hnd P.hext
  obtain ⟨hR, h0, hE⟩ := hRel
  obtain ⟨n, hrun⟩ := drain_comp1 P.hD' N.ne_nep (σ' ne) σ' rfl
  exact ⟨_, n, hrun, ⟨relc_updR (relc_updR hR (Or.inl rfl)) (Or.inr rfl), h0, by rsimp [hE, G]⟩, by rsimp []⟩

/-! ## Forward and backward simulation -/

theorem fwd_step (P : Pat rs rs' M F B S C D sel ne ne' r r0 k nb nx cnd y c iw fC fC2 g) :
    ∀ σ σ' l σ1, Rel ne ne' r r0 k nb nx g σ σ' → step (graph rs) σ l = some σ1 →
      ∃ σ1' n, Run (step (graph rs')) σ' n σ1' ∧ Rel ne ne' r r0 k nb nx g σ1 σ1' := by
  intro σ σ' l σ1 hRel hst
  by_cases lM : l = M
  · subst lM
    obtain ⟨τ, n, hrun, hτ, hτne⟩ := flush P hRel
    obtain ⟨σ1', h1, hR1⟩ := mux_fwd P hτ hτne hst
    exact ⟨σ1', n + 1, run_trans hrun (run_one h1), hR1⟩
  by_cases lD : l = D
  · subst lD; rw [step_graph_none P.hD] at hst; cases hst
  rcases lockAll P lM lD hRel with ⟨h1, -⟩ | ⟨σ1x, σ1', h1, h2, hR1⟩
  · rw [h1] at hst; cases hst
  · rw [h1] at hst; cases hst; exact ⟨σ1', 1, run_one h2, hR1⟩

theorem bwd_step (P : Pat rs rs' M F B S C D sel ne ne' r r0 k nb nx cnd y c iw fC fC2 g) :
    ∀ σ' σ l σ1', Rel ne ne' r r0 k nb nx g σ σ' → step (graph rs') σ' l = some σ1' →
      ∃ σ1 n, Run (step (graph rs)) σ n σ1 ∧ Rel ne ne' r r0 k nb nx g σ1 σ1' := by
  have N := ne11 P.hnd P.hext
  intro σ' σ l σ1' hRel hst
  by_cases lM : l = M
  · subst lM
    obtain ⟨σ1, h1, hR1⟩ := mux_bwd P hRel hst
    exact ⟨σ1, 1, run_one h1, hR1⟩
  by_cases lD : l = D
  · subst lD
    obtain ⟨hR, h0, hE⟩ := hRel
    cases hn : σ' ne with
    | nil => rw [step_comp1_none P.hD' hn] at hst; cases hst
    | cons x xs =>
      rw [step_comp1 P.hD' N.ne_nep hn] at hst; cases hst
      refine ⟨σ, 0, Run.refl _, relc_updR (relc_updR hR (Or.inl rfl)) (Or.inr rfl), h0, ?_⟩
      rw [hE, hn]; rsimp [G]
  rcases lockAll P lM lD hRel with ⟨-, h2⟩ | ⟨σ1, σ1x, h1, h2, hR1⟩
  · rw [h2] at hst; cases hst
  · rw [h2] at hst; cases hst; exact ⟨σ1, 1, run_one h1, hR1⟩

/-- Channels outside the pattern's seven. -/
def Outside (ne ne' r r0 k nb nx ch : Nat) : Prop := ch ∉ [ne, ne', r, r0, k, nb, nx]

theorem fwd_term (P : Pat rs rs' M F B S C D sel ne ne' r r0 k nb nx cnd y c iw fC fC2 g) :
    ∀ t σ', Rel ne ne' r r0 k nb nx g t σ' → Terminal (step (graph rs)) t →
      ∃ τ n, Run (step (graph rs')) σ' n τ ∧ Terminal (step (graph rs')) τ ∧
        ∀ ch, Outside ne ne' r r0 k nb nx ch → τ ch = t ch := by
  intro t σ' hRel ht
  obtain ⟨τ, n, hrun, hτ, hτne⟩ := flush P hRel
  refine ⟨τ, n, hrun, ?_, fun ch hch => relc_out hτ.1 hch⟩
  intro l
  by_cases lM : l = M
  · rw [lM]
    cases h : step (graph rs') τ M with
    | none => rfl
    | some σ1' => obtain ⟨_, h1, -⟩ := mux_bwd P hτ h; rw [ht M] at h1; cases h1
  by_cases lD : l = D
  · subst lD; exact step_comp1_none P.hD' hτne
  rcases lockAll P lM lD hτ with ⟨-, h2⟩ | ⟨_, _, h1, -, -⟩
  · exact h2
  · rw [ht l] at h1; cases h1

theorem bwd_term (P : Pat rs rs' M F B S C D sel ne ne' r r0 k nb nx cnd y c iw fC fC2 g) :
    ∀ t' σ, Rel ne ne' r r0 k nb nx g σ t' → Terminal (step (graph rs')) t' →
      ∃ τ n, Run (step (graph rs)) σ n τ ∧ Terminal (step (graph rs)) τ ∧
        ∀ ch, Outside ne ne' r r0 k nb nx ch → τ ch = t' ch := by
  have N := ne11 P.hnd P.hext
  intro t' σ hRel ht
  have tne : t' ne = [] := term_comp1 P.hD' N.ne_nep ht
  refine ⟨σ, 0, Run.refl _, ?_, fun ch hch => (relc_out hRel.1 hch).symm⟩
  intro l
  by_cases lM : l = M
  · rw [lM]
    cases h : step (graph rs) σ M with
    | none => rfl
    | some σ1 => obtain ⟨_, h2, -⟩ := mux_fwd P hRel tne h; rw [ht M] at h2; cases h2
  by_cases lD : l = D
  · subst lD; exact step_graph_none P.hD σ
  rcases lockAll P lM lD hRel with ⟨h1, -⟩ | ⟨_, _, -, h2, -⟩
  · exact h1
  · rw [ht l] at h2; cases h2

theorem rel_init (P : Pat rs rs' M F B S C D sel ne ne' r r0 k nb nx cnd y c iw fC fC2 g) {σ0 : Store Nat Nat}
    (h0 : ∀ ch ∈ [ne', r, r0, k, nb, nx], σ0 ch = []) : Rel ne ne' r r0 k nb nx g σ0 σ0 := by
  refine ⟨?_, h0 ne' (by simp), by rw [h0 ne' (by simp)]; rfl⟩
  intro ch _ _
  by_cases hring : ch = r ∨ ch = r0 ∨ ch = k ∨ ch = nb ∨ ch = nx
  · rw [h0 ch (by rcases hring with rfl | rfl | rfl | rfl | rfl <;> simp)]; rfl
  · simp [phi, hring]

/-! ## The theorems -/

/-- Every complete run of the original graph, from a store whose ring channels and `ne'` are empty (`ne` may
hold tokens), is matched by a complete run of the rewritten graph that ends in the same store outside the
seven pattern channels. -/
theorem forward (P : Pat rs rs' M F B S C D sel ne ne' r r0 k nb nx cnd y c iw fC fC2 g)
    {σ0 t : Store Nat Nat} {n : Nat} (h0 : ∀ ch ∈ [ne', r, r0, k, nb, nx], σ0 ch = [])
    (hr : Run (step (graph rs)) σ0 n t) (ht : Terminal (step (graph rs)) t) :
    ∃ t' m, Run (step (graph rs')) σ0 m t' ∧ Terminal (step (graph rs')) t' ∧
      ∀ ch, ch ∉ [ne, ne', r, r0, k, nb, nx] → t' ch = t ch :=
  sim_complete (Rel ne ne' r r0 k nb nx g) (fun t t' => ∀ ch, Outside ne ne' r r0 k nb nx ch → t' ch = t ch)
    (fwd_step P) (fwd_term P) hr ht σ0 (rel_init P h0)

/-- Every complete run of the rewritten graph, from such a store, is matched by a complete run of the original
graph that ends in the same store outside the seven pattern channels. -/
theorem backward (P : Pat rs rs' M F B S C D sel ne ne' r r0 k nb nx cnd y c iw fC fC2 g)
    {σ0 t' : Store Nat Nat} {n : Nat} (h0 : ∀ ch ∈ [ne', r, r0, k, nb, nx], σ0 ch = [])
    (hr : Run (step (graph rs')) σ0 n t') (ht : Terminal (step (graph rs')) t') :
    ∃ t m, Run (step (graph rs)) σ0 m t ∧ Terminal (step (graph rs)) t ∧
      ∀ ch, ch ∉ [ne, ne', r, r0, k, nb, nx] → t ch = t' ch :=
  sim_complete (fun σ' σ => Rel ne ne' r r0 k nb nx g σ σ')
    (fun t' t => ∀ ch, Outside ne ne' r r0 k nb nx ch → t ch = t' ch)
    (bwd_step P) (bwd_term P) hr ht σ0 (rel_init P h0)

end Pattern

end Formal.Rewrite.RingMap
