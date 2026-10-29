import Formal.Timing.ChainSettleBridge

/-!
# C-10o2 (2/3): an executable checker for 10o's `Lc`, proved exact

Replaces chainck's untrusted Python interval code (formal/tools/chainck/rulesU.py
`propagate`/`shift`/`norm`) by a Lean function, `sets`, that computes the forced-low set of
every node of a chain network driven by `pulse F T` as a list of half-open intervals, and
proves it EXACT against 10o's `Lc` (`sets_sound`, `sets_complete`): no trust in the
interval code remains. The only runtime side condition is that every computed list is
sorted with gaps (`sepB`), which the checker verifies (`Verdict.sep`).

Per row (one chain, one corner variant) `verdict` computes, by evaluation in the kernel
(`decide`, no `native_decide`):

* `exact` (chainck's PASS): the tail's forced set is ONE interval `[A, B)` with
  `B ≥ F + T + Lr`, `Lr` = lo-sum of the shortest ripple path from the input avoiding the
  side taps (computed here, `lrip`, from the row's tap flags). `exact_sound`: then 10o's
  `Settled z A (F + T + Lr)` and `Lc z t ↔ A ≤ t < B`. `gap_runt`: if instead the set has
  two or more intervals there is a BoundedDelay run with a runt on the tail (10o's
  `runt_of_gap`): the failure is real in that model.
* `bridge` = `SettledPt` (`Lc z (F+T-1)`) ∧ `DAll` (D, forced form, for every chain pin into
  a node with another in-arc). `bridge_sound`: then every INERTIAL run (H_INERTIAL, H_QUIET0)
  has the tail lumped (`ChainSettleBridge.lumped_of_forced`) — O4's H_CHAIN_SETTLED by
  `ChainSettleBridgeO4.genChain_of_check`.

What it does NOT cover: the row DATA (arcs, `[lo, hi]` per variant, `T`) comes from tcheck's
extract.py (untrusted front end: H_NAMES, H_REUSE_CAUSAL for `T`, the prjxray interval
extraction cross-checked by the audit); the late side `T` is a lower bound
(`settledPt_mono`, `dAll_mono`, `settled_mono_T` make a PASS at `T` a PASS for every later
return).

Core Lean only. No sorry/axiom/native_decide.
-/

namespace Formal.Timing.ChainSettleExe
open Formal.Net Formal.Timing Formal.Timing.ChainSettle Formal.Timing.ChainSettleBridge

abbrev Iv := List (Nat × Nat)

/-- Membership in a union of half-open intervals. -/
def memI (L : Iv) (t : Nat) : Prop := ∃ p ∈ L, p.1 ≤ t ∧ t < p.2

theorem memI_nil (t : Nat) : ¬ memI [] t := by rintro ⟨p, hp, _⟩; simp at hp

theorem memI_cons {p : Nat × Nat} {L : Iv} {t : Nat} :
    memI (p :: L) t ↔ (p.1 ≤ t ∧ t < p.2) ∨ memI L t := by
  constructor
  · rintro ⟨q, hq, h⟩
    rcases List.mem_cons.1 hq with rfl | hq
    · exact Or.inl h
    · exact Or.inr ⟨q, hq, h⟩
  · rintro (h | ⟨q, hq, h⟩)
    · exact ⟨p, List.mem_cons_self .., h⟩
    · exact ⟨q, List.mem_cons_of_mem _ hq, h⟩

theorem memI_append {L M : Iv} {t : Nat} : memI (L ++ M) t ↔ memI L t ∨ memI M t := by
  constructor
  · rintro ⟨q, hq, h⟩
    rcases List.mem_append.1 hq with hq | hq
    · exact Or.inl ⟨q, hq, h⟩
    · exact Or.inr ⟨q, hq, h⟩
  · rintro (⟨q, hq, h⟩ | ⟨q, hq, h⟩)
    · exact ⟨q, List.mem_append_left _ hq, h⟩
    · exact ⟨q, List.mem_append_right _ hq, h⟩

/-- Decidable form. -/
def memB (L : Iv) (t : Nat) : Bool := L.any (fun p => decide (p.1 ≤ t) && decide (t < p.2))

theorem memB_iff {L : Iv} {t : Nat} : memB L t = true ↔ memI L t := by
  unfold memB memI; simp [List.any_eq_true]

/-! ## The image of one arc (`lowPin_Ico`) -/

def img (lo hi : Nat) (L : Iv) : Iv :=
  L.filterMap (fun p => if p.1 + hi < p.2 then some (p.1 + hi, p.2 + lo) else none)

theorem memI_img {lo hi : Nat} {L : Iv} {t : Nat} :
    memI (img lo hi L) t ↔ ∃ p ∈ L, p.1 + hi < p.2 ∧ p.1 + hi ≤ t ∧ t < p.2 + lo := by
  unfold memI img
  constructor
  · rintro ⟨q, hq, h⟩
    obtain ⟨p, hp, he⟩ := List.mem_filterMap.1 hq
    by_cases hc : p.1 + hi < p.2
    · simp only [hc, ite_true, Option.some.injEq] at he; subst he; exact ⟨p, hp, hc, h⟩
    · simp [hc] at he
  · rintro ⟨p, hp, h1, h2, h3⟩
    exact ⟨(p.1 + hi, p.2 + lo), List.mem_filterMap.2 ⟨p, hp, by simp [h1]⟩, h2, h3⟩

theorem img_sound {lo hi : Nat} (hlh : lo ≤ hi) {L : Iv} {t : Nat} (h : memI (img lo hi L) t) :
    lowPin lo hi (memI L) t := by
  obtain ⟨p, hp, h1, h2, h3⟩ := memI_img.1 h
  exact lowPin_mono (fun w hw => ⟨p, hp, hw⟩) ((lowPin_Ico hlh p.1 p.2 t).2 ⟨h1, h2, h3⟩)

/-- Sorted, nonempty, separated by at least one point. -/
def sepB : Iv → Bool
  | [] => true
  | [p] => decide (p.1 < p.2)
  | p :: q :: r => decide (p.1 < p.2) && decide (p.2 < q.1) && sepB (q :: r)

theorem sepB_tail {p : Nat × Nat} {L : Iv} (h : sepB (p :: L) = true) : sepB L = true := by
  cases L with
  | nil => rfl
  | cons q r => simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.2

theorem sepB_lower : ∀ {p : Nat × Nat} {L : Iv}, sepB (p :: L) = true →
    ∀ t, memI (p :: L) t → p.1 ≤ t
  | p, [], _, t, h => by
    rcases memI_cons.1 h with h | h
    · exact h.1
    · exact absurd h (memI_nil t)
  | p, q :: r, hs, t, h => by
    simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at hs
    rcases memI_cons.1 h with h | h
    · exact h.1
    · have := sepB_lower (p := q) (L := r) hs.2 t h; omega

theorem img_complete {lo hi : Nat} (hlh : lo ≤ hi) :
    ∀ {L : Iv}, sepB L = true → ∀ t, lowPin lo hi (memI L) t → memI (img lo hi L) t
  | [], _, t, h => by
    obtain ⟨s, _, _, hw⟩ := h
    exact absurd (hw s (Nat.sub_le _ _) (Or.inl (Nat.le_refl _))) (memI_nil s)
  | p :: r, hs, t, h => by
    have hr := sepB_tail hs
    have gap : ∀ w, memI r w → p.2 < w := by
      intro w hw
      cases r with
      | nil => exact absurd hw (memI_nil w)
      | cons q r' =>
        simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at hs
        have := sepB_lower hr w hw; omega
    have h' : lowPin lo hi (fun w => (p.1 ≤ w ∧ w < p.2) ∨ memI r w) t :=
      lowPin_mono (fun w hw => memI_cons.1 hw) h
    rcases (lowPin_union_gap lo hi p.2 _ _ (fun w hw => hw.2) gap t).1 h' with h1 | h1
    · have := (lowPin_Ico hlh p.1 p.2 t).1 h1
      exact memI_img.2 ⟨p, List.mem_cons_self .., this⟩
    · obtain ⟨q, hq, hh⟩ := memI_img.1 (img_complete hlh hr t h1)
      exact memI_img.2 ⟨q, List.mem_cons_of_mem _ hq, hh⟩

/-! ## Normalisation (sort, merge); membership preserved exactly, no side condition -/

def ins (p : Nat × Nat) : Iv → Iv
  | [] => [p]
  | q :: r => if p.1 ≤ q.1 then p :: q :: r else q :: ins p r

def isort : Iv → Iv
  | [] => []
  | p :: r => ins p (isort r)

theorem memI_ins {p : Nat × Nat} : ∀ {L : Iv} {t : Nat},
    memI (ins p L) t ↔ (p.1 ≤ t ∧ t < p.2) ∨ memI L t
  | [], t => by simp only [ins, memI_cons]
  | q :: r, t => by
    unfold ins
    split
    · exact memI_cons
    · rw [memI_cons, memI_ins, memI_cons]
      constructor
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · exact Or.inr (Or.inl h)
        · exact Or.inl h
        · exact Or.inr (Or.inr h)

theorem memI_isort : ∀ {L : Iv} {t : Nat}, memI (isort L) t ↔ memI L t
  | [], _ => Iff.rfl
  | p :: r, t => by
    simp only [isort]; rw [memI_ins, memI_isort, memI_cons]

def mergeAcc (c : Nat × Nat) : Iv → Iv
  | [] => [c]
  | q :: r => if q.1 ≤ c.2 ∧ c.1 ≤ q.2 then mergeAcc (min c.1 q.1, max c.2 q.2) r
      else c :: mergeAcc q r

theorem memI_mergeAcc : ∀ {c : Nat × Nat} {L : Iv} {t : Nat},
    memI (mergeAcc c L) t ↔ (c.1 ≤ t ∧ t < c.2) ∨ memI L t
  | c, [], t => by
    simp only [mergeAcc, memI_cons]
  | c, q :: r, t => by
    unfold mergeAcc
    split
    · next hc =>
      rw [memI_mergeAcc, memI_cons]
      simp only
      constructor
      · rintro (h | h)
        · by_cases h1 : c.1 ≤ t ∧ t < c.2
          · exact Or.inl h1
          · right; left; omega
        · exact Or.inr (Or.inr h)
      · rintro (h | h | h)
        · left; omega
        · left; omega
        · exact Or.inr h
    · rw [memI_cons, memI_mergeAcc, memI_cons]

def normI (L : Iv) : Iv :=
  match isort (L.filter (fun p => decide (p.1 < p.2))) with
  | [] => []
  | p :: r => mergeAcc p r

theorem memI_filter {L : Iv} {t : Nat} :
    memI (L.filter (fun p => decide (p.1 < p.2))) t ↔ memI L t := by
  constructor
  · rintro ⟨q, hq, h⟩; exact ⟨q, (List.mem_filter.1 hq).1, h⟩
  · rintro ⟨q, hq, h⟩
    exact ⟨q, List.mem_filter.2 ⟨hq, by simp; omega⟩, h⟩

theorem memI_normI {L : Iv} {t : Nat} : memI (normI L) t ↔ memI L t := by
  unfold normI
  have e := (memI_isort (L := L.filter (fun p => decide (p.1 < p.2))) (t := t)).trans memI_filter
  split
  · next h => rw [h] at e; exact ⟨fun h' => absurd h' (memI_nil t), fun h' => absurd (e.2 h') (memI_nil t)⟩
  · next p r h => rw [h, memI_cons] at e; rw [memI_mergeAcc]; exact e

/-! ## The network -/

/-- Forced-low set of node `v` from the earlier sets `acc`. -/
def nodeSet (arcs : List Arc) (acc : List Iv) (v : Nat) : Iv :=
  normI ((arcs.filter (fun a => a.dst == v)).flatMap (fun a => img a.lo a.hi (acc.getD a.src [])))

theorem memI_flatMap {arcs : List Arc} {f : Arc → Iv} {t : Nat} :
    memI (arcs.flatMap f) t ↔ ∃ a ∈ arcs, memI (f a) t := by
  constructor
  · rintro ⟨q, hq, h⟩
    obtain ⟨a, ha, hq⟩ := List.mem_flatMap.1 hq
    exact ⟨a, ha, q, hq, h⟩
  · rintro ⟨a, ha, q, hq, h⟩
    exact ⟨q, List.mem_flatMap.2 ⟨a, ha, hq⟩, h⟩

theorem memI_nodeSet {arcs : List Arc} {acc : List Iv} {v t : Nat} :
    memI (nodeSet arcs acc v) t ↔
      ∃ a ∈ arcs, a.dst = v ∧ memI (img a.lo a.hi (acc.getD a.src [])) t := by
  unfold nodeSet
  rw [memI_normI, memI_flatMap]
  constructor
  · rintro ⟨a, ha, h⟩
    obtain ⟨ha, hd⟩ := List.mem_filter.1 ha
    exact ⟨a, ha, by simpa using hd, h⟩
  · rintro ⟨a, ha, hd, h⟩
    exact ⟨a, List.mem_filter.2 ⟨ha, by simpa using hd⟩, h⟩

/-- Build the sets of nodes `v, v+1, …` (fuel `f`) onto `acc`. -/
def build (arcs : List Arc) : List Iv → Nat → Nat → List Iv
  | acc, _, 0 => acc
  | acc, v, f + 1 => build arcs (acc ++ [nodeSet arcs acc v]) (v + 1) f

/-- The forced-low sets of nodes `0 … N`. -/
def sets (arcs : List Arc) (F T N : Nat) : List Iv := build arcs [[(F, F + T)]] 1 N

theorem getD_append_lt {acc : List Iv} {x : Iv} {u : Nat} (h : u < acc.length) :
    (acc ++ [x]).getD u [] = acc.getD u [] := by
  simp [List.getD_eq_getElem?_getD, List.getElem?_append_left h]

theorem getD_append_eq {acc : List Iv} {x : Iv} : (acc ++ [x]).getD acc.length [] = x := by
  simp [List.getD_eq_getElem?_getD]

/-- Invariant of `build`: entry `u` is EXACT for `Lc`. Soundness needs nothing; completeness
needs every earlier entry separated. -/
def Good (net : Netlist) (F T : Nat) (acc : List Iv) : Prop :=
  ∀ u, u < acc.length →
    (∀ t, memI (acc.getD u []) t → Lc net (pulse F T) u t) ∧
    ((∀ u', u' ≤ u → sepB (acc.getD u' []) = true) → ∀ t, Lc net (pulse F T) u t → memI (acc.getD u []) t)

theorem good_init (net : Netlist) (F T : Nat) : Good net F T [[(F, F + T)]] := by
  intro u hu
  have : u = 0 := by simp at hu; omega
  subst this
  simp only [List.getD_cons_zero]
  refine ⟨fun t h => ?_, fun _ t h => ?_⟩
  · rw [Lc_pulse]; rcases memI_cons.1 h with h | h
    · exact h
    · exact absurd h (memI_nil t)
  · rw [Lc_pulse] at h; exact memI_cons.2 (Or.inl h)

theorem good_step {net : Netlist} (hwf : net.WF) {F T : Nat} {acc : List Iv} (hpos : acc.length ≠ 0)
    (hg : Good net F T acc) :
    Good net F T (acc ++ [nodeSet net.arcs acc acc.length]) := by
  intro u hu
  simp only [List.length_append, List.length_singleton] at hu
  by_cases hlt : u < acc.length
  · rw [getD_append_lt hlt]
    refine ⟨(hg u hlt).1, fun hs => (hg u hlt).2 (fun u' hu' => ?_)⟩
    have := hs u' hu'; rwa [getD_append_lt (by omega)] at this
  · have hu' : u = acc.length := by omega
    subst hu'
    rw [getD_append_eq]
    have hv : acc.length ≠ 0 := hpos
    have src_lt : ∀ a ∈ net.arcs, a.dst = acc.length → a.src < acc.length :=
      fun a ha hd => hd ▸ (hwf a ha).1
    refine ⟨fun t h => ?_, fun hs t h => ?_⟩
    · obtain ⟨a, ha, hd, hm⟩ := memI_nodeSet.1 h
      have hl := img_sound (hwf a ha).2 hm
      obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ha
      exact (Lc_pos hwf _ hv t).2 ⟨k, a, hk, hd,
        lowPin_mono (fun w hw => (hg a.src (src_lt a ha hd)).1 w hw) hl⟩
    · obtain ⟨k, a, hk, hd, hl⟩ := (Lc_pos hwf _ hv t).1 h
      have ha := List.mem_of_getElem? hk
      have hsl := src_lt a ha hd
      have hsep : sepB (acc.getD a.src []) = true := by
        have := hs a.src (by omega); rwa [getD_append_lt hsl] at this
      have hcomp : ∀ w, Lc net (pulse F T) a.src w → memI (acc.getD a.src []) w :=
        (hg a.src hsl).2 (fun u' hu' => by have := hs u' (by omega); rwa [getD_append_lt (by omega)] at this)
      exact memI_nodeSet.2 ⟨a, ha, hd, img_complete (hwf a ha).2 hsep t (lowPin_mono hcomp hl)⟩

theorem build_good {net : Netlist} (hwf : net.WF) {F T : Nat} :
    ∀ (f : Nat) (acc : List Iv), acc.length ≠ 0 → Good net F T acc →
      Good net F T (build net.arcs acc acc.length f) ∧
      (build net.arcs acc acc.length f).length = acc.length + f
  | 0, acc, _, hg => ⟨hg, rfl⟩
  | f + 1, acc, hp, hg => by
    simp only [build]
    have hlen : (acc ++ [nodeSet net.arcs acc acc.length]).length = acc.length + 1 := by simp
    have := build_good hwf f (acc ++ [nodeSet net.arcs acc acc.length]) (by rw [hlen]; omega)
      (good_step hwf hp hg)
    rw [hlen] at this
    exact ⟨this.1, by rw [this.2]; omega⟩

theorem sets_good {net : Netlist} (hwf : net.WF) (F T N : Nat) :
    Good net F T (sets net.arcs F T N) ∧ (sets net.arcs F T N).length = N + 1 := by
  have := build_good hwf (F := F) (T := T) N [[(F, F + T)]] (by simp) (good_init net F T)
  simp only [List.length_singleton] at this
  unfold sets
  exact ⟨this.1, by rw [this.2]; omega⟩

/-- **Soundness.** -/
theorem sets_sound {net : Netlist} (hwf : net.WF) {F T N v : Nat} (hv : v ≤ N) {t : Nat}
    (h : memI ((sets net.arcs F T N).getD v []) t) : Lc net (pulse F T) v t :=
  ((sets_good hwf F T N).1 v (by rw [(sets_good hwf F T N).2]; omega)).1 t h

/-- **Completeness** (given the checked separation). -/
theorem sets_complete {net : Netlist} (hwf : net.WF) {F T N v : Nat} (hv : v ≤ N)
    (hs : (sets net.arcs F T N).all sepB = true) {t : Nat} (h : Lc net (pulse F T) v t) :
    memI ((sets net.arcs F T N).getD v []) t := by
  have hlen := (sets_good hwf F T N).2
  refine ((sets_good hwf F T N).1 v (by omega)).2 (fun u' hu' => ?_) t h
  rw [List.all_eq_true] at hs
  have hu : u' < (sets net.arcs F T N).length := by omega
  have := hs _ (List.getElem_mem hu)
  simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu] using this

theorem sets_exact {net : Netlist} (hwf : net.WF) {F T N v : Nat} (hv : v ≤ N)
    (hs : (sets net.arcs F T N).all sepB = true) (t : Nat) :
    memI ((sets net.arcs F T N).getD v []) t ↔ Lc net (pulse F T) v t :=
  ⟨sets_sound hwf hv, sets_complete hwf hv hs⟩

/-! ## Rows and verdicts -/

/-- One chain at one corner variant. Node 0 = the side-tap source, `z` = the tail; nodes
`0 … N`; `taps` = indices of the side-tap arcs out of node 0 (excluded from `Lr`). -/
structure Row where
  arcs : List Arc
  N : Nat
  z : Nat
  F : Nat
  T : Nat
  taps : List Nat
  /-- chainck's `Lrip` (data: the matched ripple length, untrusted; it only sets the target). -/
  Lr : Nat := 0
  /-- optional certificate: the forced-low table (checked locally, `certB`). -/
  S : List Iv := []
  deriving Repr

def Row.net (r : Row) : Netlist := ⟨r.arcs⟩

/-- Arcs with their indices (avoids O(k) list lookups in the kernel). -/
def enumA : Nat → List Arc → List (Nat × Arc)
  | _, [] => []
  | n, a :: l => (n, a) :: enumA (n + 1) l

theorem mem_enumA : ∀ {n : Nat} {l : List Arc} {k : Nat} {a : Arc}, l[k]? = some a → (n + k, a) ∈ enumA n l
  | _, [], _, _, h => by simp at h
  | n, b :: l, 0, a, h => by simp at h; subst h; simp [enumA]
  | n, b :: l, k + 1, a, h => by
    simp only [List.getElem?_cons_succ] at h
    have := mem_enumA (n := n + 1) h
    simp only [enumA, List.mem_cons]
    right; rw [show n + (k + 1) = n + 1 + k by omega]; exact this

theorem fst_enumA : ∀ {n : Nat} {l : List Arc} {p : Nat × Arc}, p ∈ enumA n l → l[p.1 - n]? = some p.2 ∧ n ≤ p.1
  | _, [], _, h => by simp [enumA] at h
  | n, b :: l, p, h => by
    simp only [enumA, List.mem_cons] at h
    rcases h with rfl | h
    · simp
    · have := fst_enumA h
      refine ⟨?_, by omega⟩
      rw [show p.1 - n = (p.1 - (n + 1)) + 1 by omega, List.getElem?_cons_succ]; exact this.1

/-! ## The forced-low table: computed (`sets`) or a certificate checked locally (`certB`)

Kernel evaluation of `sets` on long chains is slow (the kernel reduces call-by-name), so a row
may carry the table `S` itself (computed by the untrusted generator); `certB` checks it
LOCALLY: entry 0 is the input pulse and every entry `v ≥ 1` equals `nodeSet` of the given
table. Since `nodeSet` at `v` reads only entries `< v` (WF), that is the same recursion. -/

def chkFrom (arcs : List Arc) (S : List Iv) : Nat → List Iv → Bool
  | _, [] => true
  | v, x :: xs => (x == nodeSet arcs S v) && chkFrom arcs S (v + 1) xs

theorem chkFrom_spec {arcs : List Arc} {S : List Iv} :
    ∀ {v : Nat} {xs : List Iv}, chkFrom arcs S v xs = true →
      ∀ i (h : i < xs.length), xs[i] = nodeSet arcs S (v + i)
  | _, [], _, i, h => by simp at h
  | v, x :: xs, hc, i, h => by
    simp only [chkFrom, Bool.and_eq_true, beq_iff_eq] at hc
    cases i with
    | zero => simpa using hc.1
    | succ i =>
      have := chkFrom_spec hc.2 i (by simpa using h)
      simp only [List.getElem_cons_succ]; rw [this]; congr 1; omega

def certB (r : Row) : Bool :=
  r.S.length == r.N + 1 &&
    (match r.S with
     | x :: xs => (x == [(r.F, r.F + r.T)]) && chkFrom r.arcs r.S 1 xs
     | [] => false)

/-- The table the verdict uses. -/
def table (r : Row) : List Iv := if certB r then r.S else sets r.arcs r.F r.T r.N

theorem cert_entry {r : Row} (hc : certB r = true) :
    r.S.getD 0 [] = [(r.F, r.F + r.T)] ∧ r.S.length = r.N + 1 ∧
    ∀ v, 1 ≤ v → v ≤ r.N → r.S.getD v [] = nodeSet r.arcs r.S v := by
  unfold certB at hc
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨hl, hm⟩ := hc
  match hS : r.S, hm with
  | x :: xs, hm =>
    simp only [Bool.and_eq_true, beq_iff_eq] at hm
    rw [hS] at hl
    refine ⟨by simpa using hm.1, by simpa using hl, fun v h1 h2 => ?_⟩
    have hv : v - 1 < xs.length := by simp at hl; omega
    have := chkFrom_spec hm.2 (v - 1) hv
    rw [show 1 + (v - 1) = v by omega] at this
    rw [← hS] at this
    simp only [List.getD_eq_getElem?_getD, List.getElem?_cons]
    rw [show v = (v - 1) + 1 by omega]
    simp only [Nat.add_one_ne_zero, ↓reduceIte, Nat.add_sub_cancel, List.getElem?_eq_getElem hv,
      Option.getD_some]
    rw [show v - 1 + 1 = v by omega]; exact this

theorem cert_good {net : Netlist} (hwf : net.WF) {r : Row} (hn : r.net = net) (hc : certB r = true)
    (hN : ∀ a ∈ net.arcs, a.dst ≤ r.N) :
    ∀ v, v ≤ r.N →
      (∀ t, memI (r.S.getD v []) t → Lc net (pulse r.F r.T) v t) ∧
      ((∀ u, u ≤ v → sepB (r.S.getD u []) = true) → ∀ t, Lc net (pulse r.F r.T) v t → memI (r.S.getD v []) t) := by
  obtain ⟨h0, _, hstep⟩ := cert_entry hc
  have harcs : r.arcs = net.arcs := by rw [← hn]; rfl
  intro v
  induction v using Nat.strongRecOn with
  | ind v ih =>
    intro hv
    by_cases hv0 : v = 0
    · subst hv0
      rw [h0]
      refine ⟨fun t h => ?_, fun _ t h => ?_⟩
      · rw [Lc_pulse]; rcases memI_cons.1 h with h | h
        · exact h
        · exact absurd h (memI_nil t)
      · rw [Lc_pulse] at h; exact memI_cons.2 (Or.inl h)
    · rw [hstep v (by omega) hv, harcs]
      have src_lt : ∀ a ∈ net.arcs, a.dst = v → a.src < v := fun a ha hd => hd ▸ (hwf a ha).1
      refine ⟨fun t h => ?_, fun hs t h => ?_⟩
      · obtain ⟨a, ha, hd, hm⟩ := memI_nodeSet.1 h
        have hl := img_sound (hwf a ha).2 hm
        obtain ⟨k, hk⟩ := List.mem_iff_getElem?.1 ha
        have hlt := src_lt a ha hd
        exact (Lc_pos hwf _ hv0 t).2 ⟨k, a, hk, hd,
          lowPin_mono (fun w hw => (ih a.src hlt (by omega)).1 w hw) hl⟩
      · obtain ⟨k, a, hk, hd, hl⟩ := (Lc_pos hwf _ hv0 t).1 h
        have ha := List.mem_of_getElem? hk
        have hlt := src_lt a ha hd
        have hsep : sepB (r.S.getD a.src []) = true := hs a.src (by omega)
        have hcomp := (ih a.src hlt (by omega)).2 (fun u hu => hs u (by omega))
        exact memI_nodeSet.2 ⟨a, ha, hd, img_complete (hwf a ha).2 hsep t (lowPin_mono hcomp hl)⟩

theorem all_sepB_getD {S : List Iv} (h : S.all sepB = true) (u : Nat) : sepB (S.getD u []) = true := by
  rw [List.all_eq_true] at h
  by_cases hu : u < S.length
  · simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu] using h _ (List.getElem_mem hu)
  · simp [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega : S.length ≤ u), sepB]

/-- **The table is exact** (sound always; complete given the checked separation). -/
theorem table_exact {r : Row} (hwf : r.net.WF) (hN : ∀ a ∈ r.arcs, a.dst ≤ r.N) {v : Nat} (hv : v ≤ r.N) :
    (∀ t, memI ((table r).getD v []) t → Lc r.net (pulse r.F r.T) v t) ∧
    ((table r).all sepB = true → ∀ t, Lc r.net (pulse r.F r.T) v t → memI ((table r).getD v []) t) := by
  unfold table
  split
  · next hc =>
    have := cert_good hwf rfl hc hN v hv
    exact ⟨this.1, fun hs => this.2 (fun u _ => all_sepB_getD hs u)⟩
  · exact ⟨fun t h => sets_sound (net := r.net) hwf hv h, fun hs t h => sets_complete (net := r.net) hwf hv hs h⟩

def wfB (r : Row) : Bool := r.arcs.all (fun a => decide (a.src < a.dst) && decide (a.lo ≤ a.hi))
  && r.arcs.all (fun a => decide (a.dst ≤ r.N))

theorem wfB_wf {r : Row} (h : wfB r = true) : r.net.WF := by
  intro a ha
  unfold wfB at h
  simp only [Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at h
  exact h.1 a ha

/-- `w` has an in-arc other than index `k` (decidable form of `OtherIn`). -/
def otherB (r : Row) (k w : Nat) : Bool :=
  (enumA 0 r.arcs).any (fun p => decide (p.1 ≠ k) && decide (p.2.dst = w))

theorem otherB_of {r : Row} {k w : Nat} (h : OtherIn r.net k w) : otherB r k w = true := by
  obtain ⟨k', a', hk', hd, hne⟩ := h
  unfold otherB
  rw [List.any_eq_true]
  have hm := mem_enumA (n := 0) (l := r.arcs) hk'
  rw [Nat.zero_add] at hm
  exact ⟨(k', a'), hm, by simp [hne, hd]⟩

/-- The end of the interval of `W` that contains `x` (or `x` if none). -/
def coverEnd (W : Iv) (x : Nat) : Nat :=
  match W.find? (fun p => decide (p.1 ≤ x) && decide (x < p.2)) with
  | some p => p.2
  | none => x

theorem coverEnd_ge (W : Iv) (x : Nat) : x ≤ coverEnd W x := by
  unfold coverEnd
  split
  · next p h =>
    have := List.find?_some h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this; omega
  · exact Nat.le_refl _

theorem coverEnd_cov (W : Iv) (x : Nat) : ∀ τ, x ≤ τ → τ < coverEnd W x → memI W τ := by
  intro τ h1 h2
  unfold coverEnd at h2
  split at h2
  · next p h =>
    have hm := List.mem_of_find?_eq_some h
    have := List.find?_some h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact ⟨p, hm, by omega, h2⟩
  · omega

/-- D for arc `a` (chain pin), decided: some image interval of the pin meets
`[F + T, coverEnd W (F+T)]`, `W` = the destination's set. -/
def dB (S : List Iv) (F T : Nat) (a : Arc) : Bool :=
  (img a.lo a.hi (S.getD a.src [])).any (fun q =>
    decide (max (F + T) q.1 ≤ coverEnd (S.getD a.dst []) (F + T)) && decide (max (F + T) q.1 < q.2))

def dAllB (r : Row) (S : List Iv) : Bool :=
  (enumA 0 r.arcs).all (fun p => !(decide (p.2.src ≠ 0) && otherB r p.1 p.2.dst) || dB S r.F r.T p.2)

/-- The verdict of one row. -/
structure Verdict where
  wf : Bool
  sep : Bool
  nint : Nat          -- number of intervals of the tail's forced set
  A : Nat
  B : Nat
  Lr : Nat
  exact : Bool        -- chainck's PASS: one interval, B ≥ F + T + Lr
  s1 : Bool           -- SettledPt
  d : Bool            -- DAll
  deriving Repr, DecidableEq

def verdict (r : Row) : Verdict :=
  let S := sets r.arcs r.F r.T r.N
  let Z := S.getD r.z []
  let Lr := lrip r
  { wf := wfB r && decide (1 ≤ r.T) && decide (1 ≤ r.F) && decide (r.z ≠ 0) && decide (r.z ≤ r.N)
    sep := S.all sepB
    nint := Z.length
    A := (Z.headD (0, 0)).1
    B := (Z.headD (0, 0)).2
    Lr := Lr
    exact := match Z with
      | [p] => decide (r.F + r.T + Lr ≤ p.2)
      | _ => false
    s1 := memB Z (r.F + r.T - 1)
    d := dAllB r S }

def Verdict.bridge (v : Verdict) : Bool := v.wf && v.s1 && v.d

theorem wf_parts {r : Row} {v : Verdict} (hv : verdict r = v) (hw : v.wf = true) :
    r.net.WF ∧ 1 ≤ r.T ∧ 1 ≤ r.F ∧ r.z ≠ 0 ∧ r.z ≤ r.N := by
  subst hv
  simp only [verdict, Bool.and_eq_true, decide_eq_true_eq] at hw
  exact ⟨wfB_wf hw.1.1.1.1, hw.1.1.1.2, hw.1.1.2, hw.1.2, hw.2⟩

/-- **Exact PASS is 10o's `Settled`** (and the tail's forced set is exactly `[A, B)`). -/
theorem exact_sound {r : Row} {v : Verdict} (hv : verdict r = v) (hw : v.wf = true)
    (hs : v.sep = true) (he : v.exact = true) :
    Settled r.net (pulse r.F r.T) r.z v.A (r.F + r.T + v.Lr) ∧
    (∀ t, Lc r.net (pulse r.F r.T) r.z t ↔ v.A ≤ t ∧ t < v.B) := by
  obtain ⟨hwf, _, _, _, hzN⟩ := wf_parts hv hw
  have hs' : (sets r.net.arcs r.F r.T r.N).all sepB = true := by subst hv; exact hs
  have ex : ∀ t, memI ((sets r.arcs r.F r.T r.N).getD r.z []) t ↔ Lc r.net (pulse r.F r.T) r.z t :=
    sets_exact (net := r.net) hwf hzN hs'
  subst hv
  simp only [verdict] at he ⊢
  generalize hZ : (sets r.arcs r.F r.T r.N).getD r.z [] = Z at he ex ⊢
  match Z, he with
  | [p], he =>
    simp only [decide_eq_true_eq] at he
    have key : ∀ t, Lc r.net (pulse r.F r.T) r.z t ↔ p.1 ≤ t ∧ t < p.2 := by
      intro t
      rw [← ex t, memI_cons]
      exact ⟨fun h => h.elim id (fun h => absurd h (memI_nil t)), Or.inl⟩
    refine ⟨fun t h1 h2 => (key t).2 ⟨?_, ?_⟩, fun t => ?_⟩
    · exact h1
    · omega
    · exact key t

/-- **A gap is a real runt** (in the BoundedDelay model, 10o's `runt_of_gap`). -/
theorem gap_runt {r : Row} {v : Verdict} (hv : verdict r = v) (hw : v.wf = true)
    (hs : v.sep = true) (hn : 2 ≤ v.nint) :
    ∃ x t y, x < t ∧ t < y ∧ ∃ sig, ∃ _r : AndRun r.net (pulse r.F r.T) sig,
      sig r.z x = false ∧ sig r.z t = true ∧ sig r.z y = false := by
  obtain ⟨hwf, _, _, _, hzN⟩ := wf_parts hv hw
  have hs' : (sets r.net.arcs r.F r.T r.N).all sepB = true := by subst hv; exact hs
  have ex := sets_exact (net := r.net) hwf hzN hs'
  have hsepZ : sepB ((sets r.net.arcs r.F r.T r.N).getD r.z []) = true := by
    rw [List.all_eq_true] at hs'
    have hlen := (sets_good hwf r.F r.T r.N).2
    have hu : r.z < (sets r.net.arcs r.F r.T r.N).length := by omega
    have := hs' _ (List.getElem_mem hu)
    simpa [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hu] using this
  subst hv
  simp only [verdict] at hn
  generalize hZ : (sets r.net.arcs r.F r.T r.N).getD r.z [] = Z at ex hsepZ
  have hZ' : (sets r.arcs r.F r.T r.N).getD r.z [] = Z := hZ
  rw [hZ'] at hn
  match Z, hn, hsepZ with
  | p :: q :: rest, _, hsepZ =>
    simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at hsepZ
    have hq1 : q.1 < q.2 := by
      cases rest with
      | nil => simpa [sepB] using hsepZ.2
      | cons _ _ => simp only [sepB, Bool.and_eq_true, decide_eq_true_eq] at hsepZ; exact hsepZ.2.1.1
    have hx : Lc r.net (pulse r.F r.T) r.z p.1 :=
      (ex p.1).1 (memI_cons.2 (Or.inl ⟨Nat.le_refl _, hsepZ.1.1⟩))
    have hy : Lc r.net (pulse r.F r.T) r.z q.1 :=
      (ex q.1).1 (memI_cons.2 (Or.inr (memI_cons.2 (Or.inl ⟨Nat.le_refl _, hq1⟩))))
    have ht : ¬ Lc r.net (pulse r.F r.T) r.z p.2 := by
      intro h
      have hm := (ex p.2).2 h
      have := sepB_lower (p := p) (L := q :: rest) (by
        simp only [sepB, Bool.and_eq_true, decide_eq_true_eq]; exact ⟨⟨hsepZ.1.1, hsepZ.1.2⟩, hsepZ.2⟩) p.2 hm
      rcases memI_cons.1 hm with h1 | h1
      · omega
      · have := sepB_lower (p := q) (L := rest) hsepZ.2 p.2 h1; omega
    obtain ⟨sig, rr, h1, h2, h3⟩ := runt_of_gap hwf hx hy ht
    exact ⟨p.1, p.2, q.1, hsepZ.1.1, hsepZ.1.2, sig, rr, h1, h2, h3⟩

/-- **Bridge PASS gives the forced conditions of `lumped_of_forced`.** -/
theorem bridge_sound {r : Row} {v : Verdict} (hv : verdict r = v) (hb : v.bridge = true) :
    r.net.WF ∧ 1 ≤ r.T ∧ 1 ≤ r.F ∧ r.z ≠ 0 ∧
    SettledPt r.net r.F r.T r.z ∧ DAll r.net r.F r.T := by
  simp only [Verdict.bridge, Bool.and_eq_true] at hb
  obtain ⟨⟨hw, h1⟩, hd⟩ := hb
  obtain ⟨hwf, hT, hF, hz, hzN⟩ := wf_parts hv hw
  refine ⟨hwf, hT, hF, hz, ?_, ?_⟩
  · subst hv
    exact sets_sound hwf hzN (memB_iff.1 h1)
  · intro k a hk ha ho
    have hdd : dAllB r (sets r.arcs r.F r.T r.N) = true := by subst hv; exact hd
    unfold dAllB at hdd
    rw [List.all_eq_true] at hdd
    have hm := mem_enumA (n := 0) (l := r.arcs) (hk : r.arcs[k]? = some a)
    rw [Nat.zero_add] at hm
    have := hdd _ hm
    have hob := otherB_of ho
    simp only [ha, ne_eq, not_false_eq_true, decide_true, hob, Bool.and_self, Bool.not_true,
      Bool.false_or] at this
    unfold dB at this
    rw [List.any_eq_true] at this
    obtain ⟨q, hq, hc⟩ := this
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hc
    have hwfa := (hwf a (List.mem_of_getElem? hk)).2
    have hsrc : a.src ≤ r.N := by
      have := (hwf a (List.mem_of_getElem? hk)).1
      have hdN : a.dst ≤ r.N := by
        subst hv
        simp only [verdict, wfB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hw
        exact hw.1.1.1.1.2 a (List.mem_of_getElem? hk)
      omega
    have hdN : a.dst ≤ r.N := by
      subst hv
      simp only [verdict, wfB, Bool.and_eq_true, List.all_eq_true, decide_eq_true_eq] at hw
      exact hw.1.1.1.1.2 a (List.mem_of_getElem? hk)
    refine ⟨max (r.F + r.T) q.1, Nat.le_max_left _ _, ?_, fun τ b1 b2 => ?_⟩
    · have hm : memI (img a.lo a.hi ((sets r.arcs r.F r.T r.N).getD a.src [])) (max (r.F + r.T) q.1) :=
        ⟨q, hq, Nat.le_max_right _ _, hc.2⟩
      exact lowPin_mono (fun w hw => sets_sound hwf hsrc hw) (img_sound hwfa hm)
    · exact sets_sound hwf hdN (coverEnd_cov _ _ τ b1 (Nat.lt_of_lt_of_le b2 hc.1))

end Formal.Timing.ChainSettleExe
