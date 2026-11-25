import Formal.Target.Spec
import Mathlib.Tactic.NormNum

/-!
# Formal.Target.Witness — checking a concrete behaviour against `Spec.GateOK`

Shard A, 2026-11-01, for a Lean-checked counterexample (THE goal: "a counterexample is a
result"). A behaviour is given finitely: every node's signal is its value at time 0 and the
sorted list of times at which it flips (`SD`). A gate is checked with one fixed delay per pin
(`f i t = t - d i`, transport) by walking the segments between breakpoints (`chkFrom`), and
`chkFrom_sound` turns a successful check into the gate equation on the checked window.

Eventually periodic behaviours (the target has a free-running ring oscillator) are handled by
`ext`: the description holds up to `b`, and from `b` on the signal repeats with period `P`.

What is proved here: soundness of the check (a passing check gives the equation of
`Spec.GateOK` at every checked time), and the delay lemma `adm_slow` (at the slow corner,
`g = 1`, `κ = 0`, a delay in `[smin, smax]` with `fmin ≤ smin` is admissible). Nothing here
is about the target yet.
-/

namespace Formal.Target.Wit
open Formal.Target

/-- A signal description: the value at time 0 and the times (in ps) at which the value flips. -/
structure SD where
  v0 : Bool
  ts : List Nat
  deriving Repr, Inhabited

/-- Number of flips at times `≤ t`. -/
def SD.cnt (d : SD) (t : Nat) : Nat := (d.ts.filter fun x => decide (x ≤ t)).length

/-- The value at time `t`. -/
def SD.val (d : SD) (t : Nat) : Bool := d.v0 ^^ (d.cnt t % 2 == 1)

theorem filter_le_eq (l : List Nat) (t s : Nat) (hts : t ≤ s) (h : ∀ x ∈ l, t < x → s < x) :
    l.filter (fun x => decide (x ≤ s)) = l.filter (fun x => decide (x ≤ t)) := by
  induction l with
  | nil => rfl
  | cons y l ih =>
    have ih' := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    have hy := h y List.mem_cons_self
    by_cases h1 : y ≤ t
    · have h2 : y ≤ s := Nat.le_trans h1 hts
      simp [h1, h2, ih']
    · have h2 : ¬ y ≤ s := by omega
      simp [h1, h2, ih']

/-- A signal is constant from `t` to `s` if it has no flip in `(t, s]`. -/
theorem SD.val_const (d : SD) {t s : Nat} (hts : t ≤ s) (h : ∀ x ∈ d.ts, t < x → s < x) :
    d.val s = d.val t := by
  unfold SD.val SD.cnt; rw [filter_le_eq d.ts t s hts h]

/-- The first flip strictly after `t`, capped at `cap`. -/
def nextAfter (l : List Nat) (t cap : Nat) : Nat :=
  l.foldr (fun x m => if t < x ∧ x < m then x else m) cap

theorem nextAfter_le (l : List Nat) (t cap : Nat) : nextAfter l t cap ≤ cap := by
  induction l with
  | nil => exact Nat.le_refl _
  | cons x l ih =>
    simp only [nextAfter, List.foldr_cons] at ih ⊢
    split <;> omega

theorem nextAfter_gt (l : List Nat) (t cap : Nat) (hc : t < cap) : t < nextAfter l t cap := by
  induction l with
  | nil => exact hc
  | cons x l ih =>
    simp only [nextAfter, List.foldr_cons] at ih ⊢
    split <;> omega

/-- No element of `l` lies in `(t, nextAfter l t cap)`. -/
theorem nextAfter_gap (l : List Nat) (t cap : Nat) :
    ∀ x ∈ l, t < x → nextAfter l t cap ≤ x := by
  induction l with
  | nil => intro x hx; cases hx
  | cons y l ih =>
    intro x hx htx
    simp only [nextAfter, List.foldr_cons] at ih ⊢
    rcases List.mem_cons.1 hx with rfl | hx
    · split <;> omega
    · have := ih x hx htx; split <;> omega

/-! ## One gate with fixed pin delays -/

/-- A behaviour from descriptions: node `n` reads `D n`. -/
def beh (D : Nat → SD) : Beh := fun n t => (D n).val t

/-- The right-hand side of the gate equation at `t`, pin `i` read at `t - ds i`. -/
def rhs (x : Beh) (g : Gate) (ds : Nat → Nat) (t : Nat) : Bool :=
  g.init.testBit (addr g.k fun i => x (g.ins.getD i 0) (t - ds i))

/-- All breakpoints that matter for the gate: flips of the output, and flips of each input
shifted by that pin's delay. -/
def bpts (D : Nat → SD) (g : Gate) (ds : Nat → Nat) : List Nat :=
  (D g.out).ts ++ ((List.range g.k).flatMap fun i => ((D (g.ins.getD i 0)).ts.map (· + ds i)))

/-- Walk the segments of `[t, b)`: compare both sides at the left end of each segment. -/
def chkFrom (D : Nat → SD) (g : Gate) (ds : Nat → Nat) (b : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, t =>
    if b ≤ t then true
    else ((D g.out).val t == rhs (beh D) g ds t) &&
      chkFrom D g ds b fuel (nextAfter (bpts D g ds) t b)

theorem addr_congr (k : Nat) (v w : Nat → Bool) (h : ∀ i, i < k → v i = w i) : addr k v = addr k w := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [addr]
    rw [ih (fun i hi => h i (Nat.lt_succ_of_lt hi)), h k (Nat.lt_succ_self k)]

/-- Both sides are constant on a segment `[t, s]` with no breakpoint in `(t, s]`. -/
theorem seg_const (D : Nat → SD) (g : Gate) (ds : Nat → Nat) {t s : Nat} (hts : t ≤ s)
    (h : ∀ x ∈ bpts D g ds, t < x → s < x) :
    (D g.out).val s = (D g.out).val t ∧ rhs (beh D) g ds s = rhs (beh D) g ds t := by
  refine ⟨(D g.out).val_const hts (fun x hx => h x (List.mem_append_left _ hx)), ?_⟩
  unfold rhs
  congr 1
  apply addr_congr
  intro i hi
  simp only [beh]
  by_cases hd : s < ds i
  · have : t < ds i := by omega
    rw [show s - ds i = 0 by omega, show t - ds i = 0 by omega]
  · apply SD.val_const _ (by omega)
    intro x hx htx
    have hm : x + ds i ∈ bpts D g ds := by
      apply List.mem_append_right
      exact List.mem_flatMap.2 ⟨i, List.mem_range.2 hi, List.mem_map.2 ⟨x, hx, rfl⟩⟩
    have := h _ hm (by omega)
    omega

/-- **Soundness of the segment walk.** -/
theorem chkFrom_sound (D : Nat → SD) (g : Gate) (ds : Nat → Nat) (b : Nat) :
    ∀ fuel t, chkFrom D g ds b fuel t = true → ∀ s, t ≤ s → s < b →
      (D g.out).val s = rhs (beh D) g ds s := by
  intro fuel
  induction fuel with
  | zero => intro t h; simp [chkFrom] at h
  | succ fuel ih =>
    intro t h s hts hsb
    simp only [chkFrom] at h
    split at h
    · omega
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      let n := nextAfter (bpts D g ds) t b
      by_cases hs : s < n
      · have hgap : ∀ x ∈ bpts D g ds, t < x → s < x := fun x hx htx => by
          have := nextAfter_gap _ t b x hx htx; omega
        obtain ⟨e1, e2⟩ := seg_const D g ds hts hgap
        rw [e1, e2]; exact h.1
      · exact ih n h.2 s (by omega) hsb

/-! ## Lookup: a balanced range tree from node index to description -/

inductive BT where
  | leaf (v : SD)
  | node (mid : Nat) (l r : BT)
  deriving Inhabited

def BT.find : BT → Nat → SD
  | .leaf v, _ => v
  | .node m l r, n => if n < m then l.find n else r.find n

/-! ## Eventually periodic behaviours -/

/-- From `b` on, repeat the last period `[b - P, b)`. -/
def wrap (b P t : Nat) : Nat := if t < b then t else b - P + (t - (b - P)) % P

/-- The behaviour of a description table, extended periodically from `b` on. -/
def ext (D : Nat → SD) (b P : Nat) : Beh := fun n t => (D n).val (wrap b P t)

theorem wrap_lt {b P t : Nat} (h : t < b) : wrap b P t = t := by simp [wrap, h]

theorem wrap_per {b P t : Nat} (hP : 0 < P) (hPb : P ≤ b) (h : b ≤ t) :
    wrap b P t = wrap b P (t - P) := by
  unfold wrap
  rw [if_neg (by omega)]
  by_cases h2 : t - P < b
  · rw [if_pos h2]
    have e : t - (b - P) = (t - P - (b - P)) + P := by omega
    rw [e, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
    omega
  · rw [if_neg h2]
    have e : t - (b - P) = (t - P - (b - P)) + P := by omega
    rw [e, Nat.add_mod_right]

/-- A description repeats with period `P` on `[lo, b)`. -/
def PerOn (d : SD) (P lo b : Nat) : Prop := ∀ s, lo ≤ s → s < b → d.val s = d.val (s - P)

/-- With `PerOn` from `b - Dm` on, the extended signal repeats with period `P` from `b - Dm` on. -/
theorem ext_per (D : Nat → SD) {b P Dm n s : Nat} (hP : 0 < P) (hPb : P + Dm ≤ b)
    (hper : PerOn (D n) P (b - Dm) b) (hs : b - Dm ≤ s) :
    ext D b P n s = ext D b P n (s - P) := by
  unfold ext
  by_cases h : s < b
  · rw [wrap_lt h, wrap_lt (by omega)]; exact hper s hs h
  · rw [wrap_per hP (by omega) (by omega)]

/-- Below `b`, the extension is the description. -/
theorem ext_lt (D : Nat → SD) {b P n s : Nat} (h : s < b) : ext D b P n s = (D n).val s := by
  simp [ext, wrap_lt h]

theorem getD_mem {α : Type} (l : List α) (d : α) {i : Nat} (hi : i < l.length) : l.getD i d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; exact List.getElem_mem hi

theorem getD_eq {α : Type} (l : List α) (d : α) {i : Nat} (hi : i < l.length) : l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem hi]; rfl

/-- The longest delay of a gate's arcs (slow end). -/
def _root_.Formal.Target.Gate.dmax (g : Gate) : Nat := (g.arcs.map Arc.smax).foldr max 0

theorem le_dmax (g : Gate) (i : Nat) (hi : i < g.arcs.length) : (g.arcs.getD i default).smax ≤ g.dmax := by
  unfold Gate.dmax
  have hm : (g.arcs.getD i default).smax ∈ g.arcs.map Arc.smax := by
    exact List.mem_map.2 ⟨_, getD_mem _ _ hi, rfl⟩
  generalize g.arcs.map Arc.smax = l at hm
  induction l with
  | nil => cases hm
  | cons x l ih =>
    simp only [List.foldr_cons]
    rcases List.mem_cons.1 hm with h | h
    · omega
    · have := ih h; omega

/-- The witness's pin delays: the slow end of every arc. -/
def dsl (g : Gate) (i : Nat) : Nat := (g.arcs.getD i default).smax

/-- **The equation of a gate holds for the extended behaviour at every `t ≥ lo`**, from a
segment check on `[lo, b)` and the periodicity of its nodes from `b - Dm` on. -/
theorem eq_ext (D : Nat → SD) (g : Gate) {b P Dm lo fuel : Nat} (hP : 0 < P) (hPb : P + Dm ≤ b)
    (hlo : lo + P ≤ b) (hd : ∀ i, i < g.k → dsl g i ≤ Dm)
    (hchk : chkFrom D g (dsl g) b fuel lo = true)
    (hpo : PerOn (D g.out) P (b - Dm) b) (hpi : ∀ i, i < g.k → PerOn (D (g.ins.getD i 0)) P (b - Dm) b) :
    ∀ t, lo ≤ t → ext D b P g.out t = rhs (ext D b P) g (dsl g) t := by
  intro t
  induction t using Nat.strong_induction_on with
  | _ t ih =>
    intro hlt
    by_cases htb : t < b
    · rw [ext_lt D htb, chkFrom_sound D g (dsl g) b fuel lo hchk t hlt htb]
      unfold rhs; congr 1; apply addr_congr; intro i hi
      simp only [beh]; rw [ext_lt D (by omega)]
    · have e1 : ext D b P g.out t = ext D b P g.out (t - P) := by
        unfold ext; rw [wrap_per hP (by omega) (by omega)]
      have e2 : rhs (ext D b P) g (dsl g) t = rhs (ext D b P) g (dsl g) (t - P) := by
        unfold rhs; congr 1; apply addr_congr; intro i hi
        have := hd i hi
        rw [ext_per D hP hPb (hpi i hi) (by omega), show t - dsl g i - P = t - P - dsl g i by omega]
      rw [e1, e2]; exact ih (t - P) (by omega) (by omega)

/-! ## The slow corner, `g = 1`, `κ = 0` -/

/-- The strictest delay model of `Spec.Adm`: no guard, no scatter, slow corner. -/
def pSlow : DelayPar := ⟨1, 0⟩

theorem adm_slow (e : Arc) (d : Nat) (h0 : e.fmin ≤ e.smin) (h1 : e.smin ≤ d) (h2 : d ≤ e.smax) :
    Adm pSlow 1 e d := by
  have a1 : (e.fmin : ℚ) ≤ d := by exact_mod_cast Nat.le_trans h0 h1
  have a2 : (e.smin : ℚ) ≤ d := by exact_mod_cast h1
  have a3 : (d : ℚ) ≤ e.smax := by exact_mod_cast h2
  refine ⟨?_, ?_⟩ <;> simp only [pSlow, lerp] <;> norm_num <;> first | assumption | omega

theorem ceil_nat_one (n : Nat) : (Rat.ceil ((n : ℚ) * 1)).toNat = n := by
  rw [mul_one]
  have : Rat.ceil (n : ℚ) = (n : Int) := by
    unfold Rat.ceil; simp
  rw [this]; simp

theorem start_slow (g : Gate) : g.start pSlow = g.dmax := by
  unfold Gate.start Gate.dmax
  simp only [pSlow, add_zero, one_mul]
  congr 1
  apply List.map_congr_left
  intro e _; exact ceil_nat_one e.smax

/-- **`Spec.GateOK` for an extended behaviour at the slow corner, `g = 1`, `κ = 0`**, from the
segment check on `[dmax, b)`, the periodicity of the gate's nodes, and the per-gate
well-formedness facts (`fmin ≤ smin ≤ smax` on every arc, `arcs.length = k`). -/
theorem gateOK_slow (D : Nat → SD) (g : Gate) {b P Dm fuel : Nat} (hP : 0 < P) (hPb : P + Dm ≤ b)
    (hlo : g.dmax + P ≤ b) (hDm : g.dmax ≤ Dm) (hlen : g.arcs.length = g.k)
    (harc : ∀ e ∈ g.arcs, e.fmin ≤ e.smin ∧ e.smin ≤ e.smax)
    (hchk : chkFrom D g (dsl g) b fuel g.dmax = true)
    (hpo : PerOn (D g.out) P (b - Dm) b) (hpi : ∀ i, i < g.k → PerOn (D (g.ins.getD i 0)) P (b - Dm) b) :
    GateOK pSlow 1 g (ext D b P) := by
  have hdi : ∀ i, i < g.k → dsl g i ≤ g.dmax := fun i hi => le_dmax g i (by omega)
  refine ⟨fun i t => t - dsl g i, fun i _ a c hac => by simp only; omega, fun t ht => ?_⟩
  rw [start_slow] at ht
  refine ⟨fun i hi => ⟨Nat.sub_le _ _, ?_⟩, ?_⟩
  · have hd := hdi i hi
    rw [show t - (t - dsl g i) = dsl g i by omega]
    have hm : g.arcs.getD i default ∈ g.arcs := getD_mem _ _ (by omega)
    obtain ⟨h1, h2⟩ := harc _ hm
    exact adm_slow _ _ h1 h2 (Nat.le_refl _)
  · exact eq_ext D g hP hPb hlo (fun i hi => Nat.le_trans (hdi i hi) hDm) hchk hpo hpi t ht

/-! ## Checking periodicity of a description -/

/-- Walk `[s, b)` comparing the description with itself `P` earlier. -/
def chkPer (d : SD) (P b : Nat) : Nat → Nat → Bool
  | 0, _ => false
  | fuel + 1, s =>
    if b ≤ s then true
    else (d.val s == d.val (s - P)) && chkPer d P b fuel (nextAfter (d.ts ++ d.ts.map (· + P)) s b)

theorem chkPer_sound (d : SD) (P b : Nat) :
    ∀ fuel s, P ≤ s → chkPer d P b fuel s = true → ∀ u, s ≤ u → u < b → d.val u = d.val (u - P) := by
  intro fuel
  induction fuel with
  | zero => intro s _ h; simp [chkPer] at h
  | succ fuel ih =>
    intro s hPs h u hsu hub
    simp only [chkPer] at h
    split at h
    · omega
    · simp only [Bool.and_eq_true, beq_iff_eq] at h
      let n := nextAfter (d.ts ++ d.ts.map (· + P)) s b
      by_cases hu : u < n
      · have g1 : d.val u = d.val s := d.val_const hsu (fun x hx hsx => by
          have := nextAfter_gap (d.ts ++ d.ts.map (· + P)) s b x (List.mem_append_left (d.ts.map (· + P)) hx) hsx
          omega)
        have g2 : d.val (u - P) = d.val (s - P) := d.val_const (by omega) (fun x hx hsx => by
          have := nextAfter_gap (d.ts ++ d.ts.map (· + P)) s b (x + P)
            (List.mem_append_right d.ts (List.mem_map.2 ⟨x, hx, rfl⟩)) (by omega)
          omega)
        rw [g1, g2]; exact h.1
      · have hn := nextAfter_gt (d.ts ++ d.ts.map (· + P)) s b (by omega)
        exact ih n (by omega) h.2 u (by omega) hub

theorem perOn_of_chk (d : SD) {P b lo fuel : Nat} (hP : P ≤ lo) (h : chkPer d P b fuel lo = true) :
    PerOn d P lo b := fun u hu hub => chkPer_sound d P b fuel lo hP h u hu hub

end Formal.Target.Wit
