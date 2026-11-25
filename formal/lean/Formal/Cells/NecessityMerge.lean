import Formal.Cells.LibGapMux
import Formal.Cells.CTree

/-!
# NecessityMerge: the exact own-loop condition of bd_merge's uxa/uya, per pin

Probe Bmg (shard B). Rows `bd_merge.uxa_feedback` (S_XA_ZA / S_YA_ZA) and
`bd_merge.uxa_req_latency` (S_XA_R (1), (2)) were proved SUFFICIENT only
(`OpsTimedMux.merge_timing_of_static`, lumped LUT arcs). Both charge a wire
SPREAD (`Wzx.hi - Wzx.lo`, `Wxc.hi - Wxc.lo`) because they are launched at an
input edge. The next input edge at uxa is causally after uxa's OWN output
edge, so the spread of whichever input arrived last cancels. This file proves
the exact condition in B's per-pin model, on the real `bd_c2` INIT.

## Model (Int ps, named hypotheses)

* **H_PIN_READ** (`UxaEq`): for `t ≥ 0` uxa's output is its REAL INIT
  (`LibCtlMergeMux.c2B`, rst pin read 0) of: x_req at the client read at
  `pa.σ t` (I0: wire + site pin + I0's arc), z_ack at the server read at
  `pb.σ t` (I1: same), and its own output read at `pq.σ t` (I2: arc + feedback
  wire + site pin). Windows: `pa ∈ [Alo, Ahi]`, `pb ∈ [Blo, Bhi]`,
  `pq ∈ [Qlo, Qhi]`, `Qlo ≥ 1`.
* **H_PIN_FIFO** (`Mono`): the two INPUT pins' read maps are monotone (each
  wire / buffer / arc keeps the order of the edges it carries; different pins
  are independent, so cross-pin skew and reordering are allowed). The
  FEEDBACK read map is arbitrary (need not be monotone). Without H_PIN_FIFO
  on the input pins a single input edge could be read as new-old-new, and a
  C-element would glitch with no race at all; that is not a wire.
* **H_RESET**: the output is 0 before time 0.
* **H_CLIENT** (`HClient`, x's four-phase client, causal): every x_req edge
  that uxa's pin has not yet read at an output edge `τ` of uxa is launched at
  least `Xlo + Eo` after `τ` (`Xlo` = the uxa.O -> client wire, lo; `Eo` = the
  client's min reaction, MergeCausal.H_OWN).
* **H_SERVER** (`HServer`): likewise every z_ack edge not yet read at `τ` is
  launched at least `Xlo + Eo + K` after `τ`: it answers a request edge
  (x's own, or the next requester's, which waited for x_ack, H_OWN), and
  `K` = min request edge -> z_ack edge (`wo + Lor.lo + Dz.lo + Es`, JSON `Kz`).
* `τ` ranges over the edges of `idl`, the ZERO-DELAY C-element of uxa's own
  pin reads. When the cell is correct these are its output edges. The env
  hypotheses are stated on them, as CElemStrict states its env on the
  input-defined phase start: up to the first deviation the two coincide.

**Spec** (`UxaOK`): `q = idl`, for every feedback read map in the box: the
cell is exactly the zero-delay C-element of its own pin reads (no glitch, no
lost edge). Which edges `idl` has (x_ack firing only for x's tokens) is the
protocol rows' business (`bd_merge.seq`, `bd_merge.isochronic_forks`), not
this one.

## Results

* `cel_box_exact` (generic, any number of inputs, `cSpec` = bd_c2/c3/c4 law):
  `q = idl` for every feedback map in `[Qlo, Qhi]` **iff** `HHold`: whenever
  the pin reads disagree at `t`, `idl` is constant on `[t - Qhi, t - Qlo]`
  and equal to `idl t`. Pointwise and exact; no timing env needed.
* `merge_hhold` / `uxa_ok` (sufficient): H_CLIENT + H_SERVER and
  **H_XA_LOOP**: `Qhi ≤ Xlo + Eo + Alo ∧ Qhi ≤ Xlo + Eo + K + Blo`
  give UxaOK, for every input read map in the box.
* `uxa_box_exact` (headline): UxaOK for every driver pair, every monotone
  input read map in the box and every env obeying H_CLIENT / H_SERVER
  **iff** H_XA_LOOP. (Hypotheses: windows nonnegative, `Qlo ≥ 1`,
  `Xlo ≥ 0`, `Eo ≥ 1`, `K ≥ 0`.) The input pins' hi bounds and all spreads
  drop out.
* Necessity witness (`wit_*`): one x token, constant read maps, z_ack rising
  exactly `K` after x_req, the client reacting exactly `Eo` after seeing
  x_ack, z_ack falling exactly `K` after x_req (plus 1 ps when the x_req pin
  releases first): a physical run; it meets
  H_CLIENT / H_SERVER and breaks HHold when H_XA_LOOP fails by any amount.
* `old_imply_new`: the old row forms (S_XA_ZA, S_XA_R, and the fork form
  S_XA_FORK of `bd_merge.isochronic_forks`), rewritten per pin, imply
  H_XA_LOOP, so replacing them is safe. `old_not_necessary` /
  `old_not_necessary_R`: prjxray-shaped box numbers where S_XA_ZA (resp.
  S_XA_R (1)) FAILS and H_XA_LOOP holds, so by `uxa_ok` every run is correct.
* `nonvacuous`: a concrete run meeting every hypothesis with H_XA_LOOP at
  equality: uxa rises at 500 and falls at 1351, `q = idl`. `glitch`: the
  same run with the loop 1 ps longer: x_ack falls back at 950 while z_ack is
  still read high.
* ctree (section 6): `cel_box_exact` covers the bd_c3 / bd_c4 nodes on their
  real INITs (`c3_cspec`, `c4_cspec`); the one-node tree (root with port
  wires) is `uxa_box_exact` with `Xlo + Eo := E`, `K := 0` (`ctree1_exact`):
  exact `fmax-loop ≤ E + min port wire lo`, while `bd_ctree.node_fork` charges
  the port wires' spread. The general tree (depth ≥ 2) is NOT proved here.

Binary model: the exact condition is `≤`. The JSON's strict `+1` is the
Kleene X-window strictness of CElemStrict (Bs) and stays on top.

NOT covered: the protocol (which edges `idl` has; S_XA_FORK's y-phase part);
the uor / delay-line / server path is abstracted into `K` (one lower bound);
correlated pin delays (the box treats pins and edges independently; for a
corner model apply per realisation); Kleene X windows; depth ≥ 2 trees.
-/

namespace Formal.Cells.NecessityMerge
open Formal.Cells
open Formal.Cells.LibCtlMergeMux (cSpec c2B c2_spec)
open Formal.Cells.LibGapSteer (Rd)
open Formal.Cells.LibGapMux (int_ind)

/-! ## 0. C-element law on a pin vector -/

/-- The pins disagree (the C-element holds). -/
def Split (l : List Bool) : Prop := l.all id = false ∧ l.all (! ·) = false

instance (l : List Bool) : Decidable (Split l) := by unfold Split; infer_instance

theorem cSpec_split {l : List Bool} (h : Split l) (q : Bool) : cSpec l q = q := by
  simp [cSpec, h.1, h.2]

theorem cSpec_nsplit {l : List Bool} (h : ¬ Split l) (q q' : Bool) : cSpec l q = cSpec l q' := by
  unfold Split at h; unfold cSpec
  cases h1 : l.all id <;> cases h2 : l.all (! ·) <;> simp_all

/-- `bd_c2`'s real INIT with rst read 0 is the C-element law on `[x, y]`. -/
theorem uxa_init : ∀ x y q : Bool, c2B x y q false = cSpec [x, y] q := by decide

theorem split2 : ∀ x y : Bool, Split [x, y] ↔ x ≠ y := by decide

theorem cS2 : ∀ x y q : Bool, cSpec [x, y] q = if x = y then x else q := by decide

/-! ## 1. The zero-delay ideal and a trace constructor -/

def idlN (ins : Int → List Bool) : Nat → Bool
  | 0 => cSpec (ins 0) false
  | n + 1 => cSpec (ins ((n : Int) + 1)) (idlN ins n)

/-- The zero-delay C-element of the pin reads, 0 before time 0. -/
def idl (ins : Int → List Bool) (t : Int) : Bool := if t < 0 then false else idlN ins t.toNat

theorem idl_neg (ins : Int → List Bool) {t : Int} (h : t < 0) : idl ins t = false := by
  simp [idl, h]

theorem idl_eq (ins : Int → List Bool) {t : Int} (h : 0 ≤ t) :
    idl ins t = cSpec (ins t) (idl ins (t - 1)) := by
  obtain ⟨n, rfl⟩ : ∃ n : Nat, t = n := ⟨t.toNat, by omega⟩
  cases n with
  | zero => simp [idl, idlN]
  | succ k =>
    have e1 : ¬ ((k + 1 : Nat) : Int) < 0 := by omega
    have e2 : ¬ (((k + 1 : Nat) : Int) - 1 < 0) := by omega
    simp only [idl, e1, e2, ite_false]
    rw [show (((k + 1 : Nat) : Int)).toNat = k + 1 by omega,
      show ((((k + 1 : Nat) : Int)) - 1).toNat = k by omega]
    simp only [idlN]
    rw [show ((k : Int) + 1) = ((k + 1 : Nat) : Int) by omega]

def runF (ins : Int → List Bool) (σ : Int → Int) : Nat → Int → Bool
  | 0, _ => false
  | n + 1, t => if t < 0 then false else cSpec (ins t) (runF ins σ n (σ t))

/-- The trace a given feedback read map produces (well defined: `σ t < t`). -/
def run (ins : Int → List Bool) (σ : Int → Int) (t : Int) : Bool := runF ins σ (t.toNat + 1) t

theorem runF_stable (ins : Int → List Bool) (σ : Int → Int) (hσ : ∀ u, σ u ≤ u - 1) :
    ∀ n m : Nat, ∀ t : Int, t < n → t < m → runF ins σ n t = runF ins σ m t := by
  intro n
  induction n with
  | zero =>
    intro m t h1 _
    cases m with
    | zero => rfl
    | succ m => simp [runF, show t < 0 by omega]
  | succ n ih =>
    intro m t h1 h2
    cases m with
    | zero => simp [runF, show t < 0 by omega]
    | succ m =>
      simp only [runF]
      split
      · rfl
      · rw [ih m (σ t) (by have := hσ t; omega) (by have := hσ t; omega)]

theorem run_neg (ins : Int → List Bool) (σ : Int → Int) {t : Int} (h : t < 0) :
    run ins σ t = false := by
  simp [run, runF, h]

theorem run_eq (ins : Int → List Bool) (σ : Int → Int) (hσ : ∀ u, σ u ≤ u - 1) {t : Int}
    (ht : 0 ≤ t) : run ins σ t = cSpec (ins t) (run ins σ (σ t)) := by
  have e : run ins σ t = if t < 0 then false else cSpec (ins t) (runF ins σ t.toNat (σ t)) := rfl
  rw [e]; simp only [show ¬ t < 0 by omega, ite_false]
  unfold run
  rw [runF_stable ins σ hσ t.toNat ((σ t).toNat + 1) (σ t) (by have := hσ t; omega)
    (by omega)]

/-! ## 2. Generic exactness: one C-element, any feedback read map in a box -/

/-- **H_PIN_READ + H_RESET** on the pin-read vector `ins`. -/
def CelEq (ins : Int → List Bool) (pq : Rd) (q : Int → Bool) : Prop :=
  (∀ t, t < 0 → q t = false) ∧ ∀ t, 0 ≤ t → q t = cSpec (ins t) (q (pq.σ t))

/-- The spec, for every feedback read map in the box. -/
def CelOK (ins : Int → List Bool) (Qlo Qhi : Int) : Prop :=
  ∀ pq : Rd, Qlo ≤ pq.lo → pq.hi ≤ Qhi → ∀ q, CelEq ins pq q → ∀ t, q t = idl ins t

/-- **HHold**: a disagreement at `t` sees no ideal edge through the loop. -/
def HHold (ins : Int → List Bool) (Qlo Qhi : Int) : Prop :=
  ∀ t, 0 ≤ t → Split (ins t) → ∀ s, t - Qhi ≤ s → s ≤ t - Qlo → idl ins s = idl ins t

theorem cel_ok {ins : Int → List Bool} {Qlo Qhi : Int} (hQ : 1 ≤ Qlo)
    (H : HHold ins Qlo Qhi) : CelOK ins Qlo Qhi := by
  intro pq h1 h2 q hq
  apply int_ind (fun t => q t = idl ins t)
  · intro t ht; rw [hq.1 t ht, idl_neg ins ht]
  · intro t ht ih
    have g1 := pq.ge t; have g2 := pq.le t
    by_cases hs : Split (ins t)
    · rw [hq.2 t ht, cSpec_split hs, ih _ (by omega)]
      exact H t ht hs _ (by omega) (by omega)
    · rw [hq.2 t ht, idl_eq ins ht]; exact cSpec_nsplit hs _ _

/-- The adversarial feedback map: at `t0` it reads `s`, elsewhere `Qhi` back. -/
def advQ (t0 s Qlo Qhi : Int) (h1 : t0 - Qhi ≤ s) (h2 : s ≤ t0 - Qlo) (h3 : Qlo ≤ Qhi) : Rd :=
  ⟨fun u => if u = t0 then s else u - Qhi, Qlo, Qhi,
   fun u => by split <;> omega, fun u => by split <;> omega⟩

theorem cel_needs {ins : Int → List Bool} {Qlo Qhi : Int} (hQ : 1 ≤ Qlo) (hQ2 : Qlo ≤ Qhi)
    (H : CelOK ins Qlo Qhi) : HHold ins Qlo Qhi := by
  intro t ht hs s h1 h2
  apply Classical.byContradiction; intro hne
  let pq := advQ t s Qlo Qhi h1 h2 hQ2
  have hσ : ∀ u, pq.σ u ≤ u - 1 := fun u => by have := pq.le u; show _ ≤ _; simp [pq, advQ] at this ⊢; omega
  have hE : CelEq ins pq (run ins pq.σ) :=
    ⟨fun u hu => run_neg ins pq.σ hu, fun u hu => run_eq ins pq.σ hσ hu⟩
  have hok := H pq (Int.le_refl _) (Int.le_refl _) _ hE
  have e1 := hok t
  have e2 := hok s
  rw [hE.2 t ht, cSpec_split hs] at e1
  have hst : pq.σ t = s := by simp [pq, advQ]
  rw [hst, e2] at e1
  exact hne e1

/-- **`cel_box_exact`** (generic per-pin C-element, any pin count). -/
theorem cel_box_exact {ins : Int → List Bool} {Qlo Qhi : Int} (hQ : 1 ≤ Qlo) (hQ2 : Qlo ≤ Qhi) :
    CelOK ins Qlo Qhi ↔ HHold ins Qlo Qhi :=
  ⟨cel_needs hQ hQ2, cel_ok hQ⟩

/-! ## 3. bd_merge's uxa in its causal environment -/

/-- uxa's pin-read vector: x_req (I0) through `pa`, z_ack (I1) through `pb`. -/
def insAB (a b : Int → Bool) (pa pb : Rd) : Int → List Bool := fun t => [a (pa.σ t), b (pb.σ t)]

/-- **H_PIN_READ** on the REAL `bd_c2` INIT (rst pin read 0), with H_RESET. -/
def UxaEq (a b : Int → Bool) (pa pb pq : Rd) (q : Int → Bool) : Prop :=
  (∀ t, t < 0 → q t = false) ∧
    ∀ t, 0 ≤ t → q t = c2B (a (pa.σ t)) (b (pb.σ t)) (q (pq.σ t)) false

theorem uxaEq_iff (a b : Int → Bool) (pa pb pq : Rd) (q : Int → Bool) :
    UxaEq a b pa pb pq q ↔ CelEq (insAB a b pa pb) pq q := by
  unfold UxaEq CelEq insAB
  simp only [uxa_init]

/-- The spec on the real INIT, every feedback read map in the box. -/
def UxaOK (a b : Int → Bool) (pa pb : Rd) (Qlo Qhi : Int) : Prop :=
  ∀ pq : Rd, Qlo ≤ pq.lo → pq.hi ≤ Qhi → ∀ q, UxaEq a b pa pb pq q →
    ∀ t, q t = idl (insAB a b pa pb) t

theorem uxaOK_iff (a b : Int → Bool) (pa pb : Rd) (Qlo Qhi : Int) :
    UxaOK a b pa pb Qlo Qhi ↔ CelOK (insAB a b pa pb) Qlo Qhi := by
  unfold UxaOK CelOK
  simp only [uxaEq_iff]

/-- **H_PIN_FIFO**. -/
def Mono (p : Rd) : Prop := ∀ u v, u ≤ v → p.σ u ≤ p.σ v

/-- An edge of the ideal output at `τ`. -/
def Edge (ins : Int → List Bool) (τ : Int) : Prop := idl ins (τ - 1) ≠ idl ins τ

/-- **H_CLIENT**: x_req edges not yet read at an output edge are launched
`Xlo + Eo` after it. -/
def HClient (ins : Int → List Bool) (a : Int → Bool) (pa : Rd) (Xlo Eo : Int) : Prop :=
  ∀ τ, Edge ins τ → ∀ α, pa.σ τ < α → a α ≠ a (α - 1) → τ + Xlo + Eo ≤ α

/-- **H_SERVER**: z_ack edges not yet read at an output edge are launched
`Xlo + Eo + K` after it. -/
def HServer (ins : Int → List Bool) (b : Int → Bool) (pb : Rd) (Xlo Eo K : Int) : Prop :=
  ∀ τ, Edge ins τ → ∀ β, pb.σ τ < β → b β ≠ b (β - 1) → τ + Xlo + Eo + K ≤ β

theorem exists_change_n (f : Int → Bool) (x : Int) :
    ∀ n : Nat, ∀ y, y = x + n → f x ≠ f y → ∃ z, x < z ∧ z ≤ y ∧ f z ≠ f (z - 1) := by
  intro n
  induction n with
  | zero => intro y hy h; subst hy; exact (h (by simp)).elim
  | succ n ih =>
    intro y hy h
    by_cases hc : f (y - 1) = f y
    · obtain ⟨z, h1, h2, h3⟩ := ih (y - 1) (by omega) (by rw [hc]; exact h)
      exact ⟨z, h1, by omega, h3⟩
    · exact ⟨y, by omega, Int.le_refl _, fun e => hc e.symm⟩

theorem exists_change (f : Int → Bool) {x y : Int} (hxy : x ≤ y) (h : f x ≠ f y) :
    ∃ z, x < z ∧ z ≤ y ∧ f z ≠ f (z - 1) :=
  exists_change_n f x (y - x).toNat y (by omega) h

/-- At an ideal edge both pins read the new value. -/
theorem edge_agree {a b : Int → Bool} {pa pb : Rd} {τ : Int} (h : Edge (insAB a b pa pb) τ) :
    a (pa.σ τ) = b (pb.σ τ) := by
  unfold Edge at h
  by_cases hτ : τ < 0
  · rw [idl_neg _ hτ, idl_neg _ (by omega)] at h; exact absurd rfl h
  · rw [idl_eq _ (show 0 ≤ τ by omega)] at h
    by_cases hs : Split (insAB a b pa pb τ)
    · rw [cSpec_split hs] at h; exact absurd rfl h
    · exact Classical.byContradiction (fun hne => hs ((split2 _ _).mpr hne))

/-- **`merge_hhold`**: H_XA_LOOP and the causal env give HHold. -/
theorem merge_hhold {a b : Int → Bool} {pa pb : Rd} {Alo Blo Qlo Qhi Xlo Eo K : Int}
    (hma : Mono pa) (hmb : Mono pb) (hA : Alo ≤ pa.lo) (hB : Blo ≤ pb.lo) (hQ : 1 ≤ Qlo)
    (HC : HClient (insAB a b pa pb) a pa Xlo Eo) (HS : HServer (insAB a b pa pb) b pb Xlo Eo K)
    (H_XA_LOOP_A : Qhi ≤ Xlo + Eo + Alo) (H_XA_LOOP_B : Qhi ≤ Xlo + Eo + K + Blo) :
    HHold (insAB a b pa pb) Qlo Qhi := by
  intro t ht hs s h1 h2
  apply Classical.byContradiction; intro hne
  obtain ⟨τ, hτ1, hτ2, hτe⟩ := exists_change (idl (insAB a b pa pb)) (show s ≤ t by omega) hne
  have he : Edge (insAB a b pa pb) τ := fun e => hτe e.symm
  have hab := edge_agree he
  have hst : a (pa.σ t) ≠ b (pb.σ t) := (split2 _ _).mp hs
  by_cases hA' : a (pa.σ t) = a (pa.σ τ)
  · have hb' : b (pb.σ τ) ≠ b (pb.σ t) := by
      intro e; apply hst; rw [hA', hab, e]
    have hm := hmb τ t hτ2
    obtain ⟨β, hβ1, hβ2, hβ3⟩ := exists_change b hm hb'
    have := HS τ he β hβ1 hβ3
    have := pb.le t
    omega
  · have ha' : a (pa.σ τ) ≠ a (pa.σ t) := fun e => hA' e.symm
    have hm := hma τ t hτ2
    obtain ⟨α, hα1, hα2, hα3⟩ := exists_change a hm ha'
    have := HC τ he α hα1 hα3
    have := pa.le t
    omega

/-- **`uxa_ok`** (sufficient, any input read maps in the box). -/
theorem uxa_ok {a b : Int → Bool} {pa pb : Rd} {Alo Blo Qlo Qhi Xlo Eo K : Int}
    (hma : Mono pa) (hmb : Mono pb) (hA : Alo ≤ pa.lo) (hB : Blo ≤ pb.lo) (hQ : 1 ≤ Qlo)
    (HC : HClient (insAB a b pa pb) a pa Xlo Eo) (HS : HServer (insAB a b pa pb) b pb Xlo Eo K)
    (H_XA_LOOP_A : Qhi ≤ Xlo + Eo + Alo) (H_XA_LOOP_B : Qhi ≤ Xlo + Eo + K + Blo) :
    UxaOK a b pa pb Qlo Qhi :=
  (uxaOK_iff a b pa pb Qlo Qhi).mpr
    (cel_ok hQ (merge_hhold hma hmb hA hB hQ HC HS H_XA_LOOP_A H_XA_LOOP_B))

/-! ## 4. The necessity witness: one x token -/

/-- A driver high exactly on `[0, e)`. -/
def stp (e : Int) (t : Int) : Bool := decide (0 ≤ t ∧ t < e)

theorem stp_change {e α : Int} (h : stp e α ≠ stp e (α - 1)) : α = 0 ∨ α = e := by
  apply Classical.byContradiction; intro hn
  apply h
  have : (0 ≤ α ∧ α < e) ↔ (0 ≤ α - 1 ∧ α - 1 < e) := by omega
  simp only [stp, this]

/-- A driver high exactly on `[s0, e)` (z_ack: rises `K` after x_req). -/
def stp2 (s0 e : Int) (t : Int) : Bool := decide (s0 ≤ t ∧ t < e)

theorem stp2_change {s0 e α : Int} (h : stp2 s0 e α ≠ stp2 s0 e (α - 1)) : α = s0 ∨ α = e := by
  apply Classical.byContradiction; intro hn
  apply h
  have : (s0 ≤ α ∧ α < e) ↔ (s0 ≤ α - 1 ∧ α - 1 < e) := by omega
  simp only [stp2, this]

theorem const_mono (d : Int) : Mono (Rd.const d) := fun u v h => by simp [Rd.const]; omega

section wit
variable (Alo Blo Kb α1 β1 : Int)

/-- The witness's pin reads: x_req high on `[0, α1)`, z_ack on `[Kb, β1)`,
fixed delays `Alo`, `Blo`. -/
def insW : Int → List Bool := insAB (stp α1) (stp2 Kb β1) (Rd.const Alo) (Rd.const Blo)

theorem insW_eq (t : Int) : insW Alo Blo Kb α1 β1 t = [stp α1 (t - Alo), stp2 Kb β1 (t - Blo)] := rfl

variable {Alo Blo Kb α1 β1}

theorem wit_pre (_h0A : 0 ≤ Alo) (_h0B : 0 ≤ Blo) (_hK0 : 0 ≤ Kb) :
    ∀ t, t < max Alo (Kb + Blo) → idl (insW Alo Blo Kb α1 β1) t = false := by
  intro t
  apply int_ind (fun t => t < max Alo (Kb + Blo) → idl (insW Alo Blo Kb α1 β1) t = false)
  · intro t ht _; exact idl_neg _ ht
  · intro t ht ih hlt
    rw [idl_eq _ ht, insW_eq, cS2]
    cases hx : stp α1 (t - Alo) <;> cases hy : stp2 Kb β1 (t - Blo) <;> simp only [stp, stp2] at hx hy
    · simp
    · simp only [Bool.false_eq_true, ite_false]; exact ih _ (by omega) (by omega)
    · simp only [Bool.true_eq_false, ite_false]; exact ih _ (by omega) (by omega)
    · simp at hx hy; omega

theorem wit_mid (h0A : 0 ≤ Alo) (h0B : 0 ≤ Blo) (hK0 : 0 ≤ Kb) (h1 : max Alo (Kb + Blo) < α1) (h2 : α1 ≤ β1) :
    ∀ t, max Alo (Kb + Blo) ≤ t → t < max (α1 + Alo) (β1 + Blo) → idl (insW Alo Blo Kb α1 β1) t = true := by
  intro t
  apply int_ind (fun t => max Alo (Kb + Blo) ≤ t → t < max (α1 + Alo) (β1 + Blo) →
    idl (insW Alo Blo Kb α1 β1) t = true)
  · intro t ht h; omega
  · intro t ht ih hle hlt
    rw [idl_eq _ ht, insW_eq, cS2]
    cases hx : stp α1 (t - Alo) <;> cases hy : stp2 Kb β1 (t - Blo) <;> simp only [stp, stp2] at hx hy
    · simp at hx hy; omega
    · simp at hx hy
      simp only [Bool.false_eq_true, ite_false]
      exact ih _ (by omega) (by omega) (by omega)
    · simp at hx hy
      simp only [Bool.true_eq_false, ite_false]
      exact ih _ (by omega) (by omega) (by omega)
    · simp

theorem wit_post (h0A : 0 ≤ Alo) (h0B : 0 ≤ Blo) (hK0 : 0 ≤ Kb) (h1 : max Alo (Kb + Blo) < α1) :
    ∀ t, max (α1 + Alo) (β1 + Blo) ≤ t → idl (insW Alo Blo Kb α1 β1) t = false := by
  intro t ht
  rw [idl_eq _ (by omega), insW_eq, cS2]
  have hx : stp α1 (t - Alo) = false := by simp [stp]; omega
  have hy : stp2 Kb β1 (t - Blo) = false := by simp [stp2]; omega
  rw [hx, hy]; rfl

theorem wit_edge (h0A : 0 ≤ Alo) (h0B : 0 ≤ Blo) (hK0 : 0 ≤ Kb) (h1 : max Alo (Kb + Blo) < α1) (h2 : α1 ≤ β1)
    {τ : Int} (he : Edge (insW Alo Blo Kb α1 β1) τ) :
    τ = max Alo (Kb + Blo) ∨ τ = max (α1 + Alo) (β1 + Blo) := by
  apply Classical.byContradiction; intro hn
  apply he
  by_cases c1 : τ < max Alo (Kb + Blo)
  · rw [wit_pre h0A h0B hK0 _ c1, wit_pre h0A h0B hK0 _ (by omega)]
  · by_cases c2 : τ < max (α1 + Alo) (β1 + Blo)
    · rw [wit_mid h0A h0B hK0 h1 h2 _ (by omega) c2, wit_mid h0A h0B hK0 h1 h2 _ (by omega) (by omega)]
    · rw [wit_post h0A h0B hK0 h1 _ (by omega), wit_post h0A h0B hK0 h1 _ (by omega)]

theorem wit_client {Xlo Eo : Int} (h0A : 0 ≤ Alo) (h0B : 0 ≤ Blo) (hK0 : 0 ≤ Kb) (h1 : max Alo (Kb + Blo) < α1)
    (h2 : α1 ≤ β1) (hα : max Alo (Kb + Blo) + Xlo + Eo ≤ α1) :
    HClient (insW Alo Blo Kb α1 β1) (stp α1) (Rd.const Alo) Xlo Eo := by
  intro τ he α hα1 hα2
  have hc := stp_change hα2
  simp only [Rd.const] at hα1
  rcases wit_edge h0A h0B hK0 h1 h2 he with e | e <;> subst e <;> omega

theorem wit_server {Xlo Eo K : Int} (h0A : 0 ≤ Alo) (h0B : 0 ≤ Blo) (hK0 : 0 ≤ Kb) (h1 : max Alo (Kb + Blo) < α1)
    (h2 : α1 ≤ β1) (hβ : max Alo (Kb + Blo) + Xlo + Eo + K ≤ β1) :
    HServer (insW Alo Blo Kb α1 β1) (stp2 Kb β1) (Rd.const Blo) Xlo Eo K := by
  intro τ he β hβ1 hβ2
  have hc := stp2_change hβ2
  simp only [Rd.const] at hβ1
  rcases wit_edge h0A h0B hK0 h1 h2 he with e | e <;> subst e <;> omega

end wit

/-! ## 5. Headline: exact over the box -/

/-- **`uxa_box_exact`**. -/
theorem uxa_box_exact {Alo Ahi Blo Bhi Qlo Qhi Xlo Eo K : Int}
    (h0A : 0 ≤ Alo) (hA : Alo ≤ Ahi) (h0B : 0 ≤ Blo) (hB : Blo ≤ Bhi)
    (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi) (hX : 0 ≤ Xlo) (hE : 1 ≤ Eo) (hK : 0 ≤ K) :
    (∀ (a b : Int → Bool) (pa pb : Rd), Mono pa → Mono pb →
        Alo ≤ pa.lo → pa.hi ≤ Ahi → Blo ≤ pb.lo → pb.hi ≤ Bhi →
        HClient (insAB a b pa pb) a pa Xlo Eo → HServer (insAB a b pa pb) b pb Xlo Eo K →
        UxaOK a b pa pb Qlo Qhi) ↔
      (Qhi ≤ Xlo + Eo + Alo ∧ Qhi ≤ Xlo + Eo + K + Blo) := by
  constructor
  · intro H
    apply Classical.byContradiction; intro hn
    -- the witness: one x token
    let τ1 := max Alo (K + Blo)
    let α1 := τ1 + Xlo + Eo
    let D : Int := if Alo ≤ K + Blo then 1 else 0
    let β1 := α1 + K + D
    have hD : 0 ≤ D := by simp only [D]; split <;> omega
    have h1 : max Alo (K + Blo) < α1 := by simp only [α1, τ1]; omega
    have h2 : α1 ≤ β1 := by simp only [β1]; omega
    have hok := H (stp α1) (stp2 K β1) (Rd.const Alo) (Rd.const Blo) (const_mono _) (const_mono _)
      (Int.le_refl _) hA (Int.le_refl _) hB
      (wit_client h0A h0B hK h1 h2 (Int.le_refl _)) (wit_server h0A h0B hK h1 h2 (by simp only [β1]; omega))
    have hh := cel_needs hQ1 hQ ((uxaOK_iff _ _ _ _ _ _).mp hok)
    -- the disagreement instant
    by_cases hc : Alo ≤ K + Blo
    · have hDv : D = 1 := by simp [D, hc]
      have hQb : Xlo + Eo + Alo < Qhi := by omega
      let t := α1 + Alo
      have hs : Split (insAB (stp α1) (stp2 K β1) (Rd.const Alo) (Rd.const Blo) t) := by
        rw [show insAB (stp α1) (stp2 K β1) (Rd.const Alo) (Rd.const Blo) t =
          [stp α1 (t - Alo), stp2 K β1 (t - Blo)] from rfl, split2]
        have hx : stp α1 (t - Alo) = false := by simp [stp, t]
        have hy : stp2 K β1 (t - Blo) = true := by
          simp only [stp2, t, β1, α1, τ1, hDv, decide_eq_true_eq]; omega
        rw [hx, hy]; decide
      have e := hh t (by simp only [t, α1, τ1]; omega) hs (t - Qhi) (Int.le_refl _) (by omega)
      have e1 : idl (insW Alo Blo K α1 β1) (t - Qhi) = false :=
        wit_pre h0A h0B hK _ (by simp only [t, α1, τ1] at *; omega)
      have e2 : idl (insW Alo Blo K α1 β1) t = true :=
        wit_mid h0A h0B hK h1 h2 _ (by simp only [t, α1, τ1]; omega) (by simp only [t, β1, hDv]; omega)
      simp only [insW] at e1 e2
      rw [e1, e2] at e; exact absurd e (by decide)
    · have hDv : D = 0 := by simp [D, hc]
      have hQb : Xlo + Eo + K + Blo < Qhi := by omega
      let t := β1 + Blo
      have hs : Split (insAB (stp α1) (stp2 K β1) (Rd.const Alo) (Rd.const Blo) t) := by
        rw [show insAB (stp α1) (stp2 K β1) (Rd.const Alo) (Rd.const Blo) t =
          [stp α1 (t - Alo), stp2 K β1 (t - Blo)] from rfl, split2]
        have hx : stp α1 (t - Alo) = true := by
          simp only [stp, t, β1, α1, τ1, hDv, decide_eq_true_eq]; omega
        have hy : stp2 K β1 (t - Blo) = false := by simp [stp2, t]
        rw [hx, hy]; decide
      have e := hh t (by simp only [t, β1, α1, τ1]; omega) hs (t - Qhi) (Int.le_refl _) (by omega)
      have e1 : idl (insW Alo Blo K α1 β1) (t - Qhi) = false :=
        wit_pre h0A h0B hK _ (by simp only [t, β1, hDv, α1, τ1] at *; omega)
      have e2 : idl (insW Alo Blo K α1 β1) t = true :=
        wit_mid h0A h0B hK h1 h2 _ (by simp only [t, β1, hDv, α1, τ1]; omega)
          (by simp only [t, β1, hDv, α1, τ1]; omega)
      simp only [insW] at e1 e2
      rw [e1, e2] at e; exact absurd e (by decide)
  · intro ⟨hLA, hLB⟩ a b pa pb hma hmb hA1 _ hB1 _ HC HS
    exact uxa_ok hma hmb hA1 hB1 hQ1 HC HS hLA hLB

/-! ## 6. The old row forms vs H_XA_LOOP -/

/-- **`old_imply_new`**: the old forms, per pin, imply H_XA_LOOP (strict
forms both sides). Symbols: z_ack wire `Wzx`, x_req wire `Wxc`, site pins
`SPb` (I1), `SPa` (I0), `SPq` (I2) hi, feedback wire `wxah`, flat O6 arc
`[Llo, Lhi]` on every pin (**H_FLAT_ARC**, prjxray O6 45/124), `mz` = the
JSON's `wz + SP + la` (min z_ack -> {uxa, uya} I1 path, lo), `wa ≤ Wxa.lo`.
S_XA_ZA (`bd_merge.uxa_feedback`) gives the K branch; S_XA_FORK
(`bd_merge.isochronic_forks` form 0) gives the x_req branch. -/
theorem old_imply_new (Wzx_lo Wzx_hi SPb_lo SPb_hi Wxc_lo SPa_lo Llo Lhi wxah SPq_hi
    Wxa_lo wa mz Eo Kz : Int)
    (hW : Wzx_lo ≤ Wzx_hi) (hS : SPb_lo ≤ SPb_hi) (hmz : mz ≤ Wzx_lo + SPb_lo + Llo)
    (hwa : wa ≤ Wxa_lo)
    (S_XA_ZA : Wzx_hi + SPb_hi + Lhi + wxah + SPq_hi + 1 ≤ Wzx_lo + SPb_lo + (mz + wa + Eo) + Kz)
    (S_XA_FORK : Wzx_hi + SPb_hi + Lhi + wxah + SPq_hi + 1 ≤ (mz + wa + Eo) + Wxc_lo + SPa_lo) :
    (wxah + SPq_hi + Lhi) + 1 ≤ Wxa_lo + Eo + (Wxc_lo + SPa_lo + Llo) ∧
    (wxah + SPq_hi + Lhi) + 1 ≤ Wxa_lo + Eo + Kz + (Wzx_lo + SPb_lo + Llo) := by
  constructor <;> omega

/-- The JSON's S_XA_ZA form (`bd_merge.uxa_feedback` form 0) per pin. -/
def oldZA (Wzx_lo Wzx_hi SPb_lo SPb_hi Lhi wxah SPq_hi mz wa Eo Kz : Int) : Prop :=
  Wzx_hi + SPb_hi + Lhi + wxah + SPq_hi + 1 ≤ Wzx_lo + SPb_lo + (mz + wa + Eo) + Kz

/-- The JSON's S_XA_R (1) form (`bd_merge.uxa_req_latency` form 0) per pin. -/
def oldR1 (Wxc_lo Wxc_hi SPa_lo SPa_hi Lhi wxah SPq_hi mz wa Eo Kz : Int) : Prop :=
  Wxc_hi + SPa_hi + Lhi + wxah + SPq_hi + 1 ≤ Kz + (mz + wa + Eo) + Wxc_lo + SPa_lo

/-- **`old_not_necessary`**: prjxray-shaped box numbers (ps; FAST_MIN lo,
SLOW_MAX hi): z_ack wire [300, 1500], x_req wire [200, 600], site pins I1 = A2
[170, 507], I0 = A4 [86, 284], I2 = A1 hi 516, flat O6 [45, 124], feedback
wire [50, 300], x_ack wire lo 150, client Eo 600, Kz 1000. The old S_XA_ZA
FAILS (2948 > 2735) while H_XA_LOOP (strict) holds (941 ≤ 1081), so by
`uxa_ok` every run of uxa in the box is correct: S_XA_ZA is not necessary. -/
theorem old_not_necessary :
    ¬ oldZA 300 1500 170 507 124 300 516 (300 + 170 + 45) 150 600 1000 ∧
    (940 + 1 ≤ (150 : Int) + 600 + (200 + 86 + 45) ∧ (940 : Int) + 1 ≤ 150 + 600 + 1000 + (300 + 170 + 45)) ∧
    ∀ (a b : Int → Bool) (pa pb : Rd), Mono pa → Mono pb →
      200 + 86 + 45 ≤ pa.lo → 300 + 170 + 45 ≤ pb.lo →
      HClient (insAB a b pa pb) a pa 150 600 → HServer (insAB a b pa pb) b pb 150 600 1000 →
      UxaOK a b pa pb (50 + 172 + 45) (300 + 516 + 124) := by
  refine ⟨by unfold oldZA; decide, by decide, ?_⟩
  intro a b pa pb hma hmb hA hB HC HS
  exact uxa_ok (Alo := 200 + 86 + 45) (Blo := 300 + 170 + 45) hma hmb hA hB (by decide) HC HS
    (by decide) (by decide)

/-- **`old_not_necessary_R`**: same numbers with an x_req wire [200, 2000]:
the old S_XA_R (1) FAILS (3225 > 2551), H_XA_LOOP is unchanged (the x_req
wire's hi does not enter it). -/
theorem old_not_necessary_R :
    ¬ oldR1 200 2000 86 284 124 300 516 (300 + 170 + 45) 150 600 1000 ∧
    ∀ (a b : Int → Bool) (pa pb : Rd), Mono pa → Mono pb →
      200 + 86 + 45 ≤ pa.lo → 300 + 170 + 45 ≤ pb.lo →
      HClient (insAB a b pa pb) a pa 150 600 → HServer (insAB a b pa pb) b pb 150 600 1000 →
      UxaOK a b pa pb (50 + 172 + 45) (300 + 516 + 124) := by
  refine ⟨by unfold oldR1; decide, ?_⟩
  intro a b pa pb hma hmb hA hB HC HS
  exact uxa_ok (Alo := 200 + 86 + 45) (Blo := 300 + 170 + 45) hma hmb hA hB (by decide) HC HS
    (by decide) (by decide)

/-! ## 7. Non-vacuity and a concrete glitch -/

/-- **`nonvacuous`**: x_req high on [0, 850), z_ack on [400, 1251) (it rises
`K = 400` after x_req and falls 401 after it), both pins 100 ps, x_ack wire
50, client 300, loop up to 450 (H_XA_LOOP at equality, x_req branch:
450 = 50 + 300 + 100). Every hypothesis holds; for every feedback map in
[1, 450] every trace rises at 500 and falls at 1351; such a trace exists. -/
theorem nonvacuous :
    HClient (insW 100 100 400 850 1251) (stp 850) (Rd.const 100) 50 300 ∧
    HServer (insW 100 100 400 850 1251) (stp2 400 1251) (Rd.const 100) 50 300 400 ∧
    (∀ pq : Rd, 1 ≤ pq.lo → pq.hi ≤ 450 → ∀ q,
      UxaEq (stp 850) (stp2 400 1251) (Rd.const 100) (Rd.const 100) pq q →
        q 499 = false ∧ q 500 = true ∧ q 1350 = true ∧ q 1351 = false) ∧
    (∃ q, UxaEq (stp 850) (stp2 400 1251) (Rd.const 100) (Rd.const 100) (Rd.const 450) q) := by
  have HC := wit_client (Alo := 100) (Blo := 100) (Kb := 400) (α1 := 850) (β1 := 1251)
    (Xlo := 50) (Eo := 300) (by decide) (by decide) (by decide) (by decide) (by decide) (by decide)
  have HS := wit_server (Alo := 100) (Blo := 100) (Kb := 400) (α1 := 850) (β1 := 1251)
    (Xlo := 50) (Eo := 300) (K := 400) (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)
  refine ⟨HC, HS, ?_, ?_⟩
  · intro pq h1 h2 q hq
    have hok := uxa_ok (Alo := 100) (Blo := 100) (Qlo := 1) (Qhi := 450) (const_mono _)
      (const_mono _) (by decide) (by decide) (Int.le_refl 1) HC HS (by decide) (by decide) pq
      (by omega) (by omega) q hq
    rw [hok, hok, hok, hok]
    exact ⟨wit_pre (by decide) (by decide) (by decide) _ (by decide),
      wit_mid (by decide) (by decide) (by decide) (by decide) (by decide) _ (by decide) (by decide),
      wit_mid (by decide) (by decide) (by decide) (by decide) (by decide) _ (by decide) (by decide),
      wit_post (by decide) (by decide) (by decide) (by decide) _ (by decide)⟩
  · let ins := insW 100 100 400 850 1251
    have hσ : ∀ u, (Rd.const 450).σ u ≤ u - 1 := fun u => by show u - 450 ≤ u - 1; omega
    refine ⟨run ins (Rd.const 450).σ, ?_⟩
    rw [uxaEq_iff]
    exact ⟨fun u hu => run_neg _ _ hu, fun u hu => run_eq _ _ hσ hu⟩

/-- **`glitch`**: the same run with the loop 1 ps too long (451 > 50 + 300 +
100), feedback read 451 back. x_ack is 1 at 949 and FALLS at 950, while
z_ack is still read high (its fall is read at 1351): the cell releases on
x_req alone before the feedback has seen its own rise (at 950 it reads 499,
before the rise at 500); the ideal is still 1 there. -/
theorem glitch :
    let ins := insW 100 100 400 850 1251
    let q := run ins (Rd.const 451).σ
    q 949 = true ∧ q 950 = false ∧ idl ins 950 = true ∧ stp2 400 1251 (950 - 100) = true := by
  intro ins q
  have hσ : ∀ u, (Rd.const 451).σ u ≤ u - 1 := fun u => by show u - 451 ≤ u - 1; omega
  have e949 : q 949 = true := by
    show run ins (Rd.const 451).σ 949 = true
    rw [run_eq _ _ hσ (by decide)]
    show cSpec [stp 850 (949 - 100), stp2 400 1251 (949 - 100)] _ = true
    rw [show stp 850 (949 - 100) = true by decide, show stp2 400 1251 (949 - 100) = true by decide]
    simp [cSpec]
  have e48 : q 48 = false := by
    show run ins (Rd.const 451).σ 48 = false
    rw [run_eq _ _ hσ (by decide)]
    show cSpec [stp 850 (48 - 100), stp2 400 1251 (48 - 100)] _ = false
    rw [show stp 850 (48 - 100) = false by decide, show stp2 400 1251 (48 - 100) = false by decide]
    simp [cSpec]
  have e499 : q 499 = false := by
    show run ins (Rd.const 451).σ 499 = false
    rw [run_eq _ _ hσ (by decide)]
    show cSpec [stp 850 (499 - 100), stp2 400 1251 (499 - 100)]
      (run ins (Rd.const 451).σ (499 - 451)) = false
    rw [show stp 850 (499 - 100) = true by decide, show stp2 400 1251 (499 - 100) = false by decide]
    exact e48
  have e950 : q 950 = false := by
    show run ins (Rd.const 451).σ 950 = false
    rw [run_eq _ _ hσ (by decide)]
    show cSpec [stp 850 (950 - 100), stp2 400 1251 (950 - 100)]
      (run ins (Rd.const 451).σ (950 - 451)) = false
    rw [show stp 850 (950 - 100) = false by decide, show stp2 400 1251 (950 - 100) = true by decide]
    exact e499
  exact ⟨e949, e950,
    wit_mid (by decide) (by decide) (by decide) (by decide) (by decide) _ (by decide) (by decide),
    by decide⟩

/-! ## 8. bd_ctree: the nodes, and the one-node tree -/

/-- The bd_c3 / bd_c4 real INITs with rst read 0 are the C-element law, so
`cel_box_exact` is the exact own-loop condition of every ctree node. -/
theorem c3_cspec : ∀ a b c q : Bool, CTree.c3r false a b c q = cSpec [a, b, c] q := by decide
theorem c4_cspec : ∀ a b c d q : Bool, CTree.c4r false a b c d q = cSpec [a, b, c, d] q := by
  decide
theorem c2_cspec : ∀ a b q : Bool, CTree.c2r false a b q = cSpec [a, b] q := by decide

/-- **`ctree1_box_exact`**: a one-node bd_ctree (a bd_c2 root fed by two port
wires, reads in `[Alo, Ahi]`, `[Blo, Bhi]`), every leaf's next switch at least
`E` after the root's output edge (H_ACK, launched from the edge itself):
correct for every map in the box **iff** `Qhi ≤ E + min(Alo, Blo)`. The
row `bd_ctree.node_fork` instead asks `Spread + fmax ≤ E` with the port
wires' spread (`hi - lo`) in `Spread`: that spread cancels. -/
theorem ctree1_box_exact {Alo Ahi Blo Bhi Qlo Qhi E : Int}
    (h0A : 0 ≤ Alo) (hA : Alo ≤ Ahi) (h0B : 0 ≤ Blo) (hB : Blo ≤ Bhi)
    (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi) (hE : 1 ≤ E) :
    (∀ (a b : Int → Bool) (pa pb : Rd), Mono pa → Mono pb →
        Alo ≤ pa.lo → pa.hi ≤ Ahi → Blo ≤ pb.lo → pb.hi ≤ Bhi →
        HClient (insAB a b pa pb) a pa 0 E → HServer (insAB a b pa pb) b pb 0 E 0 →
        UxaOK a b pa pb Qlo Qhi) ↔
      (Qhi ≤ E + Alo ∧ Qhi ≤ E + Blo) := by
  have h := uxa_box_exact (Xlo := 0) (Eo := E) (K := 0) h0A hA h0B hB hQ1 hQ (Int.le_refl 0) hE
    (Int.le_refl 0)
  rw [h]; omega

end Formal.Cells.NecessityMerge
