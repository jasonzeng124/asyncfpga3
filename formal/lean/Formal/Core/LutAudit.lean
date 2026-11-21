import Formal.Core.LutTree
import Formal.Core.LutCells

/-!
# Formal.Core.LutAudit — function-hazard audit of every LUT in the cell library

Shard A, Track 4. Notes: `formal/notes/A-lut-audit.md`.

The LUT instances come from `Formal.Core.LutCells`, which is GENERATED from
`cells/rtl/*.v` by `formal/tools-A/lut_extract.py` (INIT, pin map, file:line).
The Kleene semantics is `Formal.Core.LutTree.evalTree` (the mux tree), proved
equal to the INIT-table semantics by `evalTree_eq_tableEval`.

Contents
1. Per-output pin list (root first), constant pins filled in (`fill`), the
   Kleene output `outK` on a vector of the FREE (non-constant) pins and the
   Boolean output `outB`. `outK_kv`: Booleans agree. `outK_eq_ofBool_iff`:
   Kleene value of a sub-cube is `c` iff every vertex of it gives `c`.
2. Hazard definitions on a transition `old → new` of the free pins.
   * `StaticHF` (Eichelberger 1965): `f old = f new = c` and every vertex of
     the transition cube gives `c`. Kleene form: `outK (mergeK old new) = c`
     (`staticHF_iff_kleene`).
   * `DynHF` (Unger 1969; Nowick & Dill 1995, Def. "dynamic function
     hazard"): `f old ≠ f new` and there are no `C ∈ [old,new]`,
     `D ∈ [C,new]` with `f C = f new`, `f D = f old`; i.e. every monotone
     vertex path changes the output exactly once. Kleene form
     (`dynHF_iff_kleene`): every vertex `C` of the cube with `f C = f new`
     has `outK (mergeK C new) = f new`.
   * Bool checkers `sHFk`/`dHFk` with `sHFk_iff`/`dHFk_iff`.
   * `sic_hazardFree`: every single-input change is hazard-free (static or
     dynamic) — the function-level counterpart of `PhysTree.sic_glitch_free`.
3. Bridge to the timed mux tree: `lut_static_glitch_free` (static
   hazard-free ⇒ the physical output is constant for ANY delays, under the
   explicit hypotheses `H_sram`, `H_mux_kleene` of `LutTree.PhysTree`).
   `dyn_single_window` (with `dyn_stays_new`, `dyn_never_back`): for a
   dynamic hazard-free transition, under any monotone progress of the pins the
   Kleene output goes old → X → new and never back (one switching window).
4. The audit: counts of MIC transitions per output, by class, for every
   extracted LUT (`audit_*`, kernel `decide +kernel`; no native code).
5. Protocol transitions of bd_ce, bd_link, bd_latch, bd_arb: which multi-input
   changes the four-phase environment can present, and their class.
-/

namespace Formal.Core.LutAudit

open Formal.Core.LutTree Formal.Core.LutTree.K3 Formal.Core.LutTree.PhysTree Formal.Core.LutCells

/-! ## 1. Outputs as functions of the free pins -/

/-- The constant a pin is tied to, if any. -/
def _root_.Formal.Core.LutCells.Pin.const : Pin → Option Bool
  | .c0 => some false
  | .c1 => some true
  | _ => none

/-- Fill a root-first free-pin vector into the full root-first pin vector.
(Missing entries read as `zero`; only correct-length vectors are ever used.) -/
def fill : List Pin → List K3 → List K3
  | [], _ => []
  | p :: ps, xs =>
      match p.const with
      | some b => ofBool b :: fill ps xs
      | none => xs.headD .zero :: fill ps xs.tail

/-- Boolean `fill`. -/
def fillB : List Pin → List Bool → List Bool
  | [], _ => []
  | p :: ps, xs =>
      match p.const with
      | some b => b :: fillB ps xs
      | none => xs.headD false :: fillB ps xs.tail

/-- Number of free pins. -/
def nfree : List Pin → Nat
  | [] => 0
  | p :: ps => (if p.const.isSome then 0 else 1) + nfree ps

/-- Pins seen by output `o`, ROOT FIRST (`[I5, …, I0]`): O5 of a LUT6_2 is
the lower LUT5 and does not see I5 (the root). -/
def opins (L : LutInst) : OutSel → List Pin
  | .O5 => L.pins.reverse.tail
  | _ => L.pins.reverse

/-- The table the output's mux tree reads (O5 = INIT[31:0]). -/
def effTable (L : LutInst) : OutSel → List Bool → Bool
  | .O5 => fun w => initFun L.init (false :: w)
  | _ => initFun L.init

/-- Kleene output (mux-tree semantics) on a root-first free-pin vector. -/
def outK (L : LutInst) (o : OutSel) (v : List K3) : K3 :=
  evalTree (fill (opins L o) v) (effTable L o)

/-- Boolean output. -/
def outB (L : LutInst) (o : OutSel) (w : List Bool) : Bool :=
  effTable L o (fillB (opins L o) w)

abbrev kv (w : List Bool) : List K3 := w.map ofBool

theorem fill_kv : ∀ (ps : List Pin) (w : List Bool), fill ps (kv w) = kv (fillB ps w)
  | [], _ => rfl
  | p :: ps, w => by
      cases hp : p.const with
      | some b => simp [fill, fillB, hp, fill_kv ps w]
      | none =>
          cases w with
          | nil =>
              have h := fill_kv ps []
              simp only [kv, List.map_nil] at h
              simp [fill, fillB, hp, h]
          | cons b w => simp [fill, fillB, hp, fill_kv ps w]

theorem outK_kv (L : LutInst) (o : OutSel) (w : List Bool) :
    outK L o (kv w) = ofBool (outB L o w) := by
  simp only [outK, outB, fill_kv, evalTree_ofBool]

theorem consistent_kv : ∀ (w u : List Bool), Consistent (kv w) u ↔ u = w
  | [], [] => by simp [Consistent]
  | [], _ :: _ => by simp [Consistent]
  | _ :: _, [] => by simp [Consistent]
  | a :: w, b :: u => by
      simp only [List.map_cons, Consistent, consistent_kv w u, List.cons.injEq]
      cases a <;> cases b <;> simp [ofBool]

theorem exists_consistent (v : List K3) : ∃ w, Consistent v w := by
  obtain ⟨w, hw⟩ := List.exists_mem_of_ne_nil _ (addrs_ne_nil v)
  exact ⟨w, (mem_addrs_iff v w).1 hw⟩

theorem consistent_nil_iff (u : List Bool) : Consistent [] u ↔ u = [] := by
  cases u <;> simp [Consistent]

theorem ofBool_cases (b c : Bool) : (K3.X = ofBool c ∨ ofBool b = ofBool c) ↔ c = b := by
  cases b <;> cases c <;> simp [ofBool]

theorem consistent_fill : ∀ (ps : List Pin) (v : List K3) (u : List Bool),
    Consistent (fill ps v) u ↔ ∃ w, Consistent v w ∧ u = fillB ps w
  | [], v, u => by
      simp only [fill, fillB, consistent_nil_iff]
      constructor
      · intro h; obtain ⟨w, hw⟩ := exists_consistent v; exact ⟨w, hw, h⟩
      · rintro ⟨w, _, h⟩; exact h
  | p :: ps, v, u => by
      cases hp : p.const with
      | some b =>
          cases u with
          | nil => simp [fill, fillB, hp, Consistent]
          | cons c u =>
              simp only [fill, fillB, hp, Consistent, consistent_fill ps v u, List.cons.injEq]
              constructor
              · rintro ⟨h1, w, hw, hu⟩
                refine ⟨w, hw, ?_, hu⟩
                cases b <;> cases c <;> simp_all [ofBool]
              · rintro ⟨w, hw, hc, hu⟩
                subst hc
                exact ⟨Or.inr rfl, w, hw, hu⟩
      | none =>
          cases u with
          | nil =>
              simp only [fill, fillB, hp, Consistent, false_iff, not_exists, not_and]
              intro w _ h; exact List.cons_ne_nil _ _ h.symm
          | cons c u =>
              cases v with
              | nil =>
                  simp only [fill, fillB, hp, List.headD_nil, List.tail_nil, Consistent,
                    consistent_fill ps [] u, consistent_nil_iff, List.cons.injEq]
                  constructor
                  · rintro ⟨h1, w, hw, hu⟩
                    subst hw
                    refine ⟨[], rfl, ?_, hu⟩
                    cases c <;> simp_all [ofBool]
                  · rintro ⟨w, hw, hc, hu⟩
                    subst hw
                    simp only [List.headD_nil] at hc
                    subst hc
                    exact ⟨Or.inr rfl, [], rfl, hu⟩
              | cons k v =>
                  simp only [fill, fillB, hp, List.headD_cons, List.tail_cons, Consistent,
                    consistent_fill ps v u, List.cons.injEq]
                  constructor
                  · rintro ⟨h1, w, hw, hu⟩
                    exact ⟨c :: w, ⟨h1, hw⟩, rfl, hu⟩
                  · rintro ⟨w, hw, hc, hu⟩
                    cases w with
                    | nil => simp [Consistent] at hw
                    | cons d w =>
                        obtain ⟨h1, hw⟩ := hw
                        simp only [List.headD_cons, List.tail_cons] at hc hu
                        subst hc
                        exact ⟨h1, w, hw, hu⟩

/-- **Kleene value of a sub-cube = common value of its vertices.** -/
theorem outK_eq_ofBool_iff (L : LutInst) (o : OutSel) (v : List K3) (c : Bool) :
    outK L o v = ofBool c ↔ ∀ w, Consistent v w → outB L o w = c := by
  unfold outK outB
  rw [evalTree_eq_tableEval]
  have key : (∀ u, Consistent (fill (opins L o) v) u → effTable L o u = c) ↔
      (∀ w, Consistent v w → effTable L o (fillB (opins L o) w) = c) := by
    constructor
    · intro h w hw; exact h _ ((consistent_fill _ v _).2 ⟨w, hw, rfl⟩)
    · intro h u hu
      obtain ⟨w, hw, rfl⟩ := (consistent_fill _ v u).1 hu
      exact h w hw
  cases c
  · simpa using (tableEval_eq_zero_iff _ _).trans key
  · simpa using (tableEval_eq_one_iff _ _).trans key

/-! ## 2. Hazard definitions -/

section hazards
variable (L : LutInst) (o : OutSel) (old new : List Bool)

/-- Vertex `w` lies in the transition cube `[a, b]`. -/
abbrev InCube (a b w : List Bool) : Prop := Consistent (mergeK a b) w

/-- Static function-hazard-free transition (Eichelberger). -/
def StaticHF : Prop :=
  outB L o old = outB L o new ∧ ∀ w, InCube old new w → outB L o w = outB L o old

/-- Dynamic function-hazard-free transition (Unger; Nowick–Dill): no
`C ∈ [old,new]`, `D ∈ [C,new]` with `f C = f new` and `f D = f old`. -/
def DynHF : Prop :=
  outB L o old ≠ outB L o new ∧
    ¬ ∃ C D, InCube old new C ∧ InCube C new D ∧
      outB L o C = outB L o new ∧ outB L o D = outB L o old

theorem staticHF_iff_kleene :
    StaticHF L o old new ↔
      outB L o old = outB L o new ∧ outK L o (mergeK old new) = ofBool (outB L o old) := by
  unfold StaticHF; rw [outK_eq_ofBool_iff]

theorem dynHF_iff_kleene :
    DynHF L o old new ↔
      outB L o old ≠ outB L o new ∧
        ∀ C, InCube old new C → outB L o C = outB L o new →
          outK L o (mergeK C new) = ofBool (outB L o new) := by
  unfold DynHF
  constructor
  · rintro ⟨hne, hno⟩
    refine ⟨hne, fun C hC hCv => (outK_eq_ofBool_iff _ _ _ _).2 fun D hD => ?_⟩
    cases hD' : decide (outB L o D = outB L o new)
    · exfalso
      apply hno
      refine ⟨C, D, hC, hD, hCv, ?_⟩
      have hD'' : outB L o D ≠ outB L o new := by simpa using hD'
      revert hD'' hne
      cases outB L o D <;> cases outB L o new <;> cases outB L o old <;> simp
    · simpa using hD'
  · rintro ⟨hne, h⟩
    refine ⟨hne, ?_⟩
    rintro ⟨C, D, hC, hD, hCv, hDv⟩
    have := (outK_eq_ofBool_iff _ _ _ _).1 (h C hC hCv) D hD
    exact hne (hDv.symm.trans this)

/-- Bool checker, static. -/
def sHFk : Bool :=
  outB L o old == outB L o new && decide (outK L o (mergeK old new) = ofBool (outB L o old))

/-- Bool checker, dynamic (Kleene form, enumerating the cube). -/
def dHFk : Bool :=
  outB L o old != outB L o new &&
    (addrs (mergeK old new)).all fun C =>
      outB L o C != outB L o new || decide (outK L o (mergeK C new) = ofBool (outB L o new))

theorem sHFk_iff : sHFk L o old new = true ↔ StaticHF L o old new := by
  rw [staticHF_iff_kleene]; simp [sHFk]

theorem dHFk_iff : dHFk L o old new = true ↔ DynHF L o old new := by
  rw [dynHF_iff_kleene]
  simp only [dHFk, Bool.and_eq_true, bne_iff_ne, ne_eq, List.all_eq_true, Bool.or_eq_true,
    decide_eq_true_eq, mem_addrs_iff]
  constructor
  · rintro ⟨h1, h2⟩
    exact ⟨h1, fun C hC hCv => (h2 C hC).resolve_left (by simp [hCv])⟩
  · rintro ⟨h1, h2⟩
    refine ⟨h1, fun C hC => ?_⟩
    by_cases hCv : outB L o C = outB L o new
    · exact Or.inr (h2 C hC hCv)
    · exact Or.inl hCv

/-- A transition is function-hazard-free if it is static-HF or dynamic-HF. -/
def hazardFree : Bool := sHFk L o old new || dHFk L o old new

/-- Every single-input change is function-hazard-free (static or dynamic). -/
theorem sic_hazardFree (hl : old.length = new.length) (hd : ndiff old new ≤ 1) :
    hazardFree L o old new = true := by
  have hcube : ∀ w, InCube old new w → w = old ∨ w = new :=
    fun w hw => consistent_mergeK_sic old new w hl hd hw
  unfold hazardFree
  by_cases he : outB L o old = outB L o new
  · have : sHFk L o old new = true := (sHFk_iff ..).2 ⟨he, fun w hw => by
      rcases hcube w hw with rfl | rfl
      · rfl
      · exact he.symm⟩
    simp [this]
  · have : dHFk L o old new = true := (dHFk_iff ..).2 ⟨he, by
      rintro ⟨C, D, hC, hD, hCv, hDv⟩
      rcases hcube C hC with rfl | rfl
      · exact he hCv
      · have := consistent_mergeK_self C D hD
        subst this
        exact he (hCv.symm.trans hDv).symm⟩
    simp [this]

end hazards

/-! ## 3. Bridge to the timed mux tree (`LutTree.PhysTree`) -/

/-- **Static hazard-free ⇒ no glitch, for any delays.** A physical mux tree
`P` realising output `o` of `L` (its leaves are that output's INIT bits) whose
pins are abstracted by the transition cube (constant pins steady, the changing
pins anything) holds the common value at every instant. Hypotheses
`H_sram`, `H_mux_kleene` are those of `LutTree`. -/
theorem lut_static_glitch_free (L : LutInst) (o : OutSel) (old new : List Bool)
    {n : Nat} (P : PhysTree n) (hs : P.H_sram) (hm : P.H_mux_kleene)
    (hinit : P.init = effTable L o)
    (hv : P.Abstracts (fill (opins L o) (mergeK old new)))
    (h : StaticHF L o old new) (τ : Time) : P.y [] τ = ofBool (outB L o old) := by
  refine P.glitch_free hs hm hv _ ?_ τ
  intro u hu
  obtain ⟨w, hw, rfl⟩ := (consistent_fill _ _ u).1 hu
  rw [hinit]
  exact h.2 w hw

/-! ### Dynamic transitions in time: one switching window

A transition's progress is a vector of stages per pin. `dyn_single_window`:
for a dynamic hazard-free transition the output's Kleene value is monotone
old → X → new under ANY monotone progress of the pins. -/

/-- Level of one pin during a transition `a → b`, at progress stage `s`
(0 = not yet moved, 1 = in flight, ≥ 2 = arrived). Steady pins are steady. -/
def stageK (a b : Bool) (s : Nat) : K3 :=
  if a = b then ofBool a else if s = 0 then ofBool a else if s = 1 then .X else ofBool b

def stageVec : List Bool → List Bool → List Nat → List K3
  | a :: as, b :: bs, s :: ss => stageK a b s :: stageVec as bs ss
  | _, _, _ => []

/-- Pointwise `≤` of progress vectors. -/
def StLe : List Nat → List Nat → Prop
  | [], [] => True
  | x :: xs, y :: ys => x ≤ y ∧ StLe xs ys
  | _, _ => False

theorem head_L1 (a b c : Bool) (x y : Nat) (hxy : x ≤ y)
    (hc : stageK a b y = .X ∨ stageK a b y = ofBool c) :
    ∃ d, (stageK a b x = .X ∨ stageK a b x = ofBool d) ∧
      ((if d = b then ofBool d else .X) = .X ∨ (if d = b then ofBool d else .X) = ofBool c) := by
  by_cases hab : a = b
  · subst hab
    refine ⟨a, by simp [stageK], ?_⟩
    simp [stageK] at hc ⊢
    cases a <;> cases c <;> simp_all [ofBool]
  · by_cases hx0 : x = 0
    · refine ⟨a, by simp [stageK, hab, hx0], ?_⟩
      simp [hab]
    · by_cases hx1 : x = 1
      · refine ⟨c, by simp [stageK, hab, hx1], ?_⟩
        by_cases hcb : c = b <;> simp [hcb]
      · have hy0 : y ≠ 0 := by omega
        have hy1 : y ≠ 1 := by omega
        simp [stageK, hab, hy0, hy1] at hc
        refine ⟨b, by simp [stageK, hab, hx0, hx1], ?_⟩
        cases b <;> cases c <;> simp_all [ofBool]

theorem head_L2 (a b u : Bool) (x y : Nat) (hxy : x ≤ y)
    (hu : stageK a b x = .X ∨ stageK a b x = ofBool u) :
    ∃ d, (stageK a b y = .X ∨ stageK a b y = ofBool d) ∧
      ((if u = b then ofBool u else .X) = .X ∨ (if u = b then ofBool u else .X) = ofBool d) := by
  by_cases hab : a = b
  · subst hab
    refine ⟨a, by simp [stageK], ?_⟩
    simp [stageK] at hu
    cases a <;> cases u <;> simp_all [ofBool]
  · by_cases hy0 : y = 0
    · have hx0 : x = 0 := by omega
      simp [stageK, hab, hx0] at hu
      refine ⟨a, by simp [stageK, hab, hy0], ?_⟩
      cases a <;> cases u <;> simp_all [ofBool]
    · by_cases hy1 : y = 1
      · refine ⟨u, by simp [stageK, hab, hy1], ?_⟩
        by_cases hub : u = b <;> simp [hub]
      · refine ⟨b, by simp [stageK, hab, hy0, hy1], ?_⟩
        by_cases hub : u = b <;> simp [hub]

theorem stage_L1 : ∀ (o n : List Bool) (s s' : List Nat) (v : List Bool),
    o.length = n.length → s.length = o.length → StLe s s' →
    Consistent (stageVec o n s') v →
    ∃ B, Consistent (stageVec o n s) B ∧ Consistent (mergeK B n) v
  | [], [], [], [], v, _, _, _, h => ⟨[], by simp [stageVec, Consistent], by
      cases v <;> simp_all [stageVec, mergeK, Consistent]⟩
  | a :: o, b :: n, x :: s, y :: s', v, h1, h2, h3, h4 => by
      cases v with
      | nil => simp [stageVec, Consistent] at h4
      | cons c v =>
        simp only [stageVec, Consistent] at h4
        simp only [StLe] at h3
        obtain ⟨B, hB1, hB2⟩ := stage_L1 o n s s' v (by simpa using h1) (by simpa using h2) h3.2 h4.2
        obtain ⟨d, hd1, hd2⟩ := head_L1 a b c x y h3.1 h4.1
        exact ⟨d :: B, ⟨hd1, hB1⟩, by simp only [mergeK, Consistent]; exact ⟨hd2, hB2⟩⟩
  | [], _ :: _, _, _, _, h1, _, _, _ => by simp at h1
  | _ :: _, [], _, _, _, h1, _, _, _ => by simp at h1
  | [], [], _ :: _, _, _, _, h2, _, _ => by simp at h2
  | _ :: _, _ :: _, [], _, _, _, h2, _, _ => by simp at h2
  | [], [], [], _ :: _, _, _, _, h3, _ => by simp [StLe] at h3
  | _ :: _, _ :: _, _ :: _, [], _, _, _, h3, _ => by simp [StLe] at h3

theorem stage_L2 : ∀ (o n : List Bool) (s s' : List Nat) (u : List Bool),
    o.length = n.length → s.length = o.length → StLe s s' →
    Consistent (stageVec o n s) u →
    ∃ v, Consistent (stageVec o n s') v ∧ Consistent (mergeK u n) v
  | [], [], [], [], u, _, _, _, h => ⟨[], by simp [stageVec, Consistent], by
      cases u <;> simp_all [stageVec, mergeK, Consistent]⟩
  | a :: o, b :: n, x :: s, y :: s', u, h1, h2, h3, h4 => by
      cases u with
      | nil => simp [stageVec, Consistent] at h4
      | cons c u =>
        simp only [stageVec, Consistent] at h4
        simp only [StLe] at h3
        obtain ⟨V, hV1, hV2⟩ := stage_L2 o n s s' u (by simpa using h1) (by simpa using h2) h3.2 h4.2
        obtain ⟨d, hd1, hd2⟩ := head_L2 a b c x y h3.1 h4.1
        exact ⟨d :: V, ⟨hd1, hV1⟩, by simp only [mergeK, Consistent]; exact ⟨hd2, hV2⟩⟩
  | [], _ :: _, _, _, _, h1, _, _, _ => by simp at h1
  | _ :: _, [], _, _, _, h1, _, _, _ => by simp at h1
  | [], [], _ :: _, _, _, _, h2, _, _ => by simp at h2
  | _ :: _, _ :: _, [], _, _, _, h2, _, _ => by simp at h2
  | [], [], [], _ :: _, _, _, _, h3, _ => by simp [StLe] at h3
  | _ :: _, _ :: _, _ :: _, [], _, _, _, h3, _ => by simp [StLe] at h3

theorem stage_sub : ∀ (o n : List Bool) (s : List Nat) (w : List Bool),
    s.length = o.length → Consistent (stageVec o n s) w → Consistent (mergeK o n) w
  | a :: o, b :: n, x :: s, c :: w, hl, h => by
      simp only [stageVec, Consistent, mergeK] at h ⊢
      refine ⟨?_, stage_sub o n s w (by simpa using hl) h.2⟩
      have := h.1
      by_cases hab : a = b
      · subst hab; simp_all [stageK]
      · simp [hab]
  | a :: o, b :: n, x :: s, [], _, h => by simp [stageVec, Consistent] at h
  | [], _, _, w, _, h => by cases w <;> simp_all [stageVec, Consistent, mergeK]
  | _ :: _, [], _, w, _, h => by cases w <;> simp_all [stageVec, Consistent, mergeK]
  | _ :: _, _ :: _, [], w, hl, h => by simp at hl

/-- **Dynamic hazard-free ⇒ once the Kleene output reaches the new value it
stays there** as the changing pins progress (in any order and overlap). -/
theorem dyn_stays_new {L : LutInst} {o : OutSel} {old new : List Bool}
    (h : DynHF L o old new) (hl : old.length = new.length) {s s' : List Nat}
    (hs : s.length = old.length) (hle : StLe s s')
    (hK : outK L o (stageVec old new s) = ofBool (outB L o new)) :
    outK L o (stageVec old new s') = ofBool (outB L o new) := by
  rw [outK_eq_ofBool_iff] at hK ⊢
  intro v hv
  obtain ⟨B, hB1, hB2⟩ := stage_L1 old new s s' v hl hs hle hv
  have hm := ((dynHF_iff_kleene ..).1 h).2 B (stage_sub old new s B hs hB1) (hK B hB1)
  exact (outK_eq_ofBool_iff ..).1 hm v hB2

/-- **… and once it has left the old value it never returns to it.** -/
theorem dyn_never_back {L : LutInst} {o : OutSel} {old new : List Bool}
    (h : DynHF L o old new) (hl : old.length = new.length) {s s' : List Nat}
    (hs : s.length = old.length) (hle : StLe s s')
    (hK : outK L o (stageVec old new s) ≠ ofBool (outB L o old)) :
    outK L o (stageVec old new s') ≠ ofBool (outB L o old) := by
  intro hK'
  apply hK
  rw [outK_eq_ofBool_iff] at hK' ⊢
  intro u hu
  have hne := ((dynHF_iff_kleene ..).1 h).1
  cases hb : (outB L o u == outB L o old)
  · exfalso
    have hun : outB L o u = outB L o new := by
      have : outB L o u ≠ outB L o old := by simpa using hb
      revert this hne; cases outB L o u <;> cases outB L o old <;> cases outB L o new <;> simp
    obtain ⟨v, hv1, hv2⟩ := stage_L2 old new s s' u hl hs hle hu
    have hm := ((dynHF_iff_kleene ..).1 h).2 u (stage_sub old new s u hs hu) hun
    have := (outK_eq_ofBool_iff ..).1 hm v hv2
    exact hne ((hK' v hv1).symm.trans this)
  · simpa using hb

/-- **Single switching window.** Pins follow a monotone progress schedule
`σ` (each changing pin: old, then in flight, then new; any skew and overlap).
For a dynamic hazard-free transition the Kleene value of the output is `old`,
then `X`, then `new`, never going back. With `PhysTree.root_sound` the
physical output therefore holds `old` before one window and `new` after it.
Inside the window the Kleene model says nothing (an X), so "exactly one
edge" there needs a stronger mux hypothesis than `H_mux_kleene`. -/
theorem dyn_single_window {L : LutInst} {o : OutSel} {old new : List Bool}
    (h : DynHF L o old new) (hl : old.length = new.length) (σ : Time → List Nat)
    (hlen : ∀ τ, (σ τ).length = old.length)
    (hmono : ∀ τ₁ τ₂, τ₁ ≤ τ₂ → StLe (σ τ₁) (σ τ₂)) {τ₁ τ₂ : Time} (h12 : τ₁ ≤ τ₂) :
    (outK L o (stageVec old new (σ τ₁)) = ofBool (outB L o new) →
      outK L o (stageVec old new (σ τ₂)) = ofBool (outB L o new)) ∧
    (outK L o (stageVec old new (σ τ₁)) ≠ ofBool (outB L o old) →
      outK L o (stageVec old new (σ τ₂)) ≠ ofBool (outB L o old)) :=
  ⟨dyn_stays_new h hl (hlen τ₁) (hmono τ₁ τ₂ h12),
   dyn_never_back h hl (hlen τ₁) (hmono τ₁ τ₂ h12)⟩


/-- All `3^m` Kleene vectors. -/
def k3vecs : Nat → List (List K3)
  | 0 => [[]]
  | m + 1 => [K3.zero, K3.one, K3.X].flatMap fun k => (k3vecs m).map (k :: ·)

/-- Scaling probe (and a fidelity check on a real INIT): for all 3^6 = 729
Kleene vectors on bd_c4's six free pins, the mux tree equals the INIT-table
semantics (`decide +kernel`, ≈ 8 s). -/
theorem c4_tree_eq_table_3pow6 : (k3vecs 6).all (fun v =>
    decide (outK bd_c4_u .O v = tableEval (fill (opins bd_c4_u .O) v) (effTable bd_c4_u .O))) = true := by
  decide +kernel

/-! ## 4. The audit over every extracted LUT -/

/-- Which free positions (root first) are the output's own feedback. -/
def fbMask : List Pin → List Bool
  | [] => []
  | p :: ps =>
      match p.const with
      | some _ => fbMask ps
      | none => (match p with | .fb _ => true | _ => false) :: fbMask ps

/-- All Boolean vectors of length `m`. -/
def vecs (m : Nat) : List (List Bool) := addrs (List.replicate m .X)

/-- Feedback pins are unchanged (fundamental mode: the inputs move, the
loop's own output is what responds). -/
def sameOn : List Bool → List Bool → List Bool → Bool
  | b :: ms, x :: xs, y :: ys => (!b || x == y) && sameOn ms xs ys
  | _, _, _ => true

/-- Counts `(static HF, static hazard, dynamic HF, dynamic hazard)` over all
multi-input changes (≥ 2 free pins move) with the feedback pins held. -/
def audit (L : LutInst) (o : OutSel) : Nat × Nat × Nat × Nat :=
  let ps := opins L o
  let m := nfree ps
  let fm := fbMask ps
  (vecs m).foldl (fun acc old =>
    (vecs m).foldl (fun acc new =>
      if sameOn fm old new && 2 ≤ ndiff old new then
        let (a, b, c, d) := acc
        if outB L o old == outB L o new then
          (if sHFk L o old new then (a + 1, b, c, d) else (a, b + 1, c, d))
        else
          (if dHFk L o old new then (a, b, c + 1, d) else (a, b, c, d + 1))
      else acc) acc) (0, 0, 0, 0)

/-! ### Transition classes -/

inductive Cls where
  | sic   -- at most one free pin moves (always hazard-free: `sic_hazardFree`)
  | sHF   -- static, function-hazard-free
  | sHZ   -- static function hazard
  | dHF   -- dynamic, function-hazard-free
  | dHZ   -- dynamic function hazard
  deriving DecidableEq, Repr

def classify (L : LutInst) (o : OutSel) (old new : List Bool) : Cls :=
  if ndiff old new ≤ 1 then .sic
  else if outB L o old == outB L o new then (if sHFk L o old new then .sHF else .sHZ)
  else (if dHFk L o old new then .dHF else .dHZ)

theorem classify_sHF {L o old new} (h : classify L o old new = .sHF) : StaticHF L o old new := by
  unfold classify at h
  split at h; · cases h
  split at h
  · split at h
    · exact (sHFk_iff ..).1 (by assumption)
    · cases h
  · split at h <;> cases h

theorem classify_sHZ {L o old new} (h : classify L o old new = .sHZ) :
    outB L o old = outB L o new ∧ ¬ StaticHF L o old new := by
  unfold classify at h
  split at h; · cases h
  split at h
  · split at h
    · cases h
    · rename_i h1 h2
      exact ⟨by simpa using h1, fun h' => h2 ((sHFk_iff ..).2 h')⟩
  · split at h <;> cases h

theorem classify_dHF {L o old new} (h : classify L o old new = .dHF) : DynHF L o old new := by
  unfold classify at h
  split at h; · cases h
  split at h
  · split at h <;> cases h
  · split at h
    · exact (dHFk_iff ..).1 (by assumption)
    · cases h

theorem classify_dHZ {L o old new} (h : classify L o old new = .dHZ) :
    outB L o old ≠ outB L o new ∧ ¬ DynHF L o old new := by
  unfold classify at h
  split at h; · cases h
  split at h
  · split at h <;> cases h
  · split at h
    · cases h
    · rename_i h1 h2
      exact ⟨by simpa using h1, fun h' => h2 ((dHFk_iff ..).2 h')⟩

/-! ### Audit table: every extracted LUT output, all multi-input changes
(feedback held), counts `(sHF, sHZ, dHF, dHZ)`. The numbers were first computed by an
independent vertex-enumeration script (`/tmp`-only, see notes) and are CHECKED here by
kernel `decide`. LUTs with one free pin have no multi-input change: `(0,0,0,0)`. -/

theorem audit_bd_arbcell_ugrant_O5 : audit bd_arbcell_ugrant .O5 = (8, 8, 16, 0) := by decide +kernel
theorem audit_bd_arbcell_ugrant_O6 : audit bd_arbcell_ugrant .O6 = (8, 8, 16, 0) := by decide +kernel
theorem audit_bd_arbiter_ustate_O5 : audit bd_arbiter_ustate .O5 = (128, 0, 224, 0) := by decide +kernel
theorem audit_bd_arbiter_ustate_O6 : audit bd_arbiter_ustate .O6 = (148, 76, 104, 24) := by decide +kernel
theorem audit_bd_arbiter_ugrant_O5 : audit bd_arbiter_ugrant .O5 = (8, 8, 16, 0) := by decide +kernel
theorem audit_bd_arbiter_ugrant_O6 : audit bd_arbiter_ugrant .O6 = (8, 8, 16, 0) := by decide +kernel
theorem audit_bd_c2_u_O : audit bd_c2_u .O = (16, 20, 24, 4) := by decide +kernel
theorem audit_bd_c2_set_u_O : audit bd_c2_set_u .O = (16, 20, 24, 4) := by decide +kernel
theorem audit_bd_c2n_u_O : audit bd_c2n_u .O = (16, 20, 24, 4) := by decide +kernel
theorem audit_bd_c2n_set_u_O : audit bd_c2n_set_u .O = (16, 20, 24, 4) := by decide +kernel
theorem audit_bd_c3_u_O : audit bd_c3_u .O = (148, 76, 104, 24) := by decide +kernel
theorem audit_bd_c4_u_O : audit bd_c4_u .O = (880, 260, 424, 100) := by decide +kernel
theorem audit_bd_c2_norst_u_O : audit bd_c2_norst_u .O = (0, 4, 4, 0) := by decide +kernel
theorem audit_bd_c3_norst_u_O : audit bd_c3_norst_u .O = (24, 24, 16, 0) := by decide +kernel
theorem audit_bd_steer_u_O5 : audit bd_steer_u .O5 = (0, 2, 2, 0) := by decide +kernel
theorem audit_bd_steer_u_O6 : audit bd_steer_u .O6 = (0, 2, 2, 0) := by decide +kernel
theorem audit_bd_steer_uack_O : audit bd_steer_uack .O = (0, 2, 2, 0) := by decide +kernel
theorem audit_bd_bd2dr_u_O5 : audit bd_bd2dr_u .O5 = (0, 2, 2, 0) := by decide +kernel
theorem audit_bd_bd2dr_u_O6 : audit bd_bd2dr_u .O6 = (0, 2, 2, 0) := by decide +kernel
theorem audit_bd_dr2bd_u_O5 : audit bd_dr2bd_u .O5 = (0, 4, 4, 0) := by decide +kernel
theorem audit_bd_dr2bd_u_O6 : audit bd_dr2bd_u .O6 = (0, 4, 4, 0) := by decide +kernel
theorem audit_bd_dr2bd_uor_O : audit bd_dr2bd_uor .O = (0, 2, 2, 0) := by decide +kernel
theorem audit_bd_src_u_O : audit bd_src_u .O = (0, 0, 0, 0) := by decide +kernel
theorem audit_bd_latch_u_L38_O5 : audit bd_latch_u_L38 .O5 = (32, 32, 64, 0) := by decide +kernel
theorem audit_bd_latch_u_L38_O6 : audit bd_latch_u_L38 .O6 = (32, 32, 64, 0) := by decide +kernel
theorem audit_bd_latch_u_L44_O : audit bd_latch_u_L44 .O = (0, 4, 4, 0) := by decide +kernel
theorem audit_bd_latch_rst_u_t_O : audit bd_latch_rst_u_t .O = (16, 20, 24, 4) := by decide +kernel
theorem audit_bd_latch_rst_u_f_O : audit bd_latch_rst_u_f .O = (16, 20, 24, 4) := by decide +kernel
theorem audit_bd_delay_u_L126_O : audit bd_delay_u_L126 .O = (0, 0, 0, 0) := by decide +kernel
theorem audit_bd_delay_u_L135_O : audit bd_delay_u_L135 .O = (0, 0, 0, 0) := by decide +kernel
theorem audit_bd_delay_u_L138_t_O : audit bd_delay_u_L138_t .O = (0, 2, 2, 0) := by decide +kernel
theorem audit_bd_delay_u_L138_f_O : audit bd_delay_u_L138_f .O = (0, 2, 2, 0) := by decide +kernel
theorem audit_bd_delay_gated_u_L180_O : audit bd_delay_gated_u_L180 .O = (0, 0, 0, 0) := by decide +kernel
theorem audit_bd_delay_gated_u_L183_O : audit bd_delay_gated_u_L183 .O = (0, 2, 2, 0) := by decide +kernel
theorem audit_bd_datamux_u_L209_O5 : audit bd_datamux_u_L209 .O5 = (176, 192, 400, 64) := by decide +kernel
theorem audit_bd_datamux_u_L209_O6 : audit bd_datamux_u_L209 .O6 = (176, 192, 400, 64) := by decide +kernel
theorem audit_bd_datamux_u_L215_O : audit bd_datamux_u_L215 .O = (0, 12, 16, 4) := by decide +kernel
theorem audit_bd_link_dctl_ub_O : audit bd_link_dctl_ub .O = (148, 82, 106, 16) := by decide +kernel
theorem audit_bd_link_dctl_ua_O : audit bd_link_dctl_ua .O = (148, 82, 106, 16) := by decide +kernel
theorem audit_bd_link_dctl_uld_O : audit bd_link_dctl_uld .O = (168, 82, 102, 0) := by decide +kernel
theorem audit_bd_link_dctl_ult_O : audit bd_link_dctl_ult .O = (12, 12, 8, 0) := by decide +kernel
theorem audit_bd_mem_ubuf_O : audit bd_mem_ubuf .O = (0, 0, 0, 0) := by decide +kernel
theorem audit_bd_merge_uor_O : audit bd_merge_uor .O = (0, 2, 2, 0) := by decide +kernel
theorem audit_bd_merge_usel_O : audit bd_merge_usel .O = (0, 2, 2, 0) := by decide +kernel
theorem audit_bd_mlink_ctl_ux_O : audit bd_mlink_ctl_ux .O = (4, 16, 8, 4) := by decide +kernel
theorem audit_bd_mlink_ctl_uz_O : audit bd_mlink_ctl_uz .O = (36, 44, 60, 36) := by decide +kernel
theorem audit_bd_flink_ctl_uck_O : audit bd_flink_ctl_uck .O = (4, 16, 8, 4) := by decide +kernel
theorem audit_bd_flink_ctl_uq_O : audit bd_flink_ctl_uq .O = (0, 4, 4, 0) := by decide +kernel
theorem audit_bd_mux_uj0_O : audit bd_mux_uj0 .O = (148, 92, 92, 20) := by decide +kernel
theorem audit_bd_mux_uj1_O : audit bd_mux_uj1 .O = (148, 92, 92, 20) := by decide +kernel
theorem audit_bd_mux_uor_O : audit bd_mux_uor .O = (0, 2, 2, 0) := by decide +kernel

/-! ## 5. What the four-phase environment presents to each LUT

Free-pin vectors are ROOT FIRST (`opins`): the order is given per cell. -/

/-- Sweep: every `old → new` over the free pins satisfying `pre` is hazard-free. -/
def sweep (L : LutInst) (o : OutSel) (pre : List Bool → List Bool → Bool) : Bool :=
  let m := nfree (opins L o)
  (vecs m).all fun old => (vecs m).all fun new => !pre old new || hazardFree L o old new

/-- Positions where `msk` is false do not move. -/
def heldOff (msk old new : List Bool) : Bool := sameOn (msk.map (!·)) old new

/-- Every moving masked position moves to `dir` (after polarity `pol`). -/
def allTo (dir : Bool) : List Bool → List Bool → List Bool → List Bool → Bool
  | m :: ms, p :: ps, x :: xs, y :: ys =>
      (!(m && x != y) || (y ^^ p) == dir) && allTo dir ms ps xs ys
  | _, _, _, _ => true

/-- A C-element MIC from a settled state: only data pins move, all in the same
logical direction (`pol` marks the inverted input of `bd_c2n`), and the loop
was settled (`fb` value = output). -/
def celemMono (data pol : List Bool) (qpos : Nat) (L : LutInst) (o : OutSel)
    (old new : List Bool) : Bool :=
  outB L o old == old.getD qpos false && heldOff data old new &&
    (allTo true data pol old new || allTo false data pol old new)

/-! ### bd_ce: C-elements. Free pins `[rst, q, b, a]` (c2 family),
`[rst, q, c, b, a]` (c3), `[rst, q, d, c, b, a]` (c4), `[q, b, a]` /
`[q, c, b, a]` (norst). -/

/-- **Same-direction MICs are hazard-free on every C-element LUT.** From a
settled state, any set of data inputs moving together in one logical
direction (a join's requests rising together, or falling together in
return-to-zero; for `bd_c2n` `a` and `~b`) gives no function hazard, with rst
held at either value. -/
theorem celem_same_direction_hazard_free :
    sweep bd_c2_u .O (celemMono [false, false, true, true] [false, false, false, false] 1 bd_c2_u .O) ∧
    sweep bd_c2_set_u .O (celemMono [false, false, true, true] [false, false, false, false] 1 bd_c2_set_u .O) ∧
    sweep bd_c2n_u .O (celemMono [false, false, true, true] [false, false, true, false] 1 bd_c2n_u .O) ∧
    sweep bd_c2n_set_u .O (celemMono [false, false, true, true] [false, false, true, false] 1 bd_c2n_set_u .O) ∧
    sweep bd_c3_u .O (celemMono [false, false, true, true, true] [false, false, false, false, false] 1 bd_c3_u .O) ∧
    sweep bd_c4_u .O (celemMono [false, false, true, true, true, true] [false, false, false, false, false, false] 1 bd_c4_u .O) ∧
    sweep bd_c2_norst_u .O (celemMono [false, true, true] [false, false, false] 0 bd_c2_norst_u .O) ∧
    sweep bd_c3_norst_u .O (celemMono [false, true, true, true] [false, false, false, false] 0 bd_c3_norst_u .O) := by
  decide +kernel

/-- Reset dominates: while rst is held asserted, ANY change of the other pins
(feedback included) is static hazard-free. -/
theorem celem_reset_dominates :
    sweep bd_c2_u .O (fun a b => a.getD 0 false && b.getD 0 false) ∧
    sweep bd_c2_set_u .O (fun a b => a.getD 0 false && b.getD 0 false) ∧
    sweep bd_c2n_u .O (fun a b => a.getD 0 false && b.getD 0 false) ∧
    sweep bd_c2n_set_u .O (fun a b => a.getD 0 false && b.getD 0 false) ∧
    sweep bd_c3_u .O (fun a b => a.getD 0 false && b.getD 0 false) ∧
    sweep bd_c4_u .O (fun a b => a.getD 0 false && b.getD 0 false) := by
  decide +kernel

/-- Opposite-direction MIC on a two-input C-element is ALWAYS a static hazard
(either q). For `bd_c2` as the merge acknowledge `C(x_req, z_ack)` this is
x_req rising while z_ack is still falling from the other input's transaction:
exactly what bd_merge's precondition ("the second input may not assert until
the first transaction has FULLY COMPLETED") forbids. -/
theorem c2_opposite_direction_hazard (q : Bool) :
    classify bd_c2_u .O [false, q, true, false] [false, q, false, true] = .sHZ ∧
    classify bd_c2_u .O [false, q, false, true] [false, q, true, false] = .sHZ := by
  cases q <;> decide

/-! ### bd_link (Muller stage): `bd_c2n` with `a = req_in`, `b = c_next`;
free pins `[rst, c, c_next, req_in]`. With `c = 0` the next stage cannot
rise (it needs `c = 1`) and the previous one cannot fall (it needs `c = 1`), so
the only MIC is `req_in↑ ∥ c_next↓`; dually `req_in↓ ∥ c_next↑` with `c = 1`.
Both are logical same-direction changes of `C(a, ~b)`. -/

theorem link_mic_hazard_free :
    classify bd_c2n_u .O [false, false, true, false] [false, false, false, true] = .dHF ∧
    classify bd_c2n_u .O [false, true, false, true] [false, true, true, false] = .dHF := by
  decide

/-- The MIC the Muller pipeline CANNOT present (`req_in↑ ∥ c_next↑` with
`c = 0`) is the hazardous one. -/
theorem link_unreachable_mic_hazard :
    classify bd_c2n_u .O [false, false, false, false] [false, false, true, true] = .sHZ := by
  decide

/-! ### bd_latch pair (LUT6_2): free pins `[q1, d1, q0, en, d0]` for both
outputs (O5 = bit i, O6 = bit i+1). -/

/-- Closed latch: while `en = 0` and the stored bits are settled, any change of
the data pins (both bits) is hazard-free on both outputs. -/
theorem latch_closed_data_free :
    sweep bd_latch_u_L38 .O5 (fun a b => !a.getD 3 true && !b.getD 3 true &&
      a.getD 0 false == b.getD 0 false && a.getD 2 false == b.getD 2 false) ∧
    sweep bd_latch_u_L38 .O6 (fun a b => !a.getD 3 true && !b.getD 3 true &&
      a.getD 0 false == b.getD 0 false && a.getD 2 false == b.getD 2 false) := by
  decide +kernel

/-- Bit isolation: any change confined to the OTHER bit's pins is static
hazard-free on this bit's output. -/
theorem latch_bit_isolation :
    sweep bd_latch_u_L38 .O5 (fun a b => a.getD 2 false == b.getD 2 false &&
      a.getD 3 false == b.getD 3 false && a.getD 4 false == b.getD 4 false) ∧
    sweep bd_latch_u_L38 .O6 (fun a b => a.getD 0 false == b.getD 0 false &&
      a.getD 1 false == b.getD 1 false && a.getD 3 false == b.getD 3 false) := by
  decide +kernel

/-- Closing while D moves (hold violation: the bundling rule / DACK, rule H)
is a static hazard: the LUT may store either value or a runt. -/
theorem latch_close_while_d_moves (v : Bool) :
    classify bd_latch_u_L38 .O5 [false, false, v, true, v] [false, false, v, false, !v] = .sHZ := by
  cases v <;> decide

/-- Closing while the feedback is still settling (setup: Q has not yet
followed D, rule L) is a static hazard. -/
theorem latch_close_while_q_settles (v : Bool) :
    classify bd_latch_u_L38 .O5 [false, false, !v, true, v] [false, false, v, false, v] = .sHZ := by
  cases v <;> decide

/-! ### bd_arbiter: `ustate` free pins `[A0, rst, q, r2, r1]` (O6 = q,
O5 = R0); `ugrant` free pins `[q, r2, r1]` (O5 = g1 = r1·q, O6 = g2 = r2·¬q). -/

/-- **FINDING. A same-sense tie from idle is a static function hazard on q,
for either held value of q.** Both requests rising together with `A0 = 0`
pass through `r1·¬r2` (set) or `¬r1·r2` (reset) depending on which edge
arrives first at the active muxes. The header's "a plain tie … is resolved
deterministically" holds only for exactly simultaneous arrival. -/
theorem arb_tie_from_idle_hazard (q : Bool) :
    classify bd_arbiter_ustate .O6 [false, false, q, false, false] [false, false, q, true, true] = .sHZ ∧
    classify bd_c2n_set_u .O [false, q, false, false] [false, q, true, true] = .sHZ := by
  cases q <;> decide

/-- The hold: while `A0 = 1`, any change of r1, r2 (q settled, rst = 0) is
static hazard-free on q. -/
theorem arb_frozen_while_A0 :
    sweep bd_arbiter_ustate .O6 (fun a b =>
      a.getD 0 false && b.getD 0 false && !a.getD 1 true && !b.getD 1 true &&
      a.getD 2 false == b.getD 2 false &&
      outB bd_arbiter_ustate .O6 a == a.getD 2 false) := by
  decide +kernel

/-- A competing request arriving while the server's A0 rises (q settled on
the winner) is hazard-free. -/
theorem arb_A0_rise_with_competitor :
    classify bd_arbiter_ustate .O6 [false, false, true, false, true] [true, false, true, true, true] = .sHF ∧
    classify bd_arbiter_ustate .O6 [false, false, false, true, false] [true, false, false, true, true] = .sHF := by
  decide

/-- The race the header acknowledges: A0 falling while the loser is waiting
and the winner re-requests (`r1↑`) is a static hazard on q. -/
theorem arb_A0_fall_with_rerequest :
    classify bd_arbiter_ustate .O6 [true, false, true, true, false] [false, false, true, true, true] = .sHZ := by
  decide

/-- **FINDING (digital, not metastable).** On the grant LUT, `q↑` (r1 won)
concurrent with `r2↑` is a static-0 hazard on g2 = r2·¬q: if r2 reaches
`ugrant` before the new q does, g2 pulses although q itself resolved
cleanly. The window is the skew between the two branches of the q net
(`ustate.I2` feedback vs `ugrant.I2`) plus the r2 skew. `ua2 = C(g2, A0)`
absorbs the pulse while A0 = 0 (`arb_runt_absorbed`); a direct reader of
the `g2` port (bdc/emit.py's `won = g2 | ack` → `index`) does see it. -/
theorem arb_grant_near_tie_runt :
    classify bd_arbiter_ugrant .O6 [false, false, true] [true, true, true] = .sHZ ∧
    classify bd_arbiter_ugrant .O5 [false, true, false] [true, true, true] = .dHF := by
  decide

/-- ... and `ua2` holds 0 through it: g2 = X with A0 = 0, A2 = 0 gives 0
(`bd_c2` pins `[rst, q, b, a]`, a = g2, b = A0). -/
theorem arb_runt_absorbed :
    outK bd_c2_u .O [.zero, .zero, .zero, .X] = .zero := by decide

end Formal.Core.LutAudit
