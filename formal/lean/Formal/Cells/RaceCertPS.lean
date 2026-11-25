import Formal.Cells.ArbViewPS
import Formal.Cells.SpecLatchFact
import Formal.Cells.CtlChain

/-!
# Formal.Cells.RaceCertPS — the binding race's acknowledge cannot return early, on THE target's own gates

Shard B, 2026-11-07. A hold certificate (`CtlChain`) instantiated on `DecodedPS.net` through the checked view
(`ViewPS.view_collapse`).

## Problem, plainly
B's binding race row (RaceTablePS, node `ulink_n_falseResult_85` stage 0 = SLICE_X32Y45.A, safe for κ ≤ 0.415 at
g = 1) says: after this C-element `b` rises, its acknowledge must not be read changed before `b`'s own feedback loop
has gone round. C's counterexample candidate at κ = 0.48 breaks exactly that. The row's acknowledge delay came from
simulated runs. Here the lower bound is a theorem: in EVERY behaviour of THE circuit, at its corner, the acknowledge
source (SLICE_X37Y43.B, an OR LUT) stays low until `b`'s rise has propagated through five routed LUT steps
(SLICE_X36Y46.B, .C, .D, the C-element SLICE_X36Y45.A, and the OR), each with its own routed pin's summed lower
window end.

## Proved (standard axioms)
* `KRow`, `kfact` / `kfact_sound` (decidable controlling-set INIT fact, with an optional feedback pin for a memory
  hold), `krowOK` (view check, wiring, ties), `krow_set` / `krow_mem` (row-level holds from `CtlChain`).
* `rows_ok`: THE target's five rows pass `krowOK` (kernel `decide`).
* `target_ack_holds`: the instance (statement below).
* `race_margin`: for g = 1, every κ ∈ [0, 41/100] and every corner c ∈ [0, 1], b's feedback loop upper delay
  (`kb.hi 0`) ≤ the certified acknowledge lower bound (`k1.lo 4 + … + k5.lo 4 + kb.lo 4`, b's own pin-4 chain
  included). `kb_view` / `kb_src` tie b's pin chains to the netlist.
* `target_b_switch`: assembled with `SpecFbChain.cfb_switch`: b, low until `s`, with x read high and the premises,
  is high on the whole of `[s, e']` (clean rise, no runt) whenever the margin holds at the corner;
  `target_b_switch_041`: for g = 1 and κ ≤ 0.41 the margin is discharged (`race_margin`), leaving only the local
  value premises.

## Premises of `target_ack_holds` (each a local value fact the network argument must supply)
* `b` (node 120808) low on `[a, e]` (with `e` = the instant before `b` rises: the cause);
* the reset (node 186905) low from `a` on (Env);
* SLICE_X37Y43.A6 (node 140520, the OR's other input) low on `[a, E]` (the "static" premise);
* SLICE_X36Y45.A (node 135829) low on its feedback window before the hold starts (C-element state);
* `a` at least every row's collapse start.

## Not shown
The premises themselves (order-level facts: b low before its rise, x high, the reset low, SLICE_X37Y43.A6 low,
SLICE_X36Y45.A6 low on its feedback window, and the timing order a ≪ s); the other race rows; b's fall.
-/

namespace Formal.Cells.RaceCertPS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecChain Formal.Cells.RaceLinkPS Formal.Net.CViewPS Formal.Cells.ViewPS Formal.Cells.SpecFbChain
  Formal.Cells.SpecCElemFact Formal.Cells.SpecLatchFact Formal.Cells.ArbViewPS Formal.Cells.CtlChain

/-- One certificate row: node `q`, its pins, the controlling pin set `P` with values `bv`, the held value `w`, the
feedback pin `fb` (used iff `mem`), and the tied pins. -/
structure KRow where
  q : Nat
  pins : Pins
  P : List Nat
  bv : List Bool
  w : Bool
  fb : Nat
  mem : Bool
  held : List Bool
  ov : List Bool

def KRow.g (r : KRow) : Gate := gateAt r.q
def KRow.src (r : KRow) (i : Nat) : Nat := ((pcsOf r.pins).getD i ⟨0, []⟩).src
def KRow.arcs (r : KRow) : Nat → List Arc := pinArcs r.g (pcsOf r.pins)
def KRow.S (p : DelayPar) (r : KRow) : Nat := cStart p r.g (pcsOf r.pins)
def KRow.lo (p : DelayPar) (c : ℚ) (r : KRow) (i : Nat) : Nat :=
  ((r.arcs i).map (Formal.Cells.Ua1Static.lo p.g p.κ c)).sum.toNat
def KRow.hi (p : DelayPar) (c : ℚ) (r : KRow) (i : Nat) : Nat :=
  ((r.arcs i).map (Formal.Cells.Ua1Static.hi p.g p.κ c)).sum.toNat

/-- The controlling-set fact at every INIT address. -/
def kfact (k init : Nat) (P : List Nat) (bv : Nat → Bool) (w : Bool) (mem : Bool) (fb : Nat) (held ov : Nat → Bool) :
    Bool :=
  (List.range (2 ^ k)).all fun a =>
    !(heldAt k held ov a && (P.all fun j => a.testBit j == bv j) && (!mem || a.testBit fb == w)) ||
      (init.testBit a == w)

theorem kfact_sound {k init : Nat} {P : List Nat} {bv : Nat → Bool} {w mem : Bool} {fb : Nat} {held ov : Nat → Bool}
    (h : kfact k init P bv w mem fb held ov = true) (hP : ∀ j ∈ P, j < k) (hfb : mem = true → fb < k) :
    ∀ v : Nat → Bool, (∀ i, i < k → held i = true → v i = ov i) → (∀ j ∈ P, v j = bv j) →
      (mem = true → v fb = w) → init.testBit (addr k v) = w := by
  intro v hh hv hm
  simp only [kfact, List.all_eq_true, List.mem_range] at h
  have := h _ (Formal.Timing.SpecLoop.addr_lt k v)
  have hPa : (P.all fun j => (addr k v).testBit j == bv j) = true := by
    simp only [List.all_eq_true]
    intro j hj
    rw [Formal.Timing.SpecLoop.addr_testBit k v j (hP j hj), hv j hj]; simp
  have hma : (!mem || (addr k v).testBit fb == w) = true := by
    cases hmem : mem
    · rfl
    · rw [Formal.Timing.SpecLoop.addr_testBit k v fb (hfb hmem), hm hmem]; simp
  rw [heldAt_of hh, hPa, hma] at this
  simpa using this

def krowOK (r : KRow) : Bool :=
  r.g.k == r.pins.length && viewOK r.q r.pins && (gateAt r.q).out == r.q &&
  (r.P.all fun j => decide (j < r.g.k)) && (!r.mem || (decide (r.fb < r.g.k) && (r.pins.getD r.fb ([], 0)).2 == r.q)) &&
  kfact r.g.k r.g.init r.P (fl r.bv) r.w r.mem r.fb (fl r.held) (fl r.ov) &&
  (List.range r.g.k).all fun i => !(fl r.held i) || constAt (r.pins.getD i ([], 0)).2 (fl r.ov i)

theorem ksrc_eq (r : KRow) {i : Nat} (hi : i < r.pins.length) : r.src i = (r.pins.getD i ([], 0)).2 := by
  simp only [KRow.src, pcsOf, List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_eq_getElem hi,
    Option.map_some, Option.getD_some]

/-- The facts a passing row gives, in a behaviour. -/
theorem krow_facts {p : DelayPar} {x : Beh} (hb : Behaves p (circuit net boundary) x) {r : KRow}
    (h : krowOK r = true) :
    (∀ j ∈ r.P, j < r.g.k) ∧ (r.mem = true → r.fb < r.g.k ∧ r.src r.fb = r.g.out) ∧
    (∀ v : Nat → Bool, (∀ i, i < r.g.k → fl r.held i = true → v i = fl r.ov i) → (∀ j ∈ r.P, v j = fl r.bv j) →
      (r.mem = true → v r.fb = r.w) → r.g.init.testBit (addr r.g.k v) = r.w) ∧
    (∀ i, i < r.g.k → fl r.held i = true → ∀ t, x (r.src i) t = fl r.ov i) ∧ r.g.out = r.q ∧ viewOK r.q r.pins = true := by
  simp only [krowOK, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq, List.all_eq_true, List.mem_range] at h
  obtain ⟨⟨⟨⟨⟨⟨hk, hv⟩, hout⟩, hP⟩, hm⟩, hf⟩, hh⟩ := h
  have hP' : ∀ j ∈ r.P, j < r.g.k := fun j hj => by simpa using hP j hj
  have hm' : r.mem = true → r.fb < r.g.k ∧ r.src r.fb = r.g.out := by
    intro hmem
    simp only [hmem, Bool.not_true, Bool.false_or, Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at hm
    refine ⟨hm.1, ?_⟩
    rw [ksrc_eq r (by omega), hm.2]; exact hout.symm
  refine ⟨hP', hm', kfact_sound hf hP' (fun hmem => (hm' hmem).1), fun i hi hheld t => ?_, hout, hv⟩
  have h := hh i hi
  simp only [hheld, Bool.not_true, Bool.false_or, constAt, Bool.and_eq_true, beq_iff_eq, decide_eq_true_eq] at h
  obtain ⟨⟨⟨⟨hs1, hs2⟩, hs3⟩, hs4⟩, hs5⟩ := h
  rw [ksrc_eq r (by omega), const_hold hb hs1 hs2 hs3 hs4 t, hs5]

/-- **A plain (set) row holds.** -/
theorem krow_set {p : DelayPar} {c : ℚ} {x : Beh} (hb : Behaves p (circuit net boundary) x) {r : KRow}
    (h : krowOK r = true) (hmem : r.mem = false) (hg : CGateOK p c r.g r.src r.arcs (r.S p) x)
    (a e : Nat → Nat) (hm : ∀ j ∈ r.P, ∀ t, a j ≤ t → t ≤ e j → x (r.src j) t = fl r.bv j) :
    ∀ t, r.S p ≤ t → (∀ j ∈ r.P, a j + r.hi p c j ≤ t ∧ t ≤ e j + r.lo p c j) → x r.q t = r.w := by
  obtain ⟨hP, -, hf, hh, hout, -⟩ := krow_facts hb h
  intro t hS hw
  have := hold_set hg (cbands_of_sums r.arcs) r.P hP (fl r.bv) r.w (fl r.held) (fl r.ov)
    (fun v h1 h2 => hf v h1 h2 (by simp [hmem])) hh a e hm t hS hw
  rw [hout] at this; exact this

/-- **A memory row holds.** -/
theorem krow_mem {p : DelayPar} {c : ℚ} {x : Beh} (hb : Behaves p (circuit net boundary) x) {r : KRow}
    (h : krowOK r = true) (hmem : r.mem = true) (hg : CGateOK p c r.g r.src r.arcs (r.S p) x)
    (hlo : 1 ≤ r.lo p c r.fb) {s E : Nat} (hS : r.S p ≤ s)
    (hpre : ∀ t, s ≤ t + r.hi p c r.fb → t < s → x r.q t = r.w)
    (hm : ∀ j ∈ r.P, ∀ u, s ≤ u + r.hi p c j → u + r.lo p c j ≤ E → x (r.src j) u = fl r.bv j) :
    ∀ t, s ≤ t → t ≤ E → x r.q t = r.w := by
  obtain ⟨hP, hfb, hf, hh, hout, -⟩ := krow_facts hb h
  obtain ⟨hfbk, hfbs⟩ := hfb hmem
  have := hold_mem hg (cbands_of_sums r.arcs) r.P hP hfbk hfbs hlo (fl r.bv) r.w (fl r.held) (fl r.ov)
    (fun v h1 h2 h3 => hf v h1 h2 (fun _ => h3)) hh hS (by rw [hout]; exact hpre) hm
  rw [hout] at this; exact this

set_option maxRecDepth 100000 in
/-- The certificate (GENERATED by tools-B/ps/gen_cert_ps.py from ctlcert.py's tree): SLICE_X36Y46.B6, .C6, .D6,
SLICE_X36Y45.A6 (memory), SLICE_X37Y43.B6 (the acknowledge OR). -/
def k1 : KRow := ⟨135940, [([135928, 135927], 135924), ([135930, 135929], 135924), ([135932, 135931], 135924), ([135934, 135933], 135924), ([135937, 135936, 135935, 120920, 120675, 120679], 120808), ([135939, 135938], 135924)], [4], [false, false, false, false, false, false], false, 6, false, [true, true, true, true, false, true], [true, true, true, true, false, true]⟩
def k2 : KRow := ⟨135956, [([135943, 135942], 135924), ([135945, 135944], 135924), ([135947, 135946], 135924), ([135949, 135948], 135924), ([135952, 135951, 135950, 135953], 135940), ([135955, 135954], 135924)], [4], [false, false, false, false, false, false], false, 6, false, [true, true, true, true, false, true], [true, true, true, true, false, true]⟩
def k3 : KRow := ⟨135972, [([135959, 135958], 135924), ([135961, 135960], 135924), ([135963, 135962], 135924), ([135966, 135965, 135964, 135967], 135956), ([135969, 135968], 135924), ([135971, 135970], 135924)], [3], [false, false, false, false, false, false], false, 6, false, [true, true, true, false, true, true], [true, true, true, false, true, true]⟩
def k4 : KRow := ⟨135829, [([135807, 135806, 135805, 135804, 135803, 135808], 140504), ([135813, 135812, 135811, 135810, 135809, 96083, 96082, 96081, 8034, 2383, 1181, 1180, 1179, 1185], 186905), ([135816, 135815, 135814], 135817), ([135821, 135820, 135819, 135818, 135822], 135972), ([135824, 135823, 135592, 135597], 135829), ([135828, 135827, 135826, 135825, 135814], 135817)], [1, 3], [false, false, false, false, false, false], false, 4, true, [false, false, true, false, false, true], [false, false, false, false, false, false]⟩
def k5 : KRow := ⟨140537, [([140525, 140524, 140523, 140522, 140526], 140520), ([140528, 140527], 135640), ([140530, 140529], 135640), ([140532, 140531], 135640), ([140534, 140533, 135593, 135592, 135597], 135829), ([140536, 140535], 135640)], [0, 4], [false, false, false, false, false, false], false, 6, false, [false, true, true, true, false, true], [false, true, true, true, false, true]⟩

def rows : List KRow := [k1, k2, k3, k4, k5]

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem rows_ok : rows.all krowOK = true := by decide +kernel

theorem rows_ok' : ∀ r ∈ rows, krowOK r = true := by
  have := rows_ok; simp only [List.all_eq_true] at this; exact this

/-- The acknowledge hold at a given corner, from the collapsed relations of the five rows. -/
theorem ack_holds_at {p : DelayPar} {c : ℚ} {x : Beh} (hb : Behaves p (circuit net boundary) x)
    (G : ∀ r ∈ rows, CGateOK p c r.g r.src r.arcs (r.S p) x) :
    ∀ a e E ar : Nat,
      (∀ r ∈ rows, r.S p ≤ a) →
      (∀ t, a ≤ t → t ≤ e → x 120808 t = false) →
      (∀ t, ar ≤ t → x 186905 t = false) →
      ar + k4.hi p c 1 ≤ a + k1.hi p c 4 + k2.hi p c 4 + k3.hi p c 3 + k4.hi p c 3 →
      (∀ t, a ≤ t → t ≤ E → x 140520 t = false) →
      1 ≤ k4.lo p c 4 →
      (∀ t, a + k1.hi p c 4 + k2.hi p c 4 + k3.hi p c 3 + k4.hi p c 3 ≤ t + k4.hi p c 4 →
        t < a + k1.hi p c 4 + k2.hi p c 4 + k3.hi p c 3 + k4.hi p c 3 → x 135829 t = false) →
      ∀ t, a + k1.hi p c 4 + k2.hi p c 4 + k3.hi p c 3 + k4.hi p c 3 + k5.hi p c 4 ≤ t → a + k5.hi p c 0 ≤ t →
        t ≤ e + k1.lo p c 4 + k2.lo p c 4 + k3.lo p c 3 + k4.lo p c 3 + k5.lo p c 4 → t ≤ E + k5.lo p c 0 →
        x 140537 t = false := by
  have m1 : k1 ∈ rows := by simp [rows]
  have m2 : k2 ∈ rows := by simp [rows]
  have m3 : k3 ∈ rows := by simp [rows]
  have m4 : k4 ∈ rows := by simp [rows]
  have m5 : k5 ∈ rows := by simp [rows]
  intro a e E ar hS hcause hrst hrstw hstat hlo4 hpre t t1 t2 t3 t4
  have S1 := hS k1 m1
  have S2 := hS k2 m2
  have S3 := hS k3 m3
  have S4 := hS k4 m4
  have S5 := hS k5 m5
  -- step 1: k1 (pin 4 reads b)
  have h1 : ∀ t, a + k1.hi p c 4 ≤ t → t ≤ e + k1.lo p c 4 → x 135940 t = false := fun t u1 u2 =>
    krow_set hb (rows_ok' k1 m1) rfl (G k1 m1) (fun _ => a) (fun _ => e)
      (fun j hj u v1 v2 => by
        have : j = 4 := by simpa [k1] using hj
        subst this; exact hcause u v1 v2) t (by omega) (fun j hj => by
          have : j = 4 := by simpa [k1] using hj
          subst this; exact ⟨u1, u2⟩)
  have h2 : ∀ t, a + k1.hi p c 4 + k2.hi p c 4 ≤ t → t ≤ e + k1.lo p c 4 + k2.lo p c 4 → x 135956 t = false :=
    fun t u1 u2 => krow_set hb (rows_ok' k2 m2) rfl (G k2 m2) (fun _ => a + k1.hi p c 4) (fun _ => e + k1.lo p c 4)
      (fun j hj u v1 v2 => by
        have : j = 4 := by simpa [k2] using hj
        subst this; exact h1 u v1 v2) t (by omega) (fun j hj => by
          have : j = 4 := by simpa [k2] using hj
          subst this; exact ⟨by omega, by omega⟩)
  have h3 : ∀ t, a + k1.hi p c 4 + k2.hi p c 4 + k3.hi p c 3 ≤ t →
      t ≤ e + k1.lo p c 4 + k2.lo p c 4 + k3.lo p c 3 → x 135972 t = false :=
    fun t u1 u2 => krow_set hb (rows_ok' k3 m3) rfl (G k3 m3) (fun _ => a + k1.hi p c 4 + k2.hi p c 4)
      (fun _ => e + k1.lo p c 4 + k2.lo p c 4)
      (fun j hj u v1 v2 => by
        have : j = 3 := by simpa [k3] using hj
        subst this; exact h2 u v1 v2) t (by omega) (fun j hj => by
          have : j = 3 := by simpa [k3] using hj
          subst this; exact ⟨by omega, by omega⟩)
  have h4 := krow_mem hb (rows_ok' k4 m4) rfl (G k4 m4) hlo4
    (s := a + k1.hi p c 4 + k2.hi p c 4 + k3.hi p c 3 + k4.hi p c 3)
    (E := e + k1.lo p c 4 + k2.lo p c 4 + k3.lo p c 3 + k4.lo p c 3) (by omega) hpre
    (fun j hj u v1 v2 => by
      have : j = 1 ∨ j = 3 := by simpa [k4] using hj
      rcases this with rfl | rfl
      · exact hrst u (by omega)
      · exact h3 u (by omega) (by omega))
  exact krow_set hb (rows_ok' k5 m5) rfl (G k5 m5)
    (fun j => if j = 0 then a else a + k1.hi p c 4 + k2.hi p c 4 + k3.hi p c 3 + k4.hi p c 3)
    (fun j => if j = 0 then E else e + k1.lo p c 4 + k2.lo p c 4 + k3.lo p c 3 + k4.lo p c 3)
    (fun j hj u v1 v2 => by
      have : j = 0 ∨ j = 4 := by simpa [k5] using hj
      rcases this with rfl | rfl
      · exact hstat u v1 v2
      · exact h4 u v1 v2) t (by omega) (fun j hj => by
        have : j = 0 ∨ j = 4 := by simpa [k5] using hj
        rcases this with rfl | rfl
        · simp only [if_true]; exact ⟨t2, t4⟩
        · simp only [show (4 : Nat) ≠ 0 by decide, if_false]; exact ⟨by omega, by omega⟩)

/-- **The binding race's acknowledge stays low** (THE target, every behaviour, at its corner). With `b` (node 120808,
SLICE_X32Y45.A6) low on `[a, e]` (so `e` = the instant before `b` rises), the reset low from `ar`, SLICE_X37Y43.A6
(node 140520) low on `[a, E]`, SLICE_X36Y45.A6 (node 135829) low on its feedback window before `s4`, and `a` at least
every row's start: the acknowledge source SLICE_X37Y43.B6 (node 140537) is low on the window below, whose right end is
`e` plus the five routed steps' summed LOWER window ends (`k1.lo 4 + k2.lo 4 + k3.lo 3 + k4.lo 3 + k5.lo 4`). -/
theorem target_ack_holds {p : DelayPar} (hp : Formal.Timing.SpecSettle.Sane p) {x : Beh}
    (hb : Behaves p (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ a e E ar : Nat,
      (∀ r ∈ rows, r.S p ≤ a) →
      (∀ t, a ≤ t → t ≤ e → x 120808 t = false) →
      (∀ t, ar ≤ t → x 186905 t = false) →
      ar + k4.hi p c 1 ≤ a + k1.hi p c 4 + k2.hi p c 4 + k3.hi p c 3 + k4.hi p c 3 →
      (∀ t, a ≤ t → t ≤ E → x 140520 t = false) →
      1 ≤ k4.lo p c 4 →
      (∀ t, a + k1.hi p c 4 + k2.hi p c 4 + k3.hi p c 3 + k4.hi p c 3 ≤ t + k4.hi p c 4 →
        t < a + k1.hi p c 4 + k2.hi p c 4 + k3.hi p c 3 + k4.hi p c 3 → x 135829 t = false) →
      ∀ t, a + k1.hi p c 4 + k2.hi p c 4 + k3.hi p c 3 + k4.hi p c 3 + k5.hi p c 4 ≤ t → a + k5.hi p c 0 ≤ t →
        t ≤ e + k1.lo p c 4 + k2.lo p c 4 + k3.lo p c 3 + k4.lo p c 3 + k5.lo p c 4 → t ≤ E + k5.lo p c 0 →
        x 140537 t = false := by
  obtain ⟨c, hc0, hc1, hcol⟩ := view_collapse hp hb (rows.map fun r => (r.q, r.pins)) (by
    simp only [List.all_eq_true, List.mem_map]
    rintro e ⟨r, hr, rfl⟩
    exact (krow_facts hb (rows_ok' r hr)).2.2.2.2.2)
  exact ⟨c, hc0, hc1, ack_holds_at hb fun r hr => hcol (r.q, r.pins) (List.mem_map.mpr ⟨r, hr, rfl⟩)⟩

/-! ## The margin: the switch obligation of b holds for κ ≤ 0.41 (g = 1), at every corner -/

/-- b's own row (its pin chains, from the same generator); only its arcs are used, and `kb_view` ties them to the
netlist. -/
def kb : KRow := ⟨120808, [([120783, 120782, 120730, 120729, 120675, 120679], 120808), ([120787, 120786, 120785, 120784, 48331, 5001, 2383, 1181, 1180, 1179, 1185], 186905), ([120790, 120789, 120788], 120791), ([120797, 120796, 120795, 120794, 120793, 120792, 120798], 136002), ([120803, 120802, 120801, 120800, 120799, 120804], 140537), ([120807, 120806, 120805], 120791)], [1, 4], [false, false, false, false, false, false], false, 0, true, [false, false, true, false, false, true], [false, false, false, false, false, false]⟩

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
/-- b's pin chains are the netlist's (view check; its pin 0 is its own feedback, its pin 4 reads the acknowledge
140537, as `kb_src` states). -/
theorem kb_view : viewOK kb.q kb.pins = true := by decide +kernel

theorem kb_src : kb.src 0 = 120808 ∧ kb.src 4 = 140537 := by decide

open Formal.Cells.Ua1Static in
theorem sum_lo_ge {g κ c : ℚ} : ∀ l : List Arc,
    (((l.map (lo g κ c)).sum : ℤ) : ℚ) ≥ (l.map fun e => (1 - κ) * lerp e.fmin e.smin c / g).sum
  | [] => by simp
  | e :: l => by
    have := sum_lo_ge (g := g) (κ := κ) (c := c) l
    have h : (1 - κ) * lerp e.fmin e.smin c / g ≤ ((lo g κ c e : ℤ) : ℚ) := by unfold lo; exact Rat.le_ceil
    simp only [List.map_cons, List.sum_cons, Int.cast_add]
    linarith

open Formal.Cells.Ua1Static in
theorem sum_hi_le {g κ c : ℚ} : ∀ l : List Arc,
    (((l.map (hi g κ c)).sum : ℤ) : ℚ) ≤ (l.map fun e => (1 + κ) * lerp e.fmax e.smax c * g).sum
  | [] => by simp
  | e :: l => by
    have := sum_hi_le (g := g) (κ := κ) (c := c) l
    have h : ((hi g κ c e : ℤ) : ℚ) ≤ (1 + κ) * lerp e.fmax e.smax c * g := by unfold hi; exact Rat.floor_le _
    simp only [List.map_cons, List.sum_cons, Int.cast_add]
    linarith

theorem toNat_ge (s : ℤ) : ((s.toNat : ℕ) : ℚ) ≥ (s : ℚ) := by
  have := Int.self_le_toNat s
  exact_mod_cast this

theorem toNat_le {s : ℤ} {r : ℚ} (h : (s : ℚ) ≤ r) (hr : 0 ≤ r) : ((s.toNat : ℕ) : ℚ) ≤ r := by
  rcases le_or_gt 0 s with hs | hs
  · have : ((s.toNat : ℕ) : ℤ) = s := Int.toNat_of_nonneg hs
    have : ((s.toNat : ℕ) : ℚ) = (s : ℚ) := by exact_mod_cast this
    linarith
  · have : s.toNat = 0 := Int.toNat_eq_zero.mpr hs.le
    simp [this, hr]

set_option maxRecDepth 100000 in
theorem a1 : k1.arcs 4 = [⟨79, 99, 193, 240⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨50, 71, 115, 149⟩, ⟨33, 83, 111, 176⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩] := by decide +kernel
set_option maxRecDepth 100000 in
theorem a2 : k2.arcs 4 = [⟨78, 98, 192, 238⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩] := by decide +kernel
set_option maxRecDepth 100000 in
theorem a3 : k3.arcs 3 = [⟨133, 165, 329, 408⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩] := by decide +kernel
set_option maxRecDepth 100000 in
theorem a4 : k4.arcs 3 = [⟨131, 163, 329, 408⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨44, 63, 108, 140⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩] := by decide +kernel
set_option maxRecDepth 100000 in
theorem a5 : k5.arcs 4 = [⟨79, 99, 193, 240⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨50, 135, 111, 209⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩] := by decide +kernel
set_option maxRecDepth 100000 in
theorem ab4 : kb.arcs 4 = [⟨83, 104, 202, 250⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨33, 51, 113, 147⟩, ⟨52, 74, 118, 153⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩] := by decide +kernel
set_option maxRecDepth 100000 in
theorem ab0 : kb.arcs 0 = [⟨225, 281, 528, 655⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨35, 62, 102, 142⟩, ⟨33, 51, 113, 147⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩] := by decide +kernel

/-- **The binding race's margin.** For g = 1, every κ ∈ [0, 41/100] and every corner c ∈ [0, 1]: b's feedback loop
upper delay (pin 0, `kb.hi 0`) is at most the certified acknowledge lower bound (the five rows' `lo` plus b's own
pin-4 chain `kb.lo 4`). So with `target_ack_holds`, after b rises its acknowledge is read unchanged for at least b's
loop upper delay: the switch obligation of `SpecFbChain.cfb_switch` for this node (B's binding RaceTablePS row) is
met in every behaviour satisfying the premises, up to κ = 0.41 (g = 1). (Real-valued: it fails above
κ = 632/1514 ≈ 0.417 at c = 0; C's adversary breaks the node at 0.44.) -/
theorem race_margin (κ c : ℚ) (hk0 : 0 ≤ κ) (hk : κ ≤ 41 / 100) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    kb.hi ⟨1, κ⟩ c 0 ≤ k1.lo ⟨1, κ⟩ c 4 + k2.lo ⟨1, κ⟩ c 4 + k3.lo ⟨1, κ⟩ c 3 + k4.lo ⟨1, κ⟩ c 3 +
      k5.lo ⟨1, κ⟩ c 4 + kb.lo ⟨1, κ⟩ c 4 := by
  simp only [KRow.lo, KRow.hi, a1, a2, a3, a4, a5, ab4, ab0]
  have L1 := toNat_ge _ |>.trans' (sum_lo_ge (g := 1) (κ := κ) (c := c) [⟨79, 99, 193, 240⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨50, 71, 115, 149⟩, ⟨33, 83, 111, 176⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩])
  have L2 := toNat_ge _ |>.trans' (sum_lo_ge (g := 1) (κ := κ) (c := c) [⟨78, 98, 192, 238⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩])
  have L3 := toNat_ge _ |>.trans' (sum_lo_ge (g := 1) (κ := κ) (c := c) [⟨133, 165, 329, 408⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩])
  have L4 := toNat_ge _ |>.trans' (sum_lo_ge (g := 1) (κ := κ) (c := c) [⟨131, 163, 329, 408⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨44, 63, 108, 140⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩])
  have L5 := toNat_ge _ |>.trans' (sum_lo_ge (g := 1) (κ := κ) (c := c) [⟨79, 99, 193, 240⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨50, 135, 111, 209⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩])
  have L6 := toNat_ge _ |>.trans' (sum_lo_ge (g := 1) (κ := κ) (c := c) [⟨83, 104, 202, 250⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨33, 51, 113, 147⟩, ⟨52, 74, 118, 153⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩])
  have H := sum_hi_le (g := 1) (κ := κ) (c := c) [⟨225, 281, 528, 655⟩, ⟨0, 0, 0, 0⟩, ⟨38, 47, 114, 138⟩, ⟨35, 62, 102, 142⟩, ⟨33, 51, 113, 147⟩, ⟨0, 0, 0, 0⟩, ⟨0, 0, 0, 0⟩]
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, lerp, Nat.cast_ofNat, Nat.cast_zero,
    div_one, mul_one] at L1 L2 L3 L4 L5 L6 H
  have Hn := toNat_le H (by
    have : (0 : ℚ) ≤ 1 + κ := by linarith
    have : (0 : ℚ) ≤ 1 - c := by linarith
    positivity)
  simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil]
  rw [← Nat.cast_le (α := ℚ)]
  push_cast
  have hkc : κ * c ≤ 41 / 100 * c := by nlinarith
  nlinarith [L1, L2, L3, L4, L5, L6, Hn, hkc]

/-! ## b switches cleanly (assembly with `cfb_switch`) -/

/-- b's force fact (reset low, x = pin 3 high, acknowledge = pin 4 low, ties: output 1 whatever the feedback) and its
confirm fact (reset low, x high, feedback high: output 1 whatever the acknowledge), as rows on b's pins. -/
def kbF : KRow := { kb with P := [1, 3, 4], bv := [false, false, false, true, false, false], w := true, fb := 6, mem := false }
def kbC : KRow := { kb with P := [1, 3], bv := [false, false, false, true, false, false], w := true, fb := 0, mem := true }

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem kbF_ok : krowOK kbF = true := by decide +kernel

set_option maxHeartbeats 0 in
set_option maxRecDepth 100000 in
theorem kbC_ok : krowOK kbC = true := by decide +kernel

theorem kbF_lo (p : DelayPar) (c : ℚ) : kbF.lo p c = kb.lo p c := rfl
theorem kbF_hi (p : DelayPar) (c : ℚ) : kbF.hi p c = kb.hi p c := rfl
theorem kbC_lo (p : DelayPar) (c : ℚ) : kbC.lo p c = kb.lo p c := rfl
theorem kbC_hi (p : DelayPar) (c : ℚ) : kbC.hi p c = kb.hi p c := rfl

/-- A row's INIT fact from what the reads can see (`CVisible`, pin `j` excluded and neither in `P` nor tied). -/
theorem visible_fact {p : DelayPar} {c : ℚ} {x : Beh} (hb : Behaves p (circuit net boundary) x) {r : KRow}
    (h : krowOK r = true) (j : Nat) (hjP : j ∉ r.P) (hjh : fl r.held j = false) (t : Nat)
    (hm : ∀ i ∈ r.P, ∀ u, u + r.lo p c i ≤ t → t ≤ u + r.hi p c i → x (r.src i) u = fl r.bv i)
    (v : Nat → Bool) (hv : CVisible x r.g.k r.src (r.lo p c) (r.hi p c) j t v) (hmem : r.mem = true → v r.fb = r.w) :
    r.g.init.testBit (addr r.g.k v) = r.w := by
  obtain ⟨hP, -, hf, hh, -, -⟩ := krow_facts hb h
  refine hf v (fun i hi hheld => ?_) (fun i hiP => ?_) hmem
  · have hij : i ≠ j := by rintro rfl; rw [hjh] at hheld; exact absurd hheld (by decide)
    obtain ⟨u, -, -, hvu⟩ := hv i hi hij
    rw [hvu, hh i hi hheld u]
  · have hij : i ≠ j := by rintro rfl; exact hjP hiP
    obtain ⟨u, h1, h2, hvu⟩ := hv i (hP i hiP) hij
    rw [hvu]; exact hm i hiP u h1 h2

set_option maxRecDepth 100000 in
/-- **The binding node switches cleanly** (every behaviour of THE circuit, at its corner). b = SLICE_X32Y45.A6
(node 120808) is low until `s`; from `s` its input x (node 136002) reads high (until `e'`), the reset is low, and the
acknowledge certificate's premises hold (as in `ack_holds_at`, with the cause ending at `s - 1`). If the margin
`kb.hi 0 ≤ Σ lo + kb.lo 4` holds at the corner (`race_margin`: always, for g = 1 and κ ≤ 0.41), b is high on the
whole of `[s, e']`: it rises and stays, with no runt, because its acknowledge cannot be read changed before its own
feedback loop has confirmed the new value. -/
theorem target_b_switch {p : DelayPar} (hp : Formal.Timing.SpecSettle.Sane p) {x : Beh}
    (hb : Behaves p (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ a E ar s e' : Nat,
      (∀ r ∈ rows, r.S p ≤ a) → kb.S p ≤ s → 1 ≤ s →
      (∀ t, a ≤ t → t ≤ s - 1 → x 120808 t = false) →
      (∀ t, ar ≤ t → x 186905 t = false) →
      ar + k4.hi p c 1 ≤ a + k1.hi p c 4 + k2.hi p c 4 + k3.hi p c 3 + k4.hi p c 3 →
      ar + kb.hi p c 1 ≤ s →
      (∀ t, a ≤ t → t ≤ E → x 140520 t = false) →
      1 ≤ k4.lo p c 4 →
      (∀ t, a + k1.hi p c 4 + k2.hi p c 4 + k3.hi p c 3 + k4.hi p c 3 ≤ t + k4.hi p c 4 →
        t < a + k1.hi p c 4 + k2.hi p c 4 + k3.hi p c 3 + k4.hi p c 3 → x 135829 t = false) →
      a + k1.hi p c 4 + k2.hi p c 4 + k3.hi p c 3 + k4.hi p c 3 + k5.hi p c 4 + kb.hi p c 4 ≤ s →
      a + k5.hi p c 0 + kb.hi p c 4 ≤ s →
      s + kb.hi p c 0 ≤ E + k5.lo p c 0 + kb.lo p c 4 + 1 →
      kb.hi p c 0 ≤ k1.lo p c 4 + k2.lo p c 4 + k3.lo p c 3 + k4.lo p c 3 + k5.lo p c 4 + kb.lo p c 4 →
      1 ≤ kb.lo p c 0 → s + kb.hi p c 0 ≤ e' + 1 →
      (∀ u, s ≤ u + kb.hi p c 3 → u + kb.lo p c 3 ≤ e' → x 136002 u = true) →
      ∀ t, s ≤ t → t ≤ e' → x 120808 t = true := by
  obtain ⟨c, hc0, hc1, hcol⟩ := view_collapse hp hb ((rows.map fun r => (r.q, r.pins)) ++ [(kb.q, kb.pins)]) (by
    simp only [List.all_append, List.all_eq_true, List.mem_map, Bool.and_eq_true]
    refine ⟨?_, by simpa using kb_view⟩
    rintro e ⟨r, hr, rfl⟩
    exact (krow_facts hb (rows_ok' r hr)).2.2.2.2.2)
  have G : ∀ r ∈ rows, CGateOK p c r.g r.src r.arcs (r.S p) x := fun r hr =>
    hcol (r.q, r.pins) (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨r, hr, rfl⟩)))
  have Gb : CGateOK p c kb.g kb.src kb.arcs (kb.S p) x := hcol (kb.q, kb.pins) (by simp)
  refine ⟨c, hc0, hc1, fun a E ar s e' hS hSb hs1 hcause hrst hrstw hrstb hstat hlo4 hpre w1 w2 w3 hmarg hlo0 he' hx => ?_⟩
  have ack := ack_holds_at hb G a (s - 1) E ar hS hcause hrst hrstw hstat hlo4 hpre
  obtain ⟨-, hfbC, -, -, houtC, -⟩ := krow_facts hb kbC_ok
  have hfb : kb.src 0 = kb.g.out := (hfbC rfl).2
  have hsrc : kb.src 1 = 186905 ∧ kb.src 3 = 136002 ∧ kb.src 4 = 140537 := by decide
  obtain ⟨s1, s3, s4⟩ := hsrc
  have hbd : CBands p c kb.g.k kb.arcs (kb.lo p c) (kb.hi p c) := cbands_of_sums kb.arcs
  have key := cfb_switch Gb hbd (j := 0) (by decide) hfb hlo0 (s := s) (e := s + kb.hi p c 0 - 1)
    (e' := e') hSb (by omega) (cv := true)
    (fun t t1 t2 v hv => visible_fact hb kbF_ok 0 (by decide) (by decide) t (fun i hi u u1 u2 => by
        have : i = 1 ∨ i = 3 ∨ i = 4 := by simpa [kbF] using hi
        rcases this with rfl | rfl | rfl
        · show x (kb.src 1) u = false
          rw [s1]; exact hrst u (by rw [kbF_hi] at u2; omega)
        · show x (kb.src 3) u = true
          rw [s3]; exact hx u (by rw [kbF_hi] at u2; omega) (by rw [kbF_lo] at u1; omega)
        · show x (kb.src 4) u = false
          rw [s4]; rw [kbF_lo] at u1; rw [kbF_hi] at u2
          exact ack u (by omega) (by omega) (by omega) (by omega)) v hv (by simp [kbF]))
    (fun t t1 t2 v hv0 hv => visible_fact hb kbC_ok 0 (by decide) (by decide) t (fun i hi u u1 u2 => by
        have : i = 1 ∨ i = 3 := by simpa [kbC] using hi
        rcases this with rfl | rfl
        · show x (kb.src 1) u = false
          rw [s1]; exact hrst u (by rw [kbC_hi] at u2; omega)
        · show x (kb.src 3) u = true
          rw [s3]; exact hx u (by rw [kbC_hi] at u2; omega) (by rw [kbC_lo] at u1; omega)) v hv
        (fun _ => by simpa [kbC] using hv0))
  intro t t1 t2
  have := key t t1 t2
  have hq : kb.g.out = 120808 := houtC
  rwa [hq] at this

/-- **At g = 1 and κ ≤ 0.41 the margin premise is a theorem** (`race_margin` at every corner), so the binding node
switches cleanly under the remaining local premises alone. -/
theorem target_b_switch_041 (κ : ℚ) (hk0 : 0 ≤ κ) (hk : κ ≤ 41 / 100) {x : Beh}
    (hb : Behaves ⟨1, κ⟩ (circuit net boundary) x) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧
      kb.hi ⟨1, κ⟩ c 0 ≤ k1.lo ⟨1, κ⟩ c 4 + k2.lo ⟨1, κ⟩ c 4 + k3.lo ⟨1, κ⟩ c 3 + k4.lo ⟨1, κ⟩ c 3 +
        k5.lo ⟨1, κ⟩ c 4 + kb.lo ⟨1, κ⟩ c 4 ∧ ∀ a E ar s e' : Nat,
      (∀ r ∈ rows, r.S ⟨1, κ⟩ ≤ a) → kb.S ⟨1, κ⟩ ≤ s → 1 ≤ s →
      (∀ t, a ≤ t → t ≤ s - 1 → x 120808 t = false) →
      (∀ t, ar ≤ t → x 186905 t = false) →
      ar + k4.hi ⟨1, κ⟩ c 1 ≤ a + k1.hi ⟨1, κ⟩ c 4 + k2.hi ⟨1, κ⟩ c 4 + k3.hi ⟨1, κ⟩ c 3 + k4.hi ⟨1, κ⟩ c 3 →
      ar + kb.hi ⟨1, κ⟩ c 1 ≤ s →
      (∀ t, a ≤ t → t ≤ E → x 140520 t = false) →
      1 ≤ k4.lo ⟨1, κ⟩ c 4 →
      (∀ t, a + k1.hi ⟨1, κ⟩ c 4 + k2.hi ⟨1, κ⟩ c 4 + k3.hi ⟨1, κ⟩ c 3 + k4.hi ⟨1, κ⟩ c 3 ≤ t + k4.hi ⟨1, κ⟩ c 4 →
        t < a + k1.hi ⟨1, κ⟩ c 4 + k2.hi ⟨1, κ⟩ c 4 + k3.hi ⟨1, κ⟩ c 3 + k4.hi ⟨1, κ⟩ c 3 → x 135829 t = false) →
      a + k1.hi ⟨1, κ⟩ c 4 + k2.hi ⟨1, κ⟩ c 4 + k3.hi ⟨1, κ⟩ c 3 + k4.hi ⟨1, κ⟩ c 3 + k5.hi ⟨1, κ⟩ c 4 +
        kb.hi ⟨1, κ⟩ c 4 ≤ s →
      a + k5.hi ⟨1, κ⟩ c 0 + kb.hi ⟨1, κ⟩ c 4 ≤ s →
      s + kb.hi ⟨1, κ⟩ c 0 ≤ E + k5.lo ⟨1, κ⟩ c 0 + kb.lo ⟨1, κ⟩ c 4 + 1 →
      1 ≤ kb.lo ⟨1, κ⟩ c 0 → s + kb.hi ⟨1, κ⟩ c 0 ≤ e' + 1 →
      (∀ u, s ≤ u + kb.hi ⟨1, κ⟩ c 3 → u + kb.lo ⟨1, κ⟩ c 3 ≤ e' → x 136002 u = true) →
      ∀ t, s ≤ t → t ≤ e' → x 120808 t = true := by
  have hp : Formal.Timing.SpecSettle.Sane ⟨1, κ⟩ := ⟨hk0, by linarith, by norm_num⟩
  obtain ⟨c, hc0, hc1, h⟩ := target_b_switch hp hb
  have hm := race_margin κ c hk0 hk hc0 hc1
  exact ⟨c, hc0, hc1, hm, fun a E ar s e' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 h14 h15 h16 =>
    h a E ar s e' h1 h2 h3 h4 h5 h6 h7 h8 h9 h10 h11 h12 h13 hm h14 h15 h16⟩

end Formal.Cells.RaceCertPS
