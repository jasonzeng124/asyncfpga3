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

## Premises of `target_ack_holds` (each a local value fact the network argument must supply)
* `b` (node 120808) low on `[a, e]` (with `e` = the instant before `b` rises: the cause);
* the reset (node 186905) low from `a` on (Env);
* SLICE_X37Y43.A6 (node 140520, the OR's other input) low on `[a, E]` (the "static" premise);
* SLICE_X36Y45.A (node 135829) low on its feedback window before the hold starts (C-element state);
* `a` at least every row's collapse start.

## Not shown
The premises themselves (order-level facts); the assembly with `SpecFbChain.cfb_switch` into "b switches cleanly"
(the pieces fit: the acknowledge read stays unchanged for b's loop upper delay); the other race rows.
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
  have G : ∀ r ∈ rows, CGateOK p c r.g r.src r.arcs (r.S p) x := fun r hr =>
    hcol (r.q, r.pins) (List.mem_map.mpr ⟨r, hr, rfl⟩)
  have m1 : k1 ∈ rows := by simp [rows]
  have m2 : k2 ∈ rows := by simp [rows]
  have m3 : k3 ∈ rows := by simp [rows]
  have m4 : k4 ∈ rows := by simp [rows]
  have m5 : k5 ∈ rows := by simp [rows]
  refine ⟨c, hc0, hc1, fun a e E ar hS hcause hrst hrstw hstat hlo4 hpre t t1 t2 t3 t4 => ?_⟩
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

end Formal.Cells.RaceCertPS
