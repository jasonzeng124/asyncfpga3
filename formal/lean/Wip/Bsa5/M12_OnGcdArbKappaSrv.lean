-- Bsa5 mutant M12 of Formal/Cells/OnGcdArbKappaSrv.lean: one change, kS2 numerator +1 (= kU2, claimed unsafe). Expected: FAIL.
import Formal.Cells.OnGcdArbKappaTightA

/-!
# Probe Bsrv: the gate-level κ threshold of gcd_hw's arbiters with the server credited

Shard B, 2026-10-29. Needs Mathlib (through `OnGcdArbKappa` → `CornerNat`).
Note: `formal/notes/B-gcd-arb-kappa-srv.md`.

`OnGcdArbKappa` decided all 1296 rows (36 routed gcd_hw arbiters × 2 readings × 18 forms) to
within `n/(R+D)` of the real-relaxation threshold κ\*; `OnGcdArbKappaTight` closed the binding
row (seed 3 merge12.uarb1, RT1b SERVER-FREE) exactly and found that its gate-level counter-run
needs a zero-latency server, a zero A0 route to ustate and a zero ustate O6 arc. This file
credits the server and every arc as corner-model delays: the server-free RT1/RT1b forms are
replaced by RT1s/RT1bs (A0 branch, ustate O6, q prefix and the graph server path `srv` all
realised by the same corner-model realization), and decides the design.

## Two design readings (both `lit`, A's model: one shared corner, each arc within `1 ± κ`)

* **D1 = `formsSrv`**: OnGcdArbKappa's 18 forms minus `rt1`/`rt1b` (16 forms: forks, RT2/RT2b,
  RT1s/RT1bs and ArbPin2's bare-cell rows h12/h21/o1x/o2x). Binding row: **seed 2
  merge3.uarb1, h21** (r2 → r1 handover of the BARE cell, ArbPin2, H_A0_LOW). Exact:
  safe for `κ ≤ κS1 = 80163500491/10¹²`, violated from `κU1 = κS1 + 10⁻¹²`
  (`h21_safe`, `h21_unsafe`); gate level: `h21_gate_unsafe` (a transport behaviour of the
  bare cell on the realization's point box with both grants high, ArbPin2.h21_kfail) and
  `h21_7j_bare` (the same race as a run of 7j's gate relations with EVERY delay, server
  included, a corner-model realization; in that run A0 never rises and client 2 withdraws an
  unacknowledged request, so it is NOT a four-phase run).
* **D2 = `formsHeld`**: the 12 forms whose gate model is the held arbiter in a four-phase
  scenario (7g forks, 7h/7j RT2/RT2b with `srv`, 7h/7j RT1s/RT1bs). Binding row: **seed 4
  merge12.uarb2, fork2** (A0's fall to ua2 against A0 → ustate → q → ugrant → ua2). Exact:
  safe for `κ ≤ κS2 = 216552148868/10¹²`, violated from `κU2 = κS2 + 10⁻¹²`; gate level
  through 7g's exact `fork2_box_iff` (`fork2_gate_unsafe`).
* `g2m3_held_rt1bs`: in 7j's four-phase handover (Scn2, H_SETTLED), seed 2 merge3.uarb1's
  r2 → r1 handover with the server credited is safe up to κ = 0.769 (RT1bs), so D1's binding
  row is a bare-cell row only.
* `cons_srv_neg`: in the `cons` reading, the rows failing at κ = 0 among D1's forms are exactly
  seed 2 merge3.uarb1 h21 and o1x; among D2's forms none.

## Method

The exact thresholds are finite certificates over every rational corner (Tight's point and
open-interval checks; a new head-start variant `chkH` for a row binding at the SLOW end, whose
real relaxation is below one tick on `[0, p₀]`), with constant arcs (`F = S`, e.g. the q
prefix `cq`) moved into the constants (`allOK_split`). Both are decided by `decide +kernel`.

## Assumed / proved / NOT covered

Assumed: A's corner model (H_ENDPOINTS from the UNTRUSTED extraction of probe Bar, copied in
`OnGcdArbKappa`; H_AFFINE; H_SHARED_CORNER; H_SCATTER κ; whole fs; rise = fall); the gate
models' own hypotheses (7g `Run`, 7h/7j `Run`/`Scn`/`Scn2`/`Server`, ArbPin `Cell`), the
record-realisation hypotheses (`Real7`, `Real1`/`Real2`, the A0-branch equations), and
H_SERVER_GRAPH (`d srv ≤ smin`: the server answers no faster than the realised graph path).
Proved: as listed above. NOT covered: whether gcd_hw ever runs the bare-cell race (H_A0_LOW
with a request falling) — in a four-phase run with H_SETTLED it does not; the server's actual
latency (srv is a lower bound from the routed graph, not a measurement); per-edge scatter;
Kleene X; metastability; κ itself.
-/

namespace Formal.Cells.OnGcdArbKappaSrv

open Formal.Cells

/-! ## 1. A head-start certificate (rows binding at the slow end) -/

section generic
open Formal.Cells.OnGcdArbKappaTight
variable {A : Type}

/-- The real relaxation is below one tick at the fast end and at `p` (so on `[0, p]`). -/
def headOK (M : CornerModel A) (P Q : List A) (a b : Nat) (p : Nat × Nat) : Bool :=
  let XF := M.κ.hi * DF M P + M.κ.den * a
  let XS := M.κ.hi * DS M P + M.κ.den * a
  let YF := M.κ.lo * DF M Q + M.κ.den * (b + 1)
  let YS := M.κ.lo * DS M Q + M.κ.den * (b + 1)
  decide (0 < p.1) && decide (p.1 ≤ p.2) &&
    decide ((p.2 - p.1) * XF + p.1 * XS < (p.2 - p.1) * YF + p.1 * YS) && decide (XF < YF)

theorem headOK_sound (M : CornerModel A) (P Q : List A) (a b : Nat) (p : Nat × Nat)
    (h : headOK M P Q a b p = true) (c : Corner) (ht : c.w1 * p.2 ≤ p.1 * c.W) :
    NoViolAt M P Q a b c := by
  unfold headOK at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h0, hle⟩, h1⟩, h2⟩ := h
  have hW : 0 < c.w1 + c.w0 := by have := c.pos; omega
  have e1 : p.2 - (p.2 - p.1) = p.1 := Nat.sub_sub_self hle
  have ht' : (p.2 - p.1) * (c.w1 + c.w0) ≤ c.w0 * p.2 := by
    have ht2 : c.w1 * p.2 ≤ p.1 * c.w0 + p.1 * c.w1 := by
      unfold Corner.W at ht; rw [Nat.mul_add] at ht; exact ht
    rw [Nat.sub_mul, Nat.mul_add, Nat.mul_add, Nat.mul_comm p.2 c.w1, Nat.mul_comm p.2 c.w0]
    omega
  have L := lin_tail (w0 := c.w1) (w1 := c.w0) (tn := p.2 - p.1) (td := p.2)
    (XF := M.κ.hi * DS M P + M.κ.den * a) (XS := M.κ.hi * DF M P + M.κ.den * a)
    (YF := M.κ.lo * DS M Q + M.κ.den * (b + 1)) (YS := M.κ.lo * DF M Q + M.κ.den * (b + 1))
    hW (by omega) (by rw [e1]; omega) h2 ht'
  intro d hd
  have hP : M.κ.den * c.W * pathDelay d P ≤ M.κ.hi * sumOver (fun e => nom c (M.arc e)) P :=
    sum_scale_le _ _ P (fun e _ => (hd e).2)
  have hQ : M.κ.lo * sumOver (fun e => nom c (M.arc e)) Q ≤ M.κ.den * c.W * pathDelay d Q :=
    sum_scale_le _ _ Q (fun e _ => (hd e).1)
  rw [sum_nom] at hP hQ
  unfold DF DS at L
  unfold Corner.W at hP hQ
  apply Nat.le_of_not_lt
  intro hv
  have hv' : pathDelay d Q + b + 1 ≤ pathDelay d P + a := hv
  have m := Nat.mul_le_mul_left (M.κ.den * (c.w0 + c.w1)) hv'
  grind

/-- Points from `p` to the slow end `(m, m)`: point and open-interval checks. -/
def chkF (M : CornerModel A) (P Q : List A) (a b : Nat) : List (Nat × Nat) → Bool
  | [] => false
  | [p] => wfB p && decide (p.1 = p.2) && pointOK M P Q a b p
  | p :: q :: rest => wfB p && wfB q && pointOK M P Q a b p && openOK M P Q a b p q &&
      chkF M P Q a b (q :: rest)

theorem chkF_sound (M : CornerModel A) (P Q : List A) (a b : Nat)
    (hsP : strictB M P = true) (hsQ : strictB M Q = true) (hlo : 0 < M.κ.lo) :
    ∀ (p : Nat × Nat) (rest : List (Nat × Nat)), chkF M P Q a b (p :: rest) = true →
      ∀ c : Corner, p.1 * c.W ≤ c.w1 * p.2 → NoViolAt M P Q a b c
  | p, [], h, c, ht => by
    unfold chkF at h
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    obtain ⟨⟨hw, he⟩, hpt⟩ := h
    have h0 := (wf_of hw).1
    have hw1 : c.w1 ≤ c.W := by unfold Corner.W; omega
    have a1 : c.w1 * p.2 ≤ c.W * p.2 := Nat.mul_le_mul_right _ hw1
    have a2 : c.W * p.2 = p.1 * c.W := by rw [he, Nat.mul_comm]
    exact pointOK_sound M P Q a b p hw hpt c (by omega)
  | p, q :: rest, h, c, ht => by
    unfold chkF at h
    simp only [Bool.and_eq_true] at h
    obtain ⟨⟨⟨⟨hwp, hwq⟩, hpt⟩, hop⟩, hrest⟩ := h
    by_cases hq : q.1 * c.W ≤ c.w1 * q.2
    · exact chkF_sound M P Q a b hsP hsQ hlo q rest hrest c hq
    · have hq' : c.w1 * q.2 < q.1 * c.W := by omega
      by_cases he : p.1 * c.W = c.w1 * p.2
      · exact pointOK_sound M P Q a b p hwp hpt c he.symm
      · exact openOK_sound M P Q a b p q hwp hwq hsP hsQ hlo hop c (by omega) hq'

/-- The head-start certificate: relaxation on `[0, p₀]`, then points `p₀ … (m, m)`. -/
def chkH (M : CornerModel A) (P Q : List A) (a b : Nat) : List (Nat × Nat) → Bool
  | [] => false
  | p :: rest => headOK M P Q a b p && chkF M P Q a b (p :: rest)

/-- **Head-start certificate soundness**, every rational corner, every whole-fs realization. -/
theorem allOK_of_chkH (M : CornerModel A) (P Q : List A) (a b : Nat) (l : List (Nat × Nat))
    (hsP : strictB M P = true) (hsQ : strictB M Q = true) (hlo : 0 < M.κ.lo)
    (h : chkH M P Q a b l = true) : AllOK M P Q a b := by
  intro d ⟨c, hc⟩
  cases l with
  | nil => exact absurd h (by simp [chkH])
  | cons p rest =>
    unfold chkH at h
    simp only [Bool.and_eq_true] at h
    by_cases hp : p.1 * c.W ≤ c.w1 * p.2
    · exact chkF_sound M P Q a b hsP hsQ hlo p rest h.2 c hp d hc
    · exact headOK_sound M P Q a b p h.1 c (by omega) d hc

/-! ## 2. Constant arcs (`F = S`) as constants -/

def constB (M : CornerModel A) (l : List A) : Bool :=
  l.all (fun e => decide ((M.arc e).F = (M.arc e).S))

/-- Upper bound of the constant data arcs, lower bound of the constant request arcs. -/
def ubC (M : CornerModel A) (l : List A) : Nat := sumOver (fun e => M.κ.hi * (M.arc e).F / M.κ.den) l
def lbC (M : CornerModel A) (l : List A) : Nat :=
  sumOver (fun e => (M.κ.lo * (M.arc e).F + (M.κ.den - 1)) / M.κ.den) l

theorem nom_const (c : Corner) (a : CArc) (h : a.F = a.S) : nom c a = c.W * a.F := by
  unfold nom Corner.W; rw [← h, Nat.add_mul]

theorem const_up {k : Kappa} {c : Corner} {a : CArc} {d : Nat} (h : a.F = a.S)
    (hs : Scat k c a d) : d ≤ k.hi * a.F / k.den := by
  have hW : 0 < c.W := c.pos
  have e := hs.2
  rw [nom_const c a h] at e
  have e2 : c.W * (k.den * d) ≤ c.W * (k.hi * a.F) := by
    have : k.den * c.W * d = c.W * (k.den * d) := by
      rw [Nat.mul_comm k.den c.W, Nat.mul_assoc]
    have : k.hi * (c.W * a.F) = c.W * (k.hi * a.F) := Nat.mul_left_comm _ _ _
    omega
  rw [Nat.le_div_iff_mul_le k.den_pos, Nat.mul_comm]
  exact Nat.le_of_mul_le_mul_left e2 hW

theorem const_lo {k : Kappa} {c : Corner} {a : CArc} {d : Nat} (h : a.F = a.S)
    (hs : Scat k c a d) : (k.lo * a.F + (k.den - 1)) / k.den ≤ d := by
  have hW : 0 < c.W := c.pos
  have e := hs.1
  rw [nom_const c a h] at e
  have e2 : c.W * (k.lo * a.F) ≤ c.W * (d * k.den) := by
    have : k.den * c.W * d = c.W * (d * k.den) := by
      rw [Nat.mul_comm k.den c.W, Nat.mul_assoc, Nat.mul_comm k.den d]
    have : k.lo * (c.W * a.F) = c.W * (k.lo * a.F) := Nat.mul_left_comm _ _ _
    omega
  have e3 := Nat.le_of_mul_le_mul_left e2 hW
  have hq := k.den_pos
  have : (k.lo * a.F + (k.den - 1)) / k.den < d + 1 := by
    rw [Nat.div_lt_iff_lt_mul hq, Nat.add_mul]; omega
  omega

theorem constB_mem {M : CornerModel A} {l : List A} (h : constB M l = true) :
    ∀ e ∈ l, (M.arc e).F = (M.arc e).S := by
  intro e he; unfold constB at h; rw [List.all_eq_true] at h; exact of_decide_eq_true (h e he)

theorem pathDelay_append (d : A → Nat) (l₁ l₂ : List A) :
    pathDelay d (l₁ ++ l₂) = pathDelay d l₁ + pathDelay d l₂ := by
  simp [pathDelay, List.map_append, List.sum_append]

/-- **Constants split.** Constant arcs contribute at most `ubC` (data) and at least `lbC`
(request) at every corner. -/
theorem allOK_split (M : CornerModel A) (P Pc Q Qc : List A) (a b : Nat)
    (hP : constB M Pc = true) (hQ : constB M Qc = true)
    (h : AllOK M P Q (a + ubC M Pc) (b + lbC M Qc)) : AllOK M (P ++ Pc) (Q ++ Qc) a b := by
  intro d hd
  have h1 := h d hd
  obtain ⟨c, hc⟩ := hd
  have u : pathDelay d Pc ≤ ubC M Pc :=
    sum_le Pc (fun e he => const_up (constB_mem hP e he) (hc e))
  have l : lbC M Qc ≤ pathDelay d Qc :=
    sum_le Qc (fun e he => const_lo (constB_mem hQ e he) (hc e))
  rw [pathDelay_append, pathDelay_append]
  omega

end generic

/-! ## 3. The bridge to `OnGcdArbKappa`'s objects (A's `CornerNat`) -/

open Formal.Cells.OnGcdArbKappa (E Quad holds)

/-- The `lit` arc of `v`, in Tight's restated model. -/
def tArc (v : E → Quad) (e : E) : OnGcdArbKappaTight.CArc :=
  OnGcdArbKappaTight.mkArc (v e).1 (v e).2.2.2

def TM (k : OnGcdArbKappaTight.Kappa) (v : E → Quad) : OnGcdArbKappaTight.CornerModel E :=
  ⟨tArc v, k⟩

/-- A realization of A's `litModel` is a realization of the restated model (definitional). -/
theorem real_toT {k : Formal.Core.Substrate.Kappa} {v : E → Quad} {d : E → Nat}
    (h : (OnGcdArbKappa.litModel k v).Realizes d) :
    (TM (OnGcdArbKappaTightA.toK k) v).Realizes d := by
  obtain ⟨c, hc⟩ := h
  exact ⟨OnGcdArbKappaTightA.toC c, fun e => (OnGcdArbKappaTightA.scat_iff _ _ _ _).1 (hc e)⟩

theorem real_ofT {k : Formal.Core.Substrate.Kappa} {v : E → Quad} {d : E → Nat}
    {c : Formal.Core.Substrate.Corner}
    (h : (TM (OnGcdArbKappaTightA.toK k) v).RealizesAt (OnGcdArbKappaTightA.toC c) d) :
    (OnGcdArbKappa.litModel k v).RealizesAt c d :=
  fun e => (OnGcdArbKappaTightA.scat_iff _ _ _ _).2 (h e)

/-- κ-monotone transfer of a restated `AllOK` at `kS` to A's `AllOK` at every `κ ≤ kS`. -/
theorem allOK_toA {kS : OnGcdArbKappaTight.Kappa} {v : E → Quad} {P Q : List E} {a b : Nat}
    (h : OnGcdArbKappaTight.AllOK (TM kS v) P Q a b) (k : Formal.Core.Substrate.Kappa)
    (H_KAPPA : k.num * kS.den ≤ kS.num * k.den) :
    ConstraintsKappa.AllOK (OnGcdArbKappa.litModel k v) P Q a b := by
  intro d hd
  obtain ⟨c, hc⟩ := real_toT hd
  exact h d ⟨c, fun e => OnGcdArbKappaTight.scat_mono H_KAPPA (hc e)⟩

theorem holds_of_allOK {k : Formal.Core.Substrate.Kappa} {v : E → Quad} {f : OnGcdArbKappa.Form}
    (h : ConstraintsKappa.AllOK (OnGcdArbKappa.litModel k v) f.P f.Q f.a f.b) {d : E → Nat}
    (hd : (OnGcdArbKappa.litModel k v).Realizes d) : holds d f := h d hd

/-! ## 4. D1's binding row: seed 2 merge3.uarb1, h21 (the bare-cell r2 → r1 handover)

`d(rg2) + d(ag2r) ≤ d(cq) + d(qgw) + d(pqg) + d(rs2) + d(aq) + d(ag1q)` (fs): r2's fall to
ugrant O6 against r2 → ustate → q → ugrant O5 (ArbPin2's `B2 ≤ a2 + c5`). It binds at the SLOW
end (κ\* = 138217/1724217 from OnGcdArbKappa), so its certificate is the head-start one. The q
prefix `cq` is a constant arc (FAST_MIN = SLOW_MAX = 23253 fs). -/

open Formal.Cells.OnGcdArbKappa (v_g2_merge3_uarb1 v_g4_merge12_uarb2 F_h21 F_fork2 litModel)

abbrev AK := Formal.Core.Substrate.Kappa

def P1 : List E := [.rg2, .ag2r]
def Q1 : List E := [.qgw, .pqg, .rs2, .aq, .ag1q]
def Qc1 : List E := [.cq]

/-- `κS1 = 80163500491 / 10¹²` (≈ 0.0801635005). -/
def kS1 : OnGcdArbKappaTight.Kappa := ⟨80163500491, 1000000000000, by decide, by decide⟩

/-- The corner points `(tn, td)` (t = tn/td): the head point `p₀` (the relaxation is below one
tick on `[0, p₀]`), every corner in `(p₀, 1)` where an arc's `⌊(1+κS1)n⌋` / `⌈(1−κS1)n⌉`
steps, and the slow end (generated, scratch `probes/Bsrv/gen.py`; the check is what counts). -/
def pts1 : List (Nat × Nat) := [
  (499935661, 500000000),
  (40467606509329, 40472805978396),
  (487091356892962, 487153738721441),
  (487092356892962, 487153738721441),
  (166469608534861, 166490406411129),
  (487093356892962, 487153738721441),
  (44376620790034081, 44382111101309250),
  (487094356892962, 487153738721441),
  (85322642477905, 85332916538789),
  (24219452507365, 24222361153737),
  (487095356892962, 487153738721441),
  (166470608534861, 166490406411129),
  (44376870790034081, 44382111101309250),
  (487096356892962, 487153738721441),
  (13489368836443, 13490935326132),
  (487097356892962, 487153738721441),
  (65300848023568, 65308391465139),
  (487098356892962, 487153738721441),
  (55490536178287, 55496802137043),
  (14792373596678027, 14794037033769750),
  (44281759717542, 44286703520131),
  (487100356892962, 487153738721441),
  (85323642477905, 85332916538789),
  (487101356892962, 487153738721441),
  (166472608534861, 166490406411129),
  (44377370790034081, 44382111101309250),
  (72659357522095, 72667083461211),
  (487102356892962, 487153738721441),
  (40468606509329, 40472805978396),
  (487103356892962, 487153738721441),
  (487104356892962, 487153738721441),
  (44377620790034081, 44382111101309250),
  (166473608534861, 166490406411129),
  (65301848023568, 65308391465139),
  (487105356892962, 487153738721441),
  (487106356892962, 487153738721441),
  (85324642477905, 85332916538789),
  (4930874532226009, 4931345677923250),
  (487107356892962, 487153738721441),
  (55491536178287, 55496802137043),
  (487108356892962, 487153738721441),
  (72660357522095, 72667083461211),
  (40469106509329, 40472805978396),
  (487109356892962, 487153738721441),
  (44378120790034081, 44382111101309250),
  (44282759717542, 44286703520131),
  (166475608534861, 166490406411129),
  (487111356892962, 487153738721441),
  (85325642477905, 85332916538789),
  (487112356892962, 487153738721441),
  (21767616007856, 21769463821713),
  (44378370790034081, 44382111101309250),
  (487113356892962, 487153738721441),
  (166476608534861, 166490406411129),
  (487114356892962, 487153738721441),
  (4496622945481, 4496978442044),
  (24220452507365, 24222361153737),
  (487115356892962, 487153738721441),
  (14792873596678027, 14794037033769750),
  (18497512059429, 18498934045681),
  (487116356892962, 487153738721441),
  (487117356892962, 487153738721441),
  (85326642477905, 85332916538789),
  (44378870790034081, 44382111101309250),
  (487118356892962, 487153738721441),
  (166478608534861, 166490406411129),
  (487119356892962, 487153738721441),
  (65303848023568, 65308391465139),
  (487120356892962, 487153738721441),
  (1929526990871047, 1929657004404750),
  (40470106509329, 40472805978396),
  (44283759717542, 44286703520131),
  (72662357522095, 72667083461211),
  (166479608534861, 166490406411129),
  (487122356892962, 487153738721441),
  (487123356892962, 487153738721441),
  (85327642477905, 85332916538789),
  (14793123596678027, 14794037033769750),
  (487124356892962, 487153738721441),
  (55493536178287, 55496802137043),
  (11881106265682, 11881798505401),
  (487126356892962, 487153738721441),
  (44379620790034081, 44382111101309250),
  (40470606509329, 40472805978396),
  (2839341218416, 2839495281093),
  (487127356892962, 487153738721441),
  (166481608534861, 166490406411129),
  (487128356892962, 487153738721441),
  (72663357522095, 72667083461211),
  (44379870790034081, 44382111101309250),
  (85328642477905, 85332916538789),
  (487129356892962, 487153738721441),
  (487130356892962, 487153738721441),
  (166482608534861, 166490406411129),
  (487131356892962, 487153738721441),
  (4931124532226009, 4931345677923250),
  (44284759717542, 44286703520131),
  (13490368836443, 13490935326132),
  (487133356892962, 487153738721441),
  (55494536178287, 55496802137043),
  (487134356892962, 487153738721441),
  (44380370790034081, 44382111101309250),
  (7256205335952, 7256487940571),
  (85329642477905, 85332916538789),
  (487135356892962, 487153738721441),
  (351035543585, 351048712373),
  (487136356892962, 487153738721441),
  (166484608534861, 166490406411129),
  (487137356892962, 487153738721441),
  (44380620790034081, 44382111101309250),
  (487138356892962, 487153738721441),
  (1759635065623, 1759687216452),
  (487139356892962, 487153738721441),
  (7238504718907, 7238713322223),
  (14793623596678027, 14794037033769750),
  (487140356892962, 487153738721441),
  (85330642477905, 85332916538789),
  (487141356892962, 487153738721441),
  (72665357522095, 72667083461211),
  (65306848023568, 65308391465139),
  (487142356892962, 487153738721441),
  (18498512059429, 18498934045681),
  (44381120790034081, 44382111101309250),
  (44285759717542, 44286703520131),
  (487144356892962, 487153738721441),
  (10603119337, 10603302588),
  (487145356892962, 487153738721441),
  (479791379063, 479799442107),
  (44381370790034081, 44382111101309250),
  (487146356892962, 487153738721441),
  (85331642477905, 85332916538789),
  (487147356892962, 487153738721441),
  (14793873596678027, 14794037033769750),
  (487148356892962, 487153738721441),
  (166488608534861, 166490406411129),
  (72666357522095, 72667083461211),
  (487149356892962, 487153738721441),
  (65307848023568, 65308391465139),
  (487150356892962, 487153738721441),
  (44381870790034081, 44382111101309250),
  (13490868836443, 13490935326132),
  (487151356892962, 487153738721441),
  (55496536178287, 55496802137043),
  (85332642477905, 85332916538789),
  (487152356892962, 487153738721441),
  (1940850027462, 1940851548691),
  (1, 1)]

theorem cert1 : chkH (TM kS1 v_g2_merge3_uarb1) P1 Q1 (0 + ubC (TM kS1 v_g2_merge3_uarb1) [])
    (0 + lbC (TM kS1 v_g2_merge3_uarb1) Qc1) pts1 = true := by decide +kernel

theorem safe1_T :
    OnGcdArbKappaTight.AllOK (TM kS1 v_g2_merge3_uarb1) (P1 ++ []) (Q1 ++ Qc1) 0 0 :=
  allOK_split _ _ _ _ _ 0 0 (by decide) (by decide)
    (allOK_of_chkH _ _ _ _ _ pts1 (by decide) (by decide) (by decide) cert1)

theorem pP1 (d : E → Nat) :
    Formal.Core.Substrate.pathDelay d F_h21.P = Formal.Core.Substrate.pathDelay d (P1 ++ []) := by
  simp [Formal.Core.Substrate.pathDelay, F_h21, P1]
theorem pQ1 (d : E → Nat) :
    Formal.Core.Substrate.pathDelay d F_h21.Q = Formal.Core.Substrate.pathDelay d (Q1 ++ Qc1) := by
  simp [Formal.Core.Substrate.pathDelay, F_h21, Q1, Qc1]; omega

/-- **D1's binding row, safe side (exact).** For every `κ ≤ κS1`, every realization of A's corner
model of seed 2 merge3.uarb1 satisfies h21. -/
theorem h21_safe (k : AK) (H_KAPPA : k.num * 1000000000000 ≤ k.den * 80163500491) :
    ConstraintsKappa.AllOK (litModel k v_g2_merge3_uarb1) F_h21.P F_h21.Q F_h21.a F_h21.b := by
  have h := allOK_toA safe1_T k (by
    show k.num * 1000000000000 ≤ 80163500491 * k.den
    rw [Nat.mul_comm 80163500491]; exact H_KAPPA)
  intro d hd
  have := h d hd
  rw [pP1, pQ1]; exact this

def kU1A : AK := ⟨80163500492, 1000000000000, by decide, by decide⟩

/-- The violating corner (`t ≈ 1 − 1.1e-5`, next to the slow end). -/
def cE1 : Formal.Core.Substrate.Corner := ⟨1345457287, 121787089223186, by decide⟩

/-- A realization of all 35 arcs at `cE1`, `κU1` (fs): the form's data arcs at `⌊(1+κU1)n⌋`,
its request arcs at `⌈(1−κU1)n⌉`; `ag2` (ugrant O6 from the q pin, not in the form) at
`⌊(1+κU1)n⌋`; every other arc at `⌈(1−κU1)n⌉`. -/
def dE1 : E → Nat
  | .ac => 384839
  | .dS1 => 0
  | .dS2 => 0
  | .d12 => 0
  | .es => 126937
  | .e1 => 126937
  | .e2 => 126937
  | .ps => 322861
  | .p1 => 261232
  | .p2 => 465434
  | .cq => 21389
  | .qs => 776694
  | .qgw => 263958
  | .pqg => 115899
  | .rs1 => 593291
  | .rg1 => 405645
  | .rs2 => 231797
  | .rg2 => 722624
  | .gw1 => 338627
  | .pg1 => 468194
  | .gw2 => 158090
  | .pg2 => 479232
  | .fa1 => 253791
  | .fa2 => 841235
  | .aq => 114059
  | .aRq => 141654
  | .aR1 => 141654
  | .aR2 => 110380
  | .ag1q => 109460
  | .ag1r => 140734
  | .ag2 => 133939
  | .ac1 => 114059
  | .ac2 => 114059
  | .ag2r => 133939
  | .srv => 3797059

theorem dE1_realizes : (litModel kU1A v_g2_merge3_uarb1).RealizesAt cE1 dE1 := by
  intro e; cases e <;> decide

theorem dE1_realizes_ge (k : AK) (H_KAPPA : k.den * 80163500492 ≤ k.num * 1000000000000) :
    (litModel k v_g2_merge3_uarb1).RealizesAt cE1 dE1 := by
  intro e
  have hk : (OnGcdArbKappaTightA.toK kU1A).num * (OnGcdArbKappaTightA.toK k).den ≤
      (OnGcdArbKappaTightA.toK k).num * (OnGcdArbKappaTightA.toK kU1A).den := by
    show 80163500492 * k.den ≤ k.num * 1000000000000
    rw [Nat.mul_comm 80163500492]; exact H_KAPPA
  exact (OnGcdArbKappaTightA.scat_iff _ _ _ _).2
    (OnGcdArbKappaTight.scat_mono hk ((OnGcdArbKappaTightA.scat_iff _ _ _ _).1 (dE1_realizes e)))

/-- The violation by 1 fs: request side 856562 fs, data side 856563 fs. -/
theorem dE1_viol : Formal.Core.Substrate.pathDelay dE1 F_h21.Q + 1 =
    Formal.Core.Substrate.pathDelay dE1 F_h21.P := by decide

/-- **D1's binding row, unsafe side (exact).** For every `κ ≥ κU1 = κS1 + 10⁻¹²`. -/
theorem h21_unsafe (k : AK) (H_KAPPA : k.den * 80163500492 ≤ k.num * 1000000000000) :
    ¬ ConstraintsKappa.AllOK (litModel k v_g2_merge3_uarb1) F_h21.P F_h21.Q F_h21.a F_h21.b := by
  intro h
  have := h dE1 ⟨cE1, dE1_realizes_ge k H_KAPPA⟩
  have := dE1_viol
  simp only [F_h21] at *
  omega

/-- OnGcdArbKappa's row bounds `κ* = 138217/1724217 < κS1 < κU1 < κu = 46075/574739`. -/
theorem h21_inside :
    OnGcdArbKappa.R_g2_merge3_uarb1_lit_h21.p = 138217 ∧
    OnGcdArbKappa.R_g2_merge3_uarb1_lit_h21.q = 1724217 ∧
    OnGcdArbKappa.R_g2_merge3_uarb1_lit_h21.pu = 46075 ∧
    OnGcdArbKappa.R_g2_merge3_uarb1_lit_h21.qu = 574739 ∧
    138217 * 1000000000000 < 80163500491 * 1724217 ∧
    80163500492 * 574739 < 46075 * 1000000000000 :=
  ⟨rfl, rfl, rfl, rfl, by decide, by decide⟩

/-! ### Gate level, bare cell (ArbPin's model: real INITs, A0 low) -/

/-- **Gate-level counter-trace (bare cell), κ ≥ κU1.** The realization `dE1` violates h21, the
q → O5 read is faster than q → O6 (`ag1q < ag2`), and on its point box (every window of width
0, fixed delays) there is a transport behaviour of `bd_arbcell` (r1 waiting, r2 released at 0,
q = 0 before) in which both grants are high. -/
theorem h21_gate_unsafe (k : AK) (H_KAPPA : k.den * 80163500492 ≤ k.num * 1000000000000) :
    (litModel k v_g2_merge3_uarb1).Realizes dE1 ∧ ¬ holds dE1 F_h21 ∧ dE1 .ag1q < dE1 .ag2 ∧
    ∃ c : ArbPin.Cell (OnGcdArbKappa.boxOf dE1) false ArbPin.hi1 (ArbPin.dn 0),
      ArbPin.Transport c ∧ ¬ ArbPin.Excl c := by
  refine ⟨⟨cE1, dE1_realizes_ge k H_KAPPA⟩, ?_, by decide, ?_⟩
  · unfold holds; have := dE1_viol; simp only [F_h21] at *; omega
  · exact ArbPin2.h21_kfail (OnGcdArbKappa.boxOf_ok dE1 (by decide)) (by decide) (by decide)
      (Int.le_refl 0)

/-! ### The same race in 7j's gate relations, every delay a corner-model realization

`D7` is the 7h/7j delay record of `dE1`: it realises Bar's record (`Real7 (xOfB dE1) D7`), its
server bound is the realised graph path (`smin = d srv`, 3.797 ns), and every route and arc is
the realised one (the O5 arc from the r2 pin, which O5 = r1·q does not read and the data has
no arc for, is set to the O5 arc from r1). `S7` is a run of 7j's gate relations (real INITs,
every t ∈ ℤ, server relation included) in which g1 and g2 overlap at 856562 fs. In it A0 never
rises: client 2's request was never acknowledged, and client 2 withdraws it at 0. So `S7` is
NOT a four-phase run (no `Scn2`); in every four-phase run (`Scn2`, which assumes H_SETTLED) the
hold covers this race and the r2 → r1 handover is RT1bs (`g2m3_held_rt1bs`). -/
def D7 : ArbHeldTimed.Dl where
  wr1s := 593291
  wr2s := 231797
  wr1g := 405645
  wr2g := 722624
  wfb := 798083
  wa0s := 834637
  wq := 401246
  wg1 := 806821
  wa01 := 773008
  wfa1 := 253791
  wg2 := 637322
  wa02 := 977210
  wfa2 := 841235
  qr := 114059
  qf := 114059
  Rr1 := 141654
  Rf1 := 141654
  Rr2 := 110380
  Rf2 := 110380
  Rrq := 141654
  Rfq := 141654
  g1r1 := 140734
  g1f1 := 140734
  g1r2 := 140734
  g1f2 := 140734
  g1rq := 109460
  g1fq := 109460
  g2r := 133939
  g2f := 133939
  c1r := 114059
  c1f := 114059
  c2r := 114059
  c2f := 114059
  smin := 3797059
  H_NONNEG := by omega
  H_RISE_LE_FALL := by omega
  H_LOOP_POS := by omega

theorem D7_real : OnGcdArbA0.Real7 (OnGcdArbKappa.xOfB dE1) D7 ∧ D7.smin = dE1 .srv ∧
    D7.wr1s = dE1 .rs1 ∧ D7.wr2s = dE1 .rs2 ∧ D7.wr1g = dE1 .rg1 ∧ D7.wr2g = dE1 .rg2 ∧
    D7.Rr1 = dE1 .aR1 ∧ D7.Rr2 = dE1 .aR2 ∧ D7.Rfq = dE1 .aRq ∧ D7.g1r1 = dE1 .ag1r ∧
    D7.g1fq = dE1 .ag1q := by
  refine ⟨?_, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide⟩
  unfold OnGcdArbA0.Real7; decide

def S7 : ArbHeldTimed.Sigs where
  r1 := fun _ => true
  r2 := fun t => decide (t < 0)
  q := fun t => decide (345856 ≤ t)
  R0 := fun t => decide (1285593 ≤ t) || decide (t < 342177)
  g1 := fun t => decide (856562 ≤ t)
  g2 := fun t => decide (t < 856563)
  A0 := fun _ => false
  A1 := fun _ => false
  A2 := fun _ => false

theorem S7_run : ArbHeldTimed.Run D7 S7 where
  H_q := by intro t; rw [Bool.eq_iff_iff]; simp [S7, D7, ArbHeldTimed2.FS_bool]; omega
  H_R0 := by intro t; rw [Bool.eq_iff_iff]; simp [S7, D7, ArbHeldTimed.FR_eq]; omega
  H_g1 := by intro t; rw [Bool.eq_iff_iff]; simp [S7, D7, ArbHeldTimed.FG1_eq]; omega
  H_g2 := by intro t; rw [Bool.eq_iff_iff]; simp [S7, D7, ArbHeldTimed.FG2_eq]; omega
  H_A1 := by intro t; simp [S7, ArbHeldTimed.CE_eq]
  H_A2 := by intro t; simp [S7, ArbHeldTimed.CE_eq]
  H_SRV := by intro t h; exact absurd rfl h

/-- **The h21 race in 7j's gate relations**, every delay (server included) realised at κ ≥ κU1:
both grants high at 856562 fs; A0 and A2 low throughout (client 2 never acknowledged). -/
theorem h21_7j_bare (k : AK) (H_KAPPA : k.den * 80163500492 ≤ k.num * 1000000000000) :
    (litModel k v_g2_merge3_uarb1).Realizes dE1 ∧ OnGcdArbA0.Real7 (OnGcdArbKappa.xOfB dE1) D7 ∧
    D7.smin = dE1 .srv ∧ ArbHeldTimed.Run D7 S7 ∧
    (S7.g1 856562 = true ∧ S7.g2 856562 = true) ∧
    (∀ t, S7.A0 t = false ∧ S7.A2 t = false) ∧ (∀ t, S7.r2 t = decide (t < 0)) :=
  ⟨⟨cE1, dE1_realizes_ge k H_KAPPA⟩, D7_real.1, D7_real.2.1, S7_run, by decide,
    fun _ => ⟨rfl, rfl⟩, fun _ => rfl⟩

/-! ### The four-phase handover of the same arbiter (7j, Scn2) with the server credited -/

/-- In 7j's four-phase r2 → r1 handover (`Scn2`, H_SETTLED), seed 2 merge3.uarb1 is grant-exclusive
for every κ ≤ 5293597/6879597 ≈ 0.769 (its RT1bs row), with the A0 branch, ustate O6, q prefix
and server all realised: D1's binding row is a bare-cell row only. -/
theorem g2m3_held_rt1bs (k : AK) (H_KAPPA : k.num * 6879597 ≤ k.den * 5293597) {d : E → Nat}
    (hd : (litModel k v_g2_merge3_uarb1).Realizes d) {cr : Int} {D : ArbHeldTimed.Dl}
    {s : ArbHeldTimed.Sigs} {t0 ta TA TA2 Hz : Int}
    (hr : OnGcdArbFix.Real2 (OnGcdArbKappa.qOf d) cr (d .cq) D)
    (hA : D.wa0s = d .ac + d .dS1 + d .dS2 + d .es + d .ps) (hq : D.qr = d .aq)
    (H_SERVER_GRAPH : (d .srv : Int) ≤ D.smin)
    (R : ArbHeldTimed.Run D s) (S : ArbHeldTimed2.Scn2 D s t0 ta TA TA2 Hz) :
    ∀ t, t < Hz → (s.g1 t && s.g2 t) = false :=
  OnGcdArbKappa.rt1bs_gate d
    (OnGcdArbKappa.form_safe (by decide) (by decide +kernel :
      OnGcdArbKappa.certFor .lit OnGcdArbKappa.F_rt1bs v_g2_merge3_uarb1 5293597 6879597 = true)
      k H_KAPPA d hd) hr hA hq H_SERVER_GRAPH R S

/-! ## 5. D2's binding row: seed 4 merge12.uarb2, fork2 (7g, the A0 fall to ua2)

`d(d12) + d(e2) + d(p2) ≤ d(dS1) + d(es) + d(ps) + d(cq) + d(qgw) + d(pqg) + d(gw2) + d(pg2) +
d(aq) + d(ag2)`: binds at the FAST end (κ\* = 121144/559431), so Tight's certificate
(tail relaxation) applies; `dS1` (0 fs) and `cq` are constant arcs. -/

def P2 : List E := [.d12, .e2, .p2]
def Q2 : List E := [.es, .ps, .qgw, .pqg, .gw2, .pg2, .aq, .ag2]
def Qc2 : List E := [.dS1, .cq]

/-- `κS2 = 216552148868 / 10¹²` (≈ 0.2165521489). -/
def kS2 : OnGcdArbKappaTight.Kappa := ⟨216552148869, 1000000000000, by decide, by decide⟩

def pts2 : List (Nat × Nat) := [
  (1266446, 16930350738413),
  (4849299839, 8211727004859000),
  (35312313, 41326874147213),
  (128799338, 50791052215239),
  (116699746723, 40151702370515000),
  (4317963631, 1317171699715675),
  (18409387, 5288272995141),
  (3316588871, 912414111651000),
  (195990598331, 41362773061512000),
  (253799338, 50791052215239),
  (3089564981, 489654906957500),
  (54849299839, 8211727004859000),
  (285312313, 41326874147213),
  (126266446, 16930350738413),
  (10567963631, 1317171699715675),
  (366699746723, 40151702370515000),
  (79849299839, 8211727004859000),
  (71971334, 7255864602177),
  (148663532777, 13787591020504000),
  (628799338, 50791052215239),
  (16817963631, 1317171699715675),
  (34949766613, 2737242334953000),
  (535312313, 41326874147213),
  (211674765, 15473095059857),
  (251266446, 16930350738413),
  (616699746723, 40151702370515000),
  (18549899977, 1173103857837000),
  (99427228333, 5908967580216000),
  (878799338, 50791052215239),
  (1214103349, 69324826300825),
  (154849299839, 8211727004859000),
  (41332227, 2175098639327),
  (9339564981, 489654906957500),
  (305228161, 15864818985423),
  (1003799338, 50791052215239),
  (866699746723, 40151702370515000),
  (59949766613, 2737242334953000),
  (376266446, 16930350738413),
  (29317963631, 1317171699715675),
  (945990598331, 41362773061512000),
  (1253799338, 50791052215239),
  (204849299839, 8211727004859000),
  (1035312313, 41326874147213),
  (35567963631, 1317171699715675),
  (196971334, 7255864602177),
  (1116699746723, 40151702370515000),
  (229849299839, 8211727004859000),
  (398663532777, 13787591020504000),
  (501266446, 16930350738413),
  (461674765, 15473095059857),
  (9438862957, 304138037217000),
  (1285312313, 41326874147213),
  (41817963631, 1317171699715675),
  (15589564981, 489654906957500),
  (1628799338, 50791052215239),
  (71931565617, 2113247493185000),
  (279849299839, 8211727004859000),
  (1753799338, 50791052215239),
  (1445990598331, 41362773061512000),
  (555228161, 15864818985423),
  (48067963631, 1317171699715675),
  (626266446, 16930350738413),
  (43549899977, 1173103857837000),
  (1535312313, 41326874147213),
  (2003799338, 50791052215239),
  (109949766613, 2737242334953000),
  (1616699746723, 40151702370515000),
  (99764152843, 2433104297736000),
  (54317963631, 1317171699715675),
  (2128799338, 50791052215239),
  (42201, 1000000000)]

theorem cert2 : OnGcdArbKappaTight.chk (TM kS2 v_g4_merge12_uarb2) P2 Q2
    (0 + ubC (TM kS2 v_g4_merge12_uarb2) []) (0 + lbC (TM kS2 v_g4_merge12_uarb2) Qc2)
    ((0, 1) :: pts2) = true := by decide +kernel

theorem safe2_T :
    OnGcdArbKappaTight.AllOK (TM kS2 v_g4_merge12_uarb2) (P2 ++ []) (Q2 ++ Qc2) 0 0 :=
  allOK_split _ _ _ _ _ 0 0 (by decide) (by decide)
    (OnGcdArbKappaTight.allOK_of_chk _ _ _ _ _ pts2 (by decide) (by decide) (by decide) cert2)

theorem pP2 (d : E → Nat) :
    Formal.Core.Substrate.pathDelay d F_fork2.P = Formal.Core.Substrate.pathDelay d (P2 ++ []) := by
  simp [Formal.Core.Substrate.pathDelay, F_fork2, P2]
theorem pQ2 (d : E → Nat) :
    Formal.Core.Substrate.pathDelay d F_fork2.Q = Formal.Core.Substrate.pathDelay d (Q2 ++ Qc2) := by
  simp [Formal.Core.Substrate.pathDelay, F_fork2, Q2, Qc2]; omega

/-- **D2's binding row, safe side (exact).** -/
theorem fork2_safe (k : AK) (H_KAPPA : k.num * 1000000000000 ≤ k.den * 216552148868) :
    ConstraintsKappa.AllOK (litModel k v_g4_merge12_uarb2) F_fork2.P F_fork2.Q F_fork2.a F_fork2.b := by
  have h := allOK_toA safe2_T k (by
    show k.num * 1000000000000 ≤ 216552148868 * k.den
    rw [Nat.mul_comm 216552148868]; exact H_KAPPA)
  intro d hd
  have := h d hd
  rw [pP2, pQ2]; exact this

def kU2A : AK := ⟨216552148869, 1000000000000, by decide, by decide⟩

/-- The violating corner (`t ≈ 1.28e-5`, next to the fast end). -/
def cE2 : Formal.Core.Substrate.Corner := ⟨32846488622279677, 419397183323, by decide⟩

/-- A realization of all 35 arcs at `cE2`, `κU2` (fs): the form's data arcs at `⌊(1+κU2)n⌋`,
every other arc at `⌈(1−κU2)n⌉`. -/
def dE2 : E → Nat
  | .ac => 0
  | .dS1 => 0
  | .dS2 => 0
  | .d12 => 128904
  | .es => 46789
  | .e1 => 62789
  | .e2 => 195054
  | .ps => 25855
  | .p1 => 135540
  | .p2 => 209252
  | .cq => 18267
  | .qs => 212625
  | .qgw => 77422
  | .pqg => 69729
  | .rs1 => 163471
  | .rg1 => 61111
  | .rs2 => 191635
  | .rg2 => 207591
  | .gw1 => 220330
  | .pg1 => 25855
  | .gw2 => 154906
  | .pg2 => 69729
  | .fa1 => 134695
  | .fa2 => 274420
  | .aq => 35256
  | .aRq => 34473
  | .aR1 => 32906
  | .aR2 => 34473
  | .ag1q => 36040
  | .ag1r => 37607
  | .ag2 => 35256
  | .ac1 => 35256
  | .ac2 => 35256
  | .ag2r => 35256
  | .srv => 779547

theorem dE2_realizes : (litModel kU2A v_g4_merge12_uarb2).RealizesAt cE2 dE2 := by
  intro e; cases e <;> decide

theorem dE2_realizes_ge (k : AK) (H_KAPPA : k.den * 216552148869 ≤ k.num * 1000000000000) :
    (litModel k v_g4_merge12_uarb2).RealizesAt cE2 dE2 := by
  intro e
  have hk : (OnGcdArbKappaTightA.toK kU2A).num * (OnGcdArbKappaTightA.toK k).den ≤
      (OnGcdArbKappaTightA.toK k).num * (OnGcdArbKappaTightA.toK kU2A).den := by
    show 216552148869 * k.den ≤ k.num * 1000000000000
    rw [Nat.mul_comm 216552148869]; exact H_KAPPA
  exact (OnGcdArbKappaTightA.scat_iff _ _ _ _).2
    (OnGcdArbKappaTight.scat_mono hk ((OnGcdArbKappaTightA.scat_iff _ _ _ _).1 (dE2_realizes e)))

theorem dE2_viol : Formal.Core.Substrate.pathDelay dE2 F_fork2.Q + 1 =
    Formal.Core.Substrate.pathDelay dE2 F_fork2.P := by decide

/-- **D2's binding row, unsafe side (exact).** For every `κ ≥ κU2 = κS2 + 10⁻¹²`. -/
theorem fork2_unsafe (k : AK) (H_KAPPA : k.den * 216552148869 ≤ k.num * 1000000000000) :
    ¬ ConstraintsKappa.AllOK (litModel k v_g4_merge12_uarb2) F_fork2.P F_fork2.Q F_fork2.a F_fork2.b := by
  intro h
  have := h dE2 ⟨cE2, dE2_realizes_ge k H_KAPPA⟩
  have := dE2_viol
  simp only [F_fork2] at *
  omega

theorem fork2_inside :
    OnGcdArbKappa.certFor .lit F_fork2 v_g4_merge12_uarb2 121144 559431 = true ∧
    121144 * 1000000000000 < 216552148868 * 559431 ∧ 216552148869 * 372954 < 80767 * 1000000000000 :=
  ⟨by decide +kernel, by decide, by decide⟩

/-- A record in the point box is the record. -/
theorem xin_point {x y : OnGcdArbA0.X} (h : OnGcdArbA0.Xin x x y) : y = x := by
  obtain ⟨h1, h2⟩ := h
  unfold OnGcdArbA0.X.le at h1 h2
  cases x; cases y
  simp only [OnGcdArbA0.X.mk.injEq] at *
  omega

/-- **Gate-level counter-run (7g, exact), κ ≥ κU2.** For the realization `dE2` the A0 fork of
client 2 is NOT safe: some run of 7g's gate relations (real INITs, per-pin transport delays of
`dE2`) fires A2 spuriously (7g's `fork2_box_iff` on the point box). -/
theorem fork2_gate_unsafe (k : AK) (H_KAPPA : k.den * 216552148869 ≤ k.num * 1000000000000) :
    (litModel k v_g4_merge12_uarb2).Realizes dE2 ∧ ¬ holds dE2 F_fork2 ∧
    ¬ OnGcdArbA0.Safe2 (OnGcdArbKappa.xOf dE2) := by
  refine ⟨⟨cE2, dE2_realizes_ge k H_KAPPA⟩, ?_, ?_⟩
  · unfold holds; have := dE2_viol; simp only [F_fork2] at *; omega
  · intro hs
    have h := (OnGcdArbA0.fork2_box_iff (OnGcdArbKappa.xOf dE2) (OnGcdArbKappa.xOf dE2)
      (OnGcdArbKappa.xle_refl _) (by decide) (by decide)).1
      (fun x hx => by rw [xin_point hx]; exact hs)
    exact absurd h (by decide)

/-! ## 6. The design theorems (lit) -/

open Formal.Cells.OnGcdArbKappa (Form certFor form_safe frac_trans F_fork1 F_mP F_mG F_mA F_mGG
  F_nP F_nG F_nA F_nGG F_rt1s F_rt1bs F_h12 F_o1x F_o2x)

/-- D1: OnGcdArbKappa's forms with the server credited (no server-free `rt1`/`rt1b`). -/
def formsSrv : List Form := [F_fork1, F_fork2, F_mP, F_mG, F_mA, F_mGG, F_nP, F_nG, F_nA, F_nGG,
  F_rt1s, F_rt1bs, F_h12, F_h21, F_o1x, F_o2x]
def formsSrvO : List Form := [F_fork1, F_fork2, F_mP, F_mG, F_mA, F_mGG, F_nP, F_nG, F_nA, F_nGG,
  F_rt1s, F_rt1bs, F_h12, F_o1x, F_o2x]
/-- D2: the held-arbiter (four-phase) forms. -/
def formsHeld : List Form := [F_fork1, F_fork2, F_mP, F_mG, F_mA, F_mGG, F_nP, F_nG, F_nA, F_nGG,
  F_rt1s, F_rt1bs]
def formsHeldO : List Form := [F_fork1, F_mP, F_mG, F_mA, F_mGG, F_nP, F_nG, F_nA, F_nGG,
  F_rt1s, F_rt1bs]

def arbsO1 : List (E → Quad) := [OnGcdArbKappa.v_g2_merge10_uarb1, OnGcdArbKappa.v_g2_merge11_uarb1, OnGcdArbKappa.v_g2_merge12_uarb1, OnGcdArbKappa.v_g2_merge12_uarb2, OnGcdArbKappa.v_g2_merge2_uarb1, OnGcdArbKappa.v_g2_merge4_uarb1, OnGcdArbKappa.v_g2_merge6_uarb1, OnGcdArbKappa.v_g2_merge9_uarb1, OnGcdArbKappa.v_g3_merge10_uarb1, OnGcdArbKappa.v_g3_merge11_uarb1, OnGcdArbKappa.v_g3_merge12_uarb1, OnGcdArbKappa.v_g3_merge12_uarb2, OnGcdArbKappa.v_g3_merge2_uarb1, OnGcdArbKappa.v_g3_merge3_uarb1, OnGcdArbKappa.v_g3_merge4_uarb1, OnGcdArbKappa.v_g3_merge6_uarb1, OnGcdArbKappa.v_g3_merge9_uarb1, OnGcdArbKappa.v_g4_merge10_uarb1, OnGcdArbKappa.v_g4_merge11_uarb1, OnGcdArbKappa.v_g4_merge12_uarb1, OnGcdArbKappa.v_g4_merge12_uarb2, OnGcdArbKappa.v_g4_merge2_uarb1, OnGcdArbKappa.v_g4_merge3_uarb1, OnGcdArbKappa.v_g4_merge4_uarb1, OnGcdArbKappa.v_g4_merge6_uarb1, OnGcdArbKappa.v_g4_merge9_uarb1, OnGcdArbKappa.v_gd_merge10_uarb1, OnGcdArbKappa.v_gd_merge11_uarb1, OnGcdArbKappa.v_gd_merge12_uarb1, OnGcdArbKappa.v_gd_merge12_uarb2, OnGcdArbKappa.v_gd_merge2_uarb1, OnGcdArbKappa.v_gd_merge3_uarb1, OnGcdArbKappa.v_gd_merge4_uarb1, OnGcdArbKappa.v_gd_merge6_uarb1, OnGcdArbKappa.v_gd_merge9_uarb1]
def arbsO2 : List (E → Quad) := [OnGcdArbKappa.v_g2_merge10_uarb1, OnGcdArbKappa.v_g2_merge11_uarb1, OnGcdArbKappa.v_g2_merge12_uarb1, OnGcdArbKappa.v_g2_merge12_uarb2, OnGcdArbKappa.v_g2_merge2_uarb1, OnGcdArbKappa.v_g2_merge3_uarb1, OnGcdArbKappa.v_g2_merge4_uarb1, OnGcdArbKappa.v_g2_merge6_uarb1, OnGcdArbKappa.v_g2_merge9_uarb1, OnGcdArbKappa.v_g3_merge10_uarb1, OnGcdArbKappa.v_g3_merge11_uarb1, OnGcdArbKappa.v_g3_merge12_uarb1, OnGcdArbKappa.v_g3_merge12_uarb2, OnGcdArbKappa.v_g3_merge2_uarb1, OnGcdArbKappa.v_g3_merge3_uarb1, OnGcdArbKappa.v_g3_merge4_uarb1, OnGcdArbKappa.v_g3_merge6_uarb1, OnGcdArbKappa.v_g3_merge9_uarb1, OnGcdArbKappa.v_g4_merge10_uarb1, OnGcdArbKappa.v_g4_merge11_uarb1, OnGcdArbKappa.v_g4_merge12_uarb1, OnGcdArbKappa.v_g4_merge2_uarb1, OnGcdArbKappa.v_g4_merge3_uarb1, OnGcdArbKappa.v_g4_merge4_uarb1, OnGcdArbKappa.v_g4_merge6_uarb1, OnGcdArbKappa.v_g4_merge9_uarb1, OnGcdArbKappa.v_gd_merge10_uarb1, OnGcdArbKappa.v_gd_merge11_uarb1, OnGcdArbKappa.v_gd_merge12_uarb1, OnGcdArbKappa.v_gd_merge12_uarb2, OnGcdArbKappa.v_gd_merge2_uarb1, OnGcdArbKappa.v_gd_merge3_uarb1, OnGcdArbKappa.v_gd_merge4_uarb1, OnGcdArbKappa.v_gd_merge6_uarb1, OnGcdArbKappa.v_gd_merge9_uarb1]

theorem cert_D1a : arbsO1.all (fun v => formsSrv.all (fun f =>
    certFor .lit f v 80163500491 1000000000000)) = true := by decide +kernel
theorem cert_D1b : formsSrvO.all (fun f =>
    certFor .lit f v_g2_merge3_uarb1 80163500491 1000000000000) = true := by decide +kernel
theorem cert_D2a : arbsO2.all (fun v => formsHeld.all (fun f =>
    certFor .lit f v 216552148868 1000000000000)) = true := by decide +kernel
theorem cert_D2b : formsHeldO.all (fun f =>
    certFor .lit f v_g4_merge12_uarb2 216552148868 1000000000000) = true := by decide +kernel

theorem mem_arbs1 {v : E → Quad} (hv : v ∈ OnGcdArbKappa.arbs) :
    v = v_g2_merge3_uarb1 ∨ v ∈ arbsO1 := by
  simp only [OnGcdArbKappa.arbs, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp [arbsO1]

theorem mem_arbs2 {v : E → Quad} (hv : v ∈ OnGcdArbKappa.arbs) :
    v = v_g4_merge12_uarb2 ∨ v ∈ arbsO2 := by
  simp only [OnGcdArbKappa.arbs, List.mem_cons, List.not_mem_nil, or_false] at hv
  rcases hv with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp [arbsO2]

theorem mem_formsSrv {f : Form} (hf : f ∈ formsSrv) : f = F_h21 ∨ f ∈ formsSrvO := by
  simp only [formsSrv, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with h | h | h | h | h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;>
    simp [formsSrvO]

theorem mem_formsHeld {f : Form} (hf : f ∈ formsHeld) : f = F_fork2 ∨ f ∈ formsHeldO := by
  simp only [formsHeld, List.mem_cons, List.not_mem_nil, or_false] at hf
  rcases hf with h | h | h | h | h | h | h | h | h | h | h | h <;> subst h <;> simp [formsHeldO]

/-- **D1, safe side.** For every κ ≤ κS1 ≈ 0.0801635005, on every routed gcd_hw arbiter, every
server-credited form holds on every realization of A's model. -/
theorem design_srv_holds {v : E → Quad} (hv : v ∈ OnGcdArbKappa.arbs) {f : Form}
    (hf : f ∈ formsSrv) (k : AK) (H_KAPPA : k.num * 1000000000000 ≤ k.den * 80163500491)
    {d : E → Nat} (hd : (litModel k v).Realizes d) : holds d f := by
  rcases mem_arbs1 hv with rfl | hv'
  · rcases mem_formsSrv hf with rfl | hf'
    · exact h21_safe k H_KAPPA d hd
    · exact form_safe (by decide) (List.all_eq_true.1 cert_D1b f hf') k H_KAPPA d hd
  · exact form_safe (by decide) (List.all_eq_true.1 (List.all_eq_true.1 cert_D1a v hv') f hf)
      k H_KAPPA d hd

/-- **D2, safe side.** For every κ ≤ κS2 ≈ 0.2165521489, every held-arbiter form. -/
theorem design_held_holds {v : E → Quad} (hv : v ∈ OnGcdArbKappa.arbs) {f : Form}
    (hf : f ∈ formsHeld) (k : AK) (H_KAPPA : k.num * 1000000000000 ≤ k.den * 216552148868)
    {d : E → Nat} (hd : (litModel k v).Realizes d) : holds d f := by
  rcases mem_arbs2 hv with rfl | hv'
  · rcases mem_formsHeld hf with rfl | hf'
    · exact fork2_safe k H_KAPPA d hd
    · exact form_safe (by decide) (List.all_eq_true.1 cert_D2b f hf') k H_KAPPA d hd
  · exact form_safe (by decide) (List.all_eq_true.1 (List.all_eq_true.1 cert_D2a v hv') f hf)
      k H_KAPPA d hd

/-- **D2 at the gate level (held arbiter, four-phase scenarios).** For every κ ≤ κS2, every
routed gcd_hw arbiter and every realization `d`: both A0 forks are safe on every 7g run; A1/A2
exclusive across both handovers (7h/7j) for every server no faster than the realised `srv`;
g1/g2 exclusive across both handovers (7h/7j) for every record whose A0 branch, ustate O6 arc
and q prefix are the realised ones and whose server is no faster than the realised `srv`. -/
theorem design_gate_held {v : E → Quad} (hv : v ∈ OnGcdArbKappa.arbs) (k : AK)
    (H_KAPPA : k.num * 1000000000000 ≤ k.den * 216552148868) {d : E → Nat}
    (hd : (litModel k v).Realizes d)
    (H_LOOP_ST : 0 < d .aq + d .cq + d .qs) (H_LOOP_UA1 : 0 < d .ac1 + d .fa1)
    (H_LOOP_UA2 : 0 < d .ac2 + d .fa2) :
    (OnGcdArbA0.Safe1 (OnGcdArbKappa.xOf d) ∧ OnGcdArbA0.Safe2 (OnGcdArbKappa.xOf d)) ∧
    (∀ (D : ArbHeldTimed.Dl) (s : ArbHeldTimed.Sigs) (t0 ta TA TA2 Hz : Int),
      OnGcdArbA0.Real7 (OnGcdArbKappa.xOf d) D → (d .srv : Int) ≤ D.smin → ArbHeldTimed.Run D s →
      ArbHeldTimed.Scn D s t0 ta TA TA2 Hz → ∀ t, t < Hz → (s.A1 t && s.A2 t) = false) ∧
    (∀ (D : ArbHeldTimed.Dl) (s : ArbHeldTimed.Sigs) (t0 ta TA TA2 Hz : Int),
      OnGcdArbA0.Real7 (OnGcdArbKappa.xOfB d) D → (d .srv : Int) ≤ D.smin → ArbHeldTimed.Run D s →
      ArbHeldTimed2.Scn2 D s t0 ta TA TA2 Hz → ∀ t, t < Hz → (s.A1 t && s.A2 t) = false) ∧
    (∀ (cr : Int) (D : ArbHeldTimed.Dl) (s : ArbHeldTimed.Sigs) (t0 ta TA TA2 Hz : Int),
      OnGcdArbFix.Real1 (OnGcdArbKappa.qOf d) cr (d .cq) D →
      D.wa0s = d .ac + d .dS1 + d .dS2 + d .es + d .ps → D.qf = d .aq →
      (d .srv : Int) ≤ D.smin → ArbHeldTimed.Run D s →
      ArbHeldTimed.Scn D s t0 ta TA TA2 Hz → ∀ t, t < Hz → (s.g1 t && s.g2 t) = false) ∧
    (∀ (cr : Int) (D : ArbHeldTimed.Dl) (s : ArbHeldTimed.Sigs) (t0 ta TA TA2 Hz : Int),
      OnGcdArbFix.Real2 (OnGcdArbKappa.qOf d) cr (d .cq) D →
      D.wa0s = d .ac + d .dS1 + d .dS2 + d .es + d .ps → D.qr = d .aq →
      (d .srv : Int) ≤ D.smin → ArbHeldTimed.Run D s →
      ArbHeldTimed2.Scn2 D s t0 ta TA TA2 Hz → ∀ t, t < Hz → (s.g1 t && s.g2 t) = false) := by
  have m : ∀ {f : Form}, f ∈ formsHeld → holds d f := fun hf => design_held_holds hv hf k H_KAPPA hd
  refine ⟨⟨OnGcdArbKappa.fork1_gate d (m (by simp [formsHeld])) H_LOOP_ST H_LOOP_UA1,
      OnGcdArbKappa.fork2_gate d (m (by simp [formsHeld])) H_LOOP_ST H_LOOP_UA2⟩,
    fun D s t0 ta TA TA2 Hz h hs R S => OnGcdArbKappa.rt2_gate d (m (by simp [formsHeld]))
      (m (by simp [formsHeld])) (m (by simp [formsHeld])) (m (by simp [formsHeld]))
      (m (by simp [formsHeld])) h hs R S,
    fun D s t0 ta TA TA2 Hz h hs R S => OnGcdArbKappa.rt2b_gate d (m (by simp [formsHeld]))
      (m (by simp [formsHeld])) (m (by simp [formsHeld])) (m (by simp [formsHeld]))
      (m (by simp [formsHeld])) h hs R S,
    fun cr D s t0 ta TA TA2 Hz h hA hq hs R S =>
      OnGcdArbKappa.rt1s_gate d (m (by simp [formsHeld])) h hA hq hs R S,
    fun cr D s t0 ta TA TA2 Hz h hA hq hs R S =>
      OnGcdArbKappa.rt1bs_gate d (m (by simp [formsHeld])) h hA hq hs R S⟩

/-- **D1 at the gate level.** For every κ ≤ κS1: everything of `design_gate_held`, and the bare
cell (ArbPin, H_A0_LOW) is exclusive for every per-pin behaviour of the realization's point box
in all four request scenarios (both handovers, both opposite-sense races). -/
theorem design_gate_srv {v : E → Quad} (hv : v ∈ OnGcdArbKappa.arbs) (k : AK)
    (H_KAPPA : k.num * 1000000000000 ≤ k.den * 80163500491) {d : E → Nat}
    (hd : (litModel k v).Realizes d)
    (H_LOOP_ST : 0 < d .aq + d .cq + d .qs) (H_LOOP_UA1 : 0 < d .ac1 + d .fa1)
    (H_LOOP_UA2 : 0 < d .ac2 + d .fa2) :
    (OnGcdArbA0.Safe1 (OnGcdArbKappa.xOf d) ∧ OnGcdArbA0.Safe2 (OnGcdArbKappa.xOf d)) ∧
    (∀ f : Int, 0 ≤ f → ∀ c : ArbPin.Cell (OnGcdArbKappa.boxOf d) true (ArbPin.dn f) ArbPin.hi1,
      ArbPin.Excl c) ∧
    (∀ f : Int, 0 ≤ f → ∀ c : ArbPin.Cell (OnGcdArbKappa.boxOf d) false ArbPin.hi1 (ArbPin.dn f),
      ArbPin.Excl c) ∧
    (∀ e1 e2 : Int, 0 ≤ e1 →
      ∀ c : ArbPin.Cell (OnGcdArbKappa.boxOf d) false (ArbPin.up e1) (ArbPin.dn e2), ArbPin.Excl c) ∧
    (∀ e1 e2 : Int, 0 ≤ e2 →
      ∀ c : ArbPin.Cell (OnGcdArbKappa.boxOf d) true (ArbPin.dn e1) (ArbPin.up e2), ArbPin.Excl c) := by
  have m : ∀ {f : Form}, f ∈ formsSrv → holds d f := fun hf => design_srv_holds hv hf k H_KAPPA hd
  have HL : 0 < d .cq + d .qs + d .aq := by omega
  have hk2 : k.num * 1000000000000 ≤ k.den * 216552148868 :=
    frac_trans (m1 := 80163500491) (m2 := 1000000000000) (by decide) H_KAPPA (by decide)
  have G := design_gate_held hv k hk2 hd H_LOOP_ST H_LOOP_UA1 H_LOOP_UA2
  exact ⟨G.1,
    fun f hf => OnGcdArbKappa.h12_gate d (m (by simp [formsSrv])) HL hf,
    fun f hf => OnGcdArbKappa.h21_gate d (m (by simp [formsSrv])) HL hf,
    fun e1 e2 he => OnGcdArbKappa.o1_gate d (m (by simp [formsSrv])) (m (by simp [formsSrv])) HL he,
    fun e1 e2 he => OnGcdArbKappa.o2_gate d (m (by simp [formsSrv])) (m (by simp [formsSrv])) HL he⟩

/-- **D1 is tight** (gate level, bare cell): from κU1 on, seed 2 merge3.uarb1's h21 fails on a
realization and the bare cell overlaps (`h21_gate_unsafe`); the same race is a run of 7j's
gate relations with every delay realised (`h21_7j_bare`), but not a four-phase one. -/
theorem design_srv_tight (k : AK) (H_KAPPA : k.den * 80163500492 ≤ k.num * 1000000000000) :
    v_g2_merge3_uarb1 ∈ OnGcdArbKappa.arbs ∧ F_h21 ∈ formsSrv ∧
    (litModel k v_g2_merge3_uarb1).Realizes dE1 ∧ ¬ holds dE1 F_h21 ∧
    ∃ c : ArbPin.Cell (OnGcdArbKappa.boxOf dE1) false ArbPin.hi1 (ArbPin.dn 0),
      ArbPin.Transport c ∧ ¬ ArbPin.Excl c := by
  obtain ⟨h1, h2, _, h4⟩ := h21_gate_unsafe k H_KAPPA
  exact ⟨by simp [OnGcdArbKappa.arbs], by simp [formsSrv], h1, h2, h4⟩

/-- **D2 is tight** (gate level, 7g): from κU2 on, seed 4 merge12.uarb2's client-2 A0 fork is
unsafe on a realization. -/
theorem design_held_tight (k : AK) (H_KAPPA : k.den * 216552148869 ≤ k.num * 1000000000000) :
    v_g4_merge12_uarb2 ∈ OnGcdArbKappa.arbs ∧ F_fork2 ∈ formsHeld ∧
    (litModel k v_g4_merge12_uarb2).Realizes dE2 ∧ ¬ holds dE2 F_fork2 ∧
    ¬ OnGcdArbA0.Safe2 (OnGcdArbKappa.xOf dE2) := by
  obtain ⟨h1, h2, h3⟩ := fork2_gate_unsafe k H_KAPPA
  exact ⟨by simp [OnGcdArbKappa.arbs], by simp [formsHeld], h1, h2, h3⟩

/-- Non-vacuity: κ = κS1 (and κS2) meet their `H_KAPPA`, A's fast endpoints realise every
arbiter's model at that κ, and the loop hypotheses hold there on all 36 arbiters. -/
theorem design_nonvacuous :
    (∃ k : AK, k.num * 1000000000000 ≤ k.den * 80163500491 ∧ k.num = 80163500491 ∧
      ∀ v : E → Quad, (litModel k v).Realizes (fun e => ((litModel k v).arc e).F)) ∧
    (∃ k : AK, k.num * 1000000000000 ≤ k.den * 216552148868 ∧ k.num = 216552148868 ∧
      ∀ v : E → Quad, (litModel k v).Realizes (fun e => ((litModel k v).arc e).F)) ∧
    (OnGcdArbKappa.arbs.all fun v => decide (0 < (v .aq).1 + (v .cq).1 + (v .qs).1) &&
      decide (0 < (v .ac1).1 + (v .fa1).1) && decide (0 < (v .ac2).1 + (v .fa2).1)) = true :=
  ⟨⟨⟨80163500491, 1000000000000, by decide, by decide⟩, by decide, rfl,
      fun v => ⟨_, Formal.Core.Substrate.realizes_fast _⟩⟩,
    ⟨⟨216552148868, 1000000000000, by decide, by decide⟩, by decide, rfl,
      fun v => ⟨_, Formal.Core.Substrate.realizes_fast _⟩⟩,
    OnGcdArbKappa.design_gate_nonvacuous.1⟩

/-! ## 7. The `cons` reading with the server credited -/

/-- Among the server-credited forms, the `cons` rows that fail at κ = 0 (`neg`) are exactly
seed 2 merge3.uarb1's h21 and o1x; every one of them has `pu = 0` (unsafe at every κ by
`OnGcdArbKappa.row_verdict`), and every other cons row passes at κ = 0 (`row_verdict` with
κ = 0). Among the held forms no cons row fails at κ = 0. -/
theorem cons_srv_neg :
    OnGcdArbKappa.rows.all (fun r => !(decide (r.rd = .cons)) || r.f.sf ||
      (r.neg == (decide (r.name = "g2_merge3_uarb1.cons.h21") ||
        decide (r.name = "g2_merge3_uarb1.cons.o1x"))) && (!r.neg || decide (r.pu = 0))) = true := by
  decide +kernel

end Formal.Cells.OnGcdArbKappaSrv
