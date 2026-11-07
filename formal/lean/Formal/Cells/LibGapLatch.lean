import Formal.Cells.Latch
import Formal.Cells.LibGapMux
open Formal.Core.LutList

/-!
# LibGapLatch: `bd_latch` setup_data, setup_pulse and hold, per pin, EXACT over the box

Probe Blp (shard B, Phase 2 library gap, follow-up of `LibGapSteer` /
`LibGapMux`). `bd_latch` (`cells/rtl/bd_latch.v`) holds every data bit of
every link in gcd_hw:

    pair: LUT6_2 #(.INIT(64'hFF33_CC00_B8B8_B8B8)) (.I0(d[i]), .I1(en), .I2(q[i]),
            .I3(d[i+1]), .I4(q[i+1]), .I5(1), .O5(q[i]), .O6(q[i+1]))
    odd:  LUT6   #(.INIT(64'hB8B8_B8B8_B8B8_B8B8)) (.I0(d), .I1(en), .I2(q),
            .I3(0), .I4(0), .I5(0), .O(q))

`Latch.odd_kleene`, `Latch.pair_o5_kleene`, `Latch.pair_o6_kleene` prove (for
all 3^5 Kleene inputs) that each of the three bits is the Kleene mux
`K3.mux en q d` of its OWN three pins; the other bit's pins of a pair never
reach it, X included. So one engine (sections 1-4, on `latM`) serves the
three bits, and section 5 restates it on the real INITs with the pair's
neighbour pins as arbitrary traces read through arbitrary read maps.

## Model (named hypotheses)

* **H_PIN_READ** (`LutEq`, per pin, feedback pin included): for `t ≥ 0` the
  bit's output is the real INIT (Kleene, H_KLEENE_LUT) of `d` (I0 / I3) read
  at `pd.σ t`, `en` (I1) at `pe.σ t` and its OWN output (I2 / I4) at
  `pq.σ t`. Each read map lies in its own window `[t - hi, t - lo]` (routed
  wire + site pin + that pin's own LUT arc to this output, `LibGapSteer.Rd`;
  NOT necessarily monotone, so no FIFO assumption). `pq.lo ≥ 1`.
  Before time 0 the output is ARBITRARY (power-up: bd_latch has no reset).
* **H_EN_TOKEN** (`EnTok A B C`): the enable at its driver is definite 1 on
  `[A, B)` and definite 0 from `C` on; ARBITRARY (any K3, X included) before
  `A` and on the closing window `[B, C)` (`A ≤ B ≤ C`). `C - B` is the X
  window of the falling enable (H_MUX_KLEENE: a moving select reads X).
* **H_D_STABLE** (`DStab v Td Tn`): `d` at its driver is definite `v` on
  `[Td, Tn)`; ARBITRARY (X included) elsewhere. `Tn` is the first instant the
  NEXT data is no longer definite `v` (the start of its X window).
* **H_T0**: `0 ≤ A + pe.lo` (the token is read after time 0).

## Spec (`Capt`)

`q t = v` (definite) at every `t ≥ 0` at which the enable pin reads the
closing window or later (`B ≤ pe.σ t`): from the instant the enable starts
to close, the latch shows the token's value, for ever (one token). This is
CElemStrict's `Spec` (one clean edge, the new value from the follow phase
on, X nowhere after it) for the latch.

## Results

* `capt_of_reads` (sufficient, read level, any read maps).
* `latch_pin_ok` (sufficient, any read maps in their windows):
  `H_SETUP_PULSE : A + pe.hi + pq.hi ≤ B + pe.lo`,
  `H_SETUP_DATA : Td + pd.hi + pq.hi ≤ B + pe.lo`,
  `H_HOLD : C + pe.hi ≤ Tn + pd.lo`.
* `box_exact` (headline, the JSON form): Capt for every read-map triple in
  the box `pd ∈ [Dlo,Dhi]`, `pe ∈ [Elo,Ehi]`, `pq ∈ [Qlo,Qhi]` (`Qlo ≥ 1`),
  every admissible `d`, `en` and every trace obeying H_PIN_READ
  **iff** `A + Ehi + Qhi ≤ B + Elo ∧ Td + Dhi + Qhi ≤ B + Elo ∧ C + Ehi ≤ Tn + Dlo`.
  The enable's rise is read at its slowest, its fall at its fastest
  (setup_pulse); the feedback pin enters setup_data and setup_pulse at its
  slowest and drops out of hold; the data pin drops out of setup_pulse.
* `sym_exact` (fixed per-pin delays, each anywhere in its box: rise = fall
  per arc, H_RF_SYM): same with setup_pulse **`A + Qhi ≤ B`** (the enable's
  delay cancels).
* `box_exact_edges` / `strict_edges`: the same in BINARY-EDGE times (`Ton`,
  `Toff` the enable's binary edges, `Tnew` the next data's binary edge; the
  X windows `we`, `wd` precede the binary edge, CElemStrict's convention):
  `Ton + Ehi + Qhi + we ≤ Toff + Elo`, `Td + Dhi + Qhi + we ≤ Toff + Elo`,
  `Toff + Ehi + wd ≤ Tnew + Dlo`. With one tick of X (`we = wd = 1`) all
  three are STRICT; with instantaneous selects (`we = wd = 0`) all three are
  `≤` (`atomic_edges`). setup_data's strictness is `CElemStrict.latch_facts`'
  race; hold's is new (its `strict_pending`).
* Necessity witnesses (`need_pulse_two`, `need_pulse_sym`, `need_data`,
  `need_hold`) build real traces (`run`, H_PIN_READ for all `t ≥ 0`).
* 1 ps counter-traces on concrete numbers, for EVERY trace obeying the
  hypotheses: `ct_pulse_x`, `ct_data_x`, `ct_hold_x` (an X is captured: the
  output reads X while the spec requires 1), `ct_pulse_wrong`,
  `ct_data_wrong`, `ct_hold_wrong` (instantaneous select, `C = B`: the wrong
  value 0 is captured).
* Real INITs: `odd_box_exact`, `o5_box_exact`, `o6_box_exact` (the pair's
  neighbour pins arbitrary, through arbitrary read maps), and the `sym`
  versions.
* Non-vacuity: `witness_*`, a run meeting every hypothesis, writing 0 → 1.

NOT covered: more than one token (apply per token: `Capt` is per token);
the source of `A, B, C` (the link's enable, `LinkTimed`) and of `Td, Tn`
(upstream latch / ForkData); a mid-rail select inside the mux tree beyond
H_KLEENE_LUT (grade B); the X window widths themselves (one tick is the
grid minimum, not a measured slew); correlated corners (box necessity takes
pins independent; for a corner model apply the per-realisation forms).
-/

namespace Formal.Cells.LibGapLatch
open Formal.Cells
open Formal.Cells.LibGapSteer (Rd Rd.const)
open Formal.Cells.LibGapMux (int_ind)

abbrev kb (b : Bool) : K3 := K3.ofBool b

/-! ## 0. The latch function and the real INITs -/

/-- The latch bit: `en = 1` passes `d`, `en = 0` holds `q`, `en = X` passes
a value only if `d = q` (Kleene mux). -/
def latM (d e q : K3) : K3 := K3.mux e q d

theorem odd_eq (d e q : K3) : lutK Latch.ODD [d, e, q, .f, .f, .f] = latM d e q :=
  Latch.odd_kleene d e q
theorem o5_eq (d e q dj qj : K3) : o5K Latch.PAIR [d, e, q, dj, qj, .t] = latM d e q :=
  Latch.pair_o5_kleene d e q dj qj
theorem o6_eq (di e qi d q : K3) : o6K Latch.PAIR [di, e, qi, d, q, .t] = latM d e q :=
  Latch.pair_o6_kleene di e qi d q

theorem m_same : ∀ (s : K3) (v : Bool), latM (kb v) s (kb v) = kb v := by decide
theorem m_t : ∀ d q : K3, latM d .t q = d := by decide
theorem m_f : ∀ d q : K3, latM d .f q = q := by decide
theorem m_badq : ∀ (s d : K3) (v : Bool), s ≠ .t → latM d s (kb (!v)) ≠ kb v := by decide
theorem m_badd : ∀ (q : K3) (v : Bool), latM (kb (!v)) .x q ≠ kb v := by decide
theorem m_x_val : ∀ v : Bool, latM (kb v) .x (kb (!v)) = .x := by decide
theorem m_x_val' : ∀ v : Bool, latM (kb (!v)) .x (kb v) = .x := by decide

theorem Rd.lo_le_hi (p : Rd) : p.lo ≤ p.hi := by have := p.ge 0; have := p.le 0; omega

/-! ## 1. Traces, hypotheses, spec -/

/-- **H_PIN_READ** for one latch bit. -/
def LutEq (pd pe pq : Rd) (d e q : Int → K3) : Prop :=
  ∀ t, 0 ≤ t → q t = latM (d (pd.σ t)) (e (pe.σ t)) (q (pq.σ t))

/-- **H_EN_TOKEN**. -/
def EnTok (A B C : Int) (e : Int → K3) : Prop :=
  (∀ x, A ≤ x → x < B → e x = .t) ∧ (∀ x, C ≤ x → e x = .f)

/-- **H_D_STABLE**. -/
def DStab (v : Bool) (Td Tn : Int) (d : Int → K3) : Prop :=
  ∀ x, Td ≤ x → x < Tn → d x = kb v

/-- The spec: from the enable's closing window on (as read), the output is
the token's value. -/
def Capt (v : Bool) (B : Int) (pe : Rd) (q : Int → K3) : Prop :=
  ∀ t, 0 ≤ t → B ≤ pe.σ t → q t = kb v

/-! ## 2. Sufficient -/

/-- **Read-level sufficient condition** (any read maps). -/
theorem capt_of_reads (v : Bool) (A B C Td Tn : Int) (pd pe pq : Rd) (d e q : Int → K3)
    (hq1 : 1 ≤ pq.lo) (hBC : B ≤ C)
    (hE : EnTok A B C e) (hD : DStab v Td Tn d) (hL : LutEq pd pe pq d e q)
    (R0 : ∀ t, 0 ≤ t → B ≤ pe.σ t → 0 ≤ pq.σ t)
    (RP : ∀ t, 0 ≤ t → B ≤ pe.σ t → A ≤ pe.σ (pq.σ t))
    (RS1 : ∀ t, 0 ≤ t → B ≤ pe.σ t → Td ≤ pd.σ (pq.σ t))
    (RS2 : ∀ t, 0 ≤ t → B ≤ pe.σ t → Td ≤ pd.σ t)
    (RH : ∀ u, 0 ≤ u → pe.σ u < C → pd.σ u < Tn) :
    Capt v B pe q := by
  intro t
  refine int_ind (fun t => 0 ≤ t → B ≤ pe.σ t → q t = kb v)
    (fun t ht h0 => absurd h0 (by omega)) ?_ t
  intro t ht ih _ hB
  have hfb : q (pq.σ t) = kb v := by
    have h0 := R0 t ht hB
    have hlt : pq.σ t < t := by have := pq.le t; omega
    by_cases hu : B ≤ pe.σ (pq.σ t)
    · exact ih _ hlt h0 hu
    · rw [hL _ h0, hE.1 _ (RP t ht hB) (by omega), m_t]
      exact hD _ (RS1 t ht hB) (RH _ h0 (by omega))
  rw [hL t ht, hfb]
  by_cases hc : pe.σ t < C
  · rw [hD _ (RS2 t ht hB) (RH t ht hc)]; exact m_same _ v
  · rw [hE.2 _ (by omega), m_f]

/-- **Sufficient, any read maps in their windows.** -/
theorem latch_pin_ok (v : Bool) (A B C Td Tn : Int) (pd pe pq : Rd) (d e q : Int → K3)
    (hq1 : 1 ≤ pq.lo) (hBC : B ≤ C) (H_T0 : 0 ≤ A + pe.lo)
    (H_EN_TOKEN : EnTok A B C e) (H_D_STABLE : DStab v Td Tn d) (H_PIN_READ : LutEq pd pe pq d e q)
    (H_SETUP_PULSE : A + pe.hi + pq.hi ≤ B + pe.lo)
    (H_SETUP_DATA : Td + pd.hi + pq.hi ≤ B + pe.lo)
    (H_HOLD : C + pe.hi ≤ Tn + pd.lo) :
    Capt v B pe q := by
  have e1 := Rd.lo_le_hi pe; have e2 := Rd.lo_le_hi pq; have e3 := Rd.lo_le_hi pd
  apply capt_of_reads v A B C Td Tn pd pe pq d e q hq1 hBC H_EN_TOKEN H_D_STABLE H_PIN_READ
  · intro t _ hB; have := pe.le t; have := pq.ge t; omega
  · intro t _ hB; have := pe.le t; have := pq.ge t; have := pe.ge (pq.σ t); omega
  · intro t _ hB; have := pe.le t; have := pq.ge t; have := pd.ge (pq.σ t); omega
  · intro t _ hB; have := pe.le t; have := pd.ge t; omega
  · intro u _ hu; have := pe.ge u; have := pd.le u; omega

/-- **Sufficient, fixed per-pin delays** (rise = fall on every arc): the
enable's delay cancels in setup_pulse. -/
theorem latch_sym_ok (v : Bool) (A B C Td Tn dd de dq : Int) (d e q : Int → K3)
    (hq1 : 1 ≤ dq) (hBC : B ≤ C) (H_T0 : 0 ≤ A + de)
    (H_EN_TOKEN : EnTok A B C e) (H_D_STABLE : DStab v Td Tn d)
    (H_PIN_READ : LutEq (Rd.const dd) (Rd.const de) (Rd.const dq) d e q)
    (H_SETUP_PULSE : A + dq ≤ B)
    (H_SETUP_DATA : Td + dd + dq ≤ B + de)
    (H_HOLD : C + de ≤ Tn + dd) :
    Capt v B (Rd.const de) q := by
  apply capt_of_reads v A B C Td Tn _ _ _ d e q hq1 hBC H_EN_TOKEN H_D_STABLE H_PIN_READ <;>
    (intros; simp only [Rd.const] at *; omega)

/-! ## 3. Necessity: witness traces -/

/-- Trace constructor: feedback delay `dq ≥ 1`, next-state `f`, power-up `q0`. -/
def runN (f : Int → K3 → K3) (q0 : K3) (dq : Nat) (hd : 0 < dq) : Nat → K3
  | n => f n (if _h : n < dq then q0 else runN f q0 dq hd (n - dq))
termination_by n => n
decreasing_by omega

def run (f : Int → K3 → K3) (q0 : K3) (dq : Nat) (hd : 0 < dq) (t : Int) : K3 :=
  if t < 0 then q0 else runN f q0 dq hd t.toNat

theorem run_neg (f : Int → K3 → K3) (q0 : K3) (dq : Nat) (hd : 0 < dq) (t : Int) (ht : t < 0) :
    run f q0 dq hd t = q0 := by simp [run, ht]

theorem run_eq (f : Int → K3 → K3) (q0 : K3) (dq : Nat) (hd : 0 < dq) (t : Int) (ht : 0 ≤ t) :
    run f q0 dq hd t = f t (run f q0 dq hd (t - dq)) := by
  unfold run
  rw [ite_eq_right (by omega), runN]
  have e : ((t.toNat : Nat) : Int) = t := Int.toNat_of_nonneg ht
  rw [e]
  congr 1
  by_cases h : t.toNat < dq
  · rw [dite_eq_left h, ite_eq_left (by omega)]
  · rw [dite_eq_right h, ite_eq_right (by omega)]
    congr 1; omega

/-- The latch next-state for given read maps of `d` and `en`. -/
def lf (pd pe : Rd) (d e : Int → K3) (t : Int) (qq : K3) : K3 := latM (d (pd.σ t)) (e (pe.σ t)) qq

theorem run_luteq (pd pe : Rd) (d e : Int → K3) (q0 : K3) (dq : Nat) (hd : 0 < dq) :
    LutEq pd pe (Rd.const dq) d e (run (lf pd pe d e) q0 dq hd) := by
  intro t ht; exact run_eq _ q0 dq hd t ht

/-- Adversarial data: `v` on `[Td, Tn)`, the other value elsewhere. -/
def dAdv (v : Bool) (Td Tn : Int) (x : Int) : K3 := if Td ≤ x ∧ x < Tn then kb v else kb (!v)

/-- Adversarial enable: 0 before `A`, 1 on `[A, B)`, X on `[B, C)`, 0 after. -/
def eAdv (A B C : Int) (x : Int) : K3 :=
  if x < A then .f else if x < B then .t else if x < C then .x else .f

theorem dAdv_stab (v : Bool) (Td Tn : Int) : DStab v Td Tn (dAdv v Td Tn) := by
  intro x h1 h2; simp [dAdv, h1, h2]
theorem dAdv_lo {v : Bool} {Td Tn x : Int} (h : x < Td) : dAdv v Td Tn x = kb (!v) := by
  simp only [dAdv]; rw [ite_eq_right (show ¬ (Td ≤ x ∧ x < Tn) by omega)]
theorem dAdv_hi {v : Bool} {Td Tn x : Int} (h : Tn ≤ x) : dAdv v Td Tn x = kb (!v) := by
  simp only [dAdv]; rw [ite_eq_right (show ¬ (Td ≤ x ∧ x < Tn) by omega)]
theorem dAdv_in {v : Bool} {Td Tn x : Int} (h1 : Td ≤ x) (h2 : x < Tn) : dAdv v Td Tn x = kb v := by
  simp [dAdv, h1, h2]

theorem eAdv_tok {A B C : Int} (h1 : A ≤ B) (h2 : B ≤ C) : EnTok A B C (eAdv A B C) := by
  refine ⟨fun x a b => ?_, fun x a => ?_⟩
  · simp [eAdv, show ¬ x < A by omega, b]
  · simp [eAdv, show ¬ x < A by omega, show ¬ x < B by omega, show ¬ x < C by omega]
theorem eAdv_lo {A B C x : Int} (h : x < A) : eAdv A B C x = .f := by simp [eAdv, h]
theorem eAdv_on {A B C x : Int} (h1 : A ≤ x) (h2 : x < B) : eAdv A B C x = .t := by
  simp [eAdv, show ¬ x < A by omega, h2]
theorem eAdv_win {A B C x : Int} (h0 : A ≤ B) (h1 : B ≤ x) (h2 : x < C) : eAdv A B C x = .x := by
  simp [eAdv, show ¬ x < A by omega, show ¬ x < B by omega, h2]
theorem eAdv_ne_t {A B C x : Int} (h0 : A ≤ B) (h1 : B ≤ x) : eAdv A B C x ≠ .t := by
  unfold eAdv
  rw [ite_eq_right (show ¬ x < A by omega), ite_eq_right (show ¬ x < B by omega)]
  by_cases h : x < C
  · rw [ite_eq_left h]; decide
  · rw [ite_eq_right h]; decide

/-- A two-phase read map (rise read at `hi`, fall read at `lo`): monotone,
inside `[t - hi, t - lo]`. -/
def Rd.two (K lo hi : Int) (h : lo ≤ hi) : Rd :=
  ⟨fun t => if t < K then t - hi else t - lo, lo, hi,
   fun t => by by_cases h' : t < K <;> simp [h'] <;> omega,
   fun t => by by_cases h' : t < K <;> simp [h'] <;> omega⟩

section Cases
variable (v : Bool) (A B C Td Tn : Int) (pd pe : Rd) (dq : Int) (q : Int → K3)

/-- While the enable reads 0 (before `A`), the output keeps its power-up value. -/
theorem low (K : Int) (hq1 : 1 ≤ dq)
    (hL : LutEq pd pe (Rd.const dq) (dAdv v Td Tn) (eAdv A B C) q)
    (hq0 : ∀ t, t < 0 → q t = kb (!v)) (hK : ∀ t, 0 ≤ t → t < K → pe.σ t < A) :
    ∀ t, t < K → q t = kb (!v) := by
  apply int_ind (fun t => t < K → q t = kb (!v)) (fun t ht _ => hq0 t ht)
  intro t ht ih hk
  rw [hL t ht, eAdv_lo (hK t ht hk), m_f]
  exact ih _ (by simp only [Rd.const]; omega) (by simp only [Rd.const]; omega)

/-- A wrong feedback value at the closing read: the spec fails. -/
theorem bad_fb (hAB : A ≤ B) (ts : Int) (h0 : 0 ≤ ts) (hB : B ≤ pe.σ ts)
    (hL : LutEq pd pe (Rd.const dq) (dAdv v Td Tn) (eAdv A B C) q)
    (hfb : q (ts - dq) = kb (!v)) : ¬ Capt v B pe q := by
  intro hc
  have := hc ts h0 hB
  rw [hL ts h0] at this
  have hq : q ((Rd.const dq).σ ts) = kb (!v) := hfb
  rw [hq] at this
  exact m_badq _ _ v (eAdv_ne_t (C := C) hAB hB) this

/-- Transparent read of a wrong datum gives a wrong output. -/
theorem transp_bad (u : Int) (hu : 0 ≤ u) (h1 : A ≤ pe.σ u) (h2 : pe.σ u < B)
    (hd : pd.σ u < Td ∨ Tn ≤ pd.σ u)
    (hL : LutEq pd pe (Rd.const dq) (dAdv v Td Tn) (eAdv A B C) q) : q u = kb (!v) := by
  rw [hL u hu, eAdv_on h1 h2, m_t]
  rcases hd with h | h
  · exact dAdv_lo h
  · exact dAdv_hi h

end Cases

/-- Existence of a real trace for given reads, with power-up value `!v`. -/
theorem mk_trace (v : Bool) (A B C Td Tn : Int) (pd pe : Rd) (dq : Nat) (hdq : 0 < dq)
    (hAB : A ≤ B) (hBC : B ≤ C)
    (P : (Int → K3) → Prop)
    (h : ∀ q, LutEq pd pe (Rd.const dq) (dAdv v Td Tn) (eAdv A B C) q →
      (∀ t, t < 0 → q t = kb (!v)) → P q) :
    ∃ d e q, DStab v Td Tn d ∧ EnTok A B C e ∧ LutEq pd pe (Rd.const dq) d e q ∧ P q := by
  let q := run (lf pd pe (dAdv v Td Tn) (eAdv A B C)) (kb (!v)) dq hdq
  have hL : LutEq pd pe (Rd.const dq) (dAdv v Td Tn) (eAdv A B C) q := run_luteq pd pe _ _ _ dq hdq
  exact ⟨_, _, q, dAdv_stab v Td Tn, eAdv_tok hAB hBC, hL,
    h q hL (fun t ht => run_neg _ _ dq hdq t ht)⟩

/-- setup_pulse violated (box form): the enable's rise read slow, its fall
read fast. -/
theorem need_pulse_two (v : Bool) (A B C Td Tn Dhi Elo Ehi : Int) (dq : Nat) (hdq : 0 < dq)
    (hE : Elo ≤ Ehi) (hAB : A ≤ B) (hBC : B ≤ C) (H_T0 : 0 ≤ A + Elo)
    (hbad : B + Elo < A + Ehi + dq) :
    ∃ d e q, DStab v Td Tn d ∧ EnTok A B C e ∧
      LutEq (Rd.const Dhi) (Rd.two (B + Elo) Elo Ehi hE) (Rd.const dq) d e q ∧
      ¬ Capt v B (Rd.two (B + Elo) Elo Ehi hE) q := by
  apply mk_trace v A B C Td Tn _ _ dq hdq hAB hBC
  intro q hL hq0
  have hlow := low v A B C Td Tn _ _ dq q (min (A + Ehi) (B + Elo)) (by omega) hL hq0 (by
    intro t _ ht
    show (if t < B + Elo then t - Ehi else t - Elo) < A
    rw [ite_eq_left (by omega)]; omega)
  apply bad_fb v A B C Td Tn _ _ dq q hAB (B + Elo) (by omega) (by
    show B ≤ (if B + Elo < B + Elo then B + Elo - Ehi else B + Elo - Elo)
    rw [ite_eq_right (by omega)]; omega) hL
  exact hlow _ (by omega)

/-- setup_pulse violated at fixed delays (`A + dq > B`). -/
theorem need_pulse_sym (v : Bool) (A B C Td Tn dd de : Int) (dq : Nat) (hdq : 0 < dq)
    (hAB : A ≤ B) (hBC : B ≤ C) (H_T0 : 0 ≤ A + de) (hbad : B < A + dq) :
    ∃ d e q, DStab v Td Tn d ∧ EnTok A B C e ∧
      LutEq (Rd.const dd) (Rd.const de) (Rd.const dq) d e q ∧ ¬ Capt v B (Rd.const de) q := by
  apply mk_trace v A B C Td Tn _ _ dq hdq hAB hBC
  intro q hL hq0
  have hlow := low v A B C Td Tn _ _ dq q (A + de) (by omega) hL hq0 (by
    intro t _ ht; simp only [Rd.const]; omega)
  apply bad_fb v A B C Td Tn _ _ dq q hAB (B + de) (by omega) (by simp only [Rd.const]; omega) hL
  exact hlow _ (by omega)

/-- setup_data violated (setup_pulse met at the fixed delays). -/
theorem need_data (v : Bool) (A B C Td Tn dd de : Int) (dq : Nat) (hdq : 0 < dq)
    (hAB : A ≤ B) (hBC : B ≤ C) (H_T0 : 0 ≤ A + de) (hP : A + dq ≤ B)
    (hbad : B + de < Td + dd + dq) :
    ∃ d e q, DStab v Td Tn d ∧ EnTok A B C e ∧
      LutEq (Rd.const dd) (Rd.const de) (Rd.const dq) d e q ∧ ¬ Capt v B (Rd.const de) q := by
  apply mk_trace v A B C Td Tn _ _ dq hdq hAB hBC
  intro q hL _
  apply bad_fb v A B C Td Tn _ _ dq q hAB (B + de) (by omega) (by simp only [Rd.const]; omega) hL
  exact transp_bad v A B C Td Tn _ _ dq q _ (by omega) (by simp only [Rd.const]; omega)
    (by simp only [Rd.const]; omega) (Or.inl (by simp only [Rd.const]; omega)) hL

/-- hold violated (setup_pulse met at the fixed delays). With an X window
(`B < C`) an X is captured at once; with an instantaneous select (`B = C`)
the new datum is captured and fed back. -/
theorem need_hold (v : Bool) (A B C Td Tn dd de : Int) (dq : Nat) (hdq : 0 < dq)
    (hAB : A ≤ B) (hBC : B ≤ C) (H_T0 : 0 ≤ A + de) (hP : A + dq ≤ B)
    (hbad : Tn + dd < C + de) :
    ∃ d e q, DStab v Td Tn d ∧ EnTok A B C e ∧
      LutEq (Rd.const dd) (Rd.const de) (Rd.const dq) d e q ∧ ¬ Capt v B (Rd.const de) q := by
  apply mk_trace v A B C Td Tn _ _ dq hdq hAB hBC
  intro q hL _
  by_cases hw : B < C
  · intro hc
    have h1 := hc (C - 1 + de) (by omega) (by simp only [Rd.const]; omega)
    rw [hL _ (by omega)] at h1
    simp only [Rd.const] at h1
    rw [eAdv_win hAB (by omega) (by omega), dAdv_hi (by omega)] at h1
    exact m_badd _ v h1
  · apply bad_fb v A B C Td Tn _ _ dq q hAB (B - 1 + de + dq) (by omega)
      (by simp only [Rd.const]; omega) hL
    have e1 : B - 1 + de + (dq : Int) - dq = B - 1 + de := by omega
    rw [e1]
    exact transp_bad v A B C Td Tn _ _ dq q _ (by omega) (by simp only [Rd.const]; omega)
      (by simp only [Rd.const]; omega) (Or.inr (by simp only [Rd.const]; omega)) hL

/-! ## 4. Exact -/

/-- Universally safe over a box of per-pin read maps. -/
def SafeBox (v : Bool) (A B C Td Tn Dlo Dhi Elo Ehi Qlo Qhi : Int) : Prop :=
  ∀ pd pe pq : Rd, Dlo ≤ pd.lo → pd.hi ≤ Dhi → Elo ≤ pe.lo → pe.hi ≤ Ehi →
    Qlo ≤ pq.lo → pq.hi ≤ Qhi →
    ∀ d e q, DStab v Td Tn d → EnTok A B C e → LutEq pd pe pq d e q → Capt v B pe q

/-- **Headline: exact over the per-pin delay box.** -/
theorem box_exact (v : Bool) (A B C Td Tn Dlo Dhi Elo Ehi Qlo Qhi : Int)
    (hD : Dlo ≤ Dhi) (hE : Elo ≤ Ehi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (hAB : A ≤ B) (hBC : B ≤ C) (H_T0 : 0 ≤ A + Elo) :
    SafeBox v A B C Td Tn Dlo Dhi Elo Ehi Qlo Qhi ↔
      (A + Ehi + Qhi ≤ B + Elo ∧ Td + Dhi + Qhi ≤ B + Elo ∧ C + Ehi ≤ Tn + Dlo) := by
  have hq0 : 0 < Qhi.toNat := by omega
  have hqe : ((Qhi.toNat : Nat) : Int) = Qhi := by omega
  constructor
  · intro h
    apply Classical.byContradiction; intro hn
    by_cases hP : A + Ehi + Qhi ≤ B + Elo
    · by_cases hS : Td + Dhi + Qhi ≤ B + Elo
      · obtain ⟨d, e, q, h1, h2, h3, h4⟩ :=
          need_hold v A B C Td Tn Dlo Ehi Qhi.toNat hq0 hAB hBC (by omega) (by omega) (by omega)
        exact h4 (h _ _ _ (by simp only [Rd.const]; omega) (by simp only [Rd.const]; omega)
          (by simp only [Rd.const]; omega) (by simp only [Rd.const]; omega) (by simp only [Rd.const]; omega)
          (by simp only [Rd.const]; omega) d e q h1 h2 h3)
      · obtain ⟨d, e, q, h1, h2, h3, h4⟩ :=
          need_data v A B C Td Tn Dhi Elo Qhi.toNat hq0 hAB hBC H_T0 (by omega) (by omega)
        exact h4 (h _ _ _ (by simp only [Rd.const]; omega) (by simp only [Rd.const]; omega)
          (by simp only [Rd.const]; omega) (by simp only [Rd.const]; omega) (by simp only [Rd.const]; omega)
          (by simp only [Rd.const]; omega) d e q h1 h2 h3)
    · obtain ⟨d, e, q, h1, h2, h3, h4⟩ :=
        need_pulse_two v A B C Td Tn Dhi Elo Ehi Qhi.toNat hq0 hE hAB hBC H_T0 (by omega)
      exact h4 (h _ _ _ (by simp only [Rd.const]; omega) (by simp only [Rd.const]; omega)
        (by simp only [Rd.two]; omega) (by simp only [Rd.two]; omega) (by simp only [Rd.const]; omega)
        (by simp only [Rd.const]; omega) d e q h1 h2 h3)
  · rintro ⟨h1, h2, h3⟩ pd pe pq a1 a2 a3 a4 a5 a6 d e q hd he hl
    have := Rd.lo_le_hi pe; have := Rd.lo_le_hi pq; have := Rd.lo_le_hi pd
    exact latch_pin_ok v A B C Td Tn pd pe pq d e q (by omega) hBC (by omega) he hd hl
      (by omega) (by omega) (by omega)

/-- Universally safe over FIXED per-pin delays, each anywhere in its box
(H_RF_SYM: an arc has one delay for both edges). -/
def SafeSym (v : Bool) (A B C Td Tn Dlo Dhi Elo Ehi Qlo Qhi : Int) : Prop :=
  ∀ dd de dq : Int, Dlo ≤ dd → dd ≤ Dhi → Elo ≤ de → de ≤ Ehi → Qlo ≤ dq → dq ≤ Qhi →
    ∀ d e q, DStab v Td Tn d → EnTok A B C e →
      LutEq (Rd.const dd) (Rd.const de) (Rd.const dq) d e q → Capt v B (Rd.const de) q

/-- **Exact, rise = fall per arc**: setup_pulse loses the enable's spread. -/
theorem sym_exact (v : Bool) (A B C Td Tn Dlo Dhi Elo Ehi Qlo Qhi : Int)
    (hD : Dlo ≤ Dhi) (hE : Elo ≤ Ehi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (hAB : A ≤ B) (hBC : B ≤ C) (H_T0 : 0 ≤ A + Elo) :
    SafeSym v A B C Td Tn Dlo Dhi Elo Ehi Qlo Qhi ↔
      (A + Qhi ≤ B ∧ Td + Dhi + Qhi ≤ B + Elo ∧ C + Ehi ≤ Tn + Dlo) := by
  have hq0 : 0 < Qhi.toNat := by omega
  have hqe : ((Qhi.toNat : Nat) : Int) = Qhi := by omega
  constructor
  · intro h
    apply Classical.byContradiction; intro hn
    by_cases hP : A + Qhi ≤ B
    · by_cases hS : Td + Dhi + Qhi ≤ B + Elo
      · obtain ⟨d, e, q, h1, h2, h3, h4⟩ :=
          need_hold v A B C Td Tn Dlo Ehi Qhi.toNat hq0 hAB hBC (by omega) (by omega) (by omega)
        exact h4 (h _ _ _ (Int.le_refl _) hD hE (Int.le_refl _) (by omega) (by omega) d e q h1 h2 h3)
      · obtain ⟨d, e, q, h1, h2, h3, h4⟩ :=
          need_data v A B C Td Tn Dhi Elo Qhi.toNat hq0 hAB hBC H_T0 (by omega) (by omega)
        exact h4 (h _ _ _ hD (Int.le_refl _) (Int.le_refl _) hE (by omega) (by omega) d e q h1 h2 h3)
    · obtain ⟨d, e, q, h1, h2, h3, h4⟩ :=
        need_pulse_sym v A B C Td Tn Dhi Elo Qhi.toNat hq0 hAB hBC H_T0 (by omega)
      exact h4 (h _ _ _ hD (Int.le_refl _) (Int.le_refl _) hE (by omega) (by omega) d e q h1 h2 h3)
  · rintro ⟨h1, h2, h3⟩ dd de dq a1 a2 a3 a4 a5 a6 d e q hd he hl
    exact latch_sym_ok v A B C Td Tn dd de dq d e q (by omega) hBC (by omega) he hd hl
      (by omega) (by omega) (by omega)

/-- **Binary-edge form.** `Ton`, `Toff`: the enable's binary edges (definite
1 from `Ton`; X on `[Toff - we, Toff)`, definite 0 from `Toff`); `Tnew`: the
next datum's binary edge, its X window `[Tnew - wd, Tnew)`. -/
theorem box_exact_edges (v : Bool) (Ton Toff we Td Tnew wd Dlo Dhi Elo Ehi Qlo Qhi : Int)
    (hD : Dlo ≤ Dhi) (hE : Elo ≤ Ehi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (hwe : 0 ≤ we) (hAB : Ton ≤ Toff - we) (H_T0 : 0 ≤ Ton + Elo) :
    SafeBox v Ton (Toff - we) Toff Td (Tnew - wd) Dlo Dhi Elo Ehi Qlo Qhi ↔
      (Ton + Ehi + Qhi + we ≤ Toff + Elo ∧ Td + Dhi + Qhi + we ≤ Toff + Elo ∧
        Toff + Ehi + wd ≤ Tnew + Dlo) := by
  rw [box_exact v _ _ _ _ _ _ _ _ _ _ _ hD hE hQ1 hQ hAB (by omega) H_T0]; omega

/-- **Strictness** (H_MUX_KLEENE, one tick of X on each moving select):
setup_pulse, setup_data AND hold are all strict. -/
theorem strict_edges (v : Bool) (Ton Toff Td Tnew Dlo Dhi Elo Ehi Qlo Qhi : Int)
    (hD : Dlo ≤ Dhi) (hE : Elo ≤ Ehi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (hAB : Ton ≤ Toff - 1) (H_T0 : 0 ≤ Ton + Elo) :
    SafeBox v Ton (Toff - 1) Toff Td (Tnew - 1) Dlo Dhi Elo Ehi Qlo Qhi ↔
      (Ton + Ehi + Qhi < Toff + Elo ∧ Td + Dhi + Qhi < Toff + Elo ∧ Toff + Ehi < Tnew + Dlo) := by
  rw [box_exact_edges v _ _ 1 _ _ 1 _ _ _ _ _ _ hD hE hQ1 hQ (by omega) hAB H_T0]; omega

/-- Instantaneous selects (`we = wd = 0`): all three are `≤`. -/
theorem atomic_edges (v : Bool) (Ton Toff Td Tnew Dlo Dhi Elo Ehi Qlo Qhi : Int)
    (hD : Dlo ≤ Dhi) (hE : Elo ≤ Ehi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (hAB : Ton ≤ Toff) (H_T0 : 0 ≤ Ton + Elo) :
    SafeBox v Ton (Toff - 0) Toff Td (Tnew - 0) Dlo Dhi Elo Ehi Qlo Qhi ↔
      (Ton + Ehi + Qhi ≤ Toff + Elo ∧ Td + Dhi + Qhi ≤ Toff + Elo ∧ Toff + Ehi ≤ Tnew + Dlo) := by
  rw [box_exact_edges v _ _ 0 _ _ 0 _ _ _ _ _ _ hD hE hQ1 hQ (by omega) (by omega) H_T0]; omega

/-! ## 5. The real INITs: odd bit, pair O5, pair O6 -/

/-- Odd bit, H_PIN_READ on the real LUT6 INIT. -/
def LutEqOdd (pd pe pq : Rd) (d e q : Int → K3) : Prop :=
  ∀ t, 0 ≤ t → q t = lutK Latch.ODD [d (pd.σ t), e (pe.σ t), q (pq.σ t), .f, .f, .f]

/-- Pair O5 (bit i): pins I0 = d, I1 = en, I2 = q, plus the neighbour's
I3 = d[i+1], I4 = q[i+1] through their own read maps. -/
def LutEqO5 (pd pe pq pdj pqj : Rd) (d e q dj qj : Int → K3) : Prop :=
  ∀ t, 0 ≤ t → q t = o5K Latch.PAIR [d (pd.σ t), e (pe.σ t), q (pq.σ t), dj (pdj.σ t), qj (pqj.σ t), .t]

/-- Pair O6 (bit i+1): pins I3 = d, I1 = en, I4 = q, plus the neighbour's
I0 = d[i], I2 = q[i]. -/
def LutEqO6 (pdi pqi pd pe pq : Rd) (di qi d e q : Int → K3) : Prop :=
  ∀ t, 0 ≤ t → q t = o6K Latch.PAIR [di (pdi.σ t), e (pe.σ t), qi (pqi.σ t), d (pd.σ t), q (pq.σ t), .t]

theorem odd_iff (pd pe pq : Rd) (d e q : Int → K3) : LutEqOdd pd pe pq d e q ↔ LutEq pd pe pq d e q := by
  simp only [LutEqOdd, LutEq, odd_eq]
theorem o5_iff (pd pe pq pdj pqj : Rd) (d e q dj qj : Int → K3) :
    LutEqO5 pd pe pq pdj pqj d e q dj qj ↔ LutEq pd pe pq d e q := by
  simp only [LutEqO5, LutEq, o5_eq]
theorem o6_iff (pdi pqi pd pe pq : Rd) (di qi d e q : Int → K3) :
    LutEqO6 pdi pqi pd pe pq di qi d e q ↔ LutEq pd pe pq d e q := by
  simp only [LutEqO6, LutEq, o6_eq]

/-- **Odd bit, exact over the box, real INIT.** -/
theorem odd_box_exact (v : Bool) (A B C Td Tn Dlo Dhi Elo Ehi Qlo Qhi : Int)
    (hD : Dlo ≤ Dhi) (hE : Elo ≤ Ehi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (hAB : A ≤ B) (hBC : B ≤ C) (H_T0 : 0 ≤ A + Elo) :
    (∀ pd pe pq : Rd, Dlo ≤ pd.lo → pd.hi ≤ Dhi → Elo ≤ pe.lo → pe.hi ≤ Ehi →
      Qlo ≤ pq.lo → pq.hi ≤ Qhi →
      ∀ d e q, DStab v Td Tn d → EnTok A B C e → LutEqOdd pd pe pq d e q → Capt v B pe q) ↔
      (A + Ehi + Qhi ≤ B + Elo ∧ Td + Dhi + Qhi ≤ B + Elo ∧ C + Ehi ≤ Tn + Dlo) := by
  rw [← box_exact v A B C Td Tn Dlo Dhi Elo Ehi Qlo Qhi hD hE hQ1 hQ hAB hBC H_T0]
  simp only [SafeBox, odd_iff]

/-- **Pair O5 (bit i), exact over the box, real INIT**, for every neighbour
trace and read map (the neighbour bit's pins never matter). -/
theorem o5_box_exact (v : Bool) (A B C Td Tn Dlo Dhi Elo Ehi Qlo Qhi : Int)
    (hD : Dlo ≤ Dhi) (hE : Elo ≤ Ehi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (hAB : A ≤ B) (hBC : B ≤ C) (H_T0 : 0 ≤ A + Elo) :
    (∀ pd pe pq pdj pqj : Rd, Dlo ≤ pd.lo → pd.hi ≤ Dhi → Elo ≤ pe.lo → pe.hi ≤ Ehi →
      Qlo ≤ pq.lo → pq.hi ≤ Qhi →
      ∀ d e q dj qj, DStab v Td Tn d → EnTok A B C e → LutEqO5 pd pe pq pdj pqj d e q dj qj →
        Capt v B pe q) ↔
      (A + Ehi + Qhi ≤ B + Elo ∧ Td + Dhi + Qhi ≤ B + Elo ∧ C + Ehi ≤ Tn + Dlo) := by
  rw [← box_exact v A B C Td Tn Dlo Dhi Elo Ehi Qlo Qhi hD hE hQ1 hQ hAB hBC H_T0]
  constructor
  · intro h pd pe pq a1 a2 a3 a4 a5 a6 d e q hd he hl
    exact h pd pe pq (Rd.const 0) (Rd.const 0) a1 a2 a3 a4 a5 a6 d e q (fun _ => .f) (fun _ => .f)
      hd he ((o5_iff _ _ _ _ _ _ _ _ _ _).mpr hl)
  · intro h pd pe pq _ _ a1 a2 a3 a4 a5 a6 d e q _ _ hd he hl
    exact h pd pe pq a1 a2 a3 a4 a5 a6 d e q hd he ((o5_iff _ _ _ _ _ _ _ _ _ _).mp hl)

/-- **Pair O6 (bit i+1), exact over the box, real INIT.** -/
theorem o6_box_exact (v : Bool) (A B C Td Tn Dlo Dhi Elo Ehi Qlo Qhi : Int)
    (hD : Dlo ≤ Dhi) (hE : Elo ≤ Ehi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (hAB : A ≤ B) (hBC : B ≤ C) (H_T0 : 0 ≤ A + Elo) :
    (∀ pdi pqi pd pe pq : Rd, Dlo ≤ pd.lo → pd.hi ≤ Dhi → Elo ≤ pe.lo → pe.hi ≤ Ehi →
      Qlo ≤ pq.lo → pq.hi ≤ Qhi →
      ∀ di qi d e q, DStab v Td Tn d → EnTok A B C e → LutEqO6 pdi pqi pd pe pq di qi d e q →
        Capt v B pe q) ↔
      (A + Ehi + Qhi ≤ B + Elo ∧ Td + Dhi + Qhi ≤ B + Elo ∧ C + Ehi ≤ Tn + Dlo) := by
  rw [← box_exact v A B C Td Tn Dlo Dhi Elo Ehi Qlo Qhi hD hE hQ1 hQ hAB hBC H_T0]
  constructor
  · intro h pd pe pq a1 a2 a3 a4 a5 a6 d e q hd he hl
    exact h (Rd.const 0) (Rd.const 0) pd pe pq a1 a2 a3 a4 a5 a6 (fun _ => .f) (fun _ => .f) d e q
      hd he ((o6_iff _ _ _ _ _ _ _ _ _ _).mpr hl)
  · intro h _ _ pd pe pq a1 a2 a3 a4 a5 a6 _ _ d e q hd he hl
    exact h pd pe pq a1 a2 a3 a4 a5 a6 d e q hd he ((o6_iff _ _ _ _ _ _ _ _ _ _).mp hl)

/-- The three bits under H_RF_SYM (fixed per-pin delays), real INITs. -/
theorem cells_sym_exact (v : Bool) (A B C Td Tn Dlo Dhi Elo Ehi Qlo Qhi : Int)
    (hD : Dlo ≤ Dhi) (hE : Elo ≤ Ehi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (hAB : A ≤ B) (hBC : B ≤ C) (H_T0 : 0 ≤ A + Elo) :
    ((∀ dd de dq : Int, Dlo ≤ dd → dd ≤ Dhi → Elo ≤ de → de ≤ Ehi → Qlo ≤ dq → dq ≤ Qhi →
      ∀ d e q, DStab v Td Tn d → EnTok A B C e →
        LutEqOdd (Rd.const dd) (Rd.const de) (Rd.const dq) d e q → Capt v B (Rd.const de) q) ↔
      (A + Qhi ≤ B ∧ Td + Dhi + Qhi ≤ B + Elo ∧ C + Ehi ≤ Tn + Dlo)) ∧
    (∀ pdj pqj : Rd, ∀ dj qj : Int → K3,
      (∀ dd de dq : Int, Dlo ≤ dd → dd ≤ Dhi → Elo ≤ de → de ≤ Ehi → Qlo ≤ dq → dq ≤ Qhi →
      ∀ d e q, DStab v Td Tn d → EnTok A B C e →
        LutEqO5 (Rd.const dd) (Rd.const de) (Rd.const dq) pdj pqj d e q dj qj →
          Capt v B (Rd.const de) q) ↔
      (A + Qhi ≤ B ∧ Td + Dhi + Qhi ≤ B + Elo ∧ C + Ehi ≤ Tn + Dlo)) ∧
    (∀ pdi pqi : Rd, ∀ di qi : Int → K3,
      (∀ dd de dq : Int, Dlo ≤ dd → dd ≤ Dhi → Elo ≤ de → de ≤ Ehi → Qlo ≤ dq → dq ≤ Qhi →
      ∀ d e q, DStab v Td Tn d → EnTok A B C e →
        LutEqO6 pdi pqi (Rd.const dd) (Rd.const de) (Rd.const dq) di qi d e q →
          Capt v B (Rd.const de) q) ↔
      (A + Qhi ≤ B ∧ Td + Dhi + Qhi ≤ B + Elo ∧ C + Ehi ≤ Tn + Dlo)) := by
  have hs := sym_exact v A B C Td Tn Dlo Dhi Elo Ehi Qlo Qhi hD hE hQ1 hQ hAB hBC H_T0
  simp only [SafeSym] at hs
  refine ⟨?_, fun _ _ _ _ => ?_, fun _ _ _ _ => ?_⟩ <;> rw [← hs] <;>
    simp only [odd_iff, o5_iff, o6_iff]

/-! ## 6. Counter-traces, 1 ps past each boundary (concrete ps, EVERY trace)

Box (illustrative, ps): data pin `[300, 700]`, enable pin `[400, 800]`,
feedback pin `[300, 900]`. Token `v = 1`: data definite 1 on `[1000, 3801)`,
enable definite 1 on `[2000, B)`, X on `[B, B + 1)`, 0 after. The boundaries:
setup_pulse `2000 + 800 + 900 ≤ B + 400` (B ≥ 3300), setup_data
`1000 + 700 + 900 ≤ B + 400`, hold `B + 1 + 800 ≤ 3801 + 300`. At `B = 3300`
all three hold (pulse and hold with equality). Each counter-trace moves one
boundary by 1 ps; power-up value 0. -/

/-- setup_pulse short by 1 ps (`B = 3299`): enable rise read at 800 ps, fall
at 400 ps, feedback 900 ps. At 3699 the enable reads X (its closing window)
and the latch outputs X. -/
theorem ct_pulse_x (q : Int → K3)
    (hL : LutEq (Rd.const 700) (Rd.two 3699 400 800 (by decide)) (Rd.const 900)
      (dAdv true 1000 3801) (eAdv 2000 3299 3300) q)
    (hq0 : ∀ t, t < 0 → q t = kb false) :
    (Rd.two 3699 400 800 (by decide)).σ 3699 = 3299 ∧ q 3699 = .x := by
  have hlow := low true 2000 3299 3300 1000 3801 _ _ 900 q 2800 (by decide) hL hq0 (by
    intro t _ ht; show (if t < 3699 then t - 800 else t - 400) < 2000
    rw [ite_eq_left (by omega)]; omega)
  refine ⟨by decide, ?_⟩
  rw [hL 3699 (by decide)]
  have e1 : (Rd.const 900).σ 3699 = 2799 := by decide
  rw [e1, hlow 2799 (by decide)]
  decide

/-- setup_data short by 1 ps (data settles at 2101, `B = 3300`): reads
fixed at the box corners of the witness. The latch outputs X at 3700. -/
theorem ct_data_x (q : Int → K3)
    (hL : LutEq (Rd.const 700) (Rd.const 400) (Rd.const 900)
      (dAdv true 2101 3801) (eAdv 2000 3300 3301) q) :
    q 3700 = .x := by
  have h1 : q 2800 = kb false :=
    transp_bad true 2000 3300 3301 2101 3801 _ _ 900 q 2800 (by decide) (by decide) (by decide)
      (Or.inl (by decide)) hL
  rw [hL 3700 (by decide)]
  have e1 : (Rd.const 900).σ 3700 = 2800 := by decide
  rw [e1, h1]
  decide

/-- hold short by 1 ps (next datum's X window starts at 3800): enable read
at 800 ps, data at 300 ps. At 4100 the enable reads X and the data reads
the next datum: the latch outputs X. -/
theorem ct_hold_x (q : Int → K3)
    (hL : LutEq (Rd.const 300) (Rd.const 800) (Rd.const 900)
      (dAdv true 1000 3800) (eAdv 2000 3300 3301) q) :
    q 4100 = .x := by
  have h1 : q 3200 = kb true := by
    rw [hL 3200 (by decide)]
    have he : eAdv 2000 3300 3301 ((Rd.const 800).σ 3200) = .t := by decide
    rw [he, m_t]; decide
  rw [hL 4100 (by decide)]
  have e1 : (Rd.const 900).σ 4100 = 3200 := by decide
  rw [e1, h1]
  decide

/-- Instantaneous enable select (`C = B`, no X window): setup_pulse short by
1 ps captures the WRONG value 0 (and keeps it: the enable reads 0). -/
theorem ct_pulse_wrong (q : Int → K3)
    (hL : LutEq (Rd.const 700) (Rd.two 3699 400 800 (by decide)) (Rd.const 900)
      (dAdv true 1000 3801) (eAdv 2000 3299 3299) q)
    (hq0 : ∀ t, t < 0 → q t = kb false) :
    q 3699 = kb false := by
  have hlow := low true 2000 3299 3299 1000 3801 _ _ 900 q 2800 (by decide) hL hq0 (by
    intro t _ ht; show (if t < 3699 then t - 800 else t - 400) < 2000
    rw [ite_eq_left (by omega)]; omega)
  rw [hL 3699 (by decide)]
  have e1 : (Rd.const 900).σ 3699 = 2799 := by decide
  rw [e1, hlow 2799 (by decide)]
  decide

/-- Instantaneous select, setup_data short by 1 ps: wrong value 0. -/
theorem ct_data_wrong (q : Int → K3)
    (hL : LutEq (Rd.const 700) (Rd.const 400) (Rd.const 900)
      (dAdv true 2101 3801) (eAdv 2000 3300 3300) q) :
    q 3700 = kb false := by
  have h1 : q 2800 = kb false :=
    transp_bad true 2000 3300 3300 2101 3801 _ _ 900 q 2800 (by decide) (by decide) (by decide)
      (Or.inl (by decide)) hL
  rw [hL 3700 (by decide)]
  have e1 : (Rd.const 900).σ 3700 = 2800 := by decide
  rw [e1, h1]
  decide

/-- Instantaneous select, hold short by 1 ps (`B = C = 3300`, next datum
from 3799: `3300 + 800 = 3799 + 300 + 1`): the last transparent instant
(4099, enable read 3299) takes the new datum 0, and the feedback carries it
to 4999 (enable read 0, spec requires 1). -/
theorem ct_hold_wrong (q : Int → K3)
    (hL : LutEq (Rd.const 300) (Rd.const 800) (Rd.const 900)
      (dAdv true 1000 3799) (eAdv 2000 3300 3300) q) :
    q 4999 = kb false := by
  have h1 : q 4099 = kb false :=
    transp_bad true 2000 3300 3300 1000 3799 _ _ 900 q 4099 (by decide) (by decide) (by decide)
      (Or.inr (by decide)) hL
  rw [hL 4999 (by decide)]
  have e1 : (Rd.const 900).σ 4999 = 4099 := by decide
  rw [e1, h1]
  decide

/-- The six counter-trace setups violate exactly one boundary by 1 ps. -/
theorem ct_numbers :
    -- pulse: B = 3299
    ¬ ((2000 : Int) + 800 + 900 ≤ 3299 + 400) ∧ (1000 : Int) + 700 + 900 ≤ 3299 + 400 ∧
      (3300 : Int) + 800 ≤ 3801 + 300 ∧
    -- data: Td = 2101
    (2000 : Int) + 800 + 900 ≤ 3300 + 400 ∧ ¬ ((2101 : Int) + 700 + 900 ≤ 3300 + 400) ∧
      (3301 : Int) + 800 ≤ 3801 + 300 ∧
    -- hold (X window): Tn = 3800
    ¬ ((3301 : Int) + 800 ≤ 3800 + 300) ∧
    -- hold (no window): Tn = 3799
    ¬ ((3300 : Int) + 800 ≤ 3799 + 300) := by decide

/-! ## 7. Non-vacuity -/

/-- A run at the boundary (`B = 3300`, `C = 3301`, data on `[1000, 3801)`,
reads 500 / 600 / 700 ps inside the box), power-up 0. -/
def wq : Int → K3 :=
  run (lf (Rd.const 500) (Rd.const 600) (dAdv true 1000 3801) (eAdv 2000 3300 3301)) (kb false) 700
    (by decide)

theorem witness_hyps :
    DStab true 1000 3801 (dAdv true 1000 3801) ∧ EnTok 2000 3300 3301 (eAdv 2000 3300 3301) ∧
    LutEq (Rd.const 500) (Rd.const 600) (Rd.const (700 : Nat)) (dAdv true 1000 3801)
      (eAdv 2000 3300 3301) wq ∧
    (2000 : Int) + 800 + 900 ≤ 3300 + 400 ∧ (1000 : Int) + 700 + 900 ≤ 3300 + 400 ∧
      (3301 : Int) + 800 ≤ 3801 + 300 :=
  ⟨dAdv_stab _ _ _, eAdv_tok (by decide) (by decide), run_luteq _ _ _ _ _ 700 (by decide),
   by decide, by decide, by decide⟩

/-- In that run the latch really writes: 0 at time 0 (power-up value held,
the enable reads 0), 1 at every instant from the enable's closing read on
(by `box_exact`), and that set is not empty (4000 reads 3400 ≥ B). -/
theorem witness_run : wq 0 = kb false ∧ Capt true 3300 (Rd.const 600) wq ∧
    3300 ≤ (Rd.const 600).σ 4000 := by
  obtain ⟨hd, he, hl, _, _, _⟩ := witness_hyps
  refine ⟨?_, ?_, by decide⟩
  · unfold wq; rw [run_eq _ _ _ _ 0 (by decide), run_neg _ _ _ _ _ (by decide)]; decide
  · exact (box_exact true 2000 3300 3301 1000 3801 300 700 400 800 300 900 (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide) (by decide)).mpr
      ⟨by decide, by decide, by decide⟩ _ _ _ (by decide) (by decide)
      (by decide) (by decide) (by decide) (by decide)
      _ _ _ hd he hl

end Formal.Cells.LibGapLatch
