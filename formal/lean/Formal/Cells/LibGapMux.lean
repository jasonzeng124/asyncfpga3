import Formal.Cells.LibGapSteer

/-!
# LibGapMux: `bd_mux`'s select timing at the joins, per pin, sufficient AND necessary

Probe Bmx (shard B, Phase 2 library gap, follow-up of `LibGapSteer`).
`bd_mux` (`cells/rtl/bd_mux.v`, 21 instances in gcd_hw, every loop header)
gates its select `s` in the two join LUTs, which feed back to themselves:

    LUT6 #(.INIT(64'h0000_AE08_0000_AE08)) uj0 (.I0(x_req), .I1(ctl_req),
          .I2(s), .I3(j0), .I4(rst), .I5(1'b0), .O(j0));   // j0 = C(x_req, ctl_req.~s)
    LUT6 #(.INIT(64'h0000_EA80_0000_EA80)) uj1 (.I0(y_req), .I1(ctl_req),
          .I2(s), .I3(j1), .I4(rst), .I5(1'b0), .O(j1));   // j1 = C(y_req, ctl_req.s)

Join `b` (`b = false`: uj0, fires for `s = 0`; `b = true`: uj1, fires for
`s = 1`) is evaluated from the REAL INITs (`LibCtlMergeMux.j0B/j1B`); `jB_eq`
proves `jB b r c s q = C(r, c && (s == b))` with feedback `q`.

## Model (named hypotheses)

* **H_PIN_READ** (`LutEq`, per pin, with the FEEDBACK pin): for `t ≥ 0` the
  join output is the INIT of `r` (I0: x_req / y_req) read at `pr.σ t`,
  `ctl_req` (I1) at `pc.σ t`, `s` (I2) at `ps.σ t` and its OWN output (I3) at
  `pq.σ t`, each read map in its own window `[t - hi, t - lo]` (wire + site pin
  + that pin's LUT arc to O6; `Rd` of `LibGapSteer`, not necessarily monotone).
  `rst` (I4) reads 0 from time 0 on (its timing is the `reset_first` row).
* **H_RESET** (`Rest`): the join is 0 before time 0 (reset held).
* **H_CTL_PULSE**: one control token: `ctl_req` at its driver is high exactly
  on `[Cr, Cf)`.
* **H_S_STABLE** (env): `s` at its driver equals the token's value `v` on
  `[S0, S1)`; ARBITRARY outside it.
* The client request `r` is ARBITRARY (any Boolean trace). The necessity
  witnesses use only two physical shapes: a waiting token (`r` high
  throughout: the other input's token in a loop header, or this input's own
  early request) and a request that falls while `ctl_req` is still high
  (allowed: y_req↓ and ctl_req↓ both follow z_ack↑, in either order).

## Spec (`JSpec`)

`j t = C(r(pr.σ t), c(pc.σ t) && (v == b), j(pq.σ t))`: the join obeys the
C-element law on its own reads with the decode taken from the TOKEN's value
instead of the wire `s`. Selected join (`v = b`): exactly `bd_c2` on
(r, ctl_req). Unselected join (`v ≠ b`): with H_RESET it stays 0 for ever
(`unsel_low`): no wrong-branch token.

## Results

* `dev_iff` (the whole content, pointwise, by decide on the INITs): LUT and
  spec differ at an instant iff ctl_req reads 1, s reads `!v`, and the request
  read differs from the feedback read.
* `join_pin_ok` (sufficient, any read maps, NO hypothesis on `pr`, `pq`,
  H_RESET or the loop): H_SETUP_PIN `S0 + ps.hi ≤ Cr + pc.lo` and H_HOLD_PIN
  `Cf + pc.hi ≤ S1 + ps.lo` give JSpec.
* `join_pin_exact` (fixed delays `dr dc ds`, feedback `dq ≥ 1`): JSpec for
  every request trace, every admissible `s` and every trace obeying
  H_PIN_READ + H_RESET **iff** `S0 + ds ≤ Cr + dc ∧ Cf + dc ≤ S1 + ds`.
* `join_box_exact` (headline, the JSON form): same iff over the delay box
  (`pr ∈ [Rlo,Rhi]`, `pc ∈ [Clo,Chi]`, `ps ∈ [Slo,Shi]`, `pq ∈ [Qlo,Qhi]`,
  `Qlo ≥ 1`): **`S0 + Shi ≤ Cr + Clo ∧ Cf + Chi ≤ S1 + Slo`**.
  The request pin's and the FEEDBACK pin's windows drop out of the exact
  condition: they only shape what the failure looks like (below).
* Necessity witnesses (`caseA`, `caseB_unsel`, `caseB_sel_short`,
  `caseB_sel_long`) and the trace constructor `run` (`run_luteq`, `run_rest`):
  every violation has a real trace (H_PIN_READ, H_RESET hold for all `t`).
* Counter-traces: `wrong_branch_latched` (setup short by 100 ps, loop 50 ps:
  the UNSELECTED uj0 latches 1 for ever with x_req waiting: x's token is
  taken for y's control token), `wrong_branch_runt` (same violation, loop
  200 ps: a 100 ps runt on j0 that recirculates every 200 ps), and
  `selected_early_fall` (hold violated: the selected uj1 falls 500 ps before
  ctl_req, as read, would let it).
* `join_pin_ok_K`: the sufficient half under Kleene reads (`s`, `r`, the
  feedback may be X; outside its window `s` is anything).
* Non-vacuity: `witness_*`: a constructed run meeting every hypothesis in
  which uj1 fires and uj0 (with x_req waiting) stays 0.

NOT covered: the uxa/uya acknowledges and the RTZ rows (`MuxRtzTimed`); z
bundling (`ContractsMux`, `bd_mux.bundled_z*`); the ctl_req fork to the two
joins (shard C's rule K: here each join has its own `pc`); where `S0`, `S1`
come from (the control channel's contract, s held to ctl_ack↓ = z_ack↓);
reset timing; a mid-rail select in the NMOS mux tree (H_KLEENE_LUT, grade B);
internal mux-tree delay (folded into the per-pin arcs); correlated pin
delays (box necessity assumes pins independent; use `join_pin_exact` per
corner realisation under a correlated model); multiple tokens (the pointwise
`dev_iff` / `join_ok_of_reads` apply per token, not packaged).
-/

namespace Formal.Cells.LibGapMux
open Formal.Cells
open Formal.Cells.LibCtlMergeMux (j0B j1B j0K j1K cSpec cK)
open Formal.Cells.LibGapSteer

/-! ## 0. The join from the real INITs -/

/-- Join `b`: `b = false` is uj0 (x side, fires on `s = 0`), `b = true` is
uj1 (y side, fires on `s = 1`). Pins: `r` = I0, `c` = ctl_req I1, `s` = I2,
`q` = feedback I3; `rst` = I4 read 0. -/
def jB (b r c s q : Bool) : Bool := if b then j1B r c s q false else j0B r c s q false

theorem jB_eq : ∀ b r c s q : Bool, jB b r c s q = cSpec [r, c && (s == b)] q := by decide

/-- The spec value: the decode uses the token's value `v`, not the wire. -/
def specB (b v r c q : Bool) : Bool := cSpec [r, c && (v == b)] q

/-- **Pointwise deviation, exact.** -/
theorem dev_iff : ∀ b v r c s q : Bool,
    jB b r c s q ≠ specB b v r c q ↔ (c = true ∧ s ≠ v ∧ r ≠ q) := by decide

theorem agree_of : ∀ b v r c s q : Bool, (c = true → s = v) → jB b r c s q = specB b v r c q := by
  decide

theorem spec_unsel_low : ∀ b v r c : Bool, v ≠ b → specB b v r c false = false := by decide
theorem cS_low : ∀ r : Bool, cSpec [r, false] false = false := by decide
theorem cS_11 : ∀ q : Bool, cSpec [true, true] q = true := by decide
theorem cS_1x1 : ∀ d : Bool, cSpec [true, d] true = true := by decide
theorem cS_x11 : ∀ r : Bool, cSpec [r, true] true = true := by decide
theorem jB_fire : ∀ b q : Bool, jB b true true b q = true := by decide

/-! ## 1. Traces -/

/-- **H_PIN_READ** for one join (rst released at 0). -/
def LutEq (b : Bool) (pr pc ps pq : Rd) (r c s j : Int → Bool) : Prop :=
  ∀ t, 0 ≤ t → j t = jB b (r (pr.σ t)) (c (pc.σ t)) (s (ps.σ t)) (j (pq.σ t))

/-- **H_RESET**: 0 before release. -/
def Rest (j : Int → Bool) : Prop := ∀ t, t < 0 → j t = false

/-- The spec on the same trace. -/
def JSpec (b v : Bool) (pr pc pq : Rd) (r c j : Int → Bool) : Prop :=
  ∀ t, 0 ≤ t → j t = specB b v (r (pr.σ t)) (c (pc.σ t)) (j (pq.σ t))

theorem int_ind (P : Int → Prop) (hneg : ∀ t, t < 0 → P t)
    (h : ∀ t, 0 ≤ t → (∀ u, u < t → P u) → P t) : ∀ t, P t := by
  have key : ∀ n : Nat, ∀ t : Int, t < n → P t := by
    intro n
    induction n with
    | zero => intro t ht; exact hneg t (by omega)
    | succ n ih =>
      intro t ht
      by_cases h1 : t < n
      · exact ih t h1
      · by_cases h0 : t < 0
        · exact hneg t h0
        · exact h t (by omega) (fun u hu => ih u (by omega))
  intro t
  exact key (t.toNat + 1) t (by omega)

/-- Trace constructor: feedback delay `d ≥ 1`, next-state function `f`. -/
def runN (f : Int → Bool → Bool) (d : Nat) (hd : 0 < d) : Nat → Bool
  | n => f n (if h : n < d then false else runN f d hd (n - d))
termination_by n => n
decreasing_by omega

def run (f : Int → Bool → Bool) (d : Nat) (hd : 0 < d) (t : Int) : Bool :=
  if t < 0 then false else runN f d hd t.toNat

theorem run_rest (f : Int → Bool → Bool) (d : Nat) (hd : 0 < d) : Rest (run f d hd) := by
  intro t ht; simp [run, ht]

theorem run_eq (f : Int → Bool → Bool) (d : Nat) (hd : 0 < d) (t : Int) (ht : 0 ≤ t) :
    run f d hd t = f t (run f d hd (t - d)) := by
  unfold run
  rw [ite_eq_right (by omega), runN]
  have e : ((t.toNat : Nat) : Int) = t := Int.toNat_of_nonneg ht
  rw [e]
  congr 1
  by_cases h : t.toNat < d
  · rw [dite_eq_left h, ite_eq_left (by omega)]
  · rw [dite_eq_right h, ite_eq_right (by omega)]
    congr 1; omega

/-- The fixed-delay join next-state function. -/
def jf (b : Bool) (dr dc ds : Int) (r c s : Int → Bool) (t : Int) (q : Bool) : Bool :=
  jB b (r (t - dr)) (c (t - dc)) (s (t - ds)) q

/-- Every fixed-delay environment has a trace satisfying H_PIN_READ and
H_RESET (so the exact theorems below are not vacuous on the left). -/
theorem run_luteq (b : Bool) (dr dc ds : Int) (dq : Nat) (hd : 0 < dq) (r c s : Int → Bool) :
    LutEq b (Rd.const dr) (Rd.const dc) (Rd.const ds) (Rd.const dq) r c s
      (run (jf b dr dc ds r c s) dq hd) := by
  intro t ht
  exact run_eq _ dq hd t ht

/-! ## 2. Sufficient (any read maps) -/

theorem join_ok_of_reads (b v : Bool) (pr pc ps pq : Rd) (r c s j : Int → Bool)
    (hL : LutEq b pr pc ps pq r c s j)
    (hrd : ∀ t, 0 ≤ t → c (pc.σ t) = true → s (ps.σ t) = v) :
    JSpec b v pr pc pq r c j := by
  intro t ht
  rw [hL t ht]
  exact agree_of b v _ _ _ _ (hrd t ht)

/-- **Sufficient half.** No hypothesis on the request pin, the feedback pin,
the reset or the loop. -/
theorem join_pin_ok (b v : Bool) (pr pc ps pq : Rd) (Cr Cf S0 S1 : Int) (r s j : Int → Bool)
    (H_S_STABLE : Stable s v S0 S1) (hL : LutEq b pr pc ps pq r (pulse Cr Cf) s j)
    (H_SETUP_PIN : S0 + ps.hi ≤ Cr + pc.lo) (H_HOLD_PIN : Cf + pc.hi ≤ S1 + ps.lo) :
    JSpec b v pr pc pq r (pulse Cr Cf) j := by
  apply join_ok_of_reads b v pr pc ps pq r _ s j hL
  intro t _ hc
  have h : Cr ≤ pc.σ t ∧ pc.σ t < Cf := by simpa [pulse] using hc
  have g1 := pc.ge t; have g2 := pc.le t; have g3 := ps.ge t; have g4 := ps.le t
  exact H_S_STABLE _ (by omega) (by omega)

/-- Unselected join: JSpec + H_RESET + a positive loop ⇒ 0 for ever. -/
theorem unsel_low (b v : Bool) (hvb : v ≠ b) (pr pc pq : Rd) (hq : 1 ≤ pq.lo)
    (r c j : Int → Bool) (hS : JSpec b v pr pc pq r c j) (hR : Rest j) : ∀ t, j t = false := by
  apply int_ind (fun t => j t = false) hR
  intro t ht ih
  rw [hS t ht, ih _ (by have := pq.le t; omega)]
  exact spec_unsel_low b v _ _ hvb

/-- Selected join: when request and ctl_req both read 1, it is 1. -/
theorem sel_fires (b : Bool) (pr pc pq : Rd) (r c j : Int → Bool)
    (hS : JSpec b b pr pc pq r c j) (t : Int) (ht : 0 ≤ t)
    (hr : r (pr.σ t) = true) (hc : c (pc.σ t) = true) : j t = true := by
  rw [hS t ht, hr, hc]; unfold specB; simp [cS_11]

/-! ## 3. Necessity (fixed delays, constructed traces) -/

theorem sAdv_in' {v : Bool} {S0 S1 x : Int} (h1 : S0 ≤ x) (h2 : x < S1) : sAdv v S0 S1 x = v := by
  simp [sAdv, h1, h2]
theorem sAdv_out' {v : Bool} {S0 S1 x : Int} (h : ¬ (S0 ≤ x ∧ x < S1)) : sAdv v S0 S1 x = !v := by
  simp only [sAdv]; rw [ite_eq_right h]
theorem pulse_in' {R F x : Int} (h1 : R ≤ x) (h2 : x < F) : pulse R F x = true := by
  simp [pulse, h1, h2]
theorem pulse_lo' {R F x : Int} (h1 : x < R) : pulse R F x = false := by
  simp [pulse]; omega
theorem not_v (v : Bool) : (!v) ≠ v := by cases v <;> decide

/-- The join stays 0 while its decode reads 0 (H_RESET, positive loop). -/
theorem low_until (b : Bool) (pr pc ps pq : Rd) (r c s j : Int → Bool) (hq : 1 ≤ pq.lo)
    (hL : LutEq b pr pc ps pq r c s j) (hR : Rest j) (T : Int)
    (hd : ∀ u, 0 ≤ u → u < T → (c (pc.σ u) && (s (ps.σ u) == b)) = false) :
    ∀ u, u < T → j u = false := by
  apply int_ind (fun u => u < T → j u = false) (fun t ht _ => hR t ht)
  intro u hu ih hT
  rw [hL u hu, jB_eq, hd u hu hT, ih _ (by have := pq.le u; omega) (by have := pq.le u; omega)]
  exact cS_low _

/-- With the request held high, a decode high for one loop latches the join. -/
theorem latch (b : Bool) (dr dc ds : Int) (dq : Nat) (hdq : 0 < dq) (c s j : Int → Bool) (T : Int) (hT : 0 ≤ T)
    (hL : LutEq b (Rd.const dr) (Rd.const dc) (Rd.const ds) (Rd.const dq) (fun _ => true) c s j)
    (hd : ∀ u, T ≤ u → u < T + dq → (c (u - dc) && (s (u - ds) == b)) = true) :
    ∀ u, T ≤ u → j u = true := by
  apply int_ind (fun u => T ≤ u → j u = true) (fun t ht _ => by omega)
  intro u hu ih hTu
  rw [hL u hu, jB_eq]
  by_cases h : u < T + dq
  · show cSpec [true, c (u - dc) && (s (u - ds) == b)] (j (u - dq)) = true
    rw [hd u hTu h]; exact cS_11 _
  · show cSpec [true, c (u - dc) && (s (u - ds) == b)] (j (u - dq)) = true
    rw [ih _ (by omega) (by omega)]; exact cS_1x1 _

/-- A violation instant contradicts JSpec. -/
theorem no_spec_const (b v : Bool) (dr dc ds : Int) (dq : Nat) (r c s j : Int → Bool)
    (hL : LutEq b (Rd.const dr) (Rd.const dc) (Rd.const ds) (Rd.const dq) r c s j)
    (hS : JSpec b v (Rd.const dr) (Rd.const dc) (Rd.const dq) r c j) (t : Int) (ht : 0 ≤ t)
    (hc : c (t - dc) = true) (hs : s (t - ds) ≠ v) (hrq : r (t - dr) ≠ j (t - dq)) : False :=
  (dev_iff b v (r (t - dr)) (c (t - dc)) (s (t - ds)) (j (t - dq))).mpr ⟨hc, hs, hrq⟩
    ((hL t ht).symm.trans (hS t ht))

section Cases
set_option linter.unusedSectionVars false
variable (b v : Bool) (dr dc ds : Int) (dq : Nat) (hdq : 0 < dq) (Cr Cf S0 S1 : Int)
  (hCF : Cr < Cf) (hRst : 0 ≤ Cr + dc)
include hdq hCF hRst

/-- (A) `s` does not read `v` when ctl_req's rise is read (setup violated,
or `s` already gone): request waiting ⇒ either join deviates at `Cr + dc`. -/
theorem caseA (hA : ¬ (S0 ≤ Cr + dc - ds ∧ Cr + dc - ds < S1)) (j : Int → Bool)
    (hL : LutEq b (Rd.const dr) (Rd.const dc) (Rd.const ds) (Rd.const dq) (fun _ => true)
      (pulse Cr Cf) (sAdv v S0 S1) j) (hR : Rest j) :
    ¬ JSpec b v (Rd.const dr) (Rd.const dc) (Rd.const dq) (fun _ => true) (pulse Cr Cf) j := by
  intro hS
  have hlow := low_until b _ _ _ _ _ _ _ j (by simp [Rd.const]; omega) hL hR (Cr + dc) (by
    intro u _ hu
    show (pulse Cr Cf (u - dc) && _) = false
    rw [pulse_lo' (by omega)]; rfl)
  apply no_spec_const b v dr dc ds dq _ _ _ j hL hS (Cr + dc) hRst
  · exact pulse_in' (by omega) (by omega)
  · rw [sAdv_out' hA]; exact not_v v
  · show true ≠ j (Cr + dc - dq); rw [hlow _ (by omega)]; decide

/-- (B, unselected) `s` read `v` at the rise but changes (as read) while
ctl_req still reads 1: request waiting ⇒ the unselected join rises at
`S1 + ds`. -/
theorem caseB_unsel (hvb : v ≠ b) (hB : S0 ≤ Cr + dc - ds ∧ Cr + dc - ds < S1)
    (hH : S1 + ds < Cf + dc) (j : Int → Bool)
    (hL : LutEq b (Rd.const dr) (Rd.const dc) (Rd.const ds) (Rd.const dq) (fun _ => true)
      (pulse Cr Cf) (sAdv v S0 S1) j) (hR : Rest j) :
    ¬ JSpec b v (Rd.const dr) (Rd.const dc) (Rd.const dq) (fun _ => true) (pulse Cr Cf) j := by
  intro hS
  have hlow := low_until b _ _ _ _ _ _ _ j (by simp [Rd.const]; omega) hL hR (S1 + ds) (by
    intro u _ hu
    show (pulse Cr Cf (u - dc) && (sAdv v S0 S1 (u - ds) == b)) = false
    by_cases h : u - dc < Cr
    · rw [pulse_lo' h]; rfl
    · rw [sAdv_in' (by omega) (by omega)]; cases v <;> cases b <;> simp_all)
  apply no_spec_const b v dr dc ds dq _ _ _ j hL hS (S1 + ds) (by omega)
  · exact pulse_in' (by omega) (by omega)
  · rw [sAdv_out' (by omega)]; exact not_v v
  · show true ≠ j (S1 + ds - dq); rw [hlow _ (by omega)]; decide

/-- (B, selected, bad instant within one loop of the rise) request waiting ⇒
the selected join reads its own 0 and does not hold 1: deviation at `S1 + ds`. -/
theorem caseB_sel_short (_hvb : v = b) (hB : S0 ≤ Cr + dc - ds ∧ Cr + dc - ds < S1)
    (hH : S1 + ds < Cf + dc) (hsh : S1 + ds - dq < Cr + dc) (j : Int → Bool)
    (hL : LutEq b (Rd.const dr) (Rd.const dc) (Rd.const ds) (Rd.const dq) (fun _ => true)
      (pulse Cr Cf) (sAdv v S0 S1) j) (hR : Rest j) :
    ¬ JSpec b v (Rd.const dr) (Rd.const dc) (Rd.const dq) (fun _ => true) (pulse Cr Cf) j := by
  intro hS
  have hlow := low_until b _ _ _ _ _ _ _ j (by simp [Rd.const]; omega) hL hR (Cr + dc) (by
    intro u _ hu
    show (pulse Cr Cf (u - dc) && _) = false
    rw [pulse_lo' (by omega)]; rfl)
  apply no_spec_const b v dr dc ds dq _ _ _ j hL hS (S1 + ds) (by omega)
  · exact pulse_in' (by omega) (by omega)
  · rw [sAdv_out' (by omega)]; exact not_v v
  · show true ≠ j (S1 + ds - dq); rw [hlow _ hsh]; decide

/-- (B, selected, at least one loop after the rise) the request falls (as
read) exactly when `s` changes (as read), ctl_req still reads 1: the selected
join falls early. -/
theorem caseB_sel_long (hvb : v = b) (hB : S0 ≤ Cr + dc - ds ∧ Cr + dc - ds < S1)
    (hH : S1 + ds < Cf + dc) (hlg : Cr + dc ≤ S1 + ds - dq) (j : Int → Bool)
    (hL : LutEq b (Rd.const dr) (Rd.const dc) (Rd.const ds) (Rd.const dq)
      (fun u => decide (u < S1 + ds - dr)) (pulse Cr Cf) (sAdv v S0 S1) j) :
    ¬ JSpec b v (Rd.const dr) (Rd.const dc) (Rd.const dq)
      (fun u => decide (u < S1 + ds - dr)) (pulse Cr Cf) j := by
  intro hS
  have hhi : ∀ u, Cr + dc ≤ u → u < S1 + ds → j u = true := by
    intro u h1 h2
    rw [hL u (by omega)]
    show jB b (decide (u - dr < S1 + ds - dr)) (pulse Cr Cf (u - dc)) (sAdv v S0 S1 (u - ds)) _ = true
    rw [pulse_in' (by omega) (by omega), sAdv_in' (by omega) (by omega), hvb,
      decide_eq_true (by omega)]
    exact jB_fire b _
  apply no_spec_const b v dr dc ds dq _ _ _ j hL hS (S1 + ds) (by omega)
  · exact pulse_in' (by omega) (by omega)
  · rw [sAdv_out' (by omega)]; exact not_v v
  · show decide (S1 + ds - dr < S1 + ds - dr) ≠ j (S1 + ds - dq)
    rw [hhi _ (by omega) (by omega)]; simp

end Cases

/-- **Necessity, fixed delays**: any violation has a request trace and a
real join trace (H_PIN_READ, H_RESET for all t) on which JSpec fails. -/
theorem join_needed (b v : Bool) (dr dc ds : Int) (dq : Nat) (hdq : 0 < dq) (Cr Cf S0 S1 : Int)
    (hCF : Cr < Cf) (hRst : 0 ≤ Cr + dc) (hbad : ¬ (S0 + ds ≤ Cr + dc ∧ Cf + dc ≤ S1 + ds)) :
    ∃ r j : Int → Bool,
      LutEq b (Rd.const dr) (Rd.const dc) (Rd.const ds) (Rd.const dq) r (pulse Cr Cf) (sAdv v S0 S1) j ∧
      Rest j ∧ ¬ JSpec b v (Rd.const dr) (Rd.const dc) (Rd.const dq) r (pulse Cr Cf) j := by
  have mk : ∀ r : Int → Bool, (∀ j, LutEq b (Rd.const dr) (Rd.const dc) (Rd.const ds) (Rd.const dq) r
      (pulse Cr Cf) (sAdv v S0 S1) j → Rest j →
      ¬ JSpec b v (Rd.const dr) (Rd.const dc) (Rd.const dq) r (pulse Cr Cf) j) →
      ∃ r j : Int → Bool,
      LutEq b (Rd.const dr) (Rd.const dc) (Rd.const ds) (Rd.const dq) r (pulse Cr Cf) (sAdv v S0 S1) j ∧
      Rest j ∧ ¬ JSpec b v (Rd.const dr) (Rd.const dc) (Rd.const dq) r (pulse Cr Cf) j := by
    intro r h
    let j := run (jf b dr dc ds r (pulse Cr Cf) (sAdv v S0 S1)) dq hdq
    exact ⟨r, j, run_luteq b dr dc ds dq hdq _ _ _, run_rest _ dq hdq,
      h j (run_luteq b dr dc ds dq hdq _ _ _) (run_rest _ dq hdq)⟩
  by_cases hA : S0 ≤ Cr + dc - ds ∧ Cr + dc - ds < S1
  · have hH : S1 + ds < Cf + dc := by omega
    by_cases hvb : v = b
    · by_cases hlg : Cr + dc ≤ S1 + ds - dq
      · exact mk _ (fun j hL _ => caseB_sel_long b v dr dc ds dq hdq Cr Cf S0 S1 hCF hRst hvb hA hH hlg j hL)
      · exact mk _ (fun j hL hR =>
          caseB_sel_short b v dr dc ds dq hdq Cr Cf S0 S1 hCF hRst hvb hA hH (by omega) j hL hR)
    · exact mk _ (fun j hL hR => caseB_unsel b v dr dc ds dq hdq Cr Cf S0 S1 hCF hRst hvb hA hH j hL hR)
  · exact mk _ (fun j hL hR => caseA b v dr dc ds dq hdq Cr Cf S0 S1 hCF hRst hA j hL hR)

/-- **Exact, fixed delays.** The request delay `dr` and the feedback delay
`dq` do not appear on the right. -/
theorem join_pin_exact (b v : Bool) (dr dc ds : Int) (dq : Nat) (hdq : 0 < dq) (Cr Cf S0 S1 : Int)
    (hCF : Cr < Cf) (hRst : 0 ≤ Cr + dc) :
    (∀ r s j : Int → Bool, Stable s v S0 S1 →
      LutEq b (Rd.const dr) (Rd.const dc) (Rd.const ds) (Rd.const dq) r (pulse Cr Cf) s j → Rest j →
      JSpec b v (Rd.const dr) (Rd.const dc) (Rd.const dq) r (pulse Cr Cf) j) ↔
    (S0 + ds ≤ Cr + dc ∧ Cf + dc ≤ S1 + ds) := by
  constructor
  · intro h
    apply Classical.byContradiction; intro hn
    obtain ⟨r, j, hL, hR, hS⟩ := join_needed b v dr dc ds dq hdq Cr Cf S0 S1 hCF hRst hn
    exact hS (h r _ j (sAdv_stable v S0 S1) hL hR)
  · rintro ⟨h1, h2⟩ r s j hs hL _
    exact join_pin_ok b v _ _ _ _ Cr Cf S0 S1 r s j hs hL
      (by simpa [Rd.const] using h1) (by simpa [Rd.const] using h2)

/-- **Headline: exact over the delay box** (per join, per pin, feedback pin
included in the model). -/
theorem join_box_exact (b v : Bool) (Rlo Rhi Clo Chi Slo Shi Qlo Qhi Cr Cf S0 S1 : Int)
    (hR : Rlo ≤ Rhi) (hC : Clo ≤ Chi) (hS : Slo ≤ Shi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (hCF : Cr < Cf) (hRst : 0 ≤ Cr + Clo) :
    (∀ pr pc ps pq : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Clo ≤ pc.lo → pc.hi ≤ Chi →
      Slo ≤ ps.lo → ps.hi ≤ Shi → Qlo ≤ pq.lo → pq.hi ≤ Qhi →
      ∀ r s j : Int → Bool, Stable s v S0 S1 → LutEq b pr pc ps pq r (pulse Cr Cf) s j → Rest j →
        JSpec b v pr pc pq r (pulse Cr Cf) j) ↔
    (S0 + Shi ≤ Cr + Clo ∧ Cf + Chi ≤ S1 + Slo) := by
  have hq0 : 0 < Qlo.toNat := by omega
  have hqa : Qlo ≤ ((Qlo.toNat : Nat) : Int) := by omega
  have hqb : ((Qlo.toNat : Nat) : Int) ≤ Qhi := by omega
  constructor
  · intro h
    refine ⟨?_, ?_⟩
    · exact ((join_pin_exact b v Rlo Clo Shi Qlo.toNat hq0 Cr Cf S0 S1 hCF hRst).mp
        (fun r s j hs hL hRs => h (Rd.const Rlo) (Rd.const Clo) (Rd.const Shi) (Rd.const Qlo.toNat)
          (by simp [Rd.const]) (by simp [Rd.const]; omega) (by simp [Rd.const]) (by simp [Rd.const]; omega)
          (by simp [Rd.const]; omega) (by simp [Rd.const]) (by simp [Rd.const]; omega)
          (by simp [Rd.const]; omega) r s j hs hL hRs)).1
    · exact ((join_pin_exact b v Rlo Chi Slo Qlo.toNat hq0 Cr Cf S0 S1 hCF (by omega)).mp
        (fun r s j hs hL hRs => h (Rd.const Rlo) (Rd.const Chi) (Rd.const Slo) (Rd.const Qlo.toNat)
          (by simp [Rd.const]) (by simp [Rd.const]; omega) (by simp [Rd.const]; omega) (by simp [Rd.const])
          (by simp [Rd.const]) (by simp [Rd.const]; omega) (by simp [Rd.const]; omega)
          (by simp [Rd.const]; omega) r s j hs hL hRs)).2
  · rintro ⟨h1, h2⟩ pr pc ps pq _ _ a3 a4 a5 a6 _ _ r s j hs hL _
    exact join_pin_ok b v pr pc ps pq Cr Cf S0 S1 r s j hs hL (by omega) (by omega)

/-- Both joins of one `bd_mux` for one control token: four inequalities
(each join has its own ctl_req and s read maps: the ctl_req fork is per
join). uj1 is the selected one for `v = true`. -/
theorem mux_joins (v : Bool) (pr0 pc0 ps0 pq0 pr1 pc1 ps1 pq1 : Rd) (Cr Cf S0 S1 : Int)
    (x y s j0 j1 : Int → Bool) (hs : Stable s v S0 S1)
    (hL0 : LutEq false pr0 pc0 ps0 pq0 x (pulse Cr Cf) s j0)
    (hL1 : LutEq true pr1 pc1 ps1 pq1 y (pulse Cr Cf) s j1)
    (H_SETUP_J0 : S0 + ps0.hi ≤ Cr + pc0.lo) (H_HOLD_J0 : Cf + pc0.hi ≤ S1 + ps0.lo)
    (H_SETUP_J1 : S0 + ps1.hi ≤ Cr + pc1.lo) (H_HOLD_J1 : Cf + pc1.hi ≤ S1 + ps1.lo) :
    JSpec false v pr0 pc0 pq0 x (pulse Cr Cf) j0 ∧ JSpec true v pr1 pc1 pq1 y (pulse Cr Cf) j1 :=
  ⟨join_pin_ok false v _ _ _ _ Cr Cf S0 S1 x s j0 hs hL0 H_SETUP_J0 H_HOLD_J0,
   join_pin_ok true v _ _ _ _ Cr Cf S0 S1 y s j1 hs hL1 H_SETUP_J1 H_HOLD_J1⟩

/-! ## 4. Counter-traces (concrete ps; true for EVERY trace obeying H_PIN_READ + H_RESET) -/

/-- Setup violated by 100 ps at uj0 (unselected: the token says y, `v = 1`):
ctl_req `[1000, 3000)` read through 300 ps, `s` settles to 1 at 800 read
through 600 ps (reads 0 until 1400), x_req WAITING (high throughout), loop
50 ps. uj0 latches 1 from 1300 for ever: x's token is consumed for y's control. -/
theorem wrong_branch_latched (j : Int → Bool)
    (hL : LutEq false (Rd.const 0) (Rd.const 300) (Rd.const 600) (Rd.const (50 : Nat))
      (fun _ => true) (pulse 1000 3000) (sAdv true 800 5000) j) :
    ∀ t, 1300 ≤ t → j t = true := by
  apply latch false 0 300 600 50 (by decide) _ _ j 1300 (by omega) hL
  intro u h1 h2
  rw [pulse_in' (by omega) (by omega), sAdv_out' (by omega)]; rfl

/-- Same violation, loop 200 ps (longer than the 100 ps bad window): a runt
on j0 at 1300 (gone at 1400), which the feedback recirculates at 1500. -/
theorem wrong_branch_runt (j : Int → Bool)
    (hL : LutEq false (Rd.const 0) (Rd.const 300) (Rd.const 600) (Rd.const (200 : Nat))
      (fun _ => true) (pulse 1000 3000) (sAdv true 800 5000) j) (hR : Rest j) :
    j 1300 = true ∧ j 1400 = false ∧ j 1500 = true := by
  have hlow := low_until false _ _ _ _ _ _ _ j (by simp [Rd.const]) hL hR 1300 (by
    intro u _ hu
    show (pulse 1000 3000 (u - 300) && _) = false
    rw [pulse_lo' (by omega)]; rfl)
  have a : j 1300 = true := by
    rw [hL 1300 (by omega), jB_eq]
    show cSpec [true, pulse 1000 3000 (1300 - 300) && (sAdv true 800 5000 (1300 - 600) == false)] _ = true
    rw [pulse_in' (by omega) (by omega), sAdv_out' (by omega)]; exact cS_11 _
  have b : j 1400 = false := by
    rw [hL 1400 (by omega)]
    have : j ((Rd.const ((200 : Nat) : Int)).σ 1400) = false := hlow _ (by simp [Rd.const])
    rw [this]; decide
  have c : j 1500 = true := by
    rw [hL 1500 (by omega)]
    have : j ((Rd.const ((200 : Nat) : Int)).σ 1500) = true := by
      show j (1500 - ((200 : Nat) : Int)) = true
      have e : (1500 : Int) - ((200 : Nat) : Int) = 1300 := by omega
      rw [e]; exact a
    rw [this]; decide
  exact ⟨a, b, c⟩

/-- Hold violated at the SELECTED uj1 (`v = 1`): ctl_req `[1000, 3000)` read
through 300 ps (reads 1 until 3300); `s` changes at 2500, read through 300 ps
(reads 0 from 2800); y_req falls at 2000, read through 300 ps; loop 100 ps.
uj1 is 1 on [1300, 2800) but 0 at 2800, where the spec (ctl_req still reads
1, its own 1 fed back) holds it at 1: an early fall by 500 ps. -/
theorem selected_early_fall (j : Int → Bool)
    (hL : LutEq true (Rd.const 300) (Rd.const 300) (Rd.const 300) (Rd.const (100 : Nat))
      (fun u => decide (u < 2000)) (pulse 1000 3000) (sAdv true 500 2500) j) :
    j 2700 = true ∧ j 2800 = false ∧
    specB true true (decide ((2800 : Int) - 300 < 2000)) (pulse 1000 3000 (2800 - 300)) (j 2700) = true := by
  have hhi : ∀ u, 1300 ≤ u → u < 2800 → j u = true := by
    apply int_ind (fun u => 1300 ≤ u → u < 2800 → j u = true) (fun t ht _ => by omega)
    intro u hu ih h1 h2
    rw [hL u hu, jB_eq]
    show cSpec [decide (u - 300 < 2000), pulse 1000 3000 (u - 300) && (sAdv true 500 2500 (u - 300) == true)]
      (j (u - ((100 : Nat) : Int))) = true
    rw [pulse_in' (by omega) (by omega), sAdv_in' (by omega) (by omega)]
    by_cases h : u < 1400
    · rw [decide_eq_true (by omega)]; exact cS_11 _
    · rw [ih _ (by omega) (by omega) (by omega)]; exact cS_x11 _
  have a := hhi 2700 (by omega) (by omega)
  refine ⟨a, ?_, ?_⟩
  · rw [hL 2800 (by omega)]
    have : j ((Rd.const ((100 : Nat) : Int)).σ 2800) = true := by
      show j (2800 - ((100 : Nat) : Int)) = true
      have e : (2800 : Int) - ((100 : Nat) : Int) = 2700 := by omega
      rw [e]; exact a
    rw [this]; decide
  · rw [a]; decide

/-! ## 5. Kleene reads (sufficient half) -/

def jK (b : Bool) (r c s q : K3) : K3 := if b then j1K r c s q .f else j0K r c s q .f

/-- Real INITs, Kleene: when ctl_req is definite and `s` reads the token value
whenever ctl_req reads 1, the join is the Kleene C-element on (r, decode(v))
whatever `r`, `s` (when ctl_req is 0) and the feedback are, X included. -/
theorem jK_agree : ∀ (b v c : Bool) (r s q : K3), (c = true → s = K3.ofBool v) →
    jK b r (.ofBool c) s q = cK [r, .ofBool (c && (v == b))] q := by decide

theorem join_pin_ok_K (b v : Bool) (pr pc ps pq : Rd) (Cr Cf S0 S1 : Int) (rK sK jt : Int → K3)
    (H_S_STABLE_K : ∀ t, S0 ≤ t → t < S1 → sK t = .ofBool v)
    (hL : ∀ t, 0 ≤ t → jt t = jK b (rK (pr.σ t)) (.ofBool (pulse Cr Cf (pc.σ t))) (sK (ps.σ t)) (jt (pq.σ t)))
    (H_SETUP_PIN : S0 + ps.hi ≤ Cr + pc.lo) (H_HOLD_PIN : Cf + pc.hi ≤ S1 + ps.lo) :
    ∀ t, 0 ≤ t → jt t = cK [rK (pr.σ t), .ofBool (pulse Cr Cf (pc.σ t) && (v == b))] (jt (pq.σ t)) := by
  intro t ht
  rw [hL t ht]
  apply jK_agree
  intro hc
  have h : Cr ≤ pc.σ t ∧ pc.σ t < Cf := by simpa [pulse] using hc
  have g1 := pc.ge t; have g2 := pc.le t; have g3 := ps.ge t; have g4 := ps.le t
  exact H_S_STABLE_K _ (by omega) (by omega)

/-! ## 6. Non-vacuity -/

/-- Numbers: ctl_req `[1000, 3000)` via 300 ps, `s = 1` on `[500, 4000)` via
450 ps: setup `500 + 450 ≤ 1000 + 300`, hold `3000 + 300 ≤ 4000 + 450`. -/
def wj (b : Bool) : Int → Bool :=
  run (jf b 0 300 450 (fun _ => true) (pulse 1000 3000) (sAdv true 500 4000)) 100 (by decide)

theorem witness_hyps (b : Bool) :
    Stable (sAdv true 500 4000) true 500 4000 ∧
    LutEq b (Rd.const 0) (Rd.const 300) (Rd.const 450) (Rd.const (100 : Nat)) (fun _ => true)
      (pulse 1000 3000) (sAdv true 500 4000) (wj b) ∧ Rest (wj b) ∧
    (500 : Int) + 450 ≤ 1000 + 300 ∧ (3000 : Int) + 300 ≤ 4000 + 450 :=
  ⟨sAdv_stable true 500 4000, run_luteq b 0 300 450 100 (by decide) _ _ _, run_rest _ 100 (by decide),
   by decide, by decide⟩

/-- In that run, with BOTH requests waiting (a loop header with tokens on x
and y): uj1 (selected) fires at 1300, uj0 (unselected) is 0 at every instant. -/
theorem witness_run : wj true 1300 = true ∧ ∀ t, wj false t = false := by
  obtain ⟨hs, hL1, hR1, h1, h2⟩ := witness_hyps true
  obtain ⟨_, hL0, hR0, _, _⟩ := witness_hyps false
  have S1 := join_pin_ok true true _ _ _ _ 1000 3000 500 4000 _ _ _ hs hL1
    (by simp [Rd.const]) (by simp [Rd.const])
  have S0 := join_pin_ok false true _ _ _ _ 1000 3000 500 4000 _ _ _ hs hL0
    (by simp [Rd.const]) (by simp [Rd.const])
  refine ⟨sel_fires true _ _ _ _ _ _ S1 1300 (by decide) rfl (by decide), ?_⟩
  exact unsel_low false true (by decide) _ _ _ (by simp [Rd.const]) _ _ _ S0 hR0

end Formal.Cells.LibGapMux
