import Formal.Cells.LibGapLatch
import Formal.Cells.LibGapMuxN
open Formal.Core.LutList

/-!
# KleeneBox: the per-pin box iffs of `bd_steer`, `bd_mux`'s joins, `bdc_muxn`'s selected join and `bd_latch`, with K3 traces on EVERY pin

Probe Bkx (shard B). `LibGapSteer.steer_box_exact`, `LibGapMux.join_box_exact`
and `LibGapMuxN.sel_box_exact` are iffs over BINARY traces (the adversarial
select `sAdv` is binary); only their sufficient halves had a Kleene form
(`steer_pin_ok_K`, `join_pin_ok_K`; none for MuxN). A pin that is
mid-transition is physically X. This file proves the iffs with K3 traces on
every pin (request, ctl_req, select / index bits, feedback), X allowed
anywhere outside the stable windows, outputs through the REAL INITs under
H_KLEENE_LUT (`lutK` = Core's mux-tree `Lut.keval`: `LibCtlMergeMux.req0K/
req1K`, `j0K/j1K`, `AMergeGates.SEL*`, `C2`), spec "output equals the spec
function of its reads, in K3" (so: definite and correct wherever the spec is
definite; the unselected branch definite 0 at every instant).

## Model (named hypotheses, all K3)

* **H_PIN_READ**: as in the binary files (`Rd` read maps, not necessarily
  monotone), now applied to K3 traces; feedback pins read K3 too.
* **H_REQ_SUPP** (`Supp Ra Fa r`): the request / ctl_req trace is NOT definite
  0 only inside `[Ra, Fa)` (inside: anything, X included; `Ra`, `Fa` are the
  first and last instants at which it is not a clean 0, X windows included).
* **H_S_STABLE_K** (`StabK v S0 S1 s`): the select (each index bit) is
  definite `v` on `[S0, S1)`; ANY K3 value (X included) outside.
* **H_RESET**: the join output is definite 0 before 0.
* Edge forms (sections 3-6), **H_X_UNIFORM**: each binary edge `T` (the
  time a binary trace would switch) carries an X window `[T - a, T + c)`,
  the same split `a, c ≥ 0` (width `w = a + c`) for every edge; outside its
  windows a trace is definite (request: 0 before `R - a` and from `F + c`, 1 on
  `[R + c, F - a)`; select: `v` on `[S0 + c, S1 - a)`, anything outside).
  `a = 1, c = 0` is CElemStrict's / LibGapLatch's convention, `a = 0, c = 1`
  the opposite one; the result depends only on `w`.

## Results (headlines)

* `steer_box_exact_K`, `join_box_exact_K`, `muxn_sel_box_exact_K`: the K3
  iffs. Their right sides are IDENTICAL to the binary iffs' with the windows
  read as "definite windows" (`steer_K_iff_binary`, `join_K_iff_binary`,
  `muxn_K_iff_binary`: K3 safety ⟺ binary safety). X on the inputs adds no
  failure mode of its own: every failure already has a binary witness, and the
  sufficient halves are X-proof (the select is only looked at while the
  request / ctl_req is not definite 0, where it is definite; a definite 0
  request / ctl_req masks an X select in the real INITs).
* `steer_edges_K`, `join_edges_K`, `muxn_edges_K`, `latch_edges_uniform`: in BINARY-EDGE times
  (H_X_UNIFORM) every setup and every hold gains exactly `+w`:
  steer `S0 + Shi + w ≤ R + Rlo`, `F + Rhi + w ≤ S1 + Slo`; join
  `S0 + Shi + w ≤ Cr + Clo`, `Cf + Chi + w ≤ S1 + Slo`; muxn per index bit
  the same against ctl_req at the decode pins; latch setup_pulse,
  setup_data, hold each `+ w` (as `LibGapLatch.box_exact_edges`, now for any
  uniform split). With one tick (`w = 1`): ALL STRICT (`*_strict_K`).
* `steer_ct_setup_x`, `steer_ct_hold_x`, `join_ct_setup_x`, `join_ct_hold_x`:
  1-tick X windows on every edge, binary-edge EQUALITY (where the binary iff
  is satisfied): the unselected output reads X (spec: definite 0), on every
  trace obeying the hypotheses.
* Non-vacuity: `steer_witness_K`, `join_witness_K` (all hypotheses with X
  windows on every edge, strict inequalities, outputs definite and correct).
  bdc_muxn: no X-specific witness; its K3 hypotheses are met by every binary
  witness of LibGapMuxN through the embedding (`muxn_K_to_B`'s traces).

NOT covered: the X window widths (1 tick is the grid minimum, not a measured
slew); a mid-rail select inside the mux tree beyond H_KLEENE_LUT (grade B);
`bdc_muxn`'s UNSELECTED joins in K3 (`unsel_box_exact`/`Cover` stays binary);
`NecessityReset.reset_box_exact` (not redone here); correlated corners (box
form = independent pins).
-/

namespace Formal.Cells.KleeneBox
open Formal.Cells
open Formal.Cells.LibGapSteer (Rd Rd.const pulse Stable SpecOK sAdv sAdv_stable outB outK
  outK_def outB_eq)
open Formal.Cells.LibCtlMergeMux (cK cSpec)
open Formal.Cells.LibGapMux (int_ind)

abbrev kb (b : Bool) : K3 := K3.ofBool b

theorem kb_inj : ∀ a b : Bool, kb a = kb b → a = b := by decide

/-- The spec's gate: `r` passed when the token selects this output, else 0. -/
def kgate (r : K3) (g : Bool) : K3 := if g then r else .f

theorem kgate_kb : ∀ r g : Bool, kgate (kb r) g = kb (r && g) := by decide

/-! ## 1. Trace predicates -/

/-- **H_REQ_SUPP**: not definite 0 only inside `[Ra, Fa)`. -/
def Supp (Ra Fa : Int) (r : Int → K3) : Prop := ∀ x, r x ≠ .f → Ra ≤ x ∧ x < Fa

/-- **H_S_STABLE_K**: definite `v` on `[S0, S1)`, anything (X included) outside. -/
def StabK (v : Bool) (S0 S1 : Int) (s : Int → K3) : Prop := ∀ x, S0 ≤ x → x < S1 → s x = kb v

theorem supp_pulse (Ra Fa : Int) : Supp Ra Fa (fun x => kb (pulse Ra Fa x)) := by
  intro x hx
  by_cases h : Ra ≤ x ∧ x < Fa
  · exact h
  · exact absurd (by simp [pulse, h]) hx

theorem stabK_of (v : Bool) (S0 S1 : Int) (s : Int → Bool) (h : Stable s v S0 S1) :
    StabK v S0 S1 (fun x => kb (s x)) := fun x h1 h2 => by simp [h x h1 h2]

/-! ## 2. `bd_steer` (LUT6_2 `8888_8888_2222_2222`, O5 = req0, O6 = req1) -/

/-- The spec, K3: branch `b` shows the request read, gated by the token. -/
def SpecK (b v : Bool) (pr ps : Rd) (r s : Int → K3) : Prop :=
  ∀ t, outK b (r (pr.σ t)) (s (ps.σ t)) = kgate (r (pr.σ t)) (v == b)

/-- Pointwise, real INIT, all 3^2 K3 inputs: if the select is the token's
value whenever the request is not definite 0, the output IS the spec. -/
theorem outK_sel : ∀ (b v : Bool) (r s : K3), (r ≠ .f → s = kb v) → outK b r s = kgate r (v == b) := by
  decide

/-- **Sufficient, K3, any read maps.** -/
theorem steer_ok_K (b v : Bool) (pr ps : Rd) (Ra Fa S0 S1 : Int) (r s : Int → K3)
    (H_REQ_SUPP : Supp Ra Fa r) (H_S_STABLE_K : StabK v S0 S1 s)
    (H_SETUP_PIN : S0 + ps.hi ≤ Ra + pr.lo) (H_HOLD_PIN : Fa + pr.hi ≤ S1 + ps.lo) :
    SpecK b v pr ps r s := by
  intro t
  apply outK_sel
  intro hr
  obtain ⟨h1, h2⟩ := H_REQ_SUPP _ hr
  have := pr.ge t; have := pr.le t; have := ps.ge t; have := ps.le t
  exact H_S_STABLE_K _ (by omega) (by omega)

/-- Box safety, K3 traces. -/
def SteerSafeK (b v : Bool) (Rlo Rhi Slo Shi Ra Fa S0 S1 : Int) : Prop :=
  ∀ pr ps : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Slo ≤ ps.lo → ps.hi ≤ Shi →
    ∀ r s, Supp Ra Fa r → StabK v S0 S1 s → SpecK b v pr ps r s

/-- Box safety, binary traces (the left side of `steer_box_exact`). -/
def SteerSafeB (b v : Bool) (Rlo Rhi Slo Shi Ra Fa S0 S1 : Int) : Prop :=
  ∀ pr ps : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Slo ≤ ps.lo → ps.hi ≤ Shi →
    ∀ s, Stable s v S0 S1 → SpecOK b v pr ps Ra Fa s

/-- K3 safety implies binary safety (binary traces embed). -/
theorem steer_K_to_B (b v : Bool) (Rlo Rhi Slo Shi Ra Fa S0 S1 : Int)
    (h : SteerSafeK b v Rlo Rhi Slo Shi Ra Fa S0 S1) : SteerSafeB b v Rlo Rhi Slo Shi Ra Fa S0 S1 := by
  intro pr ps a1 a2 a3 a4 s hs t
  have := h pr ps a1 a2 a3 a4 _ _ (supp_pulse Ra Fa) (stabK_of v S0 S1 s hs) t
  rw [outK_def, kgate_kb] at this
  exact kb_inj _ _ this

/-- **Headline (steer), K3 on every pin, exact over the box.** Same right side
as `steer_box_exact` with `Ra, Fa` the request's not-definite-0 support. -/
theorem steer_box_exact_K (b v : Bool) (Rlo Rhi Slo Shi Ra Fa S0 S1 : Int)
    (hR : Rlo ≤ Rhi) (hS : Slo ≤ Shi) (hRF : Ra < Fa) :
    SteerSafeK b v Rlo Rhi Slo Shi Ra Fa S0 S1 ↔ (S0 + Shi ≤ Ra + Rlo ∧ Fa + Rhi ≤ S1 + Slo) := by
  constructor
  · intro h
    exact (LibGapSteer.steer_box_exact b v Rlo Rhi Slo Shi Ra Fa S0 S1 hR hS hRF).mp
      (steer_K_to_B b v _ _ _ _ _ _ _ _ h)
  · rintro ⟨h1, h2⟩ pr ps a1 a2 a3 a4 r s hr hs
    exact steer_ok_K b v pr ps Ra Fa S0 S1 r s hr hs (by omega) (by omega)

/-- **K3 adds nothing in definite-window coordinates**: K3 box safety ⟺
binary box safety. -/
theorem steer_K_iff_binary (b v : Bool) (Rlo Rhi Slo Shi Ra Fa S0 S1 : Int)
    (hR : Rlo ≤ Rhi) (hS : Slo ≤ Shi) (hRF : Ra < Fa) :
    SteerSafeK b v Rlo Rhi Slo Shi Ra Fa S0 S1 ↔ SteerSafeB b v Rlo Rhi Slo Shi Ra Fa S0 S1 := by
  exact (steer_box_exact_K b v _ _ _ _ _ _ _ _ hR hS hRF).trans
    (LibGapSteer.steer_box_exact b v _ _ _ _ _ _ _ _ hR hS hRF).symm

/-- Spec consequences: wherever the request read is definite, the output is
definite and equals the binary spec; the unselected branch is definite 0 at
every instant, X on the request included. -/
theorem specK_definite (b v : Bool) (pr ps : Rd) (r s : Int → K3) (h : SpecK b v pr ps r s) (t : Int) :
    (∀ p : Bool, r (pr.σ t) = kb p → outK b (r (pr.σ t)) (s (ps.σ t)) = kb (p && (v == b))) ∧
    (v ≠ b → outK b (r (pr.σ t)) (s (ps.σ t)) = .f) := by
  refine ⟨fun p hp => by rw [h t, hp, kgate_kb], fun hvb => ?_⟩
  rw [h t]; simp [kgate, hvb]

/-! ## 3. Steer in binary-edge times (H_X_UNIFORM) -/

/-- Request with binary edges `R` (rise) and `F` (fall), X windows
`[R - a, R + c)` and `[F - a, F + c)`; outside them definite. -/
def ReqEdge (R F a c : Int) (r : Int → K3) : Prop :=
  (∀ x, (x < R - a ∨ F + c ≤ x) → r x = .f) ∧ (∀ x, R + c ≤ x → x < F - a → r x = .t)

theorem reqEdge_supp {R F a c : Int} {r : Int → K3} (h : ReqEdge R F a c r) : Supp (R - a) (F + c) r := by
  intro x hx
  apply Classical.byContradiction; intro hn
  exact hx (h.1 x (by omega))

theorem reqEdge_pulse (R F a c : Int) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    ReqEdge R F a c (fun x => kb (pulse (R - a) (F + c) x)) := by
  refine ⟨fun x hx => ?_, fun x h1 h2 => ?_⟩
  · have : ¬ (R - a ≤ x ∧ x < F + c) := by omega
    simp [pulse, this]
  · have : R - a ≤ x ∧ x < F + c := by omega
    simp [pulse, this]

/-- **Steer, binary-edge form, exact.** The select's binary window `[S0, S1)`
is definite only on `[S0 + c, S1 - a)`. Every inequality gains `w = a + c`. -/
theorem steer_edges_K (b v : Bool) (Rlo Rhi Slo Shi R F S0 S1 a c : Int)
    (hR : Rlo ≤ Rhi) (hS : Slo ≤ Shi) (hRF : R < F) (ha : 0 ≤ a) (hc : 0 ≤ c) :
    (∀ pr ps : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Slo ≤ ps.lo → ps.hi ≤ Shi →
      ∀ r s, ReqEdge R F a c r → StabK v (S0 + c) (S1 - a) s → SpecK b v pr ps r s) ↔
    (S0 + Shi + (a + c) ≤ R + Rlo ∧ F + Rhi + (a + c) ≤ S1 + Slo) := by
  constructor
  · intro h
    have hB : SteerSafeB b v Rlo Rhi Slo Shi (R - a) (F + c) (S0 + c) (S1 - a) := by
      intro pr ps a1 a2 a3 a4 s hs t
      have := h pr ps a1 a2 a3 a4 _ _ (reqEdge_pulse R F a c ha hc) (stabK_of v _ _ s hs) t
      rw [outK_def, kgate_kb] at this
      exact kb_inj _ _ this
    have := (LibGapSteer.steer_box_exact b v Rlo Rhi Slo Shi (R - a) (F + c) (S0 + c) (S1 - a)
      hR hS (by omega)).mp hB
    omega
  · rintro ⟨h1, h2⟩ pr ps a1 a2 a3 a4 r s hr hs
    exact steer_ok_K b v pr ps (R - a) (F + c) (S0 + c) (S1 - a) r s (reqEdge_supp hr) hs
      (by omega) (by omega)

/-- **Strict**: one tick of X on each edge (either convention): setup AND hold
of `bd_steer` are strict in binary-edge times. -/
theorem steer_strict_K (b v : Bool) (Rlo Rhi Slo Shi R F S0 S1 a c : Int)
    (hR : Rlo ≤ Rhi) (hS : Slo ≤ Shi) (hRF : R < F) (ha : 0 ≤ a) (hc : 0 ≤ c) (hw : a + c = 1) :
    (∀ pr ps : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Slo ≤ ps.lo → ps.hi ≤ Shi →
      ∀ r s, ReqEdge R F a c r → StabK v (S0 + c) (S1 - a) s → SpecK b v pr ps r s) ↔
    (S0 + Shi < R + Rlo ∧ F + Rhi < S1 + Slo) := by
  rw [steer_edges_K b v Rlo Rhi Slo Shi R F S0 S1 a c hR hS hRF ha hc]; omega

/-- Zero-width windows (`a = c = 0`): the binary iff's `≤` form back. -/
theorem steer_atomic_K (b v : Bool) (Rlo Rhi Slo Shi R F S0 S1 : Int)
    (hR : Rlo ≤ Rhi) (hS : Slo ≤ Shi) (hRF : R < F) :
    (∀ pr ps : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Slo ≤ ps.lo → ps.hi ≤ Shi →
      ∀ r s, ReqEdge R F 0 0 r → StabK v (S0 + 0) (S1 - 0) s → SpecK b v pr ps r s) ↔
    (S0 + Shi ≤ R + Rlo ∧ F + Rhi ≤ S1 + Slo) := by
  rw [steer_edges_K b v Rlo Rhi Slo Shi R F S0 S1 0 0 hR hS hRF (by omega) (by omega)]; omega

/-! ### Steer: the X counter-traces at binary-edge equality (1-tick windows, `a = 1, c = 0`)

Numbers: request rises at `R = 1000`, falls at `F = 3000`, read through
300 ps; select (token `v = 1`) rises at `S0 = 800`, falls at `S1 = 4000`,
read through 500 ps. Setup at EQUALITY in edge times: `800 + 500 = 1000 + 300`
(the binary iff is satisfied). Every edge is X for the tick before it. -/

def rX (R F : Int) (x : Int) : K3 :=
  if x = R - 1 ∨ x = F - 1 then .x else kb (decide (R ≤ x ∧ x < F))
def sX (S0 S1 : Int) (x : Int) : K3 :=
  if x = S0 - 1 ∨ x = S1 - 1 then .x else kb (decide (S0 ≤ x ∧ x < S1))

theorem rX_edge (R F : Int) (hRF : R + 1 < F) : ReqEdge R F 1 0 (rX R F) := by
  refine ⟨fun x hx => ?_, fun x h1 h2 => ?_⟩
  · have e1 : ¬ (x = R - 1 ∨ x = F - 1) := by omega
    have e2 : ¬ (R ≤ x ∧ x < F) := by omega
    simp [rX, e1, e2]
  · have e1 : ¬ (x = R - 1 ∨ x = F - 1) := by omega
    have e2 : R ≤ x ∧ x < F := by omega
    simp [rX, e1, e2]

theorem sX_stab (S0 S1 : Int) : StabK true (S0 + 0) (S1 - 1) (sX S0 S1) := by
  intro x h1 h2
  have e1 : ¬ (x = S0 - 1 ∨ x = S1 - 1) := by omega
  have e2 : S0 ≤ x ∧ x < S1 := by omega
  simp [sX, e1, e2]

/-- Setup at edge-equality: at 1299 the UNSELECTED branch O5 reads X
(request read in its rise window, select read in its rise window). -/
theorem steer_ct_setup_x :
    outK false (rX 1000 3000 ((Rd.const 300).σ 1299)) (sX 800 4000 ((Rd.const 500).σ 1299)) = .x ∧
    kgate (rX 1000 3000 ((Rd.const 300).σ 1299)) (true == false) = .f ∧
    (800 : Int) + 500 = 1000 + 300 := by
  decide

/-- Hold at edge-equality (`F + 600 = S1 + 300`, request through 600 ps,
select through 300 ps, `S1 = 3300`): at 3599 the unselected O5 reads X. -/
theorem steer_ct_hold_x :
    outK false (rX 1000 3000 ((Rd.const 600).σ 3599)) (sX 800 3300 ((Rd.const 300).σ 3599)) = .x ∧
    kgate (rX 1000 3000 ((Rd.const 600).σ 3599)) (true == false) = .f ∧
    (3000 : Int) + 600 = 3300 + 300 := by
  decide

/-- Non-vacuity (steer, K3, X on every edge): box `req ∈ [200, 400]`,
`s ∈ [300, 600]`, `R = 1000, F = 3000, S0 = 500, S1 = 4000`: strict margins,
and for that trace pair through (300, 450) the spec holds at every instant,
O6 is definite 1 at 1400 and O5 definite 0 at every instant. -/
theorem steer_witness_K :
    ((500 : Int) + 600 < 1000 + 200 ∧ (3000 : Int) + 400 < 4000 + 300) ∧
    ReqEdge 1000 3000 1 0 (rX 1000 3000) ∧ StabK true (500 + 0) (4000 - 1) (sX 500 4000) ∧
    SpecK true true (Rd.const 300) (Rd.const 450) (rX 1000 3000) (sX 500 4000) ∧
    SpecK false true (Rd.const 300) (Rd.const 450) (rX 1000 3000) (sX 500 4000) ∧
    outK true (rX 1000 3000 ((Rd.const 300).σ 1400)) (sX 500 4000 ((Rd.const 450).σ 1400)) = .t := by
  refine ⟨by decide, rX_edge _ _ (by decide), sX_stab _ _, ?_, ?_, by decide⟩
  · exact steer_ok_K true true _ _ (1000 - 1) (3000 + 0) (500 + 0) (4000 - 1) _ _
      (reqEdge_supp (rX_edge _ _ (by decide))) (sX_stab _ _) (by simp [Rd.const]) (by simp [Rd.const])
  · exact steer_ok_K false true _ _ (1000 - 1) (3000 + 0) (500 + 0) (4000 - 1) _ _
      (reqEdge_supp (rX_edge _ _ (by decide))) (sX_stab _ _) (by simp [Rd.const]) (by simp [Rd.const])

/-! ## 4. `bd_mux` joins (`uj0` `0000_AE08_0000_AE08`, `uj1` `0000_EA80_0000_EA80`) -/

open Formal.Cells.LibGapMux (jK jB specB)

/-- **H_PIN_READ**, K3, feedback included (rst I4 reads 0 from 0 on). -/
def LutEqK (b : Bool) (pr pc ps pq : Rd) (r c s j : Int → K3) : Prop :=
  ∀ t, 0 ≤ t → j t = jK b (r (pr.σ t)) (c (pc.σ t)) (s (ps.σ t)) (j (pq.σ t))

/-- **H_RESET**: definite 0 before 0. -/
def RestK (j : Int → K3) : Prop := ∀ t, t < 0 → j t = .f

/-- The spec, K3: the Kleene C-element on (request read, ctl_req read gated by
the TOKEN's decode) with its own feedback read. -/
def JSpecK (b v : Bool) (pr pc pq : Rd) (r c j : Int → K3) : Prop :=
  ∀ t, 0 ≤ t → j t = cK [r (pr.σ t), kgate (c (pc.σ t)) (v == b)] (j (pq.σ t))

/-- Pointwise, real INITs, all 3^4 K3 inputs: if `s` reads the token value
whenever ctl_req is not definite 0, the join IS the spec function. -/
theorem jK_sel : ∀ (b v : Bool) (r c s q : K3), (c ≠ .f → s = kb v) →
    jK b r c s q = cK [r, kgate c (v == b)] q := by decide
theorem jK_kb : ∀ b r c s q : Bool, jK b (kb r) (kb c) (kb s) (kb q) = kb (jB b r c s q) := by decide
theorem cK_kb : ∀ b v r c q : Bool, cK [kb r, kgate (kb c) (v == b)] (kb q) = kb (specB b v r c q) := by
  decide
theorem cK_low : ∀ r : K3, cK [r, .f] .f = .f := by decide
/-- The join stays 0 (from 0) while ctl_req reads 0 or `s` reads the other branch. -/
theorem jK_low : ∀ (b : Bool) (r c s : K3), (c = .f ∨ s = kb (!b)) → jK b r c s .f = .f := by decide
/-- X on BOTH ctl_req and `s` with the request waiting and the join at 0: X. -/
theorem jK_xx : ∀ b : Bool, jK b .t .x .x .f = .x := by decide

/-- **Sufficient, K3, any read maps** (no hypothesis on the request pin, the
feedback pin, the reset or the loop). -/
theorem join_ok_K (b v : Bool) (pr pc ps pq : Rd) (Ca Cb S0 S1 : Int) (r c s j : Int → K3)
    (H_CTL_SUPP : Supp Ca Cb c) (H_S_STABLE_K : StabK v S0 S1 s) (H_PIN_READ : LutEqK b pr pc ps pq r c s j)
    (H_SETUP_PIN : S0 + ps.hi ≤ Ca + pc.lo) (H_HOLD_PIN : Cb + pc.hi ≤ S1 + ps.lo) :
    JSpecK b v pr pc pq r c j := by
  intro t ht
  rw [H_PIN_READ t ht]
  apply jK_sel
  intro hc
  obtain ⟨h1, h2⟩ := H_CTL_SUPP _ hc
  have := pc.ge t; have := pc.le t; have := ps.ge t; have := ps.le t
  exact H_S_STABLE_K _ (by omega) (by omega)

/-- Unselected join: definite 0 at EVERY instant (X anywhere else allowed by the
spec's inputs: request, ctl_req inside its support). -/
theorem unsel_definite (b v : Bool) (hvb : v ≠ b) (pr pc pq : Rd) (hq : 1 ≤ pq.lo)
    (r c j : Int → K3) (hS : JSpecK b v pr pc pq r c j) (hR : RestK j) : ∀ t, j t = .f := by
  have hf : (v == b) = false := by cases v <;> cases b <;> simp_all
  apply int_ind (fun t => j t = .f) hR
  intro t ht ih
  rw [hS t ht, hf, ih _ (by have := pq.le t; omega)]
  exact cK_low _

def JoinSafeK (b v : Bool) (Rlo Rhi Clo Chi Slo Shi Qlo Qhi Ca Cb S0 S1 : Int) : Prop :=
  ∀ pr pc ps pq : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Clo ≤ pc.lo → pc.hi ≤ Chi →
    Slo ≤ ps.lo → ps.hi ≤ Shi → Qlo ≤ pq.lo → pq.hi ≤ Qhi →
    ∀ r c s j : Int → K3, Supp Ca Cb c → StabK v S0 S1 s → LutEqK b pr pc ps pq r c s j → RestK j →
      JSpecK b v pr pc pq r c j

/-- The left side of `LibGapMux.join_box_exact` (binary). -/
def JoinSafeB (b v : Bool) (Rlo Rhi Clo Chi Slo Shi Qlo Qhi Ca Cb S0 S1 : Int) : Prop :=
  ∀ pr pc ps pq : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Clo ≤ pc.lo → pc.hi ≤ Chi →
    Slo ≤ ps.lo → ps.hi ≤ Shi → Qlo ≤ pq.lo → pq.hi ≤ Qhi →
    ∀ r s j : Int → Bool, Stable s v S0 S1 → LibGapMux.LutEq b pr pc ps pq r (pulse Ca Cb) s j →
      LibGapMux.Rest j → LibGapMux.JSpec b v pr pc pq r (pulse Ca Cb) j

/-- Binary traces embed: any K3 statement over a ctl_req class containing the
binary pulse gives the binary statement. -/
theorem join_K_to_B (b v : Bool) (Rlo Rhi Clo Chi Slo Shi Qlo Qhi Ca Cb S0 S1 : Int)
    (P : (Int → K3) → Prop) (hP : P (fun x => kb (pulse Ca Cb x)))
    (h : ∀ pr pc ps pq : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Clo ≤ pc.lo → pc.hi ≤ Chi →
      Slo ≤ ps.lo → ps.hi ≤ Shi → Qlo ≤ pq.lo → pq.hi ≤ Qhi →
      ∀ r c s j : Int → K3, P c → StabK v S0 S1 s → LutEqK b pr pc ps pq r c s j → RestK j →
        JSpecK b v pr pc pq r c j) :
    JoinSafeB b v Rlo Rhi Clo Chi Slo Shi Qlo Qhi Ca Cb S0 S1 := by
  intro pr pc ps pq a1 a2 a3 a4 a5 a6 a7 a8 r s j hs hL hR t ht
  have hK := h pr pc ps pq a1 a2 a3 a4 a5 a6 a7 a8 (fun x => kb (r x)) (fun x => kb (pulse Ca Cb x))
    (fun x => kb (s x)) (fun x => kb (j x)) hP (stabK_of v S0 S1 s hs)
    (fun u hu => by
      show kb (j u) = jK b (kb (r (pr.σ u))) (kb (pulse Ca Cb (pc.σ u))) (kb (s (ps.σ u))) (kb (j (pq.σ u)))
      rw [hL u hu, jK_kb])
    (fun u hu => by show kb (j u) = .f; rw [hR u hu]; rfl) t ht
  exact kb_inj _ _ (hK.trans (cK_kb b v (r (pr.σ t)) (pulse Ca Cb (pc.σ t)) (j (pq.σ t))))

/-- **Headline (mux join), K3 on every pin, exact over the box.** Same right
side as `LibGapMux.join_box_exact`, with `Ca, Cb` ctl_req's not-definite-0
support. The request and FEEDBACK pins drop out, X on them included. -/
theorem join_box_exact_K (b v : Bool) (Rlo Rhi Clo Chi Slo Shi Qlo Qhi Ca Cb S0 S1 : Int)
    (hR : Rlo ≤ Rhi) (hC : Clo ≤ Chi) (hS : Slo ≤ Shi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (hCF : Ca < Cb) (hRst : 0 ≤ Ca + Clo) :
    JoinSafeK b v Rlo Rhi Clo Chi Slo Shi Qlo Qhi Ca Cb S0 S1 ↔
      (S0 + Shi ≤ Ca + Clo ∧ Cb + Chi ≤ S1 + Slo) := by
  constructor
  · intro h
    exact (LibGapMux.join_box_exact b v Rlo Rhi Clo Chi Slo Shi Qlo Qhi Ca Cb S0 S1
      hR hC hS hQ1 hQ hCF hRst).mp (join_K_to_B b v _ _ _ _ _ _ _ _ _ _ _ _ _ (supp_pulse Ca Cb) h)
  · rintro ⟨h1, h2⟩ pr pc ps pq _ _ a3 a4 a5 a6 _ _ r c s j hc hs hL _
    exact join_ok_K b v pr pc ps pq Ca Cb S0 S1 r c s j hc hs hL (by omega) (by omega)

/-- K3 join safety ⟺ binary join safety (definite-window coordinates). -/
theorem join_K_iff_binary (b v : Bool) (Rlo Rhi Clo Chi Slo Shi Qlo Qhi Ca Cb S0 S1 : Int)
    (hR : Rlo ≤ Rhi) (hC : Clo ≤ Chi) (hS : Slo ≤ Shi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (hCF : Ca < Cb) (hRst : 0 ≤ Ca + Clo) :
    JoinSafeK b v Rlo Rhi Clo Chi Slo Shi Qlo Qhi Ca Cb S0 S1 ↔
      JoinSafeB b v Rlo Rhi Clo Chi Slo Shi Qlo Qhi Ca Cb S0 S1 :=
  (join_box_exact_K b v _ _ _ _ _ _ _ _ _ _ _ _ hR hC hS hQ1 hQ hCF hRst).trans
    (LibGapMux.join_box_exact b v _ _ _ _ _ _ _ _ _ _ _ _ hR hC hS hQ1 hQ hCF hRst).symm

/-- **Join, binary-edge form (H_X_UNIFORM), exact**: ctl_req edges `Cr`, `Cf`
with X windows `[T - xa, T + xc)`; `s` definite on `[S0 + xc, S1 - xa)`.
Setup and hold each gain `w = xa + xc`. -/
theorem join_edges_K (b v : Bool) (Rlo Rhi Clo Chi Slo Shi Qlo Qhi Cr Cf S0 S1 xa xc : Int)
    (hR : Rlo ≤ Rhi) (hC : Clo ≤ Chi) (hS : Slo ≤ Shi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (hCF : Cr < Cf) (ha : 0 ≤ xa) (hc : 0 ≤ xc) (hRst : 0 ≤ Cr - xa + Clo) :
    (∀ pr pc ps pq : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Clo ≤ pc.lo → pc.hi ≤ Chi →
      Slo ≤ ps.lo → ps.hi ≤ Shi → Qlo ≤ pq.lo → pq.hi ≤ Qhi →
      ∀ r c s j : Int → K3, ReqEdge Cr Cf xa xc c → StabK v (S0 + xc) (S1 - xa) s →
        LutEqK b pr pc ps pq r c s j → RestK j → JSpecK b v pr pc pq r c j) ↔
    (S0 + Shi + (xa + xc) ≤ Cr + Clo ∧ Cf + Chi + (xa + xc) ≤ S1 + Slo) := by
  constructor
  · intro h
    have := (LibGapMux.join_box_exact b v Rlo Rhi Clo Chi Slo Shi Qlo Qhi (Cr - xa) (Cf + xc)
      (S0 + xc) (S1 - xa) hR hC hS hQ1 hQ (by omega) hRst).mp
      (join_K_to_B b v _ _ _ _ _ _ _ _ _ _ _ _ _ (reqEdge_pulse Cr Cf xa xc ha hc) h)
    omega
  · rintro ⟨h1, h2⟩ pr pc ps pq _ _ a3 a4 a5 a6 _ _ r c s j hc' hs hL _
    exact join_ok_K b v pr pc ps pq (Cr - xa) (Cf + xc) (S0 + xc) (S1 - xa) r c s j
      (reqEdge_supp hc') hs hL (by omega) (by omega)

/-- **Strict** (one tick of X per edge, either convention). -/
theorem join_strict_K (b v : Bool) (Rlo Rhi Clo Chi Slo Shi Qlo Qhi Cr Cf S0 S1 xa xc : Int)
    (hR : Rlo ≤ Rhi) (hC : Clo ≤ Chi) (hS : Slo ≤ Shi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (hCF : Cr < Cf) (ha : 0 ≤ xa) (hc : 0 ≤ xc) (hw : xa + xc = 1) (hRst : 0 ≤ Cr - xa + Clo) :
    (∀ pr pc ps pq : Rd, Rlo ≤ pr.lo → pr.hi ≤ Rhi → Clo ≤ pc.lo → pc.hi ≤ Chi →
      Slo ≤ ps.lo → ps.hi ≤ Shi → Qlo ≤ pq.lo → pq.hi ≤ Qhi →
      ∀ r c s j : Int → K3, ReqEdge Cr Cf xa xc c → StabK v (S0 + xc) (S1 - xa) s →
        LutEqK b pr pc ps pq r c s j → RestK j → JSpecK b v pr pc pq r c j) ↔
    (S0 + Shi < Cr + Clo ∧ Cf + Chi < S1 + Slo) := by
  rw [join_edges_K b v _ _ _ _ _ _ _ _ Cr Cf S0 S1 xa xc hR hC hS hQ1 hQ hCF ha hc hRst]; omega

/-! ### Join: X counter-traces at binary-edge equality (1-tick windows, `xa = 1, xc = 0`)

uj0 (`b = false`), token `v = 1` (uj0 UNSELECTED), x_req waiting (definite 1),
ctl_req `[1000, 3000)` through 300 ps, loop 50 ps. -/

theorem rX_lo {R F x : Int} (hRF : R < F) (h : x < R - 1) : rX R F x = .f := by
  have e1 : ¬ (x = R - 1 ∨ x = F - 1) := by omega
  have e2 : ¬ (R ≤ x ∧ x < F) := by omega
  simp [rX, e1, e2]
theorem sX_in {S0 S1 x : Int} (h1 : S0 ≤ x) (h2 : x < S1 - 1) : sX S0 S1 x = .t := by
  have e1 : ¬ (x = S0 - 1 ∨ x = S1 - 1) := by omega
  have e2 : S0 ≤ x ∧ x < S1 := by omega
  simp [sX, e1, e2]

/-- Setup at edge-equality (`s` rises at 800 read through 500 ps:
`800 + 500 = 1000 + 300`): uj0 reads X at 1299, the spec there is definite 0,
on EVERY trace obeying H_PIN_READ + H_RESET. -/
theorem join_ct_setup_x (j : Int → K3)
    (hL : LutEqK false (Rd.const 0) (Rd.const 300) (Rd.const 500) (Rd.const 50)
      (fun _ => .t) (rX 1000 3000) (sX 800 4000) j) (hR : RestK j) :
    j 1299 = .x ∧
    cK [.t, kgate (rX 1000 3000 ((Rd.const 300).σ 1299)) (true == false)] (j ((Rd.const 50).σ 1299)) = .f := by
  have hlow : ∀ u, u < 1299 → j u = .f := by
    apply int_ind (fun u => u < 1299 → j u = .f) (fun u hu _ => hR u hu)
    intro u hu ih hlt
    rw [hL u hu, ih _ (by show u - 50 < u; omega) (by show u - 50 < 1299; omega)]
    exact jK_low false _ _ _ (Or.inl (rX_lo (by decide) (by show u - 300 < 1000 - 1; omega)))
  have e : j ((Rd.const 50).σ 1299) = .f := hlow _ (by decide)
  refine ⟨?_, ?_⟩
  · rw [hL 1299 (by decide), e]; decide
  · rw [e]; decide

/-- Hold at edge-equality (`s` falls at `S1 = 3000`, read through 300 ps:
`3000 + 300 = 3000 + 300`): uj0 reads X at 3299, spec definite 0. -/
theorem join_ct_hold_x (j : Int → K3)
    (hL : LutEqK false (Rd.const 0) (Rd.const 300) (Rd.const 300) (Rd.const 50)
      (fun _ => .t) (rX 1000 3000) (sX 800 3000) j) (hR : RestK j) :
    j 3299 = .x ∧
    cK [.t, kgate (rX 1000 3000 ((Rd.const 300).σ 3299)) (true == false)] (j ((Rd.const 50).σ 3299)) = .f := by
  have hlow : ∀ u, u < 3299 → j u = .f := by
    apply int_ind (fun u => u < 3299 → j u = .f) (fun u hu _ => hR u hu)
    intro u hu ih hlt
    rw [hL u hu, ih _ (by show u - 50 < u; omega) (by show u - 50 < 3299; omega)]
    apply jK_low false
    by_cases h : u - 300 < 1000 - 1
    · exact Or.inl (rX_lo (by decide) h)
    · exact Or.inr (sX_in (show (800 : Int) ≤ u - 300 by omega) (show u - 300 < 3000 - 1 by omega))
  have e : j ((Rd.const 50).σ 3299) = .f := hlow _ (by decide)
  refine ⟨?_, ?_⟩
  · rw [hL 3299 (by decide), e]; decide
  · rw [e]; decide

/-- Non-vacuity (join, K3, 1-tick X on every edge, strict margins): the trace
`run` built by `LibGapLatch.run` (feedback 100 ps) meets H_PIN_READ and
H_RESET; then uj0 (unselected, x_req waiting) is definite 0 at every instant
and uj1 (selected, y_req waiting) is definite 1 at 1400. -/
def jfK (b : Bool) (dr dc ds : Int) (r c s : Int → K3) (t : Int) (q : K3) : K3 :=
  jK b (r (t - dr)) (c (t - dc)) (s (t - ds)) q

def wjK (b : Bool) : Int → K3 :=
  LibGapLatch.run (jfK b 0 300 450 (fun _ => .t) (rX 1000 3000) (sX 500 4000)) .f 100 (by decide)

theorem wjK_luteq (b : Bool) :
    LutEqK b (Rd.const 0) (Rd.const 300) (Rd.const 450) (Rd.const 100) (fun _ => .t)
      (rX 1000 3000) (sX 500 4000) (wjK b) := by
  intro t ht
  exact LibGapLatch.run_eq _ _ 100 (by decide) t ht

theorem wjK_rest (b : Bool) : RestK (wjK b) := fun t ht => LibGapLatch.run_neg _ _ 100 (by decide) t ht

theorem join_witness_K :
    ((500 : Int) + 450 < 1000 + 300 ∧ (3000 : Int) + 300 < 4000 + 450) ∧
    (∀ t, wjK false t = .f) ∧ wjK true 1400 = .t := by
  have hs := sX_stab 500 4000
  have hc := reqEdge_supp (rX_edge 1000 3000 (by decide))
  have S0 := join_ok_K false true _ _ _ _ _ _ _ _ _ _ _ _ hc hs (wjK_luteq false)
    (by simp [Rd.const]) (by simp [Rd.const])
  have S1 := join_ok_K true true _ _ _ _ _ _ _ _ _ _ _ _ hc hs (wjK_luteq true)
    (by simp [Rd.const]) (by simp [Rd.const])
  refine ⟨by decide, unsel_definite false true (by decide) _ _ _ (by simp [Rd.const]) _ _ _ S0 (wjK_rest false), ?_⟩
  rw [S1 1400 (by decide)]
  decide

/-! ## 5. `bd_latch`: already Kleene (LibGapLatch); the uniform-split edge form -/

/-- `LibGapLatch.box_exact` IS the K3 iff (every pin K3, X anywhere outside its
window, real INITs through `latM`). In binary-edge times under H_X_UNIFORM
(enable edges `Ton`, `Toff`, data edges `Td`, `Tnew`, each X on `[T - a, T + c)`)
all three conditions gain `w = a + c`, for ANY split (`box_exact_edges` is the
`c = 0` case). -/
theorem latch_edges_uniform (v : Bool) (Ton Toff Td Tnew a c Dlo Dhi Elo Ehi Qlo Qhi : Int)
    (hD : Dlo ≤ Dhi) (hE : Elo ≤ Ehi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hAB : Ton + c ≤ Toff - a) (H_T0 : 0 ≤ Ton + c + Elo) :
    LibGapLatch.SafeBox v (Ton + c) (Toff - a) (Toff + c) (Td + c) (Tnew - a) Dlo Dhi Elo Ehi Qlo Qhi ↔
      (Ton + Ehi + Qhi + (a + c) ≤ Toff + Elo ∧ Td + Dhi + Qhi + (a + c) ≤ Toff + Elo ∧
        Toff + Ehi + (a + c) ≤ Tnew + Dlo) := by
  rw [LibGapLatch.box_exact v _ _ _ _ _ _ _ _ _ _ _ hD hE hQ1 hQ hAB (by omega) H_T0]; omega

theorem latch_strict_uniform (v : Bool) (Ton Toff Td Tnew a c Dlo Dhi Elo Ehi Qlo Qhi : Int)
    (hD : Dlo ≤ Dhi) (hE : Elo ≤ Ehi) (hQ1 : 1 ≤ Qlo) (hQ : Qlo ≤ Qhi)
    (ha : 0 ≤ a) (hc : 0 ≤ c) (hw : a + c = 1) (hAB : Ton + c ≤ Toff - a) (H_T0 : 0 ≤ Ton + c + Elo) :
    LibGapLatch.SafeBox v (Ton + c) (Toff - a) (Toff + c) (Td + c) (Tnew - a) Dlo Dhi Elo Ehi Qlo Qhi ↔
      (Ton + Ehi + Qhi < Toff + Elo ∧ Td + Dhi + Qhi < Toff + Elo ∧ Toff + Ehi < Tnew + Dlo) := by
  rw [latch_edges_uniform v Ton Toff Td Tnew a c Dlo Dhi Elo Ehi Qlo Qhi hD hE hQ1 hQ ha hc hAB H_T0]
  omega

/-! ## 6. `bdc_muxn`: the SELECTED join (decode LUT3 → wire → `bd_c2`), K3 index bits -/

open Formal.Cells.LibGapMuxN (bit0 bit1 dec InBox SelCond)
open Formal.Cells.AMergeGates (SEL0 SEL1 SEL2 C2 c2)

/-- Decode `k`, Kleene, real inferred INITs and pin orders (H_YOSYS_MAP). -/
def decK : Nat → K3 → K3 → K3 → K3
  | 0, s0, s1, c => lutK SEL0 [s0, s1, c]
  | 1, s0, s1, c => lutK SEL1 [s1, s0, c]
  | _, s0, s1, c => lutK SEL2 [s0, s1, c]

/-- `bd_c2`, Kleene, real INIT (pins a b q, rst read 0). -/
def c2K (a d q : K3) : K3 := lutK C2 [a, d, q, .f, .f, .f]

theorem decK_sel (k : Nat) (hk : k < 3) : ∀ (s0 s1 c : K3),
    (c ≠ .f → s0 = kb (bit0 k) ∧ s1 = kb (bit1 k)) → decK k s0 s1 c = c := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  all_goals decide

theorem decK_kb (k : Nat) (hk : k < 3) : ∀ s0 s1 c : Bool,
    decK k (kb s0) (kb s1) (kb c) = kb (dec k s0 s1 c) := by
  obtain rfl | rfl | rfl : k = 0 ∨ k = 1 ∨ k = 2 := by omega
  all_goals decide

theorem c2K_kb : ∀ a d q : Bool, c2K (kb a) (kb d) (kb q) = kb (c2 a d q) := by decide

def DecEqK (k : Nat) (p0 p1 pc : Rd) (s0 s1 c D : Int → K3) : Prop :=
  ∀ t, D t = decK k (s0 (p0.σ t)) (s1 (p1.σ t)) (c (pc.σ t))
def JEqK (pr pd pq : Rd) (r D j : Int → K3) : Prop :=
  ∀ t, 0 ≤ t → j t = c2K (r (pr.σ t)) (D (pd.σ t)) (j (pq.σ t))
/-- The spec, K3: the decode replaced by the token's value (ctl_req read
through the composite map `pc ∘ pd`). -/
def NSpecK (k v : Nat) (pr pd pc pq : Rd) (r c j : Int → K3) : Prop :=
  ∀ t, 0 ≤ t → j t = c2K (r (pr.σ t)) (kgate (c (pc.σ (pd.σ t))) (v == k)) (j (pq.σ t))

/-- Selected-join box safety, K3 on every pin (index bits, ctl_req, decode
output, request, feedback). -/
def MuxSafeK (k : Nat) (Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi A0 A1 B0 B1 : Int)
    (Pc : (Int → K3) → Prop) : Prop :=
  ∀ pr pd pc p0 p1 pq : Rd, InBox Rlo Rhi pr → InBox Dlo Dhi pd → InBox Clo Chi pc →
    InBox Alo Ahi p0 → InBox Blo Bhi p1 → InBox Qlo Qhi pq →
    ∀ r c s0 s1 D j : Int → K3, Pc c → StabK (bit0 k) A0 A1 s0 → StabK (bit1 k) B0 B1 s1 →
      DecEqK k p0 p1 pc s0 s1 c D → JEqK pr pd pq r D j → RestK j → NSpecK k k pr pd pc pq r c j

/-- Sufficient, K3: the decode output IS ctl_req's reading at every instant. -/
theorem muxn_ok_K (k : Nat) (hk : k < 3) (Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Ca Cb A0 A1 B0 B1 : Int)
    (hc : SelCond Clo Chi Alo Ahi Blo Bhi Ca Cb A0 A1 B0 B1) :
    MuxSafeK k Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi A0 A1 B0 B1 (Supp Ca Cb) := by
  intro pr pd pc p0 p1 pq _ _ hC hA hB _ r c s0 s1 D j hcs hs0 hs1 hD hJ _ t ht
  have hDu : ∀ u, D u = c (pc.σ u) := by
    intro u
    rw [hD u]
    apply decK_sel k hk
    intro hcu
    obtain ⟨h1, h2⟩ := hcs _ hcu
    unfold SelCond at hc
    have := pc.ge u; have := pc.le u; have := p0.ge u; have := p0.le u
    have := p1.ge u; have := p1.le u
    have := hC.1; have := hC.2; have := hA.1; have := hA.2; have := hB.1; have := hB.2
    exact ⟨hs0 _ (by omega) (by omega), hs1 _ (by omega) (by omega)⟩
  rw [hJ t ht, hDu]
  simp [kgate]

/-- Binary traces embed (any ctl_req class containing the binary pulse). -/
theorem muxn_K_to_B (k : Nat) (hk : k < 3) (Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Ca Cb A0 A1 B0 B1 : Int)
    (Pc : (Int → K3) → Prop) (hP : Pc (fun x => kb (pulse Ca Cb x)))
    (h : MuxSafeK k Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi A0 A1 B0 B1 Pc) :
    LibGapMuxN.BoxOK1 k k Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Ca Cb A0 A1 B0 B1 := by
  intro s0 s1 hs0 hs1 pr pd pc p0 p1 pq a1 a2 a3 a4 a5 a6 r D j hD hJ hR t ht
  have hK := h pr pd pc p0 p1 pq a1 a2 a3 a4 a5 a6 (fun x => kb (r x)) (fun x => kb (pulse Ca Cb x))
    (fun x => kb (s0 x)) (fun x => kb (s1 x)) (fun x => kb (D x)) (fun x => kb (j x)) hP
    (stabK_of _ _ _ s0 hs0) (stabK_of _ _ _ s1 hs1)
    (fun u => by
      show kb (D u) = decK k (kb (s0 (p0.σ u))) (kb (s1 (p1.σ u))) (kb (pulse Ca Cb (pc.σ u)))
      rw [hD u, decK_kb k hk])
    (fun u hu => by
      show kb (j u) = c2K (kb (r (pr.σ u))) (kb (D (pd.σ u))) (kb (j (pq.σ u)))
      rw [hJ u hu, c2K_kb])
    (fun u hu => by show kb (j u) = .f; rw [hR u hu]; rfl) t ht
  have e := hK.trans (by
    show c2K (kb (r (pr.σ t))) (kgate (kb (pulse Ca Cb (pc.σ (pd.σ t)))) (k == k)) (kb (j (pq.σ t))) = _
    rw [kgate_kb, c2K_kb])
  exact kb_inj _ _ e

/-- **Headline (bdc_muxn selected join), K3 on every pin, exact over the box.**
Same right side as `LibGapMuxN.sel_box_exact` (`SelCond`: per index bit,
setup and hold against ctl_req's support at the DECODE pins). -/
theorem muxn_sel_box_exact_K (k : Nat) (hk : k < 3)
    (Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Ca Cb A0 A1 B0 B1 : Int)
    (hRb : Rlo ≤ Rhi) (hDb : Dlo ≤ Dhi) (hCb : Clo ≤ Chi) (hAb : Alo ≤ Ahi) (hBb : Blo ≤ Bhi)
    (hQ1 : 1 ≤ Qlo) (hQb : Qlo ≤ Qhi) (hCF : Ca < Cb) (hRst : 0 ≤ Ca + Clo + Dlo) :
    MuxSafeK k Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi A0 A1 B0 B1 (Supp Ca Cb) ↔
      SelCond Clo Chi Alo Ahi Blo Bhi Ca Cb A0 A1 B0 B1 := by
  constructor
  · intro h
    exact (LibGapMuxN.sel_box_exact (k := k) (hk := hk) (Rlo := Rlo) (Rhi := Rhi) (Dlo := Dlo) (Dhi := Dhi)
      (Clo := Clo) (Chi := Chi) (Alo := Alo) (Ahi := Ahi) (Blo := Blo) (Bhi := Bhi) (Qlo := Qlo) (Qhi := Qhi)
      (Cr := Ca) (Cf := Cb) (hRb := hRb) (hDb := hDb) (hCb := hCb) (hAb := hAb) (hBb := hBb) (hQ1 := hQ1)
      (hQb := hQb) (hCF := hCF) (hRst := hRst) (A0 := A0) (A1 := A1) (B0 := B0) (B1 := B1)).mp
      (muxn_K_to_B k hk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (supp_pulse Ca Cb) h)
  · exact muxn_ok_K k hk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _

/-- **bdc_muxn selected join, binary-edge form (H_X_UNIFORM), exact**: ctl_req
edges `Cr`, `Cf`, index bit `i` binary window `[Si0, Si1)`, every edge X on
`[T - a, T + c)`. Each of the four per-bit inequalities gains `w = a + c`. -/
theorem muxn_edges_K (k : Nat) (hk : k < 3)
    (Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi Cr Cf A0 A1 B0 B1 a c : Int)
    (hRb : Rlo ≤ Rhi) (hDb : Dlo ≤ Dhi) (hCb : Clo ≤ Chi) (hAb : Alo ≤ Ahi) (hBb : Blo ≤ Bhi)
    (hQ1 : 1 ≤ Qlo) (hQb : Qlo ≤ Qhi) (hCF : Cr < Cf) (ha : 0 ≤ a) (hc : 0 ≤ c)
    (hRst : 0 ≤ Cr - a + Clo + Dlo) :
    MuxSafeK k Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi
      (A0 + c) (A1 - a) (B0 + c) (B1 - a) (ReqEdge Cr Cf a c) ↔
    (A0 + Ahi + (a + c) ≤ Cr + Clo ∧ Cf + Chi + (a + c) ≤ A1 + Alo ∧
      B0 + Bhi + (a + c) ≤ Cr + Clo ∧ Cf + Chi + (a + c) ≤ B1 + Blo) := by
  constructor
  · intro h
    have := (LibGapMuxN.sel_box_exact (k := k) (hk := hk) (Rlo := Rlo) (Rhi := Rhi) (Dlo := Dlo) (Dhi := Dhi)
      (Clo := Clo) (Chi := Chi) (Alo := Alo) (Ahi := Ahi) (Blo := Blo) (Bhi := Bhi) (Qlo := Qlo) (Qhi := Qhi)
      (Cr := Cr - a) (Cf := Cf + c) (hRb := hRb) (hDb := hDb) (hCb := hCb) (hAb := hAb) (hBb := hBb)
      (hQ1 := hQ1) (hQb := hQb) (hCF := by omega) (hRst := hRst)
      (A0 := A0 + c) (A1 := A1 - a) (B0 := B0 + c) (B1 := B1 - a)).mp
      (muxn_K_to_B k hk _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (reqEdge_pulse Cr Cf a c ha hc) h)
    unfold SelCond at this
    omega
  · intro hcond pr pd pc p0 p1 pq i1 i2 i3 i4 i5 i6 r cc s0 s1 D j hce
    exact muxn_ok_K k hk Rlo Rhi Dlo Dhi Clo Chi Alo Ahi Blo Bhi Qlo Qhi (Cr - a) (Cf + c)
      (A0 + c) (A1 - a) (B0 + c) (B1 - a) (by unfold SelCond; omega)
      pr pd pc p0 p1 pq i1 i2 i3 i4 i5 i6 r cc s0 s1 D j (reqEdge_supp hce)

end Formal.Cells.KleeneBox
