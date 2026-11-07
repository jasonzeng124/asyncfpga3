import Formal.Net.CapstoneO1
import Formal.Net.CapstoneWitnessCells
import Formal.Cells.LinkExact
import Formal.Cells.OnGcdArbKappaSrv
open Formal.Core.LutList

/-!
# Probe Bbare: can a gcd_hw arbiter client withdraw an unacknowledged request?

Shard B, 2026-10-29. Note: `formal/notes/B-arb-no-withdraw.md`. Needs Mathlib (through
`OnGcdArbKappaSrv`).

`OnGcdArbKappaSrv` left two thresholds: D1 (κ ≤ 0.0802, set by a BARE-cell race in which
client 2 withdraws a request that was never acknowledged) and D2 (κ ≤ 0.2166, the held
arbiter's four-phase handovers, under H_SETTLED). This file decides which assumptions select
D2.

## Results

1. **C's network model** (`Formal.Net`, used verbatim). `NoWithdraw c`: a request falls only
   from the acknowledged phase. `gcd_hw_arb_no_withdraw`: under C's H_CELLS and H_BUNDLE, both
   request channels of every arbiter stage of the concrete gcd_hw network satisfy it, and
   `held_until_ack`: a request, once high, stays high until its ack is high. This is a
   corollary of C's `gcd_hw_protocol`. Non-vacuity: C's witness run `chW` meets both
   hypotheses (`net_nonvacuous`). `arb_inputs`: the 18 arbiter input channels and the C
   operator kind producing each (decided over C's `ops`).
2. **Gate level, per producer cell** (B's cell models, verbatim). In the synthesized netlists
   (all four seeds), the arbiters' requests are driven by three kinds of cell: a `bd_link`
   controller, a `bd_steer` branch (`cond_br`), or another arbiter's R0.
   * link (`LinkExact`): `link_no_withdraw`. Under LinkExact's exact conjunction, the request
     node is definitely high from `U1` until the ack's rise can first be read (`Rb + Blo`).
   * steer (`LibGapSteer`): `steer_unsel_silent`. Under the rows H_SETUP_PIN/H_HOLD_PIN, the
     unselected branch is 0 at every instant. `steer_sel_held`: the selected branch is high on
     `[R + pr.hi, F + pr.lo)`. `steer_no_withdraw`: if the request driving the steer does not
     fall before the branch's ack rises (`TA ≤ F`), the branch is high until `TA + pr.lo`.
   * **counter-run, steer row violated** (`steer_withdraws`): LibGapSteer's own spurious-token
     run (setup violated by 100 ps). There the unselected branch is high exactly on
     `[1300, 1400)`. It violates gate-level no-withdrawal (`NoWdI`) for every ack that is low on
     that window. That is the withdrawn request of D1's binding race.
   * arbiter R0 (`R0_held2`, 7j): in `Scn2`, R0 stays high through `ta`, the rise of its own
     A0.
3. **H_SETTLED from causality** (`settled1_of_causal`, `settled2_of_causal`). Assume:
   - ua_k's own gate relation (7h `Run`);
   - A0 was low before its rise `ta` (H_A0_LOW_BEFORE);
   - the client releases at least `L` after A_k rose (H_CLIENT_LAT).

   Then H_SETTLED holds as soon as `wa0s + qf ≤ wa0k + ckr + L` and `ckf ≤ ckr + L`.
   Non-vacuous (`settled1_nonvacuous`), on the run `W1c`.
4. **The latency H_SETTLED needs, on the routed data** (`fset1`/`fset2`, `setTbl`):
   - `settled_safe`: with the per-client latency `L` of `setTbl`, the arc condition holds for
     every realization at κ ≤ κS2 on all 36 arbiters × 2 clients. The largest `L` is
     1590.934 ps.
   - `settled_L0_fails`: with `L = 0`, it fails on some realization for 65 of the 72 clients,
     at every κ ≥ κS2.

   So H_SETTLED is NOT implied by the arbiter's extracted arcs. It needs the client loop
   (A_k → client → r_k), which is not extracted.
5. **D2 with H_SETTLED derived** (`design_gate_held_causal`): `design_gate_held`'s four
   handover conclusions, with Scn/Scn2's H_SETTLED replaced by a causal history (any run
   `sr` with a client-latency bound from `setTbl`).
6. **Modelling finding** (`scn_no_ack_rise`): 7h's `Scn` asserts its settled initial state on
   the WHOLE past (`∀ t < t0, A1 t = true`). So no run in which A1 ever rose before `t0` (in
   particular no run from reset) satisfies `Scn`. Hence (5) takes the causal history from a
   separate trace.

## NOT covered
- The client-loop arcs (A_k → client ack pin → client LUT → r_k), so whether gcd_hw's clients
  meet `setTbl`'s latencies.
- Whether the steer rows hold on the routes. They are LibGapSteer's rows, checked by rule I/F
  per B's constraints, but not re-checked here.
- The join C-element before each steer (`TA ≤ F` is a named hypothesis).
- Rise-edge glitches inside a request's own read window (LinkExact/LibGapSteer allow any
  value there; cleanliness is H_ROUT, WinFifo).
- A bounded-window `Scn`.
- Kleene X, metastability, κ itself.
-/

namespace Formal.Cells.ArbNoWithdraw

/-! ## 1. C's network model -/

section net
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd

/-- **No withdrawal** (C's channels): the request falls only from the acknowledged phase. -/
def NoWithdraw (c : Chan) : Prop :=
  ∀ t, c.req t = true → c.req (t + 1) = false → c.ack t = true

/-- C's `SendStep` contains it. -/
theorem noWithdraw_of_protocol {c : Chan} (hp : Protocol c) : NoWithdraw c := by
  intro t h1 h2
  have := (hp.2 t).1 (by rw [h1, h2]; decide)
  rw [← this, h1]

/-- A request high at `r + 1` stays high as long as its ack stays low (four-phase hold). -/
theorem held_until_ack {c : Chan} (hn : NoWithdraw c) {r : Nat} (hr : c.req (r + 1) = true) :
    ∀ n, (∀ m, m ≤ n → c.ack (r + 1 + m) = false) → c.req (r + 1 + (n + 1)) = true := by
  intro n
  induction n with
  | zero =>
    intro h
    cases hc : c.req (r + 1 + (0 + 1)) with
    | true => rfl
    | false =>
      have := hn (r + 1) hr (by simpa using hc)
      have h0 := h 0 (Nat.le_refl 0)
      simp at h0; rw [h0] at this; exact absurd this (by decide)
  | succ n ih =>
    intro h
    have h' : c.req (r + 1 + (n + 1)) = true := ih (fun m hm => h m (by omega))
    cases hc : c.req (r + 1 + (n + 1 + 1)) with
    | true => rfl
    | false =>
      have e : r + 1 + (n + 1 + 1) = r + 1 + (n + 1) + 1 := by omega
      rw [e] at hc
      have := hn _ h' hc
      rw [h (n + 1) (Nat.le_refl _)] at this; exact absurd this (by decide)

/-- **No withdrawal at every arbiter stage of gcd_hw (C's model).** Under C's H_CELLS and
H_BUNDLE, both request channels of every `amerge` stage of the concrete network never fall
before their acknowledge is high. -/
theorem gcd_hw_arb_no_withdraw (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (o : Fin NO) (x y z : Fin NC) (w : Nat) (_ho : opAt o = .amerge x y z w) :
    NoWithdraw (ch x) ∧ NoWithdraw (ch y) := by
  have hp := gcd_hw_protocol a b ch H_CELLS H_BUNDLE
  exact ⟨noWithdraw_of_protocol (hp x), noWithdraw_of_protocol (hp y)⟩

/-- Non-vacuity: C's witness run meets H_CELLS and H_BUNDLE (C-8t). -/
theorem net_nonvacuous : ∃ ch : Fin NC → Chan,
    (∀ o : Fin NO, Cell ch (srcV Wit.A0 Wit.B0) (opAt o)) ∧ (∀ c, Held (ch c)) :=
  ⟨Wit.chW, Wit.w_cells, Wit.w_held⟩

/-- The operator kind, as a tag. -/
def kTag : K NC → String
  | .forkG .. => "forkG" | .forkH .. => "forkH" | .join .. => "join" | .bjoin .. => "bjoin"
  | .steerC .. => "steerC" | .steerD .. => "steerD" | .mux .. => "mux" | .muxn .. => "muxn"
  | .amerge .. => "amerge" | .link .. => "link" | .src .. => "src" | .sink .. => "sink"

/-- The arbiter stages' input channels. -/
def amIns : K NC → List Nat
  | .amerge x y _ _ => [x.val, y.val]
  | _ => []

/-- **The 18 arbiter input channels of C's gcd_hw network, and the operator kind producing
each** (stage order 0..8). -/
theorem arb_inputs :
    ops.flatMap amIns = [77, 106, 78, 132, 151, 187, 207, 243, 281, 315, 342, 385, 280, 314,
      16, 34, 463, 408] ∧
    (ops.flatMap amIns).map (fun c => kTag (ops.getD (prodT.getD c 0).val (.sink 0))) =
      ["steerC", "link", "steerC", "steerC", "forkG", "link", "forkG", "link", "steerC",
       "steerC", "link", "link", "steerC", "steerC", "steerC", "steerC", "amerge", "forkG"] := by
  decide +kernel

end net

/-! ## 2. Gate level, per producer cell -/

section gate

/-- **No withdrawal, gate level** (Int-ps traces at one point, e.g. the client's driver):
whenever `req` falls, `ack` was high at some instant while `req` was continuously high. -/
def NoWdI (req ack : Int → Bool) : Prop :=
  ∀ t, req t = true → req (t + 1) = false →
    ∃ u, u ≤ t ∧ ack u = true ∧ ∀ w, u ≤ w → w ≤ t → req w = true

/-! ### 2a. `bd_link` (LinkExact's exact stage contract, verbatim) -/

section link
open Formal.Cells.LinkExact
variable {P : Par} {v : Bool} {pa pb pq pr pd pe pf : LibGapSteer.Rd} {r a b d c q : Int → K3}

/-- **The link's request does not withdraw.** Under LinkExact's scope `Wf` and exact
conjunction `Conj`, for every behaviour in the box, the request node (bd_link_ctl's output,
the arbiter client's request) is DEFINITELY high from `U1` (the request rise surely read)
until `Rb + Blo`, the first instant at which the rise of its own ack_out (`Rb`, at the ack's
driver: the arbiter's ua_k output) can be read. It cannot fall while the ack is still low. -/
theorem link_no_withdraw (S : Wf P) (H : Conj P) (Bh : Beh P v pa pb pq pr pd pe pf r a b d c q) :
    ∀ t, P.U1 ≤ t → t < P.Rb + P.Blo → c t = .t := by
  intro t h1 h2
  exact (sufficient S H Bh).hi t h1 (by simp only [Par.V0]; omega)

/-- ... and the window is nonempty-and-real: at LinkExact's witness `P0` the node is high on
`[U1, Rb + Blo) = [3521, 4680)`. -/
theorem link_no_withdraw_nonvacuous (v : Bool) :
    ∃ pa pb pq pr pd pe pf r a b d c q, Beh P0 v pa pb pq pr pd pe pf r a b d c q ∧
      P0.U1 = 3521 ∧ P0.Rb + P0.Blo = 4680 ∧ ∀ t, P0.U1 ≤ t → t < P0.Rb + P0.Blo → c t = .t := by
  obtain ⟨_, _, hC, _, pa, pb, pq, pr, pd, pe, pf, r, a, b, d, c, q, hB, _⟩ := witness v
  exact ⟨pa, pb, pq, pr, pd, pe, pf, r, a, b, d, c, q, hB, by decide, by decide,
    link_no_withdraw P0_wf hC hB⟩

end link

/-! ### 2b. `bd_steer` (LibGapSteer's per-pin model, verbatim) -/

section steer
open Formal.Cells.LibGapSteer

/-- **The unselected branch never requests** (so it never withdraws): under H_S_STABLE and the
two rows, the branch with `v ≠ b` is 0 at every instant, whatever the read maps. -/
theorem steer_unsel_silent (b v : Bool) (pr ps : Rd) (R F S0 S1 : Int) (s : Int → Bool)
    (H_S_STABLE : Stable s v S0 S1) (H_SETUP_PIN : S0 + ps.hi ≤ R + pr.lo)
    (H_HOLD_PIN : F + pr.hi ≤ S1 + ps.lo) (hb : (v == b) = false) :
    ∀ t, outB b (pulse R F (pr.σ t)) (s (ps.σ t)) = false := by
  intro t
  rw [steer_pin_ok b v pr ps R F S0 S1 s H_S_STABLE H_SETUP_PIN H_HOLD_PIN t, hb, Bool.and_false]

theorem steer_unsel_noWd (b v : Bool) (pr ps : Rd) (R F S0 S1 : Int) (s : Int → Bool)
    (H_S_STABLE : Stable s v S0 S1) (H_SETUP_PIN : S0 + ps.hi ≤ R + pr.lo)
    (H_HOLD_PIN : F + pr.hi ≤ S1 + ps.lo) (hb : (v == b) = false) (ack : Int → Bool) :
    NoWdI (fun t => outB b (pulse R F (pr.σ t)) (s (ps.σ t))) ack := by
  intro t h1 _
  have h1' : outB b (pulse R F (pr.σ t)) (s (ps.σ t)) = true := h1
  rw [steer_unsel_silent b v pr ps R F S0 S1 s H_S_STABLE H_SETUP_PIN H_HOLD_PIN hb t] at h1'
  exact absurd h1' (by decide)

/-- **The selected branch is definitely high on `[R + pr.hi, F + pr.lo)`**: it follows the
request driving the steer (the join's output, high on `[R, F)`) through its pin. -/
theorem steer_sel_held (b v : Bool) (pr ps : Rd) (R F S0 S1 : Int) (s : Int → Bool)
    (H_S_STABLE : Stable s v S0 S1) (H_SETUP_PIN : S0 + ps.hi ≤ R + pr.lo)
    (H_HOLD_PIN : F + pr.hi ≤ S1 + ps.lo) (hb : (v == b) = true) :
    ∀ t, R + pr.hi ≤ t → t < F + pr.lo → outB b (pulse R F (pr.σ t)) (s (ps.σ t)) = true := by
  intro t h1 h2
  rw [steer_pin_ok b v pr ps R F S0 S1 s H_S_STABLE H_SETUP_PIN H_HOLD_PIN t, hb, Bool.and_true]
  have := pr.ge t; have := pr.le t
  simp [pulse]; omega

/-- **The selected branch does not fall before its ack rises.** If the request that drives the
steer (the join's C-element output, high on `[R, F)`) does not fall before the rise `TA` of
this branch's ack (named **H_SRC_HOLD** `TA ≤ F`: the join and the `uack` OR, not modelled
here), then the branch is definitely high from `R + pr.hi` until `TA + pr.lo`. -/
theorem steer_no_withdraw (b v : Bool) (pr ps : Rd) (R F S0 S1 TA : Int) (s : Int → Bool)
    (H_S_STABLE : Stable s v S0 S1) (H_SETUP_PIN : S0 + ps.hi ≤ R + pr.lo)
    (H_HOLD_PIN : F + pr.hi ≤ S1 + ps.lo) (hb : (v == b) = true) (H_SRC_HOLD : TA ≤ F) :
    ∀ t, R + pr.hi ≤ t → t < TA + pr.lo → outB b (pulse R F (pr.σ t)) (s (ps.σ t)) = true :=
  fun t h1 h2 => steer_sel_held b v pr ps R F S0 S1 s H_S_STABLE H_SETUP_PIN H_HOLD_PIN hb t h1
    (by omega)

/-- LibGapSteer's spurious-token run as a trace: the UNSELECTED branch `O5` (condition
`true`), `req` high on `[1000, 2000)` read through 300 ps, `s` settled at 800 read through
600 ps (H_SETUP_PIN violated by 100 ps). -/
def o5Runt (t : Int) : Bool :=
  outB false (pulse 1000 2000 ((Rd.const 300).σ t)) (sAdv true 800 5000 ((Rd.const 600).σ t))

theorem o5Runt_eq (t : Int) : o5Runt t = decide (1300 ≤ t ∧ t < 1400) := by
  have e1 : (Rd.const 300).σ t = t - 300 := rfl
  have e2 : (Rd.const 600).σ t = t - 600 := rfl
  unfold o5Runt
  rw [e1, e2, outB_eq]
  unfold pulse sAdv
  split
  · rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · intro ⟨_, h2⟩; exact absurd h2 (by decide)
    · intro h3; omega
  · rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq]
    constructor
    · intro ⟨h1, _⟩; omega
    · intro h3; exact ⟨by omega, by decide⟩

/-- **Counter-run: a steer row violated makes an arbiter client withdraw.** In LibGapSteer's
own model, with every hypothesis but H_SETUP_PIN met (H_S_STABLE, H_HOLD_PIN), the unselected
branch is a 100 ps request pulse `[1300, 1400)`, and it violates `NoWdI` for EVERY ack that is
low on that window, e.g. any arbiter whose ack cannot answer within 100 ps. That is the
withdrawn request of `OnGcdArbKappaSrv`'s D1 race (`h21_7j_bare`). -/
theorem steer_withdraws :
    Stable (sAdv true 800 5000) true 800 5000 ∧
    ¬ ((800 : Int) + (Rd.const 600).hi ≤ 1000 + (Rd.const 300).lo) ∧
    (2000 : Int) + (Rd.const 300).hi ≤ 5000 + (Rd.const 600).lo ∧
    (∀ t, o5Runt t = decide (1300 ≤ t ∧ t < 1400)) ∧
    ∀ ack : Int → Bool, (∀ u, 1300 ≤ u → u < 1400 → ack u = false) → ¬ NoWdI o5Runt ack := by
  refine ⟨sAdv_stable true 800 5000, by simp [Rd.const], by simp [Rd.const], o5Runt_eq, ?_⟩
  intro ack hack hn
  obtain ⟨u, hu, hau, hw⟩ := hn 1399 (by rw [o5Runt_eq]; decide) (by rw [o5Runt_eq]; decide)
  by_cases hu1 : 1300 ≤ u
  · rw [hack u hu1 (by omega)] at hau; exact absurd hau (by decide)
  · have := hw 1299 (by omega) (by omega)
    rw [o5Runt_eq] at this; exact absurd this (by decide)

end steer

/-! ### 2c. Another arbiter's R0 (7j, verbatim) -/

section r0
open Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2

/-- **R0 as a client does not withdraw before its own server answers**: in 7j's four-phase
handover `Scn2`, R0 is high at every instant up to `ta` (its own A0's rise) and on to `TRb`.
For a cascaded merge, A0 is the C-join of the downstream acks (`ucontrol_mergeN_f`). So R0
falls only after the downstream ack rose (H_A0_CJOIN: that C-element, not modelled here). -/
theorem R0_held2 {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz : Int} (R : Run D s)
    (S : Scn2 D s t0 ta TA TA2 Hz) : ∀ t, t < TRb D t0 → t < Hz → s.R0 t = true ∧
      ta ≤ TRb D t0 := by
  intro t h hz
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := S.H_ORDER
  exact ⟨R0_hi2 R S t h hz, by unfold TRb; omega⟩

theorem R0_held1 {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz : Int} (R : Run D s)
    (S : Scn D s t0 ta TA TA2 Hz) : ∀ t, t < TR D t0 → t < Hz → s.R0 t = true ∧
      ta ≤ TR D t0 := by
  intro t h hz
  have := D.H_NONNEG; have := D.H_RISE_LE_FALL; have := S.H_ORDER
  exact ⟨R0_hi R S t h hz, by unfold TR; omega⟩

end r0

end gate

/-! ## 3. H_SETTLED from the four-phase causality -/

section settled
open Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2

/-- **H_A0_LOW_BEFORE + H_CLIENT_LAT, client 1** (about a run `s`): A1 rose at `T` (low on its
own feedback window before), A0 was low on ua1's A0-view window before its rise `ta`, and
client 1 released r1 (at its driver) no earlier than `L` after A1 rose: `T + L ≤ t0`. -/
def Caus1 (D : Dl) (s : Sigs) (ta t0 L : Int) : Prop :=
  ∃ T, s.A1 T = true ∧ (∀ u, T - D.wfa1 - D.c1f ≤ u → u < T → s.A1 u = false) ∧
    (∀ u, T - D.wa01 - D.c1f ≤ u → u < ta → s.A0 u = false) ∧ T + L ≤ t0

/-- The same for client 2. -/
def Caus2 (D : Dl) (s : Sigs) (ta t0 L : Int) : Prop :=
  ∃ T, s.A2 T = true ∧ (∀ u, T - D.wfa2 - D.c2f ≤ u → u < T → s.A2 u = false) ∧
    (∀ u, T - D.wa02 - D.c2f ≤ u → u < ta → s.A0 u = false) ∧ T + L ≤ t0

/-- ua1 (real INIT, 7h's gate relation) cannot raise A1 before A0's rise has reached it. -/
theorem A1_rise_after {D : Dl} {s : Sigs} (R : Run D s) {ta T : Int} (hT : s.A1 T = true)
    (hlo : ∀ u, T - D.wfa1 - D.c1f ≤ u → u < T → s.A1 u = false)
    (h0 : ∀ u, T - D.wa01 - D.c1f ≤ u → u < ta → s.A0 u = false) :
    ta + D.wa01 + D.c1r ≤ T := by
  have hn := D.H_NONNEG; have hrf := D.H_RISE_LE_FALL; have hl := D.H_LOOP_POS
  apply Classical.byContradiction; intro hc
  rw [R.H_A1 T, h0 (T - D.wa01 - D.c1r) (by omega) (by omega),
    h0 (T - D.wa01 - D.c1f) (by omega) (by omega),
    hlo (T - D.wfa1 - D.c1r) (by omega) (by omega),
    hlo (T - D.wfa1 - D.c1f) (by omega) (by omega), CE_eq, CE_eq] at hT
  simp at hT

theorem A2_rise_after {D : Dl} {s : Sigs} (R : Run D s) {ta T : Int} (hT : s.A2 T = true)
    (hlo : ∀ u, T - D.wfa2 - D.c2f ≤ u → u < T → s.A2 u = false)
    (h0 : ∀ u, T - D.wa02 - D.c2f ≤ u → u < ta → s.A0 u = false) :
    ta + D.wa02 + D.c2r ≤ T := by
  have hn := D.H_NONNEG; have hrf := D.H_RISE_LE_FALL; have hl := D.H_LOOP_POS
  apply Classical.byContradiction; intro hc
  rw [R.H_A2 T, h0 (T - D.wa02 - D.c2r) (by omega) (by omega),
    h0 (T - D.wa02 - D.c2f) (by omega) (by omega),
    hlo (T - D.wfa2 - D.c2r) (by omega) (by omega),
    hlo (T - D.wfa2 - D.c2f) (by omega) (by omega), CE_eq, CE_eq] at hT
  simp at hT

/-- **H_SETTLED (7h, client 1 releases) from causality.** In any run of 7h's gate relations
with the causal history `Caus1` (client latency `L`), 7h's H_SETTLED holds as soon as
H_ARC `wa0s + qf ≤ wa01 + c1r + L` (A0's rise reaches ustate's q no later than it reaches A1
plus the client's latency) and H_ARC2 `c1f ≤ c1r + L` (automatic with rise = fall). -/
theorem settled1_of_causal {D : Dl} {s : Sigs} (R : Run D s) {ta t0 L : Int}
    (hc : Caus1 D s ta t0 L) (H_ARC : D.wa0s + D.qf ≤ D.wa01 + D.c1r + L)
    (H_ARC2 : D.c1f ≤ D.c1r + L) :
    ta + D.wa0s + D.qf ≤ t0 ∧ ta + D.wa01 + D.c1f ≤ t0 := by
  obtain ⟨T, hT, hlo, h0, hlat⟩ := hc
  have := A1_rise_after R hT hlo h0
  omega

/-- **H_SETTLED (7j, client 2 releases) from causality.** -/
theorem settled2_of_causal {D : Dl} {s : Sigs} (R : Run D s) {ta t0 L : Int}
    (hc : Caus2 D s ta t0 L) (H_ARC : D.wa0s + D.qf ≤ D.wa02 + D.c2r + L)
    (H_ARC2 : D.c2f ≤ D.c2r + L) :
    ta + D.wa0s + D.qf ≤ t0 ∧ ta + D.wa02 + D.c2f ≤ t0 := by
  obtain ⟨T, hT, hlo, h0, hlat⟩ := hc
  have := A2_rise_after R hT hlo h0
  omega

/-- **Modelling finding: 7h's `Scn` excludes its own cause.** `Scn` asserts its settled
initial state on the WHOLE past (`∀ t < t0, A1 t = true`). So no trace satisfying `Scn` has a
causal history `Caus1` (an A1 rise before the release), for any latency `L ≥ 0`. Any run from
reset in which client 1 is ever acknowledged is outside `Scn`. -/
theorem scn_excludes_caus {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz L : Int}
    (S : Scn D s t0 ta TA TA2 Hz) (hL : 0 ≤ L) : ¬ Caus1 D s ta t0 L := by
  rintro ⟨T, _, hlo, _, hlat⟩
  have := D.H_LOOP_POS; have := D.H_RISE_LE_FALL
  have h1 := hlo (T - 1) (by omega) (by omega)
  rw [S.H_A1_init (T - 1) (by omega)] at h1
  exact absurd h1 (by decide)

theorem scn2_excludes_caus {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz L : Int}
    (S : Scn2 D s t0 ta TA TA2 Hz) (hL : 0 ≤ L) : ¬ Caus2 D s ta t0 L := by
  rintro ⟨T, _, hlo, _, hlat⟩
  have := D.H_LOOP_POS; have := D.H_RISE_LE_FALL
  have h1 := hlo (T - 1) (by omega) (by omega)
  rw [S.H_A2_init (T - 1) (by omega)] at h1
  exact absurd h1 (by decide)

/-- `Scn` without H_SETTLED (every other field verbatim). -/
structure ScnNS (D : Dl) (s : Sigs) (t0 ta TA TA2 Hz : Int) : Prop where
  H_ORDER : ta ≤ t0 ∧ ta < TA ∧ t0 < TA ∧ TA < TA2 ∧ TA2 < Hz
  H_r1 : ∀ t, t < Hz → s.r1 t = decide (t < t0)
  H_r2 : ∀ t, t < Hz → s.r2 t = true
  H_A0 : ∀ t, ta ≤ t → t < Hz → s.A0 t = (decide (t < TA) || decide (TA2 ≤ t))
  H_A0_prev : s.A0 (ta - 1) = false
  H_q_init : ∀ t, t < t0 → s.q t = true
  H_A1_init : ∀ t, t < t0 → s.A1 t = true
  H_A2_init : ∀ t, t < t0 → s.A2 t = false

theorem ScnNS.toScn {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz : Int} (S : ScnNS D s t0 ta TA TA2 Hz)
    (h : ta + D.wa0s + D.qf ≤ t0 ∧ ta + D.wa01 + D.c1f ≤ t0) : Scn D s t0 ta TA TA2 Hz :=
  ⟨S.H_ORDER, S.H_r1, S.H_r2, S.H_A0, S.H_A0_prev, S.H_q_init, S.H_A1_init, S.H_A2_init, h⟩

/-- `Scn2` without H_SETTLED. -/
structure Scn2NS (D : Dl) (s : Sigs) (t0 ta TA TA2 Hz : Int) : Prop where
  H_ORDER : ta ≤ t0 ∧ ta < TA ∧ t0 < TA ∧ TA < TA2 ∧ TA2 < Hz
  H_r1 : ∀ t, t < Hz → s.r1 t = true
  H_r2 : ∀ t, t < Hz → s.r2 t = decide (t < t0)
  H_A0 : ∀ t, ta ≤ t → t < Hz → s.A0 t = (decide (t < TA) || decide (TA2 ≤ t))
  H_A0_prev : s.A0 (ta - 1) = false
  H_q_init : ∀ t, t < t0 → s.q t = false
  H_A1_init : ∀ t, t < t0 → s.A1 t = false
  H_A2_init : ∀ t, t < t0 → s.A2 t = true

theorem Scn2NS.toScn2 {D : Dl} {s : Sigs} {t0 ta TA TA2 Hz : Int}
    (S : Scn2NS D s t0 ta TA TA2 Hz)
    (h : ta + D.wa0s + D.qf ≤ t0 ∧ ta + D.wa02 + D.c2f ≤ t0) : Scn2 D s t0 ta TA TA2 Hz :=
  ⟨S.H_ORDER, S.H_r1, S.H_r2, S.H_A0, S.H_A0_prev, S.H_q_init, S.H_A1_init, S.H_A2_init, h⟩

/-- 7j's `W1` with A1 RISING at -944 (A0 rises at -1000, ua1's rise arc 56 in `D0`). -/
def W1c : Sigs := { W1 with A1 := fun t => decide (-944 ≤ t) && decide (t < 388) }

theorem W1c_run : Run D0 W1c where
  H_q := W1_run.H_q
  H_R0 := W1_run.H_R0
  H_g1 := W1_run.H_g1
  H_g2 := W1_run.H_g2
  H_A1 := by intro t; rw [Bool.eq_iff_iff]; simp [W1c, W1, D0, prj, CE_eq]; omega
  H_A2 := W1_run.H_A2
  H_SRV := W1_run.H_SRV

/-- **Non-vacuity of `settled1_of_causal`**: `W1c` is a run of 7h's gate relations on 7j's
`D0` with a causal history at latency 68 (= qf − c1r, the least that H_ARC/H_ARC2 allow
here), and the idealized `W1` (the same `D0`, `ta`, `t0`) meets `ScnNS`. `D0` is 7j's
corner-mixed record (audit row 24): this is satisfiability only. -/
theorem settled1_nonvacuous :
    Run D0 W1c ∧ Caus1 D0 W1c (-1000) 0 68 ∧ D0.wa0s + D0.qf ≤ D0.wa01 + D0.c1r + 68 ∧
      D0.c1f ≤ D0.c1r + 68 ∧ Run D0 W1 ∧ ScnNS D0 W1 0 (-1000) 264 552 600 := by
  have S := W1_scn 600 (by omega)
  refine ⟨W1c_run, ⟨-944, by simp [W1c], ?_, ?_, by omega⟩, by simp [D0, prj],
    by simp [D0, prj], W1_run, ⟨S.H_ORDER, S.H_r1, S.H_r2, S.H_A0, S.H_A0_prev, S.H_q_init,
      S.H_A1_init, S.H_A2_init⟩⟩
  · intro u h1 h2; simp [W1c, D0, prj] at h1 ⊢; omega
  · intro u h1 h2; simp [W1c, W1, D0, prj] at h1 ⊢; omega

end settled

/-! ## 4. The client latency H_SETTLED needs, on the routed data -/

section data
open Formal.Cells.OnGcdArbKappa
open Formal.Cells.ConstraintsKappa
open Formal.Core.Substrate (Kappa pathDelay)

/-- H_ARC for client 1 under `Real7` (the shared A0 prefix `ac`, `dS1` cancels):
`dS2 + es + ps + aq ≤ d12 + e1 + p1 + ac1 + L` (fs). -/
def fset1 (L : Nat) : Form := ⟨[.dS2, .es, .ps, .aq], [.d12, .e1, .p1, .ac1], 0, L, false⟩
/-- H_ARC for client 2: `dS1 + es + ps + aq ≤ d12 + e2 + p2 + ac2 + L`. -/
def fset2 (L : Nat) : Form := ⟨[.dS1, .es, .ps, .aq], [.d12, .e2, .p2, .ac2], 0, L, false⟩

/-- Per arbiter: the client latencies (fs) certified sufficient at κS2 (script
`/tmp/claude-0/probes/Bbare/tbl.py`; the kernel checks them, `set_cert`). -/
def setTbl : List ((E → Quad) × Nat × Nat) := [(v_g2_merge10_uarb1, 680391, 275989), (v_g2_merge11_uarb1, 1590934, 1226938), (v_g2_merge12_uarb1, 12679, 11630), (v_g2_merge12_uarb2, 560923, 1161643), (v_g2_merge2_uarb1, 708583, 517422), (v_g2_merge3_uarb1, 317984, 144059), (v_g2_merge4_uarb1, 142513, 473110), (v_g2_merge6_uarb1, 750628, 169099), (v_g2_merge9_uarb1, 642778, 0), (v_g3_merge10_uarb1, 475592, 421671), (v_g3_merge11_uarb1, 726211, 600208), (v_g3_merge12_uarb1, 817342, 487041), (v_g3_merge12_uarb2, 30480, 0), (v_g3_merge2_uarb1, 593371, 496033), (v_g3_merge3_uarb1, 274132, 138596), (v_g3_merge4_uarb1, 351287, 615938), (v_g3_merge6_uarb1, 292608, 562170), (v_g3_merge9_uarb1, 349405, 847846), (v_g4_merge10_uarb1, 292613, 327389), (v_g4_merge11_uarb1, 373701, 0), (v_g4_merge12_uarb1, 308208, 594138), (v_g4_merge12_uarb2, 0, 0), (v_g4_merge2_uarb1, 753962, 753962), (v_g4_merge3_uarb1, 75127, 113193), (v_g4_merge4_uarb1, 130142, 572929), (v_g4_merge6_uarb1, 442681, 73601), (v_g4_merge9_uarb1, 741773, 317656), (v_gd_merge10_uarb1, 457772, 360507), (v_gd_merge11_uarb1, 695637, 1037342), (v_gd_merge12_uarb1, 773115, 488390), (v_gd_merge12_uarb2, 416438, 53932), (v_gd_merge2_uarb1, 140536, 459400), (v_gd_merge3_uarb1, 305097, 308230), (v_gd_merge4_uarb1, 562372, 141709), (v_gd_merge6_uarb1, 0, 0), (v_gd_merge9_uarb1, 85665, 1111321)]

theorem setTbl_fst : setTbl.map Prod.fst = arbs := rfl

theorem set_cert : setTbl.all (fun e => certFor .lit (fset1 e.2.1) e.1 216552148868 1000000000000 &&
    certFor .lit (fset2 e.2.2) e.1 216552148868 1000000000000) = true := by decide +kernel

/-- **The latency that suffices.** For every routed gcd_hw arbiter, every κ ≤ κS2 and every
realization: H_ARC holds for client 1 with latency `L1` and for client 2 with `L2` (setTbl). -/
theorem settled_safe {e : (E → Quad) × Nat × Nat} (he : e ∈ setTbl) (k : Kappa)
    (H_KAPPA : k.num * 1000000000000 ≤ k.den * 216552148868) {d : E → Nat}
    (hd : (litModel k e.1).Realizes d) : holds d (fset1 e.2.1) ∧ holds d (fset2 e.2.2) := by
  have hc := List.all_eq_true.1 set_cert e he
  simp only [Bool.and_eq_true] at hc
  exact ⟨form_safe (by decide) hc.1 k H_KAPPA d hd, form_safe (by decide) hc.2 k H_KAPPA d hd⟩

theorem setTbl_max : setTbl.all (fun e => decide (e.2.1 ≤ 1590934 ∧ e.2.2 ≤ 1590934)) = true ∧
    (v_g2_merge11_uarb1, 1590934, 1226938) ∈ setTbl := by
  refine ⟨by decide, ?_⟩
  simp [setTbl]

/-- The clients for which ZERO client latency fails at κS2 (65 of 72), as unsafe rows. -/
def setRows : List Row := [⟨"v_g2_merge10_uarb1.c1", .lit, fset1 0, v_g2_merge10_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g2_merge10_uarb1.c2", .lit, fset2 0, v_g2_merge10_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g2_merge11_uarb1.c1", .lit, fset1 0, v_g2_merge11_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g2_merge11_uarb1.c2", .lit, fset2 0, v_g2_merge11_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g2_merge12_uarb1.c1", .lit, fset1 0, v_g2_merge12_uarb1, true, 0, 1, true, 216552148868, 1000000000000⟩, ⟨"v_g2_merge12_uarb1.c2", .lit, fset2 0, v_g2_merge12_uarb1, true, 0, 1, true, 216552148868, 1000000000000⟩, ⟨"v_g2_merge12_uarb2.c1", .lit, fset1 0, v_g2_merge12_uarb2, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g2_merge12_uarb2.c2", .lit, fset2 0, v_g2_merge12_uarb2, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g2_merge2_uarb1.c1", .lit, fset1 0, v_g2_merge2_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g2_merge2_uarb1.c2", .lit, fset2 0, v_g2_merge2_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g2_merge3_uarb1.c1", .lit, fset1 0, v_g2_merge3_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g2_merge3_uarb1.c2", .lit, fset2 0, v_g2_merge3_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g2_merge4_uarb1.c1", .lit, fset1 0, v_g2_merge4_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g2_merge4_uarb1.c2", .lit, fset2 0, v_g2_merge4_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g2_merge6_uarb1.c1", .lit, fset1 0, v_g2_merge6_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g2_merge6_uarb1.c2", .lit, fset2 0, v_g2_merge6_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g2_merge9_uarb1.c1", .lit, fset1 0, v_g2_merge9_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g3_merge10_uarb1.c1", .lit, fset1 0, v_g3_merge10_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g3_merge10_uarb1.c2", .lit, fset2 0, v_g3_merge10_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g3_merge11_uarb1.c1", .lit, fset1 0, v_g3_merge11_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g3_merge11_uarb1.c2", .lit, fset2 0, v_g3_merge11_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g3_merge12_uarb1.c1", .lit, fset1 0, v_g3_merge12_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g3_merge12_uarb1.c2", .lit, fset2 0, v_g3_merge12_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g3_merge12_uarb2.c1", .lit, fset1 0, v_g3_merge12_uarb2, true, 0, 1, true, 216552148868, 1000000000000⟩, ⟨"v_g3_merge2_uarb1.c1", .lit, fset1 0, v_g3_merge2_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g3_merge2_uarb1.c2", .lit, fset2 0, v_g3_merge2_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g3_merge3_uarb1.c1", .lit, fset1 0, v_g3_merge3_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g3_merge3_uarb1.c2", .lit, fset2 0, v_g3_merge3_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g3_merge4_uarb1.c1", .lit, fset1 0, v_g3_merge4_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g3_merge4_uarb1.c2", .lit, fset2 0, v_g3_merge4_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g3_merge6_uarb1.c1", .lit, fset1 0, v_g3_merge6_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g3_merge6_uarb1.c2", .lit, fset2 0, v_g3_merge6_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g3_merge9_uarb1.c1", .lit, fset1 0, v_g3_merge9_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g3_merge9_uarb1.c2", .lit, fset2 0, v_g3_merge9_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g4_merge10_uarb1.c1", .lit, fset1 0, v_g4_merge10_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g4_merge10_uarb1.c2", .lit, fset2 0, v_g4_merge10_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g4_merge11_uarb1.c1", .lit, fset1 0, v_g4_merge11_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g4_merge12_uarb1.c1", .lit, fset1 0, v_g4_merge12_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g4_merge12_uarb1.c2", .lit, fset2 0, v_g4_merge12_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g4_merge2_uarb1.c1", .lit, fset1 0, v_g4_merge2_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g4_merge2_uarb1.c2", .lit, fset2 0, v_g4_merge2_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g4_merge3_uarb1.c1", .lit, fset1 0, v_g4_merge3_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g4_merge3_uarb1.c2", .lit, fset2 0, v_g4_merge3_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g4_merge4_uarb1.c1", .lit, fset1 0, v_g4_merge4_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g4_merge4_uarb1.c2", .lit, fset2 0, v_g4_merge4_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g4_merge6_uarb1.c1", .lit, fset1 0, v_g4_merge6_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g4_merge6_uarb1.c2", .lit, fset2 0, v_g4_merge6_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g4_merge9_uarb1.c1", .lit, fset1 0, v_g4_merge9_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_g4_merge9_uarb1.c2", .lit, fset2 0, v_g4_merge9_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_gd_merge10_uarb1.c1", .lit, fset1 0, v_gd_merge10_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_gd_merge10_uarb1.c2", .lit, fset2 0, v_gd_merge10_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_gd_merge11_uarb1.c1", .lit, fset1 0, v_gd_merge11_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_gd_merge11_uarb1.c2", .lit, fset2 0, v_gd_merge11_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_gd_merge12_uarb1.c1", .lit, fset1 0, v_gd_merge12_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_gd_merge12_uarb1.c2", .lit, fset2 0, v_gd_merge12_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_gd_merge12_uarb2.c1", .lit, fset1 0, v_gd_merge12_uarb2, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_gd_merge12_uarb2.c2", .lit, fset2 0, v_gd_merge12_uarb2, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_gd_merge2_uarb1.c1", .lit, fset1 0, v_gd_merge2_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_gd_merge2_uarb1.c2", .lit, fset2 0, v_gd_merge2_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_gd_merge3_uarb1.c1", .lit, fset1 0, v_gd_merge3_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_gd_merge3_uarb1.c2", .lit, fset2 0, v_gd_merge3_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_gd_merge4_uarb1.c1", .lit, fset1 0, v_gd_merge4_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_gd_merge4_uarb1.c2", .lit, fset2 0, v_gd_merge4_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_gd_merge9_uarb1.c1", .lit, fset1 0, v_gd_merge9_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩, ⟨"v_gd_merge9_uarb1.c2", .lit, fset2 0, v_gd_merge9_uarb1, true, 0, 1, false, 216552148868, 1000000000000⟩]

theorem setRows_ok : setRows.all (fun r => r.ok && r.pu == 216552148868 &&
    r.qu == 1000000000000 && r.f.b == 0) = true := by decide +kernel

theorem setRows_len : setRows.length = 65 := rfl

/-- **H_SETTLED is NOT implied by the arbiter's own arcs.** For each of the 65 clients in
`setRows` and every κ ≥ κS2 (in particular at κS2), some realization of that arbiter's
extracted arcs violates H_ARC with zero client latency: A0's rise reaches ustate's q later
than it reaches A_k. -/
theorem settled_L0_fails {r : Row} (hr : r ∈ setRows) (k : Kappa)
    (H_KAPPA : k.den * 216552148868 ≤ k.num * 1000000000000) :
    r.f.b = 0 ∧ ∃ d : E → Nat, (model k r.rd r.f r.v).Realizes d ∧
      pathDelay d r.f.Q + r.f.b < pathDelay d r.f.P + r.f.a := by
  have h := List.all_eq_true.1 setRows_ok r hr
  simp only [Bool.and_eq_true, beq_iff_eq] at h
  obtain ⟨⟨⟨hok, hp⟩, hq⟩, hb⟩ := h
  refine ⟨hb, row_unsafe_ex r hok k ?_⟩
  rw [hp, hq]; exact H_KAPPA

end data

/-! ## 5. D2 with H_SETTLED derived from the client's causality -/

section design
open Formal.Cells.OnGcdArbKappa
open Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2
open Formal.Core.Substrate (Kappa pathDelay)

theorem mem_arbs_of {e : (E → Quad) × Nat × Nat} (he : e ∈ setTbl) : e.1 ∈ arbs := by
  rw [← setTbl_fst]; exact List.mem_map_of_mem he

/-- **D2 at the gate level with H_SETTLED derived.** For every κ ≤ κS2 ≈ 0.2165521489, every
routed gcd_hw arbiter `e.1` and every realization `d`: OnGcdArbKappaSrv's four handover
conclusions (A1/A2 and g1/g2 exclusion, both directions) hold for every idealized handover run
`s` satisfying `Scn`/`Scn2` WITHOUT H_SETTLED, given ANY run `sr` of the same record with the
same `ta`, `t0` whose causal history (`Caus1`/`Caus2`) has client latency at least setTbl's
`L1`/`L2`. For the g1/g2 records (`Real1`/`Real2`), the routed values of ua_k's A0 route and
arc are named as hypotheses. -/
theorem design_gate_held_causal {e : (E → Quad) × Nat × Nat} (he : e ∈ setTbl) (k : Kappa)
    (H_KAPPA : k.num * 1000000000000 ≤ k.den * 216552148868) {d : E → Nat}
    (hd : (litModel k e.1).Realizes d)
    (H_LOOP_ST : 0 < d .aq + d .cq + d .qs) (H_LOOP_UA1 : 0 < d .ac1 + d .fa1)
    (H_LOOP_UA2 : 0 < d .ac2 + d .fa2) :
    (∀ (D : Dl) (s sr : Sigs) (t0 ta TA TA2 Hz L : Int),
      OnGcdArbA0.Real7 (xOf d) D → (d .srv : Int) ≤ D.smin → Run D s →
      ScnNS D s t0 ta TA TA2 Hz → Run D sr → Caus1 D sr ta t0 L → (e.2.1 : Int) ≤ L →
      ∀ t, t < Hz → (s.A1 t && s.A2 t) = false) ∧
    (∀ (D : Dl) (s sr : Sigs) (t0 ta TA TA2 Hz L : Int),
      OnGcdArbA0.Real7 (xOfB d) D → (d .srv : Int) ≤ D.smin → Run D s →
      Scn2NS D s t0 ta TA TA2 Hz → Run D sr → Caus2 D sr ta t0 L → (e.2.2 : Int) ≤ L →
      ∀ t, t < Hz → (s.A1 t && s.A2 t) = false) ∧
    (∀ (cr : Int) (D : Dl) (s sr : Sigs) (t0 ta TA TA2 Hz L : Int),
      OnGcdArbFix.Real1 (qOf d) cr (d .cq) D →
      D.wa0s = d .ac + d .dS1 + d .dS2 + d .es + d .ps → D.qf = d .aq →
      D.wa01 = d .ac + d .dS1 + d .d12 + d .e1 + d .p1 → D.c1r = d .ac1 → D.c1f = d .ac1 →
      (d .srv : Int) ≤ D.smin → Run D s →
      ScnNS D s t0 ta TA TA2 Hz → Run D sr → Caus1 D sr ta t0 L → (e.2.1 : Int) ≤ L →
      ∀ t, t < Hz → (s.g1 t && s.g2 t) = false) ∧
    (∀ (cr : Int) (D : Dl) (s sr : Sigs) (t0 ta TA TA2 Hz L : Int),
      OnGcdArbFix.Real2 (qOf d) cr (d .cq) D →
      D.wa0s = d .ac + d .dS1 + d .dS2 + d .es + d .ps → D.qr = d .aq → D.qf = d .aq →
      D.wa02 = d .ac + d .dS2 + d .d12 + d .e2 + d .p2 → D.c2r = d .ac2 → D.c2f = d .ac2 →
      (d .srv : Int) ≤ D.smin → Run D s →
      Scn2NS D s t0 ta TA TA2 Hz → Run D sr → Caus2 D sr ta t0 L → (e.2.2 : Int) ≤ L →
      ∀ t, t < Hz → (s.g1 t && s.g2 t) = false) := by
  have G := OnGcdArbKappaSrv.design_gate_held (mem_arbs_of he) k H_KAPPA hd H_LOOP_ST
    H_LOOP_UA1 H_LOOP_UA2
  obtain ⟨h1, h2⟩ := settled_safe he k H_KAPPA hd
  simp only [holds, fset1, fset2, pathDelay, List.map, List.sum_cons, List.sum_nil] at h1 h2
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro D s sr t0 ta TA TA2 Hz L hR hs R S Rr C hL
    have hR' := hR
    obtain ⟨e1, e2, _, e4, _, _, _, _, e9, e10, _⟩ := hR'
    simp only [OnGcdArbA0.As, OnGcdArbA0.A1r, xOf] at e1 e2 e4 e9 e10
    have hset := settled1_of_causal Rr C (by omega) (by omega)
    exact G.2.1 D s t0 ta TA TA2 Hz hR hs R (S.toScn hset)
  · intro D s sr t0 ta TA TA2 Hz L hR hs R S Rr C hL
    have hR' := hR
    obtain ⟨e1, _, e3, e4, _, _, _, _, _, _, e11, e12, _⟩ := hR'
    simp only [OnGcdArbA0.As, OnGcdArbA0.A2r, xOfB, xOf] at e1 e3 e4 e11 e12
    have hset := settled2_of_causal Rr C (by omega) (by omega)
    exact G.2.2.1 D s t0 ta TA TA2 Hz hR hs R (S.toScn2 hset)
  · intro cr D s sr t0 ta TA TA2 Hz L hR hA hq hA1 hc1r hc1f hs R S Rr C hL
    have hset := settled1_of_causal Rr C (by omega) (by omega)
    exact G.2.2.2.1 cr D s t0 ta TA TA2 Hz hR hA hq hs R (S.toScn hset)
  · intro cr D s sr t0 ta TA TA2 Hz L hR hA hqr hqf hA2 hc2r hc2f hs R S Rr C hL
    have hset := settled2_of_causal Rr C (by omega) (by omega)
    exact G.2.2.2.2 cr D s t0 ta TA TA2 Hz hR hA hqr hs R (S.toScn2 hset)

end design

end Formal.Cells.ArbNoWithdraw
