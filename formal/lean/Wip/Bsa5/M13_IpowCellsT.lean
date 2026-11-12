-- Bsa5 mutant M13 of Formal/Cells/IpowCellsT.lean: one change, gap_accept for d <= g + 1. Expected: FAIL.
import Formal.Cells.ContractBridge
import Formal.Cells.LutFbBridge

/-!
# Probe Bfc (shard B): timed feedback contracts for ipow (`FbCelT`, IpowCellsT)

`ContractBridge.fbCel_iff_si` shows that IpowCells' `FbCel F p o` is EQUIVALENT to the plain SI
step: its feedback trace `qp`, bounds `lo hi` and H_RT_FB are existential, and the ideal
feedback (`qp = o`, `lo = hi = 0`) always meets them. So the feedback contracts of IpowCells
(and ContractBridge, B-ipow-cells.md, B-contract-bridge.md) carry no timing content. This file
repairs that without editing those files: `FbCelT F p o r` takes the feedback ROUTE `r =
⟨qp, lo, hi⟩` as a parameter (pinned per cell: routed values or symbolic constants), with
H_FB_POS `1 ≤ lo` and H_RT_FB stated on `r.hi`. Notes: `formal/notes/B-ipow-cells-t.md`.

## Assumed / proved / NOT covered

**Assumed** (`FbCelT`, per feedback LUT, on its pinned route `r`): H_LUT_FB (`LutFb` on the
routed pin `r.qp`), H_FB_POS (`1 ≤ r.lo`), H_FB_ROUTE (`BoundedDelay r.lo r.hi o r.qp`),
H_FB_RST (`r.qp 0 = o 0`), H_RT_FB (`RespAfter r.hi p o`). `ContractT` = IpowCells' `Contract`
with every `FbCel` field replaced by `FbCelT` on the operator's routes; every other field
(H_SEL_PIN, H_WIRE_DI, H_DELAY_LUMPED, H_CTREE_ATOMIC, arbiter grant fields, data, reset,
environment) is unchanged and still a hypothesis. For the physical derivation: LutFbBridge's
`CelC`/`EnvC`/`Timing1`/H_PWR (C-element) and `Stage`/`Env1`/`Timing1`/H_LUT_POS/H_PWR (link),
plus three new named hypotheses: H_WIRE_POS (`1 ≤ wl`), H_FB_PWR (feedback pin 0 until the
wire's window is defined, `t < wh`), H_IN_RST (the node's input pins are 0 during reset).

**Proved:**
* `FbCelT.si`, `FbCelT.fbFirst`, `FbCelT.toFbCel`: `FbCelT` gives C's SI step, C's
  H_FB_FIRST on the ROUTED pin (C-10k's `fbFirst_of_resp`), and IpowCells' `FbCel`.
  `FbCelT.hi_pos`: on a switching node the pinned settle bound is `≥ 1`.
* `Gap.gap_exact`: on the gap-`g` run of a 2-input C-element (the environment answers the
  output edge `g` ticks later), with a transport feedback route of delay `d ≥ 1`, `FbCelT`
  holds iff `d ≤ g` (tcheck Rc's `fb_hi ≤ resp_lo`, exact), while the SI step and `FbCel`
  hold for every `g`. `Gap.gap_reject`: no route with `hi > g` at all.
  `Gap.si_not_fbCelT`: at `g = 0` the SI step and `FbCel` hold, the node switches, and NO
  route meets `FbCelT`: the timing content is real.
* `c2_fbCelT`, `link_fbCelT` (from LutFbBridge's `c2_lutFb` / `link_lutFb` and the new
  `respAfter_of_steps`): B's physical model (Win LUT + H_NO_REVERT + `WinDelay wl wh` wire +
  four-phase environment + H_LAT) gives `FbCelT` with the PHYSICAL wire as the pinned route
  `⟨qp, wl, wh⟩`; H_RT_FB is derived (from H_LAT: `wh ≤ min Es Ea`), not assumed. Instances
  on IpowCells' encodings: `cgate2_fbCelT`, `fork2_ack_fbCelT` (fork N=2 / join N=2),
  `ack_fbCelT` (`ua1`/`ua2`, `uxa`/`uya`).
* `contract_of_contractT`, `ipow_safe_of_contractsT`: C-8y's ipow safety from the 83 timed
  contracts, for EVERY route assignment `rt`.
* Non-vacuity: `ipow_contractsT_satisfiable` (for EVERY pinned bounds `L o i ≥ 1`, `H o i`, one
  run meets all 83 `ContractT`s on routes with exactly those bounds, H_BUNDLE, H_START_ONCE;
  the all-quiet run), and `c2_fbCelT_witness` (the real `bd_c2` loop of
  `LutFbBridge.c2_witness`, LUT band `[1, 2]`, wire 1: `FbCelT` on route `⟨sq 7, 1, 1⟩`, and
  the node toggles).

**NOT covered:** routed numbers for ipow (no ipow route exists; the routes are symbolic); the
physical derivation of `FbCelT` for `bd_c3`/`bd_c4`, the 5-input C-tree, the mux's
`uj0`/`uj1` (5-pin LUTs with the select) and any network-level derivation of `EnvC`/`Env1`
from the neighbouring cells (so no single run meets `ContractT` everywhere AND switches);
H_IN_RST and H_FB_PWR are not derived (power-up/reset facts); every non-feedback field of the
contract is as in IpowCells.
-/

namespace Formal.Cells.IpowCellsT
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.Ops.Gen Formal.Gen Formal.Gen.Cells
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk
open Formal.Timing.FbFirstRt (RespAfter si_of_resp fbFirst_of_resp)
open Formal.Cells.IpowCells (FbCel cgate cgate_eq celL celL_move)

/-! ## 1. The timed feedback contract -/

/-- A **pinned feedback route** of one feedback LUT: the trace `qp` at its feedback pin and
the route's delay bounds `[lo, hi]` (routed values, or symbolic per-cell constants). -/
structure FbRoute where
  qp : Trace
  lo : Nat
  hi : Nat

/-- **FbCelT**: `IpowCells.FbCel` with the feedback route a PARAMETER `r`, not an existential.
Fields: H_LUT_FB (`LutFb`: the LUT reads the routed feedback pin `r.qp`), H_FB_POS (the route
has a nonzero minimum delay), H_FB_ROUTE (`BoundedDelay r.lo r.hi o r.qp`), H_FB_RST (reset
agreement) and H_RT_FB (`RespAfter r.hi p o`: a non-feedback pin changes only after the
output has been stable for the route's settle bound `r.hi`, tcheck rule Rc in trace form). -/
structure FbCelT {α : Type} (F : α → Bool → Bool) (p : Nat → α) (o : Trace) (r : FbRoute) :
    Prop where
  H_LUT_FB : LutFb F p r.qp o
  H_FB_POS : 1 ≤ r.lo
  H_FB_ROUTE : BoundedDelay r.lo r.hi o r.qp
  H_FB_RST : r.qp 0 = o 0
  H_RT_FB : RespAfter r.hi p o

section basic
variable {α : Type} {F : α → Bool → Bool} {p : Nat → α} {o : Trace} {r : FbRoute}

/-- C's H_FB_FIRST on the ROUTED feedback pin (C-10k's `fbFirst_of_resp`). -/
theorem FbCelT.fbFirst (h : FbCelT F p o r) : FbFirst r.qp o :=
  fbFirst_of_resp h.H_LUT_FB h.H_FB_ROUTE h.H_FB_RST h.H_RT_FB

/-- C's SI gate step on the node's own output. -/
theorem FbCelT.si (h : FbCelT F p o r) : ∀ t, o (t + 1) ≠ o t → o (t + 1) = F (p t) (o t) :=
  si_of_resp h.H_LUT_FB h.H_FB_ROUTE h.H_FB_RST h.H_RT_FB

/-- `FbCelT` gives IpowCells' `FbCel` (the route is a witness for its existentials). -/
theorem FbCelT.toFbCel (h : FbCelT F p o r) : FbCel F p o :=
  ⟨r.qp, r.lo, r.hi, h.H_LUT_FB, h.H_FB_ROUTE, h.H_FB_RST, h.H_RT_FB⟩

/-- On a node that switches at all, the pinned settle bound is nonzero (H_FB_POS rules out
the ideal route `hi = 0`, which forces `qp = o`). -/
theorem FbCelT.hi_pos (h : FbCelT F p o r) {t : Nat} (ht : o (t + 1) ≠ o t) : 1 ≤ r.hi := by
  apply Classical.byContradiction
  intro h0
  have e : r.hi = 0 := by omega
  have hs : ∀ u, r.qp u = o u := fun u =>
    h.H_FB_ROUTE.settle u (by omega) (fun x h1 h2 => by rw [e] at h1; congr 1; omega)
  obtain ⟨d, h1, h2, _, _⟩ := h.H_FB_ROUTE.cause t (by
    show r.qp t ≠ r.qp (t + 1); rw [hs, hs]; exact fun h' => ht h'.symm)
  have := h.H_FB_POS; omega

end basic

/-! ## 2. The timing content is real: SI runs that `FbCelT` rejects (tight in the route) -/

namespace Gap

/-- Both inputs of a 2-input C-element rise at `g + 1` and fall at `2g + 2`: the environment
answers the output's rising edge (at `g + 2`) `g` ticks later. -/
def x (g t : Nat) : Bool := decide (g + 1 ≤ t ∧ t < 2 * g + 2)
/-- The C-element output: rises at `g + 2`, falls at `2g + 3`. -/
def o (g t : Nat) : Bool := decide (g + 2 ≤ t ∧ t < 2 * g + 3)
/-- The pins of the generated `bd_c2` (both inputs). -/
def p (g t : Nat) : List Bool := [x g t, x g t]
/-- The feedback pin through a transport route of delay `d`. -/
def q (g d t : Nat) : Bool := decide (g + 2 + d ≤ t ∧ t < 2 * g + 3 + d)

theorem o_succ (g t : Nat) : o g (t + 1) = x g t := by
  unfold o x; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega

theorem cgate_dup : ∀ a b : Bool, cgate [a, a] b = a := by decide +kernel

theorem x_change (g u : Nat) (h : x g (u + 1) ≠ x g u) : u = g ∨ u = 2 * g + 1 := by
  apply Classical.byContradiction; intro hn; apply h
  unfold x; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega

theorem p_change (g u : Nat) (h : p g (u + 1) ≠ p g u) : u = g ∨ u = 2 * g + 1 :=
  x_change g u (fun e => h (by unfold p; rw [e]))

theorem o_val (g t : Nat) : o g t = true ↔ (g + 2 ≤ t ∧ t < 2 * g + 3) := by
  unfold o; simp

/-- **The SI step holds** (for every `g`): `o` changes only to the C-element of its inputs
and its own output. -/
theorem gap_si (g : Nat) : ∀ t, o g (t + 1) ≠ o g t → o g (t + 1) = cgate (p g t) (o g t) :=
  fun t _ => by rw [o_succ, p, cgate_dup]

/-- So IpowCells' `FbCel` holds on every member of the family (`fbCel_iff_si`). -/
theorem gap_fbCel (g : Nat) : FbCel cgate (p g) (o g) :=
  (ContractBridge.fbCel_iff_si _ _ _).mpr (gap_si g)

/-- The transport route of delay `d`. -/
def route (g d : Nat) : FbRoute := ⟨q g d, d, d⟩

theorem route_bounded (g d : Nat) : BoundedDelay d d (o g) (q g d) := by
  apply IpowCells.bounded_of_winDelay
  · apply CElemTiming.transport_winDelay (Nat.le_refl d) (Nat.le_refl d)
    intro t; unfold q o; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega
  · intro t ht; unfold q; apply Bool.eq_iff_iff.mpr; simp only [decide_eq_true_eq]; omega

/-- **Rejection**: no route whose settle bound exceeds the response gap `g` meets `FbCelT`
(H_RT_FB fails at the inputs' fall). -/
theorem gap_reject (g : Nat) (r : FbRoute) (hr : g < r.hi) : ¬ FbCelT cgate (p g) (o g) r := by
  intro h
  have hc : p g (2 * g + 1 + 1) ≠ p g (2 * g + 1) := by
    have e1 : x g (2 * g + 1 + 1) = false := by unfold x; simp
    have e2 : x g (2 * g + 1) = true := by unfold x; simp; omega
    unfold p; rw [e1, e2]; decide
  obtain ⟨h1, h2⟩ := h.H_RT_FB (2 * g + 1) hc
  have a := h2 (2 * g + 1 + 1) (by omega) (Nat.le_refl _)
  have b1 : o g (2 * g + 1 + 1) = true := (o_val g _).mpr (by omega)
  have b2 : o g (2 * g + 1 + 1 - r.hi) = false := by
    cases e : o g (2 * g + 1 + 1 - r.hi)
    · rfl
    · have := (o_val g _).mp e; omega
  rw [b1, b2] at a; exact absurd a (by decide)

/-- **Acceptance**: the transport route of delay `d` with `1 ≤ d ≤ g` meets `FbCelT`. -/
theorem gap_accept (g d : Nat) (h1 : 1 ≤ d) (h2 : d ≤ g + 1) : FbCelT cgate (p g) (o g) (route g d) where
  H_LUT_FB := fun t _ => by show o g (t + 1) = cgate (p g t) (q g d t); rw [o_succ, p, cgate_dup]
  H_FB_POS := h1
  H_FB_ROUTE := route_bounded g d
  H_FB_RST := by show q g d 0 = o g 0; unfold q o; simp
  H_RT_FB := by
    intro u hu
    show d ≤ u + 1 ∧ stableOn (o g) (u + 1 - d) (u + 1)
    rcases p_change g u hu with e | e
    · subst e
      refine ⟨by omega, fun t a b => ?_⟩
      have e1 : o u t = false := by
        cases e : o u t
        · rfl
        · have := (o_val u t).mp e; omega
      have e2 : o u (u + 1 - d) = false := by
        cases e : o u (u + 1 - d)
        · rfl
        · have := (o_val u _).mp e; omega
      rw [e1, e2]
    · subst e
      refine ⟨by omega, fun t a b => ?_⟩
      rw [(o_val g t).mpr (by omega), (o_val g _).mpr (by omega)]

/-- **Exactness in the pinned route**: with a transport feedback route of delay `d ≥ 1`,
`FbCelT` holds on the gap-`g` run iff `d ≤ g` (tcheck Rc's `fb_hi ≤ resp_lo`), while the SI
step and IpowCells' `FbCel` hold for every `g` and `d`. -/
theorem gap_exact (g d : Nat) (h1 : 1 ≤ d) :
    (FbCelT cgate (p g) (o g) (route g d) ↔ d ≤ g) ∧ FbCel cgate (p g) (o g) := by
  refine ⟨⟨fun h => ?_, gap_accept g d h1⟩, gap_fbCel g⟩
  apply Classical.byContradiction; intro hn
  exact gap_reject g (route g d) (by show g < d; omega) h

/-- **The SI step does not imply `FbCelT` for ANY admissible route.** At gap 0 (the inputs
fall one tick after the output rises) the SI step and `FbCel` hold, but no route with
`1 ≤ lo` (H_FB_POS) meets `FbCelT`: the existential closure of `FbCelT` is strictly
stronger than the SI step, unlike `FbCel` (`ContractBridge.fbCel_iff_si`). -/
theorem si_not_fbCelT :
    (∀ t, o 0 (t + 1) ≠ o 0 t → o 0 (t + 1) = cgate (p 0 t) (o 0 t)) ∧ FbCel cgate (p 0) (o 0) ∧
      o 0 2 ≠ o 0 1 ∧ ∀ r : FbRoute, ¬ FbCelT cgate (p 0) (o 0) r := by
  refine ⟨gap_si 0, gap_fbCel 0, by decide, fun r h => ?_⟩
  have := h.hi_pos (t := 1) (by decide)
  exact gap_reject 0 r (by omega) h

end Gap

/-! ## 3. `FbCelT` from B's physical model (LutFbBridge: Win LUT + H_NO_REVERT + WinDelay wire
+ four-phase environment) -/

open Formal.Cells.LutFbBridge (Phases node_steps CelC EnvC cc_pre cc_phase cc_ge cc_gap exC_eq
  c2_lutFb link_lutFb τ seg_of_mono)
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo Stage Env1 Timing1 cph)
open Formal.Cells.PipeTimed (ex Vph)

/-- Transfer of `FbCelT` along a re-reading of the pins (same LUT function on the new pin
encoding, and a change of the new pins is a change of the old ones). -/
theorem FbCelT.map {α β : Type} {F : α → Bool → Bool} {F' : β → Bool → Bool} {p : Nat → α}
    {p' : Nat → β} {o : Trace} {r : FbRoute} (h : FbCelT F p o r)
    (hF : ∀ t q, F' (p' t) q = F (p t) q) (hp : ∀ u, p' (u + 1) ≠ p' u → p (u + 1) ≠ p u) :
    FbCelT F' p' o r where
  H_LUT_FB := fun t ht => by rw [hF]; exact h.H_LUT_FB t ht
  H_FB_POS := h.H_FB_POS
  H_FB_ROUTE := h.H_FB_ROUTE
  H_FB_RST := h.H_FB_RST
  H_RT_FB := fun u hu => h.H_RT_FB u (hp u hu)

/-- A pin that is `v0` before `ρ 0` and constant on each `[ρ j, ρ (j+1))` changes only at
some `ρ j`. -/
theorem change_at_starts {a : Nat → Bool} {ρ : Nat → Nat} {v0 : Bool} {v : Nat → Bool}
    (hm : ∀ j, ρ j < ρ (j + 1)) (h0 : ∀ t, t < ρ 0 → a t = v0)
    (hs : ∀ j t, ρ j ≤ t → t < ρ (j + 1) → a t = v j) :
    ∀ u, a (u + 1) ≠ a u → ∃ j, u + 1 = ρ j := by
  intro u hu
  rcases seg_of_mono ρ hm (u + 1) with h | ⟨j, h1, h2⟩
  · exact absurd ((h0 _ h).trans (h0 u (by omega)).symm) hu
  · refine ⟨j, ?_⟩
    apply Classical.byContradiction; intro hn
    exact hu ((hs j _ h1 h2).trans (hs j u (by omega) (by omega)).symm)

/-- **H_RT_FB from the physical node and the environment's departures.** The node is a
`Win` LUT with H_NO_REVERT on a phase-clean excitation (so a clean step signal with edges
`τ j`, `node_steps`); every pin change happens at a departure `ρ j` or `β j`; the first
departures come no earlier than `wh`, and each later one at least `wh` after the node's
previous edge. Then `RespAfter wh`. -/
theorem respAfter_of_steps {α : Type} {p : Nat → α} {x O : Trace} {lo hi wh Es Ea : Nat}
    {ρ β : Nat → Nat}
    (hW : Win lo hi x O) (hN : NoRevertI lo hi x O) (hx : Phases x (cph ρ β))
    (hlo : 1 ≤ lo) (hR : hi ≤ cph ρ β 0) (hsp : ∀ j, cph ρ β j + hi ≤ cph ρ β (j + 1))
    (hP : ∀ t, t < hi → O t = false) (hw0 : wh ≤ ρ 0 ∧ wh ≤ β 0)
    (hS : ∀ j, τ O lo hi (cph ρ β) j + Es ≤ ρ (j + 1))
    (hRv : ∀ j, τ O lo hi (cph ρ β) j + Ea ≤ β (j + 1)) (hE : wh ≤ Es ∧ wh ≤ Ea)
    (hch : ∀ u, p (u + 1) ≠ p u → (∃ j, u + 1 = ρ j) ∨ ∃ j, u + 1 = β j) :
    RespAfter wh p O := by
  obtain ⟨hb, hpre, hseg⟩ := node_steps hW hN hx hlo hR hsp hP
  have key : ∀ s j, s ≤ cph ρ β j → (j = 0 → wh ≤ s) →
      (∀ k, j = k + 1 → τ O lo hi (cph ρ β) k + wh ≤ s) → wh ≤ s ∧ stableOn O (s - wh) s := by
    intro s j hs h0 hk
    cases j with
    | zero =>
      have w := h0 rfl
      have b0 := (hb 0).1
      refine ⟨w, fun t h1 h2 => ?_⟩
      rw [hpre t (by omega), hpre (s - wh) (by omega)]
    | succ k =>
      have w := hk k rfl
      have b1 := (hb (k + 1)).1
      refine ⟨by omega, fun t h1 h2 => ?_⟩
      rw [hseg k t (by omega) (by omega), hseg k (s - wh) (by omega) (by omega)]
  intro u hu
  rcases hch u hu with ⟨j, hj⟩ | ⟨j, hj⟩
  · rw [hj]
    exact key (ρ j) j (Nat.le_max_left _ _) (fun e => by subst e; exact hw0.1)
      (fun k e => by subst e; have := hS k; omega)
  · rw [hj]
    exact key (β j) j (Nat.le_max_right _ _) (fun e => by subst e; exact hw0.2)
      (fun k e => by subst e; have := hRv k; omega)

/-- **Bridge, C-element (`bd_c2`): `FbCelT` with the PHYSICAL feedback wire as the pinned
route** `⟨qp, wl, wh⟩`. Assumed: LutFbBridge's `c2_lutFb` hypotheses (`CelC`: Win LUT band
`[lo, hi]` + H_NO_REVERT + `WinDelay wl wh` wire + H_LUT_POS; `EnvC`; `Timing1`: H_RST_LONG,
H_LAT; H_PWR) and three named additions: H_WIRE_POS `1 ≤ wl`, H_FB_PWR (the feedback pin
shows the reset value 0 until the wire's window is defined, `t < wh`), H_IN_RST (both inputs
are 0 during reset, `t < R`; `EnvC` leaves them free there). -/
theorem c2_fbCelT {a b rst O qp : Trace} {lo hi wl wh R Es Ea : Nat} {ρ β : Nat → Nat}
    {F : Bool × Bool → Bool → Bool} (hFe : ∀ x y q, F (x, y) q = cel2 x y q)
    (C : CelC a b rst O qp lo hi wl wh) (E : EnvC a b rst O lo hi R ρ β Es Ea)
    (T : Timing1 lo hi wh R Es Ea) (H_PWR : ∀ t, t < hi → O t = false)
    (H_WIRE_POS : 1 ≤ wl) (H_FB_PWR : ∀ t, t < wh → qp t = false)
    (H_IN_RST : ∀ t, t < R → a t = false ∧ b t = false) :
    FbCelT F (fun t => (a t, b t)) O ⟨qp, wl, wh⟩ := by
  obtain ⟨hL, _⟩ := c2_lutFb hFe C E T H_PWR
  have hlh := win_le C.H_LUT_WIN
  have hlo := C.H_LUT_POS
  have hwl : wl ≤ wh := by obtain ⟨s, h1, h2, _⟩ := C.H_FB wh (Nat.le_refl _); omega
  have hlat := T.H_LAT; have hrl := T.H_RST_LONG; have hre := E.H_RST_EARLY
  have hW : Win lo hi (ex a (fun t => !b t) qp rst) O := by rw [← exC_eq]; exact C.H_LUT_WIN
  have hN : NoRevertI lo hi (ex a (fun t => !b t) qp rst) O := by
    rw [← exC_eq]; exact C.H_NO_REVERT
  have hx : Phases (ex a (fun t => !b t) qp rst) (cph ρ β) :=
    ⟨fun s h => by rw [← exC_eq]; exact cc_pre C E T s h, cc_phase C E T⟩
  have hR := cc_ge C E 0
  have hgap := cc_gap C E
  have hsp : ∀ j, cph ρ β j + hi ≤ cph ρ β (j + 1) := fun j => by have := hgap j; omega
  have hmρ : ∀ j, ρ j < ρ (j + 1) := fun j => by
    have := E.H_SND j; have := nt_lo O (cph ρ β j) (Vph j) hlh (hi := hi)
    have : ρ j ≤ cph ρ β j := Nat.le_max_left _ _
    omega
  have hmβ : ∀ j, β j < β (j + 1) := fun j => by
    have := E.H_RCV j; have := nt_lo O (cph ρ β j) (Vph j) hlh (hi := hi)
    have : β j ≤ cph ρ β j := Nat.le_max_right _ _
    omega
  refine ⟨hL, H_WIRE_POS, IpowCells.bounded_of_winDelay C.H_FB
    (fun t ht => by
      show qp (t + 1) = qp t; have ht' : t + 1 < wh := ht
      rw [H_FB_PWR t (by omega), H_FB_PWR (t + 1) ht']),
    by show qp 0 = O 0; rw [H_FB_PWR 0 (by omega), H_PWR 0 (by omega)], ?_⟩
  show RespAfter wh (fun t => (a t, b t)) O
  refine respAfter_of_steps hW hN hx hlo (by omega) hsp H_PWR ⟨by omega, by omega⟩ E.H_SND
    E.H_RCV ⟨by omega, by omega⟩ (fun u hu => ?_)
  by_cases ha : a (u + 1) = a u
  · right
    have hb' : b (u + 1) ≠ b u := fun e => hu (by simp only [ha, e])
    refine change_at_starts hmβ (v0 := false) (fun t ht => ?_) E.H_B u hb'
    by_cases h : t < R
    · exact (H_IN_RST t h).2
    · exact E.H_B0 t (by omega) ht
  · left
    refine change_at_starts hmρ (v0 := false) (fun t ht => ?_) E.H_A u ha
    by_cases h : t < R
    · exact (H_IN_RST t h).1
    · exact E.H_A0 t (by omega) ht

/-- **Bridge, link controller (`bd_link` `ctl.u.u` = `bd_c2n`)**: `FbCelT linkF` with the
physical wire as the pinned route, from LutFbBridge's `link_lutFb` hypotheses plus
H_WIRE_POS, H_FB_PWR and H_IN_RST (request and acknowledge pins 0 during reset). -/
theorem link_fbCelT {req ack rst O qp : Trace} {lo hi wl wh R Es Ea : Nat} {ρ α : Nat → Nat}
    (S : Stage req ack rst O qp lo hi wl wh) (E : Env1 req ack rst O lo hi R ρ α Es Ea)
    (T : Timing1 lo hi wh R Es Ea) (H_LUT_POS : 1 ≤ lo) (H_PWR : ∀ t, t < hi → O t = false)
    (H_WIRE_POS : 1 ≤ wl) (H_FB_PWR : ∀ t, t < wh → qp t = false)
    (H_IN_RST : ∀ t, t < R → req t = false ∧ ack t = false) :
    FbCelT linkF (fun t => (req t, ack t)) O ⟨qp, wl, wh⟩ := by
  obtain ⟨hL, _⟩ := link_lutFb S E T H_LUT_POS H_PWR
  have hlh := win_le S.H_LUT_WIN
  have hwl : wl ≤ wh := by obtain ⟨s, h1, h2, _⟩ := S.H_FB wh (Nat.le_refl _); omega
  have hlat := T.H_LAT; have hrl := T.H_RST_LONG; have hre := E.H_RST_EARLY
  have ha0 := E.H_ACK0
  have hx : Phases (ex req ack qp rst) (cph ρ α) :=
    ⟨WinFifoCausal.s_pre S E T, WinFifoCausal.s_phase S E T⟩
  have hR := WinFifoCausal.cph_ge S E T 0
  have hgap := WinFifoCausal.s_gap S E T
  have hsp : ∀ j, cph ρ α j + hi ≤ cph ρ α (j + 1) := fun j => by have := hgap j; omega
  have hmρ : ∀ j, ρ j < ρ (j + 1) := fun j => by
    have := E.H_SND j; have := nt_lo O (cph ρ α j) (Vph j) hlh (hi := hi)
    have : ρ j ≤ cph ρ α j := Nat.le_max_left _ _
    unfold WinFifoCausal.τs at *; omega
  have hmα : ∀ j, α j < α (j + 1) := fun j => by
    have := E.H_RCV j; have := nt_lo O (cph ρ α j) (Vph j) hlh (hi := hi)
    have : α j ≤ cph ρ α j := Nat.le_max_right _ _
    unfold WinFifoCausal.τs at *; omega
  refine ⟨hL, H_WIRE_POS, IpowCells.bounded_of_winDelay S.H_FB
    (fun t ht => by
      show qp (t + 1) = qp t; have ht' : t + 1 < wh := ht
      rw [H_FB_PWR t (by omega), H_FB_PWR (t + 1) ht']),
    by show qp 0 = O 0; rw [H_FB_PWR 0 (by omega), H_PWR 0 (by omega)], ?_⟩
  show RespAfter wh (fun t => (req t, ack t)) O
  refine respAfter_of_steps S.H_LUT_WIN S.H_NO_REVERT hx H_LUT_POS (by omega) hsp H_PWR
    ⟨by omega, by omega⟩ E.H_SND E.H_RCV ⟨by omega, by omega⟩ (fun u hu => ?_)
  by_cases ha : req (u + 1) = req u
  · right
    have hb' : ack (u + 1) ≠ ack u := fun e => hu (by simp only [ha, e])
    exact change_at_starts hmα (v0 := false) (fun t ht => (H_IN_RST t (by omega)).2)
      E.H_ACK u hb'
  · left
    refine change_at_starts hmρ (v0 := false) (fun t ht => ?_) E.H_REQ u ha
    by_cases h : t < R
    · exact (H_IN_RST t h).1
    · exact E.H_REQ_LOW0 t (by omega) ht

theorem cgate2_cel : ∀ x y q : Bool, cgate [x, y] q = cel2 x y q := by decide +kernel

/-- **Instance: the fork / join-N=2 C-element of IpowCells' contracts** (`cgate` on the pin
list), from the physical `bd_c2` model. -/
theorem cgate2_fbCelT {a b rst O qp : Trace} {lo hi wl wh R Es Ea : Nat} {ρ β : Nat → Nat}
    (C : CelC a b rst O qp lo hi wl wh) (E : EnvC a b rst O lo hi R ρ β Es Ea)
    (T : Timing1 lo hi wh R Es Ea) (H_PWR : ∀ t, t < hi → O t = false)
    (H_WIRE_POS : 1 ≤ wl) (H_FB_PWR : ∀ t, t < wh → qp t = false)
    (H_IN_RST : ∀ t, t < R → a t = false ∧ b t = false) :
    FbCelT cgate (fun t => [a t, b t]) O ⟨qp, wl, wh⟩ :=
  (c2_fbCelT (F := fun p q => cel2 p.1 p.2 q) (fun _ _ _ => rfl) C E T H_PWR H_WIRE_POS H_FB_PWR
    H_IN_RST).map (fun t q => cgate2_cel _ _ _)
    (fun u hu e => hu (by simp only [Prod.mk.injEq] at e; rw [e.1, e.2]))

/-- **Instances: `bd_arbiter`'s `ua1`/`ua2` and `bd_mux`'s `uxa`/`uya`** (the `AMergeC` /
`MuxC` acknowledge fields), from the physical `bd_c2` model. -/
theorem ack_fbCelT {a b rst O qp : Trace} {lo hi wl wh R Es Ea : Nat} {ρ β : Nat → Nat}
    (C : CelC a b rst O qp lo hi wl wh) (E : EnvC a b rst O lo hi R ρ β Es Ea)
    (T : Timing1 lo hi wh R Es Ea) (H_PWR : ∀ t, t < hi → O t = false)
    (H_WIRE_POS : 1 ≤ wl) (H_FB_PWR : ∀ t, t < wh → qp t = false)
    (H_IN_RST : ∀ t, t < R → a t = false ∧ b t = false) :
    FbCelT arbA1F (fun t => (a t, b t)) O ⟨qp, wl, wh⟩ ∧
    FbCelT arbA2F (fun t => (a t, b t)) O ⟨qp, wl, wh⟩ ∧
    FbCelT muxXaF (fun t => (a t, b t)) O ⟨qp, wl, wh⟩ ∧
    FbCelT muxYaF (fun t => (a t, b t)) O ⟨qp, wl, wh⟩ :=
  ⟨c2_fbCelT (fun x y q => (arb_gate x y q).1) C E T H_PWR H_WIRE_POS H_FB_PWR H_IN_RST,
   c2_fbCelT (fun x y q => (arb_gate x y q).2) C E T H_PWR H_WIRE_POS H_FB_PWR H_IN_RST,
   c2_fbCelT (fun x y q => (mux_gate x false false false q y).2.2.1) C E T H_PWR H_WIRE_POS
     H_FB_PWR H_IN_RST,
   c2_fbCelT (fun x y q => (mux_gate false x false false q y).2.2.2) C E T H_PWR H_WIRE_POS
     H_FB_PWR H_IN_RST⟩

/-- **The derivation lands on `ForkCT.ack` as stated**: a 2-way fork's acknowledge C-element
from the physical `bd_c2` model, on the pinned route `⟨qp, wl, wh⟩` (the physical wire). -/
theorem fork2_ack_fbCelT {f o0 o1 : Chan} {rst qp : Trace} {lo hi wl wh R Es Ea : Nat}
    {ρ β : Nat → Nat}
    (C : CelC o0.ack o1.ack rst f.ack qp lo hi wl wh) (E : EnvC o0.ack o1.ack rst f.ack lo hi R ρ β Es Ea)
    (T : Timing1 lo hi wh R Es Ea) (H_PWR : ∀ t, t < hi → f.ack t = false)
    (H_WIRE_POS : 1 ≤ wl) (H_FB_PWR : ∀ t, t < wh → qp t = false)
    (H_IN_RST : ∀ t, t < R → o0.ack t = false ∧ o1.ack t = false) :
    FbCelT cgate (fun t => [o0, o1].map (fun o => o.ack t)) f.ack ⟨qp, wl, wh⟩ :=
  cgate2_fbCelT C E T H_PWR H_WIRE_POS H_FB_PWR H_IN_RST

open Formal.Cells.PipeTimed.Wit (sq sq_pre rstW)

/-- **Switching witness with a nonzero routed feedback delay**: LutFbBridge's real `bd_c2`
loop (`c2_witness`: LUT band `[1, 2]`, feedback wire 1 tick, inputs `sq 4`, `sq 5`, which
disagree on `[4, 5)` so the cell holds through its feedback pin) meets `FbCelT cgate` with the
pinned route `⟨sq 7, 1, 1⟩`, and the node toggles. -/
theorem c2_fbCelT_witness :
    FbCelT cgate (fun t => [sq 4 t, sq 5 t]) (sq 6) ⟨sq 7, 1, 1⟩ ∧
      sq 4 4 ≠ sq 5 4 ∧ sq 6 (5 + 1) ≠ sq 6 5 := by
  obtain ⟨C, E, T, hP, h1, h2, _, _⟩ := LutFbBridge.c2_witness
  exact ⟨cgate2_fbCelT C E T hP (Nat.le_refl 1) (fun t h => sq_pre 7 t (by omega))
    (fun t h => ⟨sq_pre 4 t h, sq_pre 5 t (by omega)⟩), h1, h2⟩

/-! ## 4. IpowCellsT: ipow's per-cell contracts with pinned feedback routes -/

open Formal.Cells.IpowCells (ForkC JoinC SteerC MuxC AMergeC LinkC Contract muxZF extraIn
  ipow_safe_of_contracts DataOK chQ mem_chQ grant_idle dvW dataOK_all cnt_quiet)

/-- `bd_fork` with its ack C-element on the pinned route `r 0`. -/
structure ForkCT (a : Chan) (os : List Chan) (r : Nat → FbRoute) : Prop where
  ne : os ≠ []
  H_WIRE_DI : ∀ o ∈ os, ∀ t, o.req (t + 1) ≠ o.req t → o.req (t + 1) = a.req t
  ack : FbCelT cgate (fun t => os.map (fun o => o.ack t)) a.ack (r 0)
  H_DATA_WIRE : ∀ o ∈ os, ∀ t, o.dat t = a.dat t
  initA : a.ack 0 = false
  initO : ∀ o ∈ os, o.req 0 = false

/-- `bd_join` with its request C-element on the pinned route `r 0`. -/
structure JoinCT (g : List Nat → Nat) (is : List Chan) (ex : List Trace) (o : Chan)
    (r : Nat → FbRoute) : Prop where
  ne : is ≠ []
  req : FbCelT cgate (fun t => is.map (fun i => i.req t) ++ ex.map (fun x => x t)) o.req (r 0)
  H_WIRE_DI : ∀ i ∈ is, ∀ t, i.ack (t + 1) ≠ i.ack t → i.ack (t + 1) = o.ack t
  H_DATA_COMB : ∀ t, o.dat t = g (is.map (fun i => i.dat t))
  initO : o.req 0 = false
  initI : ∀ i ∈ is, i.ack 0 = false

/-- `bd_mux` with `uj0`, `uj1`, `uxa`, `uya` on the pinned routes `r 0 .. r 3`. -/
structure MuxCT (sel : Nat → Bool) (x y c z : Chan) (j0 j1 : Trace) (r : Nat → FbRoute) :
    Prop where
  uj0 : FbCelT muxJ0F (fun t => (x.req t, c.req t, sel (c.dat t))) j0 (r 0)
  uj1 : FbCelT muxJ1F (fun t => (y.req t, c.req t, sel (c.dat t))) j1 (r 1)
  uxa : FbCelT muxXaF (fun t => (j0 t, z.ack t)) x.ack (r 2)
  uya : FbCelT muxYaF (fun t => (j1 t, z.ack t)) y.ack (r 3)
  H_DELAY_LUMPED : LutSI muxZF (fun t => (j0 t, j1 t)) z.req
  H_WIRE_DI : ∀ t, c.ack (t + 1) ≠ c.ack t → c.ack (t + 1) = z.ack t
  H_DATA_COMB : ∀ t, z.dat t = if sel (c.dat t) then y.dat t else x.dat t
  i0 : j0 0 = false
  i1 : j1 0 = false
  iz : z.req 0 = false
  ix : x.ack 0 = false
  iy : y.ack 0 = false
  ic : c.ack 0 = false

/-- `bdc_amerge2_0` with `ua1`, `ua2` on the pinned routes `r 0`, `r 1` (grant fields as in
IpowCells, still hypotheses). -/
structure AMergeCT (x y z : Chan) (g1 g2 : Trace) (r : Nat → FbRoute) : Prop where
  H_ARB1 : ∀ t, g1 (t + 1) ≠ g1 t → g1 (t + 1) = x.req t ∧ (g1 (t + 1) = true → g2 t = false ∧ z.ack t = false)
  H_ARB2 : ∀ t, g2 (t + 1) ≠ g2 t → g2 (t + 1) = y.req t ∧ (g2 (t + 1) = true → g1 t = false ∧ z.ack t = false)
  H_ARB_EXCL : ∀ t, (g1 t && g2 t) = false
  H_GRANT_R0 : ∃ q : Trace,
    (∀ t, g1 t = genF bd_arbiter "ugrant" .O5 ["r1", "r2", "q"] [x.req t, y.req t, q t]) ∧
    (∀ t, g2 t = genF bd_arbiter "ugrant" .O6 ["r1", "r2", "q"] [x.req t, y.req t, q t]) ∧
    (∀ t, z.req (t + 1) ≠ z.req t →
      z.req (t + 1) = genF bd_arbiter "ustate" .O5 ["r1", "r2", "q", "rst", "A0"]
        [x.req t, y.req t, q t, false, z.ack t])
  H_AMERGE_RTZ : ∀ t, z.req t = false → z.req (t + 1) = true → x.ack t = false ∧ y.ack t = false
  ua1 : FbCelT arbA1F (fun t => (g1 t, z.ack t)) x.ack (r 0)
  ua2 : FbCelT arbA2F (fun t => (g2 t, z.ack t)) y.ack (r 1)
  H_GHOST : ∀ t, z.dat t = 2 * (if (g2 t || y.ack t) then y.dat t else x.dat t) + Mux.b2n (g2 t || y.ack t)
  i1 : g1 0 = false
  i2 : g2 0 = false
  iz : z.req 0 = false
  ix : x.ack 0 = false
  iy : y.ack 0 = false

/-- `bd_link` / `bd_pipe` stage with the controller on the pinned route `r 0`. -/
structure LinkCT (i o : Chan) (c : Trace) (r : Nat → FbRoute) : Prop where
  ctl : FbCelT linkF (fun t => (i.req t, o.ack t)) c (r 0)
  H_ACK_DI : ∀ t, i.ack (t + 1) ≠ i.ack t → i.ack (t + 1) = c t
  H_REQ_DI : ∀ t, o.req (t + 1) ≠ o.req t → o.req (t + 1) = c t
  H_LATCH_OPEN : ∀ t, c t = true → o.dat t = i.dat t
  H_LATCH_HOLD : ∀ t, c (t + 1) = false → o.dat (t + 1) = o.dat t
  ic : c 0 = false
  ii : i.ack 0 = false
  io : o.req 0 = false

variable {n : Nat}

/-- **The timed per-operator contract**: IpowCells' `Contract` with every feedback LUT's
`FbCel` replaced by `FbCelT` on the operator's pinned routes `r` (slot 0 = the fork ack /
join request / link controller / `ua1` / `uj0`; mux slots 1..3 = `uj1`, `uxa`, `uya`; amerge
slot 1 = `ua2`). -/
def ContractT (ch : Fin n → Chan) (sv : Nat → Nat) (nx : Nat) (r : Nat → FbRoute) : K n → Prop
  | .forkG i os => ForkCT (ch i) (os.map ch) r
  | .forkH i os _ _ _ _ => ForkCT (ch i) ((os.map Prod.fst).map ch) r
  | .join ins o e js _ => ∃ ex : List Trace, ex.length = nx ∧ JoinCT (jg e js) (ins.map ch) ex (ch o) r
  | .bjoin ins o ec ed => ∃ ex : List Trace, ex.length = nx ∧ JoinCT (bg ec ed) (ins.map ch) ex (ch o) r
  | .steerC j t f => SteerC sel2 (fun _ => 0) (ch j) (fun b => ch (bif b then t else f))
  | .steerD j t f fd _ =>
      SteerC sel2 (fun v => fd.eval [v / 2]) (ch j) (fun b => ch (bif b then t else f))
  | .mux c x y z _ => ∃ j0 j1, MuxCT sel2 (ch x) (ch y) (ch c) (ch z) j0 j1 r
  | .muxn c x0 x1 x2 z _ =>
      ∃ j, MuxN.MuxN selD (fun k => ch (cx3 x0 x1 x2 k)) (ch c) (ch z) j
  | .amerge x y z _ => ∃ g1 g2, AMergeCT (ch x) (ch y) (ch z) g1 g2 r
  | .link i o => ∃ c, LinkCT (ch i) (ch o) c r
  | .src z which _ => Capstone.Src (ch z) (sv which)
  | .sink i => Ops.Gcd.Sink (ch i)

/-- **The timed contract implies IpowCells' contract** (each `FbCelT` gives `FbCel`). -/
theorem contract_of_contractT (ch : Fin n → Chan) (sv : Nat → Nat) (nx : Nat)
    (r : Nat → FbRoute) (k : K n) (h : ContractT ch sv nx r k) : Contract ch sv nx k := by
  cases k with
  | forkG i os => exact ⟨h.ne, h.H_WIRE_DI, h.ack.toFbCel, h.H_DATA_WIRE, h.initA, h.initO⟩
  | forkH i os l hh d hs => exact ⟨h.ne, h.H_WIRE_DI, h.ack.toFbCel, h.H_DATA_WIRE, h.initA, h.initO⟩
  | join ins o e js jw =>
    obtain ⟨ex, hl, J⟩ := h
    exact ⟨ex, hl, J.ne, J.req.toFbCel, J.H_WIRE_DI, J.H_DATA_COMB, J.initO, J.initI⟩
  | bjoin ins o ec ed =>
    obtain ⟨ex, hl, J⟩ := h
    exact ⟨ex, hl, J.ne, J.req.toFbCel, J.H_WIRE_DI, J.H_DATA_COMB, J.initO, J.initI⟩
  | steerC j t f => exact h
  | steerD j t f fd sw => exact h
  | mux c x y z mw =>
    obtain ⟨j0, j1, M⟩ := h
    exact ⟨j0, j1, M.uj0.toFbCel, M.uj1.toFbCel, M.uxa.toFbCel, M.uya.toFbCel, M.H_DELAY_LUMPED,
      M.H_WIRE_DI, M.H_DATA_COMB, M.i0, M.i1, M.iz, M.ix, M.iy, M.ic⟩
  | muxn c x0 x1 x2 z nw => exact h
  | amerge x y z w =>
    obtain ⟨g1, g2, A⟩ := h
    exact ⟨g1, g2, A.H_ARB1, A.H_ARB2, A.H_ARB_EXCL, A.H_GRANT_R0, A.H_AMERGE_RTZ, A.ua1.toFbCel,
      A.ua2.toFbCel, A.H_GHOST, A.i1, A.i2, A.iz, A.ix, A.iy⟩
  | link i o =>
    obtain ⟨c, L⟩ := h
    exact ⟨c, L.ctl.toFbCel, L.H_ACK_DI, L.H_REQ_DI, L.H_LATCH_OPEN, L.H_LATCH_HOLD, L.ic, L.ii, L.io⟩
  | src z which d => exact h
  | sink i => exact h

open Formal.Net.IpowCap (NC NO ops opAt start out0)

/-- **ipow's circuit safety from the TIMED cell contracts**: C-8y's `ipow_circuit_safe3` with
H_CELLS discharged by the 83 operators' `ContractT`s, every feedback LUT on its pinned route
`rt o i` (routed values or symbolic constants; the theorem holds for every choice). -/
theorem ipow_safe_of_contractsT (b e : Nat) (he : e < 2 ^ 32) (ch : Fin NC → Chan)
    (rt : Fin NO → Nat → FbRoute)
    (H_CONTRACTS : ∀ o : Fin NO, ContractT ch (srcV b e) (extraIn o) (rt o) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1) :
    (∀ k v, TokAt (ch out0) k v → (ch out0).dat v = IpowHw.ipowSpec b e) ∧
    (∀ t, closedVals (ch out0) t =
      List.replicate (cnt (fallB (ch out0).ack) t) (IpowHw.ipowSpec b e)) :=
  ipow_safe_of_contracts b e he ch
    (fun o => contract_of_contractT ch _ _ (rt o) (opAt o) (H_CONTRACTS o)) H_BUNDLE H_START_ONCE

/-! ## 5. Non-vacuity with nonzero pinned feedback delays -/

/-- The quiet route with pinned bounds `lo`, `hi`. -/
def rq (L H : Nat → Nat) (i : Nat) : FbRoute := ⟨fun _ => false, L i, H i⟩

/-- A feedback LUT whose pins never move and whose output stays low meets `FbCelT` on the
quiet route, for EVERY pinned `lo ≥ 1` and `hi`. -/
theorem fbCelT_quiet {α : Type} (F : α → Bool → Bool) (p : Nat → α) (hp : ∀ t, p (t + 1) = p t)
    (r : FbRoute) (hq : r.qp = fun _ => false) (hl : 1 ≤ r.lo) :
    FbCelT F p (fun _ => false) r where
  H_LUT_FB := fun _ h => absurd rfl h
  H_FB_POS := hl
  H_FB_ROUTE := ⟨fun _ h => by rw [hq] at h; exact absurd rfl h, fun _ _ _ => by rw [hq]⟩
  H_FB_RST := by rw [hq]
  H_RT_FB := fun u h => absurd (hp u) h

theorem quiet_contractT (sv : Nat → Nat) (dv : Fin n → Nat) (nx : Nat) (L H : Nat → Nat)
    (hL : ∀ i, 1 ≤ L i) (k : K n) (hd : DataOK sv dv k) : ContractT (chQ dv) sv nx (rq L H) k := by
  have fq : ∀ {α : Type} (F : α → Bool → Bool) (p : Nat → α), (∀ t, p (t + 1) = p t) → ∀ i,
      FbCelT F p (fun _ => false) (rq L H i) := fun F p hp i => fbCelT_quiet F p hp _ rfl (hL i)
  cases k with
  | forkG i os =>
    refine ⟨by simpa using hd.1, fun o ho t h => ?_, fq _ _ (fun t => ?_) 0, fun o ho t => ?_, rfl,
      fun o ho => ?_⟩
    · obtain ⟨c, _, rfl⟩ := mem_chQ ho; exact absurd rfl h
    · simp [chQ, List.map_map, Function.comp_def]
    · obtain ⟨c, hc, rfl⟩ := mem_chQ ho; exact hd.2 c hc
    · obtain ⟨c, _, rfl⟩ := mem_chQ ho; rfl
  | forkH i os l hh d hs =>
    refine ⟨by simpa using hd.1, fun o ho t h => ?_, fq _ _ (fun t => ?_) 0, fun o ho t => ?_, rfl,
      fun o ho => ?_⟩
    · obtain ⟨c, _, rfl⟩ := mem_chQ ho; exact absurd rfl h
    · simp [chQ, List.map_map, Function.comp_def]
    · obtain ⟨c, hc, rfl⟩ := mem_chQ ho
      obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hc
      exact hd.2 p hp
    · obtain ⟨c, _, rfl⟩ := mem_chQ ho; rfl
  | join ins o e js jw =>
    refine ⟨List.replicate nx (fun _ => false), List.length_replicate .., by simpa using hd.1,
      fq _ _ (fun t => ?_) 0, fun i hi t h => ?_, fun t => ?_, rfl, fun i hi => ?_⟩
    · simp [chQ, List.map_map, Function.comp_def]
    · obtain ⟨c, _, rfl⟩ := mem_chQ hi; exact absurd rfl h
    · simp only [List.map_map, Function.comp_def, chQ]; exact hd.2
    · obtain ⟨c, _, rfl⟩ := mem_chQ hi; rfl
  | bjoin ins o ec ed =>
    refine ⟨List.replicate nx (fun _ => false), List.length_replicate .., by simpa using hd.1,
      fq _ _ (fun t => ?_) 0, fun i hi t h => ?_, fun t => ?_, rfl, fun i hi => ?_⟩
    · simp [chQ, List.map_map, Function.comp_def]
    · obtain ⟨c, _, rfl⟩ := mem_chQ hi; exact absurd rfl h
    · simp only [List.map_map, Function.comp_def, chQ]; exact hd.2
    · obtain ⟨c, _, rfl⟩ := mem_chQ hi; rfl
  | steerC j t f =>
    refine ⟨fun b u h => absurd rfl h, fun u h => absurd rfl h, fun b u => ?_, rfl, fun b => rfl⟩
    cases b
    · exact hd.2
    · exact hd.1
  | steerD j t f fd sw =>
    refine ⟨fun b u h => absurd rfl h, fun u h => absurd rfl h, fun b u => ?_, rfl, fun b => rfl⟩
    cases b
    · exact hd.2
    · exact hd.1
  | mux c x y z mw =>
    exact ⟨fun _ => false, fun _ => false, fq _ _ (fun _ => rfl) 0, fq _ _ (fun _ => rfl) 1,
      fq _ _ (fun _ => rfl) 2, fq _ _ (fun _ => rfl) 3, fun _ h => absurd rfl h,
      fun _ h => absurd rfl h, fun _ => hd, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | muxn c x0 x1 x2 z nw => exact hd.elim
  | amerge x y z w =>
    refine ⟨fun _ => false, fun _ => false, fun _ h => absurd rfl h, fun _ h => absurd rfl h,
      fun _ => rfl, ⟨fun _ => false, fun _ => grant_idle.1.symm, fun _ => grant_idle.2.symm,
        fun _ h => absurd rfl h⟩, fun _ _ h => by simp [chQ] at h, fq _ _ (fun _ => rfl) 0,
      fq _ _ (fun _ => rfl) 1, fun _ => ?_, rfl, rfl, rfl, rfl, rfl⟩
    simp only [chQ, Bool.or_false, Bool.false_eq_true, ↓reduceIte, Mux.b2n]
    exact hd
  | link i o =>
    exact ⟨fun _ => false, fq _ _ (fun _ => rfl) 0, fun _ h => absurd rfl h, fun _ h => absurd rfl h,
      fun _ h => by simp at h, fun _ _ => rfl, rfl, rfl, rfl⟩
  | src z which d => exact ⟨fun _ h => absurd rfl h, fun _ => hd, rfl⟩
  | sink i => exact ⟨fun _ h => absurd rfl h, rfl⟩

/-- **Non-vacuity of `ipow_safe_of_contractsT` for EVERY pinned bound assignment with nonzero
minimum feedback delays** `L o i ≥ 1` (and any `H`): one run (b = 3, e = 7) meets all 83
timed contracts on routes with exactly those bounds, H_BUNDLE and H_START_ONCE. It is the
all-quiet run (as in IpowCells; network liveness is open); `c2_fbCelT_witness` is the
switching single-cell witness with a nonzero routed delay. -/
theorem ipow_contractsT_satisfiable (L H : Fin NO → Nat → Nat) (hL : ∀ o i, 1 ≤ L o i) :
    ∃ (b e : Nat) (ch : Fin NC → Chan) (rt : Fin NO → Nat → FbRoute),
      (∀ o i, (rt o i).lo = L o i ∧ (rt o i).hi = H o i) ∧ e < 2 ^ 32 ∧
      (∀ o : Fin NO, ContractT ch (srcV b e) (extraIn o) (rt o) (opAt o)) ∧ (∀ c, Held (ch c)) ∧
      (∀ t, cnt (riseB (ch start).req) t ≤ 1) :=
  ⟨3, 7, chQ dvW, fun o => rq (L o) (H o), fun _ _ => ⟨rfl, rfl⟩, by decide,
    fun o => quiet_contractT _ _ _ _ _ (hL o) _ (dataOK_all o),
    fun _ _ _ _ => rfl, fun t => by rw [show (chQ dvW start).req = fun _ => false from rfl, cnt_quiet]; decide⟩

end Formal.Cells.IpowCellsT
