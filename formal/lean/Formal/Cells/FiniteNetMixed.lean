import Formal.Cells.FiniteNetCells

/-!
# Probe Bfin2 (shard B): the mixed network closed by the time-indexed rule; gcd_hw, finite runs

Note: `formal/notes/B-finite-net.md`. Bseg's `mixed_closed` and `gcd_hw_safe_net`
(`AssumeGuaranteeEnds*`) in the time-indexed form of `FiniteNet`: every cell is either a B
gate model (link, `n`-pin C-element, steer branch, and now also the acknowledge OR) or an
assumed TRUNCATED contract; the run may stop.

## Assumed / proved / NOT covered

**Proved:**
* `fnet_closed`: on any network (Bseg's `GD`, verbatim) whose every cell meets its
  truncated contract (`FCellOK`: pins clean on `[0, T)` ⇒ node clean on `[0, T + lo)`),
  with `Wire`s, H_LUT_POS and wire floors, every node and pin is a clean step signal, for
  every edge-set assignment `L` (finite or infinite runs). No H_WAIT, no wire spacing.
* `flink_spec_cell`, `fcel_spec_cell`, `fsteer_spec_cell`, `for_spec_cell`: each B gate
  model gives `FCellOK` (via `tlink`, `tcelG`, `tsteer`, `tor_ex`); `fmixed_closed`;
  `flink_spec_env1`: a link cell of a closed network with finite edge counts has Bfin's
  `FEnv1` and `Timing1`, DERIVED.
* `gcd_hw_safe_fin_net`: C's `gcd_hw_circuit_safe` with every link's `H_CELLS` discharged
  by ONE gate-level network of gcd_hw (`FGcdNetOK`, finite edge counts) in which every link,
  fork N ≤ 4, 2-input join, steer branch AND steer acknowledge OR carries B's gate model;
  contracts remain on the mux cells, the muxn, the 9 amerges, the 3 sources and the 3 fork
  trees (and join1/sink have no cell).

**Assumed (`FGcdNetOK`):** B's gate model of every tied cell, with H_TIMES, the edge-set
equations H_CNT, and the departure bounds per existing edge as EDGE-TIME inequalities (as
Bseg); for the ORs H_ORD/H_DOWN (the branches interleave in token order); H_SEL_STABLE and
token enumerations; network-wide H_RST, H_WIRE, H_LUT_POS, the wire floors; for each link
the two outgoing wires, H_WIRE_SPREAD and the latch data fields; a truncated contract for
every other cell; finite edge counts. Outside: C's `H_CELLS` of the 192 non-link operators,
H_BUNDLE, H_CM_FORCED.

**NOT covered:** no joint witness of `FGcdNetOK` (a gate-level elaboration of all of
gcd_hw on a run; C's channel-level run has no internal fork/join/steer nodes); the
link-chain form `FiniteNet.gcd_hw_safe_fin_chains` has one (`FiniteNetWit`). The mux
acknowledges `uxa`/`uya`, the sources, muxn, amerge and fork trees N ≥ 5 have no truncated
lemma here. Core Lean only.
-/

namespace Formal.Cells.FiniteNet
open Formal.Cells
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo Stage Timing1 cph τs)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.FiniteRuns (FEnv1 FPhysLink fe)
open Formal.Cells.LutFbBridge2 (CelLaw CelG gc)
open Formal.Cells.LutFbBridge2Env (Wire ε ε_lo ash)
open Formal.Cells.AssumeGuaranteeEnds (GPin gE sN cmax cmax_arr cmax_last GC2 GC3 GC4)
open Formal.Cells.AssumeGuaranteeEndsNet (GD)
open Formal.Cells.AssumeGuaranteeMuxOr (oe)
open Formal.Net.Ops.Gen (genF steerF)
open Formal.Gen Formal.Gen.Cells

variable {ι : Type}

/-! ## 1. The rule on a network -/

/-- **A cell's truncated contract**: its pins clean on `[0, T)` (each pin's edge set is its
driver's) give its node clean on `[0, T + lo)`. -/
def FCellOK (D : GD ι) (L : ι → Nat → Prop) (c : ι) : Prop :=
  ∀ T, (∀ p ∈ D.pins c, GPhT p.P (gE D.τ p) (L p.drv) T) →
    GPhT (D.O c) (D.τ c) (L c) (T + D.lo c)

/-- The network-wide wire facts (Bseg's `NetW` without H_SP, with floors instead). -/
structure FNetW (D : GD ι) (L : ι → Nat → Prop) : Prop where
  H_RST : ∀ t, D.rst t = decide (t < D.R)
  H_WIRE : ∀ c, ∀ p ∈ D.pins c, Wire p.wl p.wh (D.O p.drv) p.P
  H_LUT_POS : ∀ c, 1 ≤ D.lo c
  H_FLOOR : ∀ c, ∀ p ∈ D.pins c, ∀ j, L p.drv j → p.wh ≤ D.τ p.drv j + p.wl

/-- **The time-indexed rule on a network.** -/
theorem fnet_closed (D : GD ι) (L : ι → Nat → Prop) (NW : FNetW D L)
    (H_CELL : ∀ c, FCellOK D L c) : ∀ c, GPh (D.O c) (D.τ c) (L c) := by
  have all := ag_trunc (fun c T => GPhT (D.O c) (D.τ c) (L c) T)
    (fun c T => ∀ p ∈ D.pins c, GPhT p.P (gE D.τ p) (L p.drv) T) (fun _ => 1)
    (fun _ => Nat.le_refl 1) (fun _ _ _ h hg => gphT_mono hg h) (fun _ => gphT_zero _ _ _)
    (fun c T ih p hp => gphT_mono (twire (NW.H_WIRE c p hp) (ih p.drv) (NW.H_FLOOR c p hp))
      (by omega))
    (fun c T hA => gphT_mono (H_CELL c T hA) (by have := NW.H_LUT_POS c; omega))
  exact fun c T => all c T

theorem fnet_pins (D : GD ι) (L : ι → Nat → Prop) (NW : FNetW D L)
    (H_CELL : ∀ c, FCellOK D L c) : ∀ c, ∀ p ∈ D.pins c, GPh p.P (gE D.τ p) (L p.drv) :=
  fun c p hp T => gphT_mono (twire (NW.H_WIRE c p hp) (fnet_closed D L NW H_CELL p.drv T)
    (NW.H_FLOOR c p hp)) (by omega)

/-! ## 2. Cell specs, truncated form -/

/-- **A link controller cell** (Bseg's `LinkSpec` with an edge set and per-edge bounds). -/
structure FLinkSpec (D : GD ι) (L : ι → Nat → Prop) (c : ι) (rp ap : GPin ι) (Es Ea : Nat) :
    Prop where
  H_PINS : D.pins c = [rp, ap]
  H_STAGE : Stage rp.P ap.P D.rst (D.O c) (D.qp c) (D.lo c) (D.hi c) (D.fl c) (D.fh c)
  H_PWR : ∀ t, t < D.hi c → D.O c t = false
  H_TIMES : ∀ j, D.τ c j = τs (D.O c) (D.lo c) (D.hi c) (gE D.τ rp) (ash D.R (gE D.τ ap)) j
  H_CNT : ∀ j, L c j ↔ LnL (L rp.drv) (L ap.drv) j
  H_RST_EARLY : ∀ j, D.R ≤ gE D.τ rp j
  H_SND : ∀ j, L c j → L rp.drv (j + 1) → D.τ c j + Es ≤ gE D.τ rp (j + 1)
  H_RCV : ∀ j, L c j → L ap.drv j → D.τ c j + Ea ≤ gE D.τ ap j
  H_T : Timing1 (D.lo c) (D.hi c) (D.fh c) D.R Es Ea

/-- **An `n`-pin C-element cell** (Bseg's `CelSpec`, truncated form). -/
structure FCelSpec {n : Nat} (G : (Fin n → Bool) → Bool → Bool → Bool) (D : GD ι)
    (L : ι → Nat → Prop) (c : ι) (pv : Fin n → GPin ι) (E : Nat) : Prop where
  H_PINS : D.pins c = (List.finRange n).map pv
  H_LAW : CelLaw G
  H_CEL : CelG G (fun t i => (pv i).P t) D.rst (D.O c) (D.qp c) (D.lo c) (D.hi c) (D.fl c)
    (D.fh c)
  H_PWR : ∀ t, t < D.hi c → D.O c t = false
  H_TIMES : ∀ j, D.τ c j =
    nt (D.O c) (D.lo c) (D.hi c) (cmax (fun i => gE D.τ (pv i)) j) (Vph j)
  H_CNT : ∀ j, L c j ↔ ∀ i, L (pv i).drv j
  H_RST_EARLY : ∀ j, L c j → D.R ≤ cmax (fun i => gE D.τ (pv i)) j
  H_SND : ∀ i j, L c j → L (pv i).drv (j + 1) → D.τ c j + E ≤ gE D.τ (pv i) (j + 1)
  H_RST_LONG : D.hi c + D.fh c ≤ D.R
  H_LAT : D.hi c + D.fh c ≤ D.lo c + E

/-- **A steer branch cell** (Bseg's `SteerSpec`, truncated form). -/
structure FSteerSpec (D : GD ι) (L : ι → Nat → Prop) (c : ι) (rp : GPin ι) (b : Bool)
    (s σ : Nat → Bool) (κ : Nat → Nat) : Prop where
  H_PINS : D.pins c = [rp]
  H_LUT_WIN : Win (D.lo c) (D.hi c) (fun t => steerF b (rp.P t, s t)) (D.O c)
  H_NO_REVERT : NoRevertI (D.lo c) (D.hi c) (fun t => steerF b (rp.P t, s t)) (D.O c)
  H_PWR : ∀ t, t < D.hi c → D.O c t = false
  H_TIMES : ∀ j, D.τ c j = nt (D.O c) (D.lo c) (D.hi c) (gc κ (gE D.τ rp) j) (Vph j)
  H_CNT : ∀ j, L c j ↔ L rp.drv (sN κ j)
  H_DOWN : ∀ j, L rp.drv (j + 1) → L rp.drv j
  H_INC : ∀ j, L rp.drv (j + 1) → gE D.τ rp j < gE D.τ rp (j + 1)
  H_SEL_STABLE : ∀ n t, L rp.drv (2 * n) → gE D.τ rp (2 * n) ≤ t →
    (L rp.drv (2 * n + 1) → t < gE D.τ rp (2 * n + 1)) → s t = σ n
  H_KAPPA : ∀ m, κ m < κ (m + 1)
  H_KAPPA_B : ∀ m, σ (κ m) = b
  H_KAPPA_ALL : ∀ n, σ n = b → ∃ m, κ m = n
  H_FLOOR : ∀ j, L c j → D.hi c ≤ gc κ (gE D.τ rp) j + D.lo c

/-- **An acknowledge / request OR cell** (`F` the generated LUT, equal to `a₁ ∨ a₀`: the
REAL `bd_steer` `uack`, `uor_gate` for `bd_mux` `uor`): branch pins `ap false`, `ap true`. -/
structure FOrSpec (D : GD ι) (L : ι → Nat → Prop) (c : ι) (F : Bool → Bool → Bool)
    (ap : Bool → GPin ι) (σ : Nat → Bool) (κ : Bool → Nat → Nat) : Prop where
  H_PINS : D.pins c = [ap false, ap true]
  H_GATE : ∀ a0 a1, F a0 a1 = (a1 || a0)
  H_LUT_WIN : Win (D.lo c) (D.hi c) (fun t => F ((ap false).P t) ((ap true).P t)) (D.O c)
  H_NO_REVERT : NoRevertI (D.lo c) (D.hi c) (fun t => F ((ap false).P t) ((ap true).P t))
    (D.O c)
  H_PWR : ∀ t, t < D.hi c → D.O c t = false
  H_TIMES : ∀ k, D.τ c k = nt (D.O c) (D.lo c) (D.hi c) (oe σ (fun b => gE D.τ (ap b)) k) (Vph k)
  H_CNT : ∀ k, L c k ↔ Lor σ (fun b => L (ap b).drv) k
  H_KAPPA : ∀ b m, κ b m < κ b (m + 1)
  H_KAPPA_B : ∀ b m, σ (κ b m) = b
  H_KAPPA_ALL : ∀ b n, σ n = b → ∃ m, κ b m = n
  H_DOWN : ∀ k, Lor σ (fun b => L (ap b).drv) (k + 1) → Lor σ (fun b => L (ap b).drv) k
  H_ORD : ∀ k, Lor σ (fun b => L (ap b).drv) (k + 1) →
    oe σ (fun b => gE D.τ (ap b)) k < oe σ (fun b => gE D.τ (ap b)) (k + 1)
  H_FLOOR : ∀ k, L c k → D.hi c ≤ oe σ (fun b => gE D.τ (ap b)) k + D.lo c

section cls
variable {D : GD ι} {L : ι → Nat → Prop} (NW : FNetW D L)
include NW

theorem flink_spec_cell {c : ι} {rp ap : GPin ι} {Es Ea : Nat} (S : FLinkSpec D L c rp ap Es Ea) :
    FCellOK D L c := by
  intro T hA
  have hr := hA rp (by rw [S.H_PINS]; simp)
  have ha := hA ap (by rw [S.H_PINS]; simp)
  have hτ : D.τ c = τs (D.O c) (D.lo c) (D.hi c) (gE D.τ rp) (ash D.R (gE D.τ ap)) :=
    funext S.H_TIMES
  have hL : L c = LnL (L rp.drv) (L ap.drv) := funext fun j => propext (S.H_CNT j)
  rw [hτ, hL]
  refine tlink (E := min Es Ea) S.H_STAGE NW.H_RST S.H_T.H_RST_LONG S.H_T.H_LAT S.H_PWR
    S.H_RST_EARLY (fun j hj hr' => ?_) (fun j hj ha' => ?_) hr ha
  · rw [← hτ]; have := S.H_SND j (by rw [hL]; exact hj) hr'; omega
  · rw [← hτ]; have := S.H_RCV j (by rw [hL]; exact hj) ha'; omega

theorem fcel_spec_cell {n : Nat} {G : (Fin n → Bool) → Bool → Bool → Bool} {c : ι}
    {pv : Fin n → GPin ι} {E : Nat} (S : FCelSpec G D L c pv E) : FCellOK D L c := by
  intro T hA
  have hτ : D.τ c = fe (D.O c) (D.lo c) (D.hi c) (cmax (fun i => gE D.τ (pv i))) :=
    funext S.H_TIMES
  rw [hτ]
  exact tcelG S.H_LAW S.H_CEL NW.H_RST S.H_RST_LONG S.H_LAT S.H_PWR
    (ρ := fun i => gE D.τ (pv i)) (Lp := fun i => L (pv i).drv)
    (cmax_arr _) (cmax_last _) S.H_CNT S.H_RST_EARLY
    (fun i j hj hl => by rw [← S.H_TIMES j]; exact S.H_SND i j hj hl)
    (fun i => hA (pv i) (by rw [S.H_PINS]; exact List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩))

omit NW in
theorem fsteer_spec_cell {c : ι} {rp : GPin ι} {b : Bool} {s σ : Nat → Bool} {κ : Nat → Nat}
    (S : FSteerSpec D L c rp b s σ κ) : FCellOK D L c := by
  intro T hA
  have hτ : D.τ c = fe (D.O c) (D.lo c) (D.hi c) (gc κ (gE D.τ rp)) := funext S.H_TIMES
  have hL : L c = fun j => L rp.drv (sN κ j) := funext fun j => propext (S.H_CNT j)
  rw [hτ, hL]
  exact tsteer b S.H_LUT_WIN S.H_NO_REVERT S.H_PWR S.H_DOWN S.H_INC S.H_SEL_STABLE S.H_KAPPA
    S.H_KAPPA_B S.H_KAPPA_ALL (fun j hj => S.H_FLOOR j (by rw [hL]; exact hj))
    (hA rp (by rw [S.H_PINS]; simp))

omit NW in
theorem for_spec_cell {c : ι} {F : Bool → Bool → Bool} {ap : Bool → GPin ι} {σ : Nat → Bool}
    {κ : Bool → Nat → Nat} (S : FOrSpec D L c F ap σ κ) : FCellOK D L c := by
  intro T hA
  have hτ : D.τ c = fe (D.O c) (D.lo c) (D.hi c) (oe σ (fun b => gE D.τ (ap b))) :=
    funext S.H_TIMES
  have hL : L c = Lor σ (fun b => L (ap b).drv) := funext fun j => propext (S.H_CNT j)
  have ex : (fun t => F ((ap false).P t) ((ap true).P t)) =
      fun t => (fun b => (ap b).P) true t || (fun b => (ap b).P) false t :=
    funext fun t => S.H_GATE _ _
  have hW := S.H_LUT_WIN; have hN := S.H_NO_REVERT
  rw [ex] at hW hN
  rw [hτ, hL]
  refine tnode hW hN (tor_ex (a := fun b => (ap b).P) S.H_KAPPA S.H_KAPPA_B S.H_KAPPA_ALL
    S.H_DOWN S.H_ORD (fun b => ?_)) (fun k hk => S.H_FLOOR k (by rw [hL]; exact hk)) S.H_PWR
  cases b
  · exact hA (ap false) (by rw [S.H_PINS]; simp)
  · exact hA (ap true) (by rw [S.H_PINS]; simp)

end cls

/-! ## 3. The mixed network, closed -/

/-- A cell meets one of the proved specs. -/
def FProved (D : GD ι) (L : ι → Nat → Prop) (c : ι) : Prop :=
  (∃ rp ap Es Ea, FLinkSpec D L c rp ap Es Ea) ∨
  (∃ (n : Nat) (G : (Fin n → Bool) → Bool → Bool → Bool) (pv : Fin n → GPin ι) (E : Nat),
    FCelSpec G D L c pv E) ∨
  (∃ rp b s σ κ, FSteerSpec D L c rp b s σ κ) ∨
  (∃ F ap σ κ, FOrSpec D L c F ap σ κ)

theorem fproved_ok {D : GD ι} {L : ι → Nat → Prop} (NW : FNetW D L) {c : ι}
    (h : FProved D L c) : FCellOK D L c := by
  rcases h with ⟨_, _, _, _, S⟩ | ⟨_, _, _, _, S⟩ | ⟨_, _, _, _, _, S⟩ | ⟨_, _, _, _, S⟩
  · exact flink_spec_cell NW S
  · exact fcel_spec_cell NW S
  · exact fsteer_spec_cell S
  · exact for_spec_cell S

/-- **The circle closed on a mixed network, finite or infinite runs.** Every cell is a link,
an `n`-pin C-element, a steer branch or an OR with its B gate model, or an assumed truncated
contract. -/
theorem fmixed_closed (D : GD ι) (L : ι → Nat → Prop) (NW : FNetW D L)
    (H_CLS : ∀ c, FProved D L c ∨ FCellOK D L c) : ∀ c, GPh (D.O c) (D.τ c) (L c) :=
  fnet_closed D L NW fun c => (H_CLS c).elim (fproved_ok NW) id

/-- **A link cell of a closed mixed network has `FEnv1` and `Timing1`** (finite edge
counts `n`), DERIVED. -/
theorem flink_spec_env1 (D : GD ι) (L : ι → Nat → Prop) (NW : FNetW D L)
    (H_CLS : ∀ c, FProved D L c ∨ FCellOK D L c) (n : ι → Nat) (hn : ∀ c j, L c j ↔ j < n c)
    {c : ι} {rp ap : GPin ι} {Es Ea : Nat} (S : FLinkSpec D L c rp ap Es Ea) :
    FEnv1 rp.P ap.P D.rst (D.O c) (D.lo c) (D.hi c) D.R (gE D.τ rp) (ash D.R (gE D.τ ap))
      (n rp.drv) (n ap.drv) Es Ea ∧ Timing1 (D.lo c) (D.hi c) (D.fh c) D.R Es Ea := by
  have hok : ∀ c, FCellOK D L c := fun c => (H_CLS c).elim (fproved_ok NW) id
  have pr := fnet_pins D L NW hok c rp (by rw [S.H_PINS]; simp)
  have pa := fnet_pins D L NW hok c ap (by rw [S.H_PINS]; simp)
  have hL : ∀ c, L c = fun j => j < n c := fun c => funext fun j => propext (hn c j)
  rw [hL] at pr pa
  have pr' := gph_fin_iff.1 pr
  have pa' := gph_fin_iff.1 pa
  have hlnk : ∀ j, j < n rp.drv → (∀ i, j = i + 1 → i < n ap.drv) → L c j := fun j h1 h2 =>
    (S.H_CNT j).2 ⟨(hn _ j).2 h1, fun i hi => (hn _ i).2 (h2 i hi)⟩
  refine ⟨{ H_RST := NW.H_RST
            H_REQ_LOW0 := fun t _ h => pr'.pre t h
            H_REQ := pr'.ph
            H_ACK0 := rfl
            H_ACK := fun j t hj h1 h2 => ?_
            H_RST_EARLY := S.H_RST_EARLY 0
            H_SND := fun j h1 h2 => ?_
            H_RCV := fun j h1 h2 => ?_ }, S.H_T⟩
  · cases j with
    | zero =>
      rw [pa'.pre t (by by_cases h : n ap.drv = 0; exact Or.inl h; exact Or.inr (h2 (by omega)))]
      rfl
    | succ k => rw [pa'.ph k t (by omega) h1 h2, PipeTimed.Vph_succ, Bool.not_not]
  · rw [← S.H_TIMES j]
    exact S.H_SND j (hlnk j (by omega) (fun i hi => by omega)) ((hn _ (j + 1)).2 h1)
  · rw [← S.H_TIMES j]
    exact S.H_RCV j (hlnk j h2 (fun i hi => by omega)) ((hn _ j).2 h1)

/-! ## 4. gcd_hw as one gate-level network, finite runs, steer ORs gate-modelled -/

open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe
open Formal.Cells.LutFbBridge2Env (isLink)
open Formal.Cells.AssumeGuaranteeEndsCap (GcdNet forkOuts joinIns steerIn d0 LinkOut)

/-- **A gate-level elaboration of gcd_hw** (Bseg's `GcdNet`) plus the acknowledge OR cell
`ao o` of each steer. -/
structure FGcdNet extends GcdNet where
  ao : Fin NO → ι

/-- The `n`-pin C-element tie (Bseg's `CelTie`, truncated spec). -/
def FCelTie (D : GD ι) (L : ι → Nat → Prop) (c : ι) (cs : List (Fin NC))
    (sel : Fin NC → Nat → Bool) : Prop :=
  (cs.length = 2 ∧ ∃ (pv : Fin 2 → GPin ι) (E : Nat), FCelSpec GC2 D L c pv E ∧
    ∀ i, (pv i).P = sel (cs.getD i.val d0)) ∨
  (cs.length = 3 ∧ ∃ (pv : Fin 3 → GPin ι) (E : Nat), FCelSpec GC3 D L c pv E ∧
    ∀ i, (pv i).P = sel (cs.getD i.val d0)) ∨
  (cs.length = 4 ∧ ∃ (pv : Fin 4 → GPin ι) (E : Nat), FCelSpec GC4 D L c pv E ∧
    ∀ i, (pv i).P = sel (cs.getD i.val d0))

/-- The cells that carry a B gate model. -/
def FTied (N : FGcdNet) (c : N.ι) : Prop :=
  (∃ o i o', opAt o = .link i o' ∧ c = N.lk o) ∨
  (∃ o os, forkOuts (opAt o) = some os ∧ 2 ≤ os.length ∧ os.length ≤ 4 ∧ c = N.fa o) ∨
  (∃ o ins, joinIns (opAt o) = some ins ∧ ins.length = 2 ∧ c = N.jr o) ∨
  (∃ o j b, steerIn (opAt o) = some j ∧ c = N.sb o b) ∨
  (∃ o j, steerIn (opAt o) = some j ∧ c = N.ao o)

/-- **The hypotheses on the elaboration, finite runs.** -/
structure FGcdNetOK (ch : Fin NC → Chan) (N : FGcdNet) (L : N.ι → Nat → Prop) (n : N.ι → Nat) :
    Prop where
  NW : FNetW N.D L
  H_FIN : ∀ c j, L c j ↔ j < n c
  H_LINK : ∀ o i o', opAt o = .link i o' → ∃ rp ap Es Ea, FLinkSpec N.D L (N.lk o) rp ap Es Ea ∧
    rp.P = (ch i).req ∧ ap.P = (ch o').ack ∧ LinkOut N.D (N.lk o) (ch i) (ch o') Es Ea
  H_FORK : ∀ o os, forkOuts (opAt o) = some os → 2 ≤ os.length → os.length ≤ 4 →
    FCelTie N.D L (N.fa o) os (fun c => (ch c).ack)
  H_JOIN : ∀ o ins, joinIns (opAt o) = some ins → ins.length = 2 →
    FCelTie N.D L (N.jr o) ins (fun c => (ch c).req)
  H_STEER : ∀ o j, steerIn (opAt o) = some j → ∀ b, ∃ rp s σ κ,
    FSteerSpec N.D L (N.sb o b) rp b s σ κ ∧ rp.P = (ch j).req
  H_SOR : ∀ o j, steerIn (opAt o) = some j → ∃ ap σ κ,
    FOrSpec N.D L (N.ao o) (fun a0 a1 => genF bd_steer "uack" .O ["ack0", "ack1"] [a0, a1])
      ap σ κ
  H_REST : ∀ c, ¬ FTied N c → FCellOK N.D L c

theorem fcelTie_proved {D : GD ι} {L : ι → Nat → Prop} {c : ι} {cs : List (Fin NC)}
    {sel : Fin NC → Nat → Bool} (h : FCelTie D L c cs sel) : FProved D L c := by
  rcases h with ⟨_, pv, E, S, _⟩ | ⟨_, pv, E, S, _⟩ | ⟨_, pv, E, S, _⟩
  · exact Or.inr (Or.inl ⟨2, GC2, pv, E, S⟩)
  · exact Or.inr (Or.inl ⟨3, GC3, pv, E, S⟩)
  · exact Or.inr (Or.inl ⟨4, GC4, pv, E, S⟩)

section net
variable {ch : Fin NC → Chan} {N : FGcdNet} {L : N.ι → Nat → Prop} {n : N.ι → Nat}
  (H : FGcdNetOK ch N L n)
include H

theorem fgcd_cls (c : N.ι) : FProved N.D L c ∨ FCellOK N.D L c := by
  by_cases ht : FTied N c
  · refine Or.inl ?_
    rcases ht with ⟨o, i, o', h, rfl⟩ | ⟨o, os, h, h1, h2, rfl⟩ | ⟨o, ins, h, h1, rfl⟩ |
      ⟨o, j, b, h, rfl⟩ | ⟨o, j, h, rfl⟩
    · obtain ⟨rp, ap, Es, Ea, S, _⟩ := H.H_LINK o i o' h
      exact Or.inl ⟨rp, ap, Es, Ea, S⟩
    · exact fcelTie_proved (H.H_FORK o os h h1 h2)
    · exact fcelTie_proved (H.H_JOIN o ins h h1)
    · obtain ⟨rp, s, σ, κ, S, _⟩ := H.H_STEER o j h b
      exact Or.inr (Or.inr (Or.inl ⟨rp, b, s, σ, κ, S⟩))
    · obtain ⟨ap, σ, κ, S⟩ := H.H_SOR o j h
      exact Or.inr (Or.inr (Or.inr ⟨_, ap, σ, κ, S⟩))
  · exact Or.inr (H.H_REST c ht)

/-- **Every node of gcd_hw's gate-level network is a clean step signal (finite run).** -/
theorem fgcd_net_nodes : ∀ c, GPh (N.D.O c) (N.D.τ c) (L c) :=
  fmixed_closed N.D L H.NW (fgcd_cls H)

/-- **Every link of gcd_hw is Bfin's `FPhysLink`, its `FEnv1` DERIVED from the network.** -/
theorem fphysLink_of_net {o : Fin NO} {i o' : Fin NC} (h : opAt o = .link i o') :
    FPhysLink (ch i) (ch o') := by
  obtain ⟨rp, ap, Es, Ea, S, e1, e2, wla, wha, wlr, whr, Wa, Wr, s1, s2, s3, s4, d1, d2⟩ :=
    H.H_LINK o i o' h
  obtain ⟨E, Tm⟩ := flink_spec_env1 N.D L H.NW (fgcd_cls H) n H.H_FIN S
  have St := S.H_STAGE
  rw [e1, e2] at St E
  exact ⟨N.D.rst, N.D.O (N.lk o), N.D.qp (N.lk o), N.D.lo (N.lk o), N.D.hi (N.lk o),
    N.D.fl (N.lk o), N.D.fh (N.lk o), N.D.R, Es, Ea, wla, wha, wlr, whr, n rp.drv, n ap.drv,
    gE N.D.τ rp, ash N.D.R (gE N.D.τ ap), St, E, Tm, H.NW.H_LUT_POS _,
    S.H_PWR, Wa, Wr, s1, s2, s3, s4, d1, d2⟩

end net

/-- **End to end, finite runs, one gate-level network.** C's gcd_hw circuit safety with
`H_CELLS` of all 175 links discharged by a gate-level network of gcd_hw (`FGcdNetOK`, finite
edge counts) in which every link, fork N ≤ 4, 2-input join, steer branch and steer
acknowledge OR carries B's gate model and only the other cells carry a truncated contract.
Still assumed: the edge-time bounds of `FGcdNetOK`, and C's `H_CELLS` (other 192
operators), H_BUNDLE, H_CM_FORCED.
CAVEAT (SelfAuditB9; audit P12b, 2026-10-31): the hypothesis does NOT bind the pin
drivers (`GPin.drv`) or the cell set to gcd_hw's netlist. A pinless cell's contract is
the bare claim that its node is clean (`fcellOK_nil_iff`), and a link fed by two such
cells gets its environment from them alone (`flink_env1_local`). So this theorem does not
enforce that any link's environment comes from the gate models named above; "gate-
modelled" describes the intended elaboration only. C's `H_CELLS` for the 192 non-link
operators stays a hypothesis (`H_OTHER`): B's gate models are used only to derive link
environments, never to discharge an operator contract. Driver-bound form: `FiniteNetBound`. -/
theorem gcd_hw_safe_fin_net (a b : Nat) (ch : Fin NC → Chan) (N : FGcdNet)
    (L : N.ι → Nat → Prop) (n : N.ι → Nat) (H : FGcdNetOK ch N L n)
    (H_OTHER : ∀ o : Fin NO, isLink (opAt o) = false → Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_CM_FORCED : ∃ y, Good a b y ∧ ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) :=
  FiniteRuns.gcd_hw_safe_fin_links a b ch (fun _ _ _ h => fphysLink_of_net H h) H_OTHER
    H_BUNDLE H_CM_FORCED

end Formal.Cells.FiniteNet
