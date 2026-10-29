import Formal.Cells.AssumeGuaranteeEnds

/-!
# Probe Bseg (shard B): a network of mixed cell classes, closed

`AssumeGuaranteeEnds` gives segment lemmas for the C-element classes (forks N ≤ 4, joins
N = 2) and steer branches. This file packages each class as a CELL SPEC (B's gate model
plus the edge-time definition of its node; no environment assumption, no contract) and
closes any network whose cells are each either one of these specs or an assumed segment
contract (`mixed_closed`, by `net_closed_gen`).

## Assumed / proved / NOT covered

**Assumed** (per cell, named fields): `LinkSpec` (B's `Stage`, real `bd_c2n`), `CelSpec`
(B's `CelG` with `CelLaw`, real `bd_c2`/`bd_c3`/`bd_c4`), `SteerSpec` (the real `bd_steer`
`u` LUT, `Win` + H_NO_REVERT, H_SEL_STABLE, token enumeration); for each: H_PWR, H_TIMES
(the node's edges read off its own pins), and the DEPARTURE BOUNDS (`H_SND`, `H_RCV`,
`H_RST_EARLY`; for steers `H_SPACE`, `H_INC`) as inequalities between EDGE TIMES, with
H_RST_LONG/H_LAT on constants. Network-wide: H_RST, H_WIRE, H_LUT_POS, H_SP (wire spacing,
an edge-time inequality, as `net_closed`). Every other cell: a segment contract with its
H_WAIT (`Contract`).

**Proved:** `gE_mono` (pin edges non-decreasing, from H_SP); `link_spec_cell`/`_wait`,
`cel_spec_cell`/`_wait`, `steer_spec_cell`/`_wait` (H_CELL and H_WAIT of each class, from
its spec alone; the waits are unconditional consequences of H_TIMES); `mixed_closed`:
every node of such a network is a clean step signal; `mixed_pins`; `link_spec_env1`: a
`LinkSpec` cell of a closed network has Bfb's `Env1` and `Timing1` (so `PhysLink`'s
environment is DERIVED).

**NOT covered:** the departure bounds are assumed as edge-time inequalities, not derived
from delay constants (Bnet's `Chain` derives them for all-link chains; for a mixed network
they follow along each handshake cycle from the H_WAITs, a path argument not done here).
Core Lean only.
-/

namespace Formal.Cells.AssumeGuaranteeEndsNet
open Formal.Cells
open Formal.Cells.AssumeGuaranteeLinks (SegK phases_of_segK segK_of_phases wire_segK)
open Formal.Cells.AssumeGuaranteeFork (link_cell ack_shape)
open Formal.Cells.AssumeGuaranteeEnds
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo Stage Env1 Timing1 cph τs)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.LutFbBridge (Phases)
open Formal.Cells.LutFbBridge2 (CelLaw CelG gc)
open Formal.Cells.LutFbBridge2Env (Wire ε ε_lo ash)
open Formal.Net.Ops.Gen (steerF)

/-- The data of a gate-level network: nodes, edge times, delays, reset, pins. -/
structure GD (ι : Type) where
  O : ι → Nat → Bool
  τ : ι → Nat → Nat
  lo : ι → Nat
  hi : ι → Nat
  fl : ι → Nat
  fh : ι → Nat
  qp : ι → Nat → Bool
  rst : Nat → Bool
  R : Nat
  pins : ι → List (GPin ι)

/-! ## 1. Pin edges are monotone under the wire spacing -/

theorem gE_step {ι : Type} {τ : ι → Nat → Nat} {p : GPin ι} {O : Nat → Bool}
    (W : Wire p.wl p.wh O p.P) (hsp : ∀ j, τ p.drv j + p.wh < τ p.drv (j + 1) + p.wl)
    (j : Nat) : gE τ p j ≤ gE τ p (j + 1) := by
  have h1 : gE τ p j ≤ τ p.drv j + p.wh + 1 := by
    unfold gE ε nt; exact PipeTimed.lfind_le _ _
  have h2 := ε_lo W (τ p.drv) (j + 1)
  have := hsp j
  unfold gE; unfold gE at h1; omega

theorem gE_mono {ι : Type} {τ : ι → Nat → Nat} {p : GPin ι} {O : Nat → Bool}
    (W : Wire p.wl p.wh O p.P) (hsp : ∀ j, τ p.drv j + p.wh < τ p.drv (j + 1) + p.wl)
    {j j' : Nat} (h : j ≤ j') : gE τ p j ≤ gE τ p j' := by
  induction j' with
  | zero => have : j = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j' ih =>
    rcases Nat.lt_or_ge j (j' + 1) with h' | h'
    · have := ih (by omega); have := gE_step W hsp j'; omega
    · have : j = j' + 1 := by omega
      subst this; exact Nat.le_refl _

/-! ## 2. Cell specs: B's gate models, no environment, no contract -/

variable {ι : Type}

/-- **A link controller cell** (`bd_c2n`, B's `Stage`): request pin `rp` (reads segments
`≤ k`), acknowledge pin `ap` (segments `< k`). -/
structure LinkSpec (D : GD ι) (c : ι) (rp ap : GPin ι) (Es Ea : Nat) : Prop where
  H_PINS : D.pins c = [rp, ap]
  H_NBR : rp.nb = fun k => k + 1
  H_NBA : ap.nb = fun k => k
  H_STAGE : Stage rp.P ap.P D.rst (D.O c) (D.qp c) (D.lo c) (D.hi c) (D.fl c) (D.fh c)
  H_PWR : ∀ t, t < D.hi c → D.O c t = false
  H_TIMES : ∀ j, D.τ c j = τs (D.O c) (D.lo c) (D.hi c) (gE D.τ rp) (ash D.R (gE D.τ ap)) j
  H_RST_EARLY : D.R ≤ gE D.τ rp 0
  H_SND : ∀ j, D.τ c j + Es ≤ gE D.τ rp (j + 1)
  H_RCV : ∀ j, D.τ c j + Ea ≤ gE D.τ ap j
  H_T : Timing1 (D.lo c) (D.hi c) (D.fh c) D.R Es Ea

/-- **A C-element cell with `n` pins** (B's `CelG` of a LUT `G` with the C-element laws):
every pin read at segments `≤ k`; the phase start is the last pin arrival `cmax`. -/
structure CelSpec {n : Nat} (G : (Fin n → Bool) → Bool → Bool → Bool) (D : GD ι) (c : ι)
    (pv : Fin n → GPin ι) (E : Nat) : Prop where
  H_NE : 0 < n
  H_PINS : D.pins c = (List.finRange n).map pv
  H_NB : ∀ i, (pv i).nb = fun k => k + 1
  H_LAW : CelLaw G
  H_CEL : CelG G (fun t i => (pv i).P t) D.rst (D.O c) (D.qp c) (D.lo c) (D.hi c) (D.fl c)
    (D.fh c)
  H_PWR : ∀ t, t < D.hi c → D.O c t = false
  H_TIMES : ∀ j, D.τ c j =
    nt (D.O c) (D.lo c) (D.hi c) (cmax (fun i => gE D.τ (pv i)) j) (Vph j)
  H_RST_EARLY : D.R ≤ cmax (fun i => gE D.τ (pv i)) 0
  H_SND : ∀ i j, D.τ c j + E ≤ gE D.τ (pv i) (j + 1)
  H_RST_LONG : D.hi c + D.fh c ≤ D.R
  H_LAT : D.hi c + D.fh c ≤ D.lo c + E

/-- **A steer branch cell** (`bd_steer` `u`, O5 for `b = false`, O6 for `b = true`): one pin,
the input request, read up to segment `sN κ k`. -/
structure SteerSpec (D : GD ι) (c : ι) (rp : GPin ι) (b : Bool) (s σ : Nat → Bool)
    (κ : Nat → Nat) : Prop where
  H_PINS : D.pins c = [rp]
  H_NB : rp.nb = fun k => sN κ k + 1
  H_LUT_WIN : Win (D.lo c) (D.hi c) (fun t => steerF b (rp.P t, s t)) (D.O c)
  H_NO_REVERT : NoRevertI (D.lo c) (D.hi c) (fun t => steerF b (rp.P t, s t)) (D.O c)
  H_PWR : ∀ t, t < D.hi c → D.O c t = false
  H_TIMES : ∀ j, D.τ c j = nt (D.O c) (D.lo c) (D.hi c) (gc κ (gE D.τ rp) j) (Vph j)
  /-- the input request's edges strictly increase (an edge-time fact). -/
  H_INC : ∀ k, gE D.τ rp k < gE D.τ rp (k + 1)
  H_SEL_STABLE : ∀ n t, gE D.τ rp (2 * n) ≤ t → t < gE D.τ rp (2 * n + 1) → s t = σ n
  H_KAPPA : ∀ m, κ m < κ (m + 1)
  H_KAPPA_B : ∀ m, σ (κ m) = b
  H_KAPPA_ALL : ∀ n, σ n = b → ∃ m, κ m = n
  H_SPACE : D.hi c ≤ gc κ (gE D.τ rp) 0 ∧
    ∀ j, gc κ (gE D.τ rp) j + D.hi c < gc κ (gE D.τ rp) (j + 1) + D.lo c

/-- **An assumed cell**: a segment contract and its causality (H_WAIT). -/
def Contract (D : GD ι) (c : ι) : Prop :=
  (∀ k, GA D.τ D.pins c k → SegK (D.O c) (D.τ c) k) ∧
  (∀ p ∈ D.pins c, ∀ k k', k' < p.nb k → gE D.τ p k' + D.lo c ≤ D.τ c k)

/-- The network-wide wire facts. -/
structure NetW (D : GD ι) : Prop where
  H_RST : ∀ t, D.rst t = decide (t < D.R)
  H_WIRE : ∀ c, ∀ p ∈ D.pins c, Wire p.wl p.wh (D.O p.drv) p.P
  H_LUT_POS : ∀ c, 1 ≤ D.lo c
  H_SP : ∀ c, ∀ p ∈ D.pins c, ∀ j,
    p.wh ≤ D.τ p.drv j ∧ D.τ p.drv j + p.wh < D.τ p.drv (j + 1) + p.wl

/-! ## 3. H_CELL and H_WAIT of each class -/

section cls
variable {D : GD ι} (NW : NetW D)
include NW

theorem link_spec_cell {c : ι} {rp ap : GPin ι} {Es Ea : Nat} (L : LinkSpec D c rp ap Es Ea)
    (k : Nat) (hA : GA D.τ D.pins c k) : SegK (D.O c) (D.τ c) k := by
  have hr : rp ∈ D.pins c := by rw [L.H_PINS]; simp
  have ha : ap ∈ D.pins c := by rw [L.H_PINS]; simp
  rw [show D.τ c = _ from funext L.H_TIMES]
  exact link_cell (E := min Es Ea) L.H_STAGE NW.H_RST L.H_T.H_RST_LONG L.H_T.H_LAT
    (NW.H_LUT_POS c) L.H_PWR L.H_RST_EARLY
    (fun j => by rw [← L.H_TIMES j]; have := L.H_SND j; omega)
    (fun j => by rw [← L.H_TIMES j]; have := L.H_RCV j; omega) k
    (fun k' h => hA rp hr k' (by rw [L.H_NBR]; dsimp only; omega))
    (fun k' h => hA ap ha k' (by rw [L.H_NBA]; dsimp only; omega))

theorem link_spec_wait {c : ι} {rp ap : GPin ι} {Es Ea : Nat} (L : LinkSpec D c rp ap Es Ea) :
    ∀ p ∈ D.pins c, ∀ k k', k' < p.nb k → gE D.τ p k' + D.lo c ≤ D.τ c k := by
  intro p hp k k' hk
  have hlh := win_le L.H_STAGE.H_LUT_WIN
  have hn := nt_lo (D.O c) (cph (gE D.τ rp) (ash D.R (gE D.τ ap)) k) (Vph k) hlh (hi := D.hi c)
  rw [L.H_TIMES k]; unfold τs
  rw [L.H_PINS] at hp
  rcases List.mem_cons.1 hp with rfl | hp
  · rw [L.H_NBR] at hk; dsimp only at hk
    have hrm := gE_mono (NW.H_WIRE c p (by rw [L.H_PINS]; simp))
      (fun j => (NW.H_SP c p (by rw [L.H_PINS]; simp) j).2) (show k' ≤ k by omega)
    have : gE D.τ p k ≤ cph (gE D.τ p) (ash D.R (gE D.τ ap)) k := Nat.le_max_left _ _
    omega
  · have hp : p = ap := by simpa using hp
    subst hp
    rw [L.H_NBA] at hk; dsimp only at hk
    obtain ⟨k0, rfl⟩ : ∃ k0, k = k0 + 1 := ⟨k - 1, by omega⟩
    have ham := gE_mono (NW.H_WIRE c p (by rw [L.H_PINS]; simp))
      (fun j => (NW.H_SP c p (by rw [L.H_PINS]; simp) j).2) (show k' ≤ k0 by omega)
    have : ash D.R (gE D.τ p) (k0 + 1) ≤ cph (gE D.τ rp) (ash D.R (gE D.τ p)) (k0 + 1) :=
      Nat.le_max_right _ _
    have e : ash D.R (gE D.τ p) (k0 + 1) = gE D.τ p k0 := rfl
    omega

theorem cel_spec_cell {n : Nat} {G : (Fin n → Bool) → Bool → Bool → Bool} {c : ι}
    {pv : Fin n → GPin ι} {E : Nat} (Cs : CelSpec G D c pv E) (k : Nat)
    (hA : GA D.τ D.pins c k) : SegK (D.O c) (D.τ c) k := by
  rw [show D.τ c = _ from funext Cs.H_TIMES]
  have hmem : ∀ i, pv i ∈ D.pins c := fun i => by
    rw [Cs.H_PINS]; exact List.mem_map.2 ⟨i, List.mem_finRange i, rfl⟩
  exact celG_cell Cs.H_LAW Cs.H_CEL ⟨0, Cs.H_NE⟩ NW.H_RST Cs.H_RST_LONG Cs.H_LAT Cs.H_PWR
    (cmax_arr _) (cmax_last _) Cs.H_RST_EARLY
    (fun i j => by rw [← Cs.H_TIMES j]; exact Cs.H_SND i j) k
    (fun i k' h => hA (pv i) (hmem i) k' (by rw [Cs.H_NB i]; dsimp only; omega))

theorem cel_spec_wait {n : Nat} {G : (Fin n → Bool) → Bool → Bool → Bool} {c : ι}
    {pv : Fin n → GPin ι} {E : Nat} (Cs : CelSpec G D c pv E) :
    ∀ p ∈ D.pins c, ∀ k k', k' < p.nb k → gE D.τ p k' + D.lo c ≤ D.τ c k := by
  intro p hp k k' hk
  have hp' := hp
  rw [Cs.H_PINS] at hp'
  obtain ⟨i, _, rfl⟩ := List.mem_map.1 hp'
  rw [Cs.H_NB i] at hk; dsimp only at hk
  have hm := gE_mono (NW.H_WIRE c (pv i) hp) (fun j => (NW.H_SP c (pv i) hp j).2)
    (show k' ≤ k by omega)
  have hw := celG_wait Cs.H_CEL (cmax_arr (fun i => gE D.τ (pv i))) i k
  rw [Cs.H_TIMES k]; omega

omit NW in
theorem steer_spec_cell {c : ι} {rp : GPin ι} {b : Bool} {s σ : Nat → Bool} {κ : Nat → Nat}
    (Ss : SteerSpec D c rp b s σ κ) (k : Nat) (hA : GA D.τ D.pins c k) :
    SegK (D.O c) (D.τ c) k := by
  have hr : rp ∈ D.pins c := by rw [Ss.H_PINS]; simp
  rw [show D.τ c = _ from funext Ss.H_TIMES]
  exact steer_segK b Ss.H_LUT_WIN Ss.H_NO_REVERT Ss.H_PWR Ss.H_INC Ss.H_SEL_STABLE
    Ss.H_KAPPA Ss.H_KAPPA_B Ss.H_KAPPA_ALL Ss.H_SPACE k
    (fun k' h => hA rp hr k' (by rw [Ss.H_NB]; dsimp only; omega))

omit NW in
theorem steer_spec_wait {c : ι} {rp : GPin ι} {b : Bool} {s σ : Nat → Bool} {κ : Nat → Nat}
    (Ss : SteerSpec D c rp b s σ κ) :
    ∀ p ∈ D.pins c, ∀ k k', k' < p.nb k → gE D.τ p k' + D.lo c ≤ D.τ c k := by
  intro p hp k k' hk
  have hp' := hp
  rw [Ss.H_PINS] at hp'
  have e : p = rp := by simpa using hp'
  subst e
  rw [Ss.H_NB] at hk; dsimp only at hk
  rw [Ss.H_TIMES k]
  exact steer_wait (win_le Ss.H_LUT_WIN) Ss.H_INC k k' hk

end cls

/-! ## 4. The mixed network, closed -/

/-- A cell meets one of the proved specs. -/
def Proved (D : GD ι) (c : ι) : Prop :=
  (∃ rp ap Es Ea, LinkSpec D c rp ap Es Ea) ∨
  (∃ (n : Nat) (G : (Fin n → Bool) → Bool → Bool → Bool) (pv : Fin n → GPin ι) (E : Nat),
    CelSpec G D c pv E) ∨
  (∃ rp b s σ κ, SteerSpec D c rp b s σ κ)

/-- **The assume-guarantee circle closed on a mixed network.** Every cell is a link, an
`n`-pin C-element or a steer branch with its B gate model (no environment, no contract), or
an assumed segment contract; the wires and H_LUT_POS hold, and the wire spacing H_SP. Then
every node is a clean step signal. -/
theorem mixed_closed (D : GD ι) (NW : NetW D) (H_CLS : ∀ c, Proved D c ∨ Contract D c) :
    ∀ c, Phases (D.O c) (D.τ c) := by
  refine net_closed_gen D.O D.τ D.lo D.pins (fun c k hA => ?_) NW.H_WIRE
    (fun c => ?_) NW.H_LUT_POS NW.H_SP
  · rcases H_CLS c with ((⟨_, _, _, _, L⟩ | ⟨_, _, _, _, Cs⟩ | ⟨_, _, _, _, _, Ss⟩) | K)
    · exact link_spec_cell NW L k hA
    · exact cel_spec_cell NW Cs k hA
    · exact steer_spec_cell Ss k hA
    · exact K.1 k hA
  · rcases H_CLS c with ((⟨_, _, _, _, L⟩ | ⟨_, _, _, _, Cs⟩ | ⟨_, _, _, _, _, Ss⟩) | K)
    · exact link_spec_wait NW L
    · exact cel_spec_wait NW Cs
    · exact steer_spec_wait Ss
    · exact K.2

theorem mixed_pins (D : GD ι) (NW : NetW D) (H_CLS : ∀ c, Proved D c ∨ Contract D c) :
    ∀ c, ∀ p ∈ D.pins c, Phases p.P (gE D.τ p) :=
  net_pins_gen D.O D.τ D.pins (mixed_closed D NW H_CLS) NW.H_WIRE NW.H_SP

/-- **A link cell of a closed mixed network has `Env1` and `Timing1`** (Bfb's environment
of `link_lutFb`/`link_guar`), DERIVED: the pin shapes from `mixed_pins`, the departure
bounds from its spec. -/
theorem link_spec_env1 (D : GD ι) (NW : NetW D) (H_CLS : ∀ c, Proved D c ∨ Contract D c)
    {c : ι} {rp ap : GPin ι} {Es Ea : Nat} (L : LinkSpec D c rp ap Es Ea) :
    Env1 rp.P ap.P D.rst (D.O c) (D.lo c) (D.hi c) D.R (gE D.τ rp) (ash D.R (gE D.τ ap)) Es Ea ∧
    Timing1 (D.lo c) (D.hi c) (D.fh c) D.R Es Ea := by
  have pr := mixed_pins D NW H_CLS c rp (by rw [L.H_PINS]; simp)
  have pa := mixed_pins D NW H_CLS c ap (by rw [L.H_PINS]; simp)
  exact ⟨{ H_RST := NW.H_RST
           H_REQ_LOW0 := fun t _ h => pr.pre t h
           H_REQ := pr.ph
           H_ACK0 := rfl
           H_ACK := ack_shape pa
           H_RST_EARLY := L.H_RST_EARLY
           H_SND := fun j => by rw [← L.H_TIMES j]; exact L.H_SND j
           H_RCV := fun j => by rw [← L.H_TIMES j]; exact L.H_RCV j }, L.H_T⟩

/-! ## 5. Non-vacuity: a live mixed network (source contract, a real link, sink contract) -/

namespace Wit
open Formal.Cells.AssumeGuaranteeLinks (wD w_chain w_chainT chain_witness c_hspF c_hspB w_εF w_εB)
open Formal.Cells.PipeTimed.Wit (sq)
open Formal.Cells.LutFbBridge2Env (τ4 phases_sq)

inductive C3 | src | lnk | snk
  deriving DecidableEq

open C3

def idx : C3 → Nat
  | src => 0 | lnk => 1 | snk => 2

def pA : GPin C3 := ⟨lnk, (wD 1).ack 0, 1, 1, fun k => k⟩
def rp : GPin C3 := ⟨src, (wD 1).req 1, 1, 1, fun k => k + 1⟩
def ap : GPin C3 := ⟨snk, (wD 1).ack 1, 1, 1, fun k => k⟩
def pR : GPin C3 := ⟨lnk, (wD 1).req 2, 1, 1, fun k => k + 1⟩

/-- Bnet's live chain `wD 1` as a mixed network: the link is a `LinkSpec` cell, the source
and the sink are `Contract` cells. -/
def wG : GD C3 where
  O c := (wD 1).O (idx c)
  τ c := (wD 1).τ (idx c)
  lo c := (wD 1).lo (idx c)
  hi c := (wD 1).hi (idx c)
  fl c := (wD 1).fl (idx c)
  fh c := (wD 1).fh (idx c)
  qp c := (wD 1).qp (idx c)
  rst := (wD 1).rst
  R := (wD 1).R
  pins
    | src => [pA]
    | lnk => [rp, ap]
    | snk => [pR]

theorem w_link : LinkSpec wG lnk rp ap 3 3 where
  H_PINS := rfl
  H_NBR := rfl
  H_NBA := rfl
  H_STAGE := (w_chain 1).H_STAGE 0 (by decide)
  H_PWR := (w_chain 1).H_PWR 0 (by decide)
  H_TIMES := (w_chain 1).H_TIMES 0 (by decide)
  H_RST_EARLY := by show 4 ≤ (wD 1).εF 0 0; rw [w_εF]; decide
  H_SND j := by
    have := (chain_witness 1).2.2.2.1 0 j
    show (wD 1).τ 1 j + 3 ≤ (wD 1).εF 0 (j + 1); exact Nat.le_of_eq this
  H_RCV j := by
    have := (chain_witness 1).2.2.2.2 0 j
    show (wD 1).τ 1 j + 3 ≤ (wD 1).εB 1 j; exact Nat.le_of_eq this
  H_T := ⟨by decide, by decide, by decide⟩

theorem w_netW : NetW wG where
  H_RST _ := rfl
  H_WIRE c p hp := by
    cases c <;> simp [wG] at hp <;> (try rcases hp with rfl | rfl) <;> (try subst hp)
    · exact (w_chain 1).H_WB 0 (by decide)
    · exact (w_chain 1).H_WF 0 (by decide)
    · exact (w_chain 1).H_WB 1 (by decide)
    · exact (w_chain 1).H_WF 1 (by decide)
  H_LUT_POS _ := Nat.le_refl 1
  H_SP c p hp j := by
    cases c <;> simp [wG] at hp <;> (try rcases hp with rfl | rfl) <;> (try subst hp)
    · exact c_hspB (w_chain 1) (w_chainT 1) 0 (by decide) j
    · exact c_hspF (w_chain 1) (w_chainT 1) 0 (by decide) j
    · exact c_hspB (w_chain 1) (w_chainT 1) 1 (by decide) j
    · exact c_hspF (w_chain 1) (w_chainT 1) 1 (by decide) j

theorem w_cls (c : C3) : Proved wG c ∨ Contract wG c := by
  cases c
  · refine Or.inr ⟨fun k _ => segK_of_phases (phases_sq 3) k, fun p hp k k' hk => ?_⟩
    simp [wG] at hp; subst hp
    have hk' : k' < k := hk
    show (wD 1).εB 0 k' + 1 ≤ τ4 3 k; rw [w_εB]; unfold τ4; omega
  · exact Or.inl (Or.inl ⟨rp, ap, 3, 3, w_link⟩)
  · refine Or.inr ⟨fun k _ => segK_of_phases (phases_sq 7) k, fun p hp k k' hk => ?_⟩
    simp [wG] at hp; subst hp
    have hk' : k' < k + 1 := hk
    show (wD 1).εF 1 k' + 1 ≤ τ4 7 k; rw [w_εF]; unfold τ4; omega

/-- **Non-vacuity of `mixed_closed`/`link_spec_env1`**: on this live run (Bnet's real
`bd_c2n` link, LUT band `[1, 3]`, wires 1) every hypothesis holds, with the link a
`LinkSpec` cell (no environment, no contract) and its departure bounds met with equality. -/
theorem mixed_witness :
    NetW wG ∧ (∀ c, Proved wG c ∨ Contract wG c) ∧ LinkSpec wG lnk rp ap 3 3 ∧
    (∀ j, wG.τ lnk j + 3 = gE wG.τ rp (j + 1)) :=
  ⟨w_netW, w_cls, w_link, fun j => (chain_witness 1).2.2.2.1 0 j⟩

end Wit

end Formal.Cells.AssumeGuaranteeEndsNet
