import Formal.Cells.AssumeGuaranteeLinks

/-!
# Probe Bnet (shard B): the assume-guarantee rule on any network of segment contracts, and
# the link + 2-way fork network closed

## Assumed / proved / NOT covered

**Proved (generic):** `net_closed`: for ANY network of cells, each with a list of input
pins (driver, wire band, offset 0 or 1), if every cell meets a SEGMENT CONTRACT (H_CELL:
its node's segment `k` holds if its pins' segments `≤ k - off` hold), every pin is a
`Wire`, every cell waits `lo ≥ 1` for each pin (H_WAIT, the strict-causality side
condition), and the wire spacing (H_SP) and monotonicity (H_MONO) hold, then every node is
a clean step signal. Proof: `AssumeGuarantee.ag_time` with time = segment end.

**Instance: link + 2-way fork** (`Fork`, `ForkT`): a source `S`, an upstream link `U`, the
fork's acknowledge C-element `F` (`bd_c2`, B's `CelC`), consumer links `L0`, `L1`, sinks
`K0`, `K1`, eleven wires (`fork_env`'s network with all neighbours present).
Assumed: B's gate models (`Stage` ×3, `CelC`), H_PWR, H_LUT_POS, `Wire` ×11, the edge-time
equations (H_TU/H_TF/H_T0/H_T1), the ends' contracts (`SRC_*`, `K0_WAIT`, `K1_WAIT`,
`END_SEG`), and `ForkT` (`Timing1` per gate with the derived slacks, H_WIRE_R, H_CYC).
NO `Env1`/`EnvC` hypothesis on `U`, `F`, `L0`, `L1`.
Proved: the unconditional waits and spacings (`f_wait`, `f_sp`, departure bounds
`f_snd*`/`f_rcv*`); `fork_nodes`, `fork_pins` (every node and pin clean); `fork_env1U`,
`fork_env1L0`, `fork_env1L1` (`Env1`, `Ea` of `U` = the SLOWER branch cycle),
`fork_envCF` (Bfb's `EnvC` of the fork C-element, the two branch cycles, as `fork_env`);
`fork_lutFb` (C's `link_bound` premises for `U`, `L0`, `L1` and `fork2_cel`'s for `F`).
Non-vacuity: `fork_witness`, a live run of the REAL cells (transport LUTs of the real
`bd_c2n`/`bd_c2` excitations, phases of 7 ticks, `U → L1` wire 2 ticks): `F`'s pins
disagree for a tick each phase and `L0` holds through its feedback; `U`'s derived
acknowledge slack is met with equality.

**NOT covered:** forks with N ≥ 3 (C-trees); on gcd_hw no 2-way fork is fed by a link
(Bfb2's `fork_from_link_count`), so `U` is a stand-in for the fork's real upstream
class; the ends' contracts are assumed. Core Lean only.
-/

namespace Formal.Cells.AssumeGuaranteeFork
open Formal.Cells
open Formal.Cells.AssumeGuarantee (ag_time)
open Formal.Cells.AssumeGuaranteeLinks (SegK phases_of_segK segK_of_phases wire_segK link_segK
  celc_segK)
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo Stage Env1 Timing1 cph τs)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.LutFbBridge (Phases CelC EnvC)
open Formal.Cells.LutFbBridge2Env (Wire ε ε_lo ash)

/-! ## 1. Any network of segment contracts -/

/-- An input pin of a cell: its driving cell, its trace, the wire's band, and its OFFSET
(`0`: the cell's segment `k` reads the driver's segment `k`, a request-like pin; `1`: it
reads segment `k - 1`, an acknowledge-like pin). -/
structure NPin (ι : Type) where
  drv : ι
  P : Nat → Bool
  wl : Nat
  wh : Nat
  off : Nat

/-- The pin's edges: `ε` of the driver's edges. -/
def pinE {ι : Type} (τ : ι → Nat → Nat) (p : NPin ι) : Nat → Nat := ε p.P p.wl p.wh (τ p.drv)

/-- **The environment assumption of segment `k` of cell `c`**: every input pin's segments
`k' ≤ k - off`. -/
def NetA {ι : Type} (τ : ι → Nat → Nat) (pins : ι → List (NPin ι)) (c : ι) (k : Nat) : Prop :=
  ∀ p ∈ pins c, ∀ k', k' + p.off ≤ k → SegK p.P (pinE τ p) k'

/-- **The assume-guarantee rule on a network of cells.** Each cell `c` has a node `O c` with
edges `τ c` and a list of input pins. Assumed:
* H_CELL: each cell's SEGMENT CONTRACT (its node's segment `k` holds if its pins' segments
  `≤ k - off` hold);
* H_WIRE: each pin is a `Wire` from its driver's node;
* H_WAIT (strict causality): each cell's edge `j + off` comes at least `lo c ≥ 1` after its
  pin's edge `j` (H_LUT_POS);
* H_SP: the spacing `wire_segK` needs (driver edges more than `wh - wl` apart, after `wh`);
* H_MONO: edge times non-decreasing.
Proved: every node is a clean step signal with its edges. The causality side condition is
H_WAIT with `lo c ≥ 1`: without it the induction has no well-founded measure
(`AssumeGuarantee.zero_delay_cex`). -/
theorem net_closed {ι : Type} (O : ι → Nat → Bool) (τ : ι → Nat → Nat) (lo : ι → Nat)
    (pins : ι → List (NPin ι))
    (H_CELL : ∀ c k, NetA τ pins c k → SegK (O c) (τ c) k)
    (H_WIRE : ∀ c, ∀ p ∈ pins c, Wire p.wl p.wh (O p.drv) p.P)
    (H_WAIT : ∀ c, ∀ p ∈ pins c, ∀ j, pinE τ p j + lo c ≤ τ c (j + p.off))
    (H_LUT_POS : ∀ c, 1 ≤ lo c)
    (H_SP : ∀ c, ∀ p ∈ pins c, ∀ j,
      p.wh ≤ τ p.drv j ∧ τ p.drv j + p.wh < τ p.drv (j + 1) + p.wl)
    (H_MONO : ∀ c j, τ c j ≤ τ c (j + 1)) :
    ∀ c, Phases (O c) (τ c) := by
  have mono : ∀ c j j', j ≤ j' → τ c j ≤ τ c j' := by
    intro c j j' h
    induction j' with
    | zero => have : j = 0 := by omega
              subst this; exact Nat.le_refl _
    | succ j' ih =>
      rcases Nat.lt_or_ge j (j' + 1) with h' | h'
      · have := ih (by omega); have := H_MONO c j'; omega
      · have : j = j' + 1 := by omega
        subst this; exact Nat.le_refl _
  have all := ag_time (fun e : ι × Nat => τ e.1 e.2) (fun e => SegK (O e.1) (τ e.1) e.2)
    (fun e => NetA τ pins e.1 e.2) (fun e h => H_CELL e.1 e.2 h)
    (fun e ih p hp k' hk' => by
      have hw := H_WIRE e.1 p hp
      have t1 := mono p.drv k' (e.2 - p.off) (by omega)
      have t2 := ε_lo hw (τ p.drv) (e.2 - p.off)
      have t3 := H_WAIT e.1 p hp (e.2 - p.off)
      rw [show e.2 - p.off + p.off = e.2 by omega] at t3
      have := H_LUT_POS e.1
      have hG := ih (p.drv, k') (by unfold pinE at t3; simp only; omega)
      exact wire_segK hw k' hG (fun j _ => H_SP e.1 p hp j))
  exact fun c => phases_of_segK fun k => all (c, k)

/-! ## 2. The link + 2-way fork network

Cells: a source `S`, a link `U`, the fork's acknowledge C-element `F` (`bd_c2`), two consumer
links `L0`, `L1`, two sinks `K0`, `K1`. Wires (11): `S → U.req`, `U → S.ack`,
`U → L0.req`, `U → L1.req`, `L0 → F.a`, `L1 → F.b`, `F → U.ack`, `L0 → K0.req`,
`K0 → L0.ack`, `L1 → K1.req`, `K1 → L1.ack`. This is `fork_env`'s network with every
neighbour of `U`, `F`, `L0`, `L1` present. -/

inductive FC | S | U | F | L0 | L1 | K0 | K1
  deriving DecidableEq

inductive WI | reqU | ackS | req0 | req1 | aF | bF | ackU | reqK0 | ack0 | reqK1 | ack1
  deriving DecidableEq

open FC WI

def WI.drv : WI → FC
  | reqU => S | ackS => U | req0 => U | req1 => U | aF => L0 | bF => L1 | ackU => F
  | reqK0 => L0 | ack0 => K0 | reqK1 => L1 | ack1 => K1

def WI.cons : WI → FC
  | reqU => U | ackS => S | req0 => L0 | req1 => L1 | aF => F | bF => F | ackU => U
  | reqK0 => K0 | ack0 => L0 | reqK1 => K1 | ack1 => L1

def WI.off : WI → Nat
  | ackS => 1 | ackU => 1 | ack0 => 1 | ack1 => 1
  | reqU => 0 | req0 => 0 | req1 => 0 | aF => 0 | bF => 0 | reqK0 => 0 | reqK1 => 0

def pinsW : FC → List WI
  | S => [ackS] | U => [reqU, ackU] | F => [aF, bF] | L0 => [req0, ack0] | L1 => [req1, ack1]
  | K0 => [reqK0] | K1 => [reqK1]

theorem cons_of_mem {c : FC} {w : WI} (h : w ∈ pinsW c) : w.cons = c := by
  cases c <;> simp [pinsW] at h <;> rcases h with rfl | rfl <;> rfl

structure ForkData where
  R : Nat
  O : FC → Nat → Bool
  qp : FC → Nat → Bool
  rst : Nat → Bool
  lo : FC → Nat
  hi : FC → Nat
  fl : FC → Nat
  fh : FC → Nat
  τ : FC → Nat → Nat
  P : WI → Nat → Bool
  wl : WI → Nat
  wh : WI → Nat

namespace ForkData
variable (D : ForkData)

def npin (w : WI) : NPin FC := ⟨w.drv, D.P w, D.wl w, D.wh w, w.off⟩
def pins (c : FC) : List (NPin FC) := (pinsW c).map D.npin
/-- Pin edges. -/
def pe (w : WI) : Nat → Nat := ε (D.P w) (D.wl w) (D.wh w) (D.τ w.drv)

/-- Derived departure slacks (`fork_env`'s branch cycles). -/
def EsU : Nat := D.wl ackS + D.lo S + D.wl reqU
def EaU : Nat := max (D.wl req0 + D.lo L0 + D.wl aF + D.lo F + D.wl ackU)
  (D.wl req1 + D.lo L1 + D.wl bF + D.lo F + D.wl ackU)
def EsF : Nat := D.wl ackU + D.lo U + D.wl req0 + D.lo L0 + D.wl aF
def EbF : Nat := D.wl ackU + D.lo U + D.wl req1 + D.lo L1 + D.wl bF
def Es0 : Nat := D.wl aF + D.lo F + D.wl ackU + D.lo U + D.wl req0
def Ea0 : Nat := D.wl reqK0 + D.lo K0 + D.wl ack0
def Es1 : Nat := D.wl bF + D.lo F + D.wl ackU + D.lo U + D.wl req1
def Ea1 : Nat := D.wl reqK1 + D.lo K1 + D.wl ack1

/-- A lower bound on each cell's edge spacing (unconditional, `f_sp`). -/
def cyc : FC → Nat
  | S => D.wl reqU + D.lo U + D.wl ackS + D.lo S
  | U => D.lo U + max D.EsU D.EaU
  | F => D.lo F + max D.EsF D.EbF
  | L0 => D.lo L0 + max D.Es0 D.Ea0
  | L1 => D.lo L1 + max D.Es1 D.Ea1
  | K0 => D.wl ack0 + D.lo L0 + D.wl reqK0 + D.lo K0
  | K1 => D.wl ack1 + D.lo L1 + D.wl reqK1 + D.lo K1

end ForkData

/-- **The gate relations of the fork network and the ends' contracts.** No environment
hypothesis on `U`, `F`, `L0`, `L1`. -/
structure Fork (D : ForkData) : Prop where
  H_RST : ∀ t, D.rst t = decide (t < D.R)
  H_STU : Stage (D.P reqU) (D.P ackU) D.rst (D.O U) (D.qp U) (D.lo U) (D.hi U) (D.fl U) (D.fh U)
  H_ST0 : Stage (D.P req0) (D.P ack0) D.rst (D.O L0) (D.qp L0) (D.lo L0) (D.hi L0) (D.fl L0)
    (D.fh L0)
  H_ST1 : Stage (D.P req1) (D.P ack1) D.rst (D.O L1) (D.qp L1) (D.lo L1) (D.hi L1) (D.fl L1)
    (D.fh L1)
  H_CELF : CelC (D.P aF) (D.P bF) D.rst (D.O F) (D.qp F) (D.lo F) (D.hi F) (D.fl F) (D.fh F)
  H_PWR : ∀ c, c = U ∨ c = F ∨ c = L0 ∨ c = L1 → ∀ t, t < D.hi c → D.O c t = false
  H_LUT_POS : ∀ c, 1 ≤ D.lo c
  H_WIRE : ∀ w, Wire (D.wl w) (D.wh w) (D.O w.drv) (D.P w)
  /-- **H_TIMES**: every gate's edge times read off its own trace. -/
  H_TU : ∀ j, D.τ U j = τs (D.O U) (D.lo U) (D.hi U) (D.pe reqU) (ash D.R (D.pe ackU)) j
  H_TF : ∀ j, D.τ F j = nt (D.O F) (D.lo F) (D.hi F) (cph (D.pe aF) (D.pe bF) j) (Vph j)
  H_T0 : ∀ j, D.τ L0 j = τs (D.O L0) (D.lo L0) (D.hi L0) (D.pe req0) (ash D.R (D.pe ack0)) j
  H_T1 : ∀ j, D.τ L1 j = τs (D.O L1) (D.lo L1) (D.hi L1) (D.pe req1) (ash D.R (D.pe ack1)) j
  /-- **Ends' contracts** (assume-guarantee form, as in `Chain`). -/
  SRC_WAIT : ∀ j, D.pe ackS j + D.lo S ≤ D.τ S (j + 1)
  SRC_T0 : D.R ≤ D.τ S 0 + D.wl reqU ∧ D.wh reqU ≤ D.τ S 0
  K0_WAIT : ∀ j, D.pe reqK0 j + D.lo K0 ≤ D.τ K0 j
  K1_WAIT : ∀ j, D.pe reqK1 j + D.lo K1 ≤ D.τ K1 j
  END_SEG : ∀ c, c = S ∨ c = K0 ∨ c = K1 → ∀ k, NetA D.τ D.pins c k → SegK (D.O c) (D.τ c) k

/-- **Timing of the fork network**: `Timing1` per gate with the derived slacks, H_WIRE_R,
H_CYC (each wire's maximum below its driver's minimum cycle). -/
structure ForkT (D : ForkData) : Prop where
  H_RST_LONG : ∀ c, c = U ∨ c = F ∨ c = L0 ∨ c = L1 → D.hi c + D.fh c ≤ D.R
  H_LAT_U : D.hi U + D.fh U ≤ D.lo U + min D.EsU D.EaU
  H_LAT_F : D.hi F + D.fh F ≤ D.lo F + min D.EsF D.EbF
  H_LAT_0 : D.hi L0 + D.fh L0 ≤ D.lo L0 + min D.Es0 D.Ea0
  H_LAT_1 : D.hi L1 + D.fh L1 ≤ D.lo L1 + min D.Es1 D.Ea1
  H_WIRE_R : ∀ w, D.wh w ≤ D.R
  H_CYC : ∀ w, D.wh w ≤ D.cyc w.drv

/-- A link's segment contract in the `NetA` form (request offset 0, acknowledge offset 1). -/
theorem link_cell {req ack rst O qp : Nat → Bool} {lo hi wl wh R E : Nat} {ρ αs : Nat → Nat}
    (St : Stage req ack rst O qp lo hi wl wh) (H_RST : ∀ t, rst t = decide (t < R))
    (H_RST_LONG : hi + wh ≤ R) (H_LAT : hi + wh ≤ lo + E) (H_LUT_POS : 1 ≤ lo)
    (H_PWR : ∀ t, t < hi → O t = false) (H_RST_EARLY : R ≤ ρ 0)
    (H_SND : ∀ j, τs O lo hi ρ (ash R αs) j + E ≤ ρ (j + 1))
    (H_RCV : ∀ j, τs O lo hi ρ (ash R αs) j + E ≤ αs j) (k : Nat)
    (hr : ∀ k', k' ≤ k → SegK req ρ k') (ha : ∀ k', k' + 1 ≤ k → SegK ack αs k') :
    SegK O (τs O lo hi ρ (ash R αs)) k := by
  refine link_segK St H_RST H_RST_LONG H_LAT H_LUT_POS H_PWR rfl H_RST_EARLY H_SND H_RCV k
    (fun hk t _ ht => ?_) (fun j hk => ?_)
  · subst hk; exact hr 0 (Nat.le_refl _) t (Nat.zero_le _) ht
  · subst hk
    refine ⟨fun t h1 h2 => hr (j + 1) (Nat.le_refl _) t h1 h2, fun t h1 h2 => ?_⟩
    have hs := ha j (Nat.le_refl _)
    cases j with
    | zero => rw [hs t (Nat.zero_le _) h2]; rfl
    | succ j' => rw [hs t h1 h2, PipeTimed.Vph_succ, Bool.not_not]; rfl

section fork
variable {D : ForkData} (K : Fork D)
include K

theorem f_lhU : D.lo U ≤ D.hi U := win_le K.H_STU.H_LUT_WIN
theorem f_lh0 : D.lo L0 ≤ D.hi L0 := win_le K.H_ST0.H_LUT_WIN
theorem f_lh1 : D.lo L1 ≤ D.hi L1 := win_le K.H_ST1.H_LUT_WIN
theorem f_lhF : D.lo F ≤ D.hi F := win_le K.H_CELF.H_LUT_WIN

theorem f_eps (w : WI) (j : Nat) : D.τ w.drv j + D.wl w ≤ D.pe w j :=
  ε_lo (K.H_WIRE w) (D.τ w.drv) j

/-- **Unconditional waits** (strict causality, `lo ≥ 1`): every cell's edge `j + off` comes
at least `lo` after its pin's edge `j`. -/
theorem f_wait (w : WI) (j : Nat) : D.pe w j + D.lo w.cons ≤ D.τ w.cons (j + w.off) := by
  have lU := f_lhU K; have l0 := f_lh0 K; have l1 := f_lh1 K; have lF := f_lhF K
  cases w
  · show D.pe reqU j + D.lo U ≤ D.τ U (j + 0)
    rw [K.H_TU]; unfold τs
    have := nt_lo (D.O U) (cph (D.pe reqU) (ash D.R (D.pe ackU)) (j + 0)) (Vph (j + 0)) lU
      (hi := D.hi U)
    have : D.pe reqU j ≤ cph (D.pe reqU) (ash D.R (D.pe ackU)) (j + 0) := Nat.le_max_left _ _
    omega
  · exact K.SRC_WAIT j
  · show D.pe req0 j + D.lo L0 ≤ D.τ L0 (j + 0)
    rw [K.H_T0]; unfold τs
    have := nt_lo (D.O L0) (cph (D.pe req0) (ash D.R (D.pe ack0)) (j + 0)) (Vph (j + 0)) l0
      (hi := D.hi L0)
    have : D.pe req0 j ≤ cph (D.pe req0) (ash D.R (D.pe ack0)) (j + 0) := Nat.le_max_left _ _
    omega
  · show D.pe req1 j + D.lo L1 ≤ D.τ L1 (j + 0)
    rw [K.H_T1]; unfold τs
    have := nt_lo (D.O L1) (cph (D.pe req1) (ash D.R (D.pe ack1)) (j + 0)) (Vph (j + 0)) l1
      (hi := D.hi L1)
    have : D.pe req1 j ≤ cph (D.pe req1) (ash D.R (D.pe ack1)) (j + 0) := Nat.le_max_left _ _
    omega
  · show D.pe aF j + D.lo F ≤ D.τ F (j + 0)
    rw [K.H_TF]
    have := nt_lo (D.O F) (cph (D.pe aF) (D.pe bF) (j + 0)) (Vph (j + 0)) lF (hi := D.hi F)
    have : D.pe aF j ≤ cph (D.pe aF) (D.pe bF) (j + 0) := Nat.le_max_left _ _
    omega
  · show D.pe bF j + D.lo F ≤ D.τ F (j + 0)
    rw [K.H_TF]
    have := nt_lo (D.O F) (cph (D.pe aF) (D.pe bF) (j + 0)) (Vph (j + 0)) lF (hi := D.hi F)
    have : D.pe bF j ≤ cph (D.pe aF) (D.pe bF) (j + 0) := Nat.le_max_right _ _
    omega
  · show D.pe ackU j + D.lo U ≤ D.τ U (j + 1)
    rw [K.H_TU]; unfold τs
    have := nt_lo (D.O U) (cph (D.pe reqU) (ash D.R (D.pe ackU)) (j + 1)) (Vph (j + 1)) lU
      (hi := D.hi U)
    have : ash D.R (D.pe ackU) (j + 1) ≤ cph (D.pe reqU) (ash D.R (D.pe ackU)) (j + 1) :=
      Nat.le_max_right _ _
    have e : ash D.R (D.pe ackU) (j + 1) = D.pe ackU j := rfl
    omega
  · exact K.K0_WAIT j
  · show D.pe ack0 j + D.lo L0 ≤ D.τ L0 (j + 1)
    rw [K.H_T0]; unfold τs
    have := nt_lo (D.O L0) (cph (D.pe req0) (ash D.R (D.pe ack0)) (j + 1)) (Vph (j + 1)) l0
      (hi := D.hi L0)
    have : ash D.R (D.pe ack0) (j + 1) ≤ cph (D.pe req0) (ash D.R (D.pe ack0)) (j + 1) :=
      Nat.le_max_right _ _
    have e : ash D.R (D.pe ack0) (j + 1) = D.pe ack0 j := rfl
    omega
  · exact K.K1_WAIT j
  · show D.pe ack1 j + D.lo L1 ≤ D.τ L1 (j + 1)
    rw [K.H_T1]; unfold τs
    have := nt_lo (D.O L1) (cph (D.pe req1) (ash D.R (D.pe ack1)) (j + 1)) (Vph (j + 1)) l1
      (hi := D.hi L1)
    have : ash D.R (D.pe ack1) (j + 1) ≤ cph (D.pe req1) (ash D.R (D.pe ack1)) (j + 1) :=
      Nat.le_max_right _ _
    have e : ash D.R (D.pe ack1) (j + 1) = D.pe ack1 j := rfl
    omega

/-- The eleven `eps`/`wait` facts at phase `j`, with the cell names reduced (for `omega`). -/
theorem f_facts (j : Nat) :
    (D.τ S j + D.wl reqU ≤ D.pe reqU j ∧ D.pe reqU j + D.lo U ≤ D.τ U j) ∧
    (D.τ U j + D.wl ackS ≤ D.pe ackS j ∧ D.pe ackS j + D.lo S ≤ D.τ S (j + 1)) ∧
    (D.τ U j + D.wl req0 ≤ D.pe req0 j ∧ D.pe req0 j + D.lo L0 ≤ D.τ L0 j) ∧
    (D.τ U j + D.wl req1 ≤ D.pe req1 j ∧ D.pe req1 j + D.lo L1 ≤ D.τ L1 j) ∧
    (D.τ L0 j + D.wl aF ≤ D.pe aF j ∧ D.pe aF j + D.lo F ≤ D.τ F j) ∧
    (D.τ L1 j + D.wl bF ≤ D.pe bF j ∧ D.pe bF j + D.lo F ≤ D.τ F j) ∧
    (D.τ F j + D.wl ackU ≤ D.pe ackU j ∧ D.pe ackU j + D.lo U ≤ D.τ U (j + 1)) ∧
    (D.τ L0 j + D.wl reqK0 ≤ D.pe reqK0 j ∧ D.pe reqK0 j + D.lo K0 ≤ D.τ K0 j) ∧
    (D.τ K0 j + D.wl ack0 ≤ D.pe ack0 j ∧ D.pe ack0 j + D.lo L0 ≤ D.τ L0 (j + 1)) ∧
    (D.τ L1 j + D.wl reqK1 ≤ D.pe reqK1 j ∧ D.pe reqK1 j + D.lo K1 ≤ D.τ K1 j) ∧
    (D.τ K1 j + D.wl ack1 ≤ D.pe ack1 j ∧ D.pe ack1 j + D.lo L1 ≤ D.τ L1 (j + 1)) :=
  ⟨⟨f_eps K reqU j, f_wait K reqU j⟩, ⟨f_eps K ackS j, f_wait K ackS j⟩,
   ⟨f_eps K req0 j, f_wait K req0 j⟩, ⟨f_eps K req1 j, f_wait K req1 j⟩,
   ⟨f_eps K aF j, f_wait K aF j⟩, ⟨f_eps K bF j, f_wait K bF j⟩,
   ⟨f_eps K ackU j, f_wait K ackU j⟩, ⟨f_eps K reqK0 j, f_wait K reqK0 j⟩,
   ⟨f_eps K ack0 j, f_wait K ack0 j⟩, ⟨f_eps K reqK1 j, f_wait K reqK1 j⟩,
   ⟨f_eps K ack1 j, f_wait K ack1 j⟩⟩

/-! Departure bounds (unconditional). -/

theorem f_sndU (j : Nat) : D.τ U j + D.EsU ≤ D.pe reqU (j + 1) := by
  have a := f_facts K j; have b := f_facts K (j + 1); unfold ForkData.EsU; omega
theorem f_rcvU (j : Nat) : D.τ U j + D.EaU ≤ D.pe ackU j := by
  have a := f_facts K j; unfold ForkData.EaU; omega
theorem f_sndF (j : Nat) : D.τ F j + D.EsF ≤ D.pe aF (j + 1) := by
  have a := f_facts K j; have b := f_facts K (j + 1); unfold ForkData.EsF; omega
theorem f_rcvF (j : Nat) : D.τ F j + D.EbF ≤ D.pe bF (j + 1) := by
  have a := f_facts K j; have b := f_facts K (j + 1); unfold ForkData.EbF; omega
theorem f_snd0 (j : Nat) : D.τ L0 j + D.Es0 ≤ D.pe req0 (j + 1) := by
  have a := f_facts K j; have b := f_facts K (j + 1); unfold ForkData.Es0; omega
theorem f_rcv0 (j : Nat) : D.τ L0 j + D.Ea0 ≤ D.pe ack0 j := by
  have a := f_facts K j; unfold ForkData.Ea0; omega
theorem f_snd1 (j : Nat) : D.τ L1 j + D.Es1 ≤ D.pe req1 (j + 1) := by
  have a := f_facts K j; have b := f_facts K (j + 1); unfold ForkData.Es1; omega
theorem f_rcv1 (j : Nat) : D.τ L1 j + D.Ea1 ≤ D.pe ack1 j := by
  have a := f_facts K j; unfold ForkData.Ea1; omega

/-- **Unconditional spacing** of every cell's edges. -/
theorem f_sp (c : FC) (j : Nat) : D.τ c j + D.cyc c ≤ D.τ c (j + 1) := by
  have a := f_facts K j; have b := f_facts K (j + 1)
  have lU := f_lhU K; have l0 := f_lh0 K; have l1 := f_lh1 K; have lF := f_lhF K
  cases c
  · show D.τ S j + (D.wl reqU + D.lo U + D.wl ackS + D.lo S) ≤ _; omega
  · show _ + (D.lo U + max D.EsU D.EaU) ≤ _
    have := f_sndU K j; have := f_rcvU K j
    rw [K.H_TU (j + 1)]; unfold τs
    have := nt_lo (D.O U) (cph (D.pe reqU) (ash D.R (D.pe ackU)) (j + 1)) (Vph (j + 1)) lU
      (hi := D.hi U)
    have : D.pe reqU (j + 1) ≤ cph (D.pe reqU) (ash D.R (D.pe ackU)) (j + 1) :=
      Nat.le_max_left _ _
    have : D.pe ackU j ≤ cph (D.pe reqU) (ash D.R (D.pe ackU)) (j + 1) := Nat.le_max_right _ _
    omega
  · show _ + (D.lo F + max D.EsF D.EbF) ≤ _
    have := f_sndF K j; have := f_rcvF K j
    rw [K.H_TF (j + 1)]
    have := nt_lo (D.O F) (cph (D.pe aF) (D.pe bF) (j + 1)) (Vph (j + 1)) lF (hi := D.hi F)
    have : D.pe aF (j + 1) ≤ cph (D.pe aF) (D.pe bF) (j + 1) := Nat.le_max_left _ _
    have : D.pe bF (j + 1) ≤ cph (D.pe aF) (D.pe bF) (j + 1) := Nat.le_max_right _ _
    omega
  · show _ + (D.lo L0 + max D.Es0 D.Ea0) ≤ _
    have := f_snd0 K j; have := f_rcv0 K j
    rw [K.H_T0 (j + 1)]; unfold τs
    have := nt_lo (D.O L0) (cph (D.pe req0) (ash D.R (D.pe ack0)) (j + 1)) (Vph (j + 1)) l0
      (hi := D.hi L0)
    have : D.pe req0 (j + 1) ≤ cph (D.pe req0) (ash D.R (D.pe ack0)) (j + 1) :=
      Nat.le_max_left _ _
    have : D.pe ack0 j ≤ cph (D.pe req0) (ash D.R (D.pe ack0)) (j + 1) := Nat.le_max_right _ _
    omega
  · show _ + (D.lo L1 + max D.Es1 D.Ea1) ≤ _
    have := f_snd1 K j; have := f_rcv1 K j
    rw [K.H_T1 (j + 1)]; unfold τs
    have := nt_lo (D.O L1) (cph (D.pe req1) (ash D.R (D.pe ack1)) (j + 1)) (Vph (j + 1)) l1
      (hi := D.hi L1)
    have : D.pe req1 (j + 1) ≤ cph (D.pe req1) (ash D.R (D.pe ack1)) (j + 1) :=
      Nat.le_max_left _ _
    have : D.pe ack1 j ≤ cph (D.pe req1) (ash D.R (D.pe ack1)) (j + 1) := Nat.le_max_right _ _
    omega
  · show D.τ K0 j + (D.wl ack0 + D.lo L0 + D.wl reqK0 + D.lo K0) ≤ _; omega
  · show D.τ K1 j + (D.wl ack1 + D.lo L1 + D.wl reqK1 + D.lo K1) ≤ _; omega

theorem f_mono (c : FC) (j : Nat) : D.τ c j ≤ D.τ c (j + 1) := by
  have := f_sp K c j; omega

theorem f_monoN (c : FC) {j j' : Nat} (h : j ≤ j') : D.τ c j ≤ D.τ c j' := by
  induction j' with
  | zero => have : j = 0 := by omega
            subst this; exact Nat.le_refl _
  | succ j' ih =>
    rcases Nat.lt_or_ge j (j' + 1) with h' | h'
    · have := ih (by omega); have := f_mono K c j'; omega
    · have : j = j' + 1 := by omega
      subst this; exact Nat.le_refl _

theorem f_geR (c : FC) (hc : c ≠ S) (j : Nat) : D.R < D.τ c j := by
  have a := f_facts K 0; have := K.SRC_T0
  have := K.H_LUT_POS U; have := K.H_LUT_POS L0; have := K.H_LUT_POS L1
  have := K.H_LUT_POS F; have := K.H_LUT_POS K0; have := K.H_LUT_POS K1
  have := f_monoN K c (Nat.zero_le j)
  cases c
  · exact absurd rfl hc
  all_goals omega

/-- The wire hypotheses of `wire_segK` for every wire. -/
theorem f_spw (T : ForkT D) (w : WI) (j : Nat) :
    D.wh w ≤ D.τ w.drv j ∧ D.τ w.drv j + D.wh w < D.τ w.drv (j + 1) + D.wl w := by
  have := f_sp K w.drv j; have := T.H_CYC w; have := (K.H_WIRE w).H_POS
  refine ⟨?_, by omega⟩
  have := T.H_WIRE_R w
  by_cases hw : w = reqU
  · subst hw; have := K.SRC_T0; have := f_monoN K S (Nat.zero_le j)
    show D.wh reqU ≤ D.τ S j; omega
  · have hne : w.drv ≠ S := by cases w <;> simp_all [WI.drv]
    have := f_geR K w.drv hne j; omega

end fork

theorem f_mem {D : ForkData} {c : FC} {w : WI} (h : w ∈ pinsW c) : D.npin w ∈ D.pins c :=
  List.mem_map.2 ⟨w, h, rfl⟩

theorem ack_shape {P : Nat → Bool} {e : Nat → Nat} {R : Nat} (h : Phases P e) :
    ∀ j t, ash R e j ≤ t → t < ash R e (j + 1) → P t = !Vph j := by
  intro j t h1 h2
  cases j with
  | zero => rw [h.pre t h2]; rfl
  | succ j' => rw [h.ph j' t h1 h2, PipeTimed.Vph_succ, Bool.not_not]

section forkclosed
variable {D : ForkData} (K : Fork D) (T : ForkT D)
include K T

/-- **H_CELL for the fork network**: links `U`, `L0`, `L1` by `link_segK`, the fork's
C-element by `celc_segK` (both PROVED from B's cell models), the ends by their contracts. -/
theorem fork_cell (c : FC) (k : Nat) (hA : NetA D.τ D.pins c k) : SegK (D.O c) (D.τ c) k := by
  have pin : ∀ w, w ∈ pinsW c → ∀ k', k' + w.off ≤ k → SegK (D.P w) (D.pe w) k' :=
    fun w hw k' hk => hA (D.npin w) (f_mem hw) k' hk
  cases c
  · exact K.END_SEG S (by simp) k hA
  · rw [show D.τ U = _ from funext K.H_TU]
    exact link_cell (E := min D.EsU D.EaU) K.H_STU K.H_RST (T.H_RST_LONG U (by simp))
      T.H_LAT_U (K.H_LUT_POS U) (K.H_PWR U (by simp))
      (by have := (f_facts K 0).1.1; have := K.SRC_T0; omega)
      (fun j => by rw [← K.H_TU j]; have := f_sndU K j; omega)
      (fun j => by rw [← K.H_TU j]; have := f_rcvU K j; omega) k
      (fun k' h => pin reqU (by simp [pinsW]) k' (by show k' + 0 ≤ k; omega))
      (fun k' h => pin ackU (by simp [pinsW]) k' h)
  · rw [show D.τ F = _ from funext K.H_TF]
    have hF := f_facts K 0
    have := f_geR K L0 (by decide) 0; have := f_geR K L1 (by decide) 0
    exact celc_segK (E := min D.EsF D.EbF) K.H_CELF K.H_RST (T.H_RST_LONG F (by simp))
      T.H_LAT_F (K.H_PWR F (by simp)) ⟨by omega, by omega⟩
      (fun j => by rw [← K.H_TF j]; have := f_sndF K j; omega)
      (fun j => by rw [← K.H_TF j]; have := f_rcvF K j; omega) k
      (fun hk => by
        subst hk
        exact ⟨fun t _ ht => pin aF (by simp [pinsW]) 0 (by decide) t (Nat.zero_le _) ht,
          fun t _ ht => pin bF (by simp [pinsW]) 0 (by decide) t (Nat.zero_le _) ht⟩)
      (fun j hk => by
        subst hk
        exact ⟨fun t h1 h2 => pin aF (by simp [pinsW]) (j + 1) (by show j + 1 + 0 ≤ j + 1; omega)
            t h1 h2,
          fun t h1 h2 => pin bF (by simp [pinsW]) (j + 1) (by show j + 1 + 0 ≤ j + 1; omega)
            t h1 h2⟩)
  · rw [show D.τ L0 = _ from funext K.H_T0]
    have := f_geR K U (by decide) 0
    exact link_cell (E := min D.Es0 D.Ea0) K.H_ST0 K.H_RST (T.H_RST_LONG L0 (by simp))
      T.H_LAT_0 (K.H_LUT_POS L0) (K.H_PWR L0 (by simp))
      (by have := (f_facts K 0).2.2.1.1; omega)
      (fun j => by rw [← K.H_T0 j]; have := f_snd0 K j; omega)
      (fun j => by rw [← K.H_T0 j]; have := f_rcv0 K j; omega) k
      (fun k' h => pin req0 (by simp [pinsW]) k' (by show k' + 0 ≤ k; omega))
      (fun k' h => pin ack0 (by simp [pinsW]) k' h)
  · rw [show D.τ L1 = _ from funext K.H_T1]
    have := f_geR K U (by decide) 0
    exact link_cell (E := min D.Es1 D.Ea1) K.H_ST1 K.H_RST (T.H_RST_LONG L1 (by simp))
      T.H_LAT_1 (K.H_LUT_POS L1) (K.H_PWR L1 (by simp))
      (by have := (f_facts K 0).2.2.2.1.1; omega)
      (fun j => by rw [← K.H_T1 j]; have := f_snd1 K j; omega)
      (fun j => by rw [← K.H_T1 j]; have := f_rcv1 K j; omega) k
      (fun k' h => pin req1 (by simp [pinsW]) k' (by show k' + 0 ≤ k; omega))
      (fun k' h => pin ack1 (by simp [pinsW]) k' h)
  · exact K.END_SEG K0 (by simp) k hA
  · exact K.END_SEG K1 (by simp) k hA

/-- **The circle closed on the fork network**: every node is a clean step signal. -/
theorem fork_nodes : ∀ c, Phases (D.O c) (D.τ c) :=
  net_closed D.O D.τ D.lo D.pins (fork_cell K T)
    (fun c p hp => by obtain ⟨w, _, rfl⟩ := List.mem_map.1 hp; exact K.H_WIRE w)
    (fun c p hp j => by
      obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hp
      have := f_wait K w j; rw [cons_of_mem hw] at this; exact this)
    K.H_LUT_POS
    (fun c p hp j => by obtain ⟨w, _, rfl⟩ := List.mem_map.1 hp; exact f_spw K T w j)
    (f_mono K)

theorem fork_pins (w : WI) : Phases (D.P w) (D.pe w) :=
  phases_of_segK fun k => wire_segK (K.H_WIRE w) k
    (segK_of_phases (fork_nodes K T w.drv) k) (fun j _ => f_spw K T w j)

/-- **`Env1` of the fork's upstream link `U`, derived** (`Es = EsU`, `Ea = EaU`, the
slower branch cycle). -/
theorem fork_env1U :
    Env1 (D.P reqU) (D.P ackU) D.rst (D.O U) (D.lo U) (D.hi U) D.R (D.pe reqU)
      (ash D.R (D.pe ackU)) D.EsU D.EaU := by
  have pr := fork_pins K T reqU; have pa := fork_pins K T ackU
  exact { H_RST := K.H_RST, H_REQ_LOW0 := fun t _ h => pr.pre t h, H_REQ := pr.ph,
          H_ACK0 := rfl, H_ACK := ack_shape pa
          H_RST_EARLY := by have := (f_facts K 0).1.1; have := K.SRC_T0; omega
          H_SND := fun j => by rw [← K.H_TU j]; exact f_sndU K j
          H_RCV := fun j => by rw [← K.H_TU j]; exact f_rcvU K j }

/-- **`Env1` of the consumer links, derived** (`Es` = the branch cycle through the fork,
`fork_env`'s formula; `Ea` from the sink). -/
theorem fork_env1L0 :
    Env1 (D.P req0) (D.P ack0) D.rst (D.O L0) (D.lo L0) (D.hi L0) D.R (D.pe req0)
      (ash D.R (D.pe ack0)) D.Es0 D.Ea0 := by
  have pr := fork_pins K T req0; have pa := fork_pins K T ack0
  exact { H_RST := K.H_RST, H_REQ_LOW0 := fun t _ h => pr.pre t h, H_REQ := pr.ph,
          H_ACK0 := rfl, H_ACK := ack_shape pa
          H_RST_EARLY := by have := (f_facts K 0).2.2.1.1; have := f_geR K U (by decide) 0; omega
          H_SND := fun j => by rw [← K.H_T0 j]; exact f_snd0 K j
          H_RCV := fun j => by rw [← K.H_T0 j]; exact f_rcv0 K j }

theorem fork_env1L1 :
    Env1 (D.P req1) (D.P ack1) D.rst (D.O L1) (D.lo L1) (D.hi L1) D.R (D.pe req1)
      (ash D.R (D.pe ack1)) D.Es1 D.Ea1 := by
  have pr := fork_pins K T req1; have pa := fork_pins K T ack1
  exact { H_RST := K.H_RST, H_REQ_LOW0 := fun t _ h => pr.pre t h, H_REQ := pr.ph,
          H_ACK0 := rfl, H_ACK := ack_shape pa
          H_RST_EARLY := by
            have := (f_facts K 0).2.2.2.1.1; have := f_geR K U (by decide) 0; omega
          H_SND := fun j => by rw [← K.H_T1 j]; exact f_snd1 K j
          H_RCV := fun j => by rw [← K.H_T1 j]; exact f_rcv1 K j }

/-- **Bfb's `EnvC` of the fork's C-element, derived** (`Es`, `Ea` the two branch cycles). -/
theorem fork_envCF :
    EnvC (D.P aF) (D.P bF) D.rst (D.O F) (D.lo F) (D.hi F) D.R (D.pe aF) (D.pe bF)
      D.EsF D.EbF := by
  have pa := fork_pins K T aF; have pb := fork_pins K T bF
  have hF := f_facts K 0
  have := f_geR K L0 (by decide) 0; have := f_geR K L1 (by decide) 0
  exact { H_RST := K.H_RST, H_A0 := fun t _ h => pa.pre t h, H_B0 := fun t _ h => pb.pre t h,
          H_A := pa.ph, H_B := pb.ph
          H_RST_EARLY := ⟨by omega, by omega⟩
          H_SND := fun j => by rw [← K.H_TF j]; exact f_sndF K j
          H_RCV := fun j => by rw [← K.H_TF j]; exact f_rcvF K j }

/-- **C's `LutFb`/`FbFirst` premises for `U`, `L0`, `L1` (`link_bound`) and for the fork's
C-element (`fork2_cel`), with no environment hypothesis on any of the four gates.** -/
theorem fork_lutFb :
    (Formal.Net.Ops.Gen.LutFb Formal.Net.Ops.Gen.linkF (fun t => (D.P reqU t, D.P ackU t))
      (D.qp U) (D.O U) ∧ Formal.Net.Ops.Gen.FbFirst (D.qp U) (D.O U)) ∧
    (Formal.Net.Ops.Gen.LutFb Formal.Net.Ops.Gen.linkF (fun t => (D.P req0 t, D.P ack0 t))
      (D.qp L0) (D.O L0) ∧ Formal.Net.Ops.Gen.FbFirst (D.qp L0) (D.O L0)) ∧
    (Formal.Net.Ops.Gen.LutFb Formal.Net.Ops.Gen.linkF (fun t => (D.P req1 t, D.P ack1 t))
      (D.qp L1) (D.O L1) ∧ Formal.Net.Ops.Gen.FbFirst (D.qp L1) (D.O L1)) ∧
    (Formal.Net.Ops.Gen.LutFb (fun p q => Formal.Net.Ops.Gen.genF Formal.Gen.Cells.bd_fork_N2
        Formal.Net.Ops.Gen.forkCell .O ["ack_in[0]", "ack_in[1]", "ack", "rst"]
        [p.1, p.2, q, false]) (fun t => (D.P aF t, D.P bF t)) (D.qp F) (D.O F) ∧
      Formal.Net.Ops.Gen.FbFirst (D.qp F) (D.O F)) := by
  have lU := f_lhU K; have l0 := f_lh0 K; have l1 := f_lh1 K
  refine ⟨LutFbBridge.link_lutFb K.H_STU (fork_env1U K T) ⟨?_, T.H_RST_LONG U (by simp), ?_⟩
      (K.H_LUT_POS U) (K.H_PWR U (by simp)),
    LutFbBridge.link_lutFb K.H_ST0 (fork_env1L0 K T) ⟨?_, T.H_RST_LONG L0 (by simp), T.H_LAT_0⟩
      (K.H_LUT_POS L0) (K.H_PWR L0 (by simp)),
    LutFbBridge.link_lutFb K.H_ST1 (fork_env1L1 K T) ⟨?_, T.H_RST_LONG L1 (by simp), T.H_LAT_1⟩
      (K.H_LUT_POS L1) (K.H_PWR L1 (by simp)),
    LutFbBridge.fork2_lutFb K.H_CELF (fork_envCF K T)
      ⟨?_, T.H_RST_LONG F (by simp), T.H_LAT_F⟩ (K.H_PWR F (by simp))⟩
  all_goals first
    | exact T.H_LAT_U
    | (have := T.H_RST_LONG U (by simp); have := T.H_RST_LONG F (by simp)
       have := K.H_LUT_POS U; have := K.H_LUT_POS F; have := f_lhF K; omega)
    | (have := T.H_RST_LONG L0 (by simp); have := K.H_LUT_POS L0; omega)
    | (have := T.H_RST_LONG L1 (by simp); have := K.H_LUT_POS L1; omega)

end forkclosed

/-! ## 3. Non-vacuity: a live fork network of REAL cells, nonzero delays

Phases of 7 ticks (`sq7`). Every gate is a 1-tick transport copy of its real excitation
(`bd_c2n` for `U`, `L0`, `L1`; `bd_c2` for `F`); every wire is a transport delay of 1 tick,
except `U → L1.req` (2 ticks), so `F`'s pins DISAGREE on `[8, 9)` each period and `F`
holds through its feedback there; `L0`, `L1` see their acknowledge 4 ticks after their
request, so they too hold through their feedback for 3 ticks each phase. The source and
sinks are square waves. -/

open Formal.Cells.PipeTimed.Wit (rstW)
open Formal.Cells.LutFbBridge2Env (sq7 τ7 sq7_shift phases_sq7 wire_sq7 eps7)

theorem sq7_t {o s : Nat} (h1 : o ≤ s) (h2 : (s - o) % 14 < 7) : sq7 o s = true := by
  unfold sq7; simp [h1, h2]

theorem sq7_f {o s : Nat} (h : s < o ∨ 7 ≤ (s - o) % 14) : sq7 o s = false := by
  unfold sq7; simp; omega

/-- The real `bd_c2n` excitation, acknowledge one phase (7) after the request. -/
theorem keyU (o s : Nat) (ho : 4 ≤ o) :
    PipeTimed.ex (sq7 o) (sq7 (o + 7)) (sq7 (o + 2)) rstW s = sq7 o s := by
  unfold PipeTimed.ex rstW; rw [CElemTiming.c2n_eq]
  by_cases hs : s < o
  · rw [sq7_f (Or.inl hs), sq7_f (o := o + 7) (Or.inl (by omega)),
      sq7_f (o := o + 2) (Or.inl (by omega))]
    cases decide (s < 4) <;> rfl
  · have hr : decide (s < 4) = false := by simp; omega
    rw [hr]
    by_cases c1 : (s - o) % 14 < 7
    · rw [sq7_t (by omega) c1, sq7_f (o := o + 7) (by omega)]; rfl
    · rw [sq7_f (o := o) (Or.inr (by omega)), sq7_t (o := o + 7) (by omega) (by omega)]
      cases sq7 (o + 2) s <;> rfl

/-- The real `bd_c2n` excitation, acknowledge 4 ticks after the request, feedback 2: the
cell holds through its feedback on `[o+4, o+7)` and `[o+11, o+14)` of each period. -/
theorem keyL (o s : Nat) (ho : 4 ≤ o) :
    PipeTimed.ex (sq7 o) (sq7 (o + 4)) (sq7 (o + 2)) rstW s = sq7 o s := by
  unfold PipeTimed.ex rstW; rw [CElemTiming.c2n_eq]
  by_cases hs : s < o
  · rw [sq7_f (Or.inl hs), sq7_f (o := o + 4) (Or.inl (by omega)),
      sq7_f (o := o + 2) (Or.inl (by omega))]
    cases decide (s < 4) <;> rfl
  · have hr : decide (s < 4) = false := by simp; omega
    rw [hr]
    by_cases c1 : (s - o) % 14 < 4
    · rw [sq7_t (by omega) (by omega), sq7_f (o := o + 4) (by omega)]; rfl
    · by_cases c2 : (s - o) % 14 < 7
      · rw [sq7_t (o := o) (by omega) c2, sq7_t (o := o + 4) (by omega) (by omega),
          sq7_t (o := o + 2) (by omega) (by omega)]; rfl
      · by_cases c3 : (s - o) % 14 < 11
        · rw [sq7_f (o := o) (Or.inr (by omega)), sq7_t (o := o + 4) (by omega) (by omega)]
          cases sq7 (o + 2) s <;> rfl
        · rw [sq7_f (o := o) (Or.inr (by omega)), sq7_f (o := o + 4) (Or.inr (by omega)),
            sq7_f (o := o + 2) (Or.inr (by omega))]; rfl

/-- The real `bd_c2` excitation, `b` one tick after `a`, feedback 3: equals `b` (the cell
holds through its feedback at the one tick per phase where `a ≠ b`). -/
theorem keyF (o s : Nat) (ho : 4 ≤ o) :
    LutFbBridge.exC (sq7 o) (sq7 (o + 1)) (sq7 (o + 3)) rstW s = sq7 (o + 1) s := by
  unfold LutFbBridge.exC rstW; rw [CElemTiming.c2_eq]
  by_cases hs : s < o
  · rw [sq7_f (Or.inl hs), sq7_f (o := o + 1) (Or.inl (by omega)),
      sq7_f (o := o + 3) (Or.inl (by omega))]
    cases decide (s < 4) <;> rfl
  · have hr : decide (s < 4) = false := by simp; omega
    rw [hr]
    by_cases c0 : (s - o) % 14 = 0
    · rw [sq7_t (o := o) (by omega) (by omega), sq7_f (o := o + 1) (by omega),
        sq7_f (o := o + 3) (by omega)]; rfl
    · by_cases c1 : (s - o) % 14 < 7
      · rw [sq7_t (o := o) (by omega) c1, sq7_t (o := o + 1) (by omega) (by omega)]; rfl
      · by_cases c2 : (s - o) % 14 = 7
        · rw [sq7_f (o := o) (Or.inr (by omega)), sq7_t (o := o + 1) (by omega) (by omega),
            sq7_t (o := o + 3) (by omega) (by omega)]; rfl
        · rw [sq7_f (o := o) (Or.inr (by omega)), sq7_f (o := o + 1) (Or.inr (by omega))]
          cases sq7 (o + 3) s <;> rfl

/-- Node offsets (node of cell `c` is `sq7 (nO c)`) and pin offsets. -/
def nO : FC → Nat
  | S => 3 | U => 5 | F => 10 | L0 => 7 | L1 => 8 | K0 => 9 | K1 => 10
def pO : WI → Nat
  | reqU => 4 | ackS => 6 | req0 => 6 | req1 => 7 | aF => 8 | bF => 9 | ackU => 11
  | reqK0 => 8 | ack0 => 10 | reqK1 => 9 | ack1 => 11
def dW : WI → Nat
  | req1 => 2
  | reqU => 1 | ackS => 1 | req0 => 1 | aF => 1 | bF => 1 | ackU => 1 | reqK0 => 1 | ack0 => 1
  | reqK1 => 1 | ack1 => 1
def qO : FC → Nat
  | U => 6 | L0 => 8 | L1 => 9 | F => 11 | S => 0 | K0 => 0 | K1 => 0

theorem pO_eq (w : WI) : pO w = nO w.drv + dW w := by cases w <;> rfl

def wF : ForkData where
  R := 4
  O c := sq7 (nO c)
  qp c := sq7 (qO c)
  rst := rstW
  lo _ := 1
  hi _ := 1
  fl _ := 1
  fh _ := 1
  τ c := τ7 (nO c)
  P w := sq7 (pO w)
  wl := dW
  wh := dW

theorem w_pe (w : WI) (j : Nat) : wF.pe w j = pO w + 7 * j := by
  show ε (sq7 (pO w)) (dW w) (dW w) (τ7 (nO w.drv)) j = _
  rw [eps7 (τ := τ7 (nO w.drv)) (nO w.drv) (dW w) (pO w) (pO_eq w) (fun _ => rfl), pO_eq]

/-- A 1-tick transport LUT is a `Win 1 1` channel with H_NO_REVERT. -/
theorem tr_win {x y : Nat → Bool} (h : ∀ t, 1 ≤ t → y t = x (t - 1)) :
    Win 1 1 x y ∧ NoRevertI 1 1 x y :=
  ⟨fun t ht => ⟨t - 1, by omega, by omega, h t (by omega)⟩, WinFifoCausal.noRevertI_shift h⟩

theorem sh7 (o t : Nat) (ht : 1 ≤ t) : sq7 (o + 1) t = sq7 o (t - 1) := by
  have := sq7_shift o 1 (t - 1); rw [Nat.sub_add_cancel ht] at this; exact this

theorem stageL (o : Nat) (ho : 4 ≤ o) :
    Stage (sq7 o) (sq7 (o + 4)) rstW (sq7 (o + 1)) (sq7 (o + 2)) 1 1 1 1 := by
  have hx : ∀ t, 1 ≤ t → sq7 (o + 1) t = PipeTimed.ex (sq7 o) (sq7 (o + 4)) (sq7 (o + 2)) rstW (t - 1) :=
    fun t ht => by rw [keyL o (t - 1) ho]; exact sh7 o t ht
  exact ⟨(tr_win hx).1, (tr_win hx).2,
    CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1) (fun t => sq7_shift (o + 1) 1 t),
    by decide⟩

theorem stageU (o : Nat) (ho : 4 ≤ o) :
    Stage (sq7 o) (sq7 (o + 7)) rstW (sq7 (o + 1)) (sq7 (o + 2)) 1 1 1 1 := by
  have hx : ∀ t, 1 ≤ t → sq7 (o + 1) t = PipeTimed.ex (sq7 o) (sq7 (o + 7)) (sq7 (o + 2)) rstW (t - 1) :=
    fun t ht => by rw [keyU o (t - 1) ho]; exact sh7 o t ht
  exact ⟨(tr_win hx).1, (tr_win hx).2,
    CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1) (fun t => sq7_shift (o + 1) 1 t),
    by decide⟩

theorem celF (o : Nat) (ho : 4 ≤ o) :
    CelC (sq7 o) (sq7 (o + 1)) rstW (sq7 (o + 2)) (sq7 (o + 3)) 1 1 1 1 := by
  have hx : ∀ t, 1 ≤ t → sq7 (o + 2) t = LutFbBridge.exC (sq7 o) (sq7 (o + 1)) (sq7 (o + 3)) rstW (t - 1) :=
    fun t ht => by rw [keyF o (t - 1) ho]; exact sh7 (o + 1) t ht
  exact ⟨(tr_win hx).1, (tr_win hx).2,
    CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1) (fun t => sq7_shift (o + 2) 1 t),
    by decide⟩

theorem w_nt {o c j : Nat} (h : c + 1 = o + 7 * j) : nt (sq7 o) 1 1 c (Vph j) = c + 1 :=
  WinFifoCausal.nt_eq (sq7 o) (Nat.le_refl 1) (LutFbBridge2Env.sq7_phase o j _ (by omega) (by omega))

theorem w_fork : Fork wF where
  H_RST _ := rfl
  H_STU := stageU 4 (by decide)
  H_ST0 := stageL 6 (by decide)
  H_ST1 := stageL 7 (by decide)
  H_CELF := celF 8 (by decide)
  H_PWR c hc t ht := sq7_f (Or.inl (by
    have : t < 1 := ht
    rcases hc with rfl | rfl | rfl | rfl <;> (show t < nO _; simp [nO]; omega)))
  H_LUT_POS _ := Nat.le_refl 1
  H_WIRE w := wire_sq7 (nO w.drv) (dW w) (pO w) (by cases w <;> decide) (pO_eq w)
  H_TU j := by
    show τ7 5 j = nt (sq7 5) 1 1 (cph (wF.pe reqU) (ash 4 (wF.pe ackU)) j) (Vph j)
    have : cph (wF.pe reqU) (ash 4 (wF.pe ackU)) j = 4 + 7 * j := by
      unfold cph; cases j with
      | zero => rw [w_pe]; rfl
      | succ j => rw [w_pe]; show max _ (wF.pe ackU j) = _; rw [w_pe]; simp only [pO]; omega
    rw [this, w_nt (by omega)]; unfold τ7; omega
  H_TF j := by
    show τ7 10 j = nt (sq7 10) 1 1 (cph (wF.pe aF) (wF.pe bF) j) (Vph j)
    have : cph (wF.pe aF) (wF.pe bF) j = 9 + 7 * j := by
      unfold cph; rw [w_pe, w_pe]; simp only [pO]; omega
    rw [this, w_nt (by omega)]; unfold τ7; omega
  H_T0 j := by
    show τ7 7 j = nt (sq7 7) 1 1 (cph (wF.pe req0) (ash 4 (wF.pe ack0)) j) (Vph j)
    have : cph (wF.pe req0) (ash 4 (wF.pe ack0)) j = 6 + 7 * j := by
      unfold cph; cases j with
      | zero => rw [w_pe]; rfl
      | succ j => rw [w_pe]; show max _ (wF.pe ack0 j) = _; rw [w_pe]; simp only [pO]; omega
    rw [this, w_nt (by omega)]; unfold τ7; omega
  H_T1 j := by
    show τ7 8 j = nt (sq7 8) 1 1 (cph (wF.pe req1) (ash 4 (wF.pe ack1)) j) (Vph j)
    have : cph (wF.pe req1) (ash 4 (wF.pe ack1)) j = 7 + 7 * j := by
      unfold cph; cases j with
      | zero => rw [w_pe]; rfl
      | succ j => rw [w_pe]; show max _ (wF.pe ack1 j) = _; rw [w_pe]; simp only [pO]; omega
    rw [this, w_nt (by omega)]; unfold τ7; omega
  SRC_WAIT j := by rw [w_pe]; show 6 + 7 * j + 1 ≤ τ7 3 (j + 1); unfold τ7; omega
  SRC_T0 := by decide
  K0_WAIT j := by rw [w_pe]; show 8 + 7 * j + 1 ≤ τ7 9 j; unfold τ7; omega
  K1_WAIT j := by rw [w_pe]; show 9 + 7 * j + 1 ≤ τ7 10 j; unfold τ7; omega
  END_SEG c _ k _ := segK_of_phases (phases_sq7 (nO c)) k

theorem w_forkT : ForkT wF where
  H_RST_LONG _ _ := by show 1 + 1 ≤ 4; decide
  H_LAT_U := by decide
  H_LAT_F := by decide
  H_LAT_0 := by decide
  H_LAT_1 := by decide
  H_WIRE_R w := by cases w <;> decide
  H_CYC w := by cases w <;> decide

/-- **Non-vacuity of the fork closure** (`fork_nodes`, `fork_env1*`, `fork_envCF`,
`fork_lutFb`): every hypothesis holds on this run; the fork C-element's pins disagree at
`t = 8` (so it holds through its feedback), `L0`'s request and acknowledge disagree on
`[10, 13)` (so does `L0`), and `U`'s derived acknowledge slack `EaU = 6` (the slower
branch) is met with EQUALITY. -/
theorem fork_witness :
    Fork wF ∧ ForkT wF ∧ wF.P aF 8 ≠ wF.P bF 8 ∧
    (∀ t, 10 ≤ t → t < 13 → wF.P req0 t = wF.P ack0 t) ∧
    (∀ j, wF.τ U j + wF.EaU = wF.pe ackU j) := by
  refine ⟨w_fork, w_forkT, by decide, fun t h1 h2 => ?_, fun j => ?_⟩
  · show sq7 6 t = sq7 10 t
    rw [sq7_t (by omega) (by omega), sq7_t (by omega) (by omega)]
  · rw [w_pe]; show τ7 5 j + 6 = 11 + 7 * j; unfold τ7; omega

end Formal.Cells.AssumeGuaranteeFork
