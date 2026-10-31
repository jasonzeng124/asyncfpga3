import Formal.Cells.LutFbBridge2
import Formal.Net.CapstoneSafe

/-!
# Probe Bfb2 (shard B): the environment of a cell from its neighbours, and the link class on
# C's `CapstoneNet`

Bfb (`LutFbBridge`) and `LutFbBridge2` derive C's `LutFb`/`FbFirst`/`LutSI` premises from
B's physical cell model PLUS a four-phase environment hypothesis (`Env1`, `EnvC`, `EnvG`):
each pin of the cell is a clean step signal, and each pin's next edge comes some time `E`
after the cell's own edge. This file derives those environment fields from the
NEIGHBOURING cells' behaviour (assume-guarantee, one channel at a time), and plugs the
link class into C's gcd_hw capstone.

## Assumed / proved / NOT covered

**Assumed** (named):
* H_WIRE (`Wire`): every routed wire between two cells is a `Win wl wh` channel with
  H_NO_REVERT, `1 ≤ wl`, output 0 before `wh` (power-up).
* each neighbouring node's **guarantee**, a property of its own trace: it is a clean step
  signal (`Phases O τ`), and its edge `j` comes at least its LUT's minimum delay `lo`
  after the pin carrying the edge it waits for (a link controller's next edge waits for its
  acknowledge pin; a consumer's edge waits for its request pin). `link_guar` and
  `celG_guar` PROVE these guarantees from B's cell model plus the cell's own environment.
* timing: every wire's maximum delay is at most the reset length and at most the minimum
  delay of the handshake cycle through it (H_WIRE_R, H_RT / H_CYC).

**Proved:**
* `wire_steps`, `wire_di`: through such a wire a clean step signal stays clean, with edges
  `ε` in `[τ j + wl, τ j + wh]`, and C's DI wire relation (`H_REQ_DI`/`H_ACK_DI` form:
  the pin changes only to the node's value one tick earlier) holds.
* `link_link_env` (link-to-link channel `A → B`): from the two controllers' guarantees and
  the two wires, B's request-side `Env1` fields (`H_REQ_LOW0`, `H_REQ`, `H_RST_EARLY`,
  `H_SND` with `Es = wl_ba + lo_A + wl_ab`) and A's acknowledge-side fields (`H_ACK0`,
  `H_ACK`, `H_RCV` with `Ea = wl_ab + lo_B + wl_ba`), and both DI wires.
  `env1_of_neighbours`: for a link `B` between links `A` and `C`, B's whole `Env1`.
* `fork_env` (a 2-way fork: an upstream node `U`, the fork C-element `F`, two consumer
  links `L0`, `L1`, five wires): Bfb's `EnvC` of the fork's C-element (`Es`, `Ea` the two
  branch cycles), the request-side `Env1` fields of `L0` and `L1`, U's acknowledge-side
  fields, all five DI wires.
* `link_of_phys` and the end-to-end `gcd_hw_safe_phys_links`: C's gcd_hw circuit safety
  theorem with `H_CELLS` for all 175 link operators REPLACED by B's physical model of each
  link (`PhysLink`: Win LUT + H_NO_REVERT + feedback wire + `Env1` + `Timing1` + H_LUT_POS
  + H_PWR, two `Wire`s to the neighbours, the latch data fields); C's `Link` fields
  `H_CEL_SI`, `H_ACK_DI`, `H_REQ_DI` and all three init fields are DERIVED.
* On `CapstoneNet` (kernel-checked counts): 175 link operators, 75 link-to-link channels
  (`ll_count`), 12 links whose both channels are link-to-link (`interior_count`), no 2-way
  fork whose input is a link (`fork_from_link_count`).
* Non-vacuity with nonzero delays: `link_link_witness` (B's two-stage pipe run
  `Wx.gates_w`: LUT minimum delay 1, wires 1; the derived `Es`, `Ea` are met with
  equality) and `fork_witness` (branch 1 one tick slower than branch 0, so the fork's
  C-element pins disagree for a tick each phase; the upstream guarantee met with equality).

**NOT covered:**
* The assume-guarantee loop is NOT closed: `link_guar` derives a cell's guarantee from its
  `Env1`, and `link_link_env` derives the neighbour's `Env1` fields from the guarantees.
  Closing the loop over a whole network needs the causal induction on edge index (done in
  Lean only for the two-stage pipe, `WinFifoCausal.pipe_fifo`), not done here, so neither
  `Env1` nor `PhysLink` is derived for any gcd_hw link.
* Only link-to-link channels (75 channels, 150 of the 350 link channel ends) are covered by
  `link_link_env`; the other link neighbours are forks (N=2..4), joins, steers, muxes,
  muxn and arbiters, whose guarantees are not packaged here (forks from a link: none).
* Every theorem is for an infinitely alternating run (inherited from `Env1`/`EnvC`).
* C's channel model has ONE trace per channel; the physical pin trace is identified with
  C's channel trace (`ch c`), the wire delay appearing in C's DI step.
Core Lean only.
-/

namespace Formal.Cells.LutFbBridge2Env
open Formal.Cells
open Formal.Net.Ops.Gen (LutFb FbFirst LutSI link_of_gen)
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo nt_eq Stage Env1 Timing1 cph τs)
open Formal.Cells.PipeTimed (Vph ex)
open Formal.Cells.LutFbBridge (Phases lutFb_of_phases node_steps CelC EnvC)

/-! ## 1. Wires -/

/-- **H_WIRE**: a routed wire from node `O` to pin `P`. -/
structure Wire (wl wh : Nat) (O P : Nat → Bool) : Prop where
  H_WIN : Win wl wh O P
  H_NO_REVERT : NoRevertI wl wh O P
  H_POS : 1 ≤ wl
  H_PWR : ∀ t, t < wh → P t = false

/-- The pin's edge for the node's edge `τ j`: first instant `≥ τ j + wl` showing `Vph j`. -/
def ε (P : Nat → Bool) (wl wh : Nat) (τ : Nat → Nat) (j : Nat) : Nat := nt P wl wh (τ j) (Vph j)

theorem ε_lo {P O : Nat → Bool} {wl wh : Nat} (W : Wire wl wh O P) (τ : Nat → Nat) (j : Nat) :
    τ j + wl ≤ ε P wl wh τ j := nt_lo P (τ j) (Vph j) (win_le W.H_WIN)

theorem wire_steps {wl wh : Nat} {O P : Nat → Bool} {τ : Nat → Nat} (W : Wire wl wh O P)
    (hO : Phases O τ) (h0 : wh ≤ τ 0) (hsp : ∀ j, τ j + wh ≤ τ (j + 1)) :
    Phases P (ε P wl wh τ) ∧ ∀ j, ε P wl wh τ j ≤ τ j + wh := by
  obtain ⟨hb, hpre, hseg⟩ := node_steps W.H_WIN W.H_NO_REVERT hO W.H_POS h0 hsp W.H_PWR
  exact ⟨⟨hpre, hseg⟩, fun j => (hb j).2⟩

/-- **C's DI wire relation from the physical wire.** -/
theorem wire_di {wl wh : Nat} {O P : Nat → Bool} {τ : Nat → Nat} (W : Wire wl wh O P)
    (hO : Phases O τ) (h0 : wh ≤ τ 0) (hsp : ∀ j, τ j + wh ≤ τ (j + 1)) :
    ∀ t, P (t + 1) ≠ P t → P (t + 1) = O t :=
  lutFb_of_phases (F := fun (a : Bool) (_ : Bool) => a) (p := O) (qp := fun _ => false)
    W.H_WIN W.H_NO_REVERT hO W.H_POS h0 hsp W.H_PWR (fun _ _ => rfl)

/-- The acknowledge-pin edge list of a link controller: `R`, then the pin's edges. -/
def ash (R : Nat) (e : Nat → Nat) : Nat → Nat
  | 0 => R
  | j + 1 => e j

/-! ## 2. Guarantees from B's cell models -/

/-- **A link controller's guarantee** (from B's `Stage`/`Env1`/`Timing1`): its node is a
clean step signal with edges `τs`, each edge `j` at least `lo` after both pins' phase-`j`
arrivals, and the first edge at least `lo` after reset release. -/
theorem link_guar {req ack rst O qp : Nat → Bool} {lo hi wl wh R Es Ea : Nat}
    {ρ α : Nat → Nat}
    (S : Stage req ack rst O qp lo hi wl wh) (E : Env1 req ack rst O lo hi R ρ α Es Ea)
    (T : Timing1 lo hi wh R Es Ea) (H_LUT_POS : 1 ≤ lo) (H_PWR : ∀ t, t < hi → O t = false) :
    Phases O (τs O lo hi ρ α) ∧
    (∀ j, ρ j + lo ≤ τs O lo hi ρ α j ∧ α j + lo ≤ τs O lo hi ρ α j) ∧
    R + lo ≤ τs O lo hi ρ α 0 ∧ (∀ j, τs O lo hi ρ α j ≤ cph ρ α j + hi) := by
  have hx : Phases (ex req ack qp rst) (cph ρ α) :=
    ⟨WinFifoCausal.s_pre S E T, WinFifoCausal.s_phase S E T⟩
  have hR := WinFifoCausal.cph_ge S E T 0
  have hgap := WinFifoCausal.s_gap S E T
  have hlat := T.H_LAT; have hrl := T.H_RST_LONG
  have hsp : ∀ j, cph ρ α j + hi ≤ cph ρ α (j + 1) := fun j => by have := hgap j; omega
  obtain ⟨hb, hpre, hseg⟩ := node_steps S.H_LUT_WIN S.H_NO_REVERT hx H_LUT_POS (by omega) hsp H_PWR
  refine ⟨⟨hpre, hseg⟩, fun j => ?_, ?_, fun j => (hb j).2⟩
  · have : cph ρ α j + lo ≤ nt O lo hi (cph ρ α j) (Vph j) := (hb j).1
    have : ρ j ≤ cph ρ α j := Nat.le_max_left _ _
    have : α j ≤ cph ρ α j := Nat.le_max_right _ _
    show ρ j + lo ≤ nt O lo hi (cph ρ α j) (Vph j) ∧ α j + lo ≤ nt O lo hi (cph ρ α j) (Vph j)
    omega
  · have : cph ρ α 0 + lo ≤ nt O lo hi (cph ρ α 0) (Vph 0) := (hb 0).1
    show R + lo ≤ nt O lo hi (cph ρ α 0) (Vph 0); omega

/-- **A C-element's guarantee** (from `LutFbBridge2.CelG`/`EnvG`): clean step node with
edges `nt O lo hi (c j) (Vph j)`, each at least `lo` after every pin's arrival. -/
theorem celG_guar {ι : Type} {G : (ι → Bool) → Bool → Bool → Bool} {p : Nat → ι → Bool}
    {rst O qp : Nat → Bool} {lo hi wl wh R E : Nat} {ρ : ι → Nat → Nat} {c : Nat → Nat}
    (L : LutFbBridge2.CelLaw G) (C : LutFbBridge2.CelG G p rst O qp lo hi wl wh)
    (Ev : LutFbBridge2.EnvG p rst O lo hi R ρ c E) (H_RST_LONG : hi + wh ≤ R)
    (H_LAT : hi + wh ≤ lo + E) (H_PWR : ∀ t, t < hi → O t = false) :
    Phases O (fun j => nt O lo hi (c j) (Vph j)) ∧
    ∀ i j, ρ i j + lo ≤ nt O lo hi (c j) (Vph j) := by
  have hx : Phases (fun t => G (p t) (qp t) (rst t)) c :=
    ⟨LutFbBridge2.g_pre L C Ev H_RST_LONG, LutFbBridge2.g_phase L C Ev H_RST_LONG H_LAT⟩
  have hR := LutFbBridge2.g_ge C Ev 0
  have hgap := LutFbBridge2.g_gap C Ev
  have hsp : ∀ j, c j + hi ≤ c (j + 1) := fun j => by have := hgap j; omega
  obtain ⟨hb, hpre, hseg⟩ := node_steps C.H_LUT_WIN C.H_NO_REVERT hx C.H_LUT_POS (by omega) hsp H_PWR
  refine ⟨⟨hpre, hseg⟩, fun i j => ?_⟩
  have : c j + lo ≤ nt O lo hi (c j) (Vph j) := (hb j).1
  have := Ev.H_ARR i j; omega

/-! ## 3. A link-to-link channel -/

/-- **The environment across a link-to-link channel `A → B`.** `A`'s node `OA` drives B's
request pin `reqB` through wire `ab`; `B`'s node `OB` drives A's acknowledge pin `ackA`
through wire `ba`. Assumed: the two guarantees (`GA0`, `GA`: A's next edge waits for its
acknowledge pin; `GB`: B's edge waits for its request pin), the two wires, H_WIRE_R
(wires shorter than reset), H_RT (each wire's maximum below the round trip's minimum).
Proved: the `Env1` fields of B on its request side and of A on its acknowledge side, and
both DI wires. -/
theorem link_link_env {OA OB reqB ackA : Nat → Bool} {τA τB : Nat → Nat}
    {loA loB wlab whab wlba whba R : Nat}
    (hA : Phases OA τA) (hB : Phases OB τB)
    (Wab : Wire wlab whab OA reqB) (Wba : Wire wlba whba OB ackA)
    (GA0 : R + loA ≤ τA 0)
    (GA : ∀ j, ε ackA wlba whba τB j + loA ≤ τA (j + 1))
    (GB : ∀ j, ε reqB wlab whab τA j + loB ≤ τB j)
    (H_WIRE_R : whab ≤ R ∧ whba ≤ R)
    (H_RT : whab ≤ wlab + loB + wlba + loA ∧ whba ≤ wlab + loB + wlba + loA) :
    -- B, request side (`Env1` with `ρ = ε reqB …`)
    (∀ t, R ≤ t → t < ε reqB wlab whab τA 0 → reqB t = false) ∧
    (∀ j t, ε reqB wlab whab τA j ≤ t → t < ε reqB wlab whab τA (j + 1) → reqB t = Vph j) ∧
    R ≤ ε reqB wlab whab τA 0 ∧
    (∀ j, τB j + (wlba + loA + wlab) ≤ ε reqB wlab whab τA (j + 1)) ∧
    -- A, acknowledge side (`Env1` with `α = ash R (ε ackA …)`)
    (∀ j t, ash R (ε ackA wlba whba τB) j ≤ t → t < ash R (ε ackA wlba whba τB) (j + 1) →
      ackA t = !Vph j) ∧
    (∀ j, τA j + (wlab + loB + wlba) ≤ ash R (ε ackA wlba whba τB) (j + 1)) ∧
    -- C's DI wires
    (∀ t, reqB (t + 1) ≠ reqB t → reqB (t + 1) = OA t) ∧
    (∀ t, ackA (t + 1) ≠ ackA t → ackA (t + 1) = OB t) := by
  have lab := ε_lo Wab τA
  have lba := ε_lo Wba τB
  have spA : ∀ j, τA j + whab ≤ τA (j + 1) := fun j => by
    have := GA j; have := lba j; have := GB j; have := lab j; omega
  have spB : ∀ j, τB j + whba ≤ τB (j + 1) := fun j => by
    have := GB (j + 1); have := lab (j + 1); have := GA j; have := lba j; omega
  have h0A : whab ≤ τA 0 := by omega
  have h0B : whba ≤ τB 0 := by have := GB 0; have := lab 0; omega
  obtain ⟨PA, _⟩ := wire_steps Wab hA h0A spA
  obtain ⟨PB, _⟩ := wire_steps Wba hB h0B spB
  refine ⟨fun t _ h => PA.pre t h, PA.ph, by have := lab 0; omega, fun j => ?_,
    fun j t h1 h2 => ?_, fun j => ?_, wire_di Wab hA h0A spA, wire_di Wba hB h0B spB⟩
  · have := lab (j + 1); have := GA j; have := lba j; omega
  · cases j with
    | zero =>
      have : ackA t = false := PB.pre t h2
      rw [this]; rfl
    | succ k =>
      rw [PB.ph k t h1 h2, PipeTimed.Vph_succ, Bool.not_not]
  · show τA j + (wlab + loB + wlba) ≤ ε ackA wlba whba τB j
    have := lba j; have := GB j; have := lab j; omega

/-- **A link between two links: its whole `Env1` from its neighbours.** `B` (node `OB`,
request pin `reqB` wired from `A`'s node, acknowledge pin `ackB` wired from `C`'s node),
with `ρ = ε reqB …` and `α = ash R (ε ackB …)`: assumed the guarantees of `A`, `B`, `C`,
the four wires, H_WIRE_R, H_RT on both channels, and reset; proved `Env1` for `B` with
`Es = wl_BA + lo_A + wl_AB` and `Ea = wl_BC + lo_C + wl_CB`. -/
theorem env1_of_neighbours {OA OB OC reqB ackA ackB reqC rst : Nat → Bool} {τA τC : Nat → Nat}
    {loA loB hiB loC wlab whab wlba whba wlbc whbc wlcb whcb R : Nat}
    (hA : Phases OA τA) (hC : Phases OC τC)
    (Wab : Wire wlab whab OA reqB) (Wba : Wire wlba whba OB ackA)
    (Wbc : Wire wlbc whbc OB reqC) (Wcb : Wire wlcb whcb OC ackB)
    (H_RST : ∀ t, rst t = decide (t < R))
    -- the guarantees: τB is B's own edge sequence on these pins
    (hB : Phases OB (τs OB loB hiB (ε reqB wlab whab τA) (ash R (ε ackB wlcb whcb τC))))
    (GA0 : R + loA ≤ τA 0)
    (GA : ∀ j, ε ackA wlba whba (τs OB loB hiB (ε reqB wlab whab τA) (ash R (ε ackB wlcb whcb τC))) j
      + loA ≤ τA (j + 1))
    (GB0 : R + loB ≤ τs OB loB hiB (ε reqB wlab whab τA) (ash R (ε ackB wlcb whcb τC)) 0)
    (GB : ∀ j, ε reqB wlab whab τA j + loB ≤
      τs OB loB hiB (ε reqB wlab whab τA) (ash R (ε ackB wlcb whcb τC)) j ∧
      ε ackB wlcb whcb τC j + loB ≤
      τs OB loB hiB (ε reqB wlab whab τA) (ash R (ε ackB wlcb whcb τC)) (j + 1))
    (GC : ∀ j, ε reqC wlbc whbc
      (τs OB loB hiB (ε reqB wlab whab τA) (ash R (ε ackB wlcb whcb τC))) j + loC ≤ τC j)
    (H_WIRE_R : whab ≤ R ∧ whba ≤ R ∧ whbc ≤ R ∧ whcb ≤ R)
    (H_RT1 : whab ≤ wlab + loB + wlba + loA ∧ whba ≤ wlab + loB + wlba + loA)
    (H_RT2 : whbc ≤ wlbc + loC + wlcb + loB ∧ whcb ≤ wlbc + loC + wlcb + loB) :
    Env1 reqB ackB rst OB loB hiB R (ε reqB wlab whab τA) (ash R (ε ackB wlcb whcb τC))
      (wlba + loA + wlab) (wlbc + loC + wlcb) := by
  have up := link_link_env hA hB Wab Wba GA0 GA (fun j => (GB j).1) ⟨H_WIRE_R.1, H_WIRE_R.2.1⟩
    H_RT1
  have dn := link_link_env hB hC Wbc Wcb GB0 (fun j => (GB j).2) GC
    ⟨H_WIRE_R.2.2.1, H_WIRE_R.2.2.2⟩ H_RT2
  exact { H_RST := H_RST
          H_REQ_LOW0 := up.1
          H_REQ := up.2.1
          H_ACK0 := rfl
          H_ACK := dn.2.2.2.2.1
          H_RST_EARLY := up.2.2.1
          H_SND := up.2.2.2.1
          H_RCV := dn.2.2.2.2.2.1 }

/-! ## 4. A 2-way fork -/

/-- The fork C-element's edge `j`: its node's first edge after the last pin arrival. -/
def tF (OF : Nat → Bool) (loF hiF : Nat) (ρ β : Nat → Nat) (j : Nat) : Nat :=
  nt OF loF hiF (cph ρ β j) (Vph j)

/-- **The environment of a 2-way fork from its neighbours.** Upstream node `U` (its node
`OU` fans out to the consumers' request pins `req0`, `req1`; its acknowledge pin `ackU` is
wired from the fork C-element's node `OF`); consumer links `L0`, `L1` (nodes `O0`, `O1`,
wired to the C-element's pins `a`, `b`). The C-element's edges are DEFINED from its node
(`nt` at the last pin arrival, as in Bfb's `EnvC`). Assumed: the guarantees of `U`, `L0`,
`L1`, the five wires, H_WIRE_R, H_CYC (each wire's maximum below the minimum delay of the
shorter branch cycle). Proved: Bfb's `EnvC` of the fork C-element, the request-side
`Env1` fields of `L0` and `L1`, U's acknowledge-side bounds, all five DI wires. -/
theorem fork_env {OU OF O0 O1 req0 req1 a b ackU rst : Nat → Bool} {τU τ0 τ1 : Nat → Nat}
    {loU lo0 lo1 loF hiF wlU0 whU0 wlU1 whU1 wl0F wh0F wl1F wh1F wlFU whFU R : Nat}
    (hU : Phases OU τU) (h0 : Phases O0 τ0) (h1 : Phases O1 τ1)
    (hF : Phases OF (tF OF loF hiF (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1)))
    (hFlh : loF ≤ hiF)
    (WU0 : Wire wlU0 whU0 OU req0) (WU1 : Wire wlU1 whU1 OU req1)
    (W0F : Wire wl0F wh0F O0 a) (W1F : Wire wl1F wh1F O1 b) (WFU : Wire wlFU whFU OF ackU)
    (H_RST : ∀ t, rst t = decide (t < R))
    (GU0 : R + loU ≤ τU 0)
    (GU : ∀ j, ε ackU wlFU whFU (tF OF loF hiF (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1)) j + loU ≤ τU (j + 1))
    (G0 : ∀ j, ε req0 wlU0 whU0 τU j + lo0 ≤ τ0 j)
    (G1 : ∀ j, ε req1 wlU1 whU1 τU j + lo1 ≤ τ1 j)
    (H_WIRE_R : whU0 ≤ R ∧ whU1 ≤ R ∧ wh0F ≤ R ∧ wh1F ≤ R ∧ whFU ≤ R)
    (H_CYC : ∀ w ∈ [whU0, whU1, wh0F, wh1F, whFU],
      w ≤ wlFU + loU + wlU0 + lo0 + wl0F + loF ∧ w ≤ wlFU + loU + wlU1 + lo1 + wl1F + loF) :
    EnvC a b rst OF loF hiF R (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1)
      (wlFU + loU + wlU0 + lo0 + wl0F) (wlFU + loU + wlU1 + lo1 + wl1F) ∧
    -- L0, L1: request side
    (∀ t, t < ε req0 wlU0 whU0 τU 0 → req0 t = false) ∧
    (∀ j t, ε req0 wlU0 whU0 τU j ≤ t → t < ε req0 wlU0 whU0 τU (j + 1) → req0 t = Vph j) ∧
    R ≤ ε req0 wlU0 whU0 τU 0 ∧
    (∀ j, τ0 j + (wl0F + loF + wlFU + loU + wlU0) ≤ ε req0 wlU0 whU0 τU (j + 1)) ∧
    (∀ t, t < ε req1 wlU1 whU1 τU 0 → req1 t = false) ∧
    (∀ j t, ε req1 wlU1 whU1 τU j ≤ t → t < ε req1 wlU1 whU1 τU (j + 1) → req1 t = Vph j) ∧
    R ≤ ε req1 wlU1 whU1 τU 0 ∧
    (∀ j, τ1 j + (wl1F + loF + wlFU + loU + wlU1) ≤ ε req1 wlU1 whU1 τU (j + 1)) ∧
    -- U: acknowledge side
    (∀ j t, ash R (ε ackU wlFU whFU (tF OF loF hiF (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1))) j ≤ t →
      t < ash R (ε ackU wlFU whFU (tF OF loF hiF (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1))) (j + 1) → ackU t = !Vph j) ∧
    (∀ j, τU j + (wlU0 + lo0 + wl0F + loF + wlFU) ≤ ε ackU wlFU whFU (tF OF loF hiF (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1)) j ∧
      τU j + (wlU1 + lo1 + wl1F + loF + wlFU) ≤ ε ackU wlFU whFU (tF OF loF hiF (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1)) j) ∧
    -- C's DI wires
    (∀ t, req0 (t + 1) ≠ req0 t → req0 (t + 1) = OU t) ∧
    (∀ t, req1 (t + 1) ≠ req1 t → req1 (t + 1) = OU t) ∧
    (∀ t, a (t + 1) ≠ a t → a (t + 1) = O0 t) ∧
    (∀ t, b (t + 1) ≠ b t → b (t + 1) = O1 t) ∧
    (∀ t, ackU (t + 1) ≠ ackU t → ackU (t + 1) = OF t) := by
  -- names
  have eU0 := ε_lo WU0 τU
  have eU1 := ε_lo WU1 τU
  have e0F := ε_lo W0F τ0
  have e1F := ε_lo W1F τ1
  have eFU := ε_lo WFU (tF OF loF hiF (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1))
  have GF : ∀ j, ε a wl0F wh0F τ0 j + loF ≤ (tF OF loF hiF (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1)) j ∧ ε b wl1F wh1F τ1 j + loF ≤ (tF OF loF hiF (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1)) j := by
    intro j
    have : cph (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1) j + loF ≤ (tF OF loF hiF (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1)) j :=
      nt_lo OF (cph (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1) j) (Vph j) hFlh (hi := hiF)
    have : ε a wl0F wh0F τ0 j ≤ cph (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1) j := Nat.le_max_left _ _
    have : ε b wl1F wh1F τ1 j ≤ cph (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1) j := Nat.le_max_right _ _
    constructor <;> omega
  have c0 := H_CYC whU0 (by simp); have c1 := H_CYC whU1 (by simp)
  have c2 := H_CYC wh0F (by simp); have c3 := H_CYC wh1F (by simp)
  have c4 := H_CYC whFU (by simp)
  obtain ⟨r0, r1, r2, r3, r4⟩ := H_WIRE_R
  -- spacing of every node (one branch cycle per edge)
  have spU : ∀ j, τU j + wlFU + loU + wlU0 + lo0 + wl0F + loF ≤ τU (j + 1) := fun j => by
    have := GU j; have := eFU j; have := (GF j).1; have := e0F j; have := G0 j; have := eU0 j
    omega
  have sp0 : ∀ j, τ0 j + wlFU + loU + wlU0 + lo0 + wl0F + loF ≤ τ0 (j + 1) := fun j => by
    have := G0 (j + 1); have := eU0 (j + 1); have := GU j; have := eFU j; have := (GF j).1
    have := e0F j; omega
  have sp1 : ∀ j, τ1 j + wlFU + loU + wlU1 + lo1 + wl1F + loF ≤ τ1 (j + 1) := fun j => by
    have := G1 (j + 1); have := eU1 (j + 1); have := GU j; have := eFU j; have := (GF j).2
    have := e1F j; omega
  have spF : ∀ j, (tF OF loF hiF (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1)) j + wlFU + loU + wlU0 + lo0 + wl0F + loF ≤ (tF OF loF hiF (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1)) (j + 1) := fun j => by
    have := (GF (j + 1)).1; have := e0F (j + 1); have := G0 (j + 1); have := eU0 (j + 1)
    have := GU j; have := eFU j; omega
  have i0 : R ≤ τ0 0 := by have := G0 0; have := eU0 0; omega
  have i1 : R ≤ τ1 0 := by have := G1 0; have := eU1 0; omega
  have iF : R ≤ (tF OF loF hiF (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1)) 0 := by have := (GF 0).1; have := e0F 0; omega
  have sU0 : ∀ j, τU j + whU0 ≤ τU (j + 1) := fun j => by have := spU j; omega
  have sU1 : ∀ j, τU j + whU1 ≤ τU (j + 1) := fun j => by have := spU j; omega
  have s0F : ∀ j, τ0 j + wh0F ≤ τ0 (j + 1) := fun j => by have := sp0 j; omega
  have s1F : ∀ j, τ1 j + wh1F ≤ τ1 (j + 1) := fun j => by have := sp1 j; omega
  have sFU : ∀ j, (tF OF loF hiF (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1)) j + whFU ≤ (tF OF loF hiF (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1)) (j + 1) := fun j => by have := spF j; omega
  obtain ⟨PU0, _⟩ := wire_steps WU0 hU (by omega) sU0
  obtain ⟨PU1, _⟩ := wire_steps WU1 hU (by omega) sU1
  obtain ⟨P0F, _⟩ := wire_steps W0F h0 (by omega) s0F
  obtain ⟨P1F, _⟩ := wire_steps W1F h1 (by omega) s1F
  obtain ⟨PFU, _⟩ := wire_steps WFU hF (by omega) sFU
  refine ⟨{ H_RST := H_RST
            H_A0 := fun t _ h => P0F.pre t h
            H_B0 := fun t _ h => P1F.pre t h
            H_A := P0F.ph
            H_B := P1F.ph
            H_RST_EARLY := ⟨by have := e0F 0; omega, by have := e1F 0; omega⟩
            H_SND := fun j => ?_
            H_RCV := fun j => ?_ },
    PU0.pre, PU0.ph, by have := eU0 0; omega, fun j => ?_,
    PU1.pre, PU1.ph, by have := eU1 0; omega, fun j => ?_,
    fun j t h1 h2 => ?_, fun j => ⟨?_, ?_⟩,
    wire_di WU0 hU (by omega) sU0, wire_di WU1 hU (by omega) sU1,
    wire_di W0F h0 (by omega) s0F, wire_di W1F h1 (by omega) s1F,
    wire_di WFU hF (by omega) sFU⟩
  · show (tF OF loF hiF (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1)) j + _ ≤ _
    have := e0F (j + 1); have := G0 (j + 1); have := eU0 (j + 1); have := GU j; have := eFU j
    omega
  · show (tF OF loF hiF (ε a wl0F wh0F τ0) (ε b wl1F wh1F τ1)) j + _ ≤ _
    have := e1F (j + 1); have := G1 (j + 1); have := eU1 (j + 1); have := GU j; have := eFU j
    omega
  · have := eU0 (j + 1); have := GU j; have := eFU j; have := (GF j).1; have := e0F j; omega
  · have := eU1 (j + 1); have := GU j; have := eFU j; have := (GF j).2; have := e1F j; omega
  · cases j with
    | zero =>
      have : ackU t = false := PFU.pre t h2
      rw [this]; rfl
    | succ k => rw [PFU.ph k t h1 h2, PipeTimed.Vph_succ, Bool.not_not]
  · have := eFU j; have := (GF j).1; have := e0F j; have := G0 j; have := eU0 j; omega
  · have := eFU j; have := (GF j).2; have := e1F j; have := G1 j; have := eU1 j; omega

/-! ## 5. The link class on C's gcd_hw network -/

open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe

/-- **B's physical model of one `bd_link` operator** between channels `i` and `o`: the
controller node `c` (Win LUT + H_NO_REVERT + feedback wire, `Stage` on the pins
`i.req`, `o.ack`), its four-phase environment `Env1` and `Timing1`, H_LUT_POS, H_PWR; the
two routed wires from `c` to the neighbours' pins `i.ack` and `o.req` (`Wire`, shorter
than reset and than the controller's minimum cycle, H_WIRE_SPREAD); and the latch's data
fields (bd_latch, B's `H_LATCH_*`, as C's `Link`). -/
def PhysLink (i o : Chan) : Prop :=
  ∃ (rst c qp : Nat → Bool) (lo hi wl wh R Es Ea wla wha wlr whr : Nat) (ρ α : Nat → Nat),
    Stage i.req o.ack rst c qp lo hi wl wh ∧ Env1 i.req o.ack rst c lo hi R ρ α Es Ea ∧
    Timing1 lo hi wh R Es Ea ∧ 1 ≤ lo ∧ (∀ t, t < hi → c t = false) ∧
    Wire wla wha c i.ack ∧ Wire wlr whr c o.req ∧
    wha ≤ R ∧ whr ≤ R ∧ wha + hi ≤ 2 * lo + min Es Ea ∧ whr + hi ≤ 2 * lo + min Es Ea ∧
    (∀ t, c t = true → o.dat t = i.dat t) ∧ (∀ t, c (t + 1) = false → o.dat (t + 1) = o.dat t)

/-- **C's `Link` from B's physical link model**: `H_CEL_SI` (Bfb's `link_lutFb`),
`H_ACK_DI`, `H_REQ_DI` (`wire_di`) and the three init fields (H_PWR, wire power-up) are
derived; only the latch data fields are passed through. -/
theorem link_of_phys {i o : Chan} (h : PhysLink i o) : ∃ c, Link.Link i o c := by
  obtain ⟨rst, c, qp, lo, hi, wl, wh, R, Es, Ea, wla, wha, wlr, whr, ρ, α, S, E, T, hpos, hpwr,
    Wa, Wr, ra, rr, sa, sr, lop, lho⟩ := h
  have hL := LutFbBridge.link_lutFb S E T hpos hpwr
  obtain ⟨hc, hb, hR, hup⟩ := link_guar S E T hpos hpwr
  have hgap := WinFifoCausal.s_gap S E T
  have hsp : ∀ j, τs c lo hi ρ α j + lo + min Es Ea + lo ≤ τs c lo hi ρ α (j + 1) + hi := by
    intro j
    have := (hb (j + 1)).1; have := (hb (j + 1)).2; have := hup j; have := hgap j
    have : ρ (j + 1) ≤ cph ρ α (j + 1) := Nat.le_max_left _ _
    have : α (j + 1) ≤ cph ρ α (j + 1) := Nat.le_max_right _ _
    have := (WinFifoCausal.cph_ge S E T (j + 1))
    -- τ (j+1) ≥ cph (j+1) + lo ≥ cph j + 2 lo + min, τ j ≤ cph j + hi
    have h1 : cph ρ α (j + 1) + lo ≤ τs c lo hi ρ α (j + 1) := by
      have := LutFbBridge.node_steps S.H_LUT_WIN S.H_NO_REVERT
        ⟨WinFifoCausal.s_pre S E T, WinFifoCausal.s_phase S E T⟩ hpos
        (by have := WinFifoCausal.cph_ge S E T 0; have := T.H_RST_LONG; omega)
        (fun j => by have := hgap j; have := T.H_LAT; omega) hpwr
      exact (this.1 (j + 1)).1
    omega
  have sa' : ∀ j, τs c lo hi ρ α j + wha ≤ τs c lo hi ρ α (j + 1) := fun j => by
    have := hsp j; omega
  have sr' : ∀ j, τs c lo hi ρ α j + whr ≤ τs c lo hi ρ α (j + 1) := fun j => by
    have := hsp j; omega
  have hlo1 : 1 ≤ hi := by have := WinFifoCausal.s_lh S E T; omega
  refine ⟨c, link_of_gen hL.1 hL.2 (wire_di Wa hc (by omega) sa') (wire_di Wr hc (by omega) sr')
    lop lho (hpwr 0 (by omega)) (Wa.H_PWR 0 (by have := Wa.H_POS; have := win_le Wa.H_WIN; omega))
    (Wr.H_PWR 0 (by have := Wr.H_POS; have := win_le Wr.H_WIN; omega))⟩

def isLink {n : Nat} : K n → Bool
  | .link _ _ => true
  | _ => false

theorem isLink_eq {n : Nat} {k : K n} (h : isLink k = true) : ∃ i o, k = .link i o := by
  cases k <;> simp_all [isLink]

/-- **End to end, link class.** C's gcd_hw circuit safety (`gcd_hw_circuit_safe`), with
`H_CELLS` for every one of the 175 link operators replaced by B's physical link model
(`PhysLink`); `H_CELLS` for the other operator classes, H_BUNDLE and H_CM_FORCED (C's O1)
stay C's hypotheses. -/
theorem gcd_hw_safe_phys_links (a b : Nat) (ch : Fin NC → Chan)
    (H_LINKS : ∀ (o : Fin NO) (i o' : Fin NC), opAt o = .link i o' → PhysLink (ch i) (ch o'))
    (H_OTHER : ∀ o : Fin NO, isLink (opAt o) = false → Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_CM_FORCED : ∃ y, Good a b y ∧ ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) := by
  refine gcd_hw_circuit_safe a b ch (fun o => ?_) H_BUNDLE H_CM_FORCED
  by_cases hl : isLink (opAt o) = true
  · obtain ⟨i, o', hk⟩ := isLink_eq hl
    rw [hk]; exact link_of_phys (H_LINKS o i o' hk)
  · exact H_OTHER o (by simpa using hl)

/-- The link-to-link channels of gcd_hw's circuit network. -/
def llChans : List (Fin NC) :=
  (List.finRange NC).filter (fun c => isLink (opAt (prodOf c)) && isLink (opAt (consOf c)))

theorem link_count : ((List.finRange NO).filter (fun o => isLink (opAt o))).length = 175 := by
  decide +kernel

theorem ll_count : llChans.length = 75 := by decide +kernel

/-- Links whose input AND output channels are both link-to-link (`env1_of_neighbours`
applies to them, modulo the guarantees). -/
theorem interior_count : ((List.finRange NO).filter (fun o => isLink (opAt o) &&
    (opAt o).insC.all (fun c => isLink (opAt (prodOf c))) &&
    (opAt o).outsC.all (fun c => isLink (opAt (consOf c))))).length = 12 := by decide +kernel

def isFork2 {n : Nat} : K n → Bool
  | .forkG _ os => os.length == 2
  | .forkH _ os _ _ _ _ => os.length == 2
  | _ => false

/-- No 2-way fork of gcd_hw is fed by a link (so `fork_env`'s `U` is never a link there). -/
theorem fork_from_link_count : ((List.finRange NO).filter (fun o => isFork2 (opAt o) &&
    (opAt o).insC.all (fun c => isLink (opAt (prodOf c))))).length = 0 := by decide +kernel

/-- Every link-to-link channel's two ends really are a link's output and a link's input. -/
theorem ll_ends : ∀ c ∈ llChans, (∃ i, opAt (prodOf c) = .link i c) ∧
    (∃ o, opAt (consOf c) = .link c o) := by
  intro c hc
  simp only [llChans, List.mem_filter, Bool.and_eq_true] at hc
  obtain ⟨-, hp, hq⟩ := hc
  obtain ⟨i, o, hk⟩ := isLink_eq hp
  obtain ⟨i', o', hk'⟩ := isLink_eq hq
  have h1 := prod_mem c; rw [hk] at h1
  have h2 := cons_mem c; rw [hk'] at h2
  simp only [K.outsC, K.insC, List.mem_singleton] at h1 h2
  subst h1; subst h2
  exact ⟨⟨i, hk⟩, ⟨o', hk'⟩⟩

/-! ## 6. Non-vacuity, with nonzero delays -/

open Formal.Cells.PipeTimed.Wit (sq sq_pre sq_phase sq_shift rstW)

def τ4 (o j : Nat) : Nat := o + 4 * j

theorem wire_sq (o o' : Nat) (h : o' = o + 1) : Wire 1 1 (sq o) (sq o') := by
  subst h
  refine ⟨CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1)
      (fun t => sq_shift o 1 t),
    WinFifoCausal.noRevertI_shift (fun t ht => by
      have := sq_shift o 1 (t - 1); rw [Nat.sub_add_cancel ht] at this; exact this),
    Nat.le_refl 1, fun t ht => sq_pre (o + 1) t (by omega)⟩

theorem phases_sq (o : Nat) : Phases (sq o) (τ4 o) :=
  ⟨fun t h => sq_pre o t h, fun j t h1 h2 => sq_phase o j t h1 (by unfold τ4 at h2; omega)⟩

theorem eps_sq (o o' : Nat) (h : o' = o + 1) (j : Nat) : ε (sq o') 1 1 (τ4 o) j = o + 1 + 4 * j := by
  subst h; unfold ε τ4
  rw [nt_eq (sq (o + 1)) (Nat.le_refl 1) (sq_phase (o + 1) j _ (by omega) (by omega))]; omega

/-- **Link-to-link witness**: B's two-stage pipe run (`Wx.gates_w`, the real `bd_c2n`
controllers; nodes `sq 5`, `sq 7`, request line `sq 6`, acknowledge line `sq 8`, all
delays 1): every hypothesis of `link_link_env` holds, and the derived `Es`, `Ea` (3 ticks)
are met with EQUALITY (`τB j + 3 = ρB (j+1)`, `τA j + 3 = αA (j+1)`). -/
theorem link_link_witness :
    WinFifoCausal.Gates2W WinFifoCausal.Wx.Ww rstW (sq 4) (sq 8) (sq 6) (sq 6) (sq 10) (sq 8)
      1 1 1 1 ∧
    Phases (sq 5) (τ4 5) ∧ Phases (sq 7) (τ4 7) ∧
    Wire 1 1 (sq 5) (sq 6) ∧ Wire 1 1 (sq 7) (sq 8) ∧
    4 + 1 ≤ τ4 5 0 ∧
    (∀ j, ε (sq 8) 1 1 (τ4 7) j + 1 ≤ τ4 5 (j + 1)) ∧
    (∀ j, ε (sq 6) 1 1 (τ4 5) j + 1 ≤ τ4 7 j) ∧
    (1 ≤ 4 ∧ 1 ≤ 4) ∧ (1 ≤ 1 + 1 + 1 + 1 ∧ 1 ≤ 1 + 1 + 1 + 1) ∧
    (∀ j, τ4 7 j + (1 + 1 + 1) = ε (sq 6) 1 1 (τ4 5) (j + 1)) ∧
    (∀ j, τ4 5 j + (1 + 1 + 1) = ash 4 (ε (sq 8) 1 1 (τ4 7)) (j + 1)) := by
  refine ⟨WinFifoCausal.Wx.gates_w, phases_sq 5, phases_sq 7, wire_sq 5 6 rfl, wire_sq 7 8 rfl,
    by decide, fun j => ?_, fun j => ?_, by decide, by decide, fun j => ?_, fun j => ?_⟩
  · rw [eps_sq 7 8 rfl]; unfold τ4; omega
  · rw [eps_sq 5 6 rfl]; unfold τ4; omega
  · rw [eps_sq 5 6 rfl]; unfold τ4; omega
  · show τ4 5 j + (1 + 1 + 1) = ε (sq 8) 1 1 (τ4 7) j
    rw [eps_sq 7 8 rfl]; unfold τ4; omega

/-- Square wave with phases of 7 ticks (period 14). -/
def sq7 (o t : Nat) : Bool := decide (o ≤ t ∧ (t - o) % 14 < 7)

theorem sq7_pre (o t : Nat) (h : t < o) : sq7 o t = false := by unfold sq7; simp; omega

theorem sq7_phase (o j t : Nat) (h1 : o + 7 * j ≤ t) (h2 : t < o + 7 * (j + 1)) :
    sq7 o t = Vph j := by
  unfold sq7 Vph LinkTimed.Vph
  by_cases hj : j % 2 = 0
  · have : (t - o) % 14 < 7 := by omega
    simp [hj, this, show o ≤ t by omega]
  · have : ¬ ((t - o) % 14 < 7) := by omega
    simp [hj, this]

theorem sq7_shift (o d t : Nat) : sq7 (o + d) (t + d) = sq7 o t := by
  unfold sq7
  have e : t + d - (o + d) = t - o := by omega
  rw [e]
  by_cases h : o ≤ t
  · simp [h, show o + d ≤ t + d by omega]
  · simp [h, show ¬ (o + d ≤ t + d) by omega]

def τ7 (o j : Nat) : Nat := o + 7 * j

theorem phases_sq7 (o : Nat) : Phases (sq7 o) (τ7 o) :=
  ⟨fun t h => sq7_pre o t h, fun j t h1 h2 => sq7_phase o j t h1 (by unfold τ7 at h2; omega)⟩

theorem wire_sq7 (o d o' : Nat) (hd : 1 ≤ d) (h : o' = o + d) : Wire d d (sq7 o) (sq7 o') := by
  subst h
  refine ⟨CElemTiming.transport_winDelay (Nat.le_refl d) (Nat.le_refl d)
      (fun t => sq7_shift o d t),
    WinFifoCausal.noRevertI_shift (fun t ht => by
      have := sq7_shift o d (t - d); rw [Nat.sub_add_cancel ht] at this; exact this),
    hd, fun t ht => sq7_pre (o + d) t (by omega)⟩

theorem eps7 {τ : Nat → Nat} (o d o' : Nat) (h : o' = o + d) (hτ : ∀ j, τ j = o + 7 * j)
    (j : Nat) : ε (sq7 o') d d τ j = o + d + 7 * j := by
  subst h; unfold ε; rw [hτ j]
  rw [nt_eq (sq7 (o + d)) (Nat.le_refl d) (sq7_phase (o + d) j _ (by omega) (by omega))]; omega

theorem tF_w (j : Nat) :
    tF (sq7 10) 1 1 (ε (sq7 8) 1 1 (τ7 7)) (ε (sq7 9) 1 1 (τ7 8)) j = 10 + 7 * j := by
  unfold tF cph
  rw [eps7 (τ := τ7 7) 7 1 8 rfl (fun _ => rfl), eps7 (τ := τ7 8) 8 1 9 rfl (fun _ => rfl)]
  rw [show max (7 + 1 + 7 * j) (8 + 1 + 7 * j) = 9 + 7 * j by omega]
  rw [nt_eq (sq7 10) (Nat.le_refl 1) (sq7_phase 10 j _ (by omega) (by omega))]; omega

/-- **Fork witness** (phases of 7 ticks): upstream node `sq7 5`; request wires of delay 1
(to `L0`) and 2 (to `L1`); consumer nodes `sq7 7`, `sq7 8` (LUT delay 1); the fork
C-element's pins `sq7 8`, `sq7 9` (they DISAGREE on `[8, 9)` each phase, so the C-element
holds through its feedback there), its node `sq7 10` (LUT delay 1), the acknowledge wire to
`U` (delay 1, `sq7 11`): every hypothesis of `fork_env` holds (the upstream guarantee with
equality), and so its conclusion: Bfb's `EnvC` of the fork C-element with `Es = 5`,
`Ea = 6`. -/
theorem fork_witness :
    Phases (sq7 5) (τ7 5) ∧ Phases (sq7 7) (τ7 7) ∧ Phases (sq7 8) (τ7 8) ∧
    Phases (sq7 10) (tF (sq7 10) 1 1 (ε (sq7 8) 1 1 (τ7 7)) (ε (sq7 9) 1 1 (τ7 8))) ∧
    Wire 1 1 (sq7 5) (sq7 6) ∧ Wire 2 2 (sq7 5) (sq7 7) ∧ Wire 1 1 (sq7 7) (sq7 8) ∧
    Wire 1 1 (sq7 8) (sq7 9) ∧ Wire 1 1 (sq7 10) (sq7 11) ∧
    (∀ j, ε (sq7 11) 1 1 (tF (sq7 10) 1 1 (ε (sq7 8) 1 1 (τ7 7)) (ε (sq7 9) 1 1 (τ7 8))) j + 1
      = τ7 5 (j + 1)) ∧
    sq7 8 8 ≠ sq7 9 8 ∧
    EnvC (sq7 8) (sq7 9) rstW (sq7 10) 1 1 4 (ε (sq7 8) 1 1 (τ7 7)) (ε (sq7 9) 1 1 (τ7 8))
      (1 + 1 + 1 + 1 + 1) (1 + 1 + 2 + 1 + 1) := by
  have hF : Phases (sq7 10) (tF (sq7 10) 1 1 (ε (sq7 8) 1 1 (τ7 7)) (ε (sq7 9) 1 1 (τ7 8))) :=
    ⟨fun t h => sq7_pre 10 t (by rw [tF_w] at h; omega),
     fun j t h1 h2 => sq7_phase 10 j t (by rw [tF_w] at h1; omega) (by rw [tF_w] at h2; omega)⟩
  have GU : ∀ j, ε (sq7 11) 1 1 (tF (sq7 10) 1 1 (ε (sq7 8) 1 1 (τ7 7)) (ε (sq7 9) 1 1 (τ7 8))) j
      + 1 = τ7 5 (j + 1) := fun j => by
    rw [eps7 10 1 11 rfl tF_w]; unfold τ7; omega
  have r := fork_env (OU := sq7 5) (req0 := sq7 6) (req1 := sq7 7) (O0 := sq7 7) (O1 := sq7 8)
    (a := sq7 8) (b := sq7 9) (OF := sq7 10) (ackU := sq7 11) (rst := rstW) (R := 4)
    (loU := 1) (lo0 := 1) (lo1 := 1)
    (phases_sq7 5) (phases_sq7 7) (phases_sq7 8) hF (Nat.le_refl 1)
    (wire_sq7 5 1 6 (Nat.le_refl 1) rfl) (wire_sq7 5 2 7 (by decide) rfl)
    (wire_sq7 7 1 8 (Nat.le_refl 1) rfl) (wire_sq7 8 1 9 (Nat.le_refl 1) rfl)
    (wire_sq7 10 1 11 (Nat.le_refl 1) rfl) (fun _ => rfl) (by decide)
    (fun j => by rw [GU j]; exact Nat.le_refl _)
    (fun j => by rw [eps7 (τ := τ7 5) 5 1 6 rfl (fun _ => rfl)]; unfold τ7; omega)
    (fun j => by rw [eps7 (τ := τ7 5) 5 2 7 rfl (fun _ => rfl)]; unfold τ7; omega)
    (by decide) (by decide)
  exact ⟨phases_sq7 5, phases_sq7 7, phases_sq7 8, hF, wire_sq7 5 1 6 (Nat.le_refl 1) rfl,
    wire_sq7 5 2 7 (by decide) rfl, wire_sq7 7 1 8 (Nat.le_refl 1) rfl,
    wire_sq7 8 1 9 (Nat.le_refl 1) rfl, wire_sq7 10 1 11 (Nat.le_refl 1) rfl, GU, by decide, r.1⟩

end Formal.Cells.LutFbBridge2Env
