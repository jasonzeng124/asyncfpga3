import Formal.Cells.AssumeGuaranteeMuxOr
import Formal.Cells.AssumeGuaranteeEndsCap

/-!
# Probe Bmux2 (shard B): mux cells, sources and buffers as cell specs; gcd_hw with fewer contracts

`AssumeGuaranteeEndsNet` closes a mixed network whose cells are links, `n`-pin C-elements
and steer branches (B gate models) or assumed segment contracts. This file adds four
classes as CELL SPECS (B gate model + H_TIMES + edge-time departure bounds, no environment,
no contract), proves H_CELL and H_WAIT of each, closes the larger mixed network
(`mixed_closed2`), and restates gcd_hw's capstone with the mux cells and the sources
discharged (`gcd_hw_safe_net2`).

## Assumed / proved / NOT covered

**Assumed** (per cell, named fields): `MuxJSpec` (`bd_mux` `uj0`/`uj1` as `G2` of the input
request and the gated control, H_SEL_STABLE, control token enumeration `κ`), `MuxASpec`
(`uxa`/`uya` as `G2` of the join and `z_ack`, the x-token enumeration `κ`, H_SNDZ,
H_ZFALL), `SrcSpec` (`bd_src` LUT1 `¬ack`, H_PWR_SRC), `BufSpec` (a feedback-free 1-pin
LUT: the `bd_mux` delay chain `udly`); for each H_TIMES and the departure bounds as
EDGE-TIME inequalities (as for `LinkSpec`/`CelSpec`/`SteerSpec`).

**Proved:** `muxj_spec_cell`/`_wait`, `muxa_spec_cell`/`_wait`, `src_spec_cell`/`_wait`,
`buf_spec_cell`/`_wait`; `mixed_closed2`, `mixed_pins2`; `udly_id` (the real `udly` LUT1s
are buffers); `op_classes2` (kernel census: of gcd_hw's 367 operators, after links, forks
N ≤ 4, joins N = 2, steers, muxes and sources, 42 remain: `join1` 11 and `sink` 18 with NO
cell, `muxn` 1, `amerge` 9, `forkH5` 2, `forkH6` 1); `gcd_hw_safe_net2`.

**NOT covered:** the acknowledge/request ORs (38 steer `uack`, 21 mux `uor`) stay
contracts: their low segments are not strictly causal in the segment order
(`AssumeGuaranteeMuxOr.Wit.or_not_causal`), so no spec of this rule can carry them; the
departure bounds are edge-time inequalities, not derived from delay constants (as before);
the elaboration (`ι`, which cell drives which pin) is abstract; no witness of the whole
`GcdNetOK2`. Core Lean only.
-/

namespace Formal.Cells.AssumeGuaranteeMuxNet
open Formal.Cells
open Formal.Cells.AssumeGuaranteeLinks (SegK phases_of_segK)
open Formal.Cells.AssumeGuaranteeEnds (GPin gE GA net_closed_gen net_pins_gen sN gc_sN
  lutnf_segK GC2 GC3 GC4)
open Formal.Cells.AssumeGuaranteeEndsNet
open Formal.Cells.AssumeGuaranteeMux
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.LutFbBridge (Phases)
open Formal.Cells.LutFbBridge2 (CelG gc G2 pv2 gate mono_of_succ)
open Formal.Net.Ops.Gen (genF)
open Formal.Gen Formal.Gen.Cells

variable {ι : Type}

/-! ## 1. The specs -/

/-- **A mux join** (`uj0`, `b = false`; `uj1`, `b = true`): pins the input request `xp`
(segments `≤ k`) and the control request `cp` (segments `≤ sN κ k`). -/
structure MuxJSpec (D : GD ι) (c : ι) (xp cp : GPin ι) (b : Bool) (s σ : Nat → Bool)
    (κ : Nat → Nat) (E : Nat) : Prop where
  H_PINS : D.pins c = [xp, cp]
  H_NBX : xp.nb = fun k => k + 1
  H_NBC : cp.nb = fun k => sN κ k + 1
  H_CEL : CelG G2 (pv2 xp.P (gate b cp.P s)) D.rst (D.O c) (D.qp c) (D.lo c) (D.hi c)
    (D.fl c) (D.fh c)
  H_PWR : ∀ t, t < D.hi c → D.O c t = false
  H_TIMES : ∀ j, D.τ c j =
    nt (D.O c) (D.lo c) (D.hi c) (max (gE D.τ xp j) (gc κ (gE D.τ cp) j)) (Vph j)
  H_INC : ∀ k, gE D.τ cp k < gE D.τ cp (k + 1)
  H_SEL_STABLE : ∀ n t, gE D.τ cp (2 * n) ≤ t → t < gE D.τ cp (2 * n + 1) → s t = σ n
  H_KAPPA : ∀ m, κ m < κ (m + 1)
  H_KAPPA_B : ∀ m, σ (κ m) = b
  H_KAPPA_ALL : ∀ n, σ n = b → ∃ m, κ m = n
  H_RST_EARLY : D.R ≤ max (gE D.τ xp 0) (gc κ (gE D.τ cp) 0)
  H_SND : ∀ j, D.τ c j + E ≤ gE D.τ xp (j + 1) ∧ D.τ c j + E ≤ gc κ (gE D.τ cp) (j + 1)
  H_RST_LONG : D.hi c + D.fh c ≤ D.R
  H_LAT : D.hi c + D.fh c ≤ D.lo c + E

/-- **A mux acknowledge** (`uxa`/`uya`): pins the join `ap` (segments `≤ k`) and the output
acknowledge `zp` (all output tokens; segments `≤ sN κ k`, `κ` this input's tokens). -/
structure MuxASpec (D : GD ι) (c : ι) (ap zp : GPin ι) (κ : Nat → Nat) (E : Nat) : Prop where
  H_PINS : D.pins c = [ap, zp]
  H_NBA : ap.nb = fun k => k + 1
  H_NBZ : zp.nb = fun k => sN κ k + 1
  H_CEL : CelG G2 (pv2 ap.P zp.P) D.rst (D.O c) (D.qp c) (D.lo c) (D.hi c) (D.fl c) (D.fh c)
  H_PWR : ∀ t, t < D.hi c → D.O c t = false
  H_TIMES : ∀ j, D.τ c j =
    nt (D.O c) (D.lo c) (D.hi c) (max (gE D.τ ap j) (gc κ (gE D.τ zp) j)) (Vph j)
  H_INC : ∀ k, gE D.τ zp k < gE D.τ zp (k + 1)
  H_KAPPA : ∀ m, κ m < κ (m + 1)
  H_RST_EARLY : D.R ≤ max (gE D.τ ap 0) (gc κ (gE D.τ zp) 0)
  H_SNDJ : ∀ j, D.τ c j + E ≤ gE D.τ ap (j + 1)
  H_SNDZ : ∀ j, D.τ c j + E ≤ gE D.τ zp (sN κ j + 1)
  H_ZFALL : ∀ m, 0 < κ m → gE D.τ zp (2 * κ m - 1) ≤ gE D.τ ap (2 * m)
  H_RST_LONG : D.hi c + D.fh c ≤ D.R
  H_LAT : D.hi c + D.fh c ≤ D.lo c + E

/-- **A source** (the real `bd_src` LUT1): one pin, its acknowledge, segments `< k`. -/
structure SrcSpec (D : GD ι) (c : ι) (ap : GPin ι) : Prop where
  H_PINS : D.pins c = [ap]
  H_NB : ap.nb = fun k => k
  H_LUT_WIN : Win (D.lo c) (D.hi c) (fun t => genF bd_src_W2 "u" .O ["ack"] [ap.P t]) (D.O c)
  H_NO_REVERT : NoRevertI (D.lo c) (D.hi c)
    (fun t => genF bd_src_W2 "u" .O ["ack"] [ap.P t]) (D.O c)
  H_PWR_SRC : ∀ t, t + 1 < D.hi c → D.O c (t + 1) ≠ D.O c t → D.O c (t + 1) = true
  H_TIMES : ∀ j, D.τ c j = srcE (D.O c) (D.lo c) (D.hi c) (gE D.τ ap) j
  H_SPACE : D.hi c ≤ gE D.τ ap 0 ∧ ∀ j, gE D.τ ap j + D.hi c < gE D.τ ap (j + 1) + D.lo c

/-- **A buffer** (a feedback-free 1-pin LUT copying its pin: the `bd_mux` delay chain). -/
structure BufSpec (D : GD ι) (c : ι) (p : GPin ι) : Prop where
  H_PINS : D.pins c = [p]
  H_NB : p.nb = fun k => k + 1
  H_LUT_WIN : Win (D.lo c) (D.hi c) p.P (D.O c)
  H_NO_REVERT : NoRevertI (D.lo c) (D.hi c) p.P (D.O c)
  H_PWR : ∀ t, t < D.hi c → D.O c t = false
  H_TIMES : ∀ j, D.τ c j = nt (D.O c) (D.lo c) (D.hi c) (gE D.τ p j) (Vph j)
  H_SPACE : D.hi c ≤ gE D.τ p 0 ∧ ∀ j, gE D.τ p j + D.hi c < gE D.τ p (j + 1) + D.lo c

/-- The real `udly` LUT1s of `bd_mux` (W = 2, DELAY = 2) are buffers. -/
theorem udly_id : ∀ a : Bool,
    genF bd_mux_W2 "udly.chain.g[0].u" .O ["either"] [a] = a ∧
    genF bd_mux_W2 "udly.chain.g[1].u" .O ["udly.chain.s[1]"] [a] = a := by decide +kernel

/-! ## 2. H_CELL and H_WAIT of each spec -/

section cls
variable {D : GD ι} (NW : NetW D)
include NW

theorem pin_mono {c : ι} {p : GPin ι} (hp : p ∈ D.pins c) {j j' : Nat} (h : j ≤ j') :
    gE D.τ p j ≤ gE D.τ p j' :=
  gE_mono (NW.H_WIRE c p hp) (fun j => (NW.H_SP c p hp j).2) h

theorem muxj_spec_cell {c : ι} {xp cp : GPin ι} {b : Bool} {s σ : Nat → Bool} {κ : Nat → Nat}
    {E : Nat} (S : MuxJSpec D c xp cp b s σ κ E) (k : Nat) (hA : GA D.τ D.pins c k) :
    SegK (D.O c) (D.τ c) k := by
  have hx : xp ∈ D.pins c := by rw [S.H_PINS]; simp
  have hc : cp ∈ D.pins c := by rw [S.H_PINS]; simp
  rw [show D.τ c = _ from funext S.H_TIMES]
  exact muxj_segK S.H_CEL NW.H_RST S.H_RST_LONG S.H_LAT S.H_PWR S.H_INC S.H_SEL_STABLE
    S.H_KAPPA S.H_KAPPA_B S.H_KAPPA_ALL S.H_RST_EARLY
    (fun j => by rw [← S.H_TIMES j]; exact S.H_SND j) k
    (hA xp hx k (by rw [S.H_NBX]; dsimp only; omega))
    (fun k' h => hA cp hc k' (by rw [S.H_NBC]; dsimp only; omega))

theorem muxj_spec_wait {c : ι} {xp cp : GPin ι} {b : Bool} {s σ : Nat → Bool} {κ : Nat → Nat}
    {E : Nat} (S : MuxJSpec D c xp cp b s σ κ E) :
    ∀ p ∈ D.pins c, ∀ k k', k' < p.nb k → gE D.τ p k' + D.lo c ≤ D.τ c k := by
  intro p hp k k' hk
  have hlh := win_le S.H_CEL.H_LUT_WIN
  have hn := nt_lo (D.O c) (max (gE D.τ xp k) (gc κ (gE D.τ cp) k)) (Vph k) hlh (hi := D.hi c)
  rw [S.H_TIMES k]
  have h1 := Nat.le_max_left (gE D.τ xp k) (gc κ (gE D.τ cp) k)
  have h2 := Nat.le_max_right (gE D.τ xp k) (gc κ (gE D.τ cp) k)
  have hp' := hp
  rw [S.H_PINS] at hp'
  rcases List.mem_cons.1 hp' with rfl | hp'
  · rw [S.H_NBX] at hk; dsimp only at hk
    have := pin_mono NW hp (show k' ≤ k by omega); omega
  · have e : p = cp := by simpa using hp'
    subst e
    rw [S.H_NBC] at hk; dsimp only at hk
    have := pin_mono NW hp (show k' ≤ sN κ k by omega)
    have h3 : gc κ (gE D.τ p) k = gE D.τ p (sN κ k) := gc_sN _ _ _
    omega

theorem muxa_spec_cell {c : ι} {ap zp : GPin ι} {κ : Nat → Nat} {E : Nat}
    (S : MuxASpec D c ap zp κ E) (k : Nat) (hA : GA D.τ D.pins c k) :
    SegK (D.O c) (D.τ c) k := by
  have ha : ap ∈ D.pins c := by rw [S.H_PINS]; simp
  have hz : zp ∈ D.pins c := by rw [S.H_PINS]; simp
  rw [show D.τ c = _ from funext S.H_TIMES]
  exact muxa_segK S.H_CEL NW.H_RST S.H_RST_LONG S.H_LAT S.H_PWR S.H_INC S.H_KAPPA
    S.H_RST_EARLY (fun j => by rw [← S.H_TIMES j]; exact S.H_SNDJ j)
    (fun j => by rw [← S.H_TIMES j]; exact S.H_SNDZ j) S.H_ZFALL k
    (hA ap ha k (by rw [S.H_NBA]; dsimp only; omega))
    (fun k' h => hA zp hz k' (by rw [S.H_NBZ]; dsimp only; omega))

theorem muxa_spec_wait {c : ι} {ap zp : GPin ι} {κ : Nat → Nat} {E : Nat}
    (S : MuxASpec D c ap zp κ E) :
    ∀ p ∈ D.pins c, ∀ k k', k' < p.nb k → gE D.τ p k' + D.lo c ≤ D.τ c k := by
  intro p hp k k' hk
  have hlh := win_le S.H_CEL.H_LUT_WIN
  have hn := nt_lo (D.O c) (max (gE D.τ ap k) (gc κ (gE D.τ zp) k)) (Vph k) hlh (hi := D.hi c)
  rw [S.H_TIMES k]
  have h1 := Nat.le_max_left (gE D.τ ap k) (gc κ (gE D.τ zp) k)
  have h2 := Nat.le_max_right (gE D.τ ap k) (gc κ (gE D.τ zp) k)
  have hp' := hp
  rw [S.H_PINS] at hp'
  rcases List.mem_cons.1 hp' with rfl | hp'
  · rw [S.H_NBA] at hk; dsimp only at hk
    have := pin_mono NW hp (show k' ≤ k by omega); omega
  · have e : p = zp := by simpa using hp'
    subst e
    rw [S.H_NBZ] at hk; dsimp only at hk
    have := pin_mono NW hp (show k' ≤ sN κ k by omega)
    have h3 : gc κ (gE D.τ p) k = gE D.τ p (sN κ k) := gc_sN _ _ _
    omega

theorem src_spec_cell {c : ι} {ap : GPin ι} (S : SrcSpec D c ap) (k : Nat)
    (hA : GA D.τ D.pins c k) : SegK (D.O c) (D.τ c) k := by
  have ha : ap ∈ D.pins c := by rw [S.H_PINS]; simp
  rw [show D.τ c = _ from funext S.H_TIMES]
  exact src_segK S.H_LUT_WIN S.H_NO_REVERT (NW.H_LUT_POS c) S.H_PWR_SRC S.H_SPACE k
    (fun k' h => hA ap ha k' (by rw [S.H_NB]; dsimp only; omega))

theorem src_spec_wait {c : ι} {ap : GPin ι} (S : SrcSpec D c ap) :
    ∀ p ∈ D.pins c, ∀ k k', k' < p.nb k → gE D.τ p k' + D.lo c ≤ D.τ c k := by
  intro p hp k k' hk
  have hp' := hp
  rw [S.H_PINS] at hp'
  have e : p = ap := by simpa using hp'
  subst e
  rw [S.H_NB] at hk; dsimp only at hk
  rw [S.H_TIMES k]
  exact src_wait (win_le S.H_LUT_WIN) (fun i j h => pin_mono NW hp h) k k' hk

omit NW in
theorem buf_spec_cell {c : ι} {p : GPin ι} (S : BufSpec D c p) (k : Nat)
    (hA : GA D.τ D.pins c k) : SegK (D.O c) (D.τ c) k := by
  have hp : p ∈ D.pins c := by rw [S.H_PINS]; simp
  rw [show D.τ c = _ from funext S.H_TIMES]
  exact lutnf_segK S.H_LUT_WIN S.H_NO_REVERT S.H_PWR S.H_SPACE k
    (hA p hp k (by rw [S.H_NB]; dsimp only; omega))

theorem buf_spec_wait {c : ι} {p : GPin ι} (S : BufSpec D c p) :
    ∀ q ∈ D.pins c, ∀ k k', k' < q.nb k → gE D.τ q k' + D.lo c ≤ D.τ c k := by
  intro q hq k k' hk
  have hq' := hq
  rw [S.H_PINS] at hq'
  have e : q = p := by simpa using hq'
  subst e
  rw [S.H_NB] at hk; dsimp only at hk
  rw [S.H_TIMES k]
  have := nt_lo (D.O c) (gE D.τ q k) (Vph k) (win_le S.H_LUT_WIN) (hi := D.hi c)
  have := pin_mono NW hq (show k' ≤ k by omega); omega

end cls

/-! ## 3. The larger mixed network, closed -/

/-- A cell meets one of the specs of this file. -/
def Proved2 (D : GD ι) (c : ι) : Prop :=
  (∃ xp cp b s σ κ E, MuxJSpec D c xp cp b s σ κ E) ∨
  (∃ ap zp κ E, MuxASpec D c ap zp κ E) ∨
  (∃ ap, SrcSpec D c ap) ∨
  (∃ p, BufSpec D c p)

/-- **The assume-guarantee circle closed on a mixed network with mux cells, sources and
buffers.** Every cell is a link, an `n`-pin C-element, a steer branch (`Proved`), a mux
join, a mux acknowledge, a source or a buffer (`Proved2`), all with B gate models and no
environment or contract, or an assumed segment contract. Then every node is a clean step
signal. -/
theorem mixed_closed2 (D : GD ι) (NW : NetW D)
    (H_CLS : ∀ c, Proved D c ∨ Proved2 D c ∨ Contract D c) :
    ∀ c, Phases (D.O c) (D.τ c) := by
  refine net_closed_gen D.O D.τ D.lo D.pins (fun c k hA => ?_) NW.H_WIRE
    (fun c => ?_) NW.H_LUT_POS NW.H_SP
  · rcases H_CLS c with ((⟨_, _, _, _, L⟩ | ⟨_, _, _, _, Cs⟩ | ⟨_, _, _, _, _, Ss⟩) |
      (⟨_, _, _, _, _, _, _, J⟩ | ⟨_, _, _, _, A⟩ | ⟨_, Sr⟩ | ⟨_, B⟩) | K)
    · exact link_spec_cell NW L k hA
    · exact cel_spec_cell NW Cs k hA
    · exact steer_spec_cell Ss k hA
    · exact muxj_spec_cell NW J k hA
    · exact muxa_spec_cell NW A k hA
    · exact src_spec_cell NW Sr k hA
    · exact buf_spec_cell B k hA
    · exact K.1 k hA
  · rcases H_CLS c with ((⟨_, _, _, _, L⟩ | ⟨_, _, _, _, Cs⟩ | ⟨_, _, _, _, _, Ss⟩) |
      (⟨_, _, _, _, _, _, _, J⟩ | ⟨_, _, _, _, A⟩ | ⟨_, Sr⟩ | ⟨_, B⟩) | K)
    · exact link_spec_wait NW L
    · exact cel_spec_wait NW Cs
    · exact steer_spec_wait Ss
    · exact muxj_spec_wait NW J
    · exact muxa_spec_wait NW A
    · exact src_spec_wait NW Sr
    · exact buf_spec_wait NW B
    · exact K.2

theorem mixed_pins2 (D : GD ι) (NW : NetW D)
    (H_CLS : ∀ c, Proved D c ∨ Proved2 D c ∨ Contract D c) :
    ∀ c, ∀ p ∈ D.pins c, Phases p.P (gE D.τ p) :=
  net_pins_gen D.O D.τ D.pins (mixed_closed2 D NW H_CLS) NW.H_WIRE NW.H_SP

/-- A `LinkSpec` cell of the larger network has `Env1` and `Timing1`, DERIVED. -/
theorem link_spec_env1_2 (D : GD ι) (NW : NetW D)
    (H_CLS : ∀ c, Proved D c ∨ Proved2 D c ∨ Contract D c)
    {c : ι} {rp ap : GPin ι} {Es Ea : Nat} (L : LinkSpec D c rp ap Es Ea) :
    WinFifoCausal.Env1 rp.P ap.P D.rst (D.O c) (D.lo c) (D.hi c) D.R (gE D.τ rp)
      (LutFbBridge2Env.ash D.R (gE D.τ ap)) Es Ea ∧
    WinFifoCausal.Timing1 (D.lo c) (D.hi c) (D.fh c) D.R Es Ea := by
  have pr := mixed_pins2 D NW H_CLS c rp (by rw [L.H_PINS]; simp)
  have pa := mixed_pins2 D NW H_CLS c ap (by rw [L.H_PINS]; simp)
  exact ⟨{ H_RST := NW.H_RST
           H_REQ_LOW0 := fun t _ h => pr.pre t h
           H_REQ := pr.ph
           H_ACK0 := rfl
           H_ACK := AssumeGuaranteeFork.ack_shape pa
           H_RST_EARLY := L.H_RST_EARLY
           H_SND := fun j => by rw [← L.H_TIMES j]; exact L.H_SND j
           H_RCV := fun j => by rw [← L.H_TIMES j]; exact L.H_RCV j }, L.H_T⟩

/-- **Non-vacuity of `mixed_closed2`'s hypotheses**: Bseg's live mixed network (a real
`bd_c2n` link between a source and a sink contract) meets them. -/
theorem mixed2_witness :
    NetW Wit.wG ∧ ∀ c, Proved Wit.wG c ∨ Proved2 Wit.wG c ∨ Contract Wit.wG c :=
  ⟨Wit.w_netW, fun c => (Wit.w_cls c).elim Or.inl (fun h => Or.inr (Or.inr h))⟩

/-! ## 4. gcd_hw: the mux cells and the sources discharged -/

section gcd
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe
open Formal.Cells.LutFbBridge2Env (isLink PhysLink gcd_hw_safe_phys_links)
open Formal.Cells.AssumeGuaranteeCap (kname census)
open Formal.Cells.AssumeGuaranteeEndsCap (tiedOp forkOuts joinIns steerIn CelTie GcdNet Tied
  LinkOut celTie_proved)

def isMuxK : K NC → Bool
  | .mux _ _ _ _ _ => true
  | _ => false
def isSrcK : K NC → Bool
  | .src _ _ _ => true
  | _ => false

/-- An operator whose handshake cells are all gate-modelled here, except the ORs (`uack` of
a steer, `uor` of a mux). -/
def tiedOp2 (k : K NC) : Bool := tiedOp k || isMuxK k || isSrcK k

/-- **What is left** (kernel census): after links, forks N ≤ 4, joins N = 2, steers, muxes
and sources, 42 of gcd_hw's 367 operators remain; 29 of them (`join1`, `sink`) have NO
cell. -/
theorem op_classes2 :
    census (((List.finRange NO).filter (fun o => !tiedOp2 (opAt o))).map (fun o => kname (opAt o)))
      = [("join1", 11), ("sink", 18), ("forkH5", 2), ("forkH6", 1), ("muxn", 1),
         ("amerge", 9)] := by
  decide +kernel

/-- The gate-level elaboration, with the mux and source cells: `mj o b` (`uj0`/`uj1`),
`ma o b` (`uxa`/`uya`), `md o i` (the two `udly` buffers), `mo o` (`uor`), `sr o` (the
source LUT). -/
structure GcdNet2 extends GcdNet where
  mj : Fin NO → Bool → ι
  ma : Fin NO → Bool → ι
  md : Fin NO → Fin 2 → ι
  sr : Fin NO → ι

/-- The cells that carry a B gate model in `GcdNetOK2` (the ORs do not). -/
def Tied2 (N : GcdNet2) (c : N.ι) : Prop :=
  Tied N.toGcdNet c ∨
  (∃ o cc x y z mw b, opAt o = .mux cc x y z mw ∧ (c = N.mj o b ∨ c = N.ma o b)) ∨
  (∃ o cc x y z mw i, opAt o = .mux cc x y z mw ∧ c = N.md o i) ∨
  (∃ o z w d, opAt o = .src z w d ∧ c = N.sr o)

/-- **The hypotheses on the elaboration**, as `GcdNetOK` plus: each mux's joins, acks and
delay buffers and each source carry B's gate model (with C's channel traces as the pins
of the joins, the `z_ack` pin of the acks, the acknowledge pin of the source; an ack's join
pin is driven by that join's cell); every other cell carries a segment contract. -/
structure GcdNetOK2 (ch : Fin NC → Chan) (N : GcdNet2) : Prop where
  NW : NetW N.D
  H_LINK : ∀ o i o', opAt o = .link i o' → ∃ rp ap Es Ea, LinkSpec N.D (N.lk o) rp ap Es Ea ∧
    rp.P = (ch i).req ∧ ap.P = (ch o').ack ∧ LinkOut N.D (N.lk o) (ch i) (ch o') Es Ea
  H_FORK : ∀ o os, forkOuts (opAt o) = some os → 2 ≤ os.length → os.length ≤ 4 →
    CelTie N.D (N.fa o) os (fun c => (ch c).ack)
  H_JOIN : ∀ o ins, joinIns (opAt o) = some ins → ins.length = 2 →
    CelTie N.D (N.jr o) ins (fun c => (ch c).req)
  H_STEER : ∀ o j, steerIn (opAt o) = some j → ∀ b, ∃ rp s σ κ,
    SteerSpec N.D (N.sb o b) rp b s σ κ ∧ rp.P = (ch j).req
  H_MUXJ : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ b, ∃ xp cp s σ κ E,
    MuxJSpec N.D (N.mj o b) xp cp b s σ κ E ∧ xp.P = (ch (if b then y else x)).req ∧
    cp.P = (ch cc).req
  H_MUXA : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ b, ∃ ap zp κ E,
    MuxASpec N.D (N.ma o b) ap zp κ E ∧ ap.drv = N.mj o b ∧ zp.P = (ch z).ack
  H_MUXD : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ i, ∃ p, BufSpec N.D (N.md o i) p
  H_SRC : ∀ o z w d, opAt o = .src z w d → ∃ ap, SrcSpec N.D (N.sr o) ap ∧ ap.P = (ch z).ack
  H_REST : ∀ c, ¬ Tied2 N c → Contract N.D c

section net
variable {ch : Fin NC → Chan} {N : GcdNet2} (H : GcdNetOK2 ch N)
include H

theorem gcd_cls2 (c : N.ι) : Proved N.D c ∨ Proved2 N.D c ∨ Contract N.D c := by
  by_cases ht : Tied2 N c
  · rcases ht with ht | ⟨o, cc, x, y, z, mw, b, h, rfl | rfl⟩ | ⟨o, cc, x, y, z, mw, i, h, rfl⟩ |
      ⟨o, z, w, d, h, rfl⟩
    · refine Or.inl ?_
      rcases ht with ⟨o, i, o', h, rfl⟩ | ⟨o, os, h, h1, h2, rfl⟩ | ⟨o, ins, h, h1, rfl⟩ |
        ⟨o, j, b, h, rfl⟩
      · obtain ⟨rp, ap, Es, Ea, L, _⟩ := H.H_LINK o i o' h
        exact Or.inl ⟨rp, ap, Es, Ea, L⟩
      · exact celTie_proved (H.H_FORK o os h h1 h2)
      · exact celTie_proved (H.H_JOIN o ins h h1)
      · obtain ⟨rp, s, σ, κ, S, _⟩ := H.H_STEER o j h b
        exact Or.inr (Or.inr ⟨rp, b, s, σ, κ, S⟩)
    · obtain ⟨xp, cp, s, σ, κ, E, S, _⟩ := H.H_MUXJ o cc x y z mw h b
      exact Or.inr (Or.inl (Or.inl ⟨xp, cp, b, s, σ, κ, E, S⟩))
    · obtain ⟨ap, zp, κ, E, S, _⟩ := H.H_MUXA o cc x y z mw h b
      exact Or.inr (Or.inl (Or.inr (Or.inl ⟨ap, zp, κ, E, S⟩)))
    · obtain ⟨p, S⟩ := H.H_MUXD o cc x y z mw h i
      exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inr ⟨p, S⟩))))
    · obtain ⟨ap, S, _⟩ := H.H_SRC o z w d h
      exact Or.inr (Or.inl (Or.inr (Or.inr (Or.inl ⟨ap, S⟩))))
  · exact Or.inr (Or.inr (H.H_REST c ht))

/-- **Every node of gcd_hw's gate-level network is a clean step signal.** -/
theorem gcd_net_nodes2 : ∀ c, Phases (N.D.O c) (N.D.τ c) :=
  mixed_closed2 N.D H.NW (gcd_cls2 H)

theorem physLink_of_net2 {o : Fin NO} {i o' : Fin NC} (h : opAt o = .link i o') :
    PhysLink (ch i) (ch o') := by
  obtain ⟨rp, ap, Es, Ea, L, e1, e2, wla, wha, wlr, whr, Wa, Wr, s1, s2, s3, s4, d1, d2⟩ :=
    H.H_LINK o i o' h
  obtain ⟨E, Tm⟩ := link_spec_env1_2 N.D H.NW (gcd_cls2 H) L
  have St := L.H_STAGE
  rw [e1, e2] at St E
  exact ⟨N.D.rst, N.D.O (N.lk o), N.D.qp (N.lk o), N.D.lo (N.lk o), N.D.hi (N.lk o),
    N.D.fl (N.lk o), N.D.fh (N.lk o), N.D.R, Es, Ea, wla, wha, wlr, whr, gE N.D.τ rp,
    Formal.Cells.LutFbBridge2Env.ash N.D.R (gE N.D.τ ap), St, E, Tm, H.NW.H_LUT_POS _,
    L.H_PWR, Wa, Wr, s1, s2, s3, s4, d1, d2⟩

end net

/-- **End to end, with the mux cells and the sources gate-modelled.** C's gcd_hw circuit
safety theorem with `H_CELLS` of all 175 links discharged by ONE gate-level network
(`GcdNetOK2`) in which every link, fork N ≤ 4, 2-input join, steer branch, mux join, mux
acknowledge, mux delay buffer and source carries B's gate model. Segment contracts remain
only for the cells not in `Tied2`: the 38 steer `uack` ORs, the 21 mux `uor` ORs, and the
cells of the muxn, the 9 amerges and the 3 fork trees (`op_classes2`; `join1` and `sink`
have no cell). Still assumed: the edge-time departure bounds and H_SP, C's `H_CELLS` of
the 192 non-link operators, H_BUNDLE, H_CM_FORCED. -/
theorem gcd_hw_safe_net2 (a b : Nat) (ch : Fin NC → Chan) (N : GcdNet2) (H : GcdNetOK2 ch N)
    (H_OTHER : ∀ o : Fin NO, isLink (opAt o) = false → Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_CM_FORCED : ∃ y, Good a b y ∧ ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) :=
  gcd_hw_safe_phys_links a b ch (fun _ _ _ h => physLink_of_net2 H h) H_OTHER H_BUNDLE
    H_CM_FORCED

end gcd

end Formal.Cells.AssumeGuaranteeMuxNet
