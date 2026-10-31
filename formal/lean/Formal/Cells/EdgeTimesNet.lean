import Formal.Cells.EdgeTimes
import Formal.Cells.AssumeGuaranteeEndsNet

/-!
# Probe Bedge (shard B): a link chain's departure bounds and H_SP, derived

`AssumeGuaranteeEndsNet` closes any network of mixed cell classes, but ASSUMES each link's
departure bounds (`LinkSpec.H_SND`, `H_RCV`, `H_RST_EARLY`) and the network's wire spacing
(`NetW.H_SP`) as inequalities between edge times. This file shows that for a chain of
links (source, `N` links, sink) all of them are CONSEQUENCES of `Chain`/`ChainT` (gate
relations, H_TIMES, constant rows), by the path argument around each handshake cycle that
Bnet's `c_snd`, `c_rcv`, `c_hspF`, `c_hspB` carry out (node → wire → neighbour LUT →
wire back: `Es = vl m + lo m + wl m`, `Ea = wl (m+1) + lo (m+2) + vl (m+1)`).

## Assumed / proved / NOT covered

**Assumed:** `Chain D`, `ChainT D` (Bnet's hypotheses; the end cells as contracts).

**Proved:** `chain_as_net`: the chain as a `GD` network over `Fin (N+2)` (`gD`) satisfies
`NetW` (H_SP derived), every link cell is a `LinkSpec` with the derived slacks
(`chain_linkSpec`), the ends are `Contract` cells (`chain_src`, `chain_snk`, their H_WAIT
from `SRC_WAIT`/`SNK_WAIT`), so `mixed_closed` applies. `net_solution`: with
`EdgeTimes.chain_b`, all of this holds on a constructed run for every delay assignment in
the bands (non-vacuous for every `N`, witness `EdgeTimes.chain_solution_witness`).

**NOT covered:** mixed networks (forks, joins, steers): their departure bounds would need
the same path argument through the C-element and steer specs; not done. Core Lean only.
-/

namespace Formal.Cells.EdgeTimesNet
open Formal.Cells
open Formal.Cells.WinFifoCausal (nt Stage Env1 Timing1 cph τs)
open Formal.Cells.LutFbBridge (Phases)
open Formal.Cells.LutFbBridge2Env (Wire ε ash)
open Formal.Cells.AssumeGuaranteeLinks
open Formal.Cells.AssumeGuaranteeEnds (GPin gE GA)
open Formal.Cells.AssumeGuaranteeEndsNet (GD LinkSpec Contract NetW Proved mixed_closed
  link_spec_env1)

/-! ## A link chain as an `AssumeGuaranteeEndsNet` network -/

variable (D : ChainData)

/-- Cell `i` of the chain as an index of `Fin (N + 2)` (clamped). -/
def cf (i : Nat) : Fin (D.N + 2) := ⟨min i (D.N + 1), by omega⟩

theorem cf_val {i : Nat} (h : i ≤ D.N + 1) : (cf D i).val = i := by
  show min i (D.N + 1) = i; omega

/-- Link `m+1`'s request pin (from cell `m`, reads segments `≤ k`). -/
def rpin (m : Nat) : GPin (Fin (D.N + 2)) := ⟨cf D m, D.req (m + 1), D.wl m, D.wh m, fun k => k + 1⟩
/-- Cell `i`'s acknowledge pin (from cell `i+1`, reads segments `< k`). -/
def apin (i : Nat) : GPin (Fin (D.N + 2)) := ⟨cf D (i + 1), D.ack i, D.vl i, D.vh i, fun k => k⟩

/-- The pins of each cell: source: acknowledge; link: request, acknowledge; sink: request. -/
def pins (c : Fin (D.N + 2)) : List (GPin (Fin (D.N + 2))) :=
  if c.val = 0 then [apin D 0]
  else if c.val ≤ D.N then [rpin D (c.val - 1), apin D c.val]
  else [rpin D D.N]

/-- The chain as a `GD` network over `Fin (N + 2)`. -/
def gD : GD (Fin (D.N + 2)) where
  O c := D.O c.val
  τ c := D.τ c.val
  lo c := D.lo c.val
  hi c := D.hi c.val
  fl c := D.fl c.val
  fh c := D.fh c.val
  qp c := D.qp c.val
  rst := D.rst
  R := D.R
  pins := pins D

theorem gE_r (m : Nat) (hm : m ≤ D.N) : gE (gD D).τ (rpin D m) = D.εF m := by
  funext j; show ε (D.req (m + 1)) (D.wl m) (D.wh m) (D.τ (cf D m).val) j = _
  rw [cf_val D (by omega)]; rfl

theorem gE_a (i : Nat) (hi : i ≤ D.N) : gE (gD D).τ (apin D i) = D.εB i := by
  funext j; show ε (D.ack i) (D.vl i) (D.vh i) (D.τ (cf D (i + 1)).val) j = _
  rw [cf_val D (by omega)]; rfl

theorem pins_src (c : Fin (D.N + 2)) (h : c.val = 0) : pins D c = [apin D 0] := by
  unfold pins; rw [if_pos h]

theorem pins_link (c : Fin (D.N + 2)) (m : Nat) (h : c.val = m + 1) (hm : m < D.N) :
    pins D c = [rpin D m, apin D (m + 1)] := by
  unfold pins; rw [if_neg (by omega), if_pos (by omega), h]; rfl

theorem pins_snk (c : Fin (D.N + 2)) (h : c.val = D.N + 1) : pins D c = [rpin D D.N] := by
  unfold pins; rw [if_neg (by omega), if_neg (by omega)]

section derived
variable {D} (C : Chain D) (T : ChainT D)
include C T
set_option linter.unusedSectionVars false

theorem wire_r (m : Nat) (hm : m ≤ D.N) :
    Wire (rpin D m).wl (rpin D m).wh (D.O (rpin D m).drv.val) (rpin D m).P := by
  show Wire (D.wl m) (D.wh m) (D.O (cf D m).val) (D.req (m + 1))
  rw [cf_val D (by omega)]; exact C.H_WF m hm

theorem wire_a (i : Nat) (hi : i ≤ D.N) :
    Wire (apin D i).wl (apin D i).wh (D.O (apin D i).drv.val) (apin D i).P := by
  show Wire (D.vl i) (D.vh i) (D.O (cf D (i + 1)).val) (D.ack i)
  rw [cf_val D (by omega)]; exact C.H_WB i hi

theorem sp_r (m : Nat) (hm : m ≤ D.N) (j : Nat) :
    (rpin D m).wh ≤ (gD D).τ (rpin D m).drv j ∧
      (gD D).τ (rpin D m).drv j + (rpin D m).wh < (gD D).τ (rpin D m).drv (j + 1) + (rpin D m).wl := by
  show D.wh m ≤ D.τ (cf D m).val j ∧ D.τ (cf D m).val j + D.wh m < D.τ (cf D m).val (j + 1) + D.wl m
  rw [cf_val D (by omega)]; exact c_hspF C T m hm j

theorem sp_a (i : Nat) (hi : i ≤ D.N) (j : Nat) :
    (apin D i).wh ≤ (gD D).τ (apin D i).drv j ∧
      (gD D).τ (apin D i).drv j + (apin D i).wh < (gD D).τ (apin D i).drv (j + 1) + (apin D i).wl := by
  show D.vh i ≤ D.τ (cf D (i + 1)).val j ∧
    D.τ (cf D (i + 1)).val j + D.vh i < D.τ (cf D (i + 1)).val (j + 1) + D.vl i
  rw [cf_val D (by omega)]; exact c_hspB C T i hi j

/-- **The network-wide facts, DERIVED** for the chain, including the wire spacing H_SP
(`AssumeGuaranteeEndsNet` assumes it as an edge-time inequality). -/
theorem chain_netW : NetW (gD D) where
  H_RST := C.H_RST
  H_WIRE c p hp := by
    have hc := c.isLt
    show Wire p.wl p.wh (D.O p.drv.val) p.P
    by_cases h0 : c.val = 0
    · rw [show (gD D).pins c = _ from pins_src D c h0] at hp
      simp only [List.mem_singleton] at hp; subst hp; exact wire_a C T 0 (by omega)
    · by_cases h1 : c.val ≤ D.N
      · rw [show (gD D).pins c = _ from pins_link D c (c.val - 1) (by omega) (by omega)] at hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact wire_r C T _ (by omega)
        · exact wire_a C T _ (by omega)
      · rw [show (gD D).pins c = _ from pins_snk D c (by omega)] at hp
        simp only [List.mem_singleton] at hp; subst hp; exact wire_r C T _ (Nat.le_refl _)
  H_LUT_POS c := C.H_LUT_POS c.val (by have := c.isLt; omega)
  H_SP c p hp j := by
    have hc := c.isLt
    by_cases h0 : c.val = 0
    · rw [show (gD D).pins c = _ from pins_src D c h0] at hp
      simp only [List.mem_singleton] at hp; subst hp; exact sp_a C T 0 (by omega) j
    · by_cases h1 : c.val ≤ D.N
      · rw [show (gD D).pins c = _ from pins_link D c (c.val - 1) (by omega) (by omega)] at hp
        simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl
        · exact sp_r C T _ (by omega) j
        · exact sp_a C T _ (by omega) j
      · rw [show (gD D).pins c = _ from pins_snk D c (by omega)] at hp
        simp only [List.mem_singleton] at hp; subst hp; exact sp_r C T _ (Nat.le_refl _) j

/-- **Every link of the chain is a `LinkSpec` cell, with its departure bounds `H_SND`,
`H_RCV`, `H_RST_EARLY` DERIVED** (slacks `Es = vl m + lo m + wl m`,
`Ea = wl (m+1) + lo (m+2) + vl (m+1)`: the handshake cycle through each neighbour). -/
theorem chain_linkSpec (c : Fin (D.N + 2)) (m : Nat) (hc : c.val = m + 1) (hm : m < D.N) :
    LinkSpec (gD D) c (rpin D m) (apin D (m + 1)) (D.Es m) (D.Ea m) where
  H_PINS := pins_link D c m hc hm
  H_NBR := rfl
  H_NBA := rfl
  H_STAGE := by
    show Stage (D.req (m + 1)) (D.ack (m + 1)) D.rst (D.O c.val) (D.qp c.val) (D.lo c.val)
      (D.hi c.val) (D.fl c.val) (D.fh c.val)
    rw [hc]; exact C.H_STAGE m hm
  H_PWR t ht := by
    show D.O c.val t = false; have ht' : t < D.hi c.val := ht
    rw [hc] at ht' ⊢; exact C.H_PWR m hm t ht'
  H_TIMES j := by
    rw [gE_r D m (by omega), gE_a D (m + 1) (by omega)]
    show D.τ c.val j = τs (D.O c.val) (D.lo c.val) (D.hi c.val) (D.ρL m) (D.αL m) j
    rw [hc]; exact C.H_TIMES m hm j
  H_RST_EARLY := by rw [gE_r D m (by omega)]; exact c_early C m hm
  H_SND j := by
    rw [gE_r D m (by omega)]
    show D.τ c.val j + _ ≤ _
    rw [hc, C.H_TIMES m hm j]; exact c_snd C m hm j
  H_RCV j := by
    rw [gE_a D (m + 1) (by omega)]
    show D.τ c.val j + _ ≤ _
    rw [hc, C.H_TIMES m hm j]; exact c_rcv C m hm j
  H_T := by
    show Timing1 (D.lo c.val) (D.hi c.val) (D.fh c.val) D.R (D.Es m) (D.Ea m)
    rw [hc]; exact (chain_env1 C T m hm).2

/-- The source as a `Contract` cell (its segments, and its H_WAIT from `SRC_WAIT`). -/
theorem chain_src (c : Fin (D.N + 2)) (h : c.val = 0) : Contract (gD D) c := by
  refine ⟨fun k _ => ?_, fun p hp k k' hk => ?_⟩
  · show SegK (D.O c.val) (D.τ c.val) k
    rw [h]; exact segK_of_phases (chain_nodes C T 0 (by omega)) k
  · rw [show (gD D).pins c = _ from pins_src D c h] at hp
    simp only [List.mem_singleton] at hp; subst hp
    have hk' : k' < k := hk
    rw [gE_a D 0 (by omega)]
    show D.εB 0 k' + D.lo c.val ≤ D.τ c.val k
    rw [h]
    have := C.SRC_WAIT k'; have := c_mono C 0 (by omega) (show k' + 1 ≤ k by omega); omega

/-- The sink as a `Contract` cell. -/
theorem chain_snk (c : Fin (D.N + 2)) (h : c.val = D.N + 1) : Contract (gD D) c := by
  refine ⟨fun k _ => ?_, fun p hp k k' hk => ?_⟩
  · show SegK (D.O c.val) (D.τ c.val) k
    rw [h]; exact segK_of_phases (chain_nodes C T (D.N + 1) (Nat.le_refl _)) k
  · rw [show (gD D).pins c = _ from pins_snk D c h] at hp
    simp only [List.mem_singleton] at hp; subst hp
    have hk' : k' < k + 1 := hk
    rw [gE_r D D.N (Nat.le_refl _)]
    show D.εF D.N k' + D.lo c.val ≤ D.τ c.val k
    rw [h]
    have := C.SNK_WAIT k'; have := c_mono C (D.N + 1) (Nat.le_refl _) (show k' ≤ k by omega)
    omega

theorem chain_cls (c : Fin (D.N + 2)) : Proved (gD D) c ∨ Contract (gD D) c := by
  have hc := c.isLt
  by_cases h0 : c.val = 0
  · exact Or.inr (chain_src C T c h0)
  · by_cases h1 : c.val ≤ D.N
    · exact Or.inl (Or.inl ⟨_, _, _, _, chain_linkSpec C T c (c.val - 1) (by omega) (by omega)⟩)
    · exact Or.inr (chain_snk C T c (by omega))

/-- **Headline (goal 3).** For a link chain, every hypothesis of `AssumeGuaranteeEndsNet`'s
network rule that it states as an edge-time inequality is DERIVED from `Chain`/`ChainT`
(gate relations, H_TIMES, constant rows): the wire spacing H_SP (`NetW`), and each link's
departure bounds (`LinkSpec`); the two ends are `Contract` cells. So `mixed_closed` applies
and gives every node's clean step shape. -/
theorem chain_as_net :
    NetW (gD D) ∧ (∀ c, Proved (gD D) c ∨ Contract (gD D) c) ∧
    (∀ (c : Fin (D.N + 2)) (m : Nat), c.val = m + 1 → m < D.N →
      LinkSpec (gD D) c (rpin D m) (apin D (m + 1)) (D.Es m) (D.Ea m)) ∧
    (∀ c, Phases ((gD D).O c) ((gD D).τ c)) :=
  ⟨chain_netW C T, chain_cls C T, fun c m hc hm => chain_linkSpec C T c m hc hm,
    mixed_closed (gD D) (chain_netW C T) (chain_cls C T)⟩

end derived

/-- **Goals (1) + (3) together, non-vacuous for every delay assignment**: for every chain
length and every realised delay assignment inside the bands meeting the band rows, the run
of `EdgeTimes` is a network on which all of `AssumeGuaranteeEndsNet`'s edge-time hypotheses
hold, derived. -/
theorem net_solution (P : EdgeTimes.Dly) (B : EdgeTimes.Band P) (T : ChainT (EdgeTimes.bD P)) :
    NetW (gD (EdgeTimes.bD P)) ∧
    (∀ c, Proved (gD (EdgeTimes.bD P)) c ∨ Contract (gD (EdgeTimes.bD P)) c) ∧
    (∀ (c : Fin (P.N + 2)) (m : Nat), c.val = m + 1 → m < P.N →
      LinkSpec (gD (EdgeTimes.bD P)) c (rpin (EdgeTimes.bD P) m) (apin (EdgeTimes.bD P) (m + 1))
        ((EdgeTimes.bD P).Es m) ((EdgeTimes.bD P).Ea m)) :=
  let h := chain_as_net (EdgeTimes.chain_b B T) T
  ⟨h.1, h.2.1, h.2.2.1⟩

end Formal.Cells.EdgeTimesNet
