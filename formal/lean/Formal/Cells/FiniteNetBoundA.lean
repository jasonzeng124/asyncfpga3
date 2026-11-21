import Formal.Cells.FiniteNetBoundM
import Formal.Cells.FiniteNetComb

/-!
# Probe Belab3 (shard B): the driver-bound gate-level network with the ARBITERS gate-modelled

`FiniteNetBoundMCensus`: 28 of the 39 link sides still unbound under `FiniteNetBoundM` end at an
`amerge` (gcd_hw's `bd_arbiter`). Here each arbiter is its four real cells (`cells/rtl/bd_arb.v`,
C's generated netlist `Formal.Gen.Cells.bd_arbiter`):
* `ustate` O6 `q` (feedback LUT of r1, r2, q, rst, A0) and O5 `R0` (drives `z.req`), and
  `ugrant` O5/O6 `g1`/`g2`: `FiniteNetComb.FCombSpec`, i.e. the real LUT of its bound pins plus
  ONE named race hypothesis per cell, `H_EXC_CLEAN` (clean pins give a clean excitation): this
  is where arbitration lives (`notes/B-arb-bind-plan.md`; `ArbAMergeRunWit.sep_cex_run` shows
  it is not automatic);
* `ua1`/`ua2` (drive `x.ack`/`y.ack`): the C-element of the grant and `z_ack`, with `z_ack`
  read at the tokens that client won (`FMuxASpec`, as a mux acknowledge).
Drivers: `reqSrcA` / `ackSrcA` are `FiniteNetBoundM`'s plus the arbiter (`z.req <- R0`,
`x.ack <- ua1`, `y.ack <- ua2`), followed through the same wires.

## Assumed / proved / NOT covered

**Proved:** `bound_censusA` (kernel): 164 of 175 links bound on both sides; `FGcdNetOKBA.toOKBM`
(the arbiter-extended hypothesis implies the mux-extended one: the bindings agree wherever
`FiniteNetBoundM` names a driver, and the arbiter cells' contracts follow from their specs);
`gcd_hw_safe_fin_netBA`: C's gcd_hw safety under `FGcdNetOKBA` plus C's H_OTHER, H_BUNDLE,
H_CM_FORCED.
**Assumed:** `FGcdNetOKBM`'s fields with the extended bindings, the arbiter cells' specs
(including `H_EXC_CLEAN` for `ustate`'s two outputs and `ugrant`'s two), their pins bound.
**NOT covered:** a joint witness (Python evidence only: `tools-B/bwit/bsim3.py`); C's H_OTHER.
Core Lean only.
-/

namespace Formal.Cells.FiniteNetBoundA
open Formal.Cells
open Formal.Cells.FiniteNet
open Formal.Cells.FiniteNetBound
open Formal.Cells.FiniteNetBoundM
open Formal.Cells.FiniteNetComb (FCombSpec fcomb_spec_cell)
open Formal.Cells.AssumeGuaranteeMuxNFin
open Formal.Cells.LutFbBridge2Env (Wire isLink)
open Formal.Cells.AssumeGuaranteeEnds (GPin GC2)
open Formal.Cells.AssumeGuaranteeEndsNet (GD)
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe
open Formal.Cells.AssumeGuaranteeEndsCap (forkOuts joinIns steerIn d0 LinkOut)
open Formal.Net.Ops.Gen (genF)
open Formal.Gen Formal.Gen.Cells

/-! ## 1. The elaboration and the drivers -/

structure FGcdNetA extends FGcdNetM where
  aq : Fin NO → ι
  aR : Fin NO → ι
  ag : Fin NO → Bool → ι
  aa : Fin NO → Bool → ι

inductive DKA
  | base (d : DKM)
  | aR (o : Fin NO)
  | aA (o : Fin NO) (b : Bool)
  deriving DecidableEq, Repr

def DKA.cell (N : FGcdNetA) : DKA → N.ι
  | .base d => d.cell N.toFGcdNetM
  | .aR o => N.aR o
  | .aA o b => N.aa o b

/-- An arbiter's request output, followed back through tied forks and 1-input joins. -/
def arbReq : Nat → Fin NC → Option DKA
  | 0, _ => none
  | F + 1, c =>
    let o := prodOf c
    match opAt o with
    | .forkG i os => if 2 ≤ os.length ∧ os.length ≤ 4 then arbReq F i else none
    | .forkH i os _ _ _ _ => if 2 ≤ os.length ∧ os.length ≤ 4 then arbReq F i else none
    | .join ins _ _ _ _ => if ins.length = 1 then arbReq F (ins.getD 0 d0) else none
    | .bjoin ins _ _ _ => if ins.length = 1 then arbReq F (ins.getD 0 d0) else none
    | .amerge _ _ _ _ => some (.aR o)
    | _ => none

/-- An arbiter's input acknowledge, followed forward through 1- and 2-input joins and a mux's
control acknowledge. -/
def arbAck : Nat → Fin NC → Option DKA
  | 0, _ => none
  | F + 1, c =>
    let o := consOf c
    match opAt o with
    | .join ins z _ _ _ => if ins.length = 2 ∨ ins.length = 1 then arbAck F z else none
    | .bjoin ins z _ _ => if ins.length = 2 ∨ ins.length = 1 then arbAck F z else none
    | .mux cc _ _ z _ => if c = cc then arbAck F z else none
    | .amerge _ y _ _ => some (.aA o (decide (c = y)))
    | _ => none

def reqSrcA (F : Nat) (c : Fin NC) : Option DKA := ((reqSrcM F c).map .base).orElse fun _ => arbReq F c
def ackSrcA (F : Nat) (c : Fin NC) : Option DKA := ((ackSrcM F c).map .base).orElse fun _ => arbAck F c

/-- The arbiter's cells. -/
def ArbCell (N : FGcdNetA) (c : N.ι) : Prop :=
  ∃ o x y z w, opAt o = .amerge x y z w ∧
    (c = N.aq o ∨ c = N.aR o ∨ ∃ b, c = N.ag o b ∨ c = N.aa o b)

def FTiedA (N : FGcdNetA) (c : N.ι) : Prop := FTiedM N.toFGcdNetM c ∨ ArbCell N c

theorem arbReq_tied (N : FGcdNetA) : ∀ (F : Nat) (c : Fin NC) (d : DKA),
    arbReq F c = some d → ArbCell N (d.cell N)
  | 0, _, _, h => by simp [arbReq] at h
  | F + 1, c, d, h => by
    simp only [arbReq] at h
    split at h
    · split at h
      · exact arbReq_tied N F _ d h
      · cases h
    · split at h
      · exact arbReq_tied N F _ d h
      · cases h
    · split at h
      · exact arbReq_tied N F _ d h
      · cases h
    · split at h
      · exact arbReq_tied N F _ d h
      · cases h
    · rename_i x y z w e; cases h
      exact ⟨prodOf c, x, y, z, w, e, Or.inr (Or.inl rfl)⟩
    · cases h

theorem arbAck_tied (N : FGcdNetA) : ∀ (F : Nat) (c : Fin NC) (d : DKA),
    arbAck F c = some d → ArbCell N (d.cell N)
  | 0, _, _, h => by simp [arbAck] at h
  | F + 1, c, d, h => by
    simp only [arbAck] at h
    split at h
    · split at h
      · exact arbAck_tied N F _ d h
      · cases h
    · split at h
      · exact arbAck_tied N F _ d h
      · cases h
    · split at h
      · exact arbAck_tied N F _ d h
      · cases h
    · rename_i x y z w e; cases h
      exact ⟨consOf c, x, y, z, w, e, Or.inr (Or.inr ⟨_, Or.inr rfl⟩)⟩
    · cases h

theorem reqSrcA_tied (N : FGcdNetA) (F : Nat) (c : Fin NC) (d : DKA)
    (h : reqSrcA F c = some d) : FTiedA N (d.cell N) := by
  unfold reqSrcA at h
  cases hm : reqSrcM F c with
  | some d' =>
    rw [hm] at h; cases h
    exact Or.inl (reqSrcM_tied N.toFGcdNetM F c d' hm)
  | none =>
    rw [hm] at h
    exact Or.inr (arbReq_tied N F c d h)

theorem ackSrcA_tied (N : FGcdNetA) (F : Nat) (c : Fin NC) (d : DKA)
    (h : ackSrcA F c = some d) : FTiedA N (d.cell N) := by
  unfold ackSrcA at h
  cases hm : ackSrcM F c with
  | some d' =>
    rw [hm] at h; cases h
    exact Or.inl (ackSrcM_tied N.toFGcdNetM F c d' hm)
  | none =>
    rw [hm] at h
    exact Or.inr (arbAck_tied N F c d h)

/-! ## 2. The hypothesis -/

def BoundRA (N : FGcdNetA) (c : Fin NC) (p : GPin N.ι) : Prop :=
  ∀ d, reqSrcA FU c = some d → p.drv = d.cell N

def BoundAA (N : FGcdNetA) (c : Fin NC) (p : GPin N.ι) : Prop :=
  ∀ d, ackSrcA FU c = some d → p.drv = d.cell N

theorem boundRM_of {N : FGcdNetA} {c : Fin NC} {p : GPin N.ι} (h : BoundRA N c p) :
    BoundRM N.toFGcdNetM c p := by
  intro d hd
  have : reqSrcA FU c = some (.base d) := by unfold reqSrcA; rw [hd]; rfl
  exact h _ this

theorem boundAM_of {N : FGcdNetA} {c : Fin NC} {p : GPin N.ι} (h : BoundAA N c p) :
    BoundAM N.toFGcdNetM c p := by
  intro d hd
  have : ackSrcA FU c = some (.base d) := by unfold ackSrcA; rw [hd]; rfl
  exact h _ this

/-- `ustate` O6 (`q`), O5 (`R0`); `ugrant` O5 (`g1`), O6 (`g2`): the generated LUTs. -/
def qF : List Bool → Bool → Bool
  | [r1, r2, q, a0], rst => genF bd_arbiter "ustate" .O6 ["r1", "r2", "q", "rst", "A0"] [r1, r2, q, rst, a0]
  | _, _ => false
def r0F : List Bool → Bool → Bool
  | [r1, r2, q, a0], rst => genF bd_arbiter "ustate" .O5 ["r1", "r2", "q", "rst", "A0"] [r1, r2, q, rst, a0]
  | _, _ => false
def gF (b : Bool) : List Bool → Bool → Bool
  | [r1, r2, q], _ => genF bd_arbiter "ugrant" (if b then .O6 else .O5) ["r1", "r2", "q"] [r1, r2, q]
  | _, _ => false

/-- The pin lists: `[r1, r2, q, A0]` for `ustate`, `[r1, r2, q]` for `ugrant`. -/
def ArbPins (N : FGcdNetA) (ch : Fin NC → Chan) (o : Fin NO) (x y z : Fin NC)
    (ps : List (GPin N.ι)) (k : Nat) : Prop :=
  ∃ p1 p2 pq, (ps = [p1, p2, pq] ∨ ∃ pa, ps = [p1, p2, pq, pa] ∧ pa.P = (ch z).ack ∧
      BoundAA N z pa) ∧
    p1.P = (ch x).req ∧ BoundRA N x p1 ∧ p2.P = (ch y).req ∧ BoundRA N y p2 ∧ pq.drv = N.aq o ∧
    ps.length = k

/-- **The driver-bound hypotheses, muxes and arbiters gate-modelled.** -/
structure FGcdNetOKBA (ch : Fin NC → Chan) (N : FGcdNetA) (L : N.ι → Nat → Prop)
    (n : N.ι → Nat) : Prop where
  NW : FNetW N.D L
  H_FIN : ∀ c j, L c j ↔ j < n c
  H_LINK : ∀ o i o', opAt o = .link i o' → ∃ rp ap Es Ea, FLinkSpec N.D L (N.lk o) rp ap Es Ea ∧
    rp.P = (ch i).req ∧ ap.P = (ch o').ack ∧ LinkOut N.D (N.lk o) (ch i) (ch o') Es Ea ∧
    BoundRA N i rp ∧ BoundAA N o' ap
  H_FORK : ∀ o os, forkOuts (opAt o) = some os → 2 ≤ os.length → os.length ≤ 4 →
    FCelTieB N.toFGcdNet L (N.fa o) os (fun c => (ch c).ack) (BoundAA N)
  H_JOIN : ∀ o ins, joinIns (opAt o) = some ins → ins.length = 2 →
    FCelTieB N.toFGcdNet L (N.jr o) ins (fun c => (ch c).req) (BoundRA N)
  H_STEER : ∀ o j, steerIn (opAt o) = some j → ∀ b, ∃ rp s σ κ,
    FSteerSpec N.D L (N.sb o b) rp b s σ κ ∧ rp.P = (ch j).req ∧ BoundRA N j rp ∧
    s = fun t => (ch j).dat t % 2 == 1
  H_SOR : ∀ o j t f, stJ (opAt o) = some (j, t, f) → ∃ ap σ κ,
    FOrSpec N.D L (N.ao o) (fun a0 a1 => genF bd_steer "uack" .O ["ack0", "ack1"] [a0, a1])
      ap σ κ ∧ ∀ b, (ap b).P = (ch (brC t f b)).ack ∧ BoundAA N (brC t f b) (ap b)
  H_MUXJ : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ b, ∃ xp cp s σ κ E,
    FMuxJSpec N.D L (N.mj o b) xp cp b s σ κ E ∧ xp.P = (ch (if b then y else x)).req ∧
    cp.P = (ch cc).req ∧ BoundRA N (if b then y else x) xp ∧ BoundRA N cc cp ∧
    s = fun t => (ch cc).dat t % 2 == 1
  H_MUXA : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ b, ∃ ap zp κ E,
    FMuxASpec N.D L (N.ma o b) ap zp κ E ∧ ap.drv = N.mj o b ∧ zp.P = (ch z).ack ∧
    BoundAA N z zp
  H_MUXO : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∃ ap σ κ,
    FOrSpec N.D L (N.mo o) uorF ap σ κ ∧ ∀ b, (ap b).drv = N.mj o b
  H_MUXD : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ i : Fin 2, ∃ p,
    FBufSpec N.D L (N.md o i) p ∧ p.drv = (if i.val = 0 then N.mo o else N.md o 0)
  /-- **The arbiter's `ustate`**: `q` and `R0`, real LUT of the bound pins, H_EXC_CLEAN. -/
  H_ARBQ : ∀ o x y z w, opAt o = .amerge x y z w → ∃ ps e Le,
    FCombSpec N.D L (N.aq o) qF ps e Le ∧ ArbPins N ch o x y z ps 4
  H_ARBR : ∀ o x y z w, opAt o = .amerge x y z w → ∃ ps e Le,
    FCombSpec N.D L (N.aR o) r0F ps e Le ∧ ArbPins N ch o x y z ps 4
  /-- **The arbiter's `ugrant`**: `g1` (`b = false`), `g2` (`b = true`). -/
  H_ARBG : ∀ o x y z w, opAt o = .amerge x y z w → ∀ b, ∃ ps e Le,
    FCombSpec N.D L (N.ag o b) (gF b) ps e Le ∧ ArbPins N ch o x y z ps 3
  /-- **The arbiter's `ua1`/`ua2`**: `C(g, A0)`, `A0 = z_ack` read at the winner's tokens
  (`κ`, as a mux acknowledge: `z_ack` carries both clients' tokens). -/
  H_ARBA : ∀ o x y z w, opAt o = .amerge x y z w → ∀ b, ∃ ap zp κ E,
    FMuxASpec N.D L (N.aa o b) ap zp κ E ∧ ap.drv = N.ag o b ∧ zp.P = (ch z).ack ∧
    BoundAA N z zp
  H_REST : ∀ c, ¬ FTiedA N c → FCellOK N.D L c
  H_DRV_FORK : ∀ o os i, forkOuts (opAt o) = some os → 2 ≤ os.length → os.length ≤ 4 →
    forkIn (opAt o) = some i → ∃ wl wh, Wire wl wh (N.D.O (N.fa o)) (ch i).ack
  H_DRV_JOIN : ∀ o ins z, joinIns (opAt o) = some ins → ins.length = 2 →
    joinOut (opAt o) = some z → ∃ wl wh, Wire wl wh (N.D.O (N.jr o)) (ch z).req
  H_DRV_STEER : ∀ o j t f, stJ (opAt o) = some (j, t, f) →
    (∀ b, ∃ wl wh, Wire wl wh (N.D.O (N.sb o b)) (ch (brC t f b)).req) ∧
    ∃ wl wh, Wire wl wh (N.D.O (N.ao o)) (ch j).ack
  H_DRV_MUX : ∀ o cc x y z mw, opAt o = .mux cc x y z mw →
    (∃ wl wh, Wire wl wh (N.D.O (N.md o 1)) (ch z).req) ∧
    ∀ b, ∃ wl wh, Wire wl wh (N.D.O (N.ma o b)) (ch (if b then y else x)).ack
  H_DRV_ARB : ∀ o x y z w, opAt o = .amerge x y z w →
    (∃ wl wh, Wire wl wh (N.D.O (N.aR o)) (ch z).req) ∧
    ∀ b, ∃ wl wh, Wire wl wh (N.D.O (N.aa o b)) (ch (if b then y else x)).ack

theorem tieB_mono {N : FGcdNet} {L : N.ι → Nat → Prop} {c : N.ι} {cs : List (Fin NC)}
    {sel : Fin NC → Nat → Bool} {bd bd' : Fin NC → GPin N.ι → Prop}
    (hb : ∀ c p, bd c p → bd' c p) (h : FCelTieB N L c cs sel bd) : FCelTieB N L c cs sel bd' := by
  rcases h with ⟨l, pv, E, S, hp⟩ | ⟨l, pv, E, S, hp⟩ | ⟨l, pv, E, S, hp⟩
  · exact Or.inl ⟨l, pv, E, S, fun i => ⟨(hp i).1, hb _ _ (hp i).2⟩⟩
  · exact Or.inr (Or.inl ⟨l, pv, E, S, fun i => ⟨(hp i).1, hb _ _ (hp i).2⟩⟩)
  · exact Or.inr (Or.inr ⟨l, pv, E, S, fun i => ⟨(hp i).1, hb _ _ (hp i).2⟩⟩)

/-- **The arbiter-extended hypothesis implies the mux-extended one.** -/
theorem FGcdNetOKBA.toOKBM {ch : Fin NC → Chan} {N : FGcdNetA} {L : N.ι → Nat → Prop}
    {n : N.ι → Nat} (H : FGcdNetOKBA ch N L n) : FGcdNetOKBM ch N.toFGcdNetM L n where
  NW := H.NW
  H_FIN := H.H_FIN
  H_LINK := fun o i o' h => by
    obtain ⟨rp, ap, Es, Ea, S, e1, e2, lo, br, ba⟩ := H.H_LINK o i o' h
    exact ⟨rp, ap, Es, Ea, S, e1, e2, lo, boundRM_of br, boundAM_of ba⟩
  H_FORK := fun o os h h1 h2 => tieB_mono (fun _ _ hb => boundAM_of hb) (H.H_FORK o os h h1 h2)
  H_JOIN := fun o ins h h1 => tieB_mono (fun _ _ hb => boundRM_of hb) (H.H_JOIN o ins h h1)
  H_STEER := fun o j h b => by
    obtain ⟨rp, s, σ, κ, S, e, br, hs⟩ := H.H_STEER o j h b
    exact ⟨rp, s, σ, κ, S, e, boundRM_of br, hs⟩
  H_SOR := fun o j t f h => by
    obtain ⟨ap, σ, κ, S, hb⟩ := H.H_SOR o j t f h
    exact ⟨ap, σ, κ, S, fun b => ⟨(hb b).1, boundAM_of (hb b).2⟩⟩
  H_MUXJ := fun o cc x y z mw h b => by
    obtain ⟨xp, cp, s, σ, κ, E, S, e1, e2, b1, b2, hs⟩ := H.H_MUXJ o cc x y z mw h b
    exact ⟨xp, cp, s, σ, κ, E, S, e1, e2, boundRM_of b1, boundRM_of b2, hs⟩
  H_MUXA := fun o cc x y z mw h b => by
    obtain ⟨ap, zp, κ, E, S, e1, e2, bz⟩ := H.H_MUXA o cc x y z mw h b
    exact ⟨ap, zp, κ, E, S, e1, e2, boundAM_of bz⟩
  H_MUXO := H.H_MUXO
  H_MUXD := H.H_MUXD
  H_REST := fun c hc => by
    by_cases ha : ArbCell N c
    · obtain ⟨o, x, y, z, w, ho, hq | hr | ⟨b, hg | haa⟩⟩ := ha
      · subst hq; obtain ⟨ps, e, Le, S, _⟩ := H.H_ARBQ o x y z w ho; exact fcomb_spec_cell S
      · subst hr; obtain ⟨ps, e, Le, S, _⟩ := H.H_ARBR o x y z w ho; exact fcomb_spec_cell S
      · subst hg; obtain ⟨ps, e, Le, S, _⟩ := H.H_ARBG o x y z w ho b; exact fcomb_spec_cell S
      · subst haa; obtain ⟨ap, zp, κ, E, S, _⟩ := H.H_ARBA o x y z w ho b
        exact fmuxa_spec_cell H.NW S
    · exact H.H_REST c (fun h => h.elim hc ha)
  H_DRV_FORK := H.H_DRV_FORK
  H_DRV_JOIN := H.H_DRV_JOIN
  H_DRV_STEER := H.H_DRV_STEER
  H_DRV_MUX := H.H_DRV_MUX

/-! ## 3. Census -/

def linkSidesA (F : Nat) : List (Bool × Bool) :=
  (List.finRange NO).filterMap fun o => match opAt o with
    | .link i o' => some ((reqSrcA F i).isSome, (ackSrcA F o').isSome)
    | _ => none

def nBothA : Nat := ((linkSidesA FU).filter fun p => p.1 && p.2).length

set_option maxRecDepth 100000

theorem bound_censusA : nBothA = 164 := by decide +kernel

/-! ## 4. The capstone, arbiters gate-modelled -/

/-- **End to end, runs that stop, drivers bound, muxes and arbiters gate-modelled.** -/
theorem gcd_hw_safe_fin_netBA (a b : Nat) (ch : Fin NC → Chan) (N : FGcdNetA)
    (L : N.ι → Nat → Prop) (n : N.ι → Nat) (H : FGcdNetOKBA ch N L n)
    (H_OTHER : ∀ o : Fin NO, isLink (opAt o) = false → Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_CM_FORCED : ∃ y, Good a b y ∧ ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) :=
  gcd_hw_safe_fin_netBM a b ch N.toFGcdNetM L n H.toOKBM H_OTHER H_BUNDLE H_CM_FORCED

end Formal.Cells.FiniteNetBoundA
