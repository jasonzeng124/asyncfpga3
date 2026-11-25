import Formal.Cells.FiniteNetBoundA

/-!
# Probe Belab4 (shard B): the driver-bound gate-level network with the FORK TREES gate-modelled

`FiniteNetBoundMCensus`: 6 of the 11 link sides still unbound under `FiniteNetBoundA` are
acknowledge sides ending at a fork with 5 or 6 outputs (gcd_hw's `forkH5`, `forkH6`). Such a
fork's acknowledge is `bd_ctree #(N)` (`cells/rtl/bd_ce.v`): chunks of four, then a top node,
so N = 5 is `C2(C4(a0..a3), a4)` and N = 6 is `C2(C4(a0..a3), C2(a4, a5))`, the shapes of
`AssumeGuaranteeMuxNFin.FTree5`/`FTree6`. Here each such fork is its real C-element cells:
* the top `C2` (`tr o`) drives the fork input's acknowledge;
* chunk node 0 (`tn o 0`, `C4` of leaves 0..3) and, for N = 6, chunk node 1 (`tn o 1`, `C2` of
  leaves 4, 5), wired to the top node;
* every leaf pin is the acknowledge of that fork output, bound to its driver.
Drivers: `ackSrcT` is `FiniteNetBoundA.ackSrcA` or else the top node, followed through the same
wires (1- and 2-input joins, a mux's control acknowledge).

## Assumed / proved / NOT covered

**Proved:** `bound_censusT` (kernel): 170 of 175 links bound on both sides (the 5 left: muxn 4
acknowledge sides, the source 1 request side); `FGcdNetOKBT.toOKBA` (the tree-extended
hypothesis implies the arbiter-extended one); `gcd_hw_safe_fin_netBT`.
**Assumed:** `FGcdNetOKBA`'s fields with the extended bindings, plus the tree cells' contracts
(`FCelSpec` of their real C-element gates, the chunk nodes wired to the top node) and their
leaf pins bound. **NOT covered:** a joint witness; C's H_OTHER. Core Lean only.
-/

namespace Formal.Cells.FiniteNetBoundT
open Formal.Cells
open Formal.Cells.FiniteNet
open Formal.Cells.FiniteNetBound
open Formal.Cells.FiniteNetBoundM
open Formal.Cells.FiniteNetBoundA
open Formal.Cells.FiniteNetComb (FCombSpec fcomb_spec_cell)
open Formal.Cells.AssumeGuaranteeMuxNFin
open Formal.Cells.AssumeGuaranteeMuxNTree (rp5 ip4 rp6 ip2)
open Formal.Cells.LutFbBridge2Env (Wire isLink)
open Formal.Cells.AssumeGuaranteeEnds (GPin GC2 GC4)
open Formal.Cells.AssumeGuaranteeEndsNet (GD)
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe
open Formal.Cells.AssumeGuaranteeEndsCap (forkOuts joinIns steerIn d0 LinkOut)
open Formal.Net.Ops.Gen (genF)
open Formal.Gen Formal.Gen.Cells

/-! ## 1. The elaboration and the drivers -/

structure FGcdNetT extends FGcdNetA where
  /-- The top `C2` of a fork tree (drives the fork input's acknowledge). -/
  tr : Fin NO → ι
  /-- Chunk node 0 (`C4` of leaves 0..3) and 1 (`C2` of leaves 4, 5; N = 6 only). -/
  tn : Fin NO → Fin 2 → ι

inductive DKT
  | base (d : DKA)
  | tR (o : Fin NO)
  deriving DecidableEq, Repr

def DKT.cell (N : FGcdNetT) : DKT → N.ι
  | .base d => d.cell N.toFGcdNetA
  | .tR o => N.tr o

/-- A fork with 5 or 6 outputs (an acknowledge tree). -/
def treeOuts (k : K NC) : Option (List (Fin NC)) :=
  match forkOuts k with
  | some os => if 5 ≤ os.length ∧ os.length ≤ 6 then some os else none
  | none => none

/-- A fork tree's input acknowledge, followed forward through 1- and 2-input joins and a mux's
control acknowledge (as `arbAck`). -/
def treeAck : Nat → Fin NC → Option DKT
  | 0, _ => none
  | F + 1, c =>
    let o := consOf c
    match opAt o with
    | .join ins z _ _ _ => if ins.length = 2 ∨ ins.length = 1 then treeAck F z else none
    | .bjoin ins z _ _ => if ins.length = 2 ∨ ins.length = 1 then treeAck F z else none
    | .mux cc _ _ z _ => if c = cc then treeAck F z else none
    | k => if (treeOuts k).isSome then some (.tR o) else none

def reqSrcT (F : Nat) (c : Fin NC) : Option DKT := (reqSrcA F c).map .base
def ackSrcT (F : Nat) (c : Fin NC) : Option DKT :=
  ((ackSrcA F c).map .base).orElse fun _ => treeAck F c

/-- A fork tree's cells. -/
def TreeCell (N : FGcdNetT) (c : N.ι) : Prop :=
  ∃ o os, treeOuts (opAt o) = some os ∧
    (c = N.tr o ∨ c = N.tn o 0 ∨ (os.length = 6 ∧ c = N.tn o 1))

def FTiedT (N : FGcdNetT) (c : N.ι) : Prop := FTiedA N.toFGcdNetA c ∨ TreeCell N c

/-! ## 2. The hypothesis -/

def BoundRT (N : FGcdNetT) (c : Fin NC) (p : GPin N.ι) : Prop :=
  ∀ d, reqSrcT FU c = some d → p.drv = d.cell N

def BoundAT (N : FGcdNetT) (c : Fin NC) (p : GPin N.ι) : Prop :=
  ∀ d, ackSrcT FU c = some d → p.drv = d.cell N

theorem boundRA_of {N : FGcdNetT} {c : Fin NC} {p : GPin N.ι} (h : BoundRT N c p) :
    BoundRA N.toFGcdNetA c p := by
  intro d hd
  have : reqSrcT FU c = some (.base d) := by unfold reqSrcT; rw [hd]; rfl
  exact h _ this

theorem boundAA_of {N : FGcdNetT} {c : Fin NC} {p : GPin N.ι} (h : BoundAT N c p) :
    BoundAA N.toFGcdNetA c p := by
  intro d hd
  have : ackSrcT FU c = some (.base d) := by unfold ackSrcT; rw [hd]; rfl
  exact h _ this

/-- `ArbPins` with the tree-extended bindings. -/
def ArbPinsT (N : FGcdNetT) (ch : Fin NC → Chan) (o : Fin NO) (x y z : Fin NC)
    (ps : List (GPin N.ι)) (k : Nat) : Prop :=
  ∃ p1 p2 pq, (ps = [p1, p2, pq] ∨ ∃ pa, ps = [p1, p2, pq, pa] ∧ pa.P = (ch z).ack ∧
      BoundAT N z pa) ∧
    p1.P = (ch x).req ∧ BoundRT N x p1 ∧ p2.P = (ch y).req ∧ BoundRT N y p2 ∧ pq.drv = N.aq o ∧
    ps.length = k

theorem arbPins_of {N : FGcdNetT} {ch : Fin NC → Chan} {o : Fin NO} {x y z : Fin NC}
    {ps : List (GPin N.ι)} {k : Nat} (h : ArbPinsT N ch o x y z ps k) :
    ArbPins N.toFGcdNetA ch o x y z ps k := by
  obtain ⟨p1, p2, pq, hps, e1, b1, e2, b2, eq, hk⟩ := h
  refine ⟨p1, p2, pq, ?_, e1, boundRA_of b1, e2, boundRA_of b2, eq, hk⟩
  rcases hps with h3 | ⟨pa, h4, ea, ba⟩
  · exact Or.inl h3
  · exact Or.inr ⟨pa, h4, ea, boundAA_of ba⟩

/-- **The driver-bound hypotheses, muxes, arbiters and fork trees gate-modelled.** -/
structure FGcdNetOKBT (ch : Fin NC → Chan) (N : FGcdNetT) (L : N.ι → Nat → Prop)
    (n : N.ι → Nat) : Prop where
  NW : FNetW N.D L
  H_FIN : ∀ c j, L c j ↔ j < n c
  H_LINK : ∀ o i o', opAt o = .link i o' → ∃ rp ap Es Ea, FLinkSpec N.D L (N.lk o) rp ap Es Ea ∧
    rp.P = (ch i).req ∧ ap.P = (ch o').ack ∧ LinkOut N.D (N.lk o) (ch i) (ch o') Es Ea ∧
    BoundRT N i rp ∧ BoundAT N o' ap
  H_FORK : ∀ o os, forkOuts (opAt o) = some os → 2 ≤ os.length → os.length ≤ 4 →
    FCelTieB N.toFGcdNet L (N.fa o) os (fun c => (ch c).ack) (BoundAT N)
  H_JOIN : ∀ o ins, joinIns (opAt o) = some ins → ins.length = 2 →
    FCelTieB N.toFGcdNet L (N.jr o) ins (fun c => (ch c).req) (BoundRT N)
  H_STEER : ∀ o j, steerIn (opAt o) = some j → ∀ b, ∃ rp s σ κ,
    FSteerSpec N.D L (N.sb o b) rp b s σ κ ∧ rp.P = (ch j).req ∧ BoundRT N j rp ∧
    s = fun t => (ch j).dat t % 2 == 1
  H_SOR : ∀ o j t f, stJ (opAt o) = some (j, t, f) → ∃ ap σ κ,
    FOrSpec N.D L (N.ao o) (fun a0 a1 => genF bd_steer "uack" .O ["ack0", "ack1"] [a0, a1])
      ap σ κ ∧ ∀ b, (ap b).P = (ch (brC t f b)).ack ∧ BoundAT N (brC t f b) (ap b)
  H_MUXJ : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ b, ∃ xp cp s σ κ E,
    FMuxJSpec N.D L (N.mj o b) xp cp b s σ κ E ∧ xp.P = (ch (if b then y else x)).req ∧
    cp.P = (ch cc).req ∧ BoundRT N (if b then y else x) xp ∧ BoundRT N cc cp ∧
    s = fun t => (ch cc).dat t % 2 == 1
  H_MUXA : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ b, ∃ ap zp κ E,
    FMuxASpec N.D L (N.ma o b) ap zp κ E ∧ ap.drv = N.mj o b ∧ zp.P = (ch z).ack ∧
    BoundAT N z zp
  H_MUXO : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∃ ap σ κ,
    FOrSpec N.D L (N.mo o) uorF ap σ κ ∧ ∀ b, (ap b).drv = N.mj o b
  H_MUXD : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ i : Fin 2, ∃ p,
    FBufSpec N.D L (N.md o i) p ∧ p.drv = (if i.val = 0 then N.mo o else N.md o 0)
  H_ARBQ : ∀ o x y z w, opAt o = .amerge x y z w → ∃ ps e Le,
    FCombSpec N.D L (N.aq o) qF ps e Le ∧ ArbPinsT N ch o x y z ps 4
  H_ARBR : ∀ o x y z w, opAt o = .amerge x y z w → ∃ ps e Le,
    FCombSpec N.D L (N.aR o) r0F ps e Le ∧ ArbPinsT N ch o x y z ps 4
  H_ARBG : ∀ o x y z w, opAt o = .amerge x y z w → ∀ b, ∃ ps e Le,
    FCombSpec N.D L (N.ag o b) (gF b) ps e Le ∧ ArbPinsT N ch o x y z ps 3
  H_ARBA : ∀ o x y z w, opAt o = .amerge x y z w → ∀ b, ∃ ap zp κ E,
    FMuxASpec N.D L (N.aa o b) ap zp κ E ∧ ap.drv = N.ag o b ∧ zp.P = (ch z).ack ∧
    BoundAT N z zp
  /-- **A 5-output fork's tree**: top `C2(pin, leaf 4)`, chunk `C4(leaves 0..3)`, `pin` from the
  chunk node; every leaf the bound acknowledge of its fork output. -/
  H_TREE5 : ∀ o os, treeOuts (opAt o) = some os → os.length = 5 → ∃ pin lv E E',
    FCelSpec GC2 N.D L (N.tr o) (rp5 pin lv) E ∧ FCelSpec GC4 N.D L (N.tn o 0) (ip4 (m := 1) lv) E' ∧
    pin.drv = N.tn o 0 ∧
    ∀ k : Fin 5, (lv k).P = (ch (os.getD k.val d0)).ack ∧ BoundAT N (os.getD k.val d0) (lv k)
  /-- **A 6-output fork's tree**: top `C2(pa, pb)`, chunks `C4(leaves 0..3)`, `C2(leaves 4, 5)`. -/
  H_TREE6 : ∀ o os, treeOuts (opAt o) = some os → os.length = 6 → ∃ pa pb lv E Ea Eb,
    FCelSpec GC2 N.D L (N.tr o) (rp6 pa pb) E ∧
    FCelSpec GC4 N.D L (N.tn o 0) (ip4 (m := 2) lv) Ea ∧ FCelSpec GC2 N.D L (N.tn o 1) (ip2 lv) Eb ∧
    pa.drv = N.tn o 0 ∧ pb.drv = N.tn o 1 ∧
    ∀ k : Fin 6, (lv k).P = (ch (os.getD k.val d0)).ack ∧ BoundAT N (os.getD k.val d0) (lv k)
  H_REST : ∀ c, ¬ FTiedT N c → FCellOK N.D L c
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
  /-- The top node drives the fork input's acknowledge. -/
  H_DRV_TREE : ∀ o os i, treeOuts (opAt o) = some os → forkIn (opAt o) = some i →
    ∃ wl wh, Wire wl wh (N.D.O (N.tr o)) (ch i).ack

theorem FGcdNetOKBT.toOKBA {ch : Fin NC → Chan} {N : FGcdNetT} {L : N.ι → Nat → Prop}
    {n : N.ι → Nat} (H : FGcdNetOKBT ch N L n) : FGcdNetOKBA ch N.toFGcdNetA L n where
  NW := H.NW
  H_FIN := H.H_FIN
  H_LINK := fun o i o' h => by
    obtain ⟨rp, ap, Es, Ea, S, e1, e2, lo, br, ba⟩ := H.H_LINK o i o' h
    exact ⟨rp, ap, Es, Ea, S, e1, e2, lo, boundRA_of br, boundAA_of ba⟩
  H_FORK := fun o os h h1 h2 => tieB_mono (fun _ _ hb => boundAA_of hb) (H.H_FORK o os h h1 h2)
  H_JOIN := fun o ins h h1 => tieB_mono (fun _ _ hb => boundRA_of hb) (H.H_JOIN o ins h h1)
  H_STEER := fun o j h b => by
    obtain ⟨rp, s, σ, κ, S, e, br, hs⟩ := H.H_STEER o j h b
    exact ⟨rp, s, σ, κ, S, e, boundRA_of br, hs⟩
  H_SOR := fun o j t f h => by
    obtain ⟨ap, σ, κ, S, hb⟩ := H.H_SOR o j t f h
    exact ⟨ap, σ, κ, S, fun b => ⟨(hb b).1, boundAA_of (hb b).2⟩⟩
  H_MUXJ := fun o cc x y z mw h b => by
    obtain ⟨xp, cp, s, σ, κ, E, S, e1, e2, b1, b2, hs⟩ := H.H_MUXJ o cc x y z mw h b
    exact ⟨xp, cp, s, σ, κ, E, S, e1, e2, boundRA_of b1, boundRA_of b2, hs⟩
  H_MUXA := fun o cc x y z mw h b => by
    obtain ⟨ap, zp, κ, E, S, e1, e2, bz⟩ := H.H_MUXA o cc x y z mw h b
    exact ⟨ap, zp, κ, E, S, e1, e2, boundAA_of bz⟩
  H_MUXO := H.H_MUXO
  H_MUXD := H.H_MUXD
  H_ARBQ := fun o x y z w h => by
    obtain ⟨ps, e, Le, S, hp⟩ := H.H_ARBQ o x y z w h
    exact ⟨ps, e, Le, S, arbPins_of hp⟩
  H_ARBR := fun o x y z w h => by
    obtain ⟨ps, e, Le, S, hp⟩ := H.H_ARBR o x y z w h
    exact ⟨ps, e, Le, S, arbPins_of hp⟩
  H_ARBG := fun o x y z w h b => by
    obtain ⟨ps, e, Le, S, hp⟩ := H.H_ARBG o x y z w h b
    exact ⟨ps, e, Le, S, arbPins_of hp⟩
  H_ARBA := fun o x y z w h b => by
    obtain ⟨ap, zp, κ, E, S, e1, e2, bz⟩ := H.H_ARBA o x y z w h b
    exact ⟨ap, zp, κ, E, S, e1, e2, boundAA_of bz⟩
  H_REST := fun c hc => by
    by_cases ht : TreeCell N c
    · obtain ⟨o, os, ho, hr | h0 | ⟨h6, h1⟩⟩ := ht
      · have hl : 5 ≤ os.length ∧ os.length ≤ 6 := by
          unfold treeOuts at ho; split at ho
          · split at ho
            · cases ho; assumption
            · cases ho
          · cases ho
        subst hr
        rcases (show os.length = 5 ∨ os.length = 6 by omega) with e | e
        · obtain ⟨_, _, _, _, S, _⟩ := H.H_TREE5 o os ho e; exact fcel_spec_cell H.NW S
        · obtain ⟨_, _, _, _, _, _, S, _⟩ := H.H_TREE6 o os ho e; exact fcel_spec_cell H.NW S
      · have hl : 5 ≤ os.length ∧ os.length ≤ 6 := by
          unfold treeOuts at ho; split at ho
          · split at ho
            · cases ho; assumption
            · cases ho
          · cases ho
        subst h0
        rcases (show os.length = 5 ∨ os.length = 6 by omega) with e | e
        · obtain ⟨_, _, _, _, _, S, _⟩ := H.H_TREE5 o os ho e; exact fcel_spec_cell H.NW S
        · obtain ⟨_, _, _, _, _, _, _, S, _⟩ := H.H_TREE6 o os ho e; exact fcel_spec_cell H.NW S
      · subst h1
        obtain ⟨_, _, _, _, _, _, _, _, S, _⟩ := H.H_TREE6 o os ho h6; exact fcel_spec_cell H.NW S
    · exact H.H_REST c (fun h => h.elim hc ht)
  H_DRV_FORK := H.H_DRV_FORK
  H_DRV_JOIN := H.H_DRV_JOIN
  H_DRV_STEER := H.H_DRV_STEER
  H_DRV_MUX := H.H_DRV_MUX
  H_DRV_ARB := H.H_DRV_ARB

/-! ## 3. Census -/

def linkSidesT (F : Nat) : List (Bool × Bool) :=
  (List.finRange NO).filterMap fun o => match opAt o with
    | .link i o' => some ((reqSrcT F i).isSome, (ackSrcT F o').isSome)
    | _ => none

def nBothT : Nat := ((linkSidesT FU).filter fun p => p.1 && p.2).length

set_option maxRecDepth 100000

theorem bound_censusT : nBothT = 170 := by decide +kernel

/-! ## 4. The theorem -/

/-- **gcd_hw is safe** under the tree-extended driver-bound gate-level hypothesis. -/
theorem gcd_hw_safe_fin_netBT (a b : Nat) (ch : Fin NC → Chan) (N : FGcdNetT)
    (L : N.ι → Nat → Prop) (n : N.ι → Nat) (H : FGcdNetOKBT ch N L n)
    (H_OTHER : ∀ o : Fin NO, isLink (opAt o) = false → Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_CM_FORCED : ∃ y, Good a b y ∧ ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) :=
  FiniteNetBoundA.gcd_hw_safe_fin_netBA a b ch N.toFGcdNetA L n H.toOKBA H_OTHER H_BUNDLE
    H_CM_FORCED

end Formal.Cells.FiniteNetBoundT
