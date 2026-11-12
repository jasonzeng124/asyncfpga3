import Formal.Cells.FiniteNetBoundT
import Formal.Cells.LibGapMuxN

/-!
# Probe Belab5 (shard B): the driver-bound gate-level network with the MUXN gate-modelled

`notes/B-muxn-bind-plan.md`: with `FiniteNetBoundT`, 4 of the 5 link sides still unbound are
acknowledge sides ending at gcd_hw's one `muxn` (`bdc_muxn3_32`, `bdc/emit.py emit_muxn`): its
three input acknowledges and its control acknowledge. Here the muxn's per-input cells are
gate-modelled and the INPUT acknowledges bound:
* `nd o k`, the decode `sel_k = ctl_req ∧ (s == k)` (`FDecSpec`: the LUT3 INITs of
  `LibGapMuxN`, inferred under its H_YOSYS_MAP: the emitter leaves the decode to yosys);
* `nj o k`, the join `uj_k = C(in_k.req, sel_k)` (`FCelSpec GC2`);
* `na o k`, the acknowledge `ua_k = C(j_k, z_ack)` (`FMuxASpec`), driving `in_k.ack`.
The control acknowledge (a wire from `z_ack`) stays unbound: `z` feeds a sink, which B does
not gate-model. The request OR and the delay chain to `z.req` are not modelled here (no
unbound side ends there; they stay under H_REST's truncated contract).

## Assumed / proved / NOT covered

**Proved:** `bound_censusN` (kernel): 173 of 175 links bound on both sides;
`FGcdNetOKBN.toOKBT`; `gcd_hw_safe_fin_netBN`. **Assumed:** `FGcdNetOKBT`'s fields with the
extended bindings plus H_MUXN (the three cells' specs per input, pins bound) and H_DRV_MUXN.
**NOT covered:** a joint witness (none: no simulator model of the generated muxn yet); the
decode INITs are H_YOSYS_MAP's inference, not read from a netlist; C's H_OTHER. Core Lean only.
-/

namespace Formal.Cells.FiniteNetBoundN
open Formal.Cells
open Formal.Cells.FiniteNet
open Formal.Cells.FiniteNetBound
open Formal.Cells.FiniteNetBoundM
open Formal.Cells.FiniteNetBoundA
open Formal.Cells.FiniteNetBoundT
open Formal.Cells.FiniteNetComb (FCombSpec fcomb_spec_cell)
open Formal.Cells.AssumeGuaranteeMuxNFin
open Formal.Cells.AssumeGuaranteeMuxNTree (rp5 ip4 rp6 ip2)
open Formal.Cells.LibGapMuxN (bit0 bit1)
open Formal.Cells.LutFbBridge2Env (Wire isLink)
open Formal.Cells.AssumeGuaranteeEnds (GPin GC2 GC4)
open Formal.Cells.AssumeGuaranteeEndsNet (GD)
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe
open Formal.Cells.AssumeGuaranteeEndsCap (forkOuts joinIns steerIn d0 LinkOut)
open Formal.Net.Ops.Gen (genF)
open Formal.Gen Formal.Gen.Cells

/-! ## 1. The elaboration and the drivers -/

structure FGcdNetN extends FGcdNetT where
  /-- The decode `sel_k`, the join `uj_k`, the acknowledge `ua_k` of a muxn's input `k`. -/
  nd : Fin NO → Fin 3 → ι
  nj : Fin NO → Fin 3 → ι
  na : Fin NO → Fin 3 → ι

inductive DKN
  | base (d : DKT)
  | nA (o : Fin NO) (k : Fin 3)
  deriving DecidableEq, Repr

def DKN.cell (N : FGcdNetN) : DKN → N.ι
  | .base d => d.cell N.toFGcdNetT
  | .nA o k => N.na o k

/-- A muxn's input `k`. -/
def muxIn (x0 x1 x2 : Fin NC) (k : Fin 3) : Fin NC :=
  if k.val = 0 then x0 else if k.val = 1 then x1 else x2

/-- A muxn input's acknowledge, followed forward through 1- and 2-input joins and a mux's
control acknowledge (as `arbAck`). -/
def muxnAck : Nat → Fin NC → Option DKN
  | 0, _ => none
  | F + 1, c =>
    let o := consOf c
    match opAt o with
    | .join ins z _ _ _ => if ins.length = 2 ∨ ins.length = 1 then muxnAck F z else none
    | .bjoin ins z _ _ => if ins.length = 2 ∨ ins.length = 1 then muxnAck F z else none
    | .mux cc _ _ z _ => if c = cc then muxnAck F z else none
    | .muxn _ x0 x1 x2 _ _ =>
        if c = x0 then some (.nA o 0) else if c = x1 then some (.nA o 1)
        else if c = x2 then some (.nA o 2) else none
    | _ => none

def reqSrcN (F : Nat) (c : Fin NC) : Option DKN := (reqSrcT F c).map .base
def ackSrcN (F : Nat) (c : Fin NC) : Option DKN :=
  ((ackSrcT F c).map .base).orElse fun _ => muxnAck F c

/-- A muxn's cells. -/
def MuxnCell (N : FGcdNetN) (c : N.ι) : Prop :=
  ∃ o cc x0 x1 x2 z nw, opAt o = .muxn cc x0 x1 x2 z nw ∧
    ∃ k, c = N.nd o k ∨ c = N.nj o k ∨ c = N.na o k

def FTiedN (N : FGcdNetN) (c : N.ι) : Prop := FTiedT N.toFGcdNetT c ∨ MuxnCell N c

/-! ## 2. The hypothesis -/

def BoundRN (N : FGcdNetN) (c : Fin NC) (p : GPin N.ι) : Prop :=
  ∀ d, reqSrcN FU c = some d → p.drv = d.cell N

def BoundAN (N : FGcdNetN) (c : Fin NC) (p : GPin N.ι) : Prop :=
  ∀ d, ackSrcN FU c = some d → p.drv = d.cell N

theorem boundRT_of {N : FGcdNetN} {c : Fin NC} {p : GPin N.ι} (h : BoundRN N c p) :
    BoundRT N.toFGcdNetT c p := by
  intro d hd
  have : reqSrcN FU c = some (.base d) := by unfold reqSrcN; rw [hd]; rfl
  exact h _ this

theorem boundAT_of {N : FGcdNetN} {c : Fin NC} {p : GPin N.ι} (h : BoundAN N c p) :
    BoundAT N.toFGcdNetT c p := by
  intro d hd
  have : ackSrcN FU c = some (.base d) := by unfold ackSrcN; rw [hd]; rfl
  exact h _ this

/-- `ArbPins` with the muxn-extended bindings. -/
def ArbPinsN (N : FGcdNetN) (ch : Fin NC → Chan) (o : Fin NO) (x y z : Fin NC)
    (ps : List (GPin N.ι)) (k : Nat) : Prop :=
  ∃ p1 p2 pq, (ps = [p1, p2, pq] ∨ ∃ pa, ps = [p1, p2, pq, pa] ∧ pa.P = (ch z).ack ∧
      BoundAN N z pa) ∧
    p1.P = (ch x).req ∧ BoundRN N x p1 ∧ p2.P = (ch y).req ∧ BoundRN N y p2 ∧ pq.drv = N.aq o ∧
    ps.length = k

theorem arbPinsT_of {N : FGcdNetN} {ch : Fin NC → Chan} {o : Fin NO} {x y z : Fin NC}
    {ps : List (GPin N.ι)} {k : Nat} (h : ArbPinsN N ch o x y z ps k) :
    ArbPinsT N.toFGcdNetT ch o x y z ps k := by
  obtain ⟨p1, p2, pq, hps, e1, b1, e2, b2, eq, hk⟩ := h
  refine ⟨p1, p2, pq, ?_, e1, boundRT_of b1, e2, boundRT_of b2, eq, hk⟩
  rcases hps with h3 | ⟨pa, h4, ea, ba⟩
  · exact Or.inl h3
  · exact Or.inr ⟨pa, h4, ea, boundAT_of ba⟩

structure FGcdNetOKBN (ch : Fin NC → Chan) (N : FGcdNetN) (L : N.ι → Nat → Prop)
    (n : N.ι → Nat) : Prop where
  NW : FNetW N.D L
  H_FIN : ∀ c j, L c j ↔ j < n c
  H_LINK : ∀ o i o', opAt o = .link i o' → ∃ rp ap Es Ea, FLinkSpec N.D L (N.lk o) rp ap Es Ea ∧
    rp.P = (ch i).req ∧ ap.P = (ch o').ack ∧ LinkOut N.D (N.lk o) (ch i) (ch o') Es Ea ∧
    BoundRN N i rp ∧ BoundAN N o' ap
  H_FORK : ∀ o os, forkOuts (opAt o) = some os → 2 ≤ os.length → os.length ≤ 4 →
    FCelTieB N.toFGcdNet L (N.fa o) os (fun c => (ch c).ack) (BoundAN N)
  H_JOIN : ∀ o ins, joinIns (opAt o) = some ins → ins.length = 2 →
    FCelTieB N.toFGcdNet L (N.jr o) ins (fun c => (ch c).req) (BoundRN N)
  H_STEER : ∀ o j, steerIn (opAt o) = some j → ∀ b, ∃ rp s σ κ,
    FSteerSpec N.D L (N.sb o b) rp b s σ κ ∧ rp.P = (ch j).req ∧ BoundRN N j rp ∧
    s = fun t => (ch j).dat t % 2 == 1
  H_SOR : ∀ o j t f, stJ (opAt o) = some (j, t, f) → ∃ ap σ κ,
    FOrSpec N.D L (N.ao o) (fun a0 a1 => genF bd_steer "uack" .O ["ack0", "ack1"] [a0, a1])
      ap σ κ ∧ ∀ b, (ap b).P = (ch (brC t f b)).ack ∧ BoundAN N (brC t f b) (ap b)
  H_MUXJ : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ b, ∃ xp cp s σ κ E,
    FMuxJSpec N.D L (N.mj o b) xp cp b s σ κ E ∧ xp.P = (ch (if b then y else x)).req ∧
    cp.P = (ch cc).req ∧ BoundRN N (if b then y else x) xp ∧ BoundRN N cc cp ∧
    s = fun t => (ch cc).dat t % 2 == 1
  H_MUXA : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ b, ∃ ap zp κ E,
    FMuxASpec N.D L (N.ma o b) ap zp κ E ∧ ap.drv = N.mj o b ∧ zp.P = (ch z).ack ∧
    BoundAN N z zp
  H_MUXO : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∃ ap σ κ,
    FOrSpec N.D L (N.mo o) uorF ap σ κ ∧ ∀ b, (ap b).drv = N.mj o b
  H_MUXD : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ i : Fin 2, ∃ p,
    FBufSpec N.D L (N.md o i) p ∧ p.drv = (if i.val = 0 then N.mo o else N.md o 0)
  H_ARBQ : ∀ o x y z w, opAt o = .amerge x y z w → ∃ ps e Le,
    FCombSpec N.D L (N.aq o) qF ps e Le ∧ ArbPinsN N ch o x y z ps 4
  H_ARBR : ∀ o x y z w, opAt o = .amerge x y z w → ∃ ps e Le,
    FCombSpec N.D L (N.aR o) r0F ps e Le ∧ ArbPinsN N ch o x y z ps 4
  H_ARBG : ∀ o x y z w, opAt o = .amerge x y z w → ∀ b, ∃ ps e Le,
    FCombSpec N.D L (N.ag o b) (gF b) ps e Le ∧ ArbPinsN N ch o x y z ps 3
  H_ARBA : ∀ o x y z w, opAt o = .amerge x y z w → ∀ b, ∃ ap zp κ E,
    FMuxASpec N.D L (N.aa o b) ap zp κ E ∧ ap.drv = N.ag o b ∧ zp.P = (ch z).ack ∧
    BoundAN N z zp
  /-- **A 5-output fork's tree**: top `C2(pin, leaf 4)`, chunk `C4(leaves 0..3)`, `pin` from the
  chunk node; every leaf the bound acknowledge of its fork output. -/
  H_TREE5 : ∀ o os, treeOuts (opAt o) = some os → os.length = 5 → ∃ pin lv E E',
    FCelSpec GC2 N.D L (N.tr o) (rp5 pin lv) E ∧ FCelSpec GC4 N.D L (N.tn o 0) (ip4 (m := 1) lv) E' ∧
    pin.drv = N.tn o 0 ∧
    ∀ k : Fin 5, (lv k).P = (ch (os.getD k.val d0)).ack ∧ BoundAN N (os.getD k.val d0) (lv k)
  /-- **A 6-output fork's tree**: top `C2(pa, pb)`, chunks `C4(leaves 0..3)`, `C2(leaves 4, 5)`. -/
  H_TREE6 : ∀ o os, treeOuts (opAt o) = some os → os.length = 6 → ∃ pa pb lv E Ea Eb,
    FCelSpec GC2 N.D L (N.tr o) (rp6 pa pb) E ∧
    FCelSpec GC4 N.D L (N.tn o 0) (ip4 (m := 2) lv) Ea ∧ FCelSpec GC2 N.D L (N.tn o 1) (ip2 lv) Eb ∧
    pa.drv = N.tn o 0 ∧ pb.drv = N.tn o 1 ∧
    ∀ k : Fin 6, (lv k).P = (ch (os.getD k.val d0)).ack ∧ BoundAN N (os.getD k.val d0) (lv k)
  /-- **`bdc_muxn`'s cells, per input `k`**: the decode `sel_k = ctl_req ∧ (s == k)` (its
  index bits are the control channel's data), the join `uj_k = C(in_k.req, sel_k)`, and the
  acknowledge `ua_k = C(j_k, z_ack)` read at input `k`'s tokens. -/
  H_MUXN : ∀ o cc x0 x1 x2 z nw, opAt o = .muxn cc x0 x1 x2 z nw → ∀ k : Fin 3,
    (∃ cp σ κ, FDecSpec N.D L (N.nd o k) cp k.val (fun t => bit0 ((ch cc).dat t))
        (fun t => bit1 ((ch cc).dat t)) σ κ ∧ cp.P = (ch cc).req ∧ BoundRN N cc cp) ∧
    (∃ pv E, FCelSpec GC2 N.D L (N.nj o k) pv E ∧ (pv 0).P = (ch (muxIn x0 x1 x2 k)).req ∧
        BoundRN N (muxIn x0 x1 x2 k) (pv 0) ∧ (pv 1).drv = N.nd o k) ∧
    (∃ ap zp κ E, FMuxASpec N.D L (N.na o k) ap zp κ E ∧ ap.drv = N.nj o k ∧
        zp.P = (ch z).ack ∧ BoundAN N z zp)
  H_REST : ∀ c, ¬ FTiedN N c → FCellOK N.D L c
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
  H_DRV_MUXN : ∀ o cc x0 x1 x2 z nw, opAt o = .muxn cc x0 x1 x2 z nw → ∀ k : Fin 3,
    ∃ wl wh, Wire wl wh (N.D.O (N.na o k)) (ch (muxIn x0 x1 x2 k)).ack
  /-- The top node drives the fork input's acknowledge. -/
  H_DRV_TREE : ∀ o os i, treeOuts (opAt o) = some os → forkIn (opAt o) = some i →
    ∃ wl wh, Wire wl wh (N.D.O (N.tr o)) (ch i).ack

theorem FGcdNetOKBN.toOKBT {ch : Fin NC → Chan} {N : FGcdNetN} {L : N.ι → Nat → Prop}
    {n : N.ι → Nat} (H : FGcdNetOKBN ch N L n) : FGcdNetOKBT ch N.toFGcdNetT L n where
  NW := H.NW
  H_FIN := H.H_FIN
  H_LINK := fun o i o' h => by
    obtain ⟨rp, ap, Es, Ea, S, e1, e2, lo, br, ba⟩ := H.H_LINK o i o' h
    exact ⟨rp, ap, Es, Ea, S, e1, e2, lo, boundRT_of br, boundAT_of ba⟩
  H_FORK := fun o os h h1 h2 => tieB_mono (fun _ _ hb => boundAT_of hb) (H.H_FORK o os h h1 h2)
  H_JOIN := fun o ins h h1 => tieB_mono (fun _ _ hb => boundRT_of hb) (H.H_JOIN o ins h h1)
  H_STEER := fun o j h b => by
    obtain ⟨rp, s, σ, κ, S, e, br, hs⟩ := H.H_STEER o j h b
    exact ⟨rp, s, σ, κ, S, e, boundRT_of br, hs⟩
  H_SOR := fun o j t f h => by
    obtain ⟨ap, σ, κ, S, hb⟩ := H.H_SOR o j t f h
    exact ⟨ap, σ, κ, S, fun b => ⟨(hb b).1, boundAT_of (hb b).2⟩⟩
  H_MUXJ := fun o cc x y z mw h b => by
    obtain ⟨xp, cp, s, σ, κ, E, S, e1, e2, b1, b2, hs⟩ := H.H_MUXJ o cc x y z mw h b
    exact ⟨xp, cp, s, σ, κ, E, S, e1, e2, boundRT_of b1, boundRT_of b2, hs⟩
  H_MUXA := fun o cc x y z mw h b => by
    obtain ⟨ap, zp, κ, E, S, e1, e2, bz⟩ := H.H_MUXA o cc x y z mw h b
    exact ⟨ap, zp, κ, E, S, e1, e2, boundAT_of bz⟩
  H_MUXO := H.H_MUXO
  H_MUXD := H.H_MUXD
  H_ARBQ := fun o x y z w h => by
    obtain ⟨ps, e, Le, S, hp⟩ := H.H_ARBQ o x y z w h
    exact ⟨ps, e, Le, S, arbPinsT_of hp⟩
  H_ARBR := fun o x y z w h => by
    obtain ⟨ps, e, Le, S, hp⟩ := H.H_ARBR o x y z w h
    exact ⟨ps, e, Le, S, arbPinsT_of hp⟩
  H_ARBG := fun o x y z w h b => by
    obtain ⟨ps, e, Le, S, hp⟩ := H.H_ARBG o x y z w h b
    exact ⟨ps, e, Le, S, arbPinsT_of hp⟩
  H_ARBA := fun o x y z w h b => by
    obtain ⟨ap, zp, κ, E, S, e1, e2, bz⟩ := H.H_ARBA o x y z w h b
    exact ⟨ap, zp, κ, E, S, e1, e2, boundAT_of bz⟩
  H_TREE5 := fun o os h e => by
    obtain ⟨pin, lv, E, E', S1, S2, hd, hl⟩ := H.H_TREE5 o os h e
    exact ⟨pin, lv, E, E', S1, S2, hd, fun k => ⟨(hl k).1, boundAT_of (hl k).2⟩⟩
  H_TREE6 := fun o os h e => by
    obtain ⟨pa, pb, lv, E, Ea, Eb, S1, S2, S3, ha, hb, hl⟩ := H.H_TREE6 o os h e
    exact ⟨pa, pb, lv, E, Ea, Eb, S1, S2, S3, ha, hb, fun k => ⟨(hl k).1, boundAT_of (hl k).2⟩⟩
  H_REST := fun c hc => by
    by_cases hm : MuxnCell N c
    · obtain ⟨o, cc, x0, x1, x2, z, nw, ho, k, hd | hj | ha⟩ := hm
      · subst hd; obtain ⟨⟨_, _, _, S, _⟩, _⟩ := H.H_MUXN o cc x0 x1 x2 z nw ho k
        exact fdec_spec_cell S
      · subst hj; obtain ⟨_, ⟨_, _, S, _⟩, _⟩ := H.H_MUXN o cc x0 x1 x2 z nw ho k
        exact fcel_spec_cell H.NW S
      · subst ha; obtain ⟨_, _, ⟨_, _, _, _, S, _⟩⟩ := H.H_MUXN o cc x0 x1 x2 z nw ho k
        exact fmuxa_spec_cell H.NW S
    exact H.H_REST c (fun h => h.elim hc hm)
  H_DRV_FORK := H.H_DRV_FORK
  H_DRV_JOIN := H.H_DRV_JOIN
  H_DRV_STEER := H.H_DRV_STEER
  H_DRV_MUX := H.H_DRV_MUX
  H_DRV_ARB := H.H_DRV_ARB
  H_DRV_TREE := H.H_DRV_TREE

/-! ## 3. Census -/

def linkSidesN (F : Nat) : List (Bool × Bool) :=
  (List.finRange NO).filterMap fun o => match opAt o with
    | .link i o' => some ((reqSrcN F i).isSome, (ackSrcN F o').isSome)
    | _ => none

def nBothN : Nat := ((linkSidesN FU).filter fun p => p.1 && p.2).length

set_option maxRecDepth 100000

theorem bound_censusN : nBothN = 173 := by decide +kernel

/-! ## 4. The theorem -/

/-- **gcd_hw is safe** under the muxn-extended driver-bound gate-level hypothesis. -/
theorem gcd_hw_safe_fin_netBN (a b : Nat) (ch : Fin NC → Chan) (N : FGcdNetN)
    (L : N.ι → Nat → Prop) (n : N.ι → Nat) (H : FGcdNetOKBN ch N L n)
    (H_OTHER : ∀ o : Fin NO, isLink (opAt o) = false → Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_CM_FORCED : ∃ y, Good a b y ∧ ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) :=
  FiniteNetBoundT.gcd_hw_safe_fin_netBT a b ch N.toFGcdNetT L n H.toOKBT H_OTHER H_BUNDLE
    H_CM_FORCED

end Formal.Cells.FiniteNetBoundN
