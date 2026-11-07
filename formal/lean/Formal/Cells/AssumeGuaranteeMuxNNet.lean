import Formal.Cells.AssumeGuaranteeMuxNFin

/-!
# Probe Bmn (shard B): gcd_hw with muxn and the fork trees gate-modelled (segment and truncated)

`AssumeGuaranteeMuxNet.gcd_hw_safe_net2` (segment rule, infinite runs) left contracts on the
ORs, the muxn, the 9 amerges and the 3 fork trees; `FiniteNet.gcd_hw_safe_fin_net` (time-
indexed rule, finite or infinite runs) left them on every mux cell, the muxn, the amerges,
the sources and the trees. This file restates both with the cells of `AssumeGuaranteeMuxN`,
`AssumeGuaranteeMuxNTree` and `AssumeGuaranteeMuxNFin` gate-modelled.

## Assumed / proved / NOT covered

**Proved:**
* `op_classes3` (kernel census): of gcd_hw's 367 operators, after links, forks N ≤ 4,
  joins N = 2, steers, muxes, sources, the muxn and the fork trees N = 5, 6, the operators
  NOT fully tied in the segment form are `join1` 11 and `sink` 18 (no cell) and `amerge` 9.
  `tree_classes`: the trees are `forkH5` ×2, `forkH6` ×1.
* `gcd_hw_safe_net3` (segment form): C's gcd_hw safety with all 175 links' `H_CELLS`
  discharged by one gate-level network (`GcdNetOK3`) in which, beyond `GcdNetOK2`, the
  muxn's 3 decodes, 3 joins, 3 acknowledges, `uor` and line stage 0, and every node of the
  3 fork trees carry B's gate model. Contracts remain on (`Tied3`): the 38 steer `uack` and
  21 mux `uor` ORs, the muxn's `|j` OR and its 11 FASTFALL stages (not segment-causal:
  `AssumeGuaranteeMuxN.Wit.gstage_not_causal`), and the 9 amerges.
* `op_classes_fin3`, `gcd_hw_safe_fin_net3` (truncated form, runs that stop): beyond Bfin2's
  `FGcdNetOK` (links, forks N ≤ 4, joins N = 2, steer branches and steer ORs), every cell of
  the 21 muxes (joins `FMuxJSpec`, acknowledges `FMuxASpec`, delay buffers `FBufSpec`, `uor`
  Bfin2's `FOrSpec`), the muxn's decodes, joins, acknowledges, `uor`, stage 0 AND its 11
  FASTFALL stages (`FAndSpec`), and every fork-tree node carry B's gate model. Contracts
  remain on: the muxn's `|j` (a 3-input OR), the 3 sources (no truncated source lemma), the
  9 amerges.

**Assumed:** as `GcdNetOK2` / `FGcdNetOK`, plus each new cell's spec (gate model, H_TIMES,
edge sets, departure bounds as EDGE-TIME inequalities, H_SEL_STABLE per index bit, the
trees' `H_ACK` relative to the root, the AND stages' `H_OVL`), with the channel traces as
the pins named in the fields. H_YOSYS_MAP (decode INITs) and H_TREE6_MAP (N = 6 node INITs).

**NOT covered:** no joint witness of `GcdNetOK3` / `FGcdNetOK3` (the cell specs are
witnessed separately); the elaboration is abstract; departure bounds are not derived from
delay constants. Core Lean only.
-/

namespace Formal.Cells.AssumeGuaranteeMuxNNet
open Formal.Cells
open Formal.Cells.AssumeGuaranteeEnds (GPin gE GC2 GC4)
open Formal.Cells.AssumeGuaranteeEndsNet
open Formal.Cells.AssumeGuaranteeMuxNet
open Formal.Cells.AssumeGuaranteeMuxN (DecSpec dec_spec_cell dec_spec_wait)
open Formal.Cells.AssumeGuaranteeMuxNTree (Tree5 Tree6 tree5_cel tree6_cel)
open Formal.Cells.AssumeGuaranteeMuxNFin
open Formal.Cells.FiniteNet
open Formal.Cells.LutFbBridge (Phases)
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe
open Formal.Cells.LutFbBridge2Env (isLink)
open Formal.Cells.AssumeGuaranteeCap (kname census)
open Formal.Cells.AssumeGuaranteeEndsCap (tiedOp forkOuts joinIns steerIn d0 LinkOut)
open Formal.Net.Ops.Gen (genF)
open Formal.Gen Formal.Gen.Cells

/-! ## 1. The census -/

def isMuxNK : K NC → Bool
  | .muxn _ _ _ _ _ _ => true
  | _ => false
def isTreeK (k : K NC) : Bool :=
  match forkOuts k with | some os => 5 ≤ os.length | none => false

def tiedOp3 (k : K NC) : Bool := tiedOp2 k || isMuxNK k || isTreeK k

/-- **What is left, segment form** (kernel census): `join1` and `sink` have no cell; only
the amerges are untied operators. -/
theorem op_classes3 :
    census (((List.finRange NO).filter (fun o => !tiedOp3 (opAt o))).map (fun o => kname (opAt o)))
      = [("join1", 11), ("sink", 18), ("amerge", 9)] := by
  decide +kernel

theorem tree_classes :
    census (((List.finRange NO).filter (fun o => isTreeK (opAt o))).map (fun o => kname (opAt o)))
      = [("forkH5", 2), ("forkH6", 1)] := by
  decide +kernel

/-- The truncated form ties links, forks N ≤ 4, joins N = 2, steers, muxes, the muxn and the
trees (not the sources). -/
def tiedF3 (k : K NC) : Bool := tiedOp k || isMuxK k || isMuxNK k || isTreeK k

/-- **What is left, truncated form** (kernel census). -/
theorem op_classes_fin3 :
    census (((List.finRange NO).filter (fun o => !tiedF3 (opAt o))).map (fun o => kname (opAt o)))
      = [("join1", 11), ("sink", 18), ("amerge", 9), ("src", 3)] := by
  decide +kernel

/-! ## 2. Segment form -/

section seg
variable {ι : Type}

theorem contract_of_cel {D : GD ι} (NW : NetW D) {n : Nat} {G : (Fin n → Bool) → Bool → Bool → Bool}
    {c : ι} {pv : Fin n → GPin ι} {E : Nat} (S : CelSpec G D c pv E) : Contract D c :=
  ⟨fun k hA => cel_spec_cell NW S k hA, cel_spec_wait NW S⟩

end seg

/-- The gate-level elaboration with the muxn's cells (`nd` decode, `nj` join, `na`
acknowledge, `nl` the request line: `0` = `uor`, `1` = stage 0, `2..12` the FASTFALL stages)
and the fork-tree nodes `tr` (`0` root, `1` the `C4`, `2` the inner `C2` of N = 6). -/
structure GcdNet3 extends GcdNet2 where
  nd : Fin NO → Fin 3 → ι
  nj : Fin NO → Fin 3 → ι
  na : Fin NO → Fin 3 → ι
  nl : Fin NO → Fin 13 → ι
  tr : Fin NO → Fin 3 → ι

/-- The input `k` of a muxn. -/
def mx (x0 x1 x2 : Fin NC) (k : Fin 3) : Fin NC := if k.val = 0 then x0 else if k.val = 1 then x1 else x2

/-- The cells with a B gate model in `GcdNetOK3`. -/
def Tied3 (N : GcdNet3) (c : N.ι) : Prop :=
  Tied2 N.toGcdNet2 c ∨
  (∃ o cc x0 x1 x2 z nw k, opAt o = .muxn cc x0 x1 x2 z nw ∧
    (c = N.nd o k ∨ c = N.nj o k ∨ c = N.na o k)) ∨
  (∃ o cc x0 x1 x2 z nw, ∃ i : Fin 13, opAt o = .muxn cc x0 x1 x2 z nw ∧ i.val < 2 ∧ c = N.nl o i) ∨
  (∃ o os, ∃ i : Fin 3, forkOuts (opAt o) = some os ∧
    ((os.length = 5 ∧ i.val < 2) ∨ os.length = 6) ∧ c = N.tr o i)

/-- **The hypotheses**: `GcdNetOK2`'s, plus the muxn's and the trees' cell specs; a segment
contract only on the cells not in `Tied3`. -/
structure GcdNetOK3 (ch : Fin NC → Chan) (N : GcdNet3) : Prop where
  NW : NetW N.D
  H_LINK : ∀ o i o', opAt o = .link i o' → ∃ rp ap Es Ea, LinkSpec N.D (N.lk o) rp ap Es Ea ∧
    rp.P = (ch i).req ∧ ap.P = (ch o').ack ∧ LinkOut N.D (N.lk o) (ch i) (ch o') Es Ea
  H_FORK : ∀ o os, forkOuts (opAt o) = some os → 2 ≤ os.length → os.length ≤ 4 →
    AssumeGuaranteeEndsCap.CelTie N.D (N.fa o) os (fun c => (ch c).ack)
  H_JOIN : ∀ o ins, joinIns (opAt o) = some ins → ins.length = 2 →
    AssumeGuaranteeEndsCap.CelTie N.D (N.jr o) ins (fun c => (ch c).req)
  H_STEER : ∀ o j, steerIn (opAt o) = some j → ∀ b, ∃ rp s σ κ,
    SteerSpec N.D (N.sb o b) rp b s σ κ ∧ rp.P = (ch j).req
  H_MUXJ : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ b, ∃ xp cp s σ κ E,
    MuxJSpec N.D (N.mj o b) xp cp b s σ κ E ∧ xp.P = (ch (if b then y else x)).req ∧
    cp.P = (ch cc).req
  H_MUXA : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ b, ∃ ap zp κ E,
    MuxASpec N.D (N.ma o b) ap zp κ E ∧ ap.drv = N.mj o b ∧ zp.P = (ch z).ack
  H_MUXD : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ i, ∃ p, BufSpec N.D (N.md o i) p
  H_SRC : ∀ o z w d, opAt o = .src z w d → ∃ ap, SrcSpec N.D (N.sr o) ap ∧ ap.P = (ch z).ack
  H_NDEC : ∀ o cc x0 x1 x2 z nw, opAt o = .muxn cc x0 x1 x2 z nw → ∀ k : Fin 3,
    ∃ cp s0 s1 σ κ, DecSpec N.D (N.nd o k) cp k.val s0 s1 σ κ ∧ cp.P = (ch cc).req
  H_NJ : ∀ o cc x0 x1 x2 z nw, opAt o = .muxn cc x0 x1 x2 z nw → ∀ k : Fin 3,
    ∃ (pv : Fin 2 → GPin N.ι) (E : Nat), CelSpec GC2 N.D (N.nj o k) pv E ∧
      (pv 0).P = (ch (mx x0 x1 x2 k)).req ∧ (pv 1).drv = N.nd o k
  H_NA : ∀ o cc x0 x1 x2 z nw, opAt o = .muxn cc x0 x1 x2 z nw → ∀ k : Fin 3,
    ∃ ap zp κ E, MuxASpec N.D (N.na o k) ap zp κ E ∧ ap.drv = N.nj o k ∧ zp.P = (ch z).ack
  H_NBUF : ∀ o cc x0 x1 x2 z nw, opAt o = .muxn cc x0 x1 x2 z nw → ∀ i : Fin 13, i.val < 2 →
    ∃ p, BufSpec N.D (N.nl o i) p
  H_TREE5 : ∀ o os, forkOuts (opAt o) = some os → os.length = 5 → ∃ pin lv E,
    Tree5 N.D (N.tr o 0) (N.tr o 1) pin lv E ∧ ∀ i : Fin 5, (lv i).P = (ch (os.getD i.val d0)).ack
  H_TREE6 : ∀ o os, forkOuts (opAt o) = some os → os.length = 6 → ∃ pa pb lv E,
    Tree6 N.D (N.tr o 0) (N.tr o 1) (N.tr o 2) pa pb lv E ∧
      ∀ i : Fin 6, (lv i).P = (ch (os.getD i.val d0)).ack
  H_REST : ∀ c, ¬ Tied3 N c → Contract N.D c

/-- The new specs give each new cell a segment contract, so `GcdNetOK3` contains
`GcdNetOK2`. -/
theorem GcdNetOK3.toOK2 {ch : Fin NC → Chan} {N : GcdNet3} (H : GcdNetOK3 ch N) :
    GcdNetOK2 ch N.toGcdNet2 := by
  refine ⟨H.NW, H.H_LINK, H.H_FORK, H.H_JOIN, H.H_STEER, H.H_MUXJ, H.H_MUXA, H.H_MUXD, H.H_SRC,
    fun c hc => ?_⟩
  by_cases h3 : Tied3 N c
  · rcases h3 with h | ⟨o, cc, x0, x1, x2, z, nw, k, ho, rfl | rfl | rfl⟩ |
      ⟨o, cc, x0, x1, x2, z, nw, i, ho, hi, rfl⟩ | ⟨o, os, i, ho, hl, rfl⟩
    · exact absurd h hc
    · obtain ⟨cp, s0, s1, σ, κ, S, _⟩ := H.H_NDEC o cc x0 x1 x2 z nw ho k
      exact ⟨fun j hA => dec_spec_cell S j hA, dec_spec_wait S⟩
    · obtain ⟨pv, E, S, _⟩ := H.H_NJ o cc x0 x1 x2 z nw ho k
      exact contract_of_cel H.NW S
    · obtain ⟨ap, zp, κ, E, S, _⟩ := H.H_NA o cc x0 x1 x2 z nw ho k
      exact ⟨fun j hA => muxa_spec_cell H.NW S j hA, muxa_spec_wait H.NW S⟩
    · obtain ⟨p, S⟩ := H.H_NBUF o cc x0 x1 x2 z nw ho i hi
      exact ⟨fun j hA => buf_spec_cell S j hA, buf_spec_wait H.NW S⟩
    · rcases hl with ⟨h5, hi⟩ | h6
      · obtain ⟨pin, lv, E, T, _⟩ := H.H_TREE5 o os ho h5
        obtain ⟨Sr, Sn⟩ := tree5_cel T
        match i, hi with
        | ⟨0, _⟩, _ => exact contract_of_cel H.NW Sr
        | ⟨1, _⟩, _ => exact contract_of_cel H.NW Sn
      · obtain ⟨pa, pb, lv, E, T, _⟩ := H.H_TREE6 o os ho h6
        obtain ⟨Sr, Sa, Sb⟩ := tree6_cel T
        match i with
        | ⟨0, _⟩ => exact contract_of_cel H.NW Sr
        | ⟨1, _⟩ => exact contract_of_cel H.NW Sa
        | ⟨2, _⟩ => exact contract_of_cel H.NW Sb
  · exact H.H_REST c h3

/-- **End to end, segment form, muxn and fork trees gate-modelled.** C's gcd_hw circuit
safety with `H_CELLS` of all 175 links discharged by ONE gate-level network (`GcdNetOK3`)
in which every cell carries B's gate model except (segment contracts): the 38 steer `uack`
and 21 mux `uor` ORs, the muxn's `|j` OR and its 11 FASTFALL line stages, and the cells of
the 9 amerges. Still assumed: the edge-time departure bounds and H_SP, C's `H_CELLS` of
the 192 non-link operators, H_BUNDLE, H_CM_FORCED.
CAVEAT (SelfAuditB9; audit P12b, 2026-10-31): the hypothesis does NOT bind the pin
drivers (`GPin.drv`) or the cell set to gcd_hw's netlist. A pinless cell's contract is
the bare claim that its node is clean (`fcellOK_nil_iff`), and a link fed by two such
cells gets its environment from them alone (`flink_env1_local`). So this theorem does not
enforce that any link's environment comes from the gate models named above; "gate-
modelled" describes the intended elaboration only. C's `H_CELLS` for the 192 non-link
operators stays a hypothesis (`H_OTHER`): B's gate models are used only to derive link
environments, never to discharge an operator contract. Driver-bound form: `FiniteNetBound`. -/
theorem gcd_hw_safe_net3 (a b : Nat) (ch : Fin NC → Chan) (N : GcdNet3) (H : GcdNetOK3 ch N)
    (H_OTHER : ∀ o : Fin NO, isLink (opAt o) = false → Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_CM_FORCED : ∃ y, Good a b y ∧ ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) :=
  gcd_hw_safe_net2 a b ch N.toGcdNet2 H.toOK2 H_OTHER H_BUNDLE H_CM_FORCED

/-! ## 3. Truncated form (runs that stop) -/

/-- Bfin2's elaboration plus the mux cells (`mj` joins, `ma` acknowledges, `md` delay
buffers, `mo` the `uor` OR), the muxn's cells and the tree nodes. -/
structure FGcdNet3 extends FGcdNet where
  mj : Fin NO → Bool → ι
  ma : Fin NO → Bool → ι
  md : Fin NO → Fin 2 → ι
  mo : Fin NO → ι
  nd : Fin NO → Fin 3 → ι
  nj : Fin NO → Fin 3 → ι
  na : Fin NO → Fin 3 → ι
  nl : Fin NO → Fin 13 → ι
  tr : Fin NO → Fin 3 → ι

def FTied3 (N : FGcdNet3) (c : N.ι) : Prop :=
  FTied N.toFGcdNet c ∨
  (∃ o cc x y z mw b, opAt o = .mux cc x y z mw ∧ (c = N.mj o b ∨ c = N.ma o b)) ∨
  (∃ o cc x y z mw i, opAt o = .mux cc x y z mw ∧ (c = N.md o i ∨ c = N.mo o)) ∨
  (∃ o cc x0 x1 x2 z nw k, opAt o = .muxn cc x0 x1 x2 z nw ∧
    (c = N.nd o k ∨ c = N.nj o k ∨ c = N.na o k)) ∨
  (∃ o cc x0 x1 x2 z nw i, opAt o = .muxn cc x0 x1 x2 z nw ∧ c = N.nl o i) ∨
  (∃ o os, ∃ i : Fin 3, forkOuts (opAt o) = some os ∧
    ((os.length = 5 ∧ i.val < 2) ∨ os.length = 6) ∧ c = N.tr o i)

/-- **The hypotheses, truncated form**: `FGcdNetOK`'s, plus the specs of the mux cells, the
muxn cells (line stages `0, 1` buffers, `2..12` FASTFALL ANDs gated by the `|j` cell `gp`)
and the tree nodes; a truncated contract only on the cells not in `FTied3`. -/
structure FGcdNetOK3 (ch : Fin NC → Chan) (N : FGcdNet3) (L : N.ι → Nat → Prop)
    (n : N.ι → Nat) : Prop where
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
  H_FMUXJ : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ b, ∃ xp cp s σ κ E,
    FMuxJSpec N.D L (N.mj o b) xp cp b s σ κ E ∧ xp.P = (ch (if b then y else x)).req ∧
    cp.P = (ch cc).req
  H_FMUXA : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ b, ∃ ap zp κ E,
    FMuxASpec N.D L (N.ma o b) ap zp κ E ∧ ap.drv = N.mj o b ∧ zp.P = (ch z).ack
  H_FMUXD : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ i, ∃ p, FBufSpec N.D L (N.md o i) p
  H_FMUXO : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∃ ap σ κ,
    FOrSpec N.D L (N.mo o) (fun a0 a1 => genF bd_mux_W2 "uor" .O ["j0", "j1"] [a0, a1]) ap σ κ
  H_FNDEC : ∀ o cc x0 x1 x2 z nw, opAt o = .muxn cc x0 x1 x2 z nw → ∀ k : Fin 3,
    ∃ cp s0 s1 σ κ, FDecSpec N.D L (N.nd o k) cp k.val s0 s1 σ κ ∧ cp.P = (ch cc).req
  H_FNJ : ∀ o cc x0 x1 x2 z nw, opAt o = .muxn cc x0 x1 x2 z nw → ∀ k : Fin 3,
    ∃ (pv : Fin 2 → GPin N.ι) (E : Nat), FCelSpec GC2 N.D L (N.nj o k) pv E ∧
      (pv 0).P = (ch (mx x0 x1 x2 k)).req ∧ (pv 1).drv = N.nd o k
  H_FNA : ∀ o cc x0 x1 x2 z nw, opAt o = .muxn cc x0 x1 x2 z nw → ∀ k : Fin 3,
    ∃ ap zp κ E, FMuxASpec N.D L (N.na o k) ap zp κ E ∧ ap.drv = N.nj o k ∧ zp.P = (ch z).ack
  H_FNBUF : ∀ o cc x0 x1 x2 z nw, opAt o = .muxn cc x0 x1 x2 z nw → ∀ i : Fin 13, i.val < 2 →
    ∃ p, FBufSpec N.D L (N.nl o i) p
  H_FNAND : ∀ o cc x0 x1 x2 z nw, opAt o = .muxn cc x0 x1 x2 z nw → ∀ i : Fin 13, 2 ≤ i.val →
    ∃ ap gp, FAndSpec N.D L (N.nl o i) ap gp
  H_FTREE5 : ∀ o os, forkOuts (opAt o) = some os → os.length = 5 → ∃ pin lv E,
    FTree5 N.D L (N.tr o 0) (N.tr o 1) pin lv E ∧
      ∀ i : Fin 5, (lv i).P = (ch (os.getD i.val d0)).ack
  H_FTREE6 : ∀ o os, forkOuts (opAt o) = some os → os.length = 6 → ∃ pa pb lv E,
    FTree6 N.D L (N.tr o 0) (N.tr o 1) (N.tr o 2) pa pb lv E ∧
      ∀ i : Fin 6, (lv i).P = (ch (os.getD i.val d0)).ack
  H_REST : ∀ c, ¬ FTied3 N c → FCellOK N.D L c

theorem FGcdNetOK3.toOK {ch : Fin NC → Chan} {N : FGcdNet3} {L : N.ι → Nat → Prop}
    {n : N.ι → Nat} (H : FGcdNetOK3 ch N L n) : FGcdNetOK ch N.toFGcdNet L n := by
  refine ⟨H.NW, H.H_FIN, H.H_LINK, H.H_FORK, H.H_JOIN, H.H_STEER, H.H_SOR, fun c hc => ?_⟩
  by_cases h3 : FTied3 N c
  · rcases h3 with h | ⟨o, cc, x, y, z, mw, b, ho, rfl | rfl⟩ |
      ⟨o, cc, x, y, z, mw, i, ho, rfl | rfl⟩ | ⟨o, cc, x0, x1, x2, z, nw, k, ho, rfl | rfl | rfl⟩ |
      ⟨o, cc, x0, x1, x2, z, nw, i, ho, rfl⟩ | ⟨o, os, i, ho, hl, rfl⟩
    · exact absurd h hc
    · obtain ⟨xp, cp, s, σ, κ, E, S, _⟩ := H.H_FMUXJ o cc x y z mw ho b
      exact fmuxj_spec_cell H.NW S
    · obtain ⟨ap, zp, κ, E, S, _⟩ := H.H_FMUXA o cc x y z mw ho b
      exact fmuxa_spec_cell H.NW S
    · obtain ⟨p, S⟩ := H.H_FMUXD o cc x y z mw ho i
      exact fbuf_spec_cell S
    · obtain ⟨ap, σ, κ, S⟩ := H.H_FMUXO o cc x y z mw ho
      exact for_spec_cell S
    · obtain ⟨cp, s0, s1, σ, κ, S, _⟩ := H.H_FNDEC o cc x0 x1 x2 z nw ho k
      exact fdec_spec_cell S
    · obtain ⟨pv, E, S, _⟩ := H.H_FNJ o cc x0 x1 x2 z nw ho k
      exact fcel_spec_cell H.NW S
    · obtain ⟨ap, zp, κ, E, S, _⟩ := H.H_FNA o cc x0 x1 x2 z nw ho k
      exact fmuxa_spec_cell H.NW S
    · by_cases hi : i.val < 2
      · obtain ⟨p, S⟩ := H.H_FNBUF o cc x0 x1 x2 z nw ho i hi
        exact fbuf_spec_cell S
      · obtain ⟨ap, gp, S⟩ := H.H_FNAND o cc x0 x1 x2 z nw ho i (by omega)
        exact fand_spec_cell S
    · rcases hl with ⟨h5, hi⟩ | h6
      · obtain ⟨pin, lv, E, T, _⟩ := H.H_FTREE5 o os ho h5
        obtain ⟨Sr, Sn⟩ := ftree5_cel T
        match i, hi with
        | ⟨0, _⟩, _ => exact fcel_spec_cell H.NW Sr
        | ⟨1, _⟩, _ => exact fcel_spec_cell H.NW Sn
      · obtain ⟨pa, pb, lv, E, T, _⟩ := H.H_FTREE6 o os ho h6
        obtain ⟨Sr, Sa, Sb⟩ := ftree6_cel T
        match i with
        | ⟨0, _⟩ => exact fcel_spec_cell H.NW Sr
        | ⟨1, _⟩ => exact fcel_spec_cell H.NW Sa
        | ⟨2, _⟩ => exact fcel_spec_cell H.NW Sb
  · exact H.H_REST c h3

/-- **End to end, runs that stop, mux, muxn and fork trees gate-modelled.** C's gcd_hw
circuit safety with every link's `H_CELLS` discharged by ONE gate-level network
(`FGcdNetOK3`, finite edge counts) in which every cell carries B's gate model except
(truncated contracts): the muxn's `|j` OR, the 3 sources, and the cells of the 9 amerges.
Still assumed: the edge-time bounds of `FGcdNetOK3`, C's `H_CELLS` (other 192 operators),
H_BUNDLE, H_CM_FORCED.
CAVEAT (SelfAuditB9; audit P12b, 2026-10-31): the hypothesis does NOT bind the pin
drivers (`GPin.drv`) or the cell set to gcd_hw's netlist. A pinless cell's contract is
the bare claim that its node is clean (`fcellOK_nil_iff`), and a link fed by two such
cells gets its environment from them alone (`flink_env1_local`). So this theorem does not
enforce that any link's environment comes from the gate models named above; "gate-
modelled" describes the intended elaboration only. C's `H_CELLS` for the 192 non-link
operators stays a hypothesis (`H_OTHER`): B's gate models are used only to derive link
environments, never to discharge an operator contract. Driver-bound form: `FiniteNetBound`. -/
theorem gcd_hw_safe_fin_net3 (a b : Nat) (ch : Fin NC → Chan) (N : FGcdNet3)
    (L : N.ι → Nat → Prop) (n : N.ι → Nat) (H : FGcdNetOK3 ch N L n)
    (H_OTHER : ∀ o : Fin NO, isLink (opAt o) = false → Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_CM_FORCED : ∃ y, Good a b y ∧ ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) :=
  gcd_hw_safe_fin_net a b ch N.toFGcdNet L n H.toOK H_OTHER H_BUNDLE H_CM_FORCED

end Formal.Cells.AssumeGuaranteeMuxNNet
