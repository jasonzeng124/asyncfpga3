import Formal.Cells.AssumeGuaranteeEndsNet
import Formal.Cells.AssumeGuaranteeCap

/-!
# Probe Bseg (shard B): gcd_hw's `CapstoneNet` as one mixed network, chain-end contracts gone

Bnet's `gcd_hw_safe_chains` replaced each link's `H_CELLS` by `InChain`: the link sits in a
chain of B's links whose two END cells (the producer at the head, the consumer at the
tail, 200 ends of the classes of `head_classes`/`tail_classes`) are assumed CONTRACTS. This
file states the capstone over ONE gate-level network for all of gcd_hw (`GcdNet`), in
which every link, every fork with N ≤ 4 outputs, every 2-input join (`join2`, `bjoin2`)
and both branches of every steer (`steerC`, `steerD`) carry B's GATE MODEL (`LinkSpec`,
`CelSpec` on the real `bd_c2`/`bd_c3`/`bd_c4`, `SteerSpec` on the real `bd_steer` `u`):
no environment hypothesis and no contract on them. Only the cells of the remaining
classes carry an assumed segment contract.

## Assumed / proved / NOT covered

**Proved (kernel `decide`, over C's `opAt`):** `op_classes`: of gcd_hw's 367 operators,
301 have every handshake cell gate-modelled here or are steers whose two branches are
(links 175; forks N ≤ 4: 41; joins N = 2: 47; steers: 38), and 66 are not (`join1` 11, a
wire with no cell; `mux` 21; `muxn` 1; `amerge` 9; `src` 3; `sink` 18; fork trees
`forkH5` 2, `forkH6` 1). `head_tied`/`tail_tied`: the chain-end neighbours by class.

**Proved:** `gcd_net_nodes` (every node of the network clean), `physLink_of_net` (Bfb2's
`PhysLink` of every link, with `Env1` DERIVED by `mixed_closed`/`link_spec_env1`), and
`gcd_hw_safe_net`: C's `gcd_hw_circuit_safe` with every link's `H_CELLS` discharged by the
network, NO `InChain` and no chain-end contract.

**Assumed (`GcdNetOK`):** B's gate model of every tied cell (above), with H_TIMES and its
departure bounds as EDGE-TIME inequalities; H_SEL_STABLE and a token enumeration per
steer branch; network-wide H_RST, H_WIRE, H_LUT_POS, H_SP; for each link the two outgoing
wires, H_WIRE_SPREAD and the latch data fields (as `PhysLink`); and a segment CONTRACT
(`Contract`) for every cell that is not tied: exactly the steers' acknowledge ORs (`uack`,
38), every cell of the 21 muxes, the muxn, the 9 arbiter merges, the 3 sources, the 18
sinks and the 3 fork trees (N = 5, 6). Outside: C's `H_CELLS` of the 192 non-link
operators, H_BUNDLE, H_CM_FORCED, as before.

**NOT covered:** this is NOT a strengthening of `gcd_hw_safe_chains` on every axis: the
departure bounds and wire spacing are assumed here as inequalities between edge times,
where `Chain` derives them from delay constants (H_RT); deriving them for a mixed network
is a path argument over each handshake cycle, not done. The gate-level elaboration (`ι`,
the pins' drivers) is abstract: the hypotheses fix the B model and the pin TRACES (C's
channel traces) of every tied cell, not the drivers. No non-vacuity witness of the whole
`GcdNetOK` (a live run of all of gcd_hw); the cell specs are witnessed in
`AssumeGuaranteeEnds` (`celG_witness`, `steer_seg_witness`) and Bnet's chain/fork
witnesses. Core Lean only.
-/

namespace Formal.Cells.AssumeGuaranteeEndsCap
open Formal.Cells
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe
open Formal.Cells.LutFbBridge2Env (isLink PhysLink gcd_hw_safe_phys_links Wire)
open Formal.Cells.AssumeGuaranteeCap (kname census linkIn linkOut heads tails)
open Formal.Cells.AssumeGuaranteeEnds (GPin gE GC2 GC3 GC4)
open Formal.Cells.AssumeGuaranteeEndsNet
open Formal.Cells.LutFbBridge (Phases)

/-! ## 1. The tied classes -/

def forkOuts : K NC → Option (List (Fin NC))
  | .forkG _ os => some os
  | .forkH _ os _ _ _ _ => some (os.map Prod.fst)
  | _ => none

def joinIns : K NC → Option (List (Fin NC))
  | .join ins _ _ _ _ => some ins
  | .bjoin ins _ _ _ => some ins
  | _ => none

def steerIn : K NC → Option (Fin NC)
  | .steerC j _ _ => some j
  | .steerD j _ _ _ _ => some j
  | _ => none

/-- An operator whose handshake cells are all gate-modelled here (steers: both branches;
their acknowledge OR is not). -/
def tiedOp (k : K NC) : Bool :=
  isLink k ||
  (match forkOuts k with | some os => 2 ≤ os.length && os.length ≤ 4 | none => false) ||
  (match joinIns k with | some ins => ins.length == 2 | none => false) ||
  (steerIn k).isSome

/-- **Census of gcd_hw's operators**: tied (gate-modelled) and not. -/
theorem op_classes :
    census (((List.finRange NO).filter (fun o => tiedOp (opAt o))).map (fun o => kname (opAt o)))
      = [("forkG2", 15), ("forkH2", 10), ("forkH3", 2), ("bjoin2", 38), ("steerD", 29),
         ("steerC", 9), ("forkG3", 6), ("join2", 9), ("forkH4", 7), ("forkG4", 1),
         ("link", 175)] ∧
    census (((List.finRange NO).filter (fun o => !tiedOp (opAt o))).map (fun o => kname (opAt o)))
      = [("join1", 11), ("sink", 18), ("mux", 21), ("forkH5", 2), ("forkH6", 1), ("muxn", 1),
         ("amerge", 9), ("src", 3)] := by
  decide +kernel

def tag (b : Bool) : String := if b then " tied" else " open"

/-- **Chain heads by the producer's class, tied or not.** -/
theorem head_tied :
    census (heads.map (fun o => match linkIn (opAt o) with
      | some i => kname (opAt (prodOf i)) ++ tag (tiedOp (opAt (prodOf i))) | none => "?")) =
      [("forkH2 tied", 12), ("steerD tied", 39), ("join2 tied", 4), ("forkG3 tied", 15),
       ("mux open", 9), ("steerC tied", 4), ("forkH4 tied", 9), ("forkG2 tied", 4),
       ("forkG4 tied", 4)] := by
  decide +kernel

/-- **Chain tails by the consumer's class, tied or not.** -/
theorem tail_tied :
    census (tails.map (fun o => match linkOut (opAt o) with
      | some c => kname (opAt (consOf c)) ++ tag (tiedOp (opAt (consOf c))) | none => "?")) =
      [("join1 open", 11), ("muxn open", 4), ("join2 tied", 17), ("mux open", 63),
       ("amerge open", 5)] := by
  decide +kernel

/-! ## 2. The gate-level network of gcd_hw -/

def d0 : Fin NC := ⟨0, by decide⟩

/-- The traces `sel` of the channels `cs` are the pins of a real `n`-pin C-element cell
(`bd_c2`, `bd_ctree` N = 3, `bd_c4`), in order. -/
def CelTie {ι : Type} (D : GD ι) (c : ι) (cs : List (Fin NC)) (sel : Fin NC → Nat → Bool) :
    Prop :=
  (cs.length = 2 ∧ ∃ (pv : Fin 2 → GPin ι) (E : Nat), CelSpec GC2 D c pv E ∧
    ∀ i, (pv i).P = sel (cs.getD i.val d0)) ∨
  (cs.length = 3 ∧ ∃ (pv : Fin 3 → GPin ι) (E : Nat), CelSpec GC3 D c pv E ∧
    ∀ i, (pv i).P = sel (cs.getD i.val d0)) ∨
  (cs.length = 4 ∧ ∃ (pv : Fin 4 → GPin ι) (E : Nat), CelSpec GC4 D c pv E ∧
    ∀ i, (pv i).P = sel (cs.getD i.val d0))

/-- **A gate-level elaboration of gcd_hw**: the cells, and which cell is the link
controller (`lk`), the fork acknowledge C-element (`fa`), the join request C-element
(`jr`) and the steer branch `b` (`sb`) of each operator. -/
structure GcdNet where
  ι : Type
  D : GD ι
  lk : Fin NO → ι
  fa : Fin NO → ι
  jr : Fin NO → ι
  sb : Fin NO → Bool → ι

/-- The cells that carry a B gate model. -/
def Tied (N : GcdNet) (c : N.ι) : Prop :=
  (∃ o i o', opAt o = .link i o' ∧ c = N.lk o) ∨
  (∃ o os, forkOuts (opAt o) = some os ∧ 2 ≤ os.length ∧ os.length ≤ 4 ∧ c = N.fa o) ∨
  (∃ o ins, joinIns (opAt o) = some ins ∧ ins.length = 2 ∧ c = N.jr o) ∨
  (∃ o j b, steerIn (opAt o) = some j ∧ c = N.sb o b)

/-- The link's outgoing wires, H_WIRE_SPREAD and latch data fields (as `PhysLink`). -/
def LinkOut {ι : Type} (D : GD ι) (c : ι) (i o : Chan) (Es Ea : Nat) : Prop :=
  ∃ wla wha wlr whr : Nat, Wire wla wha (D.O c) i.ack ∧ Wire wlr whr (D.O c) o.req ∧
    wha ≤ D.R ∧ whr ≤ D.R ∧ wha + D.hi c ≤ 2 * D.lo c + min Es Ea ∧
    whr + D.hi c ≤ 2 * D.lo c + min Es Ea ∧
    (∀ t, D.O c t = true → o.dat t = i.dat t) ∧
    (∀ t, D.O c (t + 1) = false → o.dat (t + 1) = o.dat t)

/-- **The hypotheses on the elaboration.** Tied cells: B's gate models with C's channel
traces as pins; every other cell: a segment contract. -/
structure GcdNetOK (ch : Fin NC → Chan) (N : GcdNet) : Prop where
  NW : NetW N.D
  H_LINK : ∀ o i o', opAt o = .link i o' → ∃ rp ap Es Ea, LinkSpec N.D (N.lk o) rp ap Es Ea ∧
    rp.P = (ch i).req ∧ ap.P = (ch o').ack ∧ LinkOut N.D (N.lk o) (ch i) (ch o') Es Ea
  H_FORK : ∀ o os, forkOuts (opAt o) = some os → 2 ≤ os.length → os.length ≤ 4 →
    CelTie N.D (N.fa o) os (fun c => (ch c).ack)
  H_JOIN : ∀ o ins, joinIns (opAt o) = some ins → ins.length = 2 →
    CelTie N.D (N.jr o) ins (fun c => (ch c).req)
  H_STEER : ∀ o j, steerIn (opAt o) = some j → ∀ b, ∃ rp s σ κ,
    SteerSpec N.D (N.sb o b) rp b s σ κ ∧ rp.P = (ch j).req
  H_REST : ∀ c, ¬ Tied N c → Contract N.D c

theorem celTie_proved {ι : Type} {D : GD ι} {c : ι} {cs : List (Fin NC)}
    {sel : Fin NC → Nat → Bool} (h : CelTie D c cs sel) : Proved D c := by
  rcases h with ⟨_, pv, E, S, _⟩ | ⟨_, pv, E, S, _⟩ | ⟨_, pv, E, S, _⟩
  · exact Or.inr (Or.inl ⟨2, GC2, pv, E, S⟩)
  · exact Or.inr (Or.inl ⟨3, GC3, pv, E, S⟩)
  · exact Or.inr (Or.inl ⟨4, GC4, pv, E, S⟩)

section net
variable {ch : Fin NC → Chan} {N : GcdNet} (H : GcdNetOK ch N)
include H

theorem gcd_cls (c : N.ι) : Proved N.D c ∨ Contract N.D c := by
  by_cases ht : Tied N c
  · refine Or.inl ?_
    rcases ht with ⟨o, i, o', h, rfl⟩ | ⟨o, os, h, h1, h2, rfl⟩ | ⟨o, ins, h, h1, rfl⟩ |
      ⟨o, j, b, h, rfl⟩
    · obtain ⟨rp, ap, Es, Ea, L, _⟩ := H.H_LINK o i o' h
      exact Or.inl ⟨rp, ap, Es, Ea, L⟩
    · exact celTie_proved (H.H_FORK o os h h1 h2)
    · exact celTie_proved (H.H_JOIN o ins h h1)
    · obtain ⟨rp, s, σ, κ, S, _⟩ := H.H_STEER o j h b
      exact Or.inr (Or.inr ⟨rp, b, s, σ, κ, S⟩)
  · exact Or.inr (H.H_REST c ht)

/-- **Every node of gcd_hw's gate-level network is a clean step signal.** -/
theorem gcd_net_nodes : ∀ c, Phases (N.D.O c) (N.D.τ c) :=
  mixed_closed N.D H.NW (gcd_cls H)

/-- **Every link of gcd_hw is Bfb2's `PhysLink`, its `Env1` DERIVED from the network.** -/
theorem physLink_of_net {o : Fin NO} {i o' : Fin NC} (h : opAt o = .link i o') :
    PhysLink (ch i) (ch o') := by
  obtain ⟨rp, ap, Es, Ea, L, e1, e2, wla, wha, wlr, whr, Wa, Wr, s1, s2, s3, s4, d1, d2⟩ :=
    H.H_LINK o i o' h
  obtain ⟨E, Tm⟩ := link_spec_env1 N.D H.NW (gcd_cls H) L
  have St := L.H_STAGE
  rw [e1, e2] at St E
  exact ⟨N.D.rst, N.D.O (N.lk o), N.D.qp (N.lk o), N.D.lo (N.lk o), N.D.hi (N.lk o),
    N.D.fl (N.lk o), N.D.fh (N.lk o), N.D.R, Es, Ea, wla, wha, wlr, whr, gE N.D.τ rp,
    Formal.Cells.LutFbBridge2Env.ash N.D.R (gE N.D.τ ap), St, E, Tm, H.NW.H_LUT_POS _,
    L.H_PWR, Wa, Wr, s1, s2, s3, s4, d1, d2⟩

end net

/-- **End to end, with NO chain-end contract.** C's gcd_hw circuit safety theorem
(`gcd_hw_circuit_safe`, via Bfb2's `gcd_hw_safe_phys_links`), with `H_CELLS` of all 175
links discharged by ONE gate-level network of gcd_hw (`GcdNetOK`) in which every link,
fork N ≤ 4, 2-input join and steer branch carries B's gate model, and only the cells
listed in `op_classes` as not tied (plus the steers' acknowledge ORs) carry an assumed
segment contract. Still assumed: the edge-time departure bounds and H_SP of `GcdNetOK`,
and C's `H_CELLS` (other 192 operators), H_BUNDLE, H_CM_FORCED. -/
theorem gcd_hw_safe_net (a b : Nat) (ch : Fin NC → Chan) (N : GcdNet) (H : GcdNetOK ch N)
    (H_OTHER : ∀ o : Fin NO, isLink (opAt o) = false → Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_CM_FORCED : ∃ y, Good a b y ∧ ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) :=
  gcd_hw_safe_phys_links a b ch (fun _ _ _ h => physLink_of_net H h) H_OTHER H_BUNDLE
    H_CM_FORCED

end Formal.Cells.AssumeGuaranteeEndsCap
