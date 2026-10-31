import Formal.Cells.FiniteNetMixed

/-!
# Probe Belab (shard B): gcd_hw's gate-level network with pin DRIVERS bound to the netlist

Answer to audit P12b (row 22) and SelfAuditB9: `FGcdNetOK` ties the pin TRACES of the tied
cells to C's channels but leaves every pin's driver (`GPin.drv`) free, so a link could take
its environment from a fresh pinless cell whose contract is the bare claim "my node is
clean" (`SelfAuditB9.flink_env1_local`). Here the drivers are fixed BY THE NETLIST.

* `reqSrc F c` / `ackSrc F c` compute, from C's generated gcd_hw netlist alone (`opAt`,
  `prodOf`, `consOf`), which elaboration cell drives channel `c`'s request / acknowledge:
  the producer's link controller, steer branch or join C-element (through 2..4-way forks,
  which are wires on the request side), resp. the consumer's link controller, steer OR or
  fork C-element (through 2-input joins, wires on the acknowledge side); `none` when the
  driver is an operator B does not gate-model (mux, muxn, amerge, source, sink, wide join,
  fork tree).
* `FGcdNetOKB`: `FGcdNetOK` plus, for every pin of every tied cell (link `rp`/`ap`, fork
  and join C-element pins, steer branch request pin, steer OR pins), `drv` = that cell
  whenever the netlist determines one (`BoundR`/`BoundA`); the steer OR's pins are also
  tied to C's branch acknowledge traces (absent from `FGcdNetOK`).

## Assumed / proved / NOT covered

**Proved:**
* `reqSrc_tied`, `ackSrc_tied`: a netlist-determined driver is a TIED cell (`FTied`), and
  `tied_pins_ne`: every tied cell of an `FGcdNetOK` network has a nonempty pin list, so its
  contract is a gate model, never the bare pinless claim.
* `link_env_bound`: for every link whose request and acknowledge drivers the netlist
  determines, both pin drivers are those tied cells (nonempty pins, B gate models); this is
  exactly what `FGcdNetOK` could not enforce.
* `bound_census`: of gcd_hw's 175 links, 63 have both drivers determined (both sides
  gate-modelled and enforced), 64 only the request side, 23 only the acknowledge side, 25
  neither (the other side is a mux, muxn, amerge, source, 1-input join or a fork / join chain
  ending at one); the kernel decides the counts.
* `gcd_hw_safe_fin_netB`: C's gcd_hw circuit safety under `FGcdNetOKB` (the proof is
  `gcd_hw_safe_fin_net` on the forgetful `toOK`; binding is a restriction of the
  hypothesis, so the conclusion is unchanged and the MEANING of the hypothesis is
  stronger).

**Assumed:** everything `FGcdNetOK` assumes (B's gate models of the tied cells, edge-time
equations and departure bounds, wires, finite edge counts, truncated contracts on the other
cells), plus the bindings; outside: C's `H_CELLS` for the 192 non-link operators
(`H_OTHER`), H_BUNDLE, H_CM_FORCED. The steer OR's pin `ap b` is bound to branch `b`
(`brC t f b`, the branch `steerF b` fires); the OR is symmetric, so the choice does not
change its gate.

**Joint witness (2026-10-31):** `BWitNet.gcd_hw_fin_netB_witness`, on a gate-timed run
(`BWitData`), not on C's unit-delay run chW, where it cannot exist (steers:
`FiniteNetSrc.chW_steer_unwired`). **NOT covered:** the witness is one run with unit LUT
delays (see `BWitNet`).
Contract cells (mux, muxn, amerge, sources, fork trees) may still be pinless: links next to
them get that side's environment from a contract, as counted by `bound_census`. Core Lean
only.
-/

namespace Formal.Cells.FiniteNetBound
open Formal.Cells
open Formal.Cells.FiniteNet
open Formal.Cells.WinFifo (Win)
open Formal.Cells.LutFbBridge2Env (Wire isLink)
open Formal.Cells.AssumeGuaranteeEnds (GPin GC2 GC3 GC4)
open Formal.Cells.AssumeGuaranteeEndsNet (GD)
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe
open Formal.Cells.AssumeGuaranteeEndsCap (GcdNet forkOuts joinIns steerIn d0 LinkOut)
open Formal.Net.Ops.Gen (genF)
open Formal.Gen Formal.Gen.Cells

/-! ## 1. The drivers the netlist determines -/

/-- An elaboration cell, named by its operator. -/
inductive DK
  | lk (o : Fin NO)
  | fa (o : Fin NO)
  | jr (o : Fin NO)
  | sb (o : Fin NO) (b : Bool)
  | ao (o : Fin NO)
  deriving DecidableEq, Repr

def DK.cell (N : FGcdNet) : DK → N.ι
  | .lk o => N.lk o
  | .fa o => N.fa o
  | .jr o => N.jr o
  | .sb o b => N.sb o b
  | .ao o => N.ao o

/-- A steer's input and branch channels. -/
def stJ : K NC → Option (Fin NC × Fin NC × Fin NC)
  | .steerC j t f => some (j, t, f)
  | .steerD j t f _ _ => some (j, t, f)
  | _ => none

/-- The steer's branch output channel (`FiniteNetSrc.brC`). -/
def brC (t f : Fin NC) (b : Bool) : Fin NC := if b then t else f

/-- A tied fork: 2..4 outputs (fork trees N ≥ 5 are not `FTied`). -/
def forkT : K NC → Option (Fin NC × List (Fin NC))
  | .forkG i os => if 2 ≤ os.length ∧ os.length ≤ 4 then some (i, os) else none
  | .forkH i os _ _ _ _ =>
      if 2 ≤ os.length ∧ os.length ≤ 4 then some (i, os.map Prod.fst) else none
  | _ => none

/-- A tied join: 2 inputs. -/
def joinT : K NC → Option (List (Fin NC) × Fin NC)
  | .join ins o _ _ _ => if ins.length = 2 then some (ins, o) else none
  | .bjoin ins o _ _ => if ins.length = 2 then some (ins, o) else none
  | _ => none

/-- **The cell that drives channel `c`'s request**, from the netlist (fuel `F` for fork
chains): the producer's link / steer branch / join; through a tied fork, the fork input's
driver; otherwise `none`. -/
def reqSrc : Nat → Fin NC → Option DK
  | 0, _ => none
  | F + 1, c =>
    let o := prodOf c
    match opAt o with
    | .link _ _ => some (.lk o)
    | .steerC _ t _ => some (.sb o (decide (c = t)))
    | .steerD _ t _ _ _ => some (.sb o (decide (c = t)))
    | .join ins _ _ _ _ => if ins.length = 2 then some (.jr o) else none
    | .bjoin ins _ _ _ => if ins.length = 2 then some (.jr o) else none
    | .forkG i os => if 2 ≤ os.length ∧ os.length ≤ 4 then reqSrc F i else none
    | .forkH i os _ _ _ _ => if 2 ≤ os.length ∧ os.length ≤ 4 then reqSrc F i else none
    | _ => none

/-- **The cell that drives channel `c`'s acknowledge**, from the netlist: the consumer's
link / steer OR / fork C-element; through a tied join, the join output's driver. -/
def ackSrc : Nat → Fin NC → Option DK
  | 0, _ => none
  | F + 1, c =>
    let o := consOf c
    match opAt o with
    | .link _ _ => some (.lk o)
    | .steerC _ _ _ => some (.ao o)
    | .steerD _ _ _ _ _ => some (.ao o)
    | .forkG _ os => if 2 ≤ os.length ∧ os.length ≤ 4 then some (.fa o) else none
    | .forkH _ os _ _ _ _ => if 2 ≤ os.length ∧ os.length ≤ 4 then some (.fa o) else none
    | .join ins z _ _ _ => if ins.length = 2 then ackSrc F z else none
    | .bjoin ins z _ _ => if ins.length = 2 then ackSrc F z else none
    | _ => none

/-- The fuel used throughout (longer than any fork / join chain of gcd_hw: `bound_census`
gives the same counts at `F` and `F + 8`). -/
abbrev FU : Nat := 16

/-! ## 2. Determined drivers are tied cells -/

theorem reqSrc_tied (N : FGcdNet) : ∀ (F : Nat) (c : Fin NC) (d : DK),
    reqSrc F c = some d → FTied N (d.cell N)
  | 0, _, _, h => by simp [reqSrc] at h
  | F + 1, c, d, h => by
    simp only [reqSrc] at h
    split at h
    · rename_i i o' e; cases h
      exact Or.inl ⟨prodOf c, i, o', e, rfl⟩
    · rename_i j t f e; cases h
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨prodOf c, j, _, by rw [e]; rfl, rfl⟩)))
    · rename_i j t f fd sw e; cases h
      exact Or.inr (Or.inr (Or.inr (Or.inl ⟨prodOf c, j, _, by rw [e]; rfl, rfl⟩)))
    · rename_i ins z ee js jw e
      split at h
      · rename_i hl; cases h
        exact Or.inr (Or.inr (Or.inl ⟨prodOf c, ins, by rw [e]; rfl, hl, rfl⟩))
      · cases h
    · rename_i ins z ec ed e
      split at h
      · rename_i hl; cases h
        exact Or.inr (Or.inr (Or.inl ⟨prodOf c, ins, by rw [e]; rfl, hl, rfl⟩))
      · cases h
    · split at h
      · exact reqSrc_tied N F _ d h
      · cases h
    · split at h
      · exact reqSrc_tied N F _ d h
      · cases h
    · cases h

theorem ackSrc_tied (N : FGcdNet) : ∀ (F : Nat) (c : Fin NC) (d : DK),
    ackSrc F c = some d → FTied N (d.cell N)
  | 0, _, _, h => by simp [ackSrc] at h
  | F + 1, c, d, h => by
    simp only [ackSrc] at h
    split at h
    · rename_i i o' e; cases h
      exact Or.inl ⟨consOf c, i, o', e, rfl⟩
    · rename_i j t f e; cases h
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨consOf c, j, by rw [e]; rfl, rfl⟩)))
    · rename_i j t f fd sw e; cases h
      exact Or.inr (Or.inr (Or.inr (Or.inr ⟨consOf c, j, by rw [e]; rfl, rfl⟩)))
    · rename_i i os e
      split at h
      · rename_i hl; cases h
        exact Or.inr (Or.inl ⟨consOf c, os, by rw [e]; rfl, hl.1, hl.2, rfl⟩)
      · cases h
    · rename_i i os l hh dd hs e
      split at h
      · rename_i hl; cases h
        exact Or.inr (Or.inl ⟨consOf c, os.map Prod.fst, by rw [e]; rfl,
          by simpa using hl.1, by simpa using hl.2, rfl⟩)
      · cases h
    · split at h
      · exact ackSrc_tied N F _ d h
      · cases h
    · split at h
      · exact ackSrc_tied N F _ d h
      · cases h
    · cases h

/-! ## 3. The driver-bound hypothesis -/

variable {ι : Type}

/-- Pin `p` reading channel `c`'s request has the netlist's driver (when it determines one). -/
def BoundR (N : FGcdNet) (c : Fin NC) (p : GPin N.ι) : Prop :=
  ∀ d, reqSrc FU c = some d → p.drv = d.cell N

/-- Pin `p` reading channel `c`'s acknowledge has the netlist's driver. -/
def BoundA (N : FGcdNet) (c : Fin NC) (p : GPin N.ι) : Prop :=
  ∀ d, ackSrc FU c = some d → p.drv = d.cell N

/-- `FCelTie` with every pin's driver bound by `bd`. -/
def FCelTieB (N : FGcdNet) (L : N.ι → Nat → Prop) (c : N.ι) (cs : List (Fin NC))
    (sel : Fin NC → Nat → Bool) (bd : Fin NC → GPin N.ι → Prop) : Prop :=
  (cs.length = 2 ∧ ∃ (pv : Fin 2 → GPin N.ι) (E : Nat), FCelSpec GC2 N.D L c pv E ∧
    ∀ i, (pv i).P = sel (cs.getD i.val d0) ∧ bd (cs.getD i.val d0) (pv i)) ∨
  (cs.length = 3 ∧ ∃ (pv : Fin 3 → GPin N.ι) (E : Nat), FCelSpec GC3 N.D L c pv E ∧
    ∀ i, (pv i).P = sel (cs.getD i.val d0) ∧ bd (cs.getD i.val d0) (pv i)) ∨
  (cs.length = 4 ∧ ∃ (pv : Fin 4 → GPin N.ι) (E : Nat), FCelSpec GC4 N.D L c pv E ∧
    ∀ i, (pv i).P = sel (cs.getD i.val d0) ∧ bd (cs.getD i.val d0) (pv i))

theorem FCelTieB.toTie {N : FGcdNet} {L : N.ι → Nat → Prop} {c : N.ι} {cs : List (Fin NC)}
    {sel : Fin NC → Nat → Bool} {bd : Fin NC → GPin N.ι → Prop}
    (h : FCelTieB N L c cs sel bd) : FCelTie N.D L c cs sel := by
  rcases h with ⟨l, pv, E, S, hp⟩ | ⟨l, pv, E, S, hp⟩ | ⟨l, pv, E, S, hp⟩
  · exact Or.inl ⟨l, pv, E, S, fun i => (hp i).1⟩
  · exact Or.inr (Or.inl ⟨l, pv, E, S, fun i => (hp i).1⟩)
  · exact Or.inr (Or.inr ⟨l, pv, E, S, fun i => (hp i).1⟩)

/-- **The driver-bound elaboration hypotheses** (`FGcdNetOK` with every tied cell's pins
bound to the netlist's drivers). -/
structure FGcdNetOKB (ch : Fin NC → Chan) (N : FGcdNet) (L : N.ι → Nat → Prop)
    (n : N.ι → Nat) : Prop where
  NW : FNetW N.D L
  H_FIN : ∀ c j, L c j ↔ j < n c
  H_LINK : ∀ o i o', opAt o = .link i o' → ∃ rp ap Es Ea, FLinkSpec N.D L (N.lk o) rp ap Es Ea ∧
    rp.P = (ch i).req ∧ ap.P = (ch o').ack ∧ LinkOut N.D (N.lk o) (ch i) (ch o') Es Ea ∧
    BoundR N i rp ∧ BoundA N o' ap
  H_FORK : ∀ o os, forkOuts (opAt o) = some os → 2 ≤ os.length → os.length ≤ 4 →
    FCelTieB N L (N.fa o) os (fun c => (ch c).ack) (BoundA N)
  H_JOIN : ∀ o ins, joinIns (opAt o) = some ins → ins.length = 2 →
    FCelTieB N L (N.jr o) ins (fun c => (ch c).req) (BoundR N)
  H_STEER : ∀ o j, steerIn (opAt o) = some j → ∀ b, ∃ rp s σ κ,
    FSteerSpec N.D L (N.sb o b) rp b s σ κ ∧ rp.P = (ch j).req ∧ BoundR N j rp
  H_SOR : ∀ o j t f, stJ (opAt o) = some (j, t, f) → ∃ ap σ κ,
    FOrSpec N.D L (N.ao o) (fun a0 a1 => genF bd_steer "uack" .O ["ack0", "ack1"] [a0, a1])
      ap σ κ ∧ ∀ b, (ap b).P = (ch (brC t f b)).ack ∧ BoundA N (brC t f b) (ap b)
  H_REST : ∀ c, ¬ FTied N c → FCellOK N.D L c

theorem stJ_of_steerIn {k : K NC} {j : Fin NC} (h : steerIn k = some j) :
    ∃ t f, stJ k = some (j, t, f) := by
  cases k <;> simp [steerIn] at h
  all_goals (subst h; exact ⟨_, _, rfl⟩)

/-- Forgetting the bindings gives `FGcdNetOK`. -/
theorem FGcdNetOKB.toOK {ch : Fin NC → Chan} {N : FGcdNet} {L : N.ι → Nat → Prop}
    {n : N.ι → Nat} (H : FGcdNetOKB ch N L n) : FGcdNetOK ch N L n where
  NW := H.NW
  H_FIN := H.H_FIN
  H_LINK := fun o i o' h => by
    obtain ⟨rp, ap, Es, Ea, S, e1, e2, lo, _⟩ := H.H_LINK o i o' h
    exact ⟨rp, ap, Es, Ea, S, e1, e2, lo⟩
  H_FORK := fun o os h h1 h2 => (H.H_FORK o os h h1 h2).toTie
  H_JOIN := fun o ins h h1 => (H.H_JOIN o ins h h1).toTie
  H_STEER := fun o j h b => by
    obtain ⟨rp, s, σ, κ, S, e, _⟩ := H.H_STEER o j h b
    exact ⟨rp, s, σ, κ, S, e⟩
  H_SOR := fun o j h => by
    obtain ⟨t, f, hs⟩ := stJ_of_steerIn h
    obtain ⟨ap, σ, κ, S, _⟩ := H.H_SOR o j t f hs
    exact ⟨ap, σ, κ, S⟩
  H_REST := H.H_REST

/-! ## 4. What the binding buys: tied drivers have pins -/

theorem fcelTie_pins_ne {D : GD ι} {L : ι → Nat → Prop} {c : ι} {cs : List (Fin NC)}
    {sel : Fin NC → Nat → Bool} (h : FCelTie D L c cs sel) : D.pins c ≠ [] := by
  rcases h with ⟨_, pv, E, S, _⟩ | ⟨_, pv, E, S, _⟩ | ⟨_, pv, E, S, _⟩ <;>
    (rw [S.H_PINS]; simp [List.finRange_succ])

/-- **Every tied cell of an `FGcdNetOK` network has pins**: its contract is a B gate model
(`fgcd_cls`), never the bare claim a pinless cell's contract reduces to. -/
theorem tied_pins_ne {ch : Fin NC → Chan} {N : FGcdNet} {L : N.ι → Nat → Prop}
    {n : N.ι → Nat} (H : FGcdNetOK ch N L n) {c : N.ι} (ht : FTied N c) : N.D.pins c ≠ [] := by
  rcases ht with ⟨o, i, o', h, rfl⟩ | ⟨o, os, h, h1, h2, rfl⟩ | ⟨o, ins, h, h1, rfl⟩ |
      ⟨o, j, b, h, rfl⟩ | ⟨o, j, h, rfl⟩
  · obtain ⟨rp, ap, Es, Ea, S, _⟩ := H.H_LINK o i o' h
    rw [S.H_PINS]; simp
  · exact fcelTie_pins_ne (H.H_FORK o os h h1 h2)
  · exact fcelTie_pins_ne (H.H_JOIN o ins h h1)
  · obtain ⟨rp, s, σ, κ, S, _⟩ := H.H_STEER o j h b
    rw [S.H_PINS]; simp
  · obtain ⟨ap, σ, κ, S⟩ := H.H_SOR o j h
    rw [S.H_PINS]; simp

/-- **A link's environment comes from the netlist's gate models**, wherever the netlist
determines its drivers: the request pin's driver is the cell `reqSrc` names, the
acknowledge pin's driver the cell `ackSrc` names; both are tied cells with pins (B gate
models). Under `FGcdNetOK` alone both drivers are free. -/
theorem link_env_bound {ch : Fin NC → Chan} {N : FGcdNet} {L : N.ι → Nat → Prop}
    {n : N.ι → Nat} (H : FGcdNetOKB ch N L n) {o : Fin NO} {i o' : Fin NC}
    (h : opAt o = .link i o') {dr da : DK} (hr : reqSrc FU i = some dr)
    (ha : ackSrc FU o' = some da) :
    ∃ rp ap Es Ea, FLinkSpec N.D L (N.lk o) rp ap Es Ea ∧ rp.P = (ch i).req ∧
      ap.P = (ch o').ack ∧ rp.drv = dr.cell N ∧ ap.drv = da.cell N ∧
      FTied N (dr.cell N) ∧ FTied N (da.cell N) ∧
      N.D.pins (dr.cell N) ≠ [] ∧ N.D.pins (da.cell N) ≠ [] := by
  obtain ⟨rp, ap, Es, Ea, S, e1, e2, _, br, ba⟩ := H.H_LINK o i o' h
  have tr := reqSrc_tied N FU i dr hr
  have ta := ackSrc_tied N FU o' da ha
  exact ⟨rp, ap, Es, Ea, S, e1, e2, br dr hr, ba da ha, tr, ta,
    tied_pins_ne H.toOK tr, tied_pins_ne H.toOK ta⟩

/-! ## 5. Census: which links are bound on both sides -/

/-- For each link: (request driver determined, acknowledge driver determined). -/
def linkSides (F : Nat) : List (Bool × Bool) :=
  (List.finRange NO).filterMap fun o => match opAt o with
    | .link i o' => some ((reqSrc F i).isSome, (ackSrc F o').isSome)
    | _ => none

def nLinks : Nat := (linkSides FU).length
def nBoth : Nat := ((linkSides FU).filter fun p => p.1 && p.2).length
def nReqOnly : Nat := ((linkSides FU).filter fun p => p.1 && !p.2).length
def nAckOnly : Nat := ((linkSides FU).filter fun p => !p.1 && p.2).length
def nNone : Nat := ((linkSides FU).filter fun p => !p.1 && !p.2).length

set_option maxRecDepth 100000

theorem census_len : nLinks = 175 := by decide +kernel
theorem census_both : nBoth = 63 := by decide +kernel
theorem census_req : nReqOnly = 64 := by decide +kernel
theorem census_ack : nAckOnly = 23 := by decide +kernel
theorem census_none : nNone = 25 := by decide +kernel
theorem census_fuel : linkSides FU = linkSides (FU + 8) := by decide +kernel

/-- **Census** (kernel): the side counts over gcd_hw's links (both / request only /
acknowledge only / neither), and fuel `FU` already saturates (same table at `FU + 8`). -/
theorem bound_census :
    nLinks = 175 ∧ nBoth = 63 ∧ nReqOnly = 64 ∧ nAckOnly = 23 ∧ nNone = 25 ∧
    linkSides FU = linkSides (FU + 8) :=
  ⟨census_len, census_both, census_req, census_ack, census_none, census_fuel⟩

/-! ## 6. The capstone, driver-bound -/

/-- **End to end, runs that stop, drivers bound to the netlist.** C's gcd_hw circuit safety
with every link's `H_CELLS` discharged by ONE gate-level network whose tied cells' pins are
wired to the cells the netlist names (`FGcdNetOKB`; `link_env_bound`). Still assumed: the
edge-time bounds of `FGcdNetOK`, contracts on the untied cells (mux, muxn, amerge,
sources, fork trees), C's `H_CELLS` for the other 192 operators (`H_OTHER`), H_BUNDLE,
H_CM_FORCED. Jointly satisfiable: `BWitNet.gcd_hw_fin_netB_witness`. -/
theorem gcd_hw_safe_fin_netB (a b : Nat) (ch : Fin NC → Chan) (N : FGcdNet)
    (L : N.ι → Nat → Prop) (n : N.ι → Nat) (H : FGcdNetOKB ch N L n)
    (H_OTHER : ∀ o : Fin NO, isLink (opAt o) = false → Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_CM_FORCED : ∃ y, Good a b y ∧ ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) :=
  gcd_hw_safe_fin_net a b ch N L n H.toOK H_OTHER H_BUNDLE H_CM_FORCED

end Formal.Cells.FiniteNetBound
