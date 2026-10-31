import Formal.Cells.FiniteNetBound
import Formal.Cells.AssumeGuaranteeMuxNFin

/-!
# Probe Belab2 (shard B): the driver-bound gate-level network with `bd_mux` gate-modelled

`FiniteNetBound` binds the pin drivers of links, forks N ≤ 4, 2-input joins and steers to the
cells the netlist names. Its census: 63 of 175 links bound on both sides; the most common
unbound side is a mux. Here every `bd_mux` is gate-modelled too (its 2 joins `uj0`/`uj1`, the
OR `uor`, the 2 `udly` buffers, the 2 acknowledges `uxa`/`uya`, Bmn's truncated specs), with
every mux pin bound as well:

* a mux output request is driven by the mux's last `udly` buffer; a mux input acknowledge by
  its `uxa`/`uya`; the control's acknowledge is `z_ack` (a wire), so its driver is `z`'s
  (`reqSrcM`, `ackSrcM`);
* inside the mux: `uor` reads the two join nodes, `udly[0]` reads `uor`, `udly[1]` reads
  `udly[0]`, `uxa`/`uya` read their join's node and `z`'s acknowledge.

## Assumed / proved / NOT covered

**Proved:** `bound_censusM` (kernel): with muxes, 124 of 175 links are bound on both sides;
`FGcdNetOKBM.toOK` (the mux cells' truncated contracts follow from their specs:
`fmuxj_spec_cell`, `fmuxa_spec_cell`, `for_spec_cell`, `fbuf_spec_cell`); `link_env_boundM`;
`gcd_hw_safe_fin_netBM`: C's gcd_hw circuit safety under `FGcdNetOKBM` plus C's H_OTHER,
H_BUNDLE, H_CM_FORCED.

**Assumed:** `FGcdNetOKB`'s fields with the extended bindings, plus Bmn's mux specs
(`FMuxJSpec`, `FMuxASpec`, `FOrSpec` with the real `uor`, `FBufSpec`), H_TIMES at existing
edges; contracts on muxn, amerge, sources, sinks, wide joins, fork trees.

**NOT covered:** a joint witness of `FGcdNetOKBM` (Python evidence only:
`tools-B/bwit/bsim2.py`); C's H_OTHER stays for the 192 non-link operators. Core Lean only.
-/

namespace Formal.Cells.FiniteNetBoundM
open Formal.Cells
open Formal.Cells.FiniteNet
open Formal.Cells.FiniteNetBound
open Formal.Cells.AssumeGuaranteeMuxNFin
open Formal.Cells.LutFbBridge2Env (Wire isLink)
open Formal.Cells.AssumeGuaranteeEnds (GPin GC2 GC3 GC4)
open Formal.Cells.AssumeGuaranteeEndsNet (GD)
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapSafe
open Formal.Cells.AssumeGuaranteeEndsCap (GcdNet forkOuts joinIns steerIn d0 LinkOut)
open Formal.Net.Ops.Gen (genF)
open Formal.Gen Formal.Gen.Cells

/-! ## 1. The elaboration and the drivers -/

/-- `FiniteNetMixed.FGcdNet` plus the cells of every `bd_mux`. -/
structure FGcdNetM extends FGcdNet where
  mj : Fin NO → Bool → ι
  ma : Fin NO → Bool → ι
  md : Fin NO → Fin 2 → ι
  mo : Fin NO → ι

inductive DKM
  | base (d : DK)
  | md (o : Fin NO) (i : Fin 2)
  | ma (o : Fin NO) (b : Bool)
  deriving DecidableEq, Repr

def DKM.cell (N : FGcdNetM) : DKM → N.ι
  | .base d => d.cell N.toFGcdNet
  | .md o i => N.md o i
  | .ma o b => N.ma o b

/-- A mux's channels: (control, x, y, z). -/
def muxC : K NC → Option (Fin NC × Fin NC × Fin NC × Fin NC)
  | .mux c x y z _ => some (c, x, y, z)
  | _ => none

/-- **Request driver**, with muxes: a mux output request is driven by its last `udly`. -/
def reqSrcM : Nat → Fin NC → Option DKM
  | 0, _ => none
  | F + 1, c =>
    let o := prodOf c
    match opAt o with
    | .link _ _ => some (.base (.lk o))
    | .steerC _ t _ => some (.base (.sb o (decide (c = t))))
    | .steerD _ t _ _ _ => some (.base (.sb o (decide (c = t))))
    | .join ins _ _ _ _ => if ins.length = 2 then some (.base (.jr o)) else none
    | .bjoin ins _ _ _ => if ins.length = 2 then some (.base (.jr o)) else none
    | .forkG i os => if 2 ≤ os.length ∧ os.length ≤ 4 then reqSrcM F i else none
    | .forkH i os _ _ _ _ => if 2 ≤ os.length ∧ os.length ≤ 4 then reqSrcM F i else none
    | .mux _ _ _ _ _ => some (.md o 1)
    | _ => none

/-- **Acknowledge driver**, with muxes: `uxa`/`uya` for the data inputs; the control's
acknowledge is `z_ack`, so through the mux to `z`'s driver. -/
def ackSrcM : Nat → Fin NC → Option DKM
  | 0, _ => none
  | F + 1, c =>
    let o := consOf c
    match opAt o with
    | .link _ _ => some (.base (.lk o))
    | .steerC _ _ _ => some (.base (.ao o))
    | .steerD _ _ _ _ _ => some (.base (.ao o))
    | .forkG _ os => if 2 ≤ os.length ∧ os.length ≤ 4 then some (.base (.fa o)) else none
    | .forkH _ os _ _ _ _ => if 2 ≤ os.length ∧ os.length ≤ 4 then some (.base (.fa o)) else none
    | .join ins z _ _ _ => if ins.length = 2 then ackSrcM F z else none
    | .bjoin ins z _ _ => if ins.length = 2 then ackSrcM F z else none
    | .mux cc _ y z _ => if c = cc then ackSrcM F z else some (.ma o (decide (c = y)))
    | _ => none

/-- The cells that carry a B gate model, with the mux cells. -/
def FTiedM (N : FGcdNetM) (c : N.ι) : Prop :=
  FTied N.toFGcdNet c ∨
  (∃ o cc x y z mw, opAt o = .mux cc x y z mw ∧
    ((∃ b, c = N.mj o b ∨ c = N.ma o b) ∨ (∃ i, c = N.md o i) ∨ c = N.mo o))

theorem reqSrcM_tied (N : FGcdNetM) : ∀ (F : Nat) (c : Fin NC) (d : DKM),
    reqSrcM F c = some d → FTiedM N (d.cell N)
  | 0, _, _, h => by simp [reqSrcM] at h
  | F + 1, c, d, h => by
    simp only [reqSrcM] at h
    split at h
    · rename_i i o' e; cases h
      exact Or.inl (Or.inl ⟨prodOf c, i, o', e, rfl⟩)
    · rename_i j t f e; cases h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨prodOf c, j, _, by rw [e]; rfl, rfl⟩))))
    · rename_i j t f fd sw e; cases h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inl ⟨prodOf c, j, _, by rw [e]; rfl, rfl⟩))))
    · rename_i ins z ee js jw e
      split at h
      · rename_i hl; cases h
        exact Or.inl (Or.inr (Or.inr (Or.inl ⟨prodOf c, ins, by rw [e]; rfl, hl, rfl⟩)))
      · cases h
    · rename_i ins z ec ed e
      split at h
      · rename_i hl; cases h
        exact Or.inl (Or.inr (Or.inr (Or.inl ⟨prodOf c, ins, by rw [e]; rfl, hl, rfl⟩)))
      · cases h
    · split at h
      · exact reqSrcM_tied N F _ d h
      · cases h
    · split at h
      · exact reqSrcM_tied N F _ d h
      · cases h
    · rename_i cc x y z mw e; cases h
      exact Or.inr ⟨prodOf c, cc, x, y, z, mw, e, Or.inr (Or.inl ⟨1, rfl⟩)⟩
    · cases h

theorem ackSrcM_tied (N : FGcdNetM) : ∀ (F : Nat) (c : Fin NC) (d : DKM),
    ackSrcM F c = some d → FTiedM N (d.cell N)
  | 0, _, _, h => by simp [ackSrcM] at h
  | F + 1, c, d, h => by
    simp only [ackSrcM] at h
    split at h
    · rename_i i o' e; cases h
      exact Or.inl (Or.inl ⟨consOf c, i, o', e, rfl⟩)
    · rename_i j t f e; cases h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨consOf c, j, by rw [e]; rfl, rfl⟩))))
    · rename_i j t f fd sw e; cases h
      exact Or.inl (Or.inr (Or.inr (Or.inr (Or.inr ⟨consOf c, j, by rw [e]; rfl, rfl⟩))))
    · rename_i i os e
      split at h
      · rename_i hl; cases h
        exact Or.inl (Or.inr (Or.inl ⟨consOf c, os, by rw [e]; rfl, hl.1, hl.2, rfl⟩))
      · cases h
    · rename_i i os l hh dd hs e
      split at h
      · rename_i hl; cases h
        exact Or.inl (Or.inr (Or.inl ⟨consOf c, os.map Prod.fst, by rw [e]; rfl,
          by simpa using hl.1, by simpa using hl.2, rfl⟩))
      · cases h
    · split at h
      · exact ackSrcM_tied N F _ d h
      · cases h
    · split at h
      · exact ackSrcM_tied N F _ d h
      · cases h
    · rename_i cc x y z mw e
      split at h
      · exact ackSrcM_tied N F _ d h
      · cases h
        exact Or.inr ⟨consOf c, cc, x, y, z, mw, e, Or.inl ⟨_, Or.inr rfl⟩⟩
    · cases h

/-! ## 2. The hypothesis -/

def BoundRM (N : FGcdNetM) (c : Fin NC) (p : GPin N.ι) : Prop :=
  ∀ d, reqSrcM FU c = some d → p.drv = d.cell N

def BoundAM (N : FGcdNetM) (c : Fin NC) (p : GPin N.ι) : Prop :=
  ∀ d, ackSrcM FU c = some d → p.drv = d.cell N

/-- The `uor` LUT of `bd_mux`. -/
def uorF (a0 a1 : Bool) : Bool := genF bd_mux_W2 "uor" .O ["j0", "j1"] [a0, a1]

/-- **The driver-bound hypotheses, with muxes.** -/
structure FGcdNetOKBM (ch : Fin NC → Chan) (N : FGcdNetM) (L : N.ι → Nat → Prop)
    (n : N.ι → Nat) : Prop where
  NW : FNetW N.D L
  H_FIN : ∀ c j, L c j ↔ j < n c
  H_LINK : ∀ o i o', opAt o = .link i o' → ∃ rp ap Es Ea, FLinkSpec N.D L (N.lk o) rp ap Es Ea ∧
    rp.P = (ch i).req ∧ ap.P = (ch o').ack ∧ LinkOut N.D (N.lk o) (ch i) (ch o') Es Ea ∧
    BoundRM N i rp ∧ BoundAM N o' ap
  H_FORK : ∀ o os, forkOuts (opAt o) = some os → 2 ≤ os.length → os.length ≤ 4 →
    FCelTieB N.toFGcdNet L (N.fa o) os (fun c => (ch c).ack) (BoundAM N)
  H_JOIN : ∀ o ins, joinIns (opAt o) = some ins → ins.length = 2 →
    FCelTieB N.toFGcdNet L (N.jr o) ins (fun c => (ch c).req) (BoundRM N)
  H_STEER : ∀ o j, steerIn (opAt o) = some j → ∀ b, ∃ rp s σ κ,
    FSteerSpec N.D L (N.sb o b) rp b s σ κ ∧ rp.P = (ch j).req ∧ BoundRM N j rp
  H_SOR : ∀ o j t f, stJ (opAt o) = some (j, t, f) → ∃ ap σ κ,
    FOrSpec N.D L (N.ao o) (fun a0 a1 => genF bd_steer "uack" .O ["ack0", "ack1"] [a0, a1])
      ap σ κ ∧ ∀ b, (ap b).P = (ch (brC t f b)).ack ∧ BoundAM N (brC t f b) (ap b)
  H_MUXJ : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ b, ∃ xp cp s σ κ E,
    FMuxJSpec N.D L (N.mj o b) xp cp b s σ κ E ∧ xp.P = (ch (if b then y else x)).req ∧
    cp.P = (ch cc).req ∧ BoundRM N (if b then y else x) xp ∧ BoundRM N cc cp
  H_MUXA : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ b, ∃ ap zp κ E,
    FMuxASpec N.D L (N.ma o b) ap zp κ E ∧ ap.drv = N.mj o b ∧ zp.P = (ch z).ack ∧
    BoundAM N z zp
  H_MUXO : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∃ ap σ κ,
    FOrSpec N.D L (N.mo o) uorF ap σ κ ∧ ∀ b, (ap b).drv = N.mj o b
  H_MUXD : ∀ o cc x y z mw, opAt o = .mux cc x y z mw → ∀ i : Fin 2, ∃ p,
    FBufSpec N.D L (N.md o i) p ∧ p.drv = (if i.val = 0 then N.mo o else N.md o 0)
  H_REST : ∀ c, ¬ FTiedM N c → FCellOK N.D L c

/-- Forgetting the bindings, with the mux cells' contracts from their specs. -/
theorem FGcdNetOKBM.toOK {ch : Fin NC → Chan} {N : FGcdNetM} {L : N.ι → Nat → Prop}
    {n : N.ι → Nat} (H : FGcdNetOKBM ch N L n) : FGcdNetOK ch N.toFGcdNet L n where
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
  H_REST := fun c hc => by
    by_cases hm : FTiedM N c
    · rcases hm with h | ⟨o, cc, x, y, z, mw, ho, ⟨b, rfl | rfl⟩ | ⟨i, rfl⟩ | rfl⟩
      · exact absurd h hc
      · obtain ⟨xp, cp, s, σ, κ, E, S, _⟩ := H.H_MUXJ o cc x y z mw ho b
        exact fmuxj_spec_cell H.NW S
      · obtain ⟨ap, zp, κ, E, S, _⟩ := H.H_MUXA o cc x y z mw ho b
        exact fmuxa_spec_cell H.NW S
      · obtain ⟨p, S, _⟩ := H.H_MUXD o cc x y z mw ho i
        exact fbuf_spec_cell S
      · obtain ⟨ap, σ, κ, S, _⟩ := H.H_MUXO o cc x y z mw ho
        exact for_spec_cell S
    · exact H.H_REST c hm

/-! ## 3. What the binding buys -/

theorem fcelTie_pins_ne' {ι : Type} {D : GD ι} {L : ι → Nat → Prop} {c : ι} {cs : List (Fin NC)}
    {sel : Fin NC → Nat → Bool} (h : FCelTie D L c cs sel) : D.pins c ≠ [] := by
  rcases h with ⟨_, pv, E, S, _⟩ | ⟨_, pv, E, S, _⟩ | ⟨_, pv, E, S, _⟩ <;>
    (rw [S.H_PINS]; simp [List.finRange_succ])

/-- Every tied cell (muxes included) has pins. -/
theorem tiedM_pins_ne {ch : Fin NC → Chan} {N : FGcdNetM} {L : N.ι → Nat → Prop}
    {n : N.ι → Nat} (H : FGcdNetOKBM ch N L n) {c : N.ι} (ht : FTiedM N c) :
    N.D.pins c ≠ [] := by
  rcases ht with ht | ⟨o, cc, x, y, z, mw, ho, ⟨b, rfl | rfl⟩ | ⟨i, rfl⟩ | rfl⟩
  · exact tied_pins_ne H.toOK ht
  · obtain ⟨xp, cp, s, σ, κ, E, S, _⟩ := H.H_MUXJ o cc x y z mw ho b
    rw [S.H_PINS]; simp
  · obtain ⟨ap, zp, κ, E, S, _⟩ := H.H_MUXA o cc x y z mw ho b
    rw [S.H_PINS]; simp
  · obtain ⟨p, S, _⟩ := H.H_MUXD o cc x y z mw ho i
    rw [S.H_PINS]; simp
  · obtain ⟨ap, σ, κ, S, _⟩ := H.H_MUXO o cc x y z mw ho
    rw [S.H_PINS]; simp

/-- **A link's environment from gate models**, muxes included. -/
theorem link_env_boundM {ch : Fin NC → Chan} {N : FGcdNetM} {L : N.ι → Nat → Prop}
    {n : N.ι → Nat} (H : FGcdNetOKBM ch N L n) {o : Fin NO} {i o' : Fin NC}
    (h : opAt o = .link i o') {dr da : DKM} (hr : reqSrcM FU i = some dr)
    (ha : ackSrcM FU o' = some da) :
    ∃ rp ap Es Ea, FLinkSpec N.D L (N.lk o) rp ap Es Ea ∧ rp.P = (ch i).req ∧
      ap.P = (ch o').ack ∧ rp.drv = dr.cell N ∧ ap.drv = da.cell N ∧
      FTiedM N (dr.cell N) ∧ FTiedM N (da.cell N) ∧
      N.D.pins (dr.cell N) ≠ [] ∧ N.D.pins (da.cell N) ≠ [] := by
  obtain ⟨rp, ap, Es, Ea, S, e1, e2, _, br, ba⟩ := H.H_LINK o i o' h
  have tr := reqSrcM_tied N FU i dr hr
  have ta := ackSrcM_tied N FU o' da ha
  exact ⟨rp, ap, Es, Ea, S, e1, e2, br dr hr, ba da ha, tr, ta, tiedM_pins_ne H tr,
    tiedM_pins_ne H ta⟩

/-! ## 4. Census -/

def linkSidesM (F : Nat) : List (Bool × Bool) :=
  (List.finRange NO).filterMap fun o => match opAt o with
    | .link i o' => some ((reqSrcM F i).isSome, (ackSrcM F o').isSome)
    | _ => none

def nBothM : Nat := ((linkSidesM FU).filter fun p => p.1 && p.2).length
def nReqOnlyM : Nat := ((linkSidesM FU).filter fun p => p.1 && !p.2).length
def nAckOnlyM : Nat := ((linkSidesM FU).filter fun p => !p.1 && p.2).length
def nNoneM : Nat := ((linkSidesM FU).filter fun p => !p.1 && !p.2).length

set_option maxRecDepth 100000

theorem censusM_both : nBothM = 124 := by decide +kernel
theorem censusM_req : nReqOnlyM = 25 := by decide +kernel
theorem censusM_ack : nAckOnlyM = 25 := by decide +kernel
theorem censusM_none : nNoneM = 1 := by decide +kernel
theorem censusM_fuel : linkSidesM FU = linkSidesM (FU + 8) := by decide +kernel

/-- **Census with muxes** (kernel): of gcd_hw's 175 links, 124 bound on both sides, 25 only
on the request side, 25 only on the acknowledge side, 1 neither; fuel saturated. -/
theorem bound_censusM :
    nBothM = 124 ∧ nReqOnlyM = 25 ∧ nAckOnlyM = 25 ∧ nNoneM = 1 ∧
    linkSidesM FU = linkSidesM (FU + 8) :=
  ⟨censusM_both, censusM_req, censusM_ack, censusM_none, censusM_fuel⟩

/-! ## 5. The capstone, driver-bound, with muxes -/

/-- **End to end, runs that stop, drivers bound to the netlist, muxes gate-modelled.** -/
theorem gcd_hw_safe_fin_netBM (a b : Nat) (ch : Fin NC → Chan) (N : FGcdNetM)
    (L : N.ι → Nat → Prop) (n : N.ι → Nat) (H : FGcdNetOKBM ch N L n)
    (H_OTHER : ∀ o : Fin NO, isLink (opAt o) = false → Cell ch (srcV a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_CM_FORCED : ∃ y, Good a b y ∧ ∀ o : Fin NO, Forced ch (omOf a b y) (opAt o)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) :=
  gcd_hw_safe_fin_net a b ch N.toFGcdNet L n H.toOK H_OTHER H_BUNDLE H_CM_FORCED

end Formal.Cells.FiniteNetBoundM
