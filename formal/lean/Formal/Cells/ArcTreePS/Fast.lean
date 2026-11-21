import Formal.Cells.ArcTreePS.AT
import Formal.Cells.SliceNetPS.TBeh

/-!
# Formal.Cells.ArcTreePS.Fast — THE target's slice-net bounds by tree lookups and Nat arithmetic (shard B, 2026-11-10)

**Problem, plainly.** `tnPS p c1 c2`'s `lo`/`hi` are route sums with ℚ ceilings over chains fetched from the chunked
gate list; a `decide`-checked certificate on `tnPS` needs them cheap.

**Proved.** `loF`/`hiF` compute a pin's bound with the gate's own pin arc plus a walk along C's copy map (`cmPS`)
reading each hop's arc from the arc trees (`aPS`, kernel-checked against the gate list), with `CornerSlice.loN`/`hiN`
(Nat ceilings/floors). `tnPS_lo_fast`/`tnPS_hi_fast`: for `p = ⟨gn/gd, kn/kd⟩` and slice ends `cn/cd`, they equal
`tnPS`'s bounds at every node and pin.

**Not shown here:** any certificate.
-/

namespace Formal.Cells.ArcTreePS
open Formal.Target Formal.Target.DecodedPS Formal.Timing.SpecChain Formal.Timing.SpecChainM Formal.Timing.ChunkCM
  Formal.Timing.Huffman Formal.Net.CViewPS Formal.Cells.ArcTree Formal.Cells.StartBound Formal.Cells.CornerSlice
  Formal.Cells.SliceReads Formal.Cells.SliceNet Formal.Cells.SliceNetPS Formal.Net.OccNet

/-- A pin's route sum of `f` over its arcs, by walk. -/
def routeF (f : Arc → Nat) (v w : Nat) : Nat :=
  let g := gAt cs 2500 v
  let pv := pvAt vss 2500 v
  let i := pinOf (keepPSN v) (srcD pv) w
  f (g.arcs.getD i default) + (if i < g.k then wsum cmPS (fun u => f (aPS u)) (g.ins.getD i 0) (pv.getD i (0, 0)).2 else 0)

def loF (kn kd gn gd cn cd : Nat) (v w : Nat) : Nat := routeF (loN kn kd gn gd cn cd) v w
def hiF (kn kd gn gd cn cd : Nat) (v w : Nat) : Nat := routeF (hiN kn kd gn gd cn cd) v w

theorem pinOf_keep (v w : Nat) : pinOf (keepPSN v) (srcOf (pcsPS v)) w = pinOf (keepPSN v) (srcD (pvAt vss 2500 v)) w := by
  unfold pinOf; rw [keep_src]

theorem route_eq_i (f : Arc → Nat) (v i : Nat) :
    ((pinArcs (gAt cs 2500 v) (pcsPS v) i).map f).sum = f ((gAt cs 2500 v).arcs.getD i default) +
      (if i < (gAt cs 2500 v).k then wsum cmPS (fun u => f (aPS u)) ((gAt cs 2500 v).ins.getD i 0)
        ((pvAt vss 2500 v).getD i (0, 0)).2 else 0) := by
  simp only [pinArcs, List.map_cons, List.sum_cons]
  congr 1
  by_cases hi : i < (gAt cs 2500 v).k
  · rw [if_pos hi]
    unfold pcsPS
    rw [toPCs_getD _ _ _ _ hi]
    simp only
    rw [List.map_map, ← List.map_map, sum_chain_walk]
    congr 1
    funext u
    rw [aPS_eq]
  · rw [if_neg hi]
    have : (pcsPS v).getD i ⟨0, []⟩ = ⟨0, []⟩ := by
      unfold pcsPS toPCs
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by simp; omega)]
      rfl
    rw [this]; rfl

theorem route_eq (f : Arc → Nat) (v w : Nat) :
    ((pinArcs (gAt cs 2500 v) (pcsPS v) (pinOf (keepPSN v) (srcOf (pcsPS v)) w)).map f).sum = routeF f v w := by
  rw [pinOf_keep, route_eq_i]; rfl

theorem tnPS_lo_fast {kn kd gn gd cn1 cd : Nat} (hk : kn ≤ kd) (hc : cn1 ≤ cd) (hkd : 0 < kd) (hgn : 0 < gn)
    (hgd : 0 < gd) (hcd : 0 < cd) (cx : ℚ) (v w : Nat) :
    (tnPS ⟨(gn : ℚ) / gd, (kn : ℚ) / kd⟩ ((cn1 : ℚ) / cd) cx).lo v w = loF kn kd gn gd cn1 cd v w := by
  rw [tnPS_lo_nat (cn2 := 0) hk hc hkd hgn hgd hcd, route_eq]; rfl

theorem tnPS_hi_fast {kn kd gn gd cn2 cd : Nat} (hc : cn2 ≤ cd) (hkd : 0 < kd)
    (hgd : 0 < gd) (hcd : 0 < cd) (cx : ℚ) (v w : Nat) :
    (tnPS ⟨(gn : ℚ) / gd, (kn : ℚ) / kd⟩ cx ((cn2 : ℚ) / cd)).hi v w = hiF kn kd gn gd cn2 cd v w := by
  rw [tnPS_hi_nat hc hkd hgd hcd, route_eq]; rfl

end Formal.Cells.ArcTreePS
