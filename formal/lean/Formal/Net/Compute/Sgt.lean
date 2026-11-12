import Formal.Net.Compute.Slt

/-!
# H_COMPUTE_FN, part 10: signed greater-than (the comparator chain's carry-out itself)

`SgtOK`: the same group/chain certificate as `SltOK`, with the output net checked to be the
chain's last carry (through bdc's kept LUT1 buffer). `sgt_sound`: the output is `slt b a`.
-/

namespace Formal.Net.Compute
open Formal.Net.GcdHw

def SgtOK (cells : List Cell) (gs : List SGrp) (z : Nat) : Prop :=
  (cells.flatMap Cell.outs).Nodup ∧ GrpsOK gs 0 ∧ chainAll cells gs none = true ∧
  (∀ g ∈ gs, NetOK cells [] g.e (grpS g.lo g.len) (eqSpecG g.lo g.len) ∧
    NetOK cells [] g.d (grpS g.lo g.len) (gtSpecG g.lo g.len)) ∧
  (∃ cl, lastCh cells gs none = some cl ∧ NetOK cells [cl] z [.cut cl] (fun l => l.getD 0 false))

theorem sgt_sound {cells : List Cell} {gs : List SGrp} {z : Nat} (h : SgtOK cells gs z)
    (xs : List Nat) :
    run (inEnv xs) [] cells (fun _ => false) z =
      decide (Ops.flip 32 (xs.getD 1 0) < Ops.flip 32 (xs.getD 0 0)) := by
  obtain ⟨hnd, hg, hch, hgrp, cl, hcl, hz⟩ := h
  let a := xs.getD 0 0
  let b := xs.getD 1 0
  let env := inEnv xs
  let R := run env [] cells (fun _ => false)
  let x := Ops.flip 32 a
  let y := Ops.flip 32 b
  have hx : x < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hy : y < 2 ^ 32 := Nat.mod_lt _ (by decide)
  have hv : ∀ g ∈ gs, R g.e = (x / 2 ^ g.lo % 2 ^ g.len == y / 2 ^ g.lo % 2 ^ g.len) ∧
      R g.d = decide (y / 2 ^ g.lo % 2 ^ g.len < x / 2 ^ g.lo % 2 ^ g.len) := by
    intro g hgm
    obtain ⟨⟨he1, he2, he3⟩, ⟨hd1, hd2, hd3⟩⟩ := hgrp g hgm
    obtain ⟨gv0, gv1⟩ := gval_grp xs a b g.lo g.len rfl rfl cells (grps_mem gs 0 hg g hgm)
    constructor
    · show run env [] cells (fun _ => false) g.e = _
      rw [cert_val hnd he1 he2 he3 env]
      simp only [eqSpecG]
      rw [gv0, gv1]
    · show run env [] cells (fun _ => false) g.d = _
      rw [cert_val hnd hd1 hd2 hd3 env]
      simp only [gtSpecG]
      rw [gv0, gv1]
  obtain ⟨⟨cl', hcl', hR⟩, -⟩ := chain_ind env cells hnd x y gs 0 none hg hch hv (fun _ => rfl)
    (by simp [pv, Nat.mod_one])
  rw [hcl] at hcl'
  injection hcl' with hcl'
  subst hcl'
  obtain ⟨z1, z2, z3⟩ := hz
  have hzv : R z = R cl := cert_val hnd z1 z2 z3 env
  show R z = _
  rw [hzv]
  show run env [] cells (fun _ => false) cl = _
  rw [hR, Nat.mod_eq_of_lt hx, Nat.mod_eq_of_lt hy]

end Formal.Net.Compute
