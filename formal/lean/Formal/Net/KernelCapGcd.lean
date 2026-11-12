import Formal.Net.KernelCap
import Formal.Net.KernelCapChk
import Formal.Net.CapstoneWalk

/-!
# Probe C-8y2: gcd_hw as an instance of the kernel-parametric capstone

`gcdKD` packages gcd_hw's data: bdc's graph (C-8i, `GcdHw.Gcd.rules`), the C reference as the
token run's stores (`init a b`, `final r`, spec `Nat.gcd`, domain `a, b < 2^31`), the generated
network (C-8m, `CapNet.Gcd.ops` ..) and the walk certificate (C-8s, `CapNet.Gcd.spN` ..).
`gcdKP` discharges every obligation, almost all by the EXISTING per-kernel theorem of the same
statement (the generic definitions are the gcd ones with constants turned into fields, so the
statements agree up to unfolding); the only real work is `opchk_conv` / `spok_conv` (the
generic source case `which + 1 < nIn` vs gcd's literal `which = 0 ∨ which = 1`, and the
generic `FoldOK`'s extra one-sided case); `spok` is re-checked by `decide` on the generic `SpOK`
(its `bjoin` case compiles to a different matcher, so the old theorem does not unify).

`gcd_hw_circuit_safe_generic` is `kernel_circuit_safe` at this instance; its statement is
`CapNet.Gcd.gcd_hw_circuit_safe3`'s, word for word (checked by `gcd_existing_same_statement`).
-/

namespace Formal.Net.KCap.GcdInst
open Formal.Net Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Handshake Formal.Net.Ops
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk
open Formal.Net.KCap

set_option maxRecDepth 100000

/-- gcd_hw's data. -/
@[reducible] def gcdKD : KD where
  rules := GcdHw.Gcd.rules
  spine := GcdHw.Gcd.spine
  init := GcdHw.Gcd.init
  final := GcdHw.Gcd.final
  spec := Nat.gcd
  dom a b := a < 2 ^ 31 ∧ b < 2 ^ 31
  chOut := 250
  chEnd := 3
  nIn := 3
  srcVal := CapNet.srcV
  NC := CapNet.Gcd.NC
  NO := CapNet.Gcd.NO
  nzC := inferInstance
  nzO := inferInstance
  ops := CapNet.Gcd.ops
  tab := CapNet.Gcd.tab
  prodT := CapNet.Gcd.prodT
  consT := CapNet.Gcd.consT
  out0 := CapNet.Gcd.out0
  out0d := 0
  start := CapNet.Gcd.start
  spL := CapNet.Gcd.spL
  spN := CapNet.Gcd.spN
  grpL := CapNet.Gcd.grpL
  rhoL := CapNet.Gcd.rhoL
  adjL := CapNet.Gcd.adjL
  alL := CapNet.Gcd.alL
  lcL := CapNet.Gcd.lcL
  recs := CapNet.Gcd.recs
  acc := CapNet.Gcd.acc
  cq1 := 13
  cq2 := 27
  cq3 := 246
  cres := 251
  cidx := 249
  cl1 := 154
  cl2 := 155

attribute [local instance] gcdKD

theorem opchk_conv (k : K CapNet.Gcd.NC) (h : CapNet.OpChk CapNet.Gcd.tab k) :
    KCap.OpChk CapNet.Gcd.tab k := by
  cases k with
  | src z which d =>
    rcases h with ⟨hw, hd⟩ | ⟨hw, hd⟩ | ⟨hw, hd⟩ <;> subst hw
    · exact Or.inl ⟨by decide, hd⟩
    · exact Or.inl ⟨by decide, hd⟩
    · exact Or.inr ⟨rfl, hd⟩
  | steerD j t f fd sw =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ?_⟩
    rcases hf : sw.fold with _ | ⟨lt, lf, gt', gf'⟩ <;> rw [hf] at h11
    · exact h11
    · exact Or.inl h11
  | _ => exact h

theorem init_src' (a b w : Nat) (hw : w + 1 < 3) : GcdHw.Gcd.init a b w = [CapNet.srcV a b w] := by
  match w, hw with
  | 0, _ => exact (GcdHw.Gcd.init_store a b).1
  | 1, _ => exact (GcdHw.Gcd.init_store a b).2.1

theorem env_np' (w : Nat) (hw : w < 3) : KCap.produced w = false := by
  match w, hw with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide

/-- gcd_hw's proof obligations, from the existing gcd_hw theorems. -/
theorem gcdKP : KP where
  spine_nodup := GcdHw.Gcd.spine_nodup
  ins_ok := GcdHw.Gcd.ins_ok
  outs_ok := GcdHw.Gcd.outs_ok
  side_ok := CapSafe.side_ok
  closedG := GcdHw.Gcd.closedG
  init_inv := GcdHw.Gcd.init_inv
  init_empty a b c h := (GcdHw.Gcd.init_store a b).2.2.2 c h
  init_src := init_src'
  init_start a b := (GcdHw.Gcd.init_store a b).2.2.1
  src_start _ _ := rfl
  final_out r := (GcdHw.Gcd.final_store r).1
  final_empty := CapSafe.final_empty
  good_run _ _ h := (GcdHw.Gcd.gcd_hw_graph_computes_gcd h.1 h.2).1
  env_np := env_np'
  out_nc := by decide
  out_ge := by decide
  ops_ok o := opchk_conv _ (CapNet.Gcd.ops_ok o)
  rank_ok := CapNet.Gcd.rank_ok
  nf_pos := CapNet.Gcd.nf_pos
  prod_out := CapNet.Gcd.prod_out
  cons_in := CapNet.Gcd.cons_in
  prod_mem := CapNet.Gcd.prod_mem
  cons_mem := CapNet.Gcd.cons_mem
  out0_desc := CapNet.Gcd.out0_desc
  spok := spok_of CapNet.Gcd.ops_len (by decide +kernel)
  noloop := CapNet.Gcd.noloop
  sp_start := CapNet.Gcd.sp_start
  prod_start := CapNet.Gcd.prod_start
  spN_chk := CapNet.Gcd.spN_chk
  recs_chk := CapNet.Gcd.recs_chk
  cOK_chk := CapNet.Gcd.cOK_chk
  recs_glob := CapNet.Gcd.recs_glob
  init_chk := CapNet.Gcd.init_chk
  grp_start := CapNet.Gcd.grp_start
  spine_noend := CapNet.Gcd.spine_noend
  cmPair_chk := CapNet.Gcd.cmPair_chk
  lab_chk := CapNet.Gcd.lab249_chk
  r154 := CapNet.Gcd.r154
  r155 := CapNet.Gcd.r155
  cq12 := by decide
  cq31 := by decide
  cq32 := by decide
  cq1_sp := by decide
  cq2_sp := by decide
  idx_ge := by decide
  start_acc := by decide

attribute [local instance] gcdKP

/-- **gcd_hw is an instance**: `kernel_circuit_safe` at `gcdKD`/`gcdKP`, stated exactly as
`CapNet.Gcd.gcd_hw_circuit_safe3`. -/
theorem gcd_hw_circuit_safe_generic (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (ch : Fin CapNet.Gcd.NC → Chan)
    (H_CELLS : ∀ o : Fin CapNet.Gcd.NO, Cell ch (CapNet.srcV a b) (CapNet.Gcd.opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch CapNet.Gcd.start).req) t ≤ 1) :
    (∀ k e, TokAt (ch CapNet.Gcd.out0) k e → (ch CapNet.Gcd.out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch CapNet.Gcd.out0) t =
      List.replicate (Handshake.cnt (fallB (ch CapNet.Gcd.out0).ack) t) (Nat.gcd a b)) :=
  kernel_circuit_safe a b (⟨ha, hb⟩ : a < 2 ^ 31 ∧ b < 2 ^ 31) ch H_CELLS H_BUNDLE H_START_ONCE

/-- The generic instance and the existing gcd_hw theorem state the same thing. -/
theorem gcd_existing_same_statement :
    (∀ (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31) (ch : Fin CapNet.Gcd.NC → Chan)
      (H_CELLS : ∀ o : Fin CapNet.Gcd.NO, Cell ch (CapNet.srcV a b) (CapNet.Gcd.opAt o))
      (H_BUNDLE : ∀ c, Held (ch c))
      (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch CapNet.Gcd.start).req) t ≤ 1),
      (∀ k e, TokAt (ch CapNet.Gcd.out0) k e → (ch CapNet.Gcd.out0).dat e = Nat.gcd a b) ∧
      (∀ t, closedVals (ch CapNet.Gcd.out0) t =
        List.replicate (Handshake.cnt (fallB (ch CapNet.Gcd.out0).ack) t) (Nat.gcd a b))) :=
  CapNet.Gcd.gcd_hw_circuit_safe3

end Formal.Net.KCap.GcdInst
