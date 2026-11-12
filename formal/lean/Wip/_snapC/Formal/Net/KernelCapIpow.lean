import Formal.Net.KernelCap
import Formal.Net.KernelCapChk
import Formal.Net.IpowCapMain

/-!
# Probe C-8y2: ipow as an instance of the kernel-parametric capstone

`ipowKD` packages ipow_ps's data (C-8v's graph `IpowHw.rules`, the C reference as the token
run's stores and `ipowSpec`, domain "e is an i32 bit pattern"; C-8y's generated network and
walk tables, with gcd's 3-input cascade constants mapped onto ipow's control_merge0 as in
C-8y). `ipowKP` takes every obligation from the existing `IpowHw*` / `IpowCap*` theorems.

`ipow_circuit_safe_generic` is `kernel_circuit_safe` at this instance; its statement is
`IpowCap.ipow_circuit_safe3`'s.
-/

namespace Formal.Net.KCap.IpowInst
open Formal.Net Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Handshake Formal.Net.Ops
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk
open Formal.Net.KCap

set_option maxRecDepth 100000

/-- ipow_ps's data. -/
@[reducible] def ipowKD : KD where
  rules := IpowHw.rules
  spine := IpowHw.spine
  init := IpowHw.init
  final := IpowHw.final
  spec := IpowHw.ipowSpec
  dom _ e := e < 2 ^ 32
  chOut := 57
  chEnd := 4
  nIn := 3
  srcVal := CapNet.srcV
  NC := IpowCap.NC
  NO := IpowCap.NO
  nzC := inferInstance
  nzO := inferInstance
  ops := IpowCap.ops
  tab := IpowCap.tab
  prodT := IpowCap.prodT
  consT := IpowCap.consT
  out0 := IpowCap.out0
  out0d := 1
  start := IpowCap.start
  spL := IpowCap.spL
  spN := IpowCap.spN
  grpL := IpowCap.grpL
  rhoL := IpowCap.rhoL
  adjL := IpowCap.adjL
  alL := IpowCap.alL
  lcL := IpowCap.lcL
  recs := IpowCap.recs
  acc := IpowCap.acc
  cq1 := 22
  cq2 := 41
  cq3 := 246
  cres := 39
  cidx := 40
  cl1 := 19
  cl2 := 20

attribute [local instance] ipowKD

theorem opchk_conv (k : K IpowCap.NC) (h : IpowCap.OpChk IpowCap.tab k) :
    KCap.OpChk IpowCap.tab k := by
  cases k with
  | src z which d =>
    rcases h with ⟨hw, hd⟩ | ⟨hw, hd⟩ | ⟨hw, hd⟩ <;> subst hw
    · exact Or.inl ⟨by decide, hd⟩
    · exact Or.inl ⟨by decide, hd⟩
    · exact Or.inr ⟨rfl, hd⟩
  | steerD j t f fd sw =>
    obtain ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, h11⟩ := h
    refine ⟨h1, h2, h3, h4, h5, h6, h7, h8, h9, h10, ?_⟩
    rcases hf : sw.fold with _ | ⟨lt, lf, gt', gf'⟩
    · exact h11
    · exact Or.inl h11
  | _ => exact h

theorem init_src' (a b w : Nat) (hw : w + 1 < 3) : IpowHw.init a b w = [CapNet.srcV a b w] := by
  match w, hw with
  | 0, _ => exact (IpowHw.init_store a b).1
  | 1, _ => exact (IpowHw.init_store a b).2.1

theorem env_np' (w : Nat) (hw : w < 3) : KCap.produced w = false := by
  match w, hw with
  | 0, _ => decide
  | 1, _ => decide
  | 2, _ => decide

/-- ipow_ps's proof obligations, from the existing ipow theorems. -/
theorem ipowKP : KP where
  spine_nodup := IpowHw.spine_nodup
  ins_ok := IpowHw.ins_ok
  outs_ok := IpowHw.outs_ok
  side_ok := IpowCap.side_ok
  closedG := IpowHw.closedG
  init_inv := IpowHw.init_inv
  init_empty := IpowCap.init_empty
  init_src := init_src'
  init_start a b := (IpowHw.init_store a b).2.2.1
  src_start _ _ := rfl
  final_out r := (IpowHw.final_store r).1
  final_empty := IpowCap.final_empty
  good_run a _ h := (IpowHw.ipow_hw_graph_computes_pow a h).1
  env_np := env_np'
  out_nc := by decide
  out_ge := by decide
  ops_ok o := opchk_conv _ (IpowCap.ops_ok o)
  rank_ok := IpowCap.rank_ok
  nf_pos := IpowCap.nf_pos
  prod_out := IpowCap.prod_out
  cons_in := IpowCap.cons_in
  prod_mem := IpowCap.prod_mem
  cons_mem := IpowCap.cons_mem
  out0_desc := IpowCap.out0_desc
  spok := spok_of IpowCap.ops_len (by decide +kernel)
  noloop := IpowCap.noloop
  sp_start := IpowCap.sp_start
  prod_start := IpowCap.prod_start
  spN_chk := IpowCap.spN_chk
  recs_chk := IpowCap.recs_chk
  cOK_chk := IpowCap.cOK_chk
  recs_glob := IpowCap.recs_glob
  init_chk := IpowCap.init_chk
  grp_start := IpowCap.grp_start
  spine_noend := IpowCap.spine_noend
  cmPair_chk := IpowCap.cmPair_chk
  lab_chk := IpowCap.lab249_chk
  r154 := IpowCap.r154
  r155 := IpowCap.r155
  cq12 := by decide
  cq31 := by decide
  cq32 := by decide
  cq1_sp := by decide
  cq2_sp := by decide
  idx_ge := by decide
  start_acc := by decide

attribute [local instance] ipowKP

/-- **ipow is an instance**: `kernel_circuit_safe` at `ipowKD`/`ipowKP`, stated exactly as
`IpowCap.ipow_circuit_safe3`. -/
theorem ipow_circuit_safe_generic (b e : Nat) (he : e < 2 ^ 32) (ch : Fin IpowCap.NC → Chan)
    (H_CELLS : ∀ o : Fin IpowCap.NO, Cell ch (CapNet.srcV b e) (IpowCap.opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch IpowCap.start).req) t ≤ 1) :
    (∀ k v, TokAt (ch IpowCap.out0) k v → (ch IpowCap.out0).dat v = IpowHw.ipowSpec b e) ∧
    (∀ t, closedVals (ch IpowCap.out0) t =
      List.replicate (Handshake.cnt (fallB (ch IpowCap.out0).ack) t) (IpowHw.ipowSpec b e)) :=
  kernel_circuit_safe b e he ch H_CELLS H_BUNDLE H_START_ONCE

/-- The existing ipow theorem has the same statement as the instance. -/
theorem ipow_existing_same_statement :
    (∀ (b e : Nat) (he : e < 2 ^ 32) (ch : Fin IpowCap.NC → Chan)
      (H_CELLS : ∀ o : Fin IpowCap.NO, Cell ch (CapNet.srcV b e) (IpowCap.opAt o))
      (H_BUNDLE : ∀ c, Held (ch c))
      (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch IpowCap.start).req) t ≤ 1),
      (∀ k v, TokAt (ch IpowCap.out0) k v → (ch IpowCap.out0).dat v = IpowHw.ipowSpec b e) ∧
      (∀ t, closedVals (ch IpowCap.out0) t =
        List.replicate (Handshake.cnt (fallB (ch IpowCap.out0).ack) t) (IpowHw.ipowSpec b e))) :=
  IpowCap.ipow_circuit_safe3

end Formal.Net.KCap.IpowInst
