import Formal.Core.EnvFast.Kernel
import Formal.Core.EnvFast.Tables
import Formal.Core.EnvFast.Tables2
import Formal.Core.EnvFast.MuxModels

/-!
# Formal.Core.EnvFast.MuxCompiled — compiled (kernel-form) bd_mux / bd_merge-data models

For each model of `MuxModels.lean`: the gates with their (checked) LUT tables,
the environment guards in kernel form, `KCompiled` proofs, and kernel forms of
the per-state properties with their equality proofs. No certificates here.
-/

namespace Formal.Core.EnvFast

set_option linter.unusedSimpArgs false

open Formal.Core.LutCells Formal.Core.Env Formal.Core.EnvFast.Tables

/-! ## bd_mux -/

def muxCG : List CGate :=
  [.lut 4 bd_mux_uj0 .O [11, 4, 3, 2, 0] tt_bd_mux_uj0_O hz_bd_mux_uj0_O,
   .lut 5 bd_mux_uj1 .O [11, 5, 3, 2, 1] tt_bd_mux_uj1_O hz_bd_mux_uj1_O,
   .lut 6 bd_mux_uor .O [5, 4] tt_bd_mux_uor_O hz_bd_mux_uor_O, .wire 7 6,
   .lut 9 bd_c2_u .O [11, 9, 8, 4] tt_bd_c2_u_O hz_bd_c2_u_O,
   .lut 10 bd_c2_u .O [11, 10, 8, 5] tt_bd_c2_u_O hz_bd_c2_u_O]

theorem muxCG_valid : muxCG.all CGate.valid = true := by
  simp only [muxCG, List.all_cons, List.all_nil, CGate.valid, List.length_cons,
    List.length_nil, Nat.reduceAdd, tt_bd_mux_uj0_O_ok, hz_bd_mux_uj0_O_ok, tt_bd_mux_uj1_O_ok,
    hz_bd_mux_uj1_O_ok, tt_bd_mux_uor_O_ok, hz_bd_mux_uor_O_ok, tt_bd_c2_u_O_ok, hz_bd_c2_u_O_ok,
    Bool.and_self]

def muxEnvK : List (Nat × (Nat → Bool)) :=
  [(0, fun s => keq (kb s 0) (kb s 9)),
   (1, fun s => keq (kb s 1) (kb s 10)),
   (3, fun s => !kb s 12 && !kb s 2 && !kb s 8),
   (12, fun s => (!kb s 12 && !kb s 2 && !kb s 8) || (kb s 12 && kb s 2)),
   (2, fun s => (!kb s 2 && kb s 12 && !kb s 8) || (kb s 2 && kb s 8)),
   (8, fun s => kne (kb s 8) (kb s 7))]

theorem muxEnv_agree : EnvAgree muxEnvK muxEnv :=
  .cons rfl (fun s => by simp [kb_eq, keq_eq]) <| .cons rfl (fun s => by simp [kb_eq, keq_eq]) <|
  .cons rfl (fun s => by simp [kb_eq]) <| .cons rfl (fun s => by simp [kb_eq]) <|
  .cons rfl (fun s => by simp [kb_eq]) <| .cons rfl (fun s => by simp [kb_eq, kne_eq]) .nil

def muxC (A : MuxAsm) : CModel where
  n := 13
  settle := true
  gates := muxCG
  env := muxEnvK
  prio := (muxModel A).prio

theorem mux_kc (A : MuxAsm) : KCompiled (muxModel A) (muxC A) where
  n := rfl
  settle := rfl
  comp := ⟨rfl, muxCG_valid⟩
  env := muxEnv_agree
  prio := rfl

/-- Kernel form of `muxQ` (for any model). -/
noncomputable def kmuxQ (C : CModel) (s : Nat) : Bool :=
  let x := kexc C s
  klive C s && !(kb x 9 && !kb s 9 && kb s 3) && !(kb x 10 && !kb s 10 && !kb s 3) &&
    !(kb (kenOf C x) 8 && !kb s 8 &&
      !(kb s 2 && cond (kb s 3) (kb s 5 && !kb s 4) (kb s 4 && !kb s 5)))

theorem kmuxQ_eq {M : Model} {C : CModel} (hc : KCompiled M C) (s : Nat) :
    kmuxQ C s = muxQ M s := by
  simp only [kmuxQ, muxQ, klive_eq hc, kexc_eq hc, kenOf_eq hc, kb_eq, enMask_eq_enOf, cond_eq_ite]

/-! ### `z_ack` fork -/

def muxZaCG : List CGate :=
  [.lut 4 bd_mux_uj0 .O [11, 4, 3, 2, 0] tt_bd_mux_uj0_O hz_bd_mux_uj0_O,
   .lut 5 bd_mux_uj1 .O [11, 5, 3, 2, 1] tt_bd_mux_uj1_O hz_bd_mux_uj1_O,
   .lut 6 bd_mux_uor .O [5, 4] tt_bd_mux_uor_O hz_bd_mux_uor_O, .wire 7 6,
   .lut 9 bd_c2_u .O [11, 9, 13, 4] tt_bd_c2_u_O hz_bd_c2_u_O,
   .lut 10 bd_c2_u .O [11, 10, 14, 5] tt_bd_c2_u_O hz_bd_c2_u_O,
   .wire 13 8, .wire 14 8, .wire 15 8]

def muxZaC (A : MuxZaAsm) : CModel where
  n := 16
  settle := true
  gates := muxZaCG
  env := [(0, fun s => keq (kb s 0) (kb s 9)),
          (1, fun s => keq (kb s 1) (kb s 10)),
          (3, fun s => !kb s 12 && !kb s 2 && !kb s 15),
          (12, fun s => (!kb s 12 && !kb s 2 && !kb s 15) || (kb s 12 && kb s 2)),
          (2, fun s => (!kb s 2 && kb s 12 && !kb s 15) || (kb s 2 && kb s 15)),
          (8, fun s => kne (kb s 8) (kb s 7))]
  prio := (muxZaModel A).prio

theorem muxZa_valid : muxZaCG.all CGate.valid = true := by
    simp only [muxZaCG, List.all_cons, List.all_nil, CGate.valid, List.length_cons,
      List.length_nil, Nat.reduceAdd, tt_bd_mux_uj0_O_ok, hz_bd_mux_uj0_O_ok, tt_bd_mux_uj1_O_ok,
      hz_bd_mux_uj1_O_ok, tt_bd_mux_uor_O_ok, hz_bd_mux_uor_O_ok, tt_bd_c2_u_O_ok, hz_bd_c2_u_O_ok,
      Bool.and_self]

theorem muxZa_kc (A : MuxZaAsm) : KCompiled (muxZaModel A) (muxZaC A) where
  n := rfl
  settle := rfl
  comp := ⟨rfl, muxZa_valid⟩
  env := .cons rfl (fun s => by simp [kb_eq, keq_eq]) <| .cons rfl (fun s => by simp [kb_eq, keq_eq]) <|
    .cons rfl (fun s => by simp [kb_eq]) <| .cons rfl (fun s => by simp [kb_eq]) <|
    .cons rfl (fun s => by simp [kb_eq]) <| .cons rfl (fun s => by simp [kb_eq, kne_eq]) .nil
  prio := rfl

/-! ### `ctl_req` branch at `uj1` -/

def muxCrCG : List CGate :=
  [.lut 4 bd_mux_uj0 .O [11, 4, 3, 2, 0] tt_bd_mux_uj0_O hz_bd_mux_uj0_O,
   .lut 5 bd_mux_uj1 .O [11, 5, 3, 13, 1] tt_bd_mux_uj1_O hz_bd_mux_uj1_O,
   .lut 6 bd_mux_uor .O [5, 4] tt_bd_mux_uor_O hz_bd_mux_uor_O, .wire 7 6,
   .lut 9 bd_c2_u .O [11, 9, 8, 4] tt_bd_c2_u_O hz_bd_c2_u_O,
   .lut 10 bd_c2_u .O [11, 10, 8, 5] tt_bd_c2_u_O hz_bd_c2_u_O, .wire 13 2]

def muxCrC (A : MuxCrAsm) : CModel where
  n := 14
  settle := true
  gates := muxCrCG
  env := muxEnvK
  prio := (muxCrModel A).prio

theorem muxCr_valid : muxCrCG.all CGate.valid = true := by
    simp only [muxCrCG, List.all_cons, List.all_nil, CGate.valid, List.length_cons,
      List.length_nil, Nat.reduceAdd, tt_bd_mux_uj0_O_ok, hz_bd_mux_uj0_O_ok, tt_bd_mux_uj1_O_ok,
      hz_bd_mux_uj1_O_ok, tt_bd_mux_uor_O_ok, hz_bd_mux_uor_O_ok, tt_bd_c2_u_O_ok, hz_bd_c2_u_O_ok,
      Bool.and_self]

theorem muxCr_kc (A : MuxCrAsm) : KCompiled (muxCrModel A) (muxCrC A) where
  n := rfl
  settle := rfl
  comp := ⟨rfl, muxCr_valid⟩
  env := muxEnv_agree
  prio := rfl

/-! ### With the data mux (W = 1) -/

def muxDCG : List CGate :=
  muxCG ++ [.lut 15 bd_datamux_u_L215 .O [14, 13, 3] tt_bd_datamux_u_L215_O hz_bd_datamux_u_L215_O]

def muxDEnvXK : List (Nat × (Nat → Bool)) :=
  [(13, fun s => !kb s 16 && !kb s 0 && !kb s 9),
   (16, fun s => (!kb s 16 && !kb s 0 && !kb s 9) || (kb s 16 && kb s 0)),
   (0, fun s => (!kb s 0 && kb s 16 && !kb s 9) || (kb s 0 && kb s 9))]

def muxDEnvYK (yMoves : Bool) : List (Nat × (Nat → Bool)) :=
  if yMoves then
    [(14, fun s => !kb s 17 && !kb s 1 && !kb s 10),
     (17, fun s => (!kb s 17 && !kb s 1 && !kb s 10) || (kb s 17 && kb s 1)),
     (1, fun s => (!kb s 1 && kb s 17 && !kb s 10) || (kb s 1 && kb s 10))]
  else [(1, fun s => keq (kb s 1) (kb s 10))]

def muxDEnvCK : List (Nat × (Nat → Bool)) :=
  [(3, fun s => !kb s 12 && !kb s 2 && !kb s 8),
   (12, fun s => (!kb s 12 && !kb s 2 && !kb s 8) || (kb s 12 && kb s 2)),
   (2, fun s => (!kb s 2 && kb s 12 && !kb s 8) || (kb s 2 && kb s 8)),
   (8, fun s => kne (kb s 8) (kb s 7))]

theorem envAgree_append : ∀ {l1 l2 m1 m2 : List (Nat × (Nat → Bool))},
    EnvAgree l1 l2 → EnvAgree m1 m2 → EnvAgree (l1 ++ m1) (l2 ++ m2)
  | [], [], _, _, .nil, h => h
  | _ :: _, _ :: _, _, _, .cons h1 h2 hs, h => .cons h1 h2 (envAgree_append hs h)

theorem muxDEnvX_agree : EnvAgree muxDEnvXK muxDEnvX :=
  .cons rfl (fun s => by simp [kb_eq]) <| .cons rfl (fun s => by simp [kb_eq]) <|
    .cons rfl (fun s => by simp [kb_eq]) .nil

theorem muxDEnvY_agree (y : Bool) : EnvAgree (muxDEnvYK y) (muxDEnvY y) := by
  cases y
  · exact .cons rfl (fun s => by simp [kb_eq, keq_eq]) .nil
  · exact .cons rfl (fun s => by simp [kb_eq]) <| .cons rfl (fun s => by simp [kb_eq]) <|
      .cons rfl (fun s => by simp [kb_eq]) .nil

theorem muxDEnvC_agree : EnvAgree muxDEnvCK muxDEnvC :=
  .cons rfl (fun s => by simp [kb_eq]) <| .cons rfl (fun s => by simp [kb_eq]) <|
    .cons rfl (fun s => by simp [kb_eq]) <| .cons rfl (fun s => by simp [kb_eq, kne_eq]) .nil

def muxDC (A : MuxDAsm) : CModel where
  n := 18
  settle := true
  gates := muxDCG
  env := muxDEnvXK ++ muxDEnvYK A.yMoves ++ muxDEnvCK
  prio := (muxDModel A).prio

theorem muxD_valid : muxDCG.all CGate.valid = true := by
    simp only [muxDCG, muxCG, List.cons_append, List.nil_append, List.all_cons, List.all_nil,
      CGate.valid, List.length_cons, List.length_nil, Nat.reduceAdd, tt_bd_mux_uj0_O_ok,
      hz_bd_mux_uj0_O_ok, tt_bd_mux_uj1_O_ok, hz_bd_mux_uj1_O_ok, tt_bd_mux_uor_O_ok,
      hz_bd_mux_uor_O_ok, tt_bd_c2_u_O_ok, hz_bd_c2_u_O_ok, tt_bd_datamux_u_L215_O_ok,
      hz_bd_datamux_u_L215_O_ok, Bool.and_self]

theorem muxD_kc (A : MuxDAsm) : KCompiled (muxDModel A) (muxDC A) where
  n := rfl
  settle := rfl
  comp := ⟨rfl, muxD_valid⟩
  env := envAgree_append (envAgree_append muxDEnvX_agree (muxDEnvY_agree A.yMoves)) muxDEnvC_agree
  prio := rfl

def muxDSpecK : DSpec := ⟨fun u => Nat.beq u 15, fun s => kb s 7 || kb s 8⟩

theorem muxDSpec_agree : DAgree muxDSpecK muxDSpec :=
  ⟨fun u => by simp [muxDSpecK, muxDSpec, beq_eq_nat], fun s => by simp [muxDSpecK, muxDSpec, kb_eq]⟩

noncomputable def kmuxDQ (C : CModel) (s : Nat) : Bool :=
  kmuxQ C s && (!(kb s 7 || kb s 8) ||
    (!kb (kexc C s) 15 && keq (kb s 15) (cond (kb s 3) (kb s 14) (kb s 13))))

theorem kmuxDQ_eq {M : Model} {C : CModel} (hc : KCompiled M C) (s : Nat) :
    kmuxDQ C s = muxDQ M s := by
  simp only [kmuxDQ, muxDQ, kmuxQ_eq hc, kexc_eq hc, kb_eq, keq_eq, cond_eq_ite]

/-! ## bd_merge with data -/

def mergeDCG (W : Nat) : List CGate :=
  [.lut 2 bd_merge_uor .O [1, 0] tt_bd_merge_uor_O hz_bd_merge_uor_O, .wire 3 2,
   .lut 5 bd_c2_u .O [8, 5, 4, 0] tt_bd_c2_u_O hz_bd_c2_u_O,
   .lut 6 bd_c2_u .O [8, 6, 4, 1] tt_bd_c2_u_O hz_bd_c2_u_O,
   .lut 7 bd_merge_usel .O [5, 0] tt_bd_merge_usel_O hz_bd_merge_usel_O] ++
  (if W = 2 then [.lut 13 bd_datamux_u_L209 .O5 [14, 15, 11, 12, 7] tt_bd_datamux_u_L209_O5
                    hz_bd_datamux_u_L209_O5,
                  .lut 16 bd_datamux_u_L209 .O6 [14, 15, 11, 12, 7] tt_bd_datamux_u_L209_O6
                    hz_bd_datamux_u_L209_O6]
   else [.lut 13 bd_datamux_u_L215 .O [11, 12, 7] tt_bd_datamux_u_L215_O hz_bd_datamux_u_L215_O])

def mergeDEnvK (W : Nat) (A : MergeDAsm) : List (Nat × (Nat → Bool)) :=
  [(11, fun s => !kb s 9 && !kb s 0 && !kb s 5),
   (9, fun s => (!kb s 9 && !kb s 0 && !kb s 5) || (kb s 9 && kb s 0)),
   (0, fun s => (!kb s 0 && kb s 9 && !kb s 5 && (!A.excl || (!kb s 1 && !kb s 6))) ||
     (kb s 0 && kb s 5)),
   (12, fun s => !kb s 10 && !kb s 1 && !kb s 6),
   (10, fun s => (!kb s 10 && !kb s 1 && !kb s 6) || (kb s 10 && kb s 1)),
   (1, fun s => (!kb s 1 && kb s 10 && !kb s 6 && (!A.excl || (!kb s 0 && !kb s 5))) ||
     (kb s 1 && kb s 6)),
   (4, fun s => kne (kb s 4) (kb s 3))] ++
  (if W = 2 then [(14, fun s => !kb s 9 && !kb s 0 && !kb s 5),
                  (15, fun s => !kb s 10 && !kb s 1 && !kb s 6)] else [])

def CM1 (A : MergeDAsm) : CModel where
  n := 14
  settle := true
  gates := mergeDCG 1
  env := mergeDEnvK 1 A
  prio := (mergeDModel 1 A).prio

def CM2 (A : MergeDAsm) : CModel where
  n := 17
  settle := true
  gates := mergeDCG 2
  env := mergeDEnvK 2 A
  prio := (mergeDModel 2 A).prio

theorem mergeD1_valid : (mergeDCG 1).all CGate.valid = true := by
    simp only [mergeDCG, List.cons_append, List.nil_append, List.all_cons, List.all_nil,
      CGate.valid, List.length_cons, List.length_nil, Nat.reduceAdd, tt_bd_merge_uor_O_ok,
      hz_bd_merge_uor_O_ok, tt_bd_c2_u_O_ok, hz_bd_c2_u_O_ok, tt_bd_merge_usel_O_ok,
      hz_bd_merge_usel_O_ok, tt_bd_datamux_u_L215_O_ok, hz_bd_datamux_u_L215_O_ok,
      Bool.and_self, ite_false, Nat.reduceEqDiff]

theorem mergeD1_kc (A : MergeDAsm) : KCompiled (mergeDModel 1 A) (CM1 A) where
  n := rfl
  settle := rfl
  comp := ⟨rfl, mergeD1_valid⟩
  env := .cons rfl (fun s => by simp [kb_eq]) <| .cons rfl (fun s => by simp [kb_eq]) <|
    .cons rfl (fun s => by simp [kb_eq]) <| .cons rfl (fun s => by simp [kb_eq]) <|
    .cons rfl (fun s => by simp [kb_eq]) <| .cons rfl (fun s => by simp [kb_eq]) <|
    .cons rfl (fun s => by simp [kb_eq, kne_eq]) .nil
  prio := rfl

theorem mergeD2_valid : (mergeDCG 2).all CGate.valid = true := by
    simp only [mergeDCG, List.cons_append, List.nil_append, List.all_cons, List.all_nil,
      CGate.valid, List.length_cons, List.length_nil, Nat.reduceAdd, tt_bd_merge_uor_O_ok,
      hz_bd_merge_uor_O_ok, tt_bd_c2_u_O_ok, hz_bd_c2_u_O_ok, tt_bd_merge_usel_O_ok,
      hz_bd_merge_usel_O_ok, tt_bd_datamux_u_L209_O5_ok, hz_bd_datamux_u_L209_O5_ok,
      tt_bd_datamux_u_L209_O6_ok, hz_bd_datamux_u_L209_O6_ok, Bool.and_self, ite_true, Nat.reduceEqDiff]

theorem mergeD2_kc (A : MergeDAsm) : KCompiled (mergeDModel 2 A) (CM2 A) where
  n := rfl
  settle := rfl
  comp := ⟨rfl, mergeD2_valid⟩
  env := .cons rfl (fun s => by simp [kb_eq]) <| .cons rfl (fun s => by simp [kb_eq]) <|
    .cons rfl (fun s => by simp [kb_eq]) <| .cons rfl (fun s => by simp [kb_eq]) <|
    .cons rfl (fun s => by simp [kb_eq]) <| .cons rfl (fun s => by simp [kb_eq]) <|
    .cons rfl (fun s => by simp [kb_eq, kne_eq]) <| .cons rfl (fun s => by simp [kb_eq]) <|
    .cons rfl (fun s => by simp [kb_eq]) .nil
  prio := rfl

def mergeDSpecK : DSpec :=
  ⟨fun u => Nat.beq u 7 || Nat.beq u 13 || Nat.beq u 16, fun s => kb s 3 || kb s 4⟩

theorem mergeDSpec_agree : DAgree mergeDSpecK mergeDSpec :=
  ⟨fun u => by simp [mergeDSpecK, mergeDSpec, beq_eq_nat], fun s => by simp [mergeDSpecK, mergeDSpec, kb_eq]⟩

noncomputable def kmergeDQ (W : Nat) (C : CModel) (s : Nat) : Bool :=
  let x := kexc C s
  klive C s && !(kb x 6 && !kb s 6 && (kb s 0 || kb s 5)) &&
    !(kb x 5 && !kb s 5 && (kb s 1 || kb s 6)) &&
    (!(kb s 3 || kb s 4) ||
      (!kb x 13 && keq (kb s 13) (cond (kb s 0 || kb s 5) (kb s 11) (kb s 12)) &&
        (!Nat.beq W 2 || (!kb x 16 && keq (kb s 16) (cond (kb s 0 || kb s 5) (kb s 14) (kb s 15))))))

theorem kmergeDQ_eq {M : Model} {C : CModel} (hc : KCompiled M C) (W s : Nat) :
    kmergeDQ W C s = mergeDQ W M s := by
  simp only [kmergeDQ, mergeDQ, mergeQ, klive_eq hc, kexc_eq hc, kb_eq, keq_eq, cond_eq_ite,
    beq_eq_nat, Bool.and_assoc]
  rfl

end Formal.Core.EnvFast
