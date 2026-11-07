import Formal.Net.KernelCap
import Formal.Net.KernelCapChk
import Formal.Net.XorshiftCapData
import Formal.Net.XorshiftHwProof

/-!
# Probe C-8y2: xorshift through the kernel-parametric capstone (the steer case)

xorshift (`kernels/xorshift/xorshift.c`, Marsaglia's xorshift32: unsigned xors, two left
shifts and one LOGICAL right shift per round) at both levels:

* token level (`XorshiftHwProof`, this probe): bdc's graph computes the C transcription on
  every schedule, unconditionally for every `seed` and every i32 `rounds`
  (`xorshift_hw_graph_computes`, result `xsSpec seed rounds`);
* circuit level (here): `xorshift_circuit_safe`, `kernel_circuit_safe` at `xorKD`/`xorKP`.

The steer case: bdc folds the zero-delay `extui0` into ONE output of `cond_br2` (the loop
counter's initial `i1 false`, extended to i32 on the true side only; the false side is sunk).
C-8m's checker required the reshape on both outputs; the generic `FoldOK` (KernelCapDefs)
adds the one-sided case when the steered data is a constant fixed by the reshape
(`ConstFix`: extui(0) = 0), with its soundness in `KernelCapSound.sound_steerD`.

Cascade constants: xorshift's control_merge0 (rules 17/18: `cm 23|38 → 36`, index 37);
`acc` = circuit channel 0 (`g0.0`, not on the spine).
-/

namespace Formal.Net.KCap.XorshiftInst
open Formal.Net Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Handshake Formal.Net.Ops
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk
open Formal.Net.KCap

set_option maxRecDepth 100000

/-- xorshift's data. -/
@[reducible] def xorKD : KD where
  rules := XorshiftHw.rules
  spine := XorshiftHw.spine
  init seed r := XorshiftHw.St XorshiftHw.T0 [seed, r]
  final x := XorshiftHw.St XorshiftHw.T2 [x]
  spec := XorshiftHw.xsSpec
  dom _ r := r < 2 ^ 32
  chOut := XorshiftHw.chOut
  chEnd := XorshiftHw.chEnd
  nIn := XorshiftCap.nIn
  srcVal := CapNet.srcV
  NC := XorshiftCap.NC
  NO := XorshiftCap.NO
  nzC := inferInstance
  nzO := inferInstance
  ops := XorshiftCap.ops
  tab := XorshiftCap.tab
  prodT := XorshiftCap.prodT
  consT := XorshiftCap.consT
  out0 := XorshiftCap.out0
  out0d := XorshiftCap.out0d
  start := XorshiftCap.start
  spL := XorshiftCap.spL
  spN := XorshiftCap.spN
  grpL := XorshiftCap.grpL
  rhoL := XorshiftCap.rhoL
  adjL := XorshiftCap.adjL
  alL := XorshiftCap.alL
  lcL := XorshiftCap.lcL
  recs := XorshiftCap.recs
  acc := 0
  cq1 := 23
  cq2 := 38
  cq3 := 999
  cres := 36
  cidx := 37
  cl1 := 17
  cl2 := 18

attribute [local instance] xorKD

theorem init_src' (a b w : Nat) (hw : w + 1 < 3) :
    XorshiftHw.St XorshiftHw.T0 [a, b] w = [CapNet.srcV a b w] := by
  match w, hw with
  | 0, _ => exact (XorshiftHw.init_store a b).1
  | 1, _ => exact (XorshiftHw.init_store a b).2.1

/-- xorshift's proof obligations: data checks by kernel evaluation, C-reference facts from
`XorshiftHwProof`. -/
theorem xorKP : KP where
  spine_nodup := XorshiftHw.spine_nodup
  ins_ok := XorshiftHw.ins_ok
  outs_ok := XorshiftHw.outs_ok
  side_ok := by decide +kernel
  closedG := XorshiftHw.closedG
  init_inv := XorshiftHw.init_inv
  init_empty a b c h := (XorshiftHw.init_store a b).2.2.2 c h
  init_src := init_src'
  init_start a b := (XorshiftHw.init_store a b).2.2.1
  src_start _ _ := rfl
  final_out x := (XorshiftHw.final_store x).1
  final_empty x c h1 h2 := (XorshiftHw.final_store x).2.2 c h2 h1
  good_run seed _ h := (XorshiftHw.xorshift_hw_graph_computes seed h).1
  env_np := env_np_of (by decide +kernel)
  out_nc := by decide +kernel
  out_ge := by decide
  ops_ok := ops_ok_of (by decide +kernel) (by decide +kernel)
  rank_ok := rank_ok_of (by decide +kernel)
  nf_pos := by decide
  prod_out := prod_out_of (by decide +kernel)
  cons_in := cons_in_of (by decide +kernel)
  prod_mem := prod_mem_of (by decide +kernel)
  cons_mem := cons_mem_of (by decide +kernel)
  out0_desc := by decide +kernel
  spok := spok_of (by decide +kernel) (by decide +kernel)
  noloop := noloop_of (by decide +kernel)
  sp_start := by decide +kernel
  prod_start := rfl
  spN_chk := by decide +kernel
  recs_chk := by decide +kernel
  cOK_chk := by decide +kernel
  recs_glob := by decide +kernel
  init_chk := by decide +kernel
  grp_start := by decide +kernel
  spine_noend := by decide +kernel
  cmPair_chk := by decide +kernel
  lab_chk := by decide +kernel
  r154 := by decide +kernel
  r155 := by decide +kernel
  cq12 := by decide
  cq31 := by decide
  cq32 := by decide
  cq1_sp := by decide +kernel
  cq2_sp := by decide +kernel
  idx_ge := by decide
  start_acc := by decide

attribute [local instance] xorKP

/-- **xorshift at circuit level.** For every `seed` and every i32 `rounds < 2^32`: every run
`ch` of the concrete xorshift network (94 channels, 77 operators) whose operators meet their
gate models (H_CELLS), whose channels are bundled (H_BUNDLE) and whose start source is offered
at most once (H_START_ONCE) latches on `out0` only `xsSpec seed rounds`, the C result
(`xorshiftC_total`), and the latched list at every time is that value repeated. -/
theorem xorshift_circuit_safe (seed rounds : Nat) (hr : rounds < 2 ^ 32)
    (ch : Fin XorshiftCap.NC → Chan)
    (H_CELLS : ∀ o : Fin XorshiftCap.NO, Cell ch (CapNet.srcV seed rounds) (KCap.opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch XorshiftCap.start).req) t ≤ 1) :
    (∀ k v, TokAt (ch XorshiftCap.out0) k v →
      (ch XorshiftCap.out0).dat v = XorshiftHw.xsSpec seed rounds) ∧
    (∀ t, closedVals (ch XorshiftCap.out0) t =
      List.replicate (Handshake.cnt (fallB (ch XorshiftCap.out0).ack) t)
        (XorshiftHw.xsSpec seed rounds)) :=
  kernel_circuit_safe seed rounds hr ch H_CELLS H_BUNDLE H_START_ONCE

/-- The same, against the C transcription directly: whatever `xorshiftC` returns. -/
theorem xorshift_circuit_safe_C (seed rounds fuel r : Nat) (hr : rounds < 2 ^ 32)
    (hc : XorshiftHw.xorshiftC fuel seed rounds = some r)
    (ch : Fin XorshiftCap.NC → Chan)
    (H_CELLS : ∀ o : Fin XorshiftCap.NO, Cell ch (CapNet.srcV seed rounds) (KCap.opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch XorshiftCap.start).req) t ≤ 1) :
    ∀ k v, TokAt (ch XorshiftCap.out0) k v → (ch XorshiftCap.out0).dat v = r := by
  have e : XorshiftHw.xsSpec seed rounds = r := by
    have h1 := XorshiftHw.xorshiftC_total seed hr
    -- the C loop is deterministic in the fuel once it has returned
    have hmono : ∀ f1 f2 r1 r2 x i, XorshiftHw.xsLoop f1 rounds x i = some r1 →
        XorshiftHw.xsLoop f2 rounds x i = some r2 → r1 = r2 := by
      intro f1
      induction f1 with
      | zero => intro _ _ _ _ _ h; simp [XorshiftHw.xsLoop] at h
      | succ f ih =>
        intro f2 r1 r2 x i h1' h2'
        cases f2 with
        | zero => simp [XorshiftHw.xsLoop] at h2'
        | succ g =>
          rw [XorshiftHw.xsLoop] at h1' h2'
          split at h1'
          · rename_i hc'; simp only [hc', ↓reduceIte] at h2'; exact ih g r1 r2 _ _ h1' h2'
          · rename_i hc'; simp only [hc', Bool.false_eq_true, ↓reduceIte] at h2'
            rw [← Option.some.inj h1', ← Option.some.inj h2']
    exact (hmono _ _ _ _ _ _ h1 hc)
  rw [← e]
  exact (xorshift_circuit_safe seed rounds hr ch H_CELLS H_BUNDLE H_START_ONCE).1

/-- The two names in the statement are the right channels: `start` is the environment's
start source (`which = nIn - 1 = 2`), `out0` carries the token graph's out0 (channel 54). -/
theorem xorshift_ports : KCap.opAt (KCap.prodOf XorshiftCap.start) = .src XorshiftCap.start 2 0 ∧
    XorshiftCap.tab.d XorshiftCap.out0.val = .hist 54 0 :=
  ⟨rfl, by decide +kernel⟩

end Formal.Net.KCap.XorshiftInst
