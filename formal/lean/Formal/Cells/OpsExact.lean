import Formal.Cells.OpsCounter
open Formal.Core.LutList

/-!
# Shard B, probe Lt4: exact forms of the operator obligations

Follows Lt3 (`OpsCounter`, notes `B-ops-counter.md`). Contents:

1. `merge_ok_noskew`: `merge_ok`'s whole conclusion without `H_OR_SKEW`
   (`MergeTimingNoSkew`), using Lt3's `or_tok_mono` and `merge_or_step`;
   `merge_timing_ns_of_static` derives it from `MergeStaticNS` = `MergeStatic`
   minus `S_OR`.
2. `merge_data_ok_exact`: the merge delivers its requester's value under
   `MergeDataExact`, which has the single node-launched condition
   **S_SEL_XA_N** in place of `S_SEL_XA_Z` and `S_SEL_XA_R`, and has NO
   `S_SEL_XR` (the x_req branch is implied by `S_ZM_SEL_X` once the proof
   tracks the LAST x token before `k`). `MergeDataStatic.exact` shows the old
   static set implies the new one, so the theorem strictly generalises
   `merge_data_ok`.
3. `S_SEL_XA_N` tight by one tick in Lt's unit merge run (`MergeCex`).
4. `MergeY`: a merge run whose token 0 is y's, with uxa's power-up level a
   parameter: `H_SEL_START` tight by one tick (fails only if uxa powers up
   high).
5. `MuxA`: a mux run with `Wc0 = 2` and x the LATE input at uj0: `S_Z_S1`
   necessary on its own (`S_Z_S0` holds), and `S_Z_X` tight by one tick.
6. `S_XA_RTZ` / `S_XA_ZA` are implied by `S_XA_J.1` / `S_XA_R.1` unless the
   z_ack wire has more delay spread than the request wire.
-/

namespace Formal.Cells.OpsTimed
open Formal.Cells
open Formal.Cells.PipeTimed (Ret Trace)
open Formal.Cells.Bundling (StableOn Gate Transport transport_gate)
open Formal.Cells.ConstraintsMux (DmRel dm_settles DM_ODD dm_odd_rel usel_high)
open Formal.Cells.LibCtlMergeMux (or2B c2B j0B j1B or2_spec c2_spec j0_spec j1_spec)

/-! ## 1. `merge_ok` without `H_OR_SKEW` -/

section mergens
variable {P : MergeRun} {Eo Es : Nat}

/-- The selected uor edge of token edge `j` precedes the next request edge
(port-level causality only). -/
theorem merge_S_lt_ρ (Cs : MergeCausal P Eo Es) (hEs : 1 ≤ Es) (j : Nat) :
    orEdges (fun k => !P.sv k) P.XO P.YO j < P.ρ (j + 1) := by
  have hSZ : orEdges (fun k => !P.sv k) P.XO P.YO j ≤ P.Z j := by
    have := P.Lor.fst_ge (orEdges (fun k => !P.sv k) P.XO P.YO j)
    have := P.Dz.fst_ge (P.Lor.fst (orEdges (fun k => !P.sv k) P.XO P.YO j))
    unfold MergeRun.Z; omega
  have h1 := Cs.H_SRV j
  have h2 := Cs.H_OWN j
  have hx : P.ζ j ≤ P.XA j := by
    have := P.Wzx.fst_ge (P.ζ j); have := P.Lxa.fst_ge (P.cx j); have := P.Wxa.fst_ge (P.Lxa.fst (P.cx j))
    unfold MergeRun.XA MergeRun.cx MergeRun.ZA0 at *; omega
  have hy : P.ζ j ≤ P.YA j := by
    have := P.Wzy.fst_ge (P.ζ j); have := P.Lya.fst_ge (P.cy j); have := P.Wya.fst_ge (P.Lya.fst (P.cy j))
    unfold MergeRun.YA MergeRun.cy MergeRun.ZA1 at *; omega
  split at h2 <;> omega

theorem merge_ρ_le_S (j : Nat) : P.ρ j ≤ orEdges (fun k => !P.sv k) P.XO P.YO j := by
  unfold orEdges MergeRun.XO MergeRun.YO; split
  · exact P.Wxo.fst_ge _
  · exact P.Wyo.fst_ge _

/-- Request edges are monotone (causality only). -/
theorem merge_ρ_mono' (Cs : MergeCausal P Eo Es) (hEs : 1 ≤ Es) : ∀ a b, a ≤ b → P.ρ a ≤ P.ρ b :=
  mono_of_step P.ρ (fun j => by have := merge_ρ_le_S (P := P) j; have := merge_S_lt_ρ Cs hEs j; omega)

/-- `merge_ok`'s timing obligations without `H_OR_SKEW`. -/
structure MergeTimingNoSkew (P : MergeRun) (R : Nat) : Prop where
  H_RST_LONG : P.Wxc.hi ≤ R ∧ P.Wyc.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧
    P.Lxa.hi + P.wxah ≤ R ∧ P.Lya.hi + P.wyah ≤ R
  H_RST_EARLY : R ≤ P.AX 0 ∧ R ≤ P.ZA0 0 ∧ R ≤ P.AY 0 ∧ R ≤ P.ZA1 0
  H_DEP_XA : ∀ j, P.cx j + P.Lxa.hi + P.wxah ≤ P.AX (j + 1) ∧ P.cx j + P.Lxa.hi + P.wxah ≤ P.ZA0 (j + 1)
  H_DEP_YA : ∀ j, P.cy j + P.Lya.hi + P.wyah ≤ P.AY (j + 1) ∧ P.cy j + P.Lya.hi + P.wyah ≤ P.ZA1 (j + 1)

theorem MergeTiming.ns {R : Nat} (TM : MergeTiming P R) : MergeTimingNoSkew P R :=
  ⟨TM.H_RST_LONG, TM.H_RST_EARLY, TM.H_DEP_XA, TM.H_DEP_YA⟩

/-- **`merge_ok_noskew`: `merge_ok`'s conclusions without `H_OR_SKEW`**, with
the partners' port-level causality (`MergeCausal`, a server taking at least
one tick) in its place. -/
theorem merge_ok_noskew {R : Nat} {rst x y za xo yo ei zr xc yc zx zy xa qa ya qb xak yak : Trace}
    (G : MergeGates P rst x y za xo yo ei zr xc yc zx zy xa qa ya qb xak yak)
    (V : MergeEnv P rst x y za R) (TM : MergeTimingNoSkew P R)
    (Cs : MergeCausal P Eo Es) (hEs : 1 ≤ Es) :
    Tok P.Tz zr P.Z (fun _ => true) ∧
    Tok P.Tx xak P.XA (fun k => !P.sv k) ∧ Tok P.Ty yak P.YA P.sv ∧
    (∀ j, P.ρ j ≤ P.Z j ∧ P.ζ j ≤ P.XA j ∧ P.ζ j ≤ P.YA j) := by
  obtain ⟨r1, r2, r3, r4, r5, r6⟩ := TM.H_RST_LONG
  obtain ⟨u1, u2, u3, u4⟩ := TM.H_RST_EARLY
  have st := merge_or_step Cs hEs
  have Sm := mono_of_step (orEdges (fun k => !P.sv k) P.XO P.YO) (fun j => Nat.le_of_lt (st j))
  have Su : ∀ j, j ≤ orEdges (fun k => !P.sv k) P.XO P.YO j := by
    intro j; induction j with
    | zero => omega
    | succ j ih => have := st j; omega
  have ρu : ∀ n, n < P.ρ (n + 1) := fun n => by have := Su n; have := merge_S_lt_ρ Cs hEs n; omega
  have p0 : Tok (P.Wxo.hi + P.Wyo.hi) xo P.XO (fun k => !P.sv k) :=
    (V.H_X.fifo P.Wxo G.H_WXO).mono (by omega)
  have p1 : Tok (P.Wxo.hi + P.Wyo.hi) yo P.YO (fun k => !(!P.sv k)) :=
    ((V.H_Y.fifo P.Wyo G.H_WYO).mono (by omega)).gcongr (fun k => by simp)
  have o := or_tok_mono p0 p1
    (fun t => ⟨t + 1, by have := ρu t; have := P.Wxo.fst_ge (P.ρ (t + 1)); unfold MergeRun.XO; omega⟩)
    (fun t => ⟨t + 1, by have := ρu t; have := P.Wyo.fst_ge (P.ρ (t + 1)); unfold MergeRun.YO; omega⟩)
    Sm
  have zt := (o.fifo P.Lor (y := ei) (fun t ht => by rw [G.H_UOR t ht, or2_spec])).fifo P.Dz G.H_DZ
  have ax : Tok R xc P.AX (fun k => !P.sv k) := (V.H_X.fifo P.Wxc G.H_WXC).mono (by omega)
  have zx' : Tok R zx P.ZA0 (fun _ => true) := (V.H_ZA.fifo P.Wzx G.H_WZX).mono (by omega)
  have CX : CEl xc zx rst xa qa (fun t => c2B (xc t) (zx t) (qa t) (rst t)) P.Lxa P.wxal P.wxah :=
    ⟨fun t => c2_spec _ _ _ _, G.H_UXA, G.H_UXA_FB, G.H_UXA_POS⟩
  have nx := cel_node CX (cel_run CX ax zx' V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r5 u1 u2 TM.H_DEP_XA)
  have ay : Tok R yc P.AY P.sv := (V.H_Y.fifo P.Wyc G.H_WYC).mono (by omega)
  have zy' : Tok R zy P.ZA1 (fun _ => true) := (V.H_ZA.fifo P.Wzy G.H_WZY).mono (by omega)
  have CY : CEl yc zy rst ya qb (fun t => c2B (yc t) (zy t) (qb t) (rst t)) P.Lya P.wyal P.wyah :=
    ⟨fun t => c2_spec _ _ _ _, G.H_UYA, G.H_UYA_FB, G.H_UYA_POS⟩
  have ny := cel_node CY (cel_run CY ay zy' V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r6 u3 u4 TM.H_DEP_YA)
  refine ⟨zt.congr (fun j => rfl), (nx.fifo P.Wxa G.H_WXA).gcongr (fun k => by simp),
    (ny.fifo P.Wya G.H_WYA).gcongr (fun k => by simp), fun j => ⟨?_, ?_, ?_⟩⟩
  · have := merge_ρ_le_S (P := P) j
    have := P.Lor.fst_ge (orEdges (fun k => !P.sv k) P.XO P.YO j)
    have := P.Dz.fst_ge (P.Lor.fst (orEdges (fun k => !P.sv k) P.XO P.YO j))
    unfold MergeRun.Z; omega
  · unfold MergeRun.XA MergeRun.cx MergeRun.ZA0
    have := P.Wzx.fst_ge (P.ζ j)
    have := P.Lxa.fst_ge (max (P.AX j) (P.Wzx.fst (P.ζ j)))
    have := P.Wxa.fst_ge (P.Lxa.fst (max (P.AX j) (P.Wzx.fst (P.ζ j))))
    omega
  · unfold MergeRun.YA MergeRun.cy MergeRun.ZA1
    have := P.Wzy.fst_ge (P.ζ j)
    have := P.Lya.fst_ge (max (P.AY j) (P.Wzy.fst (P.ζ j)))
    have := P.Wya.fst_ge (P.Lya.fst (max (P.AY j) (P.Wzy.fst (P.ζ j))))
    omega

/-- `MergeStatic` without `S_OR` (the skew condition, now unnecessary). -/
structure MergeStaticNS (P : MergeRun) (Eo Es wo wz la wa : Nat) : Prop where
  H_WO : wo ≤ P.Wxo.lo ∧ wo ≤ P.Wyo.lo
  H_WZ : wz ≤ P.Wzx.lo ∧ wz ≤ P.Wzy.lo
  H_LA : la ≤ P.Lxa.lo ∧ la ≤ P.Lya.lo
  H_WA : wa ≤ P.Wxa.lo ∧ wa ≤ P.Wya.lo
  S_XA_FORK : P.Wzx.hi + (P.Lxa.hi + P.wxah) ≤ (wz + la + wa + Eo) + P.Wxc.lo
  S_YA_FORK : P.Wzy.hi + (P.Lya.hi + P.wyah) ≤ (wz + la + wa + Eo) + P.Wyc.lo
  S_XA_ZA : P.Wzx.hi + (P.Lxa.hi + P.wxah) ≤ P.Wzx.lo + (wz + la + wa + Eo) + (wo + P.Lor.lo + P.Dz.lo + Es)
  S_YA_ZA : P.Wzy.hi + (P.Lya.hi + P.wyah) ≤ P.Wzy.lo + (wz + la + wa + Eo) + (wo + P.Lor.lo + P.Dz.lo + Es)
  S_XA_R : P.Wxc.hi + (P.Lxa.hi + P.wxah) ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (wz + la + wa + Eo) + P.Wxc.lo ∧
    P.Wxc.hi + (P.Lxa.hi + P.wxah) ≤ 2 * (wo + P.Lor.lo + P.Dz.lo + Es) + (wz + la + wa + Eo) + P.Wzx.lo
  S_YA_R : P.Wyc.hi + (P.Lya.hi + P.wyah) ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (wz + la + wa + Eo) + P.Wyc.lo ∧
    P.Wyc.hi + (P.Lya.hi + P.wyah) ≤ 2 * (wo + P.Lor.lo + P.Dz.lo + Es) + (wz + la + wa + Eo) + P.Wzy.lo

theorem MergeStatic.ns {wo wz la wa : Nat} (S : MergeStatic P Eo Es wo wz la wa) :
    MergeStaticNS P Eo Es wo wz la wa :=
  ⟨S.H_WO, S.H_WZ, S.H_LA, S.H_WA, S.S_XA_FORK, S.S_YA_FORK, S.S_XA_ZA, S.S_YA_ZA, S.S_XA_R, S.S_YA_R⟩

theorem merge_RZ' {wo wz la wa : Nat} (Cs : MergeCausal P Eo Es) (S : MergeStaticNS P Eo Es wo wz la wa)
    (j : Nat) : P.ρ j + (wo + P.Lor.lo + P.Dz.lo + Es) ≤ P.ζ j := by
  have hWO := S.H_WO
  have hs := Cs.H_SRV j; have hp := Cs.H_POS j
  unfold MergeRun.Z orEdges MergeRun.XO MergeRun.YO at hs
  split at hs
  · have a := fl P.Wxo hp
    have b := fl P.Lor (c := P.Wxo.fst (P.ρ j)) (by omega)
    have c := fl P.Dz (c := P.Lor.fst (P.Wxo.fst (P.ρ j))) (by omega)
    omega
  · have a := fl P.Wyo hp
    have b := fl P.Lor (c := P.Wyo.fst (P.ρ j)) (by omega)
    have c := fl P.Dz (c := P.Lor.fst (P.Wyo.fst (P.ρ j))) (by omega)
    omega

theorem merge_ZR' {wo wz la wa : Nat} (Cs : MergeCausal P Eo Es) (S : MergeStaticNS P Eo Es wo wz la wa)
    (j : Nat) : P.ζ j + (wz + la + wa + Eo) ≤ P.ρ (j + 1) := by
  have hWZ := S.H_WZ; have hLA := S.H_LA; have hWA := S.H_WA
  have ho := Cs.H_OWN j
  have hz : 1 ≤ P.ζ j := by have := merge_RZ' Cs S j; have := Cs.H_POS j; omega
  split at ho
  · have := merge_ζ_le_YA j hz; omega
  · have := merge_ζ_le_XA j hz; omega

/-- `merge_timing_of_static` without `S_OR`; the result has no `H_OR_SKEW`. -/
theorem merge_timing_ns_of_static {R wo wz la wa : Nat}
    (Cs : MergeCausal P Eo Es) (S : MergeStaticNS P Eo Es wo wz la wa)
    (hRL : P.Wxc.hi ≤ R ∧ P.Wyc.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧
      P.Lxa.hi + P.wxah ≤ R ∧ P.Lya.hi + P.wyah ≤ R)
    (hRE : R ≤ P.AX 0 ∧ R ≤ P.ZA0 0 ∧ R ≤ P.AY 0 ∧ R ≤ P.ZA1 0) : MergeTimingNoSkew P R := by
  have RZ := merge_RZ' Cs S
  have ZR := merge_ZR' Cs S
  refine ⟨hRL, hRE, fun j => ⟨?_, ?_⟩, fun j => ⟨?_, ?_⟩⟩
  · have := P.Wxc.fst_le (P.ρ j); have := P.Wzx.fst_le (P.ζ j)
    have := fl P.Wxc (Cs.H_POS (j + 1))
    have := RZ j; have := ZR j; have := S.S_XA_FORK; have := S.S_XA_R
    unfold MergeRun.cx MergeRun.AX MergeRun.ZA0; omega
  · have := P.Wxc.fst_le (P.ρ j); have := P.Wzx.fst_le (P.ζ j)
    have hz1 : 1 ≤ P.ζ (j + 1) := by have := RZ (j + 1); have := Cs.H_POS (j + 1); omega
    have := fl P.Wzx hz1
    have := RZ j; have := ZR j; have := RZ (j + 1); have := S.S_XA_ZA; have := S.S_XA_R
    unfold MergeRun.cx MergeRun.AX MergeRun.ZA0; omega
  · have := P.Wyc.fst_le (P.ρ j); have := P.Wzy.fst_le (P.ζ j)
    have := fl P.Wyc (Cs.H_POS (j + 1))
    have := RZ j; have := ZR j; have := S.S_YA_FORK; have := S.S_YA_R
    unfold MergeRun.cy MergeRun.AY MergeRun.ZA1; omega
  · have := P.Wyc.fst_le (P.ρ j); have := P.Wzy.fst_le (P.ζ j)
    have hz1 : 1 ≤ P.ζ (j + 1) := by have := RZ (j + 1); have := Cs.H_POS (j + 1); omega
    have := fl P.Wzy hz1
    have := RZ j; have := ZR j; have := RZ (j + 1); have := S.S_YA_ZA; have := S.S_YA_R
    unfold MergeRun.cy MergeRun.AY MergeRun.ZA1; omega

end mergens

/-- Non-vacuity of `merge_ok_noskew` on Lt's unit-delay merge run. -/
theorem MergeWit.noskew_witness :
    Tok MergeWit.run.Tz MergeWit.zr MergeWit.run.Z (fun _ => true) :=
  (merge_ok_noskew MergeWit.gates MergeWit.env
    (merge_timing_ns_of_static MergeWit.causal MergeWit.static.ns (by decide) MergeCex.hRE)
    MergeWit.causal (Nat.le_refl 1)).1


/-! ## 2. `merge_data_ok` under the exact x_ack condition, without `S_SEL_XR`

In a y token `k` the select must be low: x_req and the uxa node (x_ack) both
low before z_req reaches the server. Both have been low since the fall of the
LAST x token `k0 < k` (or since start-up if there is none): every slot in
between is a y slot, where x's gates are off. So the launch of each branch is
that x token's fall, not the previous merged token's:

* x_req fell at `ρ(2k0+1)`; that fall reached the server through `Wxo`
  (owner x), the server answered, x saw x_ack fall, and only then could any
  later token start. So `ρ(2k0+1) + Wxo.lo + Lor.lo + Dz.lo ≤ ρ(2k)`, and
  `S_ZM_SEL_X` (`hr + sh + Mz ≤ Wxo.lo + Lor.lo + Dz.lo`) already covers the
  branch. **`S_SEL_XR` is redundant.**
* the uxa node fell at `N`; x_ack at the client follows at `≥ N + Wxa.lo`,
  the client reacts (`Eo`), and the next owner's request (`≥ ρ(2k0+2)`, any
  later token) runs `Wyo`, uor, the delay line. So the single condition is
  **S_SEL_XA_N**: `hq + sh + Mz ≤ Wxa.lo + Eo + Wyo.lo + Lor.lo + Dz.lo`,
  whichever input of uxa fell last.
-/

section mergeexact
variable {P : MergeRun} {Eo Es : Nat}

/-- **The merge's data-path obligations, exact form.** As `MergeDataStatic`,
with `S_SEL_XA_N` in place of `S_SEL_XA_Z`/`S_SEL_XA_R` and without
`S_SEL_XR`. -/
structure MergeDataExact (P : MergeRun) (Eo hr hq sl sh lr lq xl xh yl yh Mz Hm Lx Ly : Nat) :
    Prop where
  /-- **S_ZM_SEL_X** = `bd_merge.bundled_z` (launch x_req rise). -/
  S_ZM_SEL_X : hr + sh + Mz ≤ P.Wxo.lo + P.Lor.lo + P.Dz.lo
  /-- **S_ZM_X / S_ZM_Y** (`bd_merge.bundled_z_data`). -/
  S_ZM_X : xh + Mz ≤ Lx + P.Wxo.lo + P.Lor.lo + P.Dz.lo
  S_ZM_Y : yh + Mz ≤ Ly + P.Wyo.lo + P.Lor.lo + P.Dz.lo
  /-- **S_SEL_XA_N** (`bd_merge.isochronic_forks`, x_ack branch, exact form):
  launch = the uxa NODE's fall in the last x token; data path node → usel
  pin (`hq`) → udat select (`sh`) + `Mz`; request path node → x_ack wire →
  x client (`Eo`) → next owner's request (y) → `Wyo` → uor → delay line.
  Test on GLS: the x_ack fork's skew (usel pin vs client pin) against the
  client's reaction plus the next requester's request path. -/
  S_SEL_XA_N : hq + sh + Mz ≤ P.Wxa.lo + Eo + P.Wyo.lo + P.Lor.lo + P.Dz.lo
  S_HM_SEL_X : Hm + 1 ≤ P.Wzx.lo + P.Lxa.lo + P.Wxa.lo + Eo + lr + sl
  S_HM_SEL_Y : Hm + 1 ≤ P.Wzy.lo + P.Lya.lo + P.Wya.lo + Eo + min lr lq + sl
  S_HM_X : Hm ≤ P.Wzx.lo + P.Lxa.lo + P.Wxa.lo + xl
  S_HM_Y : Hm ≤ P.Wzy.lo + P.Lya.lo + P.Wya.lo + yl
  /-- **H_SEL_START** (start-up), unchanged. -/
  H_SEL_START : max hr (P.Lxa.hi + hq) + sh + Mz ≤ P.ρ 0 + (P.Wyo.lo + P.Lor.lo + P.Dz.lo)

/-- The old static set implies the exact one (`S_SEL_XA_Z ⇒ S_SEL_XA_N`). -/
theorem MergeDataStatic.exact {wo wz la wa lr hr lq hq sl sh xl xh yl yh Mz Hm Lx Ly : Nat}
    (S : MergeStatic P Eo Es wo wz la wa)
    (SD : MergeDataStatic P Eo Es wo wz la wa lr hr lq hq sl sh xl xh yl yh Mz Hm Lx Ly) :
    MergeDataExact P Eo hr hq sl sh lr lq xl xh yl yh Mz Hm Lx Ly := by
  have := S.H_WZ; have := S.H_LA; have := S.H_WA; have := SD.S_SEL_XA_Z
  have := P.Wzx.lo_le_hi; have := P.Lxa.lo_le_hi
  exact ⟨SD.S_ZM_SEL_X, SD.S_ZM_X, SD.S_ZM_Y, by omega, SD.S_HM_SEL_X, SD.S_HM_SEL_Y,
    SD.S_HM_X, SD.S_HM_Y, SD.H_SEL_START⟩

/-- Every token before `k` is y's, or there is a last x token `k0 < k`. -/
theorem last_x (sv : Nat → Bool) : ∀ k, (∀ j, j < k → sv j = true) ∨
    ∃ k0, k0 < k ∧ sv k0 = false ∧ ∀ j, k0 < j → j < k → sv j = true := by
  intro k
  induction k with
  | zero => left; intro j h; omega
  | succ k ih =>
    cases hk : sv k
    · right; exact ⟨k, by omega, hk, fun j h1 h2 => by omega⟩
    · rcases ih with h | ⟨k0, h1, h2, h3⟩
      · left; intro j hj
        by_cases e : j = k
        · subst e; exact hk
        · exact h j (by omega)
      · right; refine ⟨k0, by omega, h2, fun j hj1 hj2 => ?_⟩
        by_cases e : j = k
        · subst e; exact hk
        · exact h3 j hj1 (by omega)

/-- z_req at the server follows the owner's request edge (any edge `j`). -/
theorem merge_ρ_le_Zj (hp : ∀ j, 1 ≤ P.ρ j) (j : Nat) :
    (P.sv (j / 2) = false → P.ρ j + (P.Wxo.lo + P.Lor.lo + P.Dz.lo) ≤ P.Z j) ∧
    (P.sv (j / 2) = true → P.ρ j + (P.Wyo.lo + P.Lor.lo + P.Dz.lo) ≤ P.Z j) := by
  have h1 := hp j
  unfold MergeRun.Z orEdges MergeRun.XO MergeRun.YO
  constructor
  · intro hk; simp only [hk, Bool.not_false, ite_true]
    have a := fl P.Wxo h1
    have b := fl P.Lor (c := P.Wxo.fst (P.ρ j)) (by omega)
    have c := fl P.Dz (c := P.Lor.fst (P.Wxo.fst (P.ρ j))) (by omega)
    omega
  · intro hk; simp only [hk, Bool.not_true, Bool.false_eq_true, ite_false]
    have a := fl P.Wyo h1
    have b := fl P.Lor (c := P.Wyo.fst (P.ρ j)) (by omega)
    have c := fl P.Dz (c := P.Lor.fst (P.Wyo.fst (P.ρ j))) (by omega)
    omega

/-- **`merge_data_ok_exact`: the merge delivers its requester's value**, under
`MergeDataExact` (one x_ack condition `S_SEL_XA_N`, no `S_SEL_XR`) and
`MergeStaticNS` (no `S_OR`). Same conclusion as `merge_data_ok`. -/
theorem merge_data_ok_exact {R wo wz la wa : Nat}
    {rst x y za xo yo ei zr xc yc zx zy xa qa ya qb xak yak sel xd yd z : Trace}
    {lr hr lq hq sl sh xl xh yl yh Mz Hm Lx Ly : Nat} {xS xE yS yE : Nat → Nat} {xv yv : Nat → Bool}
    (G : MergeGates P rst x y za xo yo ei zr xc yc zx zy xa qa ya qb xak yak)
    (V : MergeEnv P rst x y za R) (Cs : MergeCausal P Eo Es) (hEs : 1 ≤ Es)
    (S : MergeStaticNS P Eo Es wo wz la wa)
    (hRL : P.Wxc.hi ≤ R ∧ P.Wyc.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧
      P.Lxa.hi + P.wxah ≤ R ∧ P.Lya.hi + P.wyah ≤ R)
    (hRE : R ≤ P.AX 0 ∧ R ≤ P.ZA0 0 ∧ R ≤ P.AY 0 ∧ R ≤ P.ZA1 0)
    (hU : Gate 0xE [(x, lr, hr), (xa, lq, hq)] sel) (hlr : lr ≤ hr) (hlq : lq ≤ hq)
    (hR : DmRel sel yd xd z sl sh yl yh xl xh) (hsw : sl ≤ sh) (hyw : yl ≤ yh) (hxw : xl ≤ xh)
    (D : MergeDataEnv P xd yd xS xE yS yE xv yv Lx Ly)
    (SD : MergeDataExact P Eo hr hq sl sh lr lq xl xh yl yh Mz Hm Lx Ly) :
    ∀ k t, P.Z (2 * k) ≤ t + Mz → t ≤ P.ζ (2 * k) + Hm →
      z t = (if P.sv k then yv k else xv k) := by
  have TM := merge_timing_ns_of_static Cs S hRL hRE
  obtain ⟨_, _, _, _, r5, _⟩ := TM.H_RST_LONG
  obtain ⟨u1, u2, _, _⟩ := TM.H_RST_EARLY
  have ax : Tok R xc P.AX (fun k => !P.sv k) := (V.H_X.fifo P.Wxc G.H_WXC).mono (by omega)
  have zx' : Tok R zx P.ZA0 (fun _ => true) := (V.H_ZA.fifo P.Wzx G.H_WZX).mono (by omega)
  have CX : CEl xc zx rst xa qa (fun t => c2B (xc t) (zx t) (qa t) (rst t)) P.Lxa P.wxal P.wxah :=
    ⟨fun t => c2_spec _ _ _ _, G.H_UXA, G.H_UXA_FB, G.H_UXA_POS⟩
  have nx := cel_node CX (cel_run CX ax zx' V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r5 u1 u2 TM.H_DEP_XA)
  have hp := Cs.H_POS
  have RZ := merge_RZ' Cs S
  have RM := merge_ρ_mono' Cs hEs
  intro k t h1 h2
  have hz : 1 ≤ P.ζ (2 * k) := by have := RZ (2 * k); have := hp (2 * k); omega
  have hZ := merge_ρ_le_Z hp k
  have hρ1 := hp (2 * k + 1)
  have hown := Cs.H_OWN (2 * k)
  rw [show 2 * k / 2 = k by omega] at hown
  cases hk : P.sv k
  · -- x owns token k: sel high through x_req (as in `merge_data_ok`)
    rw [hk] at hown; simp only [Bool.false_eq_true, ite_false] at hown
    have hXA := merge_ζ_le_XA (2 * k) hz
    have hZk := hZ.1 hk
    have hxr : StableOn x true (P.ρ (2 * k)) (P.ρ (2 * k + 1) - 1) := fun u u1 u2 => by
      have := V.H_X.hi k u (Nat.zero_le _) u1 (by omega); rw [this, hk]; rfl
    have hsel := usel_high hU hlr _ _ hxr
    have st := dm_settles hR hsw hyw hxw true (xv k) _ _ (xS k) (xE k) hsel (D.H_X_DATA k hk)
    have := D.H_X_LEAD k hk; have := D.H_X_HOLD k hk
    have := SD.S_ZM_SEL_X; have := SD.S_ZM_X; have := SD.S_HM_SEL_X; have := SD.S_HM_X
    simp only [ite_true] at st
    simp only [Bool.false_eq_true, ite_false]
    exact st t (by omega) (by omega)
  · -- y owns token k: x_req and the uxa node low since the last x token
    rw [hk] at hown; simp only [ite_true] at hown
    have hYA := merge_ζ_le_YA (2 * k) hz
    have hZk := hZ.2 hk
    have hXN : P.ρ (2 * k + 1) ≤ P.Lxa.fst (max (P.AX (2 * k + 1)) (P.ZA0 (2 * k + 1))) := by
      have := P.Lxa.fst_ge (max (P.AX (2 * k + 1)) (P.ZA0 (2 * k + 1)))
      have : P.ρ (2 * k + 1) ≤ P.AX (2 * k + 1) := P.Wxc.fst_ge _
      omega
    have hS0 := SD.H_SEL_START
    have hmono := RM 0 (2 * k) (Nat.zero_le _)
    obtain ⟨T1, T2, hx0, ha0, hb1, hb2⟩ : ∃ T1 T2, StableOn x false T1 (P.ρ (2 * k + 1) - 1) ∧
        StableOn xa false T2 (P.ρ (2 * k + 1) - 1) ∧
        T1 + hr + sh + Mz ≤ P.ρ (2 * k) + (P.Wyo.lo + P.Lor.lo + P.Dz.lo) ∧
        T2 + hq + sh + Mz ≤ P.ρ (2 * k) + (P.Wyo.lo + P.Lor.lo + P.Dz.lo) := by
      rcases last_x P.sv k with hall | ⟨k0, hk0, hx0, hbt⟩
      · -- no x token yet: low since start-up
        have slo : ∀ g : Nat → Bool, (∀ i, P.sv i = true → g i = false) →
            ∀ j, j < 2 * k + 1 → Tok.SlotLow g j := fun g hg j hj => by
          rcases Nat.mod_two_eq_zero_or_one j with e | e
          · right; apply hg
            by_cases h' : j / 2 < k
            · exact hall _ h'
            · rw [show j / 2 = k by omega]; exact hk
          · left; exact e
        refine ⟨0, P.Lxa.hi, fun u u1 u2 => ?_, fun u u1 u2 => ?_, by omega, by omega⟩
        · exact V.H_X.low_pre (2 * k + 1) u (slo _ (fun i h => by simp [h])) (Nat.zero_le _) (by omega)
        · exact nx.low_pre (2 * k + 1) u (slo _ (fun i h => by simp [h])) u1 (by omega)
      · -- last x token k0
        have slo : ∀ g : Nat → Bool, (∀ i, P.sv i = true → g i = false) →
            ∀ j, 2 * k0 + 1 ≤ j → j < 2 * k + 1 → Tok.SlotLow g j := fun g hg j hj1 hj2 => by
          rcases Nat.mod_two_eq_zero_or_one j with e | e
          · right; apply hg
            by_cases h' : j / 2 < k
            · exact hbt _ (by omega) h'
            · rw [show j / 2 = k by omega]; exact hk
          · left; exact e
        -- the chain from the x token's fall to the next token's request
        have hd : (2 * k0 + 1) / 2 = k0 := by omega
        have hown := Cs.H_OWN (2 * k0 + 1)
        rw [hd, hx0] at hown; simp only [Bool.false_eq_true, ite_false] at hown
        have hm2 := RM (2 * k0 + 1 + 1) (2 * k) (by omega)
        have hZ1 := (merge_ρ_le_Zj hp (2 * k0 + 1)).1 (by rw [hd]; exact hx0)
        have hs1 := Cs.H_SRV (2 * k0 + 1)
        have hz1 : 1 ≤ P.ζ (2 * k0 + 1) := by have := hp (2 * k0 + 1); omega
        have hxa1 := merge_ζ_le_XA (2 * k0 + 1) hz1
        have hN1 : 1 ≤ P.Lxa.fst (P.cx (2 * k0 + 1)) := by
          have := P.Lxa.fst_ge (P.cx (2 * k0 + 1))
          have : P.ρ (2 * k0 + 1) ≤ P.AX (2 * k0 + 1) := P.Wxc.fst_ge _
          have := hp (2 * k0 + 1)
          unfold MergeRun.cx at *; omega
        have hNX := fl P.Wxa hN1
        have hXAe : P.XA (2 * k0 + 1) = P.Wxa.fst (P.Lxa.fst (P.cx (2 * k0 + 1))) := rfl
        have hcx : P.cx (2 * k0 + 1) = max (P.AX (2 * k0 + 1)) (P.ZA0 (2 * k0 + 1)) := rfl
        have hXA := SD.S_SEL_XA_N; have := SD.S_ZM_SEL_X
        refine ⟨P.ρ (2 * k0 + 1), max P.Lxa.hi (P.Lxa.fst (P.cx (2 * k0 + 1))),
          fun u u1 u2 => ?_, fun u u1 u2 => ?_, by omega, by omega⟩
        · exact V.H_X.low_range (2 * k + 1) (2 * k0 + 1) u (by omega) (slo _ (fun i h => by simp [h]))
            (Nat.zero_le _) u1 (by omega)
        · exact nx.low_range (2 * k + 1) (2 * k0 + 1) u (by omega) (slo _ (fun i h => by simp [h]))
            (by omega) (by rw [← hcx]; omega) (by omega)
    have hsel := usel_low2 hU hlr hlq T1 T2 _ hx0 ha0
    have st := dm_settles hR hsw hyw hxw false (yv k) _ _ (yS k) (yE k) hsel (D.H_Y_DATA k hk)
    have := D.H_Y_LEAD k hk; have := D.H_Y_HOLD k hk
    have := SD.S_ZM_Y; have := SD.S_HM_SEL_Y; have := SD.S_HM_Y
    simp only [Bool.false_eq_true, ite_false] at st
    simp only [ite_true]
    exact st t (by omega) (by omega)

end mergeexact

/-- `merge_data_ok` is a corollary (the old static set implies the exact one). -/
theorem merge_data_ok' {P : MergeRun} {R Eo Es wo wz la wa : Nat}
    {rst x y za xo yo ei zr xc yc zx zy xa qa ya qb xak yak sel xd yd z : Trace}
    {lr hr lq hq sl sh xl xh yl yh Mz Hm Lx Ly : Nat} {xS xE yS yE : Nat → Nat} {xv yv : Nat → Bool}
    (G : MergeGates P rst x y za xo yo ei zr xc yc zx zy xa qa ya qb xak yak)
    (V : MergeEnv P rst x y za R) (Cs : MergeCausal P Eo Es) (hEs : 1 ≤ Es)
    (S : MergeStatic P Eo Es wo wz la wa)
    (hRL : P.Wxc.hi ≤ R ∧ P.Wyc.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧
      P.Lxa.hi + P.wxah ≤ R ∧ P.Lya.hi + P.wyah ≤ R)
    (hRE : R ≤ P.AX 0 ∧ R ≤ P.ZA0 0 ∧ R ≤ P.AY 0 ∧ R ≤ P.ZA1 0)
    (hU : Gate 0xE [(x, lr, hr), (xa, lq, hq)] sel) (hlr : lr ≤ hr) (hlq : lq ≤ hq)
    (hR : DmRel sel yd xd z sl sh yl yh xl xh) (hsw : sl ≤ sh) (hyw : yl ≤ yh) (hxw : xl ≤ xh)
    (D : MergeDataEnv P xd yd xS xE yS yE xv yv Lx Ly)
    (SD : MergeDataStatic P Eo Es wo wz la wa lr hr lq hq sl sh xl xh yl yh Mz Hm Lx Ly) :
    ∀ k t, P.Z (2 * k) ≤ t + Mz → t ≤ P.ζ (2 * k) + Hm →
      z t = (if P.sv k then yv k else xv k) :=
  merge_data_ok_exact G V Cs hEs S.ns hRL hRE hU hlr hlq hR hsw hyw hxw D (SD.exact S)


/-! ## 3. `S_SEL_XA_N` is tight in Lt's unit-delay merge run

`MergeWit.run` (Lt's witness, unit delays, data of `MergeCex`). Boundary of
`S_SEL_XA_N`: `hq + 1 + 0 ≤ 1 + 1 + 3`, i.e. `hq = 4`; at `hq = 5` the
conclusion fails (Lt3's `cex_S_SEL_XA_Z` run: y token 1 reads x's bit). -/
namespace MergeCex
set_option maxRecDepth 100000

theorem apply_exact (dr dq ds dy dx : Nat)
    (SD : MergeDataExact MergeWit.run 1 dr dq ds ds dr dq dx dx dy dy 0 2 4 4) :
    ∀ k t, MergeWit.run.Z (2 * k) ≤ t + 0 → t ≤ MergeWit.run.ζ (2 * k) + 2 →
      zD dr dq ds dy dx t = (if MergeWit.run.sv k then yvC k else xvC k) :=
  merge_data_ok_exact MergeWit.gates MergeWit.env MergeWit.causal (Nat.le_refl 1) MergeWit.static.ns
    (by decide) hRE (sel_gate dr dq) (Nat.le_refl _) (Nat.le_refl _) (z_rel dr dq ds dy dx)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) data_env SD

/-- Boundary `hq = 4`: `merge_data_ok_exact` applies. -/
theorem bnd_S_SEL_XA_N : ∀ k t, MergeWit.run.Z (2 * k) ≤ t + 0 → t ≤ MergeWit.run.ζ (2 * k) + 2 →
    zD 1 4 1 1 1 t = (if MergeWit.run.sv k then yvC k else xvC k) :=
  apply_exact 1 4 1 1 1 (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide)

/-- **Counter-run for S_SEL_XA_N** (`hq = 5`): every other field of
`MergeDataExact` holds, `S_SEL_XA_N` fails by one tick, and the conclusion
fails at y's token 1, instant `Z 2 = 23` (`z = 1`, expected `yvC 1 = 0`). -/
theorem cex_S_SEL_XA_N :
    ¬ (5 + 1 + 0 ≤ MergeWit.run.Wxa.lo + 1 + MergeWit.run.Wyo.lo + MergeWit.run.Lor.lo +
      MergeWit.run.Dz.lo) ∧
    (1 + 1 + 0 ≤ MergeWit.run.Wxo.lo + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo) ∧
    (1 + 0 ≤ 4 + MergeWit.run.Wxo.lo + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo) ∧
    (1 + 0 ≤ 4 + MergeWit.run.Wyo.lo + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo) ∧
    (2 + 1 ≤ MergeWit.run.Wzx.lo + MergeWit.run.Lxa.lo + MergeWit.run.Wxa.lo + 1 + 1 + 1) ∧
    (2 + 1 ≤ MergeWit.run.Wzy.lo + MergeWit.run.Lya.lo + MergeWit.run.Wya.lo + 1 + min 1 5 + 1) ∧
    (2 ≤ MergeWit.run.Wzx.lo + MergeWit.run.Lxa.lo + MergeWit.run.Wxa.lo + 1) ∧
    (2 ≤ MergeWit.run.Wzy.lo + MergeWit.run.Lya.lo + MergeWit.run.Wya.lo + 1) ∧
    (max 1 (MergeWit.run.Lxa.hi + 5) + 1 + 0 ≤ MergeWit.run.ρ 0 +
      (MergeWit.run.Wyo.lo + MergeWit.run.Lor.lo + MergeWit.run.Dz.lo)) ∧
    zD 1 5 1 1 1 23 = true ∧ yvC 1 = false ∧ MergeWit.run.sv 1 = true ∧
    ¬ MergeDataExact MergeWit.run 1 1 5 1 1 1 5 1 1 1 1 0 2 4 4 := by
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, by decide, by decide, rfl, ?_⟩
  intro SD
  have := apply_exact 1 5 1 1 1 SD 1 23 (by rw [MergeWit.Z_eq 2]; omega) (by decide)
  revert this; decide

end MergeCex

/-! ## 4. A merge run whose token 0 is y's: `H_SEL_START` is tight

Lt's unit-delay merge run moved 3 ticks earlier and with the owners swapped:
`ρ j = 8j+1`, `ζ j = 8j+5`, `Z j = 8j+4`, `XA j = YA j = 8j+8`, reset high on
`[0, 2)`, even merged tokens y's, odd x's. Every LUT and wire is one tick;
the uxa C-element's output at `t = 0` is a free parameter `p` (its power-up
value: `H_UXA` constrains it only from `Lxa.hi = 1`, when it has read the
reset). The whole control side is proved for both values of `p`.

`H_SEL_START` here reads `max hr (1 + hq) + sh + Mz ≤ 1 + 3`; with `hr = sh
= 1`, `Mz = 0` its boundary is `hq = 2`, while `S_SEL_XA_N` allows `hq ≤ 4`.
At `hq = 3` only `H_SEL_START` fails, and if uxa powers up HIGH the select
still reads it when y's token 0 reaches the server: `z (Z 0) = x's bit`. -/
namespace MergeY
set_option maxRecDepth 100000

def svY (k : Nat) : Bool := decide (k % 2 = 0)
def rstY (t : Nat) : Bool := decide (t < 2)

def run : MergeRun where
  Wxo := uW
  Wyo := uW
  Lor := uW
  Dz := uW
  Wxc := uW
  Wyc := uW
  Wzx := uW
  Wzy := uW
  Lxa := uW
  Lya := uW
  wxal := 1
  wxah := 1
  wyal := 1
  wyah := 1
  Wxa := uW
  Wya := uW
  ρ j := 8 * j + 1
  ζ j := 8 * j + 5
  sv := svY

def x (t : Nat) : Bool := decide (17 ≤ t ∧ (t - 17) % 32 < 8)
def y (t : Nat) : Bool := decide (1 ≤ t ∧ (t - 1) % 32 < 8)
def za (t : Nat) : Bool := decide (5 ≤ t ∧ (t - 5) % 16 < 8)
def xo (t : Nat) : Bool := x (t - 1)
def yo (t : Nat) : Bool := y (t - 1)
def ei (t : Nat) : Bool := or2B (xo (t - 1)) (yo (t - 1))
def zr (t : Nat) : Bool := ei (t - 1)
def zx (t : Nat) : Bool := za (t - 1)
/-- uxa's output; `p` is its power-up value. -/
def xa (p : Bool) : Nat → Bool
  | 0 => p
  | 1 => c2B (xo 0) (zx 0) p (rstY 0)
  | t + 2 => c2B (xo (t + 1)) (zx (t + 1)) (xa p t) (rstY (t + 1))
def qa (p : Bool) (t : Nat) : Bool := xa p (t - 1)
def ya : Nat → Bool
  | 0 => false
  | 1 => c2B (yo 0) (zx 0) false (rstY 0)
  | t + 2 => c2B (yo (t + 1)) (zx (t + 1)) (ya t) (rstY (t + 1))
def qb (t : Nat) : Bool := ya (t - 1)
def xak (p : Bool) (t : Nat) : Bool := xa p (t - 1)
def yak (t : Nat) : Bool := ya (t - 1)

theorem gates (p : Bool) :
    MergeGates run rstY x y za xo yo ei zr xo yo zx zx (xa p) (qa p) ya qb (xak p) yak where
  H_WXO _ _ := rfl
  H_WYO _ _ := rfl
  H_UOR _ _ := rfl
  H_DZ _ _ := rfl
  H_WXC _ _ := rfl
  H_WYC _ _ := rfl
  H_WZX _ _ := rfl
  H_WZY _ _ := rfl
  H_UXA t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UXA_FB := win11 (fun _ _ => rfl)
  H_UXA_POS := by decide
  H_UYA t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UYA_FB := win11 (fun _ _ => rfl)
  H_UYA_POS := by decide
  H_WXA _ _ := rfl
  H_WYA _ _ := rfl

theorem env : MergeEnv run rstY x y za 2 where
  H_RST_HI t h := by simp [rstY, h]
  H_RST_LO t h := by simp [rstY]; omega
  H_X := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 8 * 0 + 1 := h2
      simp only [x, decide_eq_false_iff_not]; omega
    · have h1 : 8 * (2 * k) + 1 ≤ t := h1
      have h2 : t < 8 * (2 * k + 1) + 1 := h2
      show x t = !decide (k % 2 = 0)
      by_cases hk : k % 2 = 0
      · simp only [x, hk, decide_true, Bool.not_true, decide_eq_false_iff_not]; omega
      · simp only [x, hk, decide_false, Bool.not_false, decide_eq_true_eq]; omega
    · have h1 : 8 * (2 * k + 1) + 1 ≤ t := h1
      have h2 : t < 8 * (2 * k + 2) + 1 := h2
      simp only [x, decide_eq_false_iff_not]; omega
  H_Y := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 8 * 0 + 1 := h2
      simp only [y, decide_eq_false_iff_not]; omega
    · have h1 : 8 * (2 * k) + 1 ≤ t := h1
      have h2 : t < 8 * (2 * k + 1) + 1 := h2
      show y t = decide (k % 2 = 0)
      by_cases hk : k % 2 = 0
      · simp only [y, hk, decide_true, decide_eq_true_eq]; omega
      · simp only [y, hk, decide_false, decide_eq_false_iff_not]; omega
    · have h1 : 8 * (2 * k + 1) + 1 ≤ t := h1
      have h2 : t < 8 * (2 * k + 2) + 1 := h2
      simp only [y, decide_eq_false_iff_not]; omega
  H_ZA := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 8 * 0 + 5 := h2
      simp only [za, decide_eq_false_iff_not]; omega
    · have h1 : 8 * (2 * k) + 5 ≤ t := h1
      have h2 : t < 8 * (2 * k + 1) + 5 := h2
      simp only [za, decide_eq_true_eq]; omega
    · have h1 : 8 * (2 * k + 1) + 5 ≤ t := h1
      have h2 : t < 8 * (2 * k + 2) + 5 := h2
      simp only [za, decide_eq_false_iff_not]; omega

theorem XA_eq (j : Nat) : run.XA j = 8 * j + 8 ∧ run.YA j = 8 * j + 8 := by
  constructor
  · show uW.fst (uW.fst (max (uW.fst (8 * j + 1)) (uW.fst (8 * j + 5)))) = _
    rw [fuW (8 * j + 1) (by omega), fuW (8 * j + 5) (by omega),
      show max (8 * j + 1 + 1) (8 * j + 5 + 1) = 8 * j + 6 by omega,
      fuW (8 * j + 6) (by omega), fuW (8 * j + 6 + 1) (by omega)]
  · show uW.fst (uW.fst (max (uW.fst (8 * j + 1)) (uW.fst (8 * j + 5)))) = _
    rw [fuW (8 * j + 1) (by omega), fuW (8 * j + 5) (by omega),
      show max (8 * j + 1 + 1) (8 * j + 5 + 1) = 8 * j + 6 by omega,
      fuW (8 * j + 6) (by omega), fuW (8 * j + 6 + 1) (by omega)]

theorem Z_eq (j : Nat) : run.Z j = 8 * j + 4 := by
  have h0 : run.XO j = 8 * j + 2 := by show uW.fst (8 * j + 1) = _; rw [fuW _ (by omega)]
  have h1 : run.YO j = 8 * j + 2 := by show uW.fst (8 * j + 1) = _; rw [fuW _ (by omega)]
  unfold MergeRun.Z orEdges
  rw [show run.Lor = uW from rfl, show run.Dz = uW from rfl]
  split
  · rw [h0, fuW (8 * j + 2) (by omega), fuW (8 * j + 2 + 1) (by omega)]
  · rw [h1, fuW (8 * j + 2) (by omega), fuW (8 * j + 2 + 1) (by omega)]

theorem causal : MergeCausal run 1 1 where
  H_OWN j := by
    rw [(XA_eq j).1, (XA_eq j).2]; show _ ≤ 8 * (j + 1) + 1; split <;> omega
  H_SRV j := by rw [Z_eq]; show _ ≤ 8 * j + 5; omega
  H_POS j := by show 1 ≤ 8 * j + 1; omega

theorem static : MergeStatic run 1 1 1 1 1 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem hRE : 2 ≤ run.AX 0 ∧ 2 ≤ run.ZA0 0 ∧ 2 ≤ run.AY 0 ∧ 2 ≤ run.ZA1 0 := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · show 2 ≤ uW.fst (8 * 0 + 1); rw [fuW (8 * 0 + 1) (by omega)]; omega
  · show 2 ≤ uW.fst (8 * 0 + 5); rw [fuW (8 * 0 + 5) (by omega)]; omega
  · show 2 ≤ uW.fst (8 * 0 + 1); rw [fuW (8 * 0 + 1) (by omega)]; omega
  · show 2 ≤ uW.fst (8 * 0 + 5); rw [fuW (8 * 0 + 5) (by omega)]; omega

/-- Non-vacuity of the control side (for either power-up value of uxa). -/
theorem witness (p : Bool) :
    Tok run.Tz zr run.Z (fun _ => true) ∧
    Tok run.Tx (xak p) run.XA (fun k => !run.sv k) ∧ Tok run.Ty yak run.YA run.sv ∧
    (∀ j, run.ρ j ≤ run.Z j ∧ run.ζ j ≤ run.XA j ∧ run.ζ j ≤ run.YA j) :=
  merge_ok_noskew (gates p) env (merge_timing_ns_of_static causal static.ns (by decide) hRE)
    causal (Nat.le_refl 1)

-- data: same values as `MergeCex`; token `k` drives on `[16k, 16k+15]`, `Lx = Ly = 1`
def selD (p : Bool) (dr dq : Nat) (t : Nat) : Bool := lutB 0xE [x (t - dr), xa p (t - dq)]
def zD (p : Bool) (dr dq ds dy dx : Nat) (t : Nat) : Bool :=
  lutB DM_ODD [selD p dr dq (t - ds), MergeCex.ydC (t - dy), MergeCex.xdC (t - dx)]

theorem sel_gate (p : Bool) (dr dq : Nat) : Gate 0xE [(x, dr, dr), (xa p, dq, dq)] (selD p dr dq) :=
  transport_gate 0xE [(x, dr, dr, dr), (xa p, dq, dq, dq)] (selD p dr dq)
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl <;> exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (fun _ => rfl)

theorem z_rel (p : Bool) (dr dq ds dy dx : Nat) :
    DmRel (selD p dr dq) MergeCex.ydC MergeCex.xdC (zD p dr dq ds dy dx) ds ds dy dy dx dx :=
  dm_odd_rel (transport_gate DM_ODD [(selD p dr dq, ds, ds, ds), (MergeCex.ydC, dy, dy, dy),
    (MergeCex.xdC, dx, dx, dx)] (zD p dr dq ds dy dx)
    (by intro q hq; simp only [List.mem_cons, List.not_mem_nil, or_false] at hq
        rcases hq with rfl | rfl | rfl <;> exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (fun _ => rfl))

theorem data_env : MergeDataEnv run MergeCex.xdC MergeCex.ydC (fun k => 16 * k) (fun k => 16 * k + 15)
    (fun k => 16 * k) (fun k => 16 * k + 15) MergeCex.xvC MergeCex.yvC 1 1 where
  H_X_DATA k _ t h1 h2 := by
    show MergeCex.xvC (t / 16) = MergeCex.xvC k; rw [show t / 16 = k by omega]
  H_Y_DATA k _ t h1 h2 := by
    show MergeCex.yvC (t / 16) = MergeCex.yvC k; rw [show t / 16 = k by omega]
  H_X_LEAD k _ := by show _ ≤ 8 * (2 * k) + 1; omega
  H_Y_LEAD k _ := by show _ ≤ 8 * (2 * k) + 1; omega
  H_X_HOLD k _ := by rw [(XA_eq _).1]; show _ ≤ 16 * k + 15; omega
  H_Y_HOLD k _ := by rw [(XA_eq _).2]; show _ ≤ 16 * k + 15; omega

theorem apply_exact (p : Bool) (dr dq ds dy dx : Nat)
    (SD : MergeDataExact run 1 dr dq ds ds dr dq dx dx dy dy 0 2 1 1) :
    ∀ k t, run.Z (2 * k) ≤ t + 0 → t ≤ run.ζ (2 * k) + 2 →
      zD p dr dq ds dy dx t = (if run.sv k then MergeCex.yvC k else MergeCex.xvC k) :=
  merge_data_ok_exact (gates p) env causal (Nat.le_refl 1) static.ns (by decide) hRE
    (sel_gate p dr dq) (Nat.le_refl _) (Nat.le_refl _) (z_rel p dr dq ds dy dx)
    (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) data_env SD

/-- Boundary `hq = 2`: the theorem applies, whatever uxa powers up to. -/
theorem bnd_H_SEL_START (p : Bool) : ∀ k t, run.Z (2 * k) ≤ t + 0 → t ≤ run.ζ (2 * k) + 2 →
    zD p 1 2 1 1 1 t = (if run.sv k then MergeCex.yvC k else MergeCex.xvC k) :=
  apply_exact p 1 2 1 1 1 (by refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide)

/-- **Counter-run for H_SEL_START** (`hq = 3`, uxa powers up high): every
other field of `MergeDataExact` holds (in particular `S_SEL_XA_N`), only
`H_SEL_START` fails (by one tick), and at y's token 0, instant `Z 0 = 4`, the
select still reads uxa's power-up level: `z = xvC 0 = 1`, expected
`yvC 0 = 0`. -/
theorem cex_H_SEL_START :
    ¬ (max 1 (run.Lxa.hi + 3) + 1 + 0 ≤ run.ρ 0 + (run.Wyo.lo + run.Lor.lo + run.Dz.lo)) ∧
    (1 + 1 + 0 ≤ run.Wxo.lo + run.Lor.lo + run.Dz.lo) ∧
    (1 + 0 ≤ 1 + run.Wxo.lo + run.Lor.lo + run.Dz.lo) ∧
    (1 + 0 ≤ 1 + run.Wyo.lo + run.Lor.lo + run.Dz.lo) ∧
    (3 + 1 + 0 ≤ run.Wxa.lo + 1 + run.Wyo.lo + run.Lor.lo + run.Dz.lo) ∧
    (2 + 1 ≤ run.Wzx.lo + run.Lxa.lo + run.Wxa.lo + 1 + 1 + 1) ∧
    (2 + 1 ≤ run.Wzy.lo + run.Lya.lo + run.Wya.lo + 1 + min 1 3 + 1) ∧
    (2 ≤ run.Wzx.lo + run.Lxa.lo + run.Wxa.lo + 1) ∧
    (2 ≤ run.Wzy.lo + run.Lya.lo + run.Wya.lo + 1) ∧
    run.sv 0 = true ∧ run.Z (2 * 0) = 4 ∧ run.ζ (2 * 0) = 5 ∧
    xa true 0 = true ∧ xa true 1 = false ∧
    zD true 1 3 1 1 1 4 = true ∧ MergeCex.yvC 0 = false ∧ MergeCex.xvC 0 = true ∧
    ¬ (∀ k t, run.Z (2 * k) ≤ t + 0 → t ≤ run.ζ (2 * k) + 2 →
      zD true 1 3 1 1 1 t = (if run.sv k then MergeCex.yvC k else MergeCex.xvC k)) ∧
    ¬ MergeDataExact run 1 1 3 1 1 1 3 1 1 1 1 0 2 1 1 := by
  have hz : run.Z (2 * 0) = 4 := Z_eq 0
  have nc : ¬ (∀ k t, run.Z (2 * k) ≤ t + 0 → t ≤ run.ζ (2 * k) + 2 →
      zD true 1 3 1 1 1 t = (if run.sv k then MergeCex.yvC k else MergeCex.xvC k)) := by
    intro h
    have := h 0 4 (by rw [hz]; omega) (by decide)
    revert this; decide
  refine ⟨by decide, by decide, by decide, by decide, by decide, by decide, by decide, by decide,
    by decide, rfl, hz, rfl, rfl, by decide, by decide, by decide, by decide, nc, ?_⟩
  intro SD
  exact nc (apply_exact true 1 3 1 1 1 SD)

/-- The same run with uxa powering up LOW survives the violation: the
counter-run needs the power-up level that `H_SEL_START` exists to cover. -/
theorem surv_H_SEL_START_low : zD false 1 3 1 1 1 4 = MergeCex.yvC 0 ∧
    zD false 1 3 1 1 1 5 = MergeCex.yvC 0 ∧ zD false 1 3 1 1 1 6 = MergeCex.yvC 0 ∧
    zD false 1 3 1 1 1 7 = MergeCex.yvC 0 := by decide

end MergeY


/-! ## 5. An asymmetric mux run: x late at its join, `Wc0 = 2`

Every LUT and wire one tick, except the ctl_req wire to uj0 (`Wc0`), which is
two. Control token `k` (even: x, odd: y) on base `20k`: ctl_req rises at
`20k+8` (x tokens) or `20k+10` (y tokens), falls at `20k+18`. x's request
rises at `20k+10`, so it reaches uj0 at `20k+11`, one tick AFTER ctl_req
(`20k+10` through the 2-tick wire): **x is the join's late input**. y's
request rises at `20k+6`, reaching uj1 4 ticks before ctl_req: ctl is late
there. Uniformly `E (2k) = 20k+12`, `Z (2k) = 20k+15`, `ζ (2k) = 20k+16`,
`XA = YA = 20k+19`, and the falls 10 later. The select is driven from 4 ticks
before each token's ctl_req rise (`Ls = 4`, tight in both kinds of token).

This run separates the mux's data obligations:
* `S_Z_S0` RHS `= Ls + 2 + 1 + 1 + 1 + 1 = 10`, `S_Z_S1` RHS `= 9`: at
  `shi = 10` only `S_Z_S1` fails, and the conclusion fails in a y token;
* `S_Z_X` is TIGHT here (x late): at `ahi = 6` it fails by one tick and the
  conclusion fails in an x token. (Lt3's `MuxWit.run` had 4 ticks of slack.) -/
namespace MuxA
set_option maxRecDepth 100000

def run : MuxRun where
  Wx := uW
  Wy := uW
  Wc0 := Ret.shift 2
  Wc1 := uW
  Lj0 := uW
  Lj1 := uW
  wj0l := 1
  wj0h := 1
  wj1l := 1
  wj1h := 1
  W0o := uW
  W1o := uW
  W0x := uW
  W1y := uW
  Lor := uW
  Dz := uW
  Wzx := uW
  Wzy := uW
  Lxa := uW
  Lya := uW
  wxal := 1
  wxah := 1
  wyal := 1
  wyah := 1
  Wxa := uW
  Wya := uW
  ξ j := 40 * (j / 2) + 10 + 10 * (j % 2)
  η j := 40 * (j / 2) + 26 + 14 * (j % 2)
  γ j := if j % 2 = 0 then 20 * (j / 2) + 8 + 2 * ((j / 2) % 2) else 20 * (j / 2) + 18
  ζ j := 20 * (j / 2) + 16 + 10 * (j % 2)
  sv := svW
  κ0 m := 2 * m
  κ1 m := 2 * m + 1

/-- The control token whose select is on the wire at `t` (token `k` from
`20k + 4 + 2 (k % 2)`, 4 ticks before its ctl_req rise). -/
def sTok (t : Nat) : Nat := if 4 + 2 * ((t / 20) % 2) ≤ t % 20 then t / 20 else t / 20 - 1
def sS (k : Nat) : Nat := 20 * k + 4 + 2 * (k % 2)

theorem sTok_eq (k t : Nat) (h1 : sS k ≤ t) (h2 : t < sS (k + 1)) : sTok t = k := by
  unfold sS at h1 h2
  have e : t / 20 = k ∨ t / 20 = k + 1 := by omega
  rcases Nat.mod_two_eq_zero_or_one k with hk | hk <;> rcases e with e | e <;>
    (unfold sTok; rw [e]; split <;> omega)

-- environment
def x (t : Nat) : Bool := decide (10 ≤ t ∧ (t - 10) % 40 < 10)
def y (t : Nat) : Bool := decide (26 ≤ t ∧ (t - 26) % 40 < 14)
def ctl (t : Nat) : Bool := decide (t % 20 < 18 ∧ 8 + 2 * ((t / 20) % 2) ≤ t % 20)
def za (t : Nat) : Bool := decide (16 ≤ t ∧ (t - 16) % 20 < 10)
def sx (t : Nat) : Bool := svW (sTok t)
-- the cell
def xj (t : Nat) : Bool := x (t - 1)
def yj (t : Nat) : Bool := y (t - 1)
def cj0 (t : Nat) : Bool := ctl (t - 2)
def cj1 (t : Nat) : Bool := ctl (t - 1)
def j0 : Nat → Bool
  | 0 => false
  | 1 => j0B (xj 0) (cj0 0) (sx 0) false (rstW 0)
  | t + 2 => j0B (xj (t + 1)) (cj0 (t + 1)) (sx (t + 1)) (j0 t) (rstW (t + 1))
def q0 (t : Nat) : Bool := j0 (t - 1)
def j1 : Nat → Bool
  | 0 => false
  | 1 => j1B (yj 0) (cj1 0) (sx 0) false (rstW 0)
  | t + 2 => j1B (yj (t + 1)) (cj1 (t + 1)) (sx (t + 1)) (j1 t) (rstW (t + 1))
def q1 (t : Nat) : Bool := j1 (t - 1)
def e0 (t : Nat) : Bool := j0 (t - 1)
def e1 (t : Nat) : Bool := j1 (t - 1)
def ei (t : Nat) : Bool := or2B (e0 (t - 1)) (e1 (t - 1))
def zr (t : Nat) : Bool := ei (t - 1)
def j0x (t : Nat) : Bool := j0 (t - 1)
def j1y (t : Nat) : Bool := j1 (t - 1)
def zx (t : Nat) : Bool := za (t - 1)
def xa : Nat → Bool
  | 0 => false
  | 1 => c2B (j0x 0) (zx 0) false (rstW 0)
  | t + 2 => c2B (j0x (t + 1)) (zx (t + 1)) (xa t) (rstW (t + 1))
def qa (t : Nat) : Bool := xa (t - 1)
def ya : Nat → Bool
  | 0 => false
  | 1 => c2B (j1y 0) (zx 0) false (rstW 0)
  | t + 2 => c2B (j1y (t + 1)) (zx (t + 1)) (ya t) (rstW (t + 1))
def qb (t : Nat) : Bool := ya (t - 1)
def xak (t : Nat) : Bool := xa (t - 1)
def yak (t : Nat) : Bool := ya (t - 1)

theorem gates : MuxGates run rstW x y ctl za xj yj cj0 cj1 sx sx j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zx
    xa qa ya qb xak yak where
  H_WX _ _ := rfl
  H_WY _ _ := rfl
  H_WC0 _ _ := rfl
  H_WC1 _ _ := rfl
  H_UJ0 t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UJ0_FB := win11 (fun _ _ => rfl)
  H_UJ0_POS := by decide
  H_UJ1 t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UJ1_FB := win11 (fun _ _ => rfl)
  H_UJ1_POS := by decide
  H_W0O _ _ := rfl
  H_W1O _ _ := rfl
  H_UOR _ _ := rfl
  H_DZ _ _ := rfl
  H_W0X _ _ := rfl
  H_W1Y _ _ := rfl
  H_WZX _ _ := rfl
  H_WZY _ _ := rfl
  H_UXA t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UXA_FB := win11 (fun _ _ => rfl)
  H_UXA_POS := by decide
  H_UYA t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UYA_FB := win11 (fun _ _ => rfl)
  H_UYA_POS := by decide
  H_WXA _ _ := rfl
  H_WYA _ _ := rfl

theorem enum0 : Enum (fun k => !run.sv k) run.κ0 where
  mono m := by show 2 * m < 2 * (m + 1); omega
  hit m := by show (!decide (2 * m % 2 = 1)) = true; simp
  all k h := ⟨k / 2, by
    have h : (!decide (k % 2 = 1)) = true := h
    simp at h; show 2 * (k / 2) = k; omega⟩

theorem enum1 : Enum run.sv run.κ1 where
  mono m := by show 2 * m + 1 < 2 * (m + 1) + 1; omega
  hit m := by show decide ((2 * m + 1) % 2 = 1) = true; simp
  all k h := ⟨k / 2, by
    have h : decide (k % 2 = 1) = true := h
    simp at h; show 2 * (k / 2) + 1 = k; omega⟩

/-! Closed forms of the derived edges. -/
theorem γ_eq (j : Nat) : run.γ j =
    if j % 2 = 0 then 20 * (j / 2) + 8 + 2 * ((j / 2) % 2) else 20 * (j / 2) + 18 := rfl
theorem Xp_eq (j : Nat) : run.Xp j = 40 * (j / 2) + 11 + 10 * (j % 2) := by
  show uW.fst (40 * (j / 2) + 10 + 10 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem Yp_eq (j : Nat) : run.Yp j = 40 * (j / 2) + 27 + 14 * (j % 2) := by
  show uW.fst (40 * (j / 2) + 26 + 14 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem C0_eq (j : Nat) : run.C0 j = run.γ j + 2 := by
  show (Ret.shift 2).fst (run.γ j) = _
  rw [Ret.fst_shift 2 _ (by rw [γ_eq]; split <;> omega)]
theorem C1_eq (j : Nat) : run.C1 j = run.γ j + 1 := by
  show uW.fst (run.γ j) = _; rw [fuW _ (by rw [γ_eq]; split <;> omega)]
theorem D0_eq (j : Nat) : run.D0 j = 40 * (j / 2) + 10 + 10 * (j % 2) := by
  show run.C0 (2 * (2 * (j / 2)) + j % 2) = _; rw [C0_eq, γ_eq]; split <;> omega
theorem D1_eq (j : Nat) : run.D1 j = 40 * (j / 2) + 31 + 8 * (j % 2) := by
  show run.C1 (2 * (2 * (j / 2) + 1) + j % 2) = _; rw [C1_eq, γ_eq]; split <;> omega
theorem c0_eq (j : Nat) : run.c0 j = 40 * (j / 2) + 11 + 10 * (j % 2) := by
  show max (run.Xp j) (run.D0 j) = _; rw [Xp_eq, D0_eq]; omega
theorem c1_eq (j : Nat) : run.c1 j = 40 * (j / 2) + 31 + 10 * (j % 2) := by
  show max (run.Yp j) (run.D1 j) = _; rw [Yp_eq, D1_eq]; omega
theorem τ0_eq (j : Nat) : run.τ0 j = 40 * (j / 2) + 12 + 10 * (j % 2) := by
  show uW.fst (run.c0 j) = _; rw [c0_eq, fuW _ (by omega)]; omega
theorem τ1_eq (j : Nat) : run.τ1 j = 40 * (j / 2) + 32 + 10 * (j % 2) := by
  show uW.fst (run.c1 j) = _; rw [c1_eq, fuW _ (by omega)]; omega

theorem E_eq (j : Nat) : run.E j = 20 * (j / 2) + 12 + 10 * (j % 2) := by
  unfold MuxRun.E
  rcases Nat.mod_two_eq_zero_or_one (j / 2) with hk | hk
  · have hs : run.sv (j / 2) = false := by show decide (j / 2 % 2 = 1) = false; simp; omega
    have hi : idx run.κ0 (j / 2) = j / 2 / 2 := by
      have := idx_κ enum0 (j / 2 / 2)
      rw [show run.κ0 (j / 2 / 2) = j / 2 by show 2 * (j / 2 / 2) = j / 2; omega] at this
      exact this
    rw [hs, hi]; simp only [Bool.false_eq_true, ite_false]; rw [τ0_eq]; omega
  · have hs : run.sv (j / 2) = true := by show decide (j / 2 % 2 = 1) = true; simp; omega
    have hi : idx run.κ1 (j / 2) = j / 2 / 2 := by
      have := idx_κ enum1 (j / 2 / 2)
      rw [show run.κ1 (j / 2 / 2) = j / 2 by show 2 * (j / 2 / 2) + 1 = j / 2; omega] at this
      exact this
    rw [hs, hi]; simp only [ite_true]; rw [τ1_eq]; omega

theorem env : MuxEnv run rstW x y ctl za sx sx 4 where
  H_RST_HI := rstW_hi
  H_RST_LO := rstW_lo
  H_X := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 40 * (0 / 2) + 10 + 10 * (0 % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
    · have h1 : 40 * (2 * k / 2) + 10 + 10 * (2 * k % 2) ≤ t := h1
      have h2 : t < 40 * ((2 * k + 1) / 2) + 10 + 10 * ((2 * k + 1) % 2) := h2
      simp only [x, decide_eq_true_eq]; omega
    · have h1 : 40 * ((2 * k + 1) / 2) + 10 + 10 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 40 * ((2 * k + 2) / 2) + 10 + 10 * ((2 * k + 2) % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
  H_Y := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 40 * (0 / 2) + 26 + 14 * (0 % 2) := h2
      simp only [y, decide_eq_false_iff_not]; omega
    · have h1 : 40 * (2 * k / 2) + 26 + 14 * (2 * k % 2) ≤ t := h1
      have h2 : t < 40 * ((2 * k + 1) / 2) + 26 + 14 * ((2 * k + 1) % 2) := h2
      simp only [y, decide_eq_true_eq]; omega
    · have h1 : 40 * ((2 * k + 1) / 2) + 26 + 14 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 40 * ((2 * k + 2) / 2) + 26 + 14 * ((2 * k + 2) % 2) := h2
      simp only [y, decide_eq_false_iff_not]; omega
  H_CTL := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · rw [γ_eq] at h2; simp only [ctl, decide_eq_false_iff_not]; split at h2 <;> omega
    · rw [γ_eq] at h1 h2; simp only [ctl, decide_eq_true_eq]
      split at h1 <;> split at h2 <;> omega
    · rw [γ_eq] at h1 h2; simp only [ctl, decide_eq_false_iff_not]
      split at h1 <;> split at h2 <;> omega
  H_ZA := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 20 * (0 / 2) + 16 + 10 * (0 % 2) := h2
      simp only [za, decide_eq_false_iff_not]; omega
    · have h1 : 20 * (2 * k / 2) + 16 + 10 * (2 * k % 2) ≤ t := h1
      have h2 : t < 20 * ((2 * k + 1) / 2) + 16 + 10 * ((2 * k + 1) % 2) := h2
      simp only [za, decide_eq_true_eq]; omega
    · have h1 : 20 * ((2 * k + 1) / 2) + 16 + 10 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 20 * ((2 * k + 2) / 2) + 16 + 10 * ((2 * k + 2) % 2) := h2
      simp only [za, decide_eq_false_iff_not]; omega
  H_ENUM0 := enum0
  H_ENUM1 := enum1
  H_S_PIN0 k t h1 h2 := by
    rw [C0_eq, γ_eq] at h1 h2
    show svW (sTok t) = svW k
    rw [sTok_eq k t (by unfold sS; split at h1 <;> omega) (by unfold sS; split at h2 <;> omega)]
  H_S_PIN1 k t h1 h2 := by
    rw [C1_eq, γ_eq] at h1 h2
    show svW (sTok t) = svW k
    rw [sTok_eq k t (by unfold sS; split at h1 <;> omega) (by unfold sS; split at h2 <;> omega)]

theorem O0_eq (j : Nat) : run.O0 j = run.E j + 1 := by
  show uW.fst (run.E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem O1_eq (j : Nat) : run.O1 j = run.E j + 1 := by
  show uW.fst (run.E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem A0_eq (j : Nat) : run.A0 j = run.E j + 1 := by
  show uW.fst (run.E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem A1_eq (j : Nat) : run.A1 j = run.E j + 1 := by
  show uW.fst (run.E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem ZA_eq (j : Nat) : run.ZA0 j = 20 * (j / 2) + 17 + 10 * (j % 2) ∧
    run.ZA1 j = 20 * (j / 2) + 17 + 10 * (j % 2) := by
  constructor <;> (show uW.fst (20 * (j / 2) + 16 + 10 * (j % 2)) = _; rw [fuW _ (by omega)]; omega)

theorem Z_eq (j : Nat) : run.Z j = run.E j + 3 := by
  unfold MuxRun.Z orEdges
  rw [show run.Lor = uW from rfl, show run.Dz = uW from rfl]
  have hE := E_eq j
  split
  · rw [O0_eq, fuW (run.E j + 1) (by omega), fuW (run.E j + 1 + 1) (by omega)]
  · rw [O1_eq, fuW (run.E j + 1) (by omega), fuW (run.E j + 1 + 1) (by omega)]

theorem XA_eq (j : Nat) : run.XA j = 20 * (j / 2) + 19 + 10 * (j % 2) ∧
    run.YA j = 20 * (j / 2) + 19 + 10 * (j % 2) := by
  have hm : max (run.E j + 1) (20 * (j / 2) + 17 + 10 * (j % 2)) = 20 * (j / 2) + 17 + 10 * (j % 2) := by
    rw [E_eq]; omega
  constructor
  · show uW.fst (uW.fst (max (run.A0 j) (run.ZA0 j))) = _
    rw [A0_eq, (ZA_eq j).1, hm, fuW (20 * (j / 2) + 17 + 10 * (j % 2)) (by omega),
      fuW (20 * (j / 2) + 17 + 10 * (j % 2) + 1) (by omega)]; omega
  · show uW.fst (uW.fst (max (run.A1 j) (run.ZA1 j))) = _
    rw [A1_eq, (ZA_eq j).2, hm, fuW (20 * (j / 2) + 17 + 10 * (j % 2)) (by omega),
      fuW (20 * (j / 2) + 17 + 10 * (j % 2) + 1) (by omega)]; omega

theorem causal : MuxCausal run uW 1 1 1 1 where
  H_XC_FALL m := by
    rw [(XA_eq _).1]; show _ ≤ 40 * ((2 * m + 1) / 2) + 10 + 10 * ((2 * m + 1) % 2)
    show 20 * (2 * (2 * m) / 2) + 19 + 10 * (2 * (2 * m) % 2) + 1 ≤ _; omega
  H_XC_RISE m := by
    rw [(XA_eq _).1]; show _ ≤ 40 * ((2 * m + 2) / 2) + 10 + 10 * ((2 * m + 2) % 2)
    show 20 * ((2 * (2 * m) + 1) / 2) + 19 + 10 * ((2 * (2 * m) + 1) % 2) + 1 ≤ _; omega
  H_YC_FALL m := by
    rw [(XA_eq _).2]; show _ ≤ 40 * ((2 * m + 1) / 2) + 26 + 14 * ((2 * m + 1) % 2)
    show 20 * (2 * (2 * m + 1) / 2) + 19 + 10 * (2 * (2 * m + 1) % 2) + 1 ≤ _; omega
  H_YC_RISE m := by
    rw [(XA_eq _).2]; show _ ≤ 40 * ((2 * m + 2) / 2) + 26 + 14 * ((2 * m + 2) % 2)
    show 20 * ((2 * (2 * m + 1) + 1) / 2) + 19 + 10 * ((2 * (2 * m + 1) + 1) % 2) + 1 ≤ _; omega
  H_CTL_C j := by
    show uW.fst (20 * (j / 2) + 16 + 10 * (j % 2)) + 1 ≤ run.γ (j + 1)
    rw [fuW _ (by omega), γ_eq]; split <;> omega
  H_SRV j := by
    rw [Z_eq, E_eq]; show _ ≤ 20 * (j / 2) + 16 + 10 * (j % 2); omega
  H_POS j := by rw [γ_eq]; split <;> omega

theorem static : MuxStatic run uW 1 1 1 1 1 1 1 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

theorem hRE : 4 ≤ run.Xp 0 ∧ 4 ≤ run.D0 0 ∧ 4 ≤ run.Yp 0 ∧ 4 ≤ run.D1 0 ∧ 4 ≤ run.A0 0 ∧
    4 ≤ run.ZA0 0 ∧ 4 ≤ run.A1 0 ∧ 4 ≤ run.ZA1 0 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Xp_eq]; omega
  · rw [D0_eq]; omega
  · rw [Yp_eq]; omega
  · rw [D1_eq]; omega
  · rw [A0_eq, E_eq]; omega
  · rw [(ZA_eq 0).1]; omega
  · rw [A1_eq, E_eq]; omega
  · rw [(ZA_eq 0).2]; omega

/-- Non-vacuity of the control side (`mux_ok` through the static obligations). -/
theorem witness : Tok run.Tz zr run.Z (fun _ => true) ∧
    Tok run.Tx xak run.XA (fun k => !run.sv k) ∧ Tok run.Ty yak run.YA run.sv :=
  let h := mux_ok_static gates env causal static (by decide) hRE
  ⟨h.1, h.2.1, h.2.2.2.1⟩

/-- The run is what it claims: x arrives at uj0 after ctl_req (x late),
y arrives at uj1 before ctl_req (ctl late); the server sees both kinds. -/
theorem witness_values :
    run.Xp 0 = 11 ∧ run.C0 0 = 10 ∧ run.Yp 0 = 27 ∧ run.C1 2 = 31 ∧
    xak 19 = true ∧ yak 19 = false ∧ xak 39 = false ∧ yak 39 = true ∧
    zr 15 = true ∧ zr 35 = true ∧ j0 11 = false ∧ j0 12 = true := by
  refine ⟨by rw [Xp_eq], by rw [C0_eq]; rfl, by rw [Yp_eq], by rw [C1_eq]; rfl, ?_⟩
  decide

-- data: x's `m`-th bit from its request rise `40m+10` (`Lx = 0`), y's from `40m+26` (`Ly = 0`)
def xdA (t : Nat) : Bool := MuxCex.xvC ((t - 10) / 40)
def ydA (t : Nat) : Bool := MuxCex.yvC ((t - 26) / 40)
def zA (ds da db : Nat) (t : Nat) : Bool := lutB DM_ODD [sx (t - ds), xdA (t - da), ydA (t - db)]

theorem z_rel (ds da db : Nat) : DmRel sx xdA ydA (zA ds da db) ds ds da da db db :=
  dm_odd_rel (transport_gate DM_ODD [(sx, ds, ds, ds), (xdA, da, da, da), (ydA, db, db, db)]
    (zA ds da db)
    (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl <;> exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (fun _ => rfl))

theorem data_env : MuxDataEnv run uW sx xdA ydA sS (fun k => sS (k + 1) - 1) (fun m => 40 * m + 10)
    (fun m => 40 * m + 49) (fun m => 40 * m + 26) (fun m => 40 * m + 65)
    MuxCex.xvC MuxCex.yvC 4 0 0 where
  H_S_DATA k t h1 h2 := by
    show svW (sTok t) = svW k; rw [sTok_eq k t h1 (by unfold sS at h2 ⊢; omega)]
  H_X_DATA m t h1 h2 := by
    show MuxCex.xvC ((t - 10) / 40) = MuxCex.xvC m; rw [show (t - 10) / 40 = m by omega]
  H_Y_DATA m t h1 h2 := by
    show MuxCex.yvC ((t - 26) / 40) = MuxCex.yvC m; rw [show (t - 26) / 40 = m by omega]
  H_S_LEAD k := by
    rw [γ_eq]; unfold sS
    rw [show 2 * k % 2 = 0 by omega, show 2 * k / 2 = k by omega]; simp only [ite_true]; omega
  H_X_LEAD m := by show _ ≤ 40 * (2 * m / 2) + 10 + 10 * (2 * m % 2); omega
  H_Y_LEAD m := by show _ ≤ 40 * (2 * m / 2) + 26 + 14 * (2 * m % 2); omega
  H_S_HOLD k := by
    show uW.fst (20 * (2 * k / 2) + 16 + 10 * (2 * k % 2)) ≤ _
    rw [fuW _ (by omega)]; unfold sS; omega
  H_X_HOLD m := by
    rw [(XA_eq _).1]; show 20 * (2 * (2 * m) / 2) + 19 + 10 * (2 * (2 * m) % 2) ≤ _; omega
  H_Y_HOLD m := by
    rw [(XA_eq _).2]
    show 20 * (2 * (2 * m + 1) / 2) + 19 + 10 * (2 * (2 * m + 1) % 2) ≤ _; omega
  H_POS j := by
    refine ⟨?_, ?_, ?_, ?_⟩
    · rw [γ_eq]; split <;> omega
    · show 1 ≤ 40 * (j / 2) + 10 + 10 * (j % 2); omega
    · show 1 ≤ 40 * (j / 2) + 26 + 14 * (j % 2); omega
    · show 1 ≤ 20 * (j / 2) + 16 + 10 * (j % 2); omega

/-- `mux_value_ok_static` (value half) on this run, pin delays `ds, da, db`,
`wo = 1`, `Mz = 0`, `Ls = 4`, `Lx = Ly = 0`. -/
theorem apply_ok (ds da db : Nat) (SD : MuxDataStatic run 1 ds da db 0 4 0 0) :
    ∀ k t, run.Z (2 * k) ≤ t + 0 → t ≤ run.ζ (2 * k) + run.holdM uW ds da db k →
      zA ds da db t = run.zv MuxCex.xvC MuxCex.yvC k :=
  (mux_value_ok_static gates env causal static (by decide) hRE
    (z_rel ds da db) (Nat.le_refl _) (Nat.le_refl _) (Nat.le_refl _) data_env SD).2

theorem Z_ev (k : Nat) : run.Z (2 * k) = 20 * k + 15 := by rw [Z_eq, E_eq]; omega

/-- Boundary: `shi = 9` (S_Z_S1's; S_Z_S0 has 1 to spare), `ahi = bhi = 5`. -/
theorem bnd : ∀ k t, run.Z (2 * k) ≤ t + 0 → t ≤ run.ζ (2 * k) + run.holdM uW 9 5 5 k →
    zA 9 5 5 t = run.zv MuxCex.xvC MuxCex.yvC k :=
  apply_ok 9 5 5 (by refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> decide)

/-- **S_Z_S1 alone** (`shi = 10`): `S_Z_S0` holds (with equality), `S_Z_S1`
fails by one tick, `S_Z_X`/`S_Z_Y` hold; y's token 0 (control token 1)
still reads token 0's select (x): `z (Z 2) = xvC 0 = 1`, expected
`yvC 0 = 0`. So `S_Z_S1` is necessary on its own. -/
theorem cex_S_Z_S1 :
    (10 + 0 ≤ 4 + run.Wc0.lo + run.Lj0.lo + 1 + run.Lor.lo + run.Dz.lo) ∧
    ¬ (10 + 0 ≤ 4 + run.Wc1.lo + run.Lj1.lo + 1 + run.Lor.lo + run.Dz.lo) ∧
    (1 ≤ run.W0o.lo ∧ 1 ≤ run.W1o.lo) ∧
    (1 + 0 ≤ 0 + run.Wx.lo + run.Lj0.lo + 1 + run.Lor.lo + run.Dz.lo) ∧
    (1 + 0 ≤ 0 + run.Wy.lo + run.Lj1.lo + 1 + run.Lor.lo + run.Dz.lo) ∧
    run.sv 1 = true ∧ run.Z (2 * 1) = 35 ∧ zA 10 1 1 35 = true ∧
      run.zv MuxCex.xvC MuxCex.yvC 1 = false ∧
    ¬ (∀ k t, run.Z (2 * k) ≤ t + 0 →
      t ≤ run.ζ (2 * k) + run.holdM uW 10 1 1 k → zA 10 1 1 t = run.zv MuxCex.xvC MuxCex.yvC k) ∧
    ¬ MuxDataStatic run 1 10 1 1 0 4 0 0 := by
  have z1 := Z_ev 1
  have hv : run.zv MuxCex.xvC MuxCex.yvC 1 = false := by
    unfold MuxRun.zv
    rw [show run.sv 1 = true from rfl, show (1 : Nat) = run.κ1 0 from rfl, idx_κ enum1 0]; rfl
  have nc : ¬ (∀ k t, run.Z (2 * k) ≤ t + 0 →
      t ≤ run.ζ (2 * k) + run.holdM uW 10 1 1 k → zA 10 1 1 t = run.zv MuxCex.xvC MuxCex.yvC k) := by
    intro h
    have := h 1 35 (by rw [z1]; omega) (by
      unfold MuxRun.holdM; rw [show run.sv 1 = true from rfl]; decide)
    rw [hv] at this; revert this; decide
  refine ⟨by decide, by decide, by decide, by decide, by decide, rfl, z1, by decide, hv, nc, ?_⟩
  intro SD; exact nc (apply_ok 10 1 1 SD)

/-- **S_Z_X is tight when x is the late input** (`ahi = 6`, one past its
boundary; S_Z_S0/S1 and S_Z_Y hold): control token 2 (x's token 1) sees
x's previous bit: `z (Z 4) = xvC 0 = 1`, expected `xvC 1 = 0`. -/
theorem cex_S_Z_X :
    ¬ (6 + 0 ≤ 0 + run.Wx.lo + run.Lj0.lo + 1 + run.Lor.lo + run.Dz.lo) ∧
    (1 + 0 ≤ 4 + run.Wc0.lo + run.Lj0.lo + 1 + run.Lor.lo + run.Dz.lo) ∧
    (1 + 0 ≤ 4 + run.Wc1.lo + run.Lj1.lo + 1 + run.Lor.lo + run.Dz.lo) ∧
    (1 + 0 ≤ 0 + run.Wy.lo + run.Lj1.lo + 1 + run.Lor.lo + run.Dz.lo) ∧
    run.sv 2 = false ∧ run.Z (2 * 2) = 55 ∧ zA 1 6 1 55 = true ∧
      run.zv MuxCex.xvC MuxCex.yvC 2 = false ∧
    ¬ (∀ k t, run.Z (2 * k) ≤ t + 0 →
      t ≤ run.ζ (2 * k) + run.holdM uW 1 6 1 k → zA 1 6 1 t = run.zv MuxCex.xvC MuxCex.yvC k) ∧
    ¬ MuxDataStatic run 1 1 6 1 0 4 0 0 := by
  have z2 := Z_ev 2
  have hv : run.zv MuxCex.xvC MuxCex.yvC 2 = false := by
    unfold MuxRun.zv
    rw [show run.sv 2 = false from rfl, show (2 : Nat) = run.κ0 1 from rfl, idx_κ enum0 1]; rfl
  have nc : ¬ (∀ k t, run.Z (2 * k) ≤ t + 0 →
      t ≤ run.ζ (2 * k) + run.holdM uW 1 6 1 k → zA 1 6 1 t = run.zv MuxCex.xvC MuxCex.yvC k) := by
    intro h
    have := h 2 55 (by rw [z2]; omega) (by
      unfold MuxRun.holdM; rw [show run.sv 2 = false from rfl]; decide)
    rw [hv] at this; revert this; decide
  refine ⟨by decide, by decide, by decide, by decide, rfl, z2, by decide, hv, nc, ?_⟩
  intro SD; exact nc (apply_ok 1 6 1 SD)

end MuxA


/-! ## 6. When is the RTZ / z_ack-pulse obligation binding?

`S_XA_RTZ` (mux, `bd_mux.uxa_rtz_env`) and `S_XA_ZA` (merge,
`bd_merge.uxa_feedback`) bound z_ack's pulse at uxa against uxa's loop. They
are implied by the request-edge obligation of the same C-element
(`S_XA_J.1` / `S_XA_R.1`) whenever the z_ack wire's delay SPREAD is no larger
than the request wire's. In particular, with fixed (transport) wire delays
they are redundant; a counter-run for them needs a z_ack wire whose rise and
fall delays differ by more than the other wire's. -/

theorem mux_rtz_of_J {P : MuxRun} {Wzc : Ret} {Ec Es lj wc wo : Nat}
    (hsp : P.Wzx.hi - P.Wzx.lo ≤ P.W0x.hi - P.W0x.lo)
    (hJ : P.W0x.hi + (P.Lxa.hi + P.wxah) ≤
      (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W0x.lo) :
    P.Wzx.hi + (P.Lxa.hi + P.wxah) ≤ P.Wzx.lo + (Wzc.lo + Ec + wc + lj) + (wo + P.Lor.lo + P.Dz.lo + Es) := by
  have := P.Wzx.lo_le_hi; have := P.W0x.lo_le_hi; omega

theorem mux_rtz_y_of_J {P : MuxRun} {Wzc : Ret} {Ec Es lj wc wo : Nat}
    (hsp : P.Wzy.hi - P.Wzy.lo ≤ P.W1y.hi - P.W1y.lo)
    (hJ : P.W1y.hi + (P.Lya.hi + P.wyah) ≤
      (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W1y.lo) :
    P.Wzy.hi + (P.Lya.hi + P.wyah) ≤ P.Wzy.lo + (Wzc.lo + Ec + wc + lj) + (wo + P.Lor.lo + P.Dz.lo + Es) := by
  have := P.Wzy.lo_le_hi; have := P.W1y.lo_le_hi; omega

theorem merge_za_of_R {P : MergeRun} {Eo Es wo wz la wa : Nat}
    (hsp : P.Wzx.hi - P.Wzx.lo ≤ P.Wxc.hi - P.Wxc.lo)
    (hR : P.Wxc.hi + (P.Lxa.hi + P.wxah) ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (wz + la + wa + Eo) + P.Wxc.lo) :
    P.Wzx.hi + (P.Lxa.hi + P.wxah) ≤ P.Wzx.lo + (wz + la + wa + Eo) + (wo + P.Lor.lo + P.Dz.lo + Es) := by
  have := P.Wzx.lo_le_hi; have := P.Wxc.lo_le_hi; omega

end Formal.Cells.OpsTimed
