import Formal.Cells.OpsExact2
import Formal.Cells.Necessity4Mux

/-!
# Necessity7Mux: `bd_mux` with `H_DEP` asked only at real edges

Probe Bnx7 (shard B). `mux_ok` (`OpsTimedMux`) runs `cel_run` at the ack
C-elements uxa / uya, and `cel_run` asks the C-element's env latency
(`H_DEP_XA`) at EVERY edge of both inputs, including j0's edges in the
tokens that select y. There j0 does not move: those edges are bookkeeping
edges of a gated-off token. The static form `MuxStatic` pays for them with
`S_XA_FORK` (`bd_mux.isochronic_forks`) and `S_XA_J.1` (first conjunct of
`bd_mux.uxa_join_latency`).

This file re-proves the mux with Lt5's gate-aware `cel_run_g`
(`OpsExact2`), which asks `H_DEP` only in gate-on tokens plus one plain
ORDER fact per y → x hand-over.

* `MuxTimingG`: `MuxTiming` with `H_DEP_XA` / `H_DEP_YA` asked only in the
  owner's tokens, `H_SEQ_XA` / `H_SEQ_YA` (order, no loop term) in their
  place across a hand-over, and without `H_CTL_SEQ` / `H_OR_SKEW` (both
  follow from port-level causality, `MuxCausal`).
* `mux_ok_g`: `mux_ok`'s whole conclusion (`MuxConcl`) from `MuxGates +
  MuxEnv + MuxTimingG + MuxCausal` and `1 ≤ Es`.
* `MuxStaticG`, `mux_timing_g_of_static`, `mux_ok_gs`: the static form.
  Relative to `MuxStatic` it drops `S_XA_FORK`, `S_XA_J.1` (and the y
  mirrors) and `S_OR`, and adds
  - `S_XA_SEQ : Wzx.hi ≤ Kc + W0x.lo` (y → x hand-over: z_ack's fall from
    the y token reaches uxa no later than the x token's j0 rise);
  - `S_XA_R : S_XA_N ∨ (S_XA_FORK ∧ S_XA_J.1)`, where
    `S_XA_N : Lxa.hi + wxah ≤ Lxa.lo + Wxa.lo + Ex + Wx.lo + Lj0.lo + W0x.lo`
    is the node-launched client loop (in an x token the next j0 edge is
    causally after x_ack through the x client), and the right disjunct is
    the shipped pair (the same edge is also after z_ack through the control
    sender, because the join waits for ctl_req too).
  `staticG_of_static`: `MuxStatic → MuxStaticG` (the new set is implied by
  the shipped one).

`Kz = wo + Lor.lo + Dz.lo + Es`, `Kc = Wzc.lo + Ec + wc + lj` as in
`OpsTimedMux`. The counter-runs are in `Necessity7MuxRuns`.

## Assumed / proved / NOT covered

Assumed: OpsTimedMux's model (lumped FIFO LUT arcs `H_LUT_FIFO`, window
wires, FIFO line `H_LINE_FIFO`, port-level causal partners `MuxCausal` with
minimum latencies, server latency `Es ≥ 1`), real INITs of uj0 / uj1 / uor /
bd_c2 (through `MuxGates`). Proved: as above (binary `≤` forms).
NOT covered: per-pin LUT arcs; the Kleene X `+1` (CElemStrict); an iff.
-/

namespace Formal.Cells.Necessity7Mux
open Formal.Cells
open Formal.Cells.OpsTimed
open Formal.Cells.PipeTimed (Ret Trace)
open Formal.Cells.LibCtlMergeMux (or2B c2B j0B j1B or2_spec c2_spec j0_spec j1_spec)
open Formal.Cells.Necessity4Mux (MuxConcl)

/-! ## 1. Event form -/

/-- **`MuxTiming` with `H_DEP` only at real edges.** uxa's env latency is
asked only in x's tokens (and against j0's next edge only when that edge is
x's); in its place across a y → x hand-over, the order fact `H_SEQ_XA`
(no loop latency). Symmetrically for uya. `H_CTL_SEQ` and `H_OR_SKEW` are
not asked (they follow from `MuxCausal`). -/
structure MuxTimingG (P : MuxRun) (R : Nat) : Prop where
  H_RST_LONG : P.Wx.hi ≤ R ∧ P.Wy.hi ≤ R ∧ P.Wc0.hi ≤ R ∧ P.Wc1.hi ≤ R ∧
    P.Lj0.hi + P.wj0h ≤ R ∧ P.Lj1.hi + P.wj1h ≤ R ∧ P.Lj0.hi + P.W0x.hi ≤ R ∧
    P.Lj1.hi + P.W1y.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧ P.Lxa.hi + P.wxah ≤ R ∧
    P.Lya.hi + P.wyah ≤ R
  /-- Only z_ack's first edge must follow reset release at uxa / uya. -/
  H_RST_EARLY : R ≤ P.Xp 0 ∧ R ≤ P.D0 0 ∧ R ≤ P.Yp 0 ∧ R ≤ P.D1 0 ∧ R ≤ P.ZA0 0 ∧ R ≤ P.ZA1 0
  H_DEP_J0 : ∀ j, P.c0 j + P.Lj0.hi + P.wj0h ≤ P.Xp (j + 1) ∧ P.c0 j + P.Lj0.hi + P.wj0h ≤ P.D0 (j + 1)
  H_DEP_J1 : ∀ j, P.c1 j + P.Lj1.hi + P.wj1h ≤ P.Yp (j + 1) ∧ P.c1 j + P.Lj1.hi + P.wj1h ≤ P.D1 (j + 1)
  H_DEP_XA : ∀ j, P.sv (j / 2) = false → P.cx j + P.Lxa.hi + P.wxah ≤ P.ZA0 (j + 1) ∧
    (P.sv ((j + 1) / 2) = false → P.cx j + P.Lxa.hi + P.wxah ≤ P.A0 (j + 1))
  H_DEP_YA : ∀ j, P.sv (j / 2) = true → P.cy j + P.Lya.hi + P.wyah ≤ P.ZA1 (j + 1) ∧
    (P.sv ((j + 1) / 2) = true → P.cy j + P.Lya.hi + P.wyah ≤ P.A1 (j + 1))
  H_SEQ_XA : ∀ k, P.sv k = true → P.sv (k + 1) = false → P.ZA0 (2 * k + 1) ≤ P.A0 (2 * k + 2)
  H_SEQ_YA : ∀ k, P.sv k = false → P.sv (k + 1) = true → P.ZA1 (2 * k + 1) ≤ P.A1 (2 * k + 2)

/-- The shipped event form implies the new one. -/
theorem MuxTiming.g {P : MuxRun} {R : Nat} (TM : MuxTiming P R) : MuxTimingG P R := by
  obtain ⟨_, _, _, _, a5, a6, _, a8⟩ := TM.H_RST_EARLY
  refine ⟨TM.H_RST_LONG, ⟨TM.H_RST_EARLY.1, TM.H_RST_EARLY.2.1, TM.H_RST_EARLY.2.2.1,
    TM.H_RST_EARLY.2.2.2.1, a6, a8⟩, TM.H_DEP_J0, TM.H_DEP_J1,
    fun j _ => ⟨(TM.H_DEP_XA j).2, fun _ => (TM.H_DEP_XA j).1⟩,
    fun j _ => ⟨(TM.H_DEP_YA j).2, fun _ => (TM.H_DEP_YA j).1⟩, fun k _ _ => ?_, fun k _ _ => ?_⟩
  · have := (TM.H_DEP_XA (2 * k + 1)).1
    unfold MuxRun.cx at this; rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega] at this; omega
  · have := (TM.H_DEP_YA (2 * k + 1)).1
    unfold MuxRun.cy at this; rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega] at this; omega

section ord
variable {P : MuxRun} {Wzc : Ret} {Ex Ey Ec Es : Nat}

/-- Port-level ordering of the derived edges (no static inequality needed). -/
theorem γ_le_E' (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (j : Nat) : P.γ j ≤ P.E j := by
  have h := C_le_E hE0 hE1 Cs.H_POS j
  cases hs : P.sv (j / 2)
  · have := (h.2 hs).1; have := P.Wc0.fst_ge (P.γ j); unfold MuxRun.C0 at *; omega
  · have := (h.1 hs).1; have := P.Wc1.fst_ge (P.γ j); unfold MuxRun.C1 at *; omega

theorem E_le_or (j : Nat) : P.E j ≤ orEdges (fun k => !P.sv k) P.O0 P.O1 j := by
  unfold orEdges MuxRun.O0 MuxRun.O1
  split
  · exact P.W0o.fst_ge _
  · exact P.W1o.fst_ge _

theorem or_le_Z (j : Nat) : orEdges (fun k => !P.sv k) P.O0 P.O1 j ≤ P.Z j := by
  unfold MuxRun.Z
  have := P.Lor.fst_ge (orEdges (fun k => !P.sv k) P.O0 P.O1 j)
  have := P.Dz.fst_ge (P.Lor.fst (orEdges (fun k => !P.sv k) P.O0 P.O1 j))
  omega

theorem ζ_step (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (j : Nat) :
    P.ζ j + Ec ≤ P.E (j + 1) ∧ P.E j + Es ≤ P.ζ j := by
  have h1 := Cs.H_CTL_C j; have := Wzc.fst_ge (P.ζ j)
  have := γ_le_E' hE0 hE1 Cs (j + 1)
  have := Cs.H_SRV j; have := E_le_or (P := P) j; have := or_le_Z (P := P) j
  omega

end ord

/-! ## 2. `mux_ok_g` -/

section muxg
variable {P : MuxRun} {R : Nat} {Wzc : Ret} {Ex Ey Ec Es : Nat}

/-- **`mux_ok_g`: `mux_ok` with `H_DEP` only at real edges.** Same
conclusion as `mux_ok`. -/
theorem mux_ok_g {rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa
      ya qb xak yak : Trace}
    (G : MuxGates P rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa
      ya qb xak yak)
    (V : MuxEnv P rst x y ctl za sx0 sx1 R) (TM : MuxTimingG P R)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (hEs : 1 ≤ Es) :
    MuxConcl P j0 j1 zr xak yak := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10, r11, r12⟩ := TM.H_RST_LONG
  obtain ⟨u1, u2, u3, u4, u6, u8⟩ := TM.H_RST_EARLY
  have st := ζ_step V.H_ENUM0 V.H_ENUM1 Cs
  have Em : ∀ j, P.E j ≤ P.E (j + 1) := fun j => by have := (st j).1; have := (st j).2; omega
  have ζm : ∀ j, P.ζ j ≤ P.ζ (j + 1) := fun j => by
    have := (st j).1; have := (st (j + 1)).2; omega
  have ζu : ∀ n, n ≤ P.ζ n := by
    intro n; induction n with
    | zero => omega
    | succ n ih => have := (st n).1; have := (st (n + 1)).2; omega
  -- join 0, x-indexed
  have hxj : Tok R xj P.Xp (fun _ => true) := ((V.H_X.fifo P.Wx G.H_WX).mono (by omega))
  have hdec0 : Tok R (fun t => cj0 t && !sx0 t) P.D0 (fun _ => true) :=
    (((V.H_CTL.fifo P.Wc0 G.H_WC0).gate (fun a b => a && !b) (fun _ => rfl) (s := sx0) (sv := P.sv)
      (fun k t _ h1 h2 => V.H_S_PIN0 k t h1 h2)).reindex V.H_ENUM0).mono (by omega)
  have C0 : CEl xj (fun t => cj0 t && !sx0 t) rst j0 q0
      (fun t => j0B (xj t) (cj0 t) (sx0 t) (q0 t) (rst t)) P.Lj0 P.wj0l P.wj0h :=
    ⟨fun t => j0_spec _ _ _ _ _, G.H_UJ0, G.H_UJ0_FB, G.H_UJ0_POS⟩
  have n0 := cel_node C0 (cel_run C0 hxj hdec0 V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r5 u1 u2 TM.H_DEP_J0)
  have j0E : Tok P.Lj0.hi j0 P.E (fun k => !P.sv k) :=
    ((n0.congr (fun j => (E_rx0 V.H_ENUM0 j).symm)).lift V.H_ENUM0 Em)
  -- join 1, y-indexed
  have hyj : Tok R yj P.Yp (fun _ => true) := ((V.H_Y.fifo P.Wy G.H_WY).mono (by omega))
  have hdec1 : Tok R (fun t => cj1 t && sx1 t) P.D1 (fun _ => true) :=
    (((V.H_CTL.fifo P.Wc1 G.H_WC1).gate (fun a b => a && b) (fun _ => rfl) (s := sx1) (sv := P.sv)
      (fun k t _ h1 h2 => V.H_S_PIN1 k t h1 h2)).reindex V.H_ENUM1).mono (by omega)
  have C1 : CEl yj (fun t => cj1 t && sx1 t) rst j1 q1
      (fun t => j1B (yj t) (cj1 t) (sx1 t) (q1 t) (rst t)) P.Lj1 P.wj1l P.wj1h :=
    ⟨fun t => j1_spec _ _ _ _ _, G.H_UJ1, G.H_UJ1_FB, G.H_UJ1_POS⟩
  have n1 := cel_node C1 (cel_run C1 hyj hdec1 V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r6 u3 u4 TM.H_DEP_J1)
  have j1E : Tok P.Lj1.hi j1 P.E P.sv :=
    ((n1.congr (fun j => (E_rx1 V.H_ENUM1 j).symm)).lift V.H_ENUM1 Em)
  -- uor and the delay line: no skew condition (the OR's inputs are ordered by causality)
  have p0 : Tok (P.Lj0.hi + P.W0o.hi + (P.Lj1.hi + P.W1o.hi)) e0 P.O0 (fun k => !P.sv k) :=
    (j0E.fifo P.W0o G.H_W0O).mono (by omega)
  have p1 : Tok (P.Lj0.hi + P.W0o.hi + (P.Lj1.hi + P.W1o.hi)) e1 P.O1 (fun k => !(!P.sv k)) :=
    ((j1E.fifo P.W1o G.H_W1O).mono (by omega)).gcongr (fun k => by simp)
  have Sm : ∀ a b, a ≤ b → orEdges (fun k => !P.sv k) P.O0 P.O1 a ≤
      orEdges (fun k => !P.sv k) P.O0 P.O1 b :=
    mono_of_step _ (fun j => by
      have := or_le_Z (P := P) j; have := (st j).1; have := (st j).2
      have := E_le_or (P := P) (j + 1); have := Cs.H_SRV j; omega)
  have o := or_tok_mono p0 p1
    (fun t => ⟨t + 2, by
      have := ζu (t + 1); have := (st (t + 1)).1; rw [show t + 1 + 1 = t + 2 by omega] at this; have := P.W0o.fst_ge (P.E (t + 2))
      unfold MuxRun.O0; omega⟩)
    (fun t => ⟨t + 2, by
      have := ζu (t + 1); have := (st (t + 1)).1; rw [show t + 1 + 1 = t + 2 by omega] at this; have := P.W1o.fst_ge (P.E (t + 2))
      unfold MuxRun.O1; omega⟩)
    Sm
  have zt := (o.fifo P.Lor (y := ei) (fun t ht => by rw [G.H_UOR t ht, or2_spec])).fifo P.Dz G.H_DZ
  -- the acknowledge C-elements, gate-aware
  have A0m : ∀ j, P.A0 j ≤ P.A0 (j + 1) := fun j => fst_mono _ (Em j)
  have A1m : ∀ j, P.A1 j ≤ P.A1 (j + 1) := fun j => fst_mono _ (Em j)
  have Z0m : ∀ j, P.ZA0 j ≤ P.ZA0 (j + 1) := fun j => fst_mono _ (ζm j)
  have Z1m : ∀ j, P.ZA1 j ≤ P.ZA1 (j + 1) := fun j => fst_mono _ (ζm j)
  have A0u : ∀ t, ∃ n, t < P.A0 n := fun t =>
    ⟨t + 2, by have := ζu (t + 1); have := (st (t + 1)).1; rw [show t + 1 + 1 = t + 2 by omega] at this; have := P.W0x.fst_ge (P.E (t + 2))
               unfold MuxRun.A0; omega⟩
  have A1u : ∀ t, ∃ n, t < P.A1 n := fun t =>
    ⟨t + 2, by have := ζu (t + 1); have := (st (t + 1)).1; rw [show t + 1 + 1 = t + 2 by omega] at this; have := P.W1y.fst_ge (P.E (t + 2))
               unfold MuxRun.A1; omega⟩
  have Z0u : ∀ t, ∃ n, t < P.ZA0 n := fun t =>
    ⟨t + 1, by have := ζu (t + 1); have := P.Wzx.fst_ge (P.ζ (t + 1)); unfold MuxRun.ZA0; omega⟩
  have Z1u : ∀ t, ∃ n, t < P.ZA1 n := fun t =>
    ⟨t + 1, by have := ζu (t + 1); have := P.Wzy.fst_ge (P.ζ (t + 1)); unfold MuxRun.ZA1; omega⟩
  have ax : Tok R j0x P.A0 (fun k => !P.sv k) := (j0E.fifo P.W0x G.H_W0X).mono (by omega)
  have zx' : Tok R zx P.ZA0 (fun _ => true) := (V.H_ZA.fifo P.Wzx G.H_WZX).mono (by omega)
  have CX : CEl j0x zx rst xa qa (fun t => c2B (j0x t) (zx t) (qa t) (rst t)) P.Lxa P.wxal P.wxah :=
    ⟨fun t => c2_spec _ _ _ _, G.H_UXA, G.H_UXA_FB, G.H_UXA_POS⟩
  have nx := cel_node CX (cel_run_g CX ax zx' V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r11 u6
    (fun j hj => by
      have h := TM.H_DEP_XA j (by simpa using hj)
      exact ⟨h.1, fun h2 => h.2 (by simpa using h2)⟩)
    Z0m (fun k h1 h2 => TM.H_SEQ_XA k (by simpa using h1) (by simpa using h2))
    (fun j => by have := A0m j; have := Z0m j; omega) A0u Z0u)
  have xk : Tok P.Tx xak P.XA (fun k => !P.sv k) := nx.fifo P.Wxa G.H_WXA
  have ay : Tok R j1y P.A1 P.sv := (j1E.fifo P.W1y G.H_W1Y).mono (by omega)
  have zy' : Tok R zy P.ZA1 (fun _ => true) := (V.H_ZA.fifo P.Wzy G.H_WZY).mono (by omega)
  have CY : CEl j1y zy rst ya qb (fun t => c2B (j1y t) (zy t) (qb t) (rst t)) P.Lya P.wyal P.wyah :=
    ⟨fun t => c2_spec _ _ _ _, G.H_UYA, G.H_UYA_FB, G.H_UYA_POS⟩
  have ny := cel_node CY (cel_run_g CY ay zy' V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r12 u8
    TM.H_DEP_YA Z1m TM.H_SEQ_YA (fun j => by have := A1m j; have := Z1m j; omega) A1u Z1u)
  have yk : Tok P.Ty yak P.YA P.sv := ny.fifo P.Wya G.H_WYA
  refine ⟨j0E, j1E, zt.congr (fun j => rfl), xk, xk.reindex V.H_ENUM0, yk, yk.reindex V.H_ENUM1,
    fun m => ?_, fun m => ?_, fun j => ?_⟩
  · have e := E_rx0 V.H_ENUM0 (2 * m); rw [rx_e] at e; rw [e]
    have := P.Lj0.fst_ge (P.c0 (2 * m))
    have hd : P.D0 (2 * m) = P.C0 (2 * P.κ0 m) := rx_e _ _ m
    unfold MuxRun.τ0 MuxRun.c0 at *; omega
  · have e := E_rx1 V.H_ENUM1 (2 * m); rw [rx_e] at e; rw [e]
    have := P.Lj1.fst_ge (P.c1 (2 * m))
    have hd : P.D1 (2 * m) = P.C1 (2 * P.κ1 m) := rx_e _ _ m
    unfold MuxRun.τ1 MuxRun.c1 at *; omega
  · unfold MuxRun.XA MuxRun.YA MuxRun.cx MuxRun.cy MuxRun.ZA0 MuxRun.ZA1
    have := P.Wzx.fst_ge (P.ζ j); have := P.Wzy.fst_ge (P.ζ j)
    have := P.Lxa.fst_ge (max (P.A0 j) (P.Wzx.fst (P.ζ j)))
    have := P.Wxa.fst_ge (P.Lxa.fst (max (P.A0 j) (P.Wzx.fst (P.ζ j))))
    have := P.Lya.fst_ge (max (P.A1 j) (P.Wzy.fst (P.ζ j)))
    have := P.Wya.fst_ge (P.Lya.fst (max (P.A1 j) (P.Wzy.fst (P.ζ j))))
    omega

/-- `mux_ok_g` generalises `mux_ok` (under causal partners with `1 ≤ Es`). -/
theorem mux_ok_of_timing {rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa
      ya qb xak yak : Trace}
    (G : MuxGates P rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa
      ya qb xak yak)
    (V : MuxEnv P rst x y ctl za sx0 sx1 R) (TM : MuxTiming P R)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (hEs : 1 ≤ Es) :
    MuxConcl P j0 j1 zr xak yak := mux_ok_g G V (MuxTiming.g TM) Cs hEs

end muxg

/-! ## 3. Static form -/

/-- **Static per-arc obligations, real edges only.** `MuxStatic` without
`S_OR`, `S_XA_FORK`, `S_XA_J.1` (and the y mirrors); with `S_XA_R` (the
uxa loop against j0's next REAL edge: the client loop `S_XA_N`, or the
shipped fork pair) and `S_XA_SEQ` (y → x hand-over, order only). -/
structure MuxStaticG (P : MuxRun) (Wzc : Ret) (Ex Ey Ec Es lj wc wo : Nat) : Prop where
  H_LJ : lj ≤ P.Lj0.lo ∧ lj ≤ P.Lj1.lo
  H_WC : wc ≤ P.Wc0.lo ∧ wc ≤ P.Wc1.lo
  H_WO : wo ≤ P.W0o.lo ∧ wo ≤ P.W1o.lo
  S_J0_X : P.Lj0.hi + P.wj0h ≤ P.Lj0.lo + P.W0x.lo + P.Lxa.lo + P.Wxa.lo + Ex + P.Wx.lo
  S_J1_Y : P.Lj1.hi + P.wj1h ≤ P.Lj1.lo + P.W1y.lo + P.Lya.lo + P.Wya.lo + Ey + P.Wy.lo
  S_J0_C : P.Lj0.hi + P.wj0h ≤ P.Lj0.lo + (wo + P.Lor.lo + P.Dz.lo + Es) + Wzc.lo + Ec + P.Wc0.lo
  S_J1_C : P.Lj1.hi + P.wj1h ≤ P.Lj1.lo + (wo + P.Lor.lo + P.Dz.lo + Es) + Wzc.lo + Ec + P.Wc1.lo
  S_XA_RTZ : P.Wzx.hi + (P.Lxa.hi + P.wxah) ≤ P.Wzx.lo + (Wzc.lo + Ec + wc + lj) + (wo + P.Lor.lo + P.Dz.lo + Es)
  S_YA_RTZ : P.Wzy.hi + (P.Lya.hi + P.wyah) ≤ P.Wzy.lo + (Wzc.lo + Ec + wc + lj) + (wo + P.Lor.lo + P.Dz.lo + Es)
  /-- `S_XA_J.2` (unchanged, Necessity6MuxJ: necessary at the boundary). -/
  S_XA_J2 : P.W0x.hi + (P.Lxa.hi + P.wxah) ≤ 2 * (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.Wzx.lo
  S_YA_J2 : P.W1y.hi + (P.Lya.hi + P.wyah) ≤ 2 * (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.Wzy.lo
  /-- **S_XA_R**: in an x token, uxa's loop settles before j0's next (real)
  edge reaches uxa: through the x client (`S_XA_N`, node-launched), or
  through the control sender (the shipped `S_XA_FORK ∧ S_XA_J.1`). -/
  S_XA_R : P.Lxa.hi + P.wxah ≤ P.Lxa.lo + P.Wxa.lo + Ex + P.Wx.lo + P.Lj0.lo + P.W0x.lo ∨
    (P.Wzx.hi + (P.Lxa.hi + P.wxah) ≤ (Wzc.lo + Ec + wc + lj) + P.W0x.lo ∧
     P.W0x.hi + (P.Lxa.hi + P.wxah) ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W0x.lo)
  S_YA_R : P.Lya.hi + P.wyah ≤ P.Lya.lo + P.Wya.lo + Ey + P.Wy.lo + P.Lj1.lo + P.W1y.lo ∨
    (P.Wzy.hi + (P.Lya.hi + P.wyah) ≤ (Wzc.lo + Ec + wc + lj) + P.W1y.lo ∧
     P.W1y.hi + (P.Lya.hi + P.wyah) ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W1y.lo)
  /-- **S_XA_SEQ**: y → x hand-over, z_ack's fall (y token) reaches uxa no
  later than the x token's j0 rise (launched by the same fall through the
  control sender). Order only, no loop term. -/
  S_XA_SEQ : P.Wzx.hi ≤ (Wzc.lo + Ec + wc + lj) + P.W0x.lo
  S_YA_SEQ : P.Wzy.hi ≤ (Wzc.lo + Ec + wc + lj) + P.W1y.lo

/-- The shipped static set implies the new one. -/
theorem staticG_of_static {P : MuxRun} {Wzc : Ret} {Ex Ey Ec Es lj wc wo : Nat}
    (S : MuxStatic P Wzc Ex Ey Ec Es lj wc wo) : MuxStaticG P Wzc Ex Ey Ec Es lj wc wo where
  H_LJ := S.H_LJ
  H_WC := S.H_WC
  H_WO := S.H_WO
  S_J0_X := S.S_J0_X
  S_J1_Y := S.S_J1_Y
  S_J0_C := S.S_J0_C
  S_J1_C := S.S_J1_C
  S_XA_RTZ := S.S_XA_RTZ
  S_YA_RTZ := S.S_YA_RTZ
  S_XA_J2 := S.S_XA_J.2
  S_YA_J2 := S.S_YA_J.2
  S_XA_R := Or.inr ⟨S.S_XA_FORK, S.S_XA_J.1⟩
  S_YA_R := Or.inr ⟨S.S_YA_FORK, S.S_YA_J.1⟩
  S_XA_SEQ := by have := S.S_XA_FORK; omega
  S_YA_SEQ := by have := S.S_YA_FORK; omega

section gstatic
variable {P : MuxRun} {Wzc : Ret} {Ex Ey Ec Es lj wc wo : Nat}

theorem GEg (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1) (hpos : ∀ j, 1 ≤ P.γ j)
    (hLJ : lj ≤ P.Lj0.lo ∧ lj ≤ P.Lj1.lo) (hWC : wc ≤ P.Wc0.lo ∧ wc ≤ P.Wc1.lo) (j : Nat) :
    P.γ j + wc + lj ≤ P.E j ∧ 1 ≤ P.E j := by
  have h := C_le_E hE0 hE1 hpos j
  have := hpos j
  cases hs : P.sv (j / 2)
  · have := (h.2 hs).1
    have := fl P.Wc0 (hpos j); unfold MuxRun.C0 at *; omega
  · have := (h.1 hs).1
    have := fl P.Wc1 (hpos j); unfold MuxRun.C1 at *; omega

theorem EZg (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (hLJ : lj ≤ P.Lj0.lo ∧ lj ≤ P.Lj1.lo)
    (hWC : wc ≤ P.Wc0.lo ∧ wc ≤ P.Wc1.lo) (hWO : wo ≤ P.W0o.lo ∧ wo ≤ P.W1o.lo) (j : Nat) :
    P.E j + (wo + P.Lor.lo + P.Dz.lo + Es) ≤ P.ζ j := by
  have hE := (GEg hE0 hE1 Cs.H_POS hLJ hWC j).2
  have hs := Cs.H_SRV j
  unfold MuxRun.Z orEdges at hs
  unfold MuxRun.O0 MuxRun.O1 at hs
  split at hs
  · have a := fl P.W0o hE
    have b := fl P.Lor (c := P.W0o.fst (P.E j)) (by omega)
    have c := fl P.Dz (c := P.Lor.fst (P.W0o.fst (P.E j))) (by omega)
    omega
  · have a := fl P.W1o hE
    have b := fl P.Lor (c := P.W1o.fst (P.E j)) (by omega)
    have c := fl P.Dz (c := P.Lor.fst (P.W1o.fst (P.E j))) (by omega)
    omega

theorem ZEg (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (hLJ : lj ≤ P.Lj0.lo ∧ lj ≤ P.Lj1.lo)
    (hWC : wc ≤ P.Wc0.lo ∧ wc ≤ P.Wc1.lo) (hWO : wo ≤ P.W0o.lo ∧ wo ≤ P.W1o.lo) (j : Nat) :
    P.ζ j + (Wzc.lo + Ec + wc + lj) ≤ P.E (j + 1) := by
  have h1 := Cs.H_CTL_C j
  have hz : 1 ≤ P.ζ j := by
    have := EZg hE0 hE1 Cs hLJ hWC hWO j; have := (GEg hE0 hE1 Cs.H_POS hLJ hWC j).2; omega
  have h2 := fl Wzc hz
  have h3 := (GEg hE0 hE1 Cs.H_POS hLJ hWC (j + 1)).1
  omega

theorem GMg (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (hLJ : lj ≤ P.Lj0.lo ∧ lj ≤ P.Lj1.lo)
    (hWC : wc ≤ P.Wc0.lo ∧ wc ≤ P.Wc1.lo) (hWO : wo ≤ P.W0o.lo ∧ wo ≤ P.W1o.lo) :
    ∀ a b, a ≤ b → P.γ a ≤ P.γ b :=
  mono_of_step _ (fun j => by
    have := (GEg hE0 hE1 Cs.H_POS hLJ hWC j).1
    have := EZg hE0 hE1 Cs hLJ hWC hWO j
    have := Cs.H_CTL_C j
    have := Wzc.fst_ge (P.ζ j)
    omega)

/-- In an x token `k`, the x-indexed token `m` it consumes (`κ0 m = k`),
and j0's edges at uxa are launched by x_req's edges at uj0. -/
theorem A0_of_x (hE0 : Enum (fun k => !P.sv k) P.κ0) (Cs : MuxCausal P Wzc Ex Ey Ec Es)
    (m r : Nat) (hr : r < 2) :
    P.Xp (2 * m + r) + P.Lj0.lo + P.W0x.lo ≤ P.A0 (2 * P.κ0 m + r) := by
  have hs : P.sv (P.κ0 m) = false := by have := hE0.hit m; simpa using this
  have hE : P.E (2 * P.κ0 m + r) = P.τ0 (2 * m + r) := by
    unfold MuxRun.E
    rw [show (2 * P.κ0 m + r) / 2 = P.κ0 m by omega, show (2 * P.κ0 m + r) % 2 = r by omega, hs,
      idx_κ hE0]
    rfl
  have hc : 1 ≤ P.c0 (2 * m + r) := by
    have := Cs.H_POS (2 * P.κ0 ((2 * m + r) / 2) + (2 * m + r) % 2)
    have := P.Wc0.fst_ge (P.γ (2 * P.κ0 ((2 * m + r) / 2) + (2 * m + r) % 2))
    have hd : P.D0 (2 * m + r) = P.C0 (2 * P.κ0 ((2 * m + r) / 2) + (2 * m + r) % 2) := rfl
    unfold MuxRun.c0 MuxRun.C0 at *; omega
  have a := fl P.Lj0 hc
  have b := fl P.W0x (c := P.τ0 (2 * m + r)) (by unfold MuxRun.τ0 at *; omega)
  unfold MuxRun.A0; rw [hE]; unfold MuxRun.τ0 MuxRun.c0 at *; omega

/-- The same for uj1 / uya. -/
theorem A1_of_y (hE1 : Enum P.sv P.κ1) (Cs : MuxCausal P Wzc Ex Ey Ec Es)
    (m r : Nat) (hr : r < 2) :
    P.Yp (2 * m + r) + P.Lj1.lo + P.W1y.lo ≤ P.A1 (2 * P.κ1 m + r) := by
  have hs : P.sv (P.κ1 m) = true := hE1.hit m
  have hE : P.E (2 * P.κ1 m + r) = P.τ1 (2 * m + r) := by
    unfold MuxRun.E
    rw [show (2 * P.κ1 m + r) / 2 = P.κ1 m by omega, show (2 * P.κ1 m + r) % 2 = r by omega, hs,
      idx_κ hE1]
    rfl
  have hc : 1 ≤ P.c1 (2 * m + r) := by
    have := Cs.H_POS (2 * P.κ1 ((2 * m + r) / 2) + (2 * m + r) % 2)
    have := P.Wc1.fst_ge (P.γ (2 * P.κ1 ((2 * m + r) / 2) + (2 * m + r) % 2))
    have hd : P.D1 (2 * m + r) = P.C1 (2 * P.κ1 ((2 * m + r) / 2) + (2 * m + r) % 2) := rfl
    unfold MuxRun.c1 MuxRun.C1 at *; omega
  have a := fl P.Lj1 hc
  have b := fl P.W1y (c := P.τ1 (2 * m + r)) (by unfold MuxRun.τ1 at *; omega)
  unfold MuxRun.A1; rw [hE]; unfold MuxRun.τ1 MuxRun.c1 at *; omega

/-- Two consecutive x tokens are consecutive in the x enumeration. -/
theorem κ_succ {g : Nat → Bool} {κ : Nat → Nat} (h : Enum g κ) {m k : Nat} (hm : κ m = k)
    (hk : g (k + 1) = true) : κ (m + 1) = k + 1 := by
  obtain ⟨n, hn⟩ := h.all (k + 1) hk
  have h1 : m < n := h.lt_rev (by omega)
  have h2 := h.le_of_le (show m + 1 ≤ n by omega)
  have h3 := h.mono m
  omega

/-- **The event-form obligations from port-level causality and
`MuxStaticG`.** Reset sequencing stays as given. -/
theorem mux_timing_g_of_static {R : Nat} (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (S : MuxStaticG P Wzc Ex Ey Ec Es lj wc wo)
    (hRL : P.Wx.hi ≤ R ∧ P.Wy.hi ≤ R ∧ P.Wc0.hi ≤ R ∧ P.Wc1.hi ≤ R ∧
      P.Lj0.hi + P.wj0h ≤ R ∧ P.Lj1.hi + P.wj1h ≤ R ∧ P.Lj0.hi + P.W0x.hi ≤ R ∧
      P.Lj1.hi + P.W1y.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧ P.Lxa.hi + P.wxah ≤ R ∧
      P.Lya.hi + P.wyah ≤ R)
    (hRE : R ≤ P.Xp 0 ∧ R ≤ P.D0 0 ∧ R ≤ P.Yp 0 ∧ R ≤ P.D1 0 ∧ R ≤ P.ZA0 0 ∧ R ≤ P.ZA1 0) :
    MuxTimingG P R := by
  have hLJ := S.H_LJ; have hWC := S.H_WC; have hWO := S.H_WO
  have EZ := EZg hE0 hE1 Cs hLJ hWC hWO
  have ZE := ZEg hE0 hE1 Cs hLJ hWC hWO
  have GE := GEg hE0 hE1 Cs.H_POS hLJ hWC
  have GM := GMg hE0 hE1 Cs hLJ hWC hWO
  have e0 : ∀ j, P.τ0 j = P.E (2 * P.κ0 (j / 2) + j % 2) := fun j => by
    have := E_rx0 hE0 j; unfold rx at this; exact this.symm
  have e1 : ∀ j, P.τ1 j = P.E (2 * P.κ1 (j / 2) + j % 2) := fun j => by
    have := E_rx1 hE1 j; unfold rx at this; exact this.symm
  have XAge : ∀ i, P.E i + P.W0x.lo + P.Lxa.lo + P.Wxa.lo ≤ P.XA i := by
    intro i
    have hE := (GE i).2
    have a := fl P.W0x hE
    have hcA : P.A0 i ≤ P.cx i := by unfold MuxRun.cx; omega
    have hA : P.A0 i = P.W0x.fst (P.E i) := rfl
    have b := fl P.Lxa (c := P.cx i) (by omega)
    have c := fl P.Wxa (c := P.Lxa.fst (P.cx i)) (by omega)
    show _ ≤ P.Wxa.fst (P.Lxa.fst (P.cx i)); omega
  have YAge : ∀ i, P.E i + P.W1y.lo + P.Lya.lo + P.Wya.lo ≤ P.YA i := by
    intro i
    have hE := (GE i).2
    have a := fl P.W1y hE
    have hcA : P.A1 i ≤ P.cy i := by unfold MuxRun.cy; omega
    have hA : P.A1 i = P.W1y.fst (P.E i) := rfl
    have b := fl P.Lya (c := P.cy i) (by omega)
    have c := fl P.Wya (c := P.Lya.fst (P.cy i)) (by omega)
    show _ ≤ P.Wya.fst (P.Lya.fst (P.cy i)); omega
  -- an acknowledge at its client follows the C-element's phase start (node-launched)
  have XAc : ∀ i, P.cx i + P.Lxa.lo + P.Wxa.lo ≤ P.XA i := by
    intro i
    have hE := (GE i).2
    have a := fl P.W0x hE
    have hcA : P.A0 i ≤ P.cx i := by unfold MuxRun.cx; omega
    have hA : P.A0 i = P.W0x.fst (P.E i) := rfl
    have b := fl P.Lxa (c := P.cx i) (by omega)
    have c := fl P.Wxa (c := P.Lxa.fst (P.cx i)) (by omega)
    show _ ≤ P.Wxa.fst (P.Lxa.fst (P.cx i)); omega
  have YAc : ∀ i, P.cy i + P.Lya.lo + P.Wya.lo ≤ P.YA i := by
    intro i
    have hE := (GE i).2
    have a := fl P.W1y hE
    have hcA : P.A1 i ≤ P.cy i := by unfold MuxRun.cy; omega
    have hA : P.A1 i = P.W1y.fst (P.E i) := rfl
    have b := fl P.Lya (c := P.cy i) (by omega)
    have c := fl P.Wya (c := P.Lya.fst (P.cy i)) (by omega)
    show _ ≤ P.Wya.fst (P.Lya.fst (P.cy i)); omega
  have t0 : ∀ j, P.c0 j + P.Lj0.lo ≤ P.τ0 j ∧ 1 ≤ P.c0 j := by
    intro j
    have hd : P.D0 j = P.C0 (2 * P.κ0 (j / 2) + j % 2) := rfl
    have := P.Wc0.fst_ge (P.γ (2 * P.κ0 (j / 2) + j % 2)); have := Cs.H_POS (2 * P.κ0 (j / 2) + j % 2)
    have c1 : 1 ≤ P.c0 j := by unfold MuxRun.c0 MuxRun.C0 at *; omega
    exact ⟨fl P.Lj0 c1, c1⟩
  have t1 : ∀ j, P.c1 j + P.Lj1.lo ≤ P.τ1 j ∧ 1 ≤ P.c1 j := by
    intro j
    have hd : P.D1 j = P.C1 (2 * P.κ1 (j / 2) + j % 2) := rfl
    have := P.Wc1.fst_ge (P.γ (2 * P.κ1 (j / 2) + j % 2)); have := Cs.H_POS (2 * P.κ1 (j / 2) + j % 2)
    have c1 : 1 ≤ P.c1 j := by unfold MuxRun.c1 MuxRun.C1 at *; omega
    exact ⟨fl P.Lj1 c1, c1⟩
  -- the client loop: in an x token, j0's next x edge at uxa follows x_ack
  have xloop : ∀ j, P.sv (j / 2) = false → P.sv ((j + 1) / 2) = false →
      P.cx j + P.Lxa.lo + P.Wxa.lo + Ex + P.Wx.lo + P.Lj0.lo + P.W0x.lo ≤ P.A0 (j + 1) := by
    intro j h0 h1
    obtain ⟨m, hm⟩ := hE0.all (j / 2) (by simp [h0])
    have hX : P.XA j + Ex + P.Wx.lo ≤ P.Xp (2 * m + (j + 1) % 2 + 2 * ((j % 2))) ∧
        2 * P.κ0 m + (j + 1) % 2 + 2 * (j % 2) = j + 1 ∧
        ((j % 2 = 0 ∧ (2 * m + (j + 1) % 2 + 2 * (j % 2)) = 2 * m + 1) ∨
         (j % 2 = 1 ∧ (2 * m + (j + 1) % 2 + 2 * (j % 2)) = 2 * (m + 1))) := by
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · have hx := Cs.H_XC_FALL m
        rw [hm, show 2 * (j / 2) = j by omega] at hx
        have hp : 1 ≤ P.ξ (2 * m + 1) := by have := (GE j).2; have := XAge j; omega
        have := fl P.Wx hp
        refine ⟨?_, by omega, Or.inl ⟨hj, by omega⟩⟩
        rw [show 2 * m + (j + 1) % 2 + 2 * (j % 2) = 2 * m + 1 by omega]
        unfold MuxRun.Xp; omega
      · have hx := Cs.H_XC_RISE m
        rw [hm, show 2 * (j / 2) + 1 = j by omega] at hx
        have hp : 1 ≤ P.ξ (2 * m + 2) := by have := (GE j).2; have := XAge j; omega
        have := fl P.Wx hp
        refine ⟨?_, by omega, Or.inr ⟨hj, by omega⟩⟩
        rw [show 2 * m + (j + 1) % 2 + 2 * (j % 2) = 2 * m + 2 by omega]
        unfold MuxRun.Xp; omega
    obtain ⟨hX, _, hc⟩ := hX
    have hXA := XAc j
    rcases hc with ⟨hj, he⟩ | ⟨hj, he⟩
    · have := A0_of_x hE0 Cs m 1 (by omega)
      rw [he] at hX
      rw [show 2 * P.κ0 m + 1 = j + 1 by omega] at this
      omega
    · have hk1 := κ_succ hE0 hm (by rw [show j / 2 + 1 = (j + 1) / 2 by omega]; simp [h1])
      have := A0_of_x hE0 Cs (m + 1) 0 (by omega)
      rw [he] at hX
      rw [hk1, show 2 * (j / 2 + 1) + 0 = j + 1 by omega,
        show 2 * (m + 1) + 0 = 2 * (m + 1) by omega] at this
      omega
  have yloop : ∀ j, P.sv (j / 2) = true → P.sv ((j + 1) / 2) = true →
      P.cy j + P.Lya.lo + P.Wya.lo + Ey + P.Wy.lo + P.Lj1.lo + P.W1y.lo ≤ P.A1 (j + 1) := by
    intro j h0 h1
    obtain ⟨m, hm⟩ := hE1.all (j / 2) h0
    have hX : P.YA j + Ey + P.Wy.lo ≤ P.Yp (2 * m + (j + 1) % 2 + 2 * ((j % 2))) ∧
        2 * P.κ1 m + (j + 1) % 2 + 2 * (j % 2) = j + 1 ∧
        ((j % 2 = 0 ∧ (2 * m + (j + 1) % 2 + 2 * (j % 2)) = 2 * m + 1) ∨
         (j % 2 = 1 ∧ (2 * m + (j + 1) % 2 + 2 * (j % 2)) = 2 * (m + 1))) := by
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · have hx := Cs.H_YC_FALL m
        rw [hm, show 2 * (j / 2) = j by omega] at hx
        have hp : 1 ≤ P.η (2 * m + 1) := by have := (GE j).2; have := YAge j; omega
        have := fl P.Wy hp
        refine ⟨?_, by omega, Or.inl ⟨hj, by omega⟩⟩
        rw [show 2 * m + (j + 1) % 2 + 2 * (j % 2) = 2 * m + 1 by omega]
        unfold MuxRun.Yp; omega
      · have hx := Cs.H_YC_RISE m
        rw [hm, show 2 * (j / 2) + 1 = j by omega] at hx
        have hp : 1 ≤ P.η (2 * m + 2) := by have := (GE j).2; have := YAge j; omega
        have := fl P.Wy hp
        refine ⟨?_, by omega, Or.inr ⟨hj, by omega⟩⟩
        rw [show 2 * m + (j + 1) % 2 + 2 * (j % 2) = 2 * m + 2 by omega]
        unfold MuxRun.Yp; omega
    obtain ⟨hX, _, hc⟩ := hX
    have hYA := YAc j
    rcases hc with ⟨hj, he⟩ | ⟨hj, he⟩
    · have := A1_of_y hE1 Cs m 1 (by omega)
      rw [he] at hX
      rw [show 2 * P.κ1 m + 1 = j + 1 by omega] at this
      omega
    · have hk1 := κ_succ hE1 hm (by rw [show j / 2 + 1 = (j + 1) / 2 by omega]; exact h1)
      have := A1_of_y hE1 Cs (m + 1) 0 (by omega)
      rw [he] at hX
      rw [hk1, show 2 * (j / 2 + 1) + 0 = j + 1 by omega,
        show 2 * (m + 1) + 0 = 2 * (m + 1) by omega] at this
      omega
  refine ⟨hRL, hRE, fun j => ⟨?_, ?_⟩, fun j => ⟨?_, ?_⟩, fun j _ => ⟨?_, fun _ => ?_⟩,
    fun j _ => ⟨?_, fun _ => ?_⟩, fun k _ _ => ?_, fun k _ _ => ?_⟩
  · -- uj0, through x (as `mux_timing_of_static`)
    have hXA : P.XA (2 * P.κ0 (j / 2) + j % 2) + Ex ≤ P.ξ (j + 1) := by
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m := ⟨j / 2, by omega⟩
        have := Cs.H_XC_FALL m
        rw [show 2 * m / 2 = m by omega, show 2 * m % 2 = 0 by omega, Nat.add_zero]; exact this
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m + 1 := ⟨j / 2, by omega⟩
        have := Cs.H_XC_RISE m
        rw [show (2 * m + 1) / 2 = m by omega, show (2 * m + 1) % 2 = 1 by omega]; exact this
    have := XAge (2 * P.κ0 (j / 2) + j % 2)
    have hpos : 1 ≤ P.ξ (j + 1) := by have := (GE (2 * P.κ0 (j / 2) + j % 2)).2; omega
    have := fl P.Wx hpos
    have : P.Xp (j + 1) = P.Wx.fst (P.ξ (j + 1)) := rfl
    have := (t0 j).1; have := e0 j; have := S.S_J0_X
    omega
  · -- uj0, through the server and the control sender
    have hk : P.D0 (j + 1) = P.C0 (2 * P.κ0 ((j + 1) / 2) + (j + 1) % 2) := rfl
    have hge : 2 * P.κ0 (j / 2) + j % 2 + 1 ≤ 2 * P.κ0 ((j + 1) / 2) + (j + 1) % 2 := by
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · rw [show (j + 1) / 2 = j / 2 by omega]; omega
      · have := hE0.mono (j / 2); rw [show (j + 1) / 2 = j / 2 + 1 by omega]; omega
    have g := GM _ _ hge
    have hC := fl P.Wc0 (Cs.H_POS (2 * P.κ0 ((j + 1) / 2) + (j + 1) % 2))
    have hz := EZ (2 * P.κ0 (j / 2) + j % 2)
    have hc := Cs.H_CTL_C (2 * P.κ0 (j / 2) + j % 2)
    have hzz : 1 ≤ P.ζ (2 * P.κ0 (j / 2) + j % 2) := by
      have := (GE (2 * P.κ0 (j / 2) + j % 2)).2; omega
    have hw := fl Wzc hzz
    have := (t0 j).1; have := e0 j; have := S.S_J0_C
    unfold MuxRun.C0 at hk hC; omega
  · -- uj1, through y
    have hYA : P.YA (2 * P.κ1 (j / 2) + j % 2) + Ey ≤ P.η (j + 1) := by
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m := ⟨j / 2, by omega⟩
        have := Cs.H_YC_FALL m
        rw [show 2 * m / 2 = m by omega, show 2 * m % 2 = 0 by omega, Nat.add_zero]; exact this
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m + 1 := ⟨j / 2, by omega⟩
        have := Cs.H_YC_RISE m
        rw [show (2 * m + 1) / 2 = m by omega, show (2 * m + 1) % 2 = 1 by omega]; exact this
    have := YAge (2 * P.κ1 (j / 2) + j % 2)
    have hpos : 1 ≤ P.η (j + 1) := by have := (GE (2 * P.κ1 (j / 2) + j % 2)).2; omega
    have := fl P.Wy hpos
    have : P.Yp (j + 1) = P.Wy.fst (P.η (j + 1)) := rfl
    have := (t1 j).1; have := e1 j; have := S.S_J1_Y
    omega
  · -- uj1, through the server and the control sender
    have hk : P.D1 (j + 1) = P.C1 (2 * P.κ1 ((j + 1) / 2) + (j + 1) % 2) := rfl
    have hge : 2 * P.κ1 (j / 2) + j % 2 + 1 ≤ 2 * P.κ1 ((j + 1) / 2) + (j + 1) % 2 := by
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · rw [show (j + 1) / 2 = j / 2 by omega]; omega
      · have := hE1.mono (j / 2); rw [show (j + 1) / 2 = j / 2 + 1 by omega]; omega
    have g := GM _ _ hge
    have hC := fl P.Wc1 (Cs.H_POS (2 * P.κ1 ((j + 1) / 2) + (j + 1) % 2))
    have hz := EZ (2 * P.κ1 (j / 2) + j % 2)
    have hc := Cs.H_CTL_C (2 * P.κ1 (j / 2) + j % 2)
    have hzz : 1 ≤ P.ζ (2 * P.κ1 (j / 2) + j % 2) := by
      have := (GE (2 * P.κ1 (j / 2) + j % 2)).2; omega
    have hw := fl Wzc hzz
    have := (t1 j).1; have := e1 j; have := S.S_J1_C
    unfold MuxRun.C1 at hk hC; omega
  · -- H_DEP_XA against the next z_ack edge (H_MUX_RTZ and S_XA_J.2, as shipped)
    have := P.W0x.fst_le (P.E j); have := P.Wzx.fst_le (P.ζ j)
    have hz1 : 1 ≤ P.ζ (j + 1) := by have := EZ (j + 1); have := (GE (j + 1)).2; omega
    have := fl P.Wzx hz1
    have := ZE j; have := EZ j; have := EZ (j + 1); have := S.S_XA_RTZ; have := S.S_XA_J2
    unfold MuxRun.cx MuxRun.A0 MuxRun.ZA0; omega
  · -- H_DEP_XA against j0's next real edge: the client loop or the fork pair
    rename_i h0 h1
    rcases S.S_XA_R with hN | ⟨hF, hJ⟩
    · have := xloop j h0 h1; omega
    · have := P.W0x.fst_le (P.E j); have := P.Wzx.fst_le (P.ζ j)
      have := fl P.W0x (GE (j + 1)).2
      have := ZE j; have := EZ j
      unfold MuxRun.cx MuxRun.A0 MuxRun.ZA0; omega
  · have := P.W1y.fst_le (P.E j); have := P.Wzy.fst_le (P.ζ j)
    have hz1 : 1 ≤ P.ζ (j + 1) := by have := EZ (j + 1); have := (GE (j + 1)).2; omega
    have := fl P.Wzy hz1
    have := ZE j; have := EZ j; have := EZ (j + 1); have := S.S_YA_RTZ; have := S.S_YA_J2
    unfold MuxRun.cy MuxRun.A1 MuxRun.ZA1; omega
  · rename_i h0 h1
    rcases S.S_YA_R with hN | ⟨hF, hJ⟩
    · have := yloop j h0 h1; omega
    · have := P.W1y.fst_le (P.E j); have := P.Wzy.fst_le (P.ζ j)
      have := fl P.W1y (GE (j + 1)).2
      have := ZE j; have := EZ j
      unfold MuxRun.cy MuxRun.A1 MuxRun.ZA1; omega
  · -- H_SEQ_XA: order only
    have := ZE (2 * k + 1); have := S.S_XA_SEQ
    have hE := (GE (2 * k + 2)).2
    have h := fst_order P.Wzx P.W0x (a := P.ζ (2 * k + 1)) (b := P.E (2 * k + 2)) hE
      (by rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega] at *; omega)
    unfold MuxRun.ZA0 MuxRun.A0; exact h
  · have := ZE (2 * k + 1); have := S.S_YA_SEQ
    have hE := (GE (2 * k + 2)).2
    have h := fst_order P.Wzy P.W1y (a := P.ζ (2 * k + 1)) (b := P.E (2 * k + 2)) hE
      (by rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega] at *; omega)
    unfold MuxRun.ZA1 MuxRun.A1; exact h

/-- Reset sequencing as `mux_ok_gs` takes it (no first request edge at uxa
/ uya need follow reset release). -/
def MuxRstG (P : MuxRun) (R : Nat) : Prop :=
  (P.Wx.hi ≤ R ∧ P.Wy.hi ≤ R ∧ P.Wc0.hi ≤ R ∧ P.Wc1.hi ≤ R ∧
    P.Lj0.hi + P.wj0h ≤ R ∧ P.Lj1.hi + P.wj1h ≤ R ∧ P.Lj0.hi + P.W0x.hi ≤ R ∧
    P.Lj1.hi + P.W1y.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧ P.Lxa.hi + P.wxah ≤ R ∧
    P.Lya.hi + P.wyah ≤ R) ∧
  (R ≤ P.Xp 0 ∧ R ≤ P.D0 0 ∧ R ≤ P.Yp 0 ∧ R ≤ P.D1 0 ∧ R ≤ P.ZA0 0 ∧ R ≤ P.ZA1 0)

/-- **`mux_ok_gs` (sufficient).** `mux_ok`'s whole conclusion from the gates,
the environment, causal partners (`1 ≤ Es`), `MuxStaticG` and reset
sequencing. -/
theorem mux_ok_gs {R : Nat} {rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y
      zx zy xa qa ya qb xak yak : Trace}
    (G : MuxGates P rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa
      ya qb xak yak)
    (V : MuxEnv P rst x y ctl za sx0 sx1 R) (Cs : MuxCausal P Wzc Ex Ey Ec Es) (hEs : 1 ≤ Es)
    (S : MuxStaticG P Wzc Ex Ey Ec Es lj wc wo) (hR : MuxRstG P R) :
    MuxConcl P j0 j1 zr xak yak :=
  mux_ok_g G V (mux_timing_g_of_static V.H_ENUM0 V.H_ENUM1 Cs S hR.1 hR.2) Cs hEs

end gstatic

end Formal.Cells.Necessity7Mux
