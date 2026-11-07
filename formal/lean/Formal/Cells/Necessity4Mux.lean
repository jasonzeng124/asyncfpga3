import Formal.Cells.OpsTimedWit

/-!
# Necessity4Mux: `bd_mux.uj_env_latency_req` is NOT necessary; its max-form replacement

Probe Bnx4 (shard B). The row `bd_mux.uj_env_latency_req` is the
`MuxStatic` field pair `S_J0_X` / `S_J1_Y` (`OpsTimedMux`):

    S_J0_X : Lj0.hi + wj0h ≤ Lj0.lo + W0x.lo + Lxa.lo + Wxa.lo + Ex + Wx.lo

It bounds the x return path (join → uxa → x_ack → client → x_req → join) by
the j0 → uxa branch alone. But uxa is a C-element of j0 AND z_ack, so x_ack
moves only after `cx = max (A0, ZA0)`, and the z_ack edge is itself launched
by the same join edge through uor, the line and the server (Lt4's analysis,
B-ops-exact.md section 5, not proved there).

## Result

* `MuxStaticN … s0 s1` is `MuxStatic` with `S_J0_X` / `S_J1_Y` replaced by
  the **max form** (weakened by `s0` / `s1` ticks):

      S_J0_XR : Lj0.hi + wj0h ≤ Lj0.lo + max W0x.lo (W0o.lo + Lor.lo + Dz.lo + Es + Wzx.lo)
                                + Lxa.lo + Wxa.lo + Ex + Wx.lo + s0

  (and the y twin with W1y, W1o, Wzy, Lya, Wya, Ey, Wy). Every other field is
  `MuxStatic`'s, word for word.
* `staticN_of_static`: `MuxStatic → MuxStaticN 0 0` (the max form is weaker).
* `mux_timing_of_staticN`, `mux_ok_staticN`: **sufficient**. `mux_ok`'s
  whole conclusion from `MuxGates + MuxEnv + MuxCausal + MuxStaticN 0 0 +`
  reset sequencing. This is `mux_timing_of_static` with one branch of the
  proof changed (the x/y return now waits for z_ack too).
* `pass8`: **`S_J0_X` is NOT necessary.** A concrete run (`N4.run 8`, real
  INITs, every gate relation for all `t`) whose uj0 feedback net is 8 ticks:
  `S_J0_X` fails by 3 (`9 ≤ 6` is false), every `MuxStaticN 0 0` field holds,
  and `mux_ok_staticN` gives `mux_ok`'s full conclusion. Since
  `mux_ok_staticN` covers EVERY run with these arc windows and partner
  latencies, this is non-necessity over the box, not one lucky run. The
  same run satisfies the strict (+1, CElemStrict) max form too (`10 ≤ 10`),
  and violates the strict original by 4.
* `fail10`: **the max form is necessary at the boundary, on its new z_ack
  branch.** The same run family with a 10-tick feedback net (`N4.run 10`):
  every `MuxStaticN … 1 0` field holds (the max form weakened by ONE tick),
  `S_J0_XR` itself fails by exactly 1 (`11 ≤ 10`), every other hypothesis of
  `mux_ok_staticN` holds, and the conclusion fails: j0 drops at 32 inside its
  token-0 window [22, 35) (x_req's fall reaches uj0 at 31, one tick before
  the 10-tick feedback shows j0 = 1), and z_req drops at 35 inside its window
  [25, 38). In this run `W0o.lo + Lor.lo + Dz.lo + Es + Wzx.lo = 5 > W0x.lo
  = 1`: the max is taken by the z_ack branch, which the shipped form omits.

So the row's label should be **sufficient (not necessary)**, with the
replacement `S_J0_XR` / `S_J1_YR` labelled **sufficient +
necessary_at_boundary** (x branch; the y branch is the symmetric statement,
its counter-run not built). This is one parameter point, not an iff over the
box. `bd_mux.uj_env_latency_ctl` is in Necessity4MuxC.

## Which form

Lean proves the binary `≤` forms. The JSON row carries the strict `+1`
(CElemStrict, Kleene X window). The counter-run refutes the binary max form
at slack 1 (so the strict max form `L + 1 ≤ R` is 2 ticks from the refuted
point there, the audit's P8 item 1 caveat applies unchanged); the strict
max form is sufficient because it implies the `≤` form. Equality failing
under a Kleene X window is CElemStrict's generic own-feedback result, not
re-proved for this composed path.

## Assumed / proved / NOT covered

Assumed: OpsTimedMux's model (lumped FIFO LUT arcs `H_LUT_FIFO`, window
wires, FIFO line `H_LINE_FIFO`, port-level causal partners `MuxCausal` with
minimum latencies), real INITs of uj0/uj1/uor/bd_c2.
Proved: as above.
NOT covered: per-pin LUT arcs (the `Lj0.hi` / `Lj0.lo` pair is kept as the
house's lumped box: in the single-σ model of OpsTimedMux the two cancel, in
a per-pin model they are the feedback-pin and release-pin arcs); the y-branch
counter-run; the other sufficient-only bd_mux rows (see B-necessity4.md).
-/

namespace Formal.Cells.Necessity4Mux
open Formal.Cells
open Formal.Cells.OpsTimed
open Formal.Cells.PipeTimed (Ret Trace)
open Formal.Cells.LibCtlMergeMux (or2B c2B j0B j1B)

/-! ## 1. The max form and its sufficiency -/

/-- `MuxStatic` with the join env latency through the client in its max form
(the return waits for z_ack as well), weakened by `s0` / `s1`. -/
structure MuxStaticN (P : MuxRun) (Wzc : Ret) (Ex Ey Ec Es lj wc wo s0 s1 : Nat) : Prop where
  H_LJ : lj ≤ P.Lj0.lo ∧ lj ≤ P.Lj1.lo
  H_WC : wc ≤ P.Wc0.lo ∧ wc ≤ P.Wc1.lo
  H_WO : wo ≤ P.W0o.lo ∧ wo ≤ P.W1o.lo
  /-- **S_J0_XR**: the max form of `S_J0_X`. -/
  S_J0_XR : P.Lj0.hi + P.wj0h ≤ P.Lj0.lo +
    max P.W0x.lo (P.W0o.lo + P.Lor.lo + P.Dz.lo + Es + P.Wzx.lo) + P.Lxa.lo + P.Wxa.lo + Ex + P.Wx.lo + s0
  /-- **S_J1_YR**: the max form of `S_J1_Y`. -/
  S_J1_YR : P.Lj1.hi + P.wj1h ≤ P.Lj1.lo +
    max P.W1y.lo (P.W1o.lo + P.Lor.lo + P.Dz.lo + Es + P.Wzy.lo) + P.Lya.lo + P.Wya.lo + Ey + P.Wy.lo + s1
  S_J0_C : P.Lj0.hi + P.wj0h ≤ P.Lj0.lo + (wo + P.Lor.lo + P.Dz.lo + Es) + Wzc.lo + Ec + P.Wc0.lo
  S_J1_C : P.Lj1.hi + P.wj1h ≤ P.Lj1.lo + (wo + P.Lor.lo + P.Dz.lo + Es) + Wzc.lo + Ec + P.Wc1.lo
  S_OR : P.W0o.hi ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W1o.lo ∧
    P.W1o.hi ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W0o.lo
  S_XA_FORK : P.Wzx.hi + (P.Lxa.hi + P.wxah) ≤ (Wzc.lo + Ec + wc + lj) + P.W0x.lo
  S_YA_FORK : P.Wzy.hi + (P.Lya.hi + P.wyah) ≤ (Wzc.lo + Ec + wc + lj) + P.W1y.lo
  S_XA_RTZ : P.Wzx.hi + (P.Lxa.hi + P.wxah) ≤ P.Wzx.lo + (Wzc.lo + Ec + wc + lj) + (wo + P.Lor.lo + P.Dz.lo + Es)
  S_YA_RTZ : P.Wzy.hi + (P.Lya.hi + P.wyah) ≤ P.Wzy.lo + (Wzc.lo + Ec + wc + lj) + (wo + P.Lor.lo + P.Dz.lo + Es)
  S_XA_J : P.W0x.hi + (P.Lxa.hi + P.wxah) ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W0x.lo ∧
    P.W0x.hi + (P.Lxa.hi + P.wxah) ≤ 2 * (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.Wzx.lo
  S_YA_J : P.W1y.hi + (P.Lya.hi + P.wyah) ≤ (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.W1y.lo ∧
    P.W1y.hi + (P.Lya.hi + P.wyah) ≤ 2 * (wo + P.Lor.lo + P.Dz.lo + Es) + (Wzc.lo + Ec + wc + lj) + P.Wzy.lo

section suff
variable {P : MuxRun} {Wzc : Ret} {Ex Ey Ec Es lj wc wo : Nat}

/-- The shipped form implies the max form. -/
theorem staticN_of_static (S : MuxStatic P Wzc Ex Ey Ec Es lj wc wo) :
    MuxStaticN P Wzc Ex Ey Ec Es lj wc wo 0 0 where
  H_LJ := S.H_LJ
  H_WC := S.H_WC
  H_WO := S.H_WO
  S_J0_XR := by have := S.S_J0_X; omega
  S_J1_YR := by have := S.S_J1_Y; omega
  S_J0_C := S.S_J0_C
  S_J1_C := S.S_J1_C
  S_OR := S.S_OR
  S_XA_FORK := S.S_XA_FORK
  S_YA_FORK := S.S_YA_FORK
  S_XA_RTZ := S.S_XA_RTZ
  S_YA_RTZ := S.S_YA_RTZ
  S_XA_J := S.S_XA_J
  S_YA_J := S.S_YA_J

variable {s0 s1 : Nat}

theorem C_le_EN (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1) (hpos : ∀ j, 1 ≤ P.γ j)
    (S : MuxStaticN P Wzc Ex Ey Ec Es lj wc wo s0 s1) (j : Nat) : P.γ j + wc + lj ≤ P.E j ∧ 1 ≤ P.E j := by
  have h := C_le_E hE0 hE1 hpos j
  have := S.H_LJ; have := S.H_WC; have := hpos j
  cases hs : P.sv (j / 2)
  · have := (h.2 hs).1
    have := fl P.Wc0 (hpos j); unfold MuxRun.C0 at *; omega
  · have := (h.1 hs).1
    have := fl P.Wc1 (hpos j); unfold MuxRun.C1 at *; omega

/-- The server's edge follows the selected join's edge (min over both branches). -/
theorem E_le_ζN (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (S : MuxStaticN P Wzc Ex Ey Ec Es lj wc wo s0 s1) (j : Nat) :
    P.E j + (wo + P.Lor.lo + P.Dz.lo + Es) ≤ P.ζ j := by
  have hE := (C_le_EN hE0 hE1 Cs.H_POS S j).2
  have hs := Cs.H_SRV j
  have := S.H_WO
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

/-- In a token selecting x the server's edge follows j0's edge through `W0o`. -/
theorem E_le_ζ0 (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (S : MuxStaticN P Wzc Ex Ey Ec Es lj wc wo s0 s1) (j : Nat)
    (hs0 : P.sv (j / 2) = false) :
    P.E j + (P.W0o.lo + P.Lor.lo + P.Dz.lo + Es) ≤ P.ζ j := by
  have hE := (C_le_EN hE0 hE1 Cs.H_POS S j).2
  have hs := Cs.H_SRV j
  unfold MuxRun.Z orEdges at hs
  unfold MuxRun.O0 at hs
  have hc : (fun k => !P.sv k) (j / 2) = true := by simp [hs0]
  split at hs
  · have a := fl P.W0o hE
    have b := fl P.Lor (c := P.W0o.fst (P.E j)) (by omega)
    have c := fl P.Dz (c := P.Lor.fst (P.W0o.fst (P.E j))) (by omega)
    omega
  · contradiction

/-- In a token selecting y the server's edge follows j1's edge through `W1o`. -/
theorem E_le_ζ1 (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (S : MuxStaticN P Wzc Ex Ey Ec Es lj wc wo s0 s1) (j : Nat)
    (hs1 : P.sv (j / 2) = true) :
    P.E j + (P.W1o.lo + P.Lor.lo + P.Dz.lo + Es) ≤ P.ζ j := by
  have hE := (C_le_EN hE0 hE1 Cs.H_POS S j).2
  have hs := Cs.H_SRV j
  unfold MuxRun.Z orEdges at hs
  unfold MuxRun.O1 at hs
  have hc : ¬ (fun k => !P.sv k) (j / 2) = true := by simp [hs1]
  split at hs
  · contradiction
  · have a := fl P.W1o hE
    have b := fl P.Lor (c := P.W1o.fst (P.E j)) (by omega)
    have c := fl P.Dz (c := P.Lor.fst (P.W1o.fst (P.E j))) (by omega)
    omega

theorem ζ_le_EN (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (S : MuxStaticN P Wzc Ex Ey Ec Es lj wc wo s0 s1) (j : Nat) :
    P.ζ j + (Wzc.lo + Ec + wc + lj) ≤ P.E (j + 1) := by
  have h1 := Cs.H_CTL_C j
  have hz : 1 ≤ P.ζ j := by
    have := E_le_ζN hE0 hE1 Cs S j; have := (C_le_EN hE0 hE1 Cs.H_POS S j).2; omega
  have h2 := fl Wzc hz
  have h3 := (C_le_EN hE0 hE1 Cs.H_POS S (j + 1)).1
  omega

theorem γ_monoN (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (S : MuxStaticN P Wzc Ex Ey Ec Es lj wc wo s0 s1) :
    ∀ a b, a ≤ b → P.γ a ≤ P.γ b := by
  have step : ∀ j, P.γ j ≤ P.γ (j + 1) := by
    intro j
    have := (C_le_EN hE0 hE1 Cs.H_POS S j).1
    have := E_le_ζN hE0 hE1 Cs S j
    have := Cs.H_CTL_C j
    have := Wzc.fst_ge (P.ζ j)
    omega
  intro a b hab
  induction b with
  | zero => have : a = 0 := by omega
            subst this; omega
  | succ b ih =>
    by_cases h' : a ≤ b
    · have := ih h'; have := step b; omega
    · have : a = b + 1 := by omega
      subst this; omega

/-- **The event-form obligations from the max form.** `mux_timing_of_static`
with `S_J0_X` / `S_J1_Y` replaced by `S_J0_XR` / `S_J1_YR` (at slack 0). -/
theorem mux_timing_of_staticN {R : Nat} (hE0 : Enum (fun k => !P.sv k) P.κ0) (hE1 : Enum P.sv P.κ1)
    (Cs : MuxCausal P Wzc Ex Ey Ec Es) (S : MuxStaticN P Wzc Ex Ey Ec Es lj wc wo 0 0)
    (hRL : P.Wx.hi ≤ R ∧ P.Wy.hi ≤ R ∧ P.Wc0.hi ≤ R ∧ P.Wc1.hi ≤ R ∧
      P.Lj0.hi + P.wj0h ≤ R ∧ P.Lj1.hi + P.wj1h ≤ R ∧ P.Lj0.hi + P.W0x.hi ≤ R ∧
      P.Lj1.hi + P.W1y.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧ P.Lxa.hi + P.wxah ≤ R ∧
      P.Lya.hi + P.wyah ≤ R)
    (hRE : R ≤ P.Xp 0 ∧ R ≤ P.D0 0 ∧ R ≤ P.Yp 0 ∧ R ≤ P.D1 0 ∧ R ≤ P.A0 0 ∧
      R ≤ P.ZA0 0 ∧ R ≤ P.A1 0 ∧ R ≤ P.ZA1 0) :
    MuxTiming P R := by
  have EZ := E_le_ζN hE0 hE1 Cs S
  have ZE := ζ_le_EN hE0 hE1 Cs S
  have GE := C_le_EN hE0 hE1 Cs.H_POS S
  have GM := γ_monoN hE0 hE1 Cs S
  have hLJ := S.H_LJ; have hWC := S.H_WC; have hWO := S.H_WO
  have e0 : ∀ j, P.τ0 j = P.E (2 * P.κ0 (j / 2) + j % 2) := fun j => by
    have := E_rx0 hE0 j; unfold rx at this; exact this.symm
  have e1 : ∀ j, P.τ1 j = P.E (2 * P.κ1 (j / 2) + j % 2) := fun j => by
    have := E_rx1 hE1 j; unfold rx at this; exact this.symm
  -- x_ack follows the join edge through uxa AND through the server (max form)
  have XAge : ∀ i, P.sv (i / 2) = false →
      P.E i + max P.W0x.lo (P.W0o.lo + P.Lor.lo + P.Dz.lo + Es + P.Wzx.lo) + P.Lxa.lo + P.Wxa.lo ≤ P.XA i := by
    intro i hs
    have hE := (GE i).2
    have a := fl P.W0x hE
    have hz := E_le_ζ0 hE0 hE1 Cs S i hs
    have z1 := fl P.Wzx (c := P.ζ i) (by omega)
    have hcA : P.A0 i ≤ P.cx i := by unfold MuxRun.cx; omega
    have hcZ : P.ZA0 i ≤ P.cx i := by unfold MuxRun.cx; omega
    have hA : P.A0 i = P.W0x.fst (P.E i) := rfl
    have hZ : P.ZA0 i = P.Wzx.fst (P.ζ i) := rfl
    have b := fl P.Lxa (c := P.cx i) (by omega)
    have c := fl P.Wxa (c := P.Lxa.fst (P.cx i)) (by omega)
    show _ ≤ P.Wxa.fst (P.Lxa.fst (P.cx i)); omega
  have YAge : ∀ i, P.sv (i / 2) = true →
      P.E i + max P.W1y.lo (P.W1o.lo + P.Lor.lo + P.Dz.lo + Es + P.Wzy.lo) + P.Lya.lo + P.Wya.lo ≤ P.YA i := by
    intro i hs
    have hE := (GE i).2
    have a := fl P.W1y hE
    have hz := E_le_ζ1 hE0 hE1 Cs S i hs
    have z1 := fl P.Wzy (c := P.ζ i) (by omega)
    have hcA : P.A1 i ≤ P.cy i := by unfold MuxRun.cy; omega
    have hcZ : P.ZA1 i ≤ P.cy i := by unfold MuxRun.cy; omega
    have hA : P.A1 i = P.W1y.fst (P.E i) := rfl
    have hZ : P.ZA1 i = P.Wzy.fst (P.ζ i) := rfl
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
  refine ⟨hRL, hRE, fun j => ⟨?_, ?_⟩, fun j => ⟨?_, ?_⟩, fun k => ?_, fun j => ⟨?_, ?_⟩,
    fun j => ⟨?_, ?_⟩, fun j => ⟨?_, ?_⟩⟩
  · -- uj0, through x (max form)
    have hXA : P.XA (2 * P.κ0 (j / 2) + j % 2) + Ex ≤ P.ξ (j + 1) := by
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m := ⟨j / 2, by omega⟩
        have := Cs.H_XC_FALL m
        rw [show 2 * m / 2 = m by omega, show 2 * m % 2 = 0 by omega, Nat.add_zero]; exact this
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m + 1 := ⟨j / 2, by omega⟩
        have := Cs.H_XC_RISE m
        rw [show (2 * m + 1) / 2 = m by omega, show (2 * m + 1) % 2 = 1 by omega]; exact this
    have hsel : P.sv ((2 * P.κ0 (j / 2) + j % 2) / 2) = false := by
      rw [show (2 * P.κ0 (j / 2) + j % 2) / 2 = P.κ0 (j / 2) by omega]
      have := hE0.hit (j / 2); simpa using this
    have := XAge (2 * P.κ0 (j / 2) + j % 2) hsel
    have hpos : 1 ≤ P.ξ (j + 1) := by have := (GE (2 * P.κ0 (j / 2) + j % 2)).2; omega
    have := fl P.Wx hpos
    have : P.Xp (j + 1) = P.Wx.fst (P.ξ (j + 1)) := rfl
    have := (t0 j).1; have := e0 j; have := S.S_J0_XR
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
  · -- uj1, through y (max form)
    have hYA : P.YA (2 * P.κ1 (j / 2) + j % 2) + Ey ≤ P.η (j + 1) := by
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m := ⟨j / 2, by omega⟩
        have := Cs.H_YC_FALL m
        rw [show 2 * m / 2 = m by omega, show 2 * m % 2 = 0 by omega, Nat.add_zero]; exact this
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m + 1 := ⟨j / 2, by omega⟩
        have := Cs.H_YC_RISE m
        rw [show (2 * m + 1) / 2 = m by omega, show (2 * m + 1) % 2 = 1 by omega]; exact this
    have hsel : P.sv ((2 * P.κ1 (j / 2) + j % 2) / 2) = true := by
      rw [show (2 * P.κ1 (j / 2) + j % 2) / 2 = P.κ1 (j / 2) by omega]
      exact hE1.hit (j / 2)
    have := YAge (2 * P.κ1 (j / 2) + j % 2) hsel
    have hpos : 1 ≤ P.η (j + 1) := by have := (GE (2 * P.κ1 (j / 2) + j % 2)).2; omega
    have := fl P.Wy hpos
    have : P.Yp (j + 1) = P.Wy.fst (P.η (j + 1)) := rfl
    have := (t1 j).1; have := e1 j; have := S.S_J1_YR
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
  · -- H_CTL_SEQ
    have := ZE (2 * k + 1); have := EZ (2 * k + 1)
    have hc : Wzc.fst (P.ζ (2 * k + 1)) + Ec ≤ P.γ (2 * k + 2) := Cs.H_CTL_C (2 * k + 1)
    have := Wzc.fst_ge (P.ζ (2 * k + 1))
    have := P.Wc0.fst_ge (P.γ (2 * k + 2)); have := P.Wc1.fst_ge (P.γ (2 * k + 2))
    unfold MuxRun.C0 MuxRun.C1
    split <;> omega
  · -- H_OR_SKEW
    have := P.W0o.fst_le (P.E j); have := fl P.W1o (GE (j + 1)).2
    have := ZE j; have := EZ j; have := S.S_OR
    unfold MuxRun.O0 MuxRun.O1; omega
  · have := P.W1o.fst_le (P.E j); have := fl P.W0o (GE (j + 1)).2
    have := ZE j; have := EZ j; have := S.S_OR
    unfold MuxRun.O0 MuxRun.O1; omega
  · have := P.W0x.fst_le (P.E j); have := P.Wzx.fst_le (P.ζ j)
    have := fl P.W0x (GE (j + 1)).2
    have := ZE j; have := EZ j; have := S.S_XA_FORK; have := S.S_XA_J
    unfold MuxRun.cx MuxRun.A0 MuxRun.ZA0; omega
  · have := P.W0x.fst_le (P.E j); have := P.Wzx.fst_le (P.ζ j)
    have hz1 : 1 ≤ P.ζ (j + 1) := by have := EZ (j + 1); have := (GE (j + 1)).2; omega
    have := fl P.Wzx hz1
    have := ZE j; have := EZ j; have := EZ (j + 1); have := S.S_XA_RTZ; have := S.S_XA_J
    unfold MuxRun.cx MuxRun.A0 MuxRun.ZA0; omega
  · have := P.W1y.fst_le (P.E j); have := P.Wzy.fst_le (P.ζ j)
    have := fl P.W1y (GE (j + 1)).2
    have := ZE j; have := EZ j; have := S.S_YA_FORK; have := S.S_YA_J
    unfold MuxRun.cy MuxRun.A1 MuxRun.ZA1; omega
  · have := P.W1y.fst_le (P.E j); have := P.Wzy.fst_le (P.ζ j)
    have hz1 : 1 ≤ P.ζ (j + 1) := by have := EZ (j + 1); have := (GE (j + 1)).2; omega
    have := fl P.Wzy hz1
    have := ZE j; have := EZ j; have := EZ (j + 1); have := S.S_YA_RTZ; have := S.S_YA_J
    unfold MuxRun.cy MuxRun.A1 MuxRun.ZA1; omega

/-- The conclusion of `mux_ok` (joins, z_req, both acks, order). -/
def MuxConcl (P : MuxRun) (j0 j1 zr xak yak : Trace) : Prop :=
  Tok P.Lj0.hi j0 P.E (fun k => !P.sv k) ∧ Tok P.Lj1.hi j1 P.E P.sv ∧
  Tok P.Tz zr P.Z (fun _ => true) ∧
  Tok P.Tx xak P.XA (fun k => !P.sv k) ∧ Tok P.Tx xak (rx P.XA P.κ0) (fun _ => true) ∧
  Tok P.Ty yak P.YA P.sv ∧ Tok P.Ty yak (rx P.YA P.κ1) (fun _ => true) ∧
  (∀ m, P.Xp (2 * m) ≤ P.E (2 * P.κ0 m) ∧ P.C0 (2 * P.κ0 m) ≤ P.E (2 * P.κ0 m)) ∧
  (∀ m, P.Yp (2 * m) ≤ P.E (2 * P.κ1 m) ∧ P.C1 (2 * P.κ1 m) ≤ P.E (2 * P.κ1 m)) ∧
  (∀ j, P.ζ j ≤ P.XA j ∧ P.ζ j ≤ P.YA j)

/-- Reset sequencing as `mux_ok_static` takes it. -/
def MuxRst (P : MuxRun) (R : Nat) : Prop :=
  (P.Wx.hi ≤ R ∧ P.Wy.hi ≤ R ∧ P.Wc0.hi ≤ R ∧ P.Wc1.hi ≤ R ∧
    P.Lj0.hi + P.wj0h ≤ R ∧ P.Lj1.hi + P.wj1h ≤ R ∧ P.Lj0.hi + P.W0x.hi ≤ R ∧
    P.Lj1.hi + P.W1y.hi ≤ R ∧ P.Wzx.hi ≤ R ∧ P.Wzy.hi ≤ R ∧ P.Lxa.hi + P.wxah ≤ R ∧
    P.Lya.hi + P.wyah ≤ R) ∧
  (R ≤ P.Xp 0 ∧ R ≤ P.D0 0 ∧ R ≤ P.Yp 0 ∧ R ≤ P.D1 0 ∧ R ≤ P.A0 0 ∧
    R ≤ P.ZA0 0 ∧ R ≤ P.A1 0 ∧ R ≤ P.ZA1 0)

/-- **`mux_ok_staticN` (sufficient).** `mux_ok`'s whole conclusion from the
gates, the environment, causal partners, the max-form static obligations
and reset sequencing. -/
theorem mux_ok_staticN {R : Nat} {rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y
      zx zy xa qa ya qb xak yak : Trace}
    (G : MuxGates P rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa
      ya qb xak yak)
    (V : MuxEnv P rst x y ctl za sx0 sx1 R) (Cs : MuxCausal P Wzc Ex Ey Ec Es)
    (S : MuxStaticN P Wzc Ex Ey Ec Es lj wc wo 0 0) (hR : MuxRst P R) :
    MuxConcl P j0 j1 zr xak yak :=
  mux_ok G V (mux_timing_of_staticN V.H_ENUM0 V.H_ENUM1 Cs S hR.1 hR.2)

end suff

/-- The claim at slack `s0` on the x branch: `mux_ok_staticN` with
`S_J0_XR` weakened by `s0`, every other hypothesis verbatim. -/
def ClaimX (s0 : Nat) : Prop :=
  ∀ (P : MuxRun) (Wzc : Ret) (Ex Ey Ec Es lj wc wo R : Nat)
    (rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa ya qb xak yak : Trace),
    MuxGates P rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x j1y zx zy xa qa ya qb xak yak →
    MuxEnv P rst x y ctl za sx0 sx1 R → MuxCausal P Wzc Ex Ey Ec Es →
    MuxStaticN P Wzc Ex Ey Ec Es lj wc wo s0 0 → MuxRst P R → MuxConcl P j0 j1 zr xak yak

theorem claimX0 : ClaimX 0 := by
  intro P Wzc Ex Ey Ec Es lj wc wo R rst x y ctl za xj yj cj0 cj1 sx0 sx1 j0 q0 j1 q1 e0 e1 ei zr j0x
    j1y zx zy xa qa ya qb xak yak G V Cs S hR
  exact mux_ok_staticN G V Cs S hR

/-! ## 2. A run family: a passing run that violates `S_J0_X`, and the counter-run

Every LUT, wire and line one tick (`uW`), except uj0's feedback net, which is
a fixed `W`-tick wire. Reset high on `[0, 12)`. Control tokens alternate
x, y, x, y (period 26 per token); each client raises its request 4 ticks
before ctl_req (it waits at its join), the x client drops x_req ONE tick
after seeing x_ack (tight, `Ex = 1`), the control sender moves 6 ticks after
ctl_ack (`Ec = 6`), the server answers in 1 (`Es = 1`). Derived edges of
token `k` (base `b = 26 k + 20`): join node `b + 2`, z_ack at the server
`b + 6`, x_ack `b + 9`, x_req's fall at uj0 `b + 11`, ctl_req's fall at uj0
`b + 14`. The z_ack branch of uxa (`W0o + Lor + Dz + Es + Wzx = 5`) is
longer than the j0 branch (`W0x = 1`). -/
namespace N4

def run (W : Nat) : MuxRun where
  Wx := uW
  Wy := uW
  Wc0 := uW
  Wc1 := uW
  Lj0 := uW
  Lj1 := uW
  wj0l := W
  wj0h := W
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
  ξ j := 52 * (j / 2) + 16 + 14 * (j % 2)
  η j := 52 * (j / 2) + 42 + 14 * (j % 2)
  γ j := 26 * (j / 2) + 20 + 13 * (j % 2)
  ζ j := 26 * (j / 2) + 26 + 13 * (j % 2)
  sv := svW
  κ0 m := 2 * m
  κ1 m := 2 * m + 1

def rst (t : Nat) : Bool := decide (t < 12)
theorem rst_hi : ∀ t, t < 12 → rst t = true := fun t h => by simp [rst, h]
theorem rst_lo : ∀ t, 12 ≤ t → rst t = false := fun t h => by simp [rst]; omega

-- environment
def x (t : Nat) : Bool := decide (16 ≤ t ∧ (t - 16) % 52 < 14)
def y (t : Nat) : Bool := decide (42 ≤ t ∧ (t - 42) % 52 < 14)
def ctl (t : Nat) : Bool := decide (20 ≤ t ∧ (t - 20) % 26 < 13)
def za (t : Nat) : Bool := decide (26 ≤ t ∧ (t - 26) % 26 < 13)
def sx (t : Nat) : Bool := svW ((t - 20) / 26)
-- the cell
def xj (t : Nat) : Bool := x (t - 1)
def yj (t : Nat) : Bool := y (t - 1)
def cj (t : Nat) : Bool := ctl (t - 1)
/-- uj0's feedback pin: j0 through the `W`-tick net. -/
def q0 (W : Nat) (J : Trace) (t : Nat) : Bool := J (t - W)
def j1 : Nat → Bool
  | 0 => false
  | 1 => j1B (yj 0) (cj 0) (sx 0) false (rst 0)
  | t + 2 => j1B (yj (t + 1)) (cj (t + 1)) (sx (t + 1)) (j1 t) (rst (t + 1))
def q1 (t : Nat) : Bool := j1 (t - 1)
def e0 (J : Trace) (t : Nat) : Bool := J (t - 1)
def e1 (t : Nat) : Bool := j1 (t - 1)
def ei (J : Trace) (t : Nat) : Bool := or2B (e0 J (t - 1)) (e1 (t - 1))
def zr (J : Trace) (t : Nat) : Bool := ei J (t - 1)
def j0x (J : Trace) (t : Nat) : Bool := J (t - 1)
def j1y (t : Nat) : Bool := j1 (t - 1)
def zx (t : Nat) : Bool := za (t - 1)
def xa (J : Trace) : Nat → Bool
  | 0 => false
  | 1 => c2B (j0x J 0) (zx 0) false (rst 0)
  | t + 2 => c2B (j0x J (t + 1)) (zx (t + 1)) (xa J t) (rst (t + 1))
def qa (J : Trace) (t : Nat) : Bool := xa J (t - 1)
def ya : Nat → Bool
  | 0 => false
  | 1 => c2B (j1y 0) (zx 0) false (rst 0)
  | t + 2 => c2B (j1y (t + 1)) (zx (t + 1)) (ya t) (rst (t + 1))
def qb (t : Nat) : Bool := ya (t - 1)
def xak (J : Trace) (t : Nat) : Bool := xa J (t - 1)
def yak (t : Nat) : Bool := ya (t - 1)

/-- The join's gate relation through a `W`-tick feedback net. -/
def JoinEq (W : Nat) (J : Trace) : Prop :=
  ∀ t, 1 ≤ t → J t = j0B (xj (t - 1)) (cj (t - 1)) (sx (t - 1)) (J (t - 1 - W)) (rst (t - 1))

/-- uj0 with an 8-tick feedback net (loop 9). -/
def j0p : Nat → Bool
  | t + 9 => j0B (xj (t + 8)) (cj (t + 8)) (sx (t + 8)) (j0p t) (rst (t + 8))
  | _ => false
/-- uj0 with a 10-tick feedback net (loop 11). -/
def j0f : Nat → Bool
  | t + 11 => j0B (xj (t + 10)) (cj (t + 10)) (sx (t + 10)) (j0f t) (rst (t + 10))
  | _ => false

theorem j0p_eq : JoinEq 8 j0p := by
  intro t ht
  match t, ht with
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | t + 9, _ => rfl

theorem j0f_eq : JoinEq 10 j0f := by
  intro t ht
  match t, ht with
  | 1, _ => rfl
  | 2, _ => rfl
  | 3, _ => rfl
  | 4, _ => rfl
  | 5, _ => rfl
  | 6, _ => rfl
  | 7, _ => rfl
  | 8, _ => rfl
  | 9, _ => rfl
  | 10, _ => rfl
  | t + 11, _ => rfl

theorem gates (W : Nat) (J : Trace) (hJ : JoinEq W J) :
    MuxGates (run W) rst x y ctl za xj yj cj cj sx sx J (q0 W J) j1 q1 (e0 J) e1 (ei J) (zr J)
      (j0x J) j1y zx zx (xa J) (qa J) ya qb (xak J) yak where
  H_WX _ _ := rfl
  H_WY _ _ := rfl
  H_WC0 _ _ := rfl
  H_WC1 _ _ := rfl
  H_UJ0 t ht := hJ t ht
  H_UJ0_FB := fun t ht => by
    have h : W ≤ t := ht
    exact ⟨t - W, by show t ≤ t - W + W; omega, by show t - W + W ≤ t; omega, rfl⟩
  H_UJ0_POS := by show 1 ≤ 1 + W; omega
  H_UJ1 t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UJ1_FB := win11 (fun _ _ => rfl)
  H_UJ1_POS := Nat.le_of_ble_eq_true rfl
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
  H_UXA_POS := Nat.le_of_ble_eq_true rfl
  H_UYA t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UYA_FB := win11 (fun _ _ => rfl)
  H_UYA_POS := Nat.le_of_ble_eq_true rfl
  H_WXA _ _ := rfl
  H_WYA _ _ := rfl

section closed
variable (W : Nat)

theorem enum0 : Enum (fun k => !(run W).sv k) (run W).κ0 where
  mono m := by show 2 * m < 2 * (m + 1); omega
  hit m := by show (!decide (2 * m % 2 = 1)) = true; simp
  all k h := ⟨k / 2, by
    have h : (!decide (k % 2 = 1)) = true := h
    simp at h; show 2 * (k / 2) = k; omega⟩

theorem enum1 : Enum (run W).sv (run W).κ1 where
  mono m := by show 2 * m + 1 < 2 * (m + 1) + 1; omega
  hit m := by show decide ((2 * m + 1) % 2 = 1) = true; simp
  all k h := ⟨k / 2, by
    have h : decide (k % 2 = 1) = true := h
    simp at h; show 2 * (k / 2) + 1 = k; omega⟩

theorem Xp_eq (j : Nat) : (run W).Xp j = 52 * (j / 2) + 17 + 14 * (j % 2) := by
  show uW.fst (52 * (j / 2) + 16 + 14 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem Yp_eq (j : Nat) : (run W).Yp j = 52 * (j / 2) + 43 + 14 * (j % 2) := by
  show uW.fst (52 * (j / 2) + 42 + 14 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem C0_eq (j : Nat) : (run W).C0 j = 26 * (j / 2) + 21 + 13 * (j % 2) := by
  show uW.fst (26 * (j / 2) + 20 + 13 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem C1_eq (j : Nat) : (run W).C1 j = 26 * (j / 2) + 21 + 13 * (j % 2) := by
  show uW.fst (26 * (j / 2) + 20 + 13 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem D0_eq (j : Nat) : (run W).D0 j = 52 * (j / 2) + 21 + 13 * (j % 2) := by
  show (run W).C0 (2 * (2 * (j / 2)) + j % 2) = _; rw [C0_eq]; omega
theorem D1_eq (j : Nat) : (run W).D1 j = 52 * (j / 2) + 47 + 13 * (j % 2) := by
  show (run W).C1 (2 * (2 * (j / 2) + 1) + j % 2) = _; rw [C1_eq]; omega
theorem c0_eq (j : Nat) : (run W).c0 j = 52 * (j / 2) + 21 + 13 * (j % 2) := by
  show max ((run W).Xp j) ((run W).D0 j) = _; rw [Xp_eq, D0_eq]; omega
theorem c1_eq (j : Nat) : (run W).c1 j = 52 * (j / 2) + 47 + 13 * (j % 2) := by
  show max ((run W).Yp j) ((run W).D1 j) = _; rw [Yp_eq, D1_eq]; omega
theorem τ0_eq (j : Nat) : (run W).τ0 j = 52 * (j / 2) + 22 + 13 * (j % 2) := by
  show uW.fst ((run W).c0 j) = _; rw [c0_eq, fuW _ (by omega)]; omega
theorem τ1_eq (j : Nat) : (run W).τ1 j = 52 * (j / 2) + 48 + 13 * (j % 2) := by
  show uW.fst ((run W).c1 j) = _; rw [c1_eq, fuW _ (by omega)]; omega

theorem E_eq (j : Nat) : (run W).E j = 26 * (j / 2) + 22 + 13 * (j % 2) := by
  unfold MuxRun.E
  rcases Nat.mod_two_eq_zero_or_one (j / 2) with hk | hk
  · have hs : (run W).sv (j / 2) = false := by show decide (j / 2 % 2 = 1) = false; simp; omega
    have hi : idx (run W).κ0 (j / 2) = j / 2 / 2 := by
      have := idx_κ (enum0 W) (j / 2 / 2)
      rw [show (run W).κ0 (j / 2 / 2) = j / 2 by show 2 * (j / 2 / 2) = j / 2; omega] at this
      exact this
    rw [hs, hi]; simp only [Bool.false_eq_true, ite_false]; rw [τ0_eq]; omega
  · have hs : (run W).sv (j / 2) = true := by show decide (j / 2 % 2 = 1) = true; simp; omega
    have hi : idx (run W).κ1 (j / 2) = j / 2 / 2 := by
      have := idx_κ (enum1 W) (j / 2 / 2)
      rw [show (run W).κ1 (j / 2 / 2) = j / 2 by show 2 * (j / 2 / 2) + 1 = j / 2; omega] at this
      exact this
    rw [hs, hi]; simp only [ite_true]; rw [τ1_eq]; omega

theorem O0_eq (j : Nat) : (run W).O0 j = (run W).E j + 1 := by
  show uW.fst ((run W).E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem O1_eq (j : Nat) : (run W).O1 j = (run W).E j + 1 := by
  show uW.fst ((run W).E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem A0_eq (j : Nat) : (run W).A0 j = (run W).E j + 1 := by
  show uW.fst ((run W).E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem A1_eq (j : Nat) : (run W).A1 j = (run W).E j + 1 := by
  show uW.fst ((run W).E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem ZA_eq (j : Nat) : (run W).ZA0 j = 26 * (j / 2) + 27 + 13 * (j % 2) ∧
    (run W).ZA1 j = 26 * (j / 2) + 27 + 13 * (j % 2) := by
  constructor <;> (show uW.fst (26 * (j / 2) + 26 + 13 * (j % 2)) = _; rw [fuW _ (by omega)]; omega)

theorem Z_eq (j : Nat) : (run W).Z j = (run W).E j + 3 := by
  unfold MuxRun.Z orEdges
  rw [show (run W).Lor = uW from rfl, show (run W).Dz = uW from rfl]
  have hE := E_eq W j
  split
  · rw [O0_eq, fuW ((run W).E j + 1) (by omega), fuW ((run W).E j + 1 + 1) (by omega)]
  · rw [O1_eq, fuW ((run W).E j + 1) (by omega), fuW ((run W).E j + 1 + 1) (by omega)]

theorem XA_eq (j : Nat) : (run W).XA j = 26 * (j / 2) + 29 + 13 * (j % 2) ∧
    (run W).YA j = 26 * (j / 2) + 29 + 13 * (j % 2) := by
  have hm : max ((run W).E j + 1) (26 * (j / 2) + 27 + 13 * (j % 2)) = 26 * (j / 2) + 27 + 13 * (j % 2) := by
    rw [E_eq]; omega
  constructor
  · show uW.fst (uW.fst (max ((run W).A0 j) ((run W).ZA0 j))) = _
    rw [A0_eq, (ZA_eq W j).1, hm, fuW (26 * (j / 2) + 27 + 13 * (j % 2)) (by omega),
      fuW (26 * (j / 2) + 27 + 13 * (j % 2) + 1) (by omega)]; omega
  · show uW.fst (uW.fst (max ((run W).A1 j) ((run W).ZA1 j))) = _
    rw [A1_eq, (ZA_eq W j).2, hm, fuW (26 * (j / 2) + 27 + 13 * (j % 2)) (by omega),
      fuW (26 * (j / 2) + 27 + 13 * (j % 2) + 1) (by omega)]; omega

theorem env : MuxEnv (run W) rst x y ctl za sx sx 12 where
  H_RST_HI := rst_hi
  H_RST_LO := rst_lo
  H_X := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 52 * (0 / 2) + 16 + 14 * (0 % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
    · have h1 : 52 * (2 * k / 2) + 16 + 14 * (2 * k % 2) ≤ t := h1
      have h2 : t < 52 * ((2 * k + 1) / 2) + 16 + 14 * ((2 * k + 1) % 2) := h2
      simp only [x, decide_eq_true_eq]; omega
    · have h1 : 52 * ((2 * k + 1) / 2) + 16 + 14 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 52 * ((2 * k + 2) / 2) + 16 + 14 * ((2 * k + 2) % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
  H_Y := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 52 * (0 / 2) + 42 + 14 * (0 % 2) := h2
      simp only [y, decide_eq_false_iff_not]; omega
    · have h1 : 52 * (2 * k / 2) + 42 + 14 * (2 * k % 2) ≤ t := h1
      have h2 : t < 52 * ((2 * k + 1) / 2) + 42 + 14 * ((2 * k + 1) % 2) := h2
      simp only [y, decide_eq_true_eq]; omega
    · have h1 : 52 * ((2 * k + 1) / 2) + 42 + 14 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 52 * ((2 * k + 2) / 2) + 42 + 14 * ((2 * k + 2) % 2) := h2
      simp only [y, decide_eq_false_iff_not]; omega
  H_CTL := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 26 * (0 / 2) + 20 + 13 * (0 % 2) := h2
      simp only [ctl, decide_eq_false_iff_not]; omega
    · have h1 : 26 * (2 * k / 2) + 20 + 13 * (2 * k % 2) ≤ t := h1
      have h2 : t < 26 * ((2 * k + 1) / 2) + 20 + 13 * ((2 * k + 1) % 2) := h2
      simp only [ctl, decide_eq_true_eq]; omega
    · have h1 : 26 * ((2 * k + 1) / 2) + 20 + 13 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 26 * ((2 * k + 2) / 2) + 20 + 13 * ((2 * k + 2) % 2) := h2
      simp only [ctl, decide_eq_false_iff_not]; omega
  H_ZA := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 26 * (0 / 2) + 26 + 13 * (0 % 2) := h2
      simp only [za, decide_eq_false_iff_not]; omega
    · have h1 : 26 * (2 * k / 2) + 26 + 13 * (2 * k % 2) ≤ t := h1
      have h2 : t < 26 * ((2 * k + 1) / 2) + 26 + 13 * ((2 * k + 1) % 2) := h2
      simp only [za, decide_eq_true_eq]; omega
    · have h1 : 26 * ((2 * k + 1) / 2) + 26 + 13 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 26 * ((2 * k + 2) / 2) + 26 + 13 * ((2 * k + 2) % 2) := h2
      simp only [za, decide_eq_false_iff_not]; omega
  H_ENUM0 := enum0 W
  H_ENUM1 := enum1 W
  H_S_PIN0 k t h1 h2 := by
    rw [C0_eq] at h1 h2
    show svW ((t - 20) / 26) = svW k
    rw [show (t - 20) / 26 = k by omega]
  H_S_PIN1 k t h1 h2 := by
    rw [C1_eq] at h1 h2
    show svW ((t - 20) / 26) = svW k
    rw [show (t - 20) / 26 = k by omega]

/-- The partners are causal; the x client and the control sender are tight. -/
theorem causal : MuxCausal (run W) uW 1 1 6 1 where
  H_XC_FALL m := by
    rw [(XA_eq W _).1]; show _ ≤ 52 * ((2 * m + 1) / 2) + 16 + 14 * ((2 * m + 1) % 2)
    show 26 * (2 * (2 * m) / 2) + 29 + 13 * (2 * (2 * m) % 2) + 1 ≤ _; omega
  H_XC_RISE m := by
    rw [(XA_eq W _).1]; show _ ≤ 52 * ((2 * m + 2) / 2) + 16 + 14 * ((2 * m + 2) % 2)
    show 26 * ((2 * (2 * m) + 1) / 2) + 29 + 13 * ((2 * (2 * m) + 1) % 2) + 1 ≤ _; omega
  H_YC_FALL m := by
    rw [(XA_eq W _).2]; show _ ≤ 52 * ((2 * m + 1) / 2) + 42 + 14 * ((2 * m + 1) % 2)
    show 26 * (2 * (2 * m + 1) / 2) + 29 + 13 * (2 * (2 * m + 1) % 2) + 1 ≤ _; omega
  H_YC_RISE m := by
    rw [(XA_eq W _).2]; show _ ≤ 52 * ((2 * m + 2) / 2) + 42 + 14 * ((2 * m + 2) % 2)
    show 26 * ((2 * (2 * m + 1) + 1) / 2) + 29 + 13 * ((2 * (2 * m + 1) + 1) % 2) + 1 ≤ _; omega
  H_CTL_C j := by
    show uW.fst (26 * (j / 2) + 26 + 13 * (j % 2)) + 6 ≤ 26 * ((j + 1) / 2) + 20 + 13 * ((j + 1) % 2)
    rw [fuW _ (by omega)]; omega
  H_SRV j := by
    rw [Z_eq, E_eq]; show _ ≤ 26 * (j / 2) + 26 + 13 * (j % 2); omega
  H_POS j := by show 1 ≤ 26 * (j / 2) + 20 + 13 * (j % 2); omega

theorem rstOK (hW : W ≤ 11) : MuxRst (run W) 12 := by
  have b : ∀ {a c : Nat}, Nat.ble a c = true → a ≤ c := fun h => Nat.le_of_ble_eq_true h
  refine ⟨⟨b rfl, b rfl, b rfl, b rfl, by show 1 + W ≤ 12; omega, b rfl,
    b rfl, b rfl, b rfl, b rfl, b rfl, b rfl⟩, ?_⟩
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Xp_eq]; omega
  · rw [D0_eq]; omega
  · rw [Yp_eq]; omega
  · rw [D1_eq]; omega
  · rw [A0_eq, E_eq]; omega
  · rw [(ZA_eq W 0).1]; omega
  · rw [A1_eq, E_eq]; omega
  · rw [(ZA_eq W 0).2]; omega

/-- Every max-form static obligation, `S_J0_XR` at slack `s0`, holds as long
as `1 + W ≤ 10 + s0` (and `W ≤ 12` for `S_J0_C`). -/
theorem staticN (s0 : Nat) (h1 : 1 + W ≤ 10 + s0) (h2 : W ≤ 12) :
    MuxStaticN (run W) uW 1 1 6 1 1 1 1 s0 0 where
  H_LJ := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  H_WC := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  H_WO := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  S_J0_XR := by show 1 + W ≤ 1 + max 1 (1 + 1 + 1 + 1 + 1) + 1 + 1 + 1 + 1 + s0; omega
  S_J1_YR := Nat.le_of_ble_eq_true rfl
  S_J0_C := by show 1 + W ≤ 1 + (1 + 1 + 1 + 1) + 1 + 6 + 1; omega
  S_J1_C := Nat.le_of_ble_eq_true rfl
  S_OR := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  S_XA_FORK := Nat.le_of_ble_eq_true rfl
  S_YA_FORK := Nat.le_of_ble_eq_true rfl
  S_XA_RTZ := Nat.le_of_ble_eq_true rfl
  S_YA_RTZ := Nat.le_of_ble_eq_true rfl
  S_XA_J := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩
  S_YA_J := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

end closed

/-- The shipped `S_J0_X` of a run with an `W`-tick uj0 feedback net. -/
def SJ0X (W : Nat) : Prop :=
  (run W).Lj0.hi + (run W).wj0h ≤
    (run W).Lj0.lo + (run W).W0x.lo + (run W).Lxa.lo + (run W).Wxa.lo + 1 + (run W).Wx.lo

theorem SJ0X_iff (W : Nat) : SJ0X W ↔ W ≤ 5 := by
  show 1 + W ≤ 1 + 1 + 1 + 1 + 1 + 1 ↔ _; omega

end N4

open N4

/-- **`S_J0_X` is not necessary** (row `bd_mux.uj_env_latency_req`). With an
8-tick uj0 feedback net, the shipped `S_J0_X` fails (`9 ≤ 6`), and so does
its strict (+1) form, while every max-form obligation holds, including its
strict form (`1 + 8 + 1 ≤ 10`): the run meets every hypothesis of
`mux_ok_staticN` and so `mux_ok`'s whole conclusion. -/
theorem pass8 :
    ¬ SJ0X 8 ∧
    (run 8).Lj0.hi + (run 8).wj0h + 1 ≤ (run 8).Lj0.lo +
      max (run 8).W0x.lo ((run 8).W0o.lo + (run 8).Lor.lo + (run 8).Dz.lo + 1 + (run 8).Wzx.lo) +
      (run 8).Lxa.lo + (run 8).Wxa.lo + 1 + (run 8).Wx.lo ∧
    MuxStaticN (run 8) uW 1 1 6 1 1 1 1 0 0 ∧
    MuxConcl (run 8) j0p j1 (zr j0p) (xak j0p) yak := by
  refine ⟨fun h => by have := (SJ0X_iff 8).1 h; omega, by decide, staticN 8 0 (by omega) (by omega), ?_⟩
  exact mux_ok_staticN (gates 8 j0p j0p_eq) (env 8) (causal 8) (staticN 8 0 (by omega) (by omega))
    (rstOK 8 (by omega))

/-- The passing run is not degenerate: x's token 0 and y's token 1 are
acknowledged, z_req carries both, and the race the shipped `S_J0_X` is
about is live: j0 rises at 22, its 8-tick net shows that from 30, x_req is
already low at uj0's pin at 31 (one tick of margin: the return from the node
edge is 9 ticks, through z_ack, where `S_J0_X` counts 5), and j0 holds
until 35. -/
theorem pass8_values :
    xak j0p 30 = true ∧ yak 30 = false ∧ xak j0p 56 = false ∧ yak 56 = true ∧
    zr j0p 30 = true ∧ zr j0p 56 = true ∧ j0p 22 = true ∧ j0p 21 = false ∧ xj 31 = false ∧
    j0p 34 = true ∧ j0p 35 = false := by
  decide +kernel

/-- **The max form is necessary at the boundary** (its z_ack branch). With a
10-tick uj0 feedback net: every hypothesis of `mux_ok_staticN` holds except
`S_J0_XR`, which holds only when weakened by one tick (`MuxStaticN … 1 0`)
and fails by exactly one (`11 = 10 + 1`), and the conclusion fails: j0 is 0
at 32 inside its token-0 window `[E 0, E 1) = [22, 35)`, and z_req is 0 at
35 inside its window `[Z 0, Z 1) = [25, 38)`. -/
theorem fail10 :
    MuxStaticN (run 10) uW 1 1 6 1 1 1 1 1 0 ∧
    (run 10).Lj0.hi + (run 10).wj0h = (run 10).Lj0.lo +
      max (run 10).W0x.lo ((run 10).W0o.lo + (run 10).Lor.lo + (run 10).Dz.lo + 1 + (run 10).Wzx.lo) +
      (run 10).Lxa.lo + (run 10).Wxa.lo + 1 + (run 10).Wx.lo + 1 ∧
    (run 10).W0x.lo < (run 10).W0o.lo + (run 10).Lor.lo + (run 10).Dz.lo + 1 + (run 10).Wzx.lo ∧
    MuxRst (run 10) 12 ∧
    (run 10).E 0 = 22 ∧ (run 10).E 1 = 35 ∧ (run 10).Z 0 = 25 ∧ (run 10).Z 1 = 38 ∧
    j0f 32 = false ∧ zr j0f 35 = false ∧
    ¬ Tok (run 10).Lj0.hi j0f (run 10).E (fun k => !(run 10).sv k) ∧
    ¬ Tok (run 10).Tz (zr j0f) (run 10).Z (fun _ => true) ∧
    ¬ MuxConcl (run 10) j0f j1 (zr j0f) (xak j0f) yak := by
  have hE0 : (run 10).E 0 = 22 := by rw [E_eq]
  have hE1 : (run 10).E 1 = 35 := by rw [E_eq]
  have hZ0 : (run 10).Z 0 = 25 := by rw [Z_eq, E_eq]
  have hZ1 : (run 10).Z 1 = 38 := by rw [Z_eq, E_eq]
  have v1 : j0f 32 = false := by decide +kernel
  have v2 : zr j0f 35 = false := by decide +kernel
  have nj : ¬ Tok (run 10).Lj0.hi j0f (run 10).E (fun k => !(run 10).sv k) := by
    intro h
    have := h.hi 0 32 (by decide) (by rw [show 2 * 0 = 0 from rfl, hE0]; omega)
      (by rw [show 2 * 0 + 1 = 1 from rfl, hE1]; omega)
    rw [v1] at this; exact absurd this (by decide)
  have nz : ¬ Tok (run 10).Tz (zr j0f) (run 10).Z (fun _ => true) := by
    intro h
    have := h.hi 0 35 (by decide) (by rw [show 2 * 0 = 0 from rfl, hZ0]; omega)
      (by rw [show 2 * 0 + 1 = 1 from rfl, hZ1]; omega)
    rw [v2] at this; exact absurd this (by decide)
  exact ⟨staticN 10 1 (by omega) (by omega), by decide, by decide, rstOK 10 (by omega),
    hE0, hE1, hZ0, hZ1, v1, v2, nj, nz, fun h => nz h.2.2.1⟩

/-- The counter-run meets every other hypothesis of `mux_ok_staticN`
(gates for all `t`, environment, causal partners), so `ClaimX 1` is false:
weakening the max form by one tick is unsound. -/
theorem claimX1_false : ¬ ClaimX 1 := by
  intro h
  exact fail10.2.2.2.2.2.2.2.2.2.2.2.2
    (h (run 10) uW 1 1 6 1 1 1 1 12 rst x y ctl za xj yj cj cj sx sx j0f (q0 10 j0f) j1 q1 (e0 j0f) e1
      (ei j0f) (zr j0f) (j0x j0f) j1y zx zx (xa j0f) (qa j0f) ya qb (xak j0f) yak
      (gates 10 j0f j0f_eq) (env 10) (causal 10) fail10.1 (rstOK 10 (by omega)))

end Formal.Cells.Necessity4Mux
