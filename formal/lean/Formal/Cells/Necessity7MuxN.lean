import Formal.Cells.MuxN3Timed
import Formal.Cells.OpsExact2

/-!
# Necessity7MuxN: `bdc_muxn` with `H_DEP_A` asked only at real edges

Probe Bnx7 (shard B). The bdc_muxn analogue of `Necessity7Mux`.
`muxn3_ok` (`MuxN3Timed`) runs `cel_run` at each ack C-element ua_i, which
asks `H_DEP_A` at every control token, including the tokens not selecting
`i`, where j_i does not move (bookkeeping edges). Its static form
`MN3Static` pays for them with `S_A_FORK` and `S_A_J.1` (row
`bdc_muxn.iso_zack`).

* `MN3TimingG`: `MN3Timing` with `H_DEP_A` asked only in input `i`'s tokens
  (against j_i's next edge only when it is `i`'s), plus `H_SEQ_A` (order
  only) when a token of `i` follows a token of another input.
* `muxn3_ok_g`: `muxn3_ok`'s whole conclusion from it (Lt5's `cel_run_g`).
* `MN3StaticG`, `muxn3_timing_g_of_static`, `muxn3_ok_gs`: the static form.
  `MN3Static` without `S_A_FORK` and `S_A_J.1`, with
  - `S_A_SEQ i : Wza.hi ≤ Kc + Wja.lo` (hand-over to input `i`, order only);
  - `S_A_R i : S_A_N ∨ (S_A_FORK ∧ S_A_J.1)`, `S_A_N` the node-launched
    client loop `La.hi + wah ≤ La.lo + Wak.lo + Ex + Wx.lo + Lj.lo + Wja.lo`.
  `staticG_of_static : MN3Static → MN3StaticG`.

`Kz = wo + Lo.lo + Dl + Es`, `Kc = Wzc.lo + Ec + (wc + ls + wsj + lj)`.

## Assumed / proved / NOT covered

Assumed: MuxN3Timed's model (lumped FIFO LUT arcs, window wires, Lt2's FIFO
FASTFALL line, port-level causal partners), real inferred INITs. Proved: as
above (binary `≤`). NOT covered: per-pin arcs, the Kleene X `+1`, an iff.
-/

namespace Formal.Cells.MuxN3Timed
namespace Nec7
open Formal.Cells
open Formal.Cells.OpsTimed
open Formal.Cells.PipeTimed (Ret Trace)
open Formal.Cells.LibCtlMergeMux (c2B c2_spec)
open Formal.Cells.AMergeGates (or3)

/-- **`MN3Timing` with `H_DEP_A` only at real edges.** -/
structure MN3TimingG (P : MN3Run) (R : Nat) : Prop where
  H_RST_LONG : ∀ i, i < 3 → (P.Wx i).hi ≤ R ∧ (P.Wc i).hi + (P.Ls i).hi + (P.Wsj i).hi ≤ R ∧
    (P.Lj i).hi + P.wjh i ≤ R ∧ (P.Lj i).hi + (P.Wja i).hi ≤ R ∧ (P.Wza i).hi ≤ R ∧
    (P.La i).hi + P.wah i ≤ R
  /-- Only z_ack's first edge must follow reset release at ua_i. -/
  H_RST_EARLY : ∀ i, i < 3 → R ≤ P.Xp i 0 ∧ R ≤ P.D i 0 ∧ R ≤ P.ZA i 0
  H_DEP_J : ∀ i, i < 3 → ∀ j, P.c i j + (P.Lj i).hi + P.wjh i ≤ P.Xp i (j + 1) ∧
    P.c i j + (P.Lj i).hi + P.wjh i ≤ P.D i (j + 1)
  H_DEP_A : ∀ i, i < 3 → ∀ j, P.g i (j / 2) = true →
    P.cx i j + (P.La i).hi + P.wah i ≤ P.ZA i (j + 1) ∧
    (P.g i ((j + 1) / 2) = true → P.cx i j + (P.La i).hi + P.wah i ≤ P.A i (j + 1))
  H_SEQ_A : ∀ i, i < 3 → ∀ k, P.g i k = false → P.g i (k + 1) = true →
    P.ZA i (2 * k + 1) ≤ P.A i (2 * k + 2)
  H_FLUSH : ∀ i, 1 ≤ i → i < P.N → ∀ k,
    (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 1)) ≤ (P.Tp i).fst (P.OJ (2 * k + 2)) ∧
    (P.Tp i).fst (P.OJ (2 * k + 1)) ≤ (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 2))
  H_N : 1 ≤ P.N

/-- The shipped event form implies the new one. -/
theorem MN3Timing.g {P : MN3Run} {R : Nat} (TM : MN3Timing P R) : MN3TimingG P R := by
  refine ⟨TM.H_RST_LONG, fun i hi => ⟨(TM.H_RST_EARLY i hi).1, (TM.H_RST_EARLY i hi).2.1,
    (TM.H_RST_EARLY i hi).2.2.2⟩, TM.H_DEP_J,
    fun i hi j _ => ⟨(TM.H_DEP_A i hi j).2, fun _ => (TM.H_DEP_A i hi j).1⟩,
    fun i hi k _ _ => ?_, TM.H_FLUSH, TM.H_N⟩
  have := (TM.H_DEP_A i hi (2 * k + 1)).1
  unfold MN3Run.cx at this; rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega] at this; omega

/-- **`muxn3_ok_g`**: `muxn3_ok`'s conclusion with `H_DEP_A` only at real
edges. -/
theorem muxn3_ok_g {P : MN3Run} {R : Nat} {Wzc : Ret} {Ex Ec Es : Nat} {rst ctl za orj : Trace}
    {x xj cp s0p s1p sl sj j q jo s ja zx a qa ak : Nat → Trace}
    (G : MN3Gates P rst ctl za x xj cp s0p s1p sl sj j q jo orj s ja zx a qa ak)
    (V : MN3Env P rst ctl za x s0p s1p R) (TM : MN3TimingG P R) (Cs : MN3Causal P Wzc Ex Ec Es) :
    (∀ i, i < 3 → Tok (P.Lj i).hi (j i) P.E (P.g i)) ∧
    Tok P.To orj P.OJ (fun _ => true) ∧
    Tok (ffT P.H P.Tp P.To P.N) (s P.N) P.Z (fun _ => true) ∧
    (∀ i, i < 3 → Tok (P.Ta i) (ak i) (P.XA i) (P.g i) ∧
      Tok (P.Ta i) (ak i) (rx (P.XA i) (P.κ i)) (fun _ => true)) ∧
    (∀ i, i < 3 → ∀ m, P.Xp i (2 * m) ≤ P.E (2 * P.κ i m) ∧ P.D i (2 * m) ≤ P.E (2 * P.κ i m)) ∧
    (∀ i, i < 3 → ∀ j, P.ζ j ≤ P.XA i j) := by
  have st := E_step V.H_ENUM V.H_RANGE Cs TM.H_N
  have Em : ∀ a b, a ≤ b → P.E a ≤ P.E b :=
    mono_of_step P.E (fun j => by have := st j; omega)
  have Eu : ∀ j, j ≤ P.E j := by
    intro j; induction j with
    | zero => omega
    | succ j ih => have := st j; omega
  have Sm : ∀ a b, a ≤ b → P.Sor a ≤ P.Sor b :=
    mono_of_step P.Sor (fun j => by have := st j; have := st (j + 1); omega)
  -- z_ack's edges: `E j ≤ Z j < ζ j ≤ E (j + 1)`
  have ζs : ∀ j, P.E j ≤ P.ζ j ∧ P.ζ j ≤ P.E (j + 1) := by
    intro j
    have h := E_le_Z V.H_ENUM V.H_RANGE Cs.H_POS (wo := 0) (Dl := 0) (fun _ _ => Nat.zero_le _)
      (Nat.zero_le _) (fun _ _ _ => Nat.zero_le _) TM.H_N j
    have h1 := Cs.H_SRV j; have h2 := Cs.H_CTL_C j; have h3 := Wzc.fst_ge (P.ζ j)
    have h4 := γ_le_E V.H_ENUM V.H_RANGE Cs.H_POS (j + 1)
    omega
  -- the joins
  have joinE : ∀ i, i < 3 → Tok (P.Lj i).hi (j i) P.E (P.g i) := by
    intro i hi
    obtain ⟨r1, r2, r3, -, -, -⟩ := TM.H_RST_LONG i hi
    obtain ⟨u1, u2, -⟩ := TM.H_RST_EARLY i hi
    have hxj : Tok R (xj i) (P.Xp i) (fun _ => true) :=
      ((V.H_X i hi).fifo (P.Wx i) (G.H_WX i hi)).mono (by omega)
    have hcp : Tok (0 + (P.Wc i).hi) (cp i) (P.Cp i) (fun _ => true) :=
      V.H_CTL.fifo (P.Wc i) (G.H_WC i hi)
    have hdec : Tok (0 + (P.Wc i).hi) (fun t => selF i (s0p i t) (s1p i t) (cp i t)) (P.Cp i)
        (P.g i) := by
      have := tok_gate2 hcp (selF i) (selF_off i) (v0 := fun k => b0 (P.sv k))
        (v1 := fun k => b1 (P.sv k)) (fun k t _ h1 h2 => V.H_S_PIN i hi k t h1 h2)
      exact this.gcongr (fun k => by rw [selF_idx hi (V.H_RANGE k)]; rfl)
    have hsl := hdec.fifo (P.Ls i) (y := sl i) (G.H_SEL i hi)
    have hsj := hsl.fifo (P.Wsj i) (G.H_WSJ i hi)
    have hD : Tok R (sj i) (P.D i) (fun _ => true) :=
      (hsj.reindex (V.H_ENUM i hi)).mono (by omega)
    have C : CEl (xj i) (sj i) rst (j i) (q i)
        (fun t => c2B (xj i t) (sj i t) (q i t) (rst t)) (P.Lj i) (P.wjl i) (P.wjh i) :=
      ⟨fun t => c2_spec _ _ _ _, G.H_UJ i hi, G.H_UJ_FB i hi, G.H_UJ_POS i hi⟩
    have n := cel_node C (cel_run C hxj hD V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r3 u1 u2
      (TM.H_DEP_J i hi))
    have n' := n.gcongr (fun _ => Bool.true_and _)
    exact (n'.congr (fun j => (E_rx (V.H_ENUM i hi) j).symm)).lift (V.H_ENUM i hi)
      (fun j => Em j (j + 1) (by omega))
  -- |j
  have pin : ∀ i, i < 3 → Tok P.Tj (jo i) P.Sor (P.g i) := by
    intro i hi
    have p := (joinE i hi).fifo (P.Wjo i) (G.H_WJO i hi)
    have p' : Tok P.Tj (jo i) (P.Op i) (P.g i) :=
      p.mono (by unfold MN3Run.Tj; obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
                 all_goals omega)
    refine tok_retime p' (fun t => ⟨t + 1, ?_⟩) Sm (fun k hk => ?_)
    · have := Eu (t + 1); have := (P.Wjo i).fst_ge (P.E (t + 1)); unfold MN3Run.Op; omega
    · have hs : P.sv k = i := by unfold MN3Run.g at hk; simpa using hk
      unfold MN3Run.Sor
      rw [show 2 * k / 2 = k by omega, show (2 * k + 1) / 2 = k by omega, hs]; exact ⟨rfl, rfl⟩
  have o := or3_same (pin 0 (by omega)) (pin 1 (by omega)) (pin 2 (by omega)) (fun k => by
    have := V.H_RANGE k; unfold MN3Run.g
    obtain h | h | h : P.sv k = 0 ∨ P.sv k = 1 ∨ P.sv k = 2 := by omega
    all_goals simp [h])
  have oj : Tok P.To orj P.OJ (fun _ => true) :=
    o.fifo P.Lo (fun t ht => by rw [G.H_OR3 t ht, or3_spec])
  have zt := ff_tok G.H_LINE oj TM.H_FLUSH P.N TM.H_N (Nat.le_refl _)
  -- the acknowledge C-elements, gate-aware
  have ack : ∀ i, i < 3 → Tok (P.Ta i) (ak i) (P.XA i) (P.g i) := by
    intro i hi
    obtain ⟨-, -, -, r4, r5, r6⟩ := TM.H_RST_LONG i hi
    obtain ⟨-, -, u4⟩ := TM.H_RST_EARLY i hi
    have hja : Tok R (ja i) (P.A i) (P.g i) :=
      ((joinE i hi).fifo (P.Wja i) (G.H_WJA i hi)).mono (by omega)
    have hzx : Tok R (zx i) (P.ZA i) (fun _ => true) :=
      (V.H_ZA.fifo (P.Wza i) (G.H_WZA i hi)).mono (by omega)
    have C : CEl (ja i) (zx i) rst (a i) (qa i)
        (fun t => c2B (ja i t) (zx i t) (qa i t) (rst t)) (P.La i) (P.wal i) (P.wah i) :=
      ⟨fun t => c2_spec _ _ _ _, G.H_UA i hi, G.H_UA_FB i hi, G.H_UA_POS i hi⟩
    have Am : ∀ j, P.A i j ≤ P.A i (j + 1) := fun j => fst_mono _ (Em j (j + 1) (by omega))
    have Zm : ∀ j, P.ZA i j ≤ P.ZA i (j + 1) := fun j =>
      fst_mono _ (by have := ζs j; have := ζs (j + 1); omega)
    have n := cel_node C (cel_run_g C hja hzx V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r6 u4
      (TM.H_DEP_A i hi) Zm (TM.H_SEQ_A i hi) (fun j => by have := Am j; have := Zm j; omega)
      (fun t => ⟨t + 1, by have := Eu (t + 1); have := (P.Wja i).fst_ge (P.E (t + 1))
                           unfold MN3Run.A; omega⟩)
      (fun t => ⟨t + 1, by have := Eu (t + 1); have := ζs (t + 1)
                           have := (P.Wza i).fst_ge (P.ζ (t + 1)); unfold MN3Run.ZA; omega⟩))
    exact n.fifo (P.Wak i) (G.H_WAK i hi)
  refine ⟨joinE, oj, zt, fun i hi => ⟨ack i hi, (ack i hi).reindex (V.H_ENUM i hi)⟩,
    fun i hi m => ?_, fun i hi j => ?_⟩
  · have e := E_rx (V.H_ENUM i hi) (2 * m); rw [rx_e] at e; rw [e]
    have := (P.Lj i).fst_ge (P.c i (2 * m))
    unfold MN3Run.τ MN3Run.c at *; omega
  · unfold MN3Run.XA MN3Run.cx MN3Run.ZA
    have := (P.Wza i).fst_ge (P.ζ j)
    have := (P.La i).fst_ge (max (P.A i j) ((P.Wza i).fst (P.ζ j)))
    have := (P.Wak i).fst_ge ((P.La i).fst (max (P.A i j) ((P.Wza i).fst (P.ζ j))))
    omega

/-! ## Static form -/

/-- **Static per-arc obligations of `bdc_muxn3`, real edges only.** -/
structure MN3StaticG (P : MN3Run) (Wzc : Ret) (Ex Ec Es wc ls wsj lj wo Dl : Nat) : Prop where
  H_MIN : ∀ i, i < 3 → wc ≤ (P.Wc i).lo ∧ ls ≤ (P.Ls i).lo ∧ wsj ≤ (P.Wsj i).lo ∧
    lj ≤ (P.Lj i).lo ∧ wo ≤ (P.Wjo i).lo
  H_DL0 : Dl ≤ (P.H 0).lo
  H_DLT : ∀ i, 1 ≤ i → i < P.N → Dl ≤ (P.Tp i).lo
  S_J_X : ∀ i, i < 3 → (P.Lj i).hi + P.wjh i ≤
    (P.Lj i).lo + (P.Wja i).lo + (P.La i).lo + (P.Wak i).lo + Ex + (P.Wx i).lo
  S_J_C : ∀ i, i < 3 → (P.Lj i).hi + P.wjh i ≤
    (P.Lj i).lo + (wo + P.Lo.lo + Dl + Es) + Wzc.lo + Ec + (P.Wc i).lo + (P.Ls i).lo + (P.Wsj i).lo
  S_A_RTZ : ∀ i, i < 3 → (P.Wza i).hi + ((P.La i).hi + P.wah i) ≤
    (P.Wza i).lo + (Wzc.lo + Ec + (wc + ls + wsj + lj)) + (wo + P.Lo.lo + Dl + Es)
  /-- `S_A_J.2` (unchanged). -/
  S_A_J2 : ∀ i, i < 3 → (P.Wja i).hi + ((P.La i).hi + P.wah i) ≤
      2 * (wo + P.Lo.lo + Dl + Es) + (Wzc.lo + Ec + (wc + ls + wsj + lj)) + (P.Wza i).lo
  /-- **S_A_R**: in a token of `i`, ua_i's loop settles before j_i's next
  real edge reaches ua_i: through client `i` (`S_A_N`, node-launched) or
  through the control sender (the shipped `S_A_FORK ∧ S_A_J.1`). -/
  S_A_R : ∀ i, i < 3 →
    (P.La i).hi + P.wah i ≤ (P.La i).lo + (P.Wak i).lo + Ex + (P.Wx i).lo + (P.Lj i).lo + (P.Wja i).lo ∨
    ((P.Wza i).hi + ((P.La i).hi + P.wah i) ≤ (Wzc.lo + Ec + (wc + ls + wsj + lj)) + (P.Wja i).lo ∧
     (P.Wja i).hi + ((P.La i).hi + P.wah i) ≤
      (wo + P.Lo.lo + Dl + Es) + (Wzc.lo + Ec + (wc + ls + wsj + lj)) + (P.Wja i).lo)
  /-- **S_A_SEQ**: a token of `i` after a token of another input: z_ack's
  fall reaches ua_i no later than j_i's rise. Order only. -/
  S_A_SEQ : ∀ i, i < 3 → (P.Wza i).hi ≤ (Wzc.lo + Ec + (wc + ls + wsj + lj)) + (P.Wja i).lo

theorem staticG_of_static {P : MN3Run} {Wzc : Ret} {Ex Ec Es wc ls wsj lj wo Dl : Nat}
    (S : MN3Static P Wzc Ex Ec Es wc ls wsj lj wo Dl) : MN3StaticG P Wzc Ex Ec Es wc ls wsj lj wo Dl where
  H_MIN := S.H_MIN
  H_DL0 := S.H_DL0
  H_DLT := S.H_DLT
  S_J_X := S.S_J_X
  S_J_C := S.S_J_C
  S_A_RTZ := S.S_A_RTZ
  S_A_J2 i hi := (S.S_A_J i hi).2
  S_A_R i hi := Or.inr ⟨S.S_A_FORK i hi, (S.S_A_J i hi).1⟩
  S_A_SEQ i hi := by have := S.S_A_FORK i hi; omega

section gstatic
variable {P : MN3Run} {Wzc : Ret} {Ex Ec Es wc ls wsj lj wo Dl : Nat}

theorem κ_succ {g : Nat → Bool} {κ : Nat → Nat} (h : Enum g κ) {m k : Nat} (hm : κ m = k)
    (hk : g (k + 1) = true) : κ (m + 1) = k + 1 := by
  obtain ⟨n, hn⟩ := h.all (k + 1) hk
  have h1 : m < n := h.lt_rev (by omega)
  have h2 := h.le_of_le (show m + 1 ≤ n by omega)
  have h3 := h.mono m
  omega

/-- **The event-form obligations from port-level causality and
`MN3StaticG`** (reset sequencing, the line's flush and `1 ≤ N` as given). -/
theorem muxn3_timing_g_of_static {R : Nat} (hE : ∀ i, i < 3 → Enum (P.g i) (P.κ i))
    (hR : ∀ k, P.sv k < 3) (Cs : MN3Causal P Wzc Ex Ec Es)
    (S : MN3StaticG P Wzc Ex Ec Es wc ls wsj lj wo Dl)
    (hRL : ∀ i, i < 3 → (P.Wx i).hi ≤ R ∧ (P.Wc i).hi + (P.Ls i).hi + (P.Wsj i).hi ≤ R ∧
      (P.Lj i).hi + P.wjh i ≤ R ∧ (P.Lj i).hi + (P.Wja i).hi ≤ R ∧ (P.Wza i).hi ≤ R ∧
      (P.La i).hi + P.wah i ≤ R)
    (hRE : ∀ i, i < 3 → R ≤ P.Xp i 0 ∧ R ≤ P.D i 0 ∧ R ≤ P.ZA i 0)
    (hFL : ∀ i, 1 ≤ i → i < P.N → ∀ k,
      (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 1)) ≤ (P.Tp i).fst (P.OJ (2 * k + 2)) ∧
      (P.Tp i).fst (P.OJ (2 * k + 1)) ≤ (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 2)))
    (hN : 1 ≤ P.N) : MN3TimingG P R := by
  have GE : ∀ j, P.γ j + (wc + ls + wsj + lj) ≤ P.E j := fun j => by
    have := γ_le_E hE hR Cs.H_POS j; have := S.H_MIN _ (hR (j / 2)); omega
  have EZ : ∀ j, P.E j + (wo + P.Lo.lo + Dl + Es) ≤ P.ζ j := fun j => by
    have := E_le_Z hE hR Cs.H_POS (fun i hi => (S.H_MIN i hi).2.2.2.2) S.H_DL0 S.H_DLT hN j
    have := Cs.H_SRV j; omega
  have ZE : ∀ j, P.ζ j + (Wzc.lo + Ec + (wc + ls + wsj + lj)) ≤ P.E (j + 1) := fun j => by
    have h1 := Cs.H_CTL_C j
    have hz : 1 ≤ P.ζ j := by have := EZ j; have := GE j; have := Cs.H_POS j; omega
    have h2 := fl Wzc hz
    have h3 := GE (j + 1)
    omega
  have GM : ∀ a b, a ≤ b → P.γ a ≤ P.γ b :=
    mono_of_step P.γ (fun j => by
      have := GE j; have := EZ j; have := Cs.H_CTL_C j
      have := Wzc.fst_ge (P.ζ j); omega)
  have Ep : ∀ j, 1 ≤ P.E j := fun j => by have := GE j; have := Cs.H_POS j; omega
  have hA : ∀ i n, P.cx i n + (P.La i).lo + (P.Wak i).lo ≤ P.XA i n := by
    intro i n
    have := Ep n
    have a := fl (P.Wja i) (Ep n)
    have hc : P.A i n ≤ P.cx i n := by unfold MN3Run.cx; omega
    have hAe : P.A i n = (P.Wja i).fst (P.E n) := rfl
    have b := fl (P.La i) (c := P.cx i n) (by omega)
    have c := fl (P.Wak i) (c := (P.La i).fst (P.cx i n)) (by omega)
    show _ ≤ (P.Wak i).fst ((P.La i).fst (P.cx i n)); omega
  have XAp : ∀ i n, 1 ≤ P.cx i n := by
    intro i n
    have := Ep n
    have a := (P.Wja i).fst_ge (P.E n)
    have hAe : P.A i n = (P.Wja i).fst (P.E n) := rfl
    unfold MN3Run.cx; omega
  -- in a token of `i`, j_i's edges at ua_i are launched by in_i_req's edges at uj_i
  have Aof : ∀ i, i < 3 → ∀ m r, r < 2 →
      P.Xp i (2 * m + r) + (P.Lj i).lo + (P.Wja i).lo ≤ P.A i (2 * P.κ i m + r) := by
    intro i hi m r hr
    have e := E_rx (hE i hi) (2 * m + r)
    unfold rx at e
    rw [show (2 * m + r) / 2 = m by omega, show (2 * m + r) % 2 = r by omega] at e
    have hc : 1 ≤ P.c i (2 * m + r) := by
      have := Cs.H_POS (2 * P.κ i ((2 * m + r) / 2) + (2 * m + r) % 2)
      have := Sd_ge Cs.H_POS i (2 * P.κ i ((2 * m + r) / 2) + (2 * m + r) % 2)
      have : P.D i (2 * m + r) = P.Sd i (2 * P.κ i ((2 * m + r) / 2) + (2 * m + r) % 2) := rfl
      unfold MN3Run.c; omega
    have a := fl (P.Lj i) hc
    have b := fl (P.Wja i) (c := P.E (2 * P.κ i m + r)) (Ep _)
    unfold MN3Run.A; unfold MN3Run.τ at e; unfold MN3Run.c at *; omega
  have xloop : ∀ i, i < 3 → ∀ j, P.g i (j / 2) = true → P.g i ((j + 1) / 2) = true →
      P.cx i j + (P.La i).lo + (P.Wak i).lo + Ex + (P.Wx i).lo + (P.Lj i).lo + (P.Wja i).lo ≤
        P.A i (j + 1) := by
    intro i hi j h0 h1
    obtain ⟨m, hm⟩ := (hE i hi).all (j / 2) h0
    have hXA := hA i j
    rcases Nat.mod_two_eq_zero_or_one j with hj | hj
    · have hx := Cs.H_XC_FALL i hi m
      rw [hm, show 2 * (j / 2) = j by omega] at hx
      have hp : 1 ≤ P.ξ i (2 * m + 1) := by have := XAp i j; omega
      have := fl (P.Wx i) hp
      have := Aof i hi m 1 (by omega)
      rw [show 2 * P.κ i m + 1 = j + 1 by omega] at this
      unfold MN3Run.Xp at *; omega
    · have hx := Cs.H_XC_RISE i hi m
      rw [hm, show 2 * (j / 2) + 1 = j by omega] at hx
      have hp : 1 ≤ P.ξ i (2 * m + 2) := by have := XAp i j; omega
      have := fl (P.Wx i) hp
      have hk1 := κ_succ (hE i hi) hm (by rw [show j / 2 + 1 = (j + 1) / 2 by omega]; exact h1)
      have := Aof i hi (m + 1) 0 (by omega)
      rw [hk1, show 2 * (j / 2 + 1) + 0 = j + 1 by omega,
        show 2 * (m + 1) + 0 = 2 * m + 2 by omega] at this
      unfold MN3Run.Xp at *; omega
  refine ⟨hRL, hRE, fun i hi j => ⟨?_, ?_⟩, fun i hi j _ => ⟨?_, fun _ => ?_⟩, fun i hi k _ _ => ?_,
    hFL, hN⟩
  · -- uj_i, through client i (as `muxn3_timing_of_static`)
    have e0 : P.τ i j = P.E (2 * P.κ i (j / 2) + j % 2) := by
      have := E_rx (hE i hi) j; unfold rx at this; exact this.symm
    have hXA : P.XA i (2 * P.κ i (j / 2) + j % 2) + Ex ≤ P.ξ i (j + 1) := by
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m := ⟨j / 2, by omega⟩
        have := Cs.H_XC_FALL i hi m
        rw [show 2 * m / 2 = m by omega, show 2 * m % 2 = 0 by omega, Nat.add_zero]; exact this
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m + 1 := ⟨j / 2, by omega⟩
        have := Cs.H_XC_RISE i hi m
        rw [show (2 * m + 1) / 2 = m by omega, show (2 * m + 1) % 2 = 1 by omega]; exact this
    have hA' : ∀ n, P.E n + (P.Wja i).lo + (P.La i).lo + (P.Wak i).lo ≤ P.XA i n := by
      intro n
      have := Ep n
      have a := fl (P.Wja i) (Ep n)
      have hc : P.A i n ≤ P.cx i n := by unfold MN3Run.cx; omega
      have hAe : P.A i n = (P.Wja i).fst (P.E n) := rfl
      have b := fl (P.La i) (c := P.cx i n) (by omega)
      have c := fl (P.Wak i) (c := (P.La i).fst (P.cx i n)) (by omega)
      show _ ≤ (P.Wak i).fst ((P.La i).fst (P.cx i n)); omega
    have := hA' (2 * P.κ i (j / 2) + j % 2)
    have hp : 1 ≤ P.ξ i (j + 1) := by have := Ep (2 * P.κ i (j / 2) + j % 2); omega
    have := fl (P.Wx i) hp
    have : P.Xp i (j + 1) = (P.Wx i).fst (P.ξ i (j + 1)) := rfl
    have t0 : P.c i j + (P.Lj i).lo ≤ P.τ i j := fl (P.Lj i) (by
      have := Cs.H_POS (2 * P.κ i (j / 2) + j % 2)
      have := Sd_ge Cs.H_POS i (2 * P.κ i (j / 2) + j % 2)
      have : P.D i j = P.Sd i (2 * P.κ i (j / 2) + j % 2) := rfl
      unfold MN3Run.c; omega)
    have := S.S_J_X i hi
    omega
  · -- uj_i, through the server, the control sender and decode i
    have e0 : P.τ i j = P.E (2 * P.κ i (j / 2) + j % 2) := by
      have := E_rx (hE i hi) j; unfold rx at this; exact this.symm
    have hk : P.D i (j + 1) = P.Sd i (2 * P.κ i ((j + 1) / 2) + (j + 1) % 2) := rfl
    have hge : 2 * P.κ i (j / 2) + j % 2 + 1 ≤ 2 * P.κ i ((j + 1) / 2) + (j + 1) % 2 := by
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · rw [show (j + 1) / 2 = j / 2 by omega]; omega
      · have := (hE i hi).mono (j / 2); rw [show (j + 1) / 2 = j / 2 + 1 by omega]; omega
    have g := GM _ _ hge
    have hS := Sd_ge Cs.H_POS i (2 * P.κ i ((j + 1) / 2) + (j + 1) % 2)
    have hz := EZ (2 * P.κ i (j / 2) + j % 2)
    have hc := Cs.H_CTL_C (2 * P.κ i (j / 2) + j % 2)
    have hzz : 1 ≤ P.ζ (2 * P.κ i (j / 2) + j % 2) := by
      have := Ep (2 * P.κ i (j / 2) + j % 2); omega
    have hw := fl Wzc hzz
    have t0 : P.c i j + (P.Lj i).lo ≤ P.τ i j := fl (P.Lj i) (by
      have := Cs.H_POS (2 * P.κ i (j / 2) + j % 2)
      have := Sd_ge Cs.H_POS i (2 * P.κ i (j / 2) + j % 2)
      have : P.D i j = P.Sd i (2 * P.κ i (j / 2) + j % 2) := rfl
      unfold MN3Run.c; omega)
    have := S.S_J_C i hi
    omega
  · -- ua_i against the next z_ack edge (H_MUX_RTZ and S_A_J.2, as shipped)
    have := (P.Wja i).fst_le (P.E j); have := (P.Wza i).fst_le (P.ζ j)
    have hz1 : 1 ≤ P.ζ (j + 1) := by have := EZ (j + 1); have := Ep (j + 1); omega
    have := fl (P.Wza i) hz1
    have := ZE j; have := EZ j; have := EZ (j + 1); have := S.S_A_RTZ i hi; have := S.S_A_J2 i hi
    unfold MN3Run.cx MN3Run.A MN3Run.ZA; omega
  · -- ua_i against j_i's next real edge: the client loop or the fork pair
    rename_i h0 h1
    rcases S.S_A_R i hi with hN' | ⟨hF, hJ⟩
    · have := xloop i hi j h0 h1; omega
    · have := (P.Wja i).fst_le (P.E j); have := (P.Wza i).fst_le (P.ζ j)
      have := fl (P.Wja i) (Ep (j + 1))
      have := ZE j; have := EZ j
      unfold MN3Run.cx MN3Run.A MN3Run.ZA; omega
  · -- H_SEQ_A: order only
    have := ZE (2 * k + 1); have := S.S_A_SEQ i hi
    have h := fst_order (P.Wza i) (P.Wja i) (a := P.ζ (2 * k + 1)) (b := P.E (2 * k + 2)) (Ep _)
      (by rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega] at *; omega)
    unfold MN3Run.ZA MN3Run.A; exact h

/-- **`muxn3_ok_gs` (sufficient)**: `muxn3_ok`'s conclusion from causal
partners and `MN3StaticG` (reset sequencing, the line's flush and `1 ≤ N`
as given). -/
theorem muxn3_ok_gs {R : Nat} {rst ctl za orj : Trace}
    {x xj cp s0p s1p sl sj j q jo s ja zx a qa ak : Nat → Trace}
    (G : MN3Gates P rst ctl za x xj cp s0p s1p sl sj j q jo orj s ja zx a qa ak)
    (V : MN3Env P rst ctl za x s0p s1p R) (Cs : MN3Causal P Wzc Ex Ec Es)
    (S : MN3StaticG P Wzc Ex Ec Es wc ls wsj lj wo Dl)
    (hRL : ∀ i, i < 3 → (P.Wx i).hi ≤ R ∧ (P.Wc i).hi + (P.Ls i).hi + (P.Wsj i).hi ≤ R ∧
      (P.Lj i).hi + P.wjh i ≤ R ∧ (P.Lj i).hi + (P.Wja i).hi ≤ R ∧ (P.Wza i).hi ≤ R ∧
      (P.La i).hi + P.wah i ≤ R)
    (hRE : ∀ i, i < 3 → R ≤ P.Xp i 0 ∧ R ≤ P.D i 0 ∧ R ≤ P.ZA i 0)
    (hFL : ∀ i, 1 ≤ i → i < P.N → ∀ k,
      (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 1)) ≤ (P.Tp i).fst (P.OJ (2 * k + 2)) ∧
      (P.Tp i).fst (P.OJ (2 * k + 1)) ≤ (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 2)))
    (hN : 1 ≤ P.N) :
    (∀ i, i < 3 → Tok (P.Lj i).hi (j i) P.E (P.g i)) ∧
    Tok (ffT P.H P.Tp P.To P.N) (s P.N) P.Z (fun _ => true) ∧
    (∀ i, i < 3 → Tok (P.Ta i) (ak i) (P.XA i) (P.g i) ∧
      Tok (P.Ta i) (ak i) (rx (P.XA i) (P.κ i)) (fun _ => true)) := by
  have h := muxn3_ok_g G V (muxn3_timing_g_of_static V.H_ENUM V.H_RANGE Cs S hRL hRE hFL hN) Cs
  exact ⟨h.1, h.2.2.1, h.2.2.2.1⟩

end gstatic

end Nec7
end Formal.Cells.MuxN3Timed
