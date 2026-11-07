import Formal.Cells.AssumeGuaranteeMuxNet
import Formal.Cells.LibGapMuxN

/-!
# Probe Bmn (shard B): `bdc_muxn`'s cells as segment specs

gcd_hw has ONE `bdc_muxn3_32` (`bdc/emit.py` `emit_muxn(32, 3)`, DELAY 12, BDC_FASTFALL = 1,
the emitter's default). Its handshake cells (`MuxN3`, `LibGapMuxN`, `MuxN3Timed`):

    sel[k] = ctl_req & (s == k)       decode LUT3 (inferred INIT, H_YOSYS_MAP), k = 0, 1, 2
    j[k]   = bd_c2 uj_k (in_k_req, sel[k])
    |j     = LUT3 FE (j2, j1, j0)     the request OR (inferred)
    either = LUT1 2'h2 uor (|j)       a buffer (keep)
    z_req  = bd_delay_gated #(12) (either, gate = |j): stage 0 a LUT1 buffer, stages 1..11
             LUT2 8 = s[i] & |j (FASTFALL: the fall is flushed from |j into every stage)
    in_k_ack = bd_c2 ua_k (j[k], z_ack);   ctl_ack = z_ack

This file gives each cell the per-segment form `net_closed_gen` consumes (a cell spec with
H_CELL and H_WAIT, as `MuxJSpec`/`MuxASpec` of `AssumeGuaranteeMuxNet`), or shows why the
segment rule cannot carry it.

## Assumed / proved / NOT covered

**Proved:**
* `dgated_segK`: segment `k` of the DECODED gate `ctl_req ∧ (code(s0, s1) == k)` from the
  control request's segments `≤ sN κ k`, H_SEL_STABLE per index bit (both bits show the token's
  code while `ctl_req` is high), H_S_RANGE (`σ n < 4`) and the enumeration `κ` of the control
  tokens whose code is `k`. Reduced to Bseg's `gated_segK` on the Bool trace `code == k`.
* `dec_segK`: the REAL decode LUT3 (`LibGapMuxN.dec`, INITs `8'h10`/`8'h40`/`8'h40` with
  H_YOSYS_MAP's pin orders) carries that segment to its node (`lutnf_segK`).
  `DecSpec`, `dec_spec_cell`, `dec_spec_wait` (H_WAIT unconditional, as a steer branch's).
* The joins `uj_k` are `bd_c2` on `(in_k_req, sel[k])`, both pins four-phase in the join's own
  numbering (the decode node carries only `k`'s tokens), so they are Bseg's `CelSpec GC2`
  (no new spec; `uj_is_c2`).
* The acknowledges `ua_k = bd_c2 (j[k], z_ack)`: `z_ack` carries the tokens of ALL THREE
  inputs; `ua_cel` (the real `bd_c2` LUT is the `G2` model), so Bmux2's `MuxASpec` applies
  verbatim, with `κ` the tokens of input `k` (`H_ZFALL`, `H_SNDZ` as there; no `σ` needed).
* The line: `uor` and stage 0 are LUT1 buffers (`buf_init`): Bmux2's `BufSpec`.
* **Negative** (`Wit.gstage_not_causal`): a FASTFALL stage `s[i+1] = s[i] ∧ |j` falls from
  `|j` BEFORE its data pin `s[i]` falls; its high segment needs `s[i]` high up to its own fall,
  a PREFIX of a data segment that ends later. On a run: the data segment ends at `16`, the
  stage's node edge is `13` (H_WAIT fails for any `nb` that includes it), and a data trace
  equal on every earlier segment but low at `t = 10` breaks the stage's excitation (dropping
  it fails). Same shape as the ORs (`AssumeGuaranteeMuxOr.Wit.or_not_causal`).
* Witnesses (REAL INITs, band `[1, 1]`, feedback 1, reset 4), one 3-way run (`Wit`): the
  control carries tokens with codes `0, 1, 2, 0, ...`; decode 0 fires on every third token
  only; `uj0` joins it with `in0_req`; `ua0` holds low through the other two inputs' `z_ack`
  pulses. Every hypothesis of `dgated_segK`/`dec_segK`, `celG_segK` (on `GC2`) and
  `muxa_segK` holds and every node segment follows (`Wit.muxn_witness`).

**Assumed (named):** B's gate models (`Win` + H_NO_REVERT; `CelG`), H_PWR, H_RST_LONG,
H_LAT, H_YOSYS_MAP (the decode INITs and pin orders, as in `AMergeGates`); H_SEL_STABLE per
index bit and H_S_RANGE; per cell the departure bounds as edge-time inequalities.

**NOT covered (in this segment form):** the request OR `|j`; the 11 FASTFALL stages of the
line (not segment-causal, above; `AssumeGuaranteeMuxNFin.tand` carries them in Bfin2's
time-indexed rule); the data mux (bundling, not a handshake cell); departure bounds from
delay constants. Core Lean only.
-/

namespace Formal.Cells.AssumeGuaranteeMuxN
open Formal.Cells
open Formal.Cells.AssumeGuaranteeLinks (SegK phases_of_segK segK_of_phases)
open Formal.Cells.AssumeGuaranteeEnds (GPin gE GA sN sN_even sN_odd gc_sN gated_segK lutnf_segK
  steer_wait GC2 c2_gen lawC2 celG_segK)
open Formal.Cells.AssumeGuaranteeEndsNet
open Formal.Cells.AssumeGuaranteeMux (muxa_segK max_last)
open Formal.Cells.AssumeGuaranteeMuxNet
open Formal.Cells.WinFifo (Win win_le)
open Formal.Cells.WinFifoCausal (NoRevertI nt nt_lo)
open Formal.Cells.PipeTimed (Vph)
open Formal.Cells.LutFbBridge (Phases)
open Formal.Cells.LutFbBridge2 (CelG gc G2 pv2)
open Formal.Cells.LibGapMuxN (code bit0 bit1 code_bits dec dec_eq)
open Formal.Net.Ops.Gen (genF cel2)
open Formal.Gen Formal.Gen.Cells

/-! ## 1. The decoded gate and the decode LUT3 -/

/-- **The decoded gate, one segment.** Segment `j` of `r ∧ (code(s0, s1) == k)` (phase starts
`gc κ γ`) from the request's segments `≤ sN κ j`, H_SEL_STABLE per index bit (while `r` is high
in token `n`, bit `i` shows bit `i` of the token's code `σ n`), H_S_RANGE (`σ n < 4`) and an
enumeration `κ` (strictly increasing) of exactly the tokens whose code is `k`. -/
theorem dgated_segK {r s0 s1 : Nat → Bool} {γ σ κ : Nat → Nat} {k : Nat}
    (hγ : ∀ j, γ j < γ (j + 1))
    (H_SEL_STABLE : ∀ n t, γ (2 * n) ≤ t → t < γ (2 * n + 1) →
      s0 t = bit0 (σ n) ∧ s1 t = bit1 (σ n))
    (H_S_RANGE : ∀ n, σ n < 4)
    (hκ : ∀ m, κ m < κ (m + 1)) (hκk : ∀ m, σ (κ m) = k)
    (hκall : ∀ n, σ n = k → ∃ m, κ m = n) (j : Nat)
    (hr : ∀ k', k' ≤ sN κ j → SegK r γ k') :
    SegK (fun t => r t && (code (s0 t) (s1 t) == k)) (gc κ γ) j := by
  have hS : ∀ n t, γ (2 * n) ≤ t → t < γ (2 * n + 1) →
      (code (s0 t) (s1 t) == k) = (σ n == k) := by
    intro n t h1 h2
    obtain ⟨e0, e1⟩ := H_SEL_STABLE n t h1 h2
    rw [e0, e1, code_bits _ (H_S_RANGE n)]
  have g := gated_segK (s := fun t => code (s0 t) (s1 t) == k) (σ := fun n => σ n == k)
    (b := true) hγ hS hκ (fun m => by simp [hκk m])
    (fun n h => hκall n (by simpa using h)) j hr
  have e : (fun t => r t && ((code (s0 t) (s1 t) == k) == true)) =
      (fun t => r t && (code (s0 t) (s1 t) == k)) := by
    funext t; cases (code (s0 t) (s1 t) == k) <;> rfl
  rw [e] at g; exact g

/-- The decode's generated excitation is the decoded gate (`LibGapMuxN.dec_eq`). -/
theorem dec_exc (k : Nat) (hk : k < 3) (cr s0 s1 : Nat → Bool) :
    (fun t => dec k (s0 t) (s1 t) (cr t)) = (fun t => cr t && (code (s0 t) (s1 t) == k)) :=
  funext fun _ => dec_eq k hk _ _ _

/-- **Decode `k`, one segment** (the REAL inferred LUT3, `Win` + H_NO_REVERT, no feedback, no
reset): its node segment `j` (edges `nt O lo hi (gc κ γ j) (Vph j)`) from the control
request's segments `≤ sN κ j`. -/
theorem dec_segK (k : Nat) (hk : k < 3) {cr s0 s1 O : Nat → Bool} {lo hi : Nat}
    {γ σ κ : Nat → Nat}
    (H_LUT_WIN : Win lo hi (fun t => dec k (s0 t) (s1 t) (cr t)) O)
    (H_NO_REVERT : NoRevertI lo hi (fun t => dec k (s0 t) (s1 t) (cr t)) O)
    (H_PWR : ∀ t, t < hi → O t = false)
    (hγ : ∀ j, γ j < γ (j + 1))
    (H_SEL_STABLE : ∀ n t, γ (2 * n) ≤ t → t < γ (2 * n + 1) →
      s0 t = bit0 (σ n) ∧ s1 t = bit1 (σ n))
    (H_S_RANGE : ∀ n, σ n < 4)
    (hκ : ∀ m, κ m < κ (m + 1)) (hκk : ∀ m, σ (κ m) = k)
    (hκall : ∀ n, σ n = k → ∃ m, κ m = n)
    (H_SPACE : hi ≤ gc κ γ 0 ∧ ∀ j, gc κ γ j + hi < gc κ γ (j + 1) + lo) (j : Nat)
    (hr : ∀ k', k' ≤ sN κ j → SegK cr γ k') :
    SegK O (fun j => nt O lo hi (gc κ γ j) (Vph j)) j := by
  rw [dec_exc k hk] at H_LUT_WIN H_NO_REVERT
  exact lutnf_segK H_LUT_WIN H_NO_REVERT H_PWR H_SPACE j
    (dgated_segK hγ H_SEL_STABLE H_S_RANGE hκ hκk hκall j hr)

/-! ## 2. The acknowledges and the line buffers: the real LUTs are Bmux2's models -/

/-- `bd_c2` is the `G2` model. -/
theorem GC2_G2 : GC2 = G2 := by
  funext pv q r; unfold GC2 G2; rw [c2_gen]

/-- **`ua_k` (the REAL `bd_c2`, pins `a = j[k]`, `b = z_ack`) is the `G2` model of
`(j[k], z_ack)`**, so `MuxASpec` applies to it as to `bd_mux`'s `uxa`/`uya`. -/
theorem ua_cel {a z rst O qp : Nat → Bool} {lo hi wl wh : Nat}
    (H_LUT_WIN : Win lo hi (fun t => genF bd_c2 "u" .O ["a", "b", "q", "rst"]
      [a t, z t, qp t, rst t]) O)
    (H_NO_REVERT : NoRevertI lo hi (fun t => genF bd_c2 "u" .O ["a", "b", "q", "rst"]
      [a t, z t, qp t, rst t]) O)
    (H_FB : CElemTiming.WinDelay wl wh O qp) (H_LUT_POS : 1 ≤ lo) :
    CelG G2 (pv2 a z) rst O qp lo hi wl wh := by
  have e : (fun t => genF bd_c2 "u" .O ["a", "b", "q", "rst"] [a t, z t, qp t, rst t]) =
      (fun t => G2 (pv2 a z t) (qp t) (rst t)) := by
    funext t; rw [c2_gen]; rfl
  rw [e] at H_LUT_WIN H_NO_REVERT
  exact ⟨H_LUT_WIN, H_NO_REVERT, H_FB, H_LUT_POS⟩

/-- **`uj_k` is `bd_c2` on `(in_k_req, sel[k])`**: the generated `bd_c2` LUT is the
C-element `GC2` of Bseg's `CelSpec` (the identity; recorded so the census can cite it). -/
theorem uj_is_c2 (a b q r : Bool) :
    genF bd_c2 "u" .O ["a", "b", "q", "rst"] [a, b, q, r] = GC2 (fun i => if i.val = 0 then a else b) q r := rfl

/-- **`uor` and stage 0 of `bd_delay_gated`** are `LUT1 #(.INIT(2'h2))`: buffers. -/
theorem buf_init (a : Bool) : AMergeGates.buf1 a = a := AMergeGates.buf1_eq a

/-! ## 3. The decode as a cell spec -/

variable {ι : Type}

/-- **A decode LUT3 of `bdc_muxn`** (`sel[k]`, the REAL inferred INIT): one pin, the control
request, read up to segment `sN κ j`; the index bits `s0`, `s1` are data traces, stable while
the control request is high (H_SEL_STABLE, as a steer's select). -/
structure DecSpec (D : GD ι) (c : ι) (cp : GPin ι) (k : Nat) (s0 s1 : Nat → Bool)
    (σ κ : Nat → Nat) : Prop where
  H_K : k < 3
  H_PINS : D.pins c = [cp]
  H_NB : cp.nb = fun j => sN κ j + 1
  H_LUT_WIN : Win (D.lo c) (D.hi c) (fun t => dec k (s0 t) (s1 t) (cp.P t)) (D.O c)
  H_NO_REVERT : NoRevertI (D.lo c) (D.hi c) (fun t => dec k (s0 t) (s1 t) (cp.P t)) (D.O c)
  H_PWR : ∀ t, t < D.hi c → D.O c t = false
  H_TIMES : ∀ j, D.τ c j = nt (D.O c) (D.lo c) (D.hi c) (gc κ (gE D.τ cp) j) (Vph j)
  H_INC : ∀ j, gE D.τ cp j < gE D.τ cp (j + 1)
  H_SEL_STABLE : ∀ n t, gE D.τ cp (2 * n) ≤ t → t < gE D.τ cp (2 * n + 1) →
    s0 t = bit0 (σ n) ∧ s1 t = bit1 (σ n)
  H_S_RANGE : ∀ n, σ n < 4
  H_KAPPA : ∀ m, κ m < κ (m + 1)
  H_KAPPA_K : ∀ m, σ (κ m) = k
  H_KAPPA_ALL : ∀ n, σ n = k → ∃ m, κ m = n
  H_SPACE : D.hi c ≤ gc κ (gE D.τ cp) 0 ∧
    ∀ j, gc κ (gE D.τ cp) j + D.hi c < gc κ (gE D.τ cp) (j + 1) + D.lo c

theorem dec_spec_cell {D : GD ι} {c : ι} {cp : GPin ι} {k : Nat} {s0 s1 : Nat → Bool}
    {σ κ : Nat → Nat} (S : DecSpec D c cp k s0 s1 σ κ) (j : Nat) (hA : GA D.τ D.pins c j) :
    SegK (D.O c) (D.τ c) j := by
  have hc : cp ∈ D.pins c := by rw [S.H_PINS]; simp
  rw [show D.τ c = _ from funext S.H_TIMES]
  exact dec_segK k S.H_K S.H_LUT_WIN S.H_NO_REVERT S.H_PWR S.H_INC S.H_SEL_STABLE S.H_S_RANGE
    S.H_KAPPA S.H_KAPPA_K S.H_KAPPA_ALL S.H_SPACE j
    (fun k' h => hA cp hc k' (by rw [S.H_NB]; dsimp only; omega))

theorem dec_spec_wait {D : GD ι} {c : ι} {cp : GPin ι} {k : Nat} {s0 s1 : Nat → Bool}
    {σ κ : Nat → Nat} (S : DecSpec D c cp k s0 s1 σ κ) :
    ∀ p ∈ D.pins c, ∀ j j', j' < p.nb j → gE D.τ p j' + D.lo c ≤ D.τ c j := by
  intro p hp j j' hj
  have hp' := hp
  rw [S.H_PINS] at hp'
  have e : p = cp := by simpa using hp'
  subst e
  rw [S.H_NB] at hj; dsimp only at hj
  rw [S.H_TIMES j]
  exact steer_wait (win_le S.H_LUT_WIN) S.H_INC j j' hj

/-! ## 4. Non-vacuity on one 3-way run, and the FASTFALL stage's non-causality -/

namespace Wit
open Formal.Cells.PipeTimed.Wit (rstW)
open Formal.Cells.WinFifoCausal (nt_eq noRevertI_shift)
open Formal.Cells.AssumeGuaranteeMux.Wit (pw8 e8 pw8_segK e8_inc)

/-- Period-24 waves, high 4 ticks from offset `o`, and their edges. -/
def p24 (o t : Nat) : Bool := decide (o ≤ t ∧ (t - o) % 24 < 4)
def e24 (o j : Nat) : Nat := o + 24 * (j / 2) + 4 * (j % 2)

theorem p24_segK (o k : Nat) : SegK (p24 o) (e24 o) k := by
  match k with
  | 0 =>
    intro t _ ht
    show decide _ = false
    simp only [decide_eq_false_iff_not]; unfold e24 at ht; omega
  | j + 1 =>
    intro t h1 h2
    have h1' : e24 o j ≤ t := h1
    show decide _ = decide (j % 2 = 0)
    rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; unfold e24 at h1' h2; omega

theorem p24_per (o u : Nat) (h : o + 24 ≤ u) : p24 o u = p24 o (u - 24) := by
  unfold p24; rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega
theorem pw8_per24 (o u : Nat) (h : o + 24 ≤ u) : pw8 o u = pw8 o (u - 24) := by
  unfold pw8; rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega

/-- The run: `ctl_req` (`cr`) carries a control token every 8 ticks, high on `[8n+10, 8n+14)`;
token `n`'s code is `n % 3` (`σ`), shown on the index bits `s0`, `s1` (`sidx`); `in0_req` (`x0`)
is high on `[24m+9, 24m+13)`; `z_ack` (`zA`) carries EVERY output token, high on
`[8n+14, 8n+18)`; input 0 owns the tokens `κ m = 3m`. -/
def cr : Nat → Bool := pw8 10
def sidx (t : Nat) : Nat := (t - 10) / 8 % 3
def s0 (t : Nat) : Bool := bit0 (sidx t)
def s1 (t : Nat) : Bool := bit1 (sidx t)
def σ (n : Nat) : Nat := n % 3
def κ (m : Nat) : Nat := 3 * m
def x0 : Nat → Bool := p24 9
def zA : Nat → Bool := pw8 14
/-- Decode 0, a 1-tick transport copy of its REAL excitation. -/
def Od (t : Nat) : Bool := if t = 0 then false else dec 0 (s0 (t - 1)) (s1 (t - 1)) (cr (t - 1))
/-- `uj0` and `ua0` (closed forms, checked against the REAL LUTs below). -/
def Oj : Nat → Bool := p24 12
def qpj (t : Nat) : Bool := Oj (t - 1)
def Oa : Nat → Bool := p24 15
def qpa (t : Nat) : Bool := Oa (t - 1)

theorem Od_eq (t : Nat) : Od t = p24 11 t := by
  unfold Od
  by_cases h0 : t = 0
  · subst h0; rfl
  · simp only [h0, ↓reduceIte]
    rw [dec_eq 0 (by decide), s0, s1, code_bits _ (by unfold sidx; omega)]
    unfold cr pw8 p24 sidx
    rw [Bool.eq_iff_iff]
    simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq]
    omega

theorem gc_w (j : Nat) : gc κ (e8 10) j = 10 + 24 * (j / 2) + 4 * (j % 2) := by
  unfold gc κ e8; omega

theorem ntd (j : Nat) : nt Od 1 1 (gc κ (e8 10) j) (Vph j) = e24 11 j := by
  rw [gc_w, nt_eq Od (Nat.le_refl 1)]
  · unfold e24; omega
  · rw [Od_eq]
    show decide _ = decide (j % 2 = 0)
    rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega

theorem uj0_small : ∀ t, t < 64 → 1 ≤ t →
    Oj t = (!rstW (t - 1) && cel2 (x0 (t - 1)) (p24 11 (t - 1)) (Oj (t - 1 - 1))) := by
  decide

theorem uj0_step : ∀ t, 1 ≤ t →
    Oj t = (!rstW (t - 1) && cel2 (x0 (t - 1)) (p24 11 (t - 1)) (Oj (t - 1 - 1))) := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht
    by_cases hs : t < 64
    · exact uj0_small t hs ht
    · have h := ih (t - 24) (by omega) (by omega)
      have r1 : rstW (t - 1) = rstW (t - 24 - 1) := by unfold rstW; simp; omega
      unfold Oj x0 at h ⊢
      rw [p24_per 12 t (by omega), p24_per 9 (t - 1) (by omega), p24_per 11 (t - 1) (by omega),
        p24_per 12 (t - 1 - 1) (by omega), r1, h,
        show t - 1 - 24 = t - 24 - 1 by omega, show t - 1 - 1 - 24 = t - 24 - 1 - 1 by omega]

theorem ua0_small : ∀ t, t < 64 → 1 ≤ t →
    Oa t = (!rstW (t - 1) && cel2 (Oj (t - 1)) (zA (t - 1)) (Oa (t - 1 - 1))) := by
  decide

theorem ua0_step : ∀ t, 1 ≤ t →
    Oa t = (!rstW (t - 1) && cel2 (Oj (t - 1)) (zA (t - 1)) (Oa (t - 1 - 1))) := by
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro ht
    by_cases hs : t < 64
    · exact ua0_small t hs ht
    · have h := ih (t - 24) (by omega) (by omega)
      have r1 : rstW (t - 1) = rstW (t - 24 - 1) := by unfold rstW; simp; omega
      unfold Oa Oj zA at h ⊢
      rw [p24_per 15 t (by omega), p24_per 12 (t - 1) (by omega), pw8_per24 14 (t - 1) (by omega),
        p24_per 15 (t - 1 - 1) (by omega), r1, h,
        show t - 1 - 24 = t - 24 - 1 by omega, show t - 1 - 1 - 24 = t - 24 - 1 - 1 by omega]

/-- **Non-vacuity, one 3-way run of `bdc_muxn`'s input-0 path, REAL INITs, band `[1, 1]`,
feedback 1, reset 4.** Decode 0 (`dec_segK`, the inferred LUT3 `8'h10`) fires on the control
tokens with code 0 only (`κ m = 3m`; at `t = 18`, a code-1 token, `ctl_req` is high and the
decode stays low); `uj0` (`celG_segK` on the real `bd_c2` = `GC2`) joins `in0_req` with the
decode node; `ua0` (`muxa_segK`, real `bd_c2` via `ua_cel`) holds LOW through the `z_ack`
pulses of the other two inputs' tokens (`t = 22`: `z_ack` high, `j0` low, `ua0` low). Every
hypothesis of the three lemmas holds and every node segment of the three cells follows. -/
theorem muxn_witness :
    (∀ k, SegK Od (e24 11) k) ∧
    CelG GC2 (pv2 x0 Od) rstW Oj qpj 1 1 1 1 ∧ (∀ k, SegK Oj (e24 12) k) ∧
    CelG G2 (pv2 Oj zA) rstW Oa qpa 1 1 1 1 ∧ (∀ k, SegK Oa (e24 15) k) ∧
    (cr 18 = true ∧ Od 19 = false) ∧ (zA 22 = true ∧ Oj 22 = false ∧ Oa 23 = false) := by
  -- decode 0
  have hxd : ∀ t, 1 ≤ t → Od t = dec 0 (s0 (t - 1)) (s1 (t - 1)) (cr (t - 1)) := by
    intro t ht; unfold Od; simp [show t ≠ 0 by omega]
  have hWd : Win 1 1 (fun t => dec 0 (s0 t) (s1 t) (cr t)) Od :=
    fun t ht => ⟨t - 1, by omega, by omega, hxd t ht⟩
  have hNd : NoRevertI 1 1 (fun t => dec 0 (s0 t) (s1 t) (cr t)) Od := noRevertI_shift hxd
  have hS : ∀ n t, e8 10 (2 * n) ≤ t → t < e8 10 (2 * n + 1) →
      s0 t = bit0 (σ n) ∧ s1 t = bit1 (σ n) := by
    intro n t h1 h2
    unfold e8 at h1 h2
    have : sidx t = σ n := by unfold sidx σ; rw [show (t - 10) / 8 = n by omega]
    unfold s0 s1; rw [this]; exact ⟨rfl, rfl⟩
  have hd : ∀ k, SegK Od (e24 11) k := by
    intro k
    have := dec_segK 0 (by decide) (κ := κ) (σ := σ) hWd hNd
      (fun t h => by unfold Od; simp [show t = 0 by omega]) (e8_inc 10) hS
      (fun n => by unfold σ; omega) (fun m => by unfold κ; omega)
      (fun m => by unfold σ κ; omega) (fun n h => ⟨n / 3, by unfold σ at h; unfold κ; omega⟩)
      ⟨by rw [gc_w]; omega, fun j => by rw [gc_w, gc_w]; omega⟩ k (fun k' _ => pw8_segK 10 k')
    rwa [show (fun j => nt Od 1 1 (gc κ (e8 10) j) (Vph j)) = e24 11 from funext ntd] at this
  -- uj0
  have hWj : Win 1 1 (fun t => GC2 (pv2 x0 Od t) (qpj t) (rstW t)) Oj := fun t ht =>
    ⟨t - 1, by omega, by omega, by
      show Oj t = GC2 (pv2 x0 Od (t - 1)) (qpj (t - 1)) (rstW (t - 1))
      rw [GC2_G2, uj0_step t ht, ← Od_eq]; rfl⟩
  have hNj : NoRevertI 1 1 (fun t => GC2 (pv2 x0 Od t) (qpj t) (rstW t)) Oj :=
    noRevertI_shift (fun t ht => by
      show Oj t = GC2 (pv2 x0 Od (t - 1)) (qpj (t - 1)) (rstW (t - 1))
      rw [GC2_G2, uj0_step t ht, ← Od_eq]; rfl)
  have Cj : CelG GC2 (pv2 x0 Od) rstW Oj qpj 1 1 1 1 :=
    ⟨hWj, hNj, fun t ht => ⟨t - 1, by omega, by omega, rfl⟩, Nat.le_refl 1⟩
  have ntj : ∀ j, nt Oj 1 1 (e24 11 j) (Vph j) = e24 12 j := by
    intro j
    rw [nt_eq Oj (Nat.le_refl 1)]
    · unfold e24; omega
    · show p24 12 _ = decide (j % 2 = 0)
      unfold p24 e24; rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega
  let ρj : Fin 2 → Nat → Nat := fun i => if i.val = 0 then e24 9 else e24 11
  have hj : ∀ k, SegK Oj (e24 12) k := by
    intro k
    have := celG_segK lawC2 Cj (0 : Fin 2) (R := 4) (E := 1) (ρ := ρj) (c := e24 11)
      (fun _ => rfl) (by decide) (by decide) (fun t h => by unfold Oj p24; simp; omega)
      (fun i j => by
        by_cases h : i.val = 0
        · simp only [ρj, h, ite_true]; unfold e24; omega
        · simp only [ρj, h, ite_false]; exact Nat.le_refl _)
      (fun j s h => ⟨1, by simp only [ρj]; exact h⟩) (by decide)
      (fun i j => by
        rw [ntj]
        by_cases h : i.val = 0
        · simp only [ρj, h, ite_true]; unfold e24; omega
        · simp only [ρj, h, ite_false]; unfold e24; omega) k
      (fun hk i t _ ht => by
        subst hk
        by_cases h : i.val = 0
        · simp only [ρj, h, ite_true] at ht; simp only [pv2, h, ite_true]
          exact p24_segK 9 0 t (Nat.zero_le _) ht
        · simp only [ρj, h, ite_false] at ht; simp only [pv2, h, ite_false]
          exact hd 0 t (Nat.zero_le _) ht)
      (fun j hk i t h1 h2 => by
        subst hk
        by_cases h : i.val = 0
        · simp only [ρj, h, ite_true] at h1 h2; simp only [pv2, h, ite_true]
          exact p24_segK 9 (j + 1) t h1 h2
        · simp only [ρj, h, ite_false] at h1 h2; simp only [pv2, h, ite_false]
          exact hd (j + 1) t h1 h2)
    rwa [show (fun j => nt Oj 1 1 (e24 11 j) (Vph j)) = e24 12 from funext ntj] at this
  -- ua0
  have hWa : Win 1 1 (fun t => genF bd_c2 "u" .O ["a", "b", "q", "rst"]
      [Oj t, zA t, qpa t, rstW t]) Oa := fun t ht =>
    ⟨t - 1, by omega, by omega, by
      show Oa t = genF bd_c2 "u" .O ["a", "b", "q", "rst"]
        [Oj (t - 1), zA (t - 1), qpa (t - 1), rstW (t - 1)]
      rw [c2_gen, ua0_step t ht]; rfl⟩
  have hNa : NoRevertI 1 1 (fun t => genF bd_c2 "u" .O ["a", "b", "q", "rst"]
      [Oj t, zA t, qpa t, rstW t]) Oa :=
    noRevertI_shift (fun t ht => by
      show Oa t = genF bd_c2 "u" .O ["a", "b", "q", "rst"]
        [Oj (t - 1), zA (t - 1), qpa (t - 1), rstW (t - 1)]
      rw [c2_gen, ua0_step t ht]; rfl)
  have Ca := ua_cel (wl := 1) (wh := 1) hWa hNa (fun t ht => ⟨t - 1, by omega, by omega, rfl⟩) (Nat.le_refl 1)
  have gcz : ∀ j, gc κ (e8 14) j = 14 + 24 * (j / 2) + 4 * (j % 2) := fun j => by
    unfold gc κ e8; omega
  have nta : ∀ j, nt Oa 1 1 (max (e24 12 j) (gc κ (e8 14) j)) (Vph j) = e24 15 j := by
    intro j
    have hm : max (e24 12 j) (gc κ (e8 14) j) = 14 + 24 * (j / 2) + 4 * (j % 2) := by
      rw [gcz]; unfold e24; omega
    rw [hm, nt_eq Oa (Nat.le_refl 1)]
    · unfold e24; omega
    · show p24 15 _ = decide (j % 2 = 0)
      unfold p24; rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; omega
  have ha : ∀ k, SegK Oa (e24 15) k := by
    intro k
    have := muxa_segK (E := 1) (κ := κ) (ρ := e24 12) (ζ := e8 14) Ca (fun _ => rfl) (by decide) (by decide)
      (fun t h => by unfold Oa p24; simp; omega) (e8_inc 14) (fun m => by unfold κ; omega)
      (by rw [gcz]; unfold e24; omega)
      (fun j => by rw [nta]; unfold e24; omega)
      (fun j => by rw [nta]; unfold sN κ e8 e24; omega)
      (fun m h => by unfold κ e8 e24; unfold κ at h; omega)
      k (hj k) (fun k' _ => pw8_segK 14 k')
    rwa [show (fun j => nt Oa 1 1 (max (e24 12 j) (gc κ (e8 14) j)) (Vph j)) = e24 15 from
      funext nta] at this
  exact ⟨hd, Cj, hj, Ca, ha, ⟨by decide, by rw [Od_eq]; decide⟩, by decide, by decide,
    by decide⟩

/-! ### A FASTFALL stage of `bd_delay_gated` is not segment-causal -/

/-- The REAL stage LUT2 `4'h8` on `[s[i], gate]`. -/
def stg (a g : Bool) : Bool := Formal.Core.LutList.lutB 0x8 [a, g]
theorem stg_eq (a g : Bool) : stg a g = (a && g) := by cases a <;> cases g <;> decide

/-- Period-32 waves, high `w` ticks from `o`, and their edges. -/
def pq (o w t : Nat) : Bool := decide (o ≤ t ∧ (t - o) % 32 < w)
def eq32 (o w j : Nat) : Nat := o + 32 * (j / 2) + w * (j % 2)

theorem pq_segK (o w : Nat) (hw : 0 < w ∧ w < 32) (k : Nat) : SegK (pq o w) (eq32 o w) k := by
  match k with
  | 0 =>
    intro t _ ht
    show decide _ = false
    simp only [decide_eq_false_iff_not]; unfold eq32 at ht
    rw [show 0 % 2 = 0 from rfl, Nat.mul_zero] at ht; omega
  | j + 1 =>
    intro t h1 h2
    have h1' : eq32 o w j ≤ t := h1
    show decide _ = decide (j % 2 = 0)
    rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]; unfold eq32 at h1' h2
    rcases Nat.mod_two_eq_zero_or_one j with h | h
    · rw [h, Nat.mul_zero] at h1'
      rw [show (j + 1) % 2 = 1 by omega, Nat.mul_one, show (j + 1) / 2 = j / 2 by omega] at h2
      omega
    · rw [h, Nat.mul_one] at h1'
      rw [show (j + 1) % 2 = 0 by omega, Nat.mul_zero, show (j + 1) / 2 = j / 2 + 1 by omega] at h2
      omega

/-- The stage run: the gate pin (`|j` at the stage) high on `[32n+4, 32n+12)`; the data pin
`s[i]` high on `[32n+6, 32n+16)` (it rises after the gate, and, being an upstream stage reached
later by the flush or the `uor`/stage-0 buffers, falls after it); the stage (1 tick) high on
`[32n+7, 32n+13)`. -/
def gg : Nat → Bool := pq 4 8
def ag : Nat → Bool := pq 6 10
def Os (t : Nat) : Bool := if t = 0 then false else stg (ag (t - 1)) (gg (t - 1))
/-- The stage's excitation edges: rise at the later rise, fall at the EARLIER fall. -/
def xe : Nat → Nat := eq32 6 6
def es : Nat → Nat := eq32 7 6
/-- The data pin with a 1-tick dip at `t = 10`, inside its segment 1 and before the stage's
edge. -/
def ag' (t : Nat) : Bool := if t = 10 then false else ag t

theorem Os_eq (t : Nat) : Os t = pq 7 6 t := by
  unfold Os
  by_cases h0 : t = 0
  · subst h0; rfl
  · simp only [h0, ↓reduceIte]
    rw [stg_eq]; unfold ag gg pq
    rw [Bool.eq_iff_iff]; simp only [Bool.and_eq_true, decide_eq_true_eq]; omega

/-- **A FASTFALL stage is not segment-causal, in either direction** (the REAL LUT2 `4'h8`,
1 tick; on the run above every pin and the stage node are clean step signals):

* the stage's HIGH segment 1 needs the data pin high up to the stage's fall, i.e. the data
  pin's segment 1, which ends at `16`, after the stage's own node edge `13`: no dependency
  bound `nb` that includes it meets `net_closed_gen`'s H_WAIT (`gE + lo ≤ τ`, `lo = 1`);
* dropping it does not work: a data trace `ag'` equal to `ag` everywhere except a dip at
  `t = 10` (so equal on segment 0 and on every edge) gives an excitation that is NOT clean
  on segment 1.

So, as for the ORs, the stage's segment is a function of a PREFIX of a later-ending
segment; the end-ordered rule cannot discharge it with any `nb`. -/
theorem gstage_not_causal :
    Win 1 1 (fun t => stg (ag t) (gg t)) Os ∧
    (∀ k, SegK ag (eq32 6 10) k) ∧ (∀ k, SegK gg (eq32 4 8) k) ∧ (∀ k, SegK Os es k) ∧
    (∀ j, nt Os 1 1 (xe j) (Vph j) = es j) ∧
    eq32 6 10 1 = 16 ∧ es 1 = 13 ∧ ¬ (eq32 6 10 1 + 1 ≤ es 1) ∧
    (∀ t, t ≠ 10 → ag' t = ag t) ∧ (∀ t, t < eq32 6 10 0 → ag' t = ag t) ∧
    ¬ SegK (fun t => stg (ag' t) (gg t)) xe 1 := by
  have hW : Win 1 1 (fun t => stg (ag t) (gg t)) Os := fun t ht =>
    ⟨t - 1, by omega, by omega, by unfold Os; simp [show t ≠ 0 by omega]⟩
  refine ⟨hW, pq_segK 6 10 (by decide), pq_segK 4 8 (by decide), fun k => ?_, fun j => ?_,
    rfl, rfl, by decide, fun t h => by unfold ag'; simp [h],
    fun t h => by unfold ag'; unfold eq32 at h; simp [show t ≠ 10 by omega], fun h => ?_⟩
  · have := pq_segK 7 6 (by decide) k
    rwa [show pq 7 6 = Os from funext fun t => (Os_eq t).symm] at this
  · rw [nt_eq Os (Nat.le_refl 1)]
    · unfold xe es eq32; omega
    · rw [Os_eq]; unfold xe eq32 pq
      show decide _ = decide (j % 2 = 0)
      rw [Bool.eq_iff_iff]; simp only [decide_eq_true_eq]
      rcases Nat.mod_two_eq_zero_or_one j with h | h <;> rw [h] <;> omega
  · have := h 10 (by decide) (by decide)
    revert this; decide

end Wit

end Formal.Cells.AssumeGuaranteeMuxN
