import Formal.Cells.ContractsTrunc

/-!
# Probe G1, part 2: `bd_steer` as a causal cell (prefix up to `N` ⇒ outputs up to `N + d`)

Shard B, Phase 3. Notes: `formal/notes/B-contracts-trunc.md`.

`ContractsB.steer_contract` derives the steer's driven wires for the whole run
from its partners' wires for the whole run. Here the same gate model
(`OpsTimed.SteerGates`: the real INITs `0x8888888822222222` / `4'hE` through
`lutB`, every LUT and wire a FIFO bounded-delay arc) is re-run on PREFIXES:

* `steer_fwdN`: the sender's request a clean prefix up to `N` and the select
  bundled up to `N` ⇒ both branch requests (gated) are prefixes up to
  `N + dq + Lm` (`dq ≤ Wq.lo, Ws.lo`; `Lm ≤ L5.lo + W0.lo, L6.lo + W1.lo`);
* `steer_backN`: the receivers' acknowledges prefixes up to `N` and the
  `uack` pin skew up to `N` ⇒ the sender-side acknowledge is a prefix up to
  `N + Wm + La.lo + Wk.lo`;
* `steer_pinN`, `steer_skewN`: the event-form obligations (H_S_PIN,
  H_ACK_SKEW) are DERIVED up to `N` from the partners' causality up to `N`
  and the static obligations (S_S_SETUP with zero lead, S_S_HOLD to ack-fall,
  S_ACK), exactly as `OpsTimed2.steer_env_of_static` does for the whole run;
* `steer_step`: packaged in `ContractsTrunc`'s port halves: from the sender's
  `ReqUpTo` and the select window up to `N`, and the receivers' (gated, B-form)
  acknowledges and causality up to `N`, the steer's three driven halves follow:
  `AckUpTo` of its input channel up to `N + dB`, and `ReqUpTo` of each branch
  channel (re-indexed on the tokens routed to it) up to `N + dF`. This is the
  `step` hypothesis of `ContractsTrunc.ports_of_causal` for the steer's halves,
  with delay `dB` for its acknowledge half and `dF` for its two request halves
  (`steer_step_ports` states it on the port halves alone).
* `steer_sorder_closed`, `steer_ev_closed`: after the closure (whole-run
  facts), B's ordering and C's `SteerEv` follow as in `ContractsB`.

Every partner fact used at time `N` is itself a prefix fact up to `N`: no
partner's wire after `N` is used. This is what makes the steer's step
non-circular.

Named hypotheses (beyond `SteerGates`):
* `H_START`, `H_ER`, `H_ES ≥ 1`, `H_FWD_POS : 1 ≤ dq + Lm`, `H_BACK_POS :
  1 ≤ Wm + La.lo + Wk.lo`: positive minimum delays (prjxray SDF minima > 0).
* `H_QUIET_FWD`, `H_QUIET_ACK`: the steer-driven wires are low before the FIFO
  model's window opens (`T1 0`, `T2 0`): reset facts (`ResetGcd`).
* `H_FIRST_REQ : T1 0 ≤ ρ 0 + Wq.lo + Lm`, `H_FIRST_ACK : T2 0 ≤ ρ 0 + Wq.lo
  + Lm + Er + Wm + La.lo + Wk.lo`: the first request comes late enough after
  time 0 for the delay model to cover it (GLS: first req edge vs release).
* `S_SETUP0 : Ws.hi ≤ Wq.lo` (S_S_SETUP with the port's zero lead: the bus
  is only guaranteed from `ρ (2k)`), `S_HOLD_RT : Wq.hi ≤ Ws.lo + RT`
  (S_S_HOLD with the hold = the round trip to ack-fall), `S_ACK` as in
  `SteerStatic`.
-/

namespace Formal.Cells.Contracts
open Formal.Net Formal.Net.Handshake Formal.Net.Ops
open Formal.Cells.OpsTimed (Tok Enum rx rx_e rx_o rx_e2 rx_0 orEdges SteerRun SteerGates
  steer_K_ge steer_R_ge fst_order)
open Formal.Cells.PipeTimed (Ret)
open Formal.Cells.LibCtlMergeMux (steer_req0 steer_req1 or2_spec)

section steerN
variable {P : SteerRun}

/-! ## Elementary edge facts -/

theorem R0_ge {Lm : Nat} (hLm : Lm ≤ P.L5.lo + P.W0.lo) (j : Nat) (hρ : 1 ≤ P.ρ j) :
    P.ρ j + P.Wq.lo + Lm ≤ P.R0 j := by
  unfold SteerRun.R0 SteerRun.qr
  have a := P.Wq.fst_lo hρ
  have b := P.L5.fst_lo (c := P.Wq.fst (P.ρ j)) (by omega)
  have c := P.W0.fst_lo (c := P.L5.fst (P.Wq.fst (P.ρ j))) (by omega)
  omega

theorem R1_ge {Lm : Nat} (hLm : Lm ≤ P.L6.lo + P.W1.lo) (j : Nat) (hρ : 1 ≤ P.ρ j) :
    P.ρ j + P.Wq.lo + Lm ≤ P.R1 j := by
  unfold SteerRun.R1 SteerRun.qr
  have a := P.Wq.fst_lo hρ
  have b := P.L6.fst_lo (c := P.Wq.fst (P.ρ j)) (by omega)
  have c := P.W1.fst_lo (c := P.L6.fst (P.Wq.fst (P.ρ j))) (by omega)
  omega

theorem Rb_ge {Lm : Nat} (hLm : Lm ≤ P.L5.lo + P.W0.lo ∧ Lm ≤ P.L6.lo + P.W1.lo) (b : Bool)
    (j : Nat) (hρ : 1 ≤ P.ρ j) : P.ρ j + P.Wq.lo + Lm ≤ Rb P b j := by
  cases b
  · exact R0_ge hLm.1 j hρ
  · exact R1_ge hLm.2 j hρ

theorem Rb_mono (b : Bool) {x y : Nat} (h : P.ρ x ≤ P.ρ y) : Rb P b x ≤ Rb P b y := by
  have hq := fst_mono P.Wq h
  cases b
  · exact fst_mono P.W0 (fst_mono P.L5 hq)
  · exact fst_mono P.W1 (fst_mono P.L6 hq)

/-- The partners' causality up to `N` (the steer's own derived edges `Rsel`,
`K` are functions of `ρ`, `A`; only partner edges that happened by `N` are
constrained). -/
structure SteerCausalN (P : SteerRun) (N Er Es : Nat) : Prop where
  /-- **H_RCV_CAUSAL up to N** (receivers' `AckUpTo.ra`, with margin `Er`). -/
  H_RCV : ∀ j, P.A j ≤ N → P.Rsel j + Er ≤ P.A j
  /-- **H_SND_CAUSAL up to N** (sender's `ReqUpTo.ar`, with margin `Es`). -/
  H_SND : ∀ j, P.ρ (j + 1) ≤ N → P.K j + Es ≤ P.ρ (j + 1)
  /-- **H_START** (`ReqUpTo.start`). -/
  H_START : 1 ≤ P.ρ 0

variable {N Er Es Lm Wm : Nat}

theorem SteerCausalN.down (C : SteerCausalN P N Er Es) {N' : Nat} (h : N' ≤ N) :
    SteerCausalN P N' Er Es :=
  ⟨fun j hj => C.H_RCV j (by omega), fun j hj => C.H_SND j (by omega), C.H_START⟩

theorem SteerCausalN.ρpos (C : SteerCausalN P N Er Es) (H_ES : 1 ≤ Es) : ∀ j, 1 ≤ P.ρ j
  | 0 => C.H_START
  | j + 1 => by
    by_cases h : P.ρ (j + 1) ≤ N
    · have := C.H_SND j h; omega
    · omega

theorem SteerCausalN.Apos (C : SteerCausalN P N Er Es) (H_ER : 1 ≤ Er) (j : Nat) : 1 ≤ P.A j := by
  by_cases h : P.A j ≤ N
  · have := C.H_RCV j h; omega
  · omega

/-- Request edges that have happened by `N` increase. -/
theorem SteerCausalN.ρ_step (C : SteerCausalN P N Er Es) (H_ER : 1 ≤ Er) (H_ES : 1 ≤ Es)
    (hWm : Wm ≤ P.Wa0.lo ∧ Wm ≤ P.Wa1.lo) (hLm : Lm ≤ P.L5.lo + P.W0.lo ∧ Lm ≤ P.L6.lo + P.W1.lo)
    (j : Nat) (h : P.ρ (j + 1) ≤ N) : P.ρ j < P.ρ (j + 1) := by
  have h1 := C.H_SND j h
  have h2 := steer_K_ge Wm hWm j (C.Apos H_ER j)
  have h3 := C.H_RCV j (by omega)
  have h4 := steer_R_ge Lm hLm j (C.ρpos H_ES j)
  omega

theorem SteerCausalN.ρ_mono (C : SteerCausalN P N Er Es) (H_ER : 1 ≤ Er) (H_ES : 1 ≤ Es)
    (hWm : Wm ≤ P.Wa0.lo ∧ Wm ≤ P.Wa1.lo) (hLm : Lm ≤ P.L5.lo + P.W0.lo ∧ Lm ≤ P.L6.lo + P.W1.lo) :
    ∀ a b, a ≤ b → P.ρ b ≤ N → P.ρ a ≤ P.ρ b := by
  intro a b hab
  induction b with
  | zero => intro _; have : a = 0 := by omega
            subst this; omega
  | succ b ih =>
    intro hb
    have := C.ρ_step H_ER H_ES hWm hLm b hb
    by_cases h : a ≤ b
    · have := ih h (by omega); omega
    · have : a = b + 1 := by omega
      subst this; omega

/-! ## The event-form obligations, derived up to `N` -/

/-- **H_S_PIN up to `N + dq`** (from the select window at the sender up to
`N`: `s = sv k` on `[ρ (2k), K (2k+1))`, the port's H_BUNDLE window). -/
theorem steer_pinN {su s : Trace} (Ws : Ret) {dq : Nat} (C : SteerCausalN P N Er Es)
    (H_ER : 1 ≤ Er) (H_ES : 1 ≤ Es)
    (hWm : Wm ≤ P.Wa0.lo ∧ Wm ≤ P.Wa1.lo) (hLm : Lm ≤ P.L5.lo + P.W0.lo ∧ Lm ≤ P.L6.lo + P.W1.lo)
    (hdq : dq ≤ Ws.lo)
    (hw : ∀ t, Ws.hi ≤ t → su t = s (Ws.σ t))
    (hsel : ∀ k t, t ≤ N → P.ρ (2 * k) ≤ t → t < P.K (2 * k + 1) → s t = P.sv k)
    (S_SETUP0 : Ws.hi ≤ P.Wq.lo)
    (S_HOLD_RT : P.Wq.hi ≤ Ws.lo + (P.Wq.lo + Lm + Er + Wm + P.La.lo + P.Wk.lo)) :
    ∀ k t, t ≤ N + dq → P.qr (2 * k) ≤ t → t < P.qr (2 * k + 1) → su t = P.sv k := by
  intro k t hN h1 h2
  have p0 := C.ρpos H_ES (2 * k); have p1 := C.ρpos H_ES (2 * k + 1)
  unfold SteerRun.qr at h1 h2
  have a1 := P.Wq.fst_lo p0
  have a2 := P.Wq.fst_le (P.ρ (2 * k + 1))
  have b1 := Ws.ge t; have b2 := Ws.le t
  rw [hw t (by omega)]
  apply hsel k _ (by omega) (by omega)
  have hK := steer_K_ge Wm hWm (2 * k + 1) (C.Apos H_ER (2 * k + 1))
  by_cases hA : P.A (2 * k + 1) ≤ N
  · have := C.H_RCV (2 * k + 1) hA
    have := steer_R_ge Lm hLm (2 * k + 1) p1
    omega
  · omega

/-- **H_ACK_SKEW up to `N + Wm`** (from the causality up to `N` and S_ACK). -/
theorem steer_skewN (C : SteerCausalN P N Er Es) (H_ER : 1 ≤ Er) (H_ES : 1 ≤ Es)
    (hWm : Wm ≤ P.Wa0.lo ∧ Wm ≤ P.Wa1.lo) (hLm : Lm ≤ P.L5.lo + P.W0.lo ∧ Lm ≤ P.L6.lo + P.W1.lo)
    (S_ACK : P.Wa0.hi ≤ (Wm + P.La.lo + P.Wk.lo + Es + P.Wq.lo + Lm + Er) + P.Wa1.lo ∧
      P.Wa1.hi ≤ (Wm + P.La.lo + P.Wk.lo + Es + P.Wq.lo + Lm + Er) + P.Wa0.lo) :
    (∀ j, P.Wa1.fst (P.A (j + 1)) ≤ N + Wm → P.Wa0.fst (P.A j) ≤ P.Wa1.fst (P.A (j + 1))) ∧
    (∀ j, P.Wa0.fst (P.A (j + 1)) ≤ N + Wm → P.Wa1.fst (P.A j) ≤ P.Wa0.fst (P.A (j + 1))) := by
  have gap : ∀ j, P.A (j + 1) ≤ N →
      P.A j + (Wm + P.La.lo + P.Wk.lo + Es + P.Wq.lo + Lm + Er) ≤ P.A (j + 1) := by
    intro j hA
    have h1 := C.H_RCV (j + 1) hA
    have h2 := steer_R_ge Lm hLm (j + 1) (C.ρpos H_ES (j + 1))
    have h3 := C.H_SND j (by omega)
    have h4 := steer_K_ge Wm hWm j (C.Apos H_ER j)
    omega
  have hA1 := fun j => C.Apos H_ER (j + 1)
  constructor
  · intro j hj
    have := P.Wa1.fst_lo (hA1 j)
    have g := gap j (by omega)
    exact fst_order P.Wa0 P.Wa1 (hA1 j) (by omega)
  · intro j hj
    have := P.Wa0.fst_lo (hA1 j)
    have g := gap j (by omega)
    exact fst_order P.Wa1 P.Wa0 (hA1 j) (by omega)

/-! ## The two halves of the steer, prefix form -/

variable {req rqu su o5 o6 r0 r1 a0 a1 a0u a1u ao ack : Trace}

/-- **Forward half, prefix form.** -/
theorem steer_fwdN {dq : Nat} (G : SteerGates P req rqu su o5 o6 r0 r1 a0 a1 a0u a1u ao ack)
    (hreq : TokN 0 N req P.ρ (fun _ => true)) (hdq : dq ≤ P.Wq.lo)
    (hLm : Lm ≤ P.L5.lo + P.W0.lo ∧ Lm ≤ P.L6.lo + P.W1.lo)
    (hs : ∀ k t, t ≤ N + dq → P.qr (2 * k) ≤ t → t < P.qr (2 * k + 1) → su t = P.sv k) :
    TokN (P.T1 0) (N + dq + Lm) r0 P.R0 (fun k => !P.sv k) ∧
    TokN (P.T1 0) (N + dq + Lm) r1 P.R1 P.sv := by
  have hq := (hreq.fifo P.Wq G.H_WQ).down (N' := N + dq) (by omega)
  have g0 := hq.gate (fun a b => a && !b) (fun _ => rfl) (s := su) (sv := P.sv)
    (fun k t _ hN h1 h2 => hs k t hN h1 h2)
  have g1 := hq.gate (fun a b => a && b) (fun _ => rfl) (s := su) (sv := P.sv)
    (fun k t _ hN h1 h2 => hs k t hN h1 h2)
  have o5t := g0.fifo P.L5 (y := o5) (fun t ht => by rw [G.H_U5 t ht, steer_req0])
  have o6t := g1.fifo P.L6 (y := o6) (fun t ht => by rw [G.H_U6 t ht, steer_req1])
  have r0t := o5t.fifo P.W0 G.H_W0
  have r1t := o6t.fifo P.W1 G.H_W1
  constructor
  · exact (r0t.mono (T' := P.T1 0) (by unfold SteerRun.T1; omega)).down (by omega)
  · exact (r1t.mono (T' := P.T1 0) (by unfold SteerRun.T1; omega)).down (by omega)

/-- **Backward half, prefix form.** -/
theorem steer_backN (G : SteerGates P req rqu su o5 o6 r0 r1 a0 a1 a0u a1u ao ack)
    (hWm : Wm ≤ P.Wa0.lo ∧ Wm ≤ P.Wa1.lo)
    (h0 : TokN 0 N a0 P.A (fun k => !P.sv k)) (h1 : TokN 0 N a1 P.A P.sv)
    (hsk : (∀ j, P.Wa1.fst (P.A (j + 1)) ≤ N + Wm → P.Wa0.fst (P.A j) ≤ P.Wa1.fst (P.A (j + 1))) ∧
      (∀ j, P.Wa0.fst (P.A (j + 1)) ≤ N + Wm → P.Wa1.fst (P.A j) ≤ P.Wa0.fst (P.A (j + 1)))) :
    TokN (P.T2 0) (N + Wm + P.La.lo + P.Wk.lo) ack P.K (fun _ => true) := by
  have p0 := ((h0.fifo P.Wa0 G.H_WA0).mono (T' := P.Wa0.hi + P.Wa1.hi) (by omega)).down
    (N' := N + Wm) (by omega)
  have p1 := ((h1.fifo P.Wa1 G.H_WA1).mono (T' := P.Wa0.hi + P.Wa1.hi) (by omega)).down
    (N' := N + Wm) (by omega)
  have p1' : TokN (P.Wa0.hi + P.Wa1.hi) (N + Wm) a1u (fun j => P.Wa1.fst (P.A j))
      (fun k => !(!P.sv k)) := by simpa using p1
  have o := TokN.or_tok p0 p1' hsk.1 hsk.2
  have ot := o.fifo P.La (y := ao) (fun t ht => by rw [G.H_UA t ht, or2_spec])
  have kt := (ot.fifo P.Wk G.H_WK).congr (e' := P.K) (fun j => rfl)
  exact kt.mono (by unfold SteerRun.T2; omega)

/-! ## The steer as a causal cell on port halves -/

/-- **The steer's causal step.** Inputs, all up to `N`: the sender's request
half `ReqUpTo cin ρ K N` (so `Es = 1`), the select at the sender's driver
inside the port's bus window, the receivers' acknowledges (B's gated form on
the common sequence `A`) and their causality. Outputs: the steer's
acknowledge half of the input channel up to `N + dB`, and the request half of
each branch channel (re-indexed on its tokens) up to `N + dF`. -/
theorem steer_step {dq Er : Nat} {s : Trace} (Ws : Ret)
    (G : SteerGates P req rqu su o5 o6 r0 r1 a0 a1 a0u a1u ao ack)
    (hw : ∀ t, Ws.hi ≤ t → su t = s (Ws.σ t))
    {cin : Chan} (hcr : cin.req = req) (hca : cin.ack = ack)
    (hrq : ReqUpTo cin P.ρ P.K N)
    (hsel : ∀ k t, t ≤ N → P.ρ (2 * k) ≤ t → t < P.K (2 * k + 1) → s t = P.sv k)
    (h0 : TokN 0 N a0 P.A (fun k => !P.sv k)) (h1 : TokN 0 N a1 P.A P.sv)
    (H_RCV : ∀ j, P.A j ≤ N → P.Rsel j + Er ≤ P.A j)
    (H_ER : 1 ≤ Er) (hdq : dq ≤ P.Wq.lo ∧ dq ≤ Ws.lo)
    (hLm : Lm ≤ P.L5.lo + P.W0.lo ∧ Lm ≤ P.L6.lo + P.W1.lo) (hWm : Wm ≤ P.Wa0.lo ∧ Wm ≤ P.Wa1.lo)
    (S_SETUP0 : Ws.hi ≤ P.Wq.lo)
    (S_HOLD_RT : P.Wq.hi ≤ Ws.lo + (P.Wq.lo + Lm + Er + Wm + P.La.lo + P.Wk.lo))
    (S_ACK : P.Wa0.hi ≤ (Wm + P.La.lo + P.Wk.lo + 1 + P.Wq.lo + Lm + Er) + P.Wa1.lo ∧
      P.Wa1.hi ≤ (Wm + P.La.lo + P.Wk.lo + 1 + P.Wq.lo + Lm + Er) + P.Wa0.lo)
    (H_QUIET_FWD : ∀ t, t < P.T1 0 → r0 t = false ∧ r1 t = false)
    (H_QUIET_ACK : ∀ t, t < P.T2 0 → ack t = false)
    (H_FIRST_REQ : P.T1 0 ≤ P.ρ 0 + P.Wq.lo + Lm)
    (H_FIRST_ACK : P.T2 0 ≤ P.ρ 0 + P.Wq.lo + Lm + Er + Wm + P.La.lo + P.Wk.lo)
    (κ : Bool → Nat → Nat) (hE0 : Enum (fun k => !P.sv k) (κ false)) (hE1 : Enum P.sv (κ true))
    {cout : Bool → Chan} (hor : ∀ b, (cout b).req = if b then r1 else r0) :
    AckUpTo cin P.ρ P.K (N + Wm + P.La.lo + P.Wk.lo) ∧
    ∀ b, ReqUpTo (cout b) (rx (Rb P b) (κ b)) (rx P.A (κ b)) (N + dq + Lm) := by
  have C : SteerCausalN P N Er 1 :=
    ⟨H_RCV, fun j hj => by have := hrq.ar j hj; omega, hrq.start⟩
  have hreq : TokN 0 N req P.ρ (fun _ => true) := by rw [← hcr]; exact hrq.req
  have ρpos := C.ρpos (Nat.le_refl 1)
  have ρmono := C.ρ_mono H_ER (Nat.le_refl 1) hWm hLm
  have hpin := steer_pinN Ws C H_ER (Nat.le_refl 1) hWm hLm hdq.2 hw hsel S_SETUP0 S_HOLD_RT
  have hsk := steer_skewN C H_ER (Nat.le_refl 1) hWm hLm S_ACK
  have back := steer_backN G hWm h0 h1 hsk
  obtain ⟨f0, f1⟩ := steer_fwdN G hreq hdq.1 hLm hpin
  have Kge : ∀ j, P.A j + Wm + P.La.lo + P.Wk.lo ≤ P.K j :=
    fun j => steer_K_ge Wm hWm j (C.Apos H_ER j)
  refine ⟨⟨?_, fun j hj => ?_⟩, fun b => ?_⟩
  · -- the acknowledge half of the input channel
    rw [hca]
    refine back.from0 H_QUIET_ACK (fun h => ?_) (fun j hj => ?_)
    · have := Kge 0
      have := H_RCV 0 (by omega)
      have := steer_R_ge Lm hLm 0 (ρpos 0)
      omega
    · -- K is monotone on the edges that have happened by `N + dB`
      have hA := Kge j
      have h3 := H_RCV j (by omega)
      have h4 := steer_R_ge Lm hLm j (ρpos j)
      rcases Nat.eq_zero_or_pos j with h | h
      · subst h; omega
      · have := ρmono 1 j h (by omega)
        have : P.K 0 < P.ρ 1 := hrq.ar 0 (show P.ρ 1 ≤ N by omega)
        omega
  · -- causality of the acknowledge: `ρ j < K j`
    have := Kge j
    have := H_RCV j (by omega)
    have := steer_R_ge Lm hLm j (ρpos j)
    omega
  · -- the request half of branch `b`
    have hE : Enum (if b then P.sv else fun k => !P.sv k) (κ b) := by cases b <;> assumption
    have fb : TokN (P.T1 0) (N + dq + Lm) (if b then r1 else r0) (Rb P b)
        (if b then P.sv else fun k => !P.sv k) := by cases b <;> assumption
    have hroute : ∀ m, P.sv (κ b m) = b := fun m => by
      cases b
      · have := hE0.hit m; simpa using this
      · exact hE1.hit m
    have Rge := fun j => Rb_ge hLm b j (ρpos j)
    have Rmono : ∀ x y, x ≤ y → P.ρ y ≤ N → Rb P b x ≤ Rb P b y :=
      fun x y h hy => Rb_mono b (ρmono x y h hy)
    refine ⟨?_, ?_, fun j hj => ?_⟩
    · rw [hor b]
      refine (fb.reindex hE).from0 (fun t ht => by
          cases b
          · exact (H_QUIET_FWD t ht).1
          · exact (H_QUIET_FWD t ht).2) (fun h => ?_) (fun j hj => ?_)
      · rw [rx_0] at h ⊢
        have := Rge (2 * κ b 0)
        have := ρmono 0 (2 * κ b 0) (Nat.zero_le _) (by omega)
        omega
      · rw [rx_0]
        unfold rx at hj ⊢
        have := Rge (2 * κ b (j / 2) + j % 2)
        have hk := hE.le_of_le (Nat.zero_le (j / 2))
        exact Rmono _ _ (by omega) (by omega)
    · rw [rx_0]; have := Rge (2 * κ b 0); have := ρpos (2 * κ b 0); omega
    · -- next request on the branch only after the branch's acknowledge
      rcases Nat.mod_two_eq_zero_or_one j with hj2 | hj2
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m := ⟨j / 2, by omega⟩
        rw [rx_o] at hj ⊢; rw [rx_e]
        have := Rge (2 * κ b m + 1)
        have hρ1 : P.ρ (2 * κ b m + 1) ≤ N := by omega
        have := hrq.ar (2 * κ b m) hρ1
        have := Kge (2 * κ b m)
        omega
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m + 1 := ⟨j / 2, by omega⟩
        rw [show 2 * m + 1 + 1 = 2 * m + 2 by omega, rx_e2] at hj ⊢; rw [rx_o]
        have := Rge (2 * κ b (m + 1))
        have hm := hE.mono m
        have hρ2 : P.ρ (2 * κ b (m + 1)) ≤ N := by omega
        have := ρmono (2 * κ b m + 2) (2 * κ b (m + 1)) (by omega) hρ2
        have : P.K (2 * κ b m + 1) < P.ρ (2 * κ b m + 2) := hrq.ar (2 * κ b m + 1) (show P.ρ (2 * κ b m + 2) ≤ N by omega)
        have := Kge (2 * κ b m + 1)
        omega

/-! ## After the closure: whole-run ordering and C's `SteerEv` -/

/-- With the closure's whole-run facts (the receivers' causality and the
sender's "next request after ack" at every `N`), B's whole-run ordering
`SOrder P Er 1` holds. -/
theorem steer_sorder_closed {Er : Nat} (hLm : Lm ≤ P.L5.lo + P.W0.lo ∧ Lm ≤ P.L6.lo + P.W1.lo)
    (hWm : Wm ≤ P.Wa0.lo ∧ Wm ≤ P.Wa1.lo) (H_ER : 1 ≤ Er)
    (H_RCV : ∀ j, P.Rsel j + Er ≤ P.A j) (H_SND : ∀ j, P.K j < P.ρ (j + 1))
    (H_START : 1 ≤ P.ρ 0) : SOrder P Er 1 := by
  have hpos : ∀ j, 1 ≤ P.ρ j := fun j => by
    cases j with
    | zero => exact H_START
    | succ j => have := H_SND j; omega
  intro j
  have := steer_R_ge Lm hLm j (hpos j)
  have := H_RCV j
  have := steer_K_ge Wm hWm j (by omega)
  have := H_SND j
  omega

/-- **C's `SteerEv` after the closure** (`ContractsB.steer_ev` with `Es = 1`). -/
theorem steer_ev_closed {C : Type} {ρ v : C → Nat → Nat} {sel : Nat → Bool} {f : Nat → Nat}
    {cj : C} {cout : Bool → C} {Er : Nat}
    (hLm : Lm ≤ P.L5.lo + P.W0.lo ∧ Lm ≤ P.L6.lo + P.W1.lo) (hWm : Wm ≤ P.Wa0.lo ∧ Wm ≤ P.Wa1.lo)
    (H_ER : 1 ≤ Er) (H_RCV : ∀ j, P.Rsel j + Er ≤ P.A j) (H_SND : ∀ j, P.K j < P.ρ (j + 1))
    (H_START : 1 ≤ P.ρ 0) (H_FWD_POS : 1 ≤ P.Wq.lo + Lm)
    (κ : Bool → Nat → Nat) (hE0 : Enum (fun k => !P.sv k) (κ false)) (hE1 : Enum P.sv (κ true))
    (hρj : ρ cj = P.ρ) (hρo : ∀ b, ρ (cout b) = rx (Rb P b) (κ b))
    (H_SEL_VAL : ∀ i, P.sv i = sel (v cj i))
    (H_STEER_DATA : ∀ b m, v (cout b) m = f (v cj (κ b m))) :
    SteerEv ρ v sel f cj cout := by
  have hO := steer_sorder_closed hLm hWm H_ER H_RCV H_SND H_START
  have hpos : ∀ j, 1 ≤ P.ρ j := fun j => by
    cases j with
    | zero => exact H_START
    | succ j => have := H_SND j; omega
  exact steer_ev hO (Nat.le_refl 1) hLm H_FWD_POS hpos κ hE0 hE1 hρj hρo H_SEL_VAL H_STEER_DATA

/-- The select window from the port's bus half: if the select at the
sender's driver is `sel` of the bus and token `k`'s select is `sel` of its
value, `DatUpTo` gives `steer_step`'s `hsel`. -/
theorem sel_of_dat {cin : Chan} {v : Nat → Nat} {sel : Nat → Bool} {s : Trace}
    (hd : DatUpTo cin P.ρ P.K v N) (H_SEL_WIRE : ∀ t, s t = sel (cin.dat t))
    (H_SEL_VAL : ∀ k, P.sv k = sel (v k)) :
    ∀ k t, t ≤ N → P.ρ (2 * k) ≤ t → t < P.K (2 * k + 1) → s t = P.sv k := by
  intro k t h1 h2 h3
  rw [H_SEL_WIRE, hd k t h1 h2 h3, H_SEL_VAL]

/-! ## The steer's step from port halves only

`steer_step` still takes the receivers' acknowledges in B's gated form on the
common sequence `A`. Here they are derived from the branch channels' own
`AckUpTo` (re-indexed edges `rx A κ_b`), with `TokN.lift`; the receivers'
causality is their `AckUpTo.ra` (so `Er = 1`). The result is the steer's step
stated on `ContractsTrunc`'s port halves alone. -/

/-- The branch channels' acknowledge halves give B's receiver causality up to
`N` (`Er = 1`). -/
theorem rcv_of_branches {κ : Bool → Nat → Nat} (hE0 : Enum (fun k => !P.sv k) (κ false))
    (hE1 : Enum P.sv (κ true)) {cout : Bool → Chan}
    (hak : ∀ b, AckUpTo (cout b) (rx (Rb P b) (κ b)) (rx P.A (κ b)) N) :
    ∀ j, P.A j ≤ N → P.Rsel j + 1 ≤ P.A j := by
  intro j hj
  have hrx : ∀ (e : Nat → Nat) b m, κ b m = j / 2 → rx e (κ b) (2 * m + j % 2) = e j := by
    intro e b m hm
    unfold rx
    rw [show (2 * m + j % 2) / 2 = m by omega, show (2 * m + j % 2) % 2 = j % 2 by omega, hm,
      show 2 * (j / 2) + j % 2 = j by omega]
  unfold SteerRun.Rsel
  cases hb : P.sv (j / 2)
  · obtain ⟨m, hm⟩ := hE0.all (j / 2) (by simp [hb])
    have := (hak false).ra (2 * m + j % 2) (by rw [hrx _ false m hm]; exact hj)
    rw [hrx _ false m hm, hrx _ false m hm] at this
    exact this
  · obtain ⟨m, hm⟩ := hE1.all (j / 2) hb
    have := (hak true).ra (2 * m + j % 2) (by rw [hrx _ true m hm]; exact hj)
    rw [hrx _ true m hm, hrx _ true m hm] at this
    exact this

/-- The common acknowledge sequence is monotone on the edges that have
happened by `N`. -/
theorem SteerCausalN.A_mono (C : SteerCausalN P N 1 1)
    (hWm : Wm ≤ P.Wa0.lo ∧ Wm ≤ P.Wa1.lo) (hLm : Lm ≤ P.L5.lo + P.W0.lo ∧ Lm ≤ P.L6.lo + P.W1.lo) :
    ∀ a b, a ≤ b → P.A b ≤ N → P.A a ≤ P.A b := by
  have step : ∀ j, P.A (j + 1) ≤ N → P.A j < P.A (j + 1) := fun j hj => by
    have h1 := C.H_RCV (j + 1) hj
    have h2 := steer_R_ge Lm hLm (j + 1) (C.ρpos (Nat.le_refl 1) (j + 1))
    have h3 := C.H_SND j (by omega)
    have h4 := steer_K_ge Wm hWm j (C.Apos (Nat.le_refl 1) j)
    omega
  intro a b hab
  induction b with
  | zero => intro _; have : a = 0 := by omega
            subst this; omega
  | succ b ih =>
    intro hb
    have := step b hb
    by_cases h : a ≤ b
    · have := ih h (by omega); omega
    · have : a = b + 1 := by omega
      subst this; omega

/-- **The steer's causal step on port halves.** Inputs, all up to `N`, are
exactly the halves the steer's partners drive: the sender's `ReqUpTo` and
`DatUpTo` of the input channel (the select is `sel` of the bus), and each
receiver's `AckUpTo` of its branch channel. Outputs are exactly the halves
the steer drives: `AckUpTo` of the input channel up to `N + dB` and
`ReqUpTo` of each branch channel up to `N + dF`
(`dF = dq + Lm`, `dB = Wm + La.lo + Wk.lo`). The branch BUS halves
(`DatUpTo` of the branch channels) are not the steer's: the data wire runs
beside `bd_steer` (C's H_STEER_DATA). -/
theorem steer_step_ports {dq : Nat} {s : Trace} (Ws : Ret)
    (G : SteerGates P req rqu su o5 o6 r0 r1 a0 a1 a0u a1u ao ack)
    (hw : ∀ t, Ws.hi ≤ t → su t = s (Ws.σ t))
    {cin : Chan} {v : Nat → Nat} {sel : Nat → Bool}
    (hcr : cin.req = req) (hca : cin.ack = ack)
    (hrq : ReqUpTo cin P.ρ P.K N) (hdt : DatUpTo cin P.ρ P.K v N)
    (H_SEL_WIRE : ∀ t, s t = sel (cin.dat t)) (H_SEL_VAL : ∀ k, P.sv k = sel (v k))
    (κ : Bool → Nat → Nat) (hE0 : Enum (fun k => !P.sv k) (κ false)) (hE1 : Enum P.sv (κ true))
    {cout : Bool → Chan} (hor : ∀ b, (cout b).req = if b then r1 else r0)
    (hoa : ∀ b, (cout b).ack = if b then a1 else a0)
    (hak : ∀ b, AckUpTo (cout b) (rx (Rb P b) (κ b)) (rx P.A (κ b)) N)
    (hdq : dq ≤ P.Wq.lo ∧ dq ≤ Ws.lo)
    (hLm : Lm ≤ P.L5.lo + P.W0.lo ∧ Lm ≤ P.L6.lo + P.W1.lo) (hWm : Wm ≤ P.Wa0.lo ∧ Wm ≤ P.Wa1.lo)
    (S_SETUP0 : Ws.hi ≤ P.Wq.lo)
    (S_HOLD_RT : P.Wq.hi ≤ Ws.lo + (P.Wq.lo + Lm + 1 + Wm + P.La.lo + P.Wk.lo))
    (S_ACK : P.Wa0.hi ≤ (Wm + P.La.lo + P.Wk.lo + 1 + P.Wq.lo + Lm + 1) + P.Wa1.lo ∧
      P.Wa1.hi ≤ (Wm + P.La.lo + P.Wk.lo + 1 + P.Wq.lo + Lm + 1) + P.Wa0.lo)
    (H_QUIET_FWD : ∀ t, t < P.T1 0 → r0 t = false ∧ r1 t = false)
    (H_QUIET_ACK : ∀ t, t < P.T2 0 → ack t = false)
    (H_FIRST_REQ : P.T1 0 ≤ P.ρ 0 + P.Wq.lo + Lm)
    (H_FIRST_ACK : P.T2 0 ≤ P.ρ 0 + P.Wq.lo + Lm + 1 + Wm + P.La.lo + P.Wk.lo) :
    AckUpTo cin P.ρ P.K (N + Wm + P.La.lo + P.Wk.lo) ∧
    ∀ b, ReqUpTo (cout b) (rx (Rb P b) (κ b)) (rx P.A (κ b)) (N + dq + Lm) := by
  have H_RCV := rcv_of_branches hE0 hE1 hak
  have C : SteerCausalN P N 1 1 :=
    ⟨H_RCV, fun j hj => by have := hrq.ar j hj; omega, hrq.start⟩
  have Am := C.A_mono hWm hLm
  have h0 : TokN 0 N a0 P.A (fun k => !P.sv k) := by
    have := (hak false).ack; rw [hoa false] at this; exact this.lift hE0 Am
  have h1 : TokN 0 N a1 P.A P.sv := by
    have := (hak true).ack; rw [hoa true] at this; exact this.lift hE1 Am
  exact steer_step Ws G hw hcr hca hrq (sel_of_dat hdt H_SEL_WIRE H_SEL_VAL) h0 h1 H_RCV
    (Nat.le_refl 1) hdq hLm hWm S_SETUP0 S_HOLD_RT S_ACK H_QUIET_FWD H_QUIET_ACK H_FIRST_REQ
    H_FIRST_ACK κ hE0 hE1 hor

end steerN

end Formal.Cells.Contracts
