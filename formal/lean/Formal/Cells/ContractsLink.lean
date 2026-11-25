import Formal.Cells.ContractsB
import Formal.Cells.OpsHold
import Formal.Cells.PipePerPin

/-!
# Probe G5b: the link / pipe contract in C's interface

Shard B, Phase 3, gap G5 of `B-contracts.md` for `bd_link` and `bd_pipe`.
In the style of `ContractsB.steer_contract`: B's timed theorems
(`LinkTimed.stage_forward`, `PipeTimedN.pipe_forward`,
`PipePerPin.pipe_forward`) are turned into `Port` facts on the input and
output channels and C's `LinkEv` (each output token's value is the input
token's, offered strictly after it), hence C's `OpSpec … (linkEq ci co)`.

## Observation points (the G2 convention used here)

Every channel is observed at its CONSUMER's pins:
* `req` and `dat` at the receiver's request pin and data (D) pins;
* `ack` at the sender's acknowledge pin.
Each cell owns its OUTPUT wires: a link owns `req_out` up to the receiver's
request pin, the `data_out` wires up to the receiver's D pins, and `ack_in`
up to the sender's acknowledge pin. With this convention the request and
acknowledge pins the link's own controller reads (I0 = `req_in`, I1 =
`ack_out`) are exactly the observation points of the partners' wires, so
`LinkTimed.CtlEnv`'s pin traces ARE the ports' `req_in` and `ack_out`, and
nothing is counted twice.

## The link-owned wires

* `LinkTimed` (one stage, non-FIFO controller): the node may glitch inside
  its transition windows, so the cleanness of the link-driven wires at the
  partners' pins cannot be derived; it is a named hypothesis (`H_ROUT`,
  `H_AIN`: clean four-phase trace; `H_ROUT_LATE`, `H_AIN_LATE`: each edge
  no earlier than the node's earliest edge plus the wire's minimum). This is
  LinkTimed's open row 4.
* `PipeTimedN` / `PipePerPin` (N stages, FIFO controller / per-pin LUT):
  the nodes are proved clean (`nodes_clean`), so the end wires are DERIVED to
  be clean four-phase traces from a FIFO read-time map (`fifo_tok`).

## `H_X_LEAD` (req_out leads data_out)

At the link's own pins `req_out` leads `data_out` (bd_link.v: one latch
arc). The output port's data window starts at the request edge AT THE
RECEIVER'S PIN, so the request wire (wire + DELAY) must be slower than the
enable-branch + latch arc + data wire. `LinkLead` states this as two
inequalities over routed delays (the enable path and the data-through path);
`link_x_lead` proves it suffices, and in the same form it discharges
`OpsTimed2`'s `H_X_LEAD` for a link sender of a mux. For a pipe it is one
integer inequality on the last stage's data lateness `Dl`.
-/

namespace Formal.Cells.ContractsLink
open Formal.Net Formal.Net.Handshake Formal.Net.Ops
open Formal.Cells.Contracts
open Formal.Cells.OpsTimed (Tok)
open Formal.Cells.LinkTimed (CtlEnv DataPath cph Vph Vph_e Vph_o par_cases)
open Formal.Cells.PipeTimed (Ret fifo_hold)
open Formal.Net.Ops.Link (linkEq)

/-! ## 1. Generic helpers -/

/-- Interleave two event sequences: `ilv a b (2k) = a k`, `ilv a b (2k+1) = b k`. -/
def ilv (a b : Nat → Nat) (j : Nat) : Nat := if j % 2 = 0 then a (j / 2) else b (j / 2)

theorem ilv_e (a b : Nat → Nat) (k : Nat) : ilv a b (2 * k) = a k := by
  simp only [ilv, show 2 * k % 2 = 0 by omega, show 2 * k / 2 = k by omega, ↓reduceIte]

theorem ilv_o (a b : Nat → Nat) (k : Nat) : ilv a b (2 * k + 1) = b k := by
  simp only [ilv, show (2 * k + 1) % 2 = 1 by omega, show (2 * k + 1) / 2 = k by omega]; rfl

theorem ilv_e2 (a b : Nat → Nat) (k : Nat) : ilv a b (2 * k + 2) = a (k + 1) := by
  rw [show 2 * k + 2 = 2 * (k + 1) by omega, ilv_e]

theorem ilv_zero (a b : Nat → Nat) : ilv a b 0 = a 0 := by
  have := ilv_e a b 0; simpa using this

/-- A wire with explicit rise times `a k` and fall times `b k` is a clean
four-phase `Tok` from time 0 on the interleaved edges. -/
theorem tok_ilv {x : Nat → Bool} {a b : Nat → Nat}
    (h0 : ∀ t, t < a 0 → x t = false)
    (h1 : ∀ k t, a k ≤ t → t < b k → x t = true)
    (h2 : ∀ k t, b k ≤ t → t < a (k + 1) → x t = false) :
    Tok 0 x (ilv a b) (fun _ => true) := by
  refine ⟨fun t _ h => h0 t (by rw [ilv_zero] at h; exact h), fun k t _ ha hb => ?_,
    fun k t _ ha hb => ?_⟩
  · rw [ilv_e] at ha; rw [ilv_o] at hb; exact h1 k t ha hb
  · rw [ilv_o] at ha; rw [ilv_e2] at hb; exact h2 k t ha hb

/-- A wire that is low before `e 0` and shows `Vph j` between consecutive
edges is a clean four-phase `Tok` from time 0. -/
theorem tok_vph {x : Nat → Bool} {e : Nat → Nat}
    (h0 : ∀ t, t < e 0 → x t = false)
    (h : ∀ j t, e j ≤ t → t < e (j + 1) → x t = Vph j) : Tok 0 x e (fun _ => true) :=
  ⟨fun t _ h1 => h0 t h1, fun k t _ h1 h2 => by rw [h (2 * k) t h1 h2, Vph_e],
   fun k t _ h1 h2 => by
    rw [h (2 * k + 1) t h1 (by rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega]; exact h2), Vph_o]⟩

/-- **A window wire passes a stable stretch** (5b's `WinDelay [lo, hi]`, non-FIFO
allowed): stable on `[a, c)` at the driver gives stable on `[a + hi, c + lo)`
at the far pin. Used for the data wires `q i → receiver D pin`. -/
theorem win_stable {lo hi : Nat} {q x : Nat → Bool} (hw : CElemTiming.WinDelay lo hi q x)
    {a c : Nat} {v : Bool} (hs : ∀ t, a ≤ t → t < c → q t = v) :
    ∀ t, a + hi ≤ t → t < c + lo → x t = v := by
  intro t h1 h2
  obtain ⟨s, hs1, hs2, hs3⟩ := hw t (by omega)
  rw [hs3]; exact hs s (by omega) (by omega)

/-- **A FIFO wire from a clean node is a clean wire.** If the node `x` is low
on `[h0, τ 0)` and shows `Vph j` on `[τ j, τ (j+1))`, the far end `y` of a
FIFO read-time map `Wr` (flushed by the first edge: `Wr.hi ≤ τ j`) is a clean
four-phase `Tok` from 0 on the edges `Wr.fst (τ j)`, given that it is quiet
(reset) before `Q`. -/
theorem fifo_tok {x y : Nat → Bool} (Wr : Ret) {τ : Nat → Nat} {h0 Q : Nat}
    (hpre : ∀ t, h0 ≤ t → t < τ 0 → x t = false)
    (hph : ∀ j t, τ j ≤ t → t < τ (j + 1) → x t = Vph j)
    (hy : ∀ t, Wr.hi ≤ t → y t = x (Wr.σ t))
    (hτ : ∀ j, Wr.hi ≤ τ j) (hQ : Wr.hi ≤ Q ∧ Wr.fst h0 ≤ Q)
    (H_QUIET : ∀ t, t < Q → y t = false) :
    Tok 0 y (fun j => Wr.fst (τ j)) (fun _ => true) := by
  refine tok_vph (fun t ht => ?_) (fun j t h1 h2 => ?_)
  · by_cases hq : t < Q
    · exact H_QUIET t hq
    · exact fifo_hold Wr hy hpre t (by omega) ht (by omega)
  · have := hτ j; have := Wr.fst_ge (τ j)
    exact fifo_hold Wr hy (hph j) t h1 h2 (by omega)

/-- The channel value of a `W`-bit bus (bit `i` weighs `2^i`). Only its
congruence is used: the value depends only on the `W` bits. -/
def busVal : Nat → (Nat → Bool) → Nat
  | 0, _ => 0
  | n + 1, b => busVal n b + (if b n then 2 ^ n else 0)

theorem busVal_congr : ∀ (n : Nat) (b b' : Nat → Bool), (∀ i, i < n → b i = b' i) →
    busVal n b = busVal n b'
  | 0, _, _, _ => rfl
  | n + 1, b, b', h => by
    simp only [busVal]; rw [busVal_congr n b b' (fun i hi => h i (by omega)), h n (by omega)]

/-! ## 2. `H_X_LEAD`: the request wire must outlast the latch arc -/

/-- **H_X_LEAD (link sender), as an obligation over routed delays.** `M` is the
lead the consumer needs at its pin (the data wire's maximum `xhi` for C's
port; `Lx` for `OpsTimed2`'s mux contract). `rlo` is the minimum of the
request path from the link's node to the consumer's request pin (wire +
`DELAY` chain + wire).
* **H_X_LEAD_EN** (enable path): the slowest node edge + enable branch of
  this bit + `M` arrives no later than the fastest request:
  `dlmax + ehi i + M ≤ dlmin + rlo`.
* **H_X_LEAD_D** (data-through path, a transparent latch passing late input
  data): `dhi i + Lag + M ≤ Sdr + dlmin + rlo`.
This is skew.py rule E / tighten.py rule I at a link output (B-ops-hold:
"needs a DELAY / request-wire obligation"); no rule checks it at a link
output today. GLS test: at the consumer, the data pins settle before the
request pin rises, per token, at both corners. -/
structure LinkLead (dlmin dlmax rlo ehi dhi Sdr Lag M : Nat) : Prop where
  H_X_LEAD_EN : dlmax + ehi + M ≤ dlmin + rlo
  H_X_LEAD_D : dhi + Lag + M ≤ Sdr + dlmin + rlo

section link
variable {req ack rst O qp : Nat → Bool} {ρ φ α β : Nat → Nat}
  {dlmin dlmax dwmin dwmax E t0 : Nat}
  {d q : Nat → Bundling.Sig} {val : Nat → Nat → Bool} {dS dE : Nat → Nat}
  {dlo dhi elo ehi flo fhi : Nat → Nat} {W Erel Sdr Lag : Nat}

theorem rho_le_cph (ρ φ α β : Nat → Nat) (k : Nat) : ρ k ≤ cph ρ φ α β (2 * k) := by
  rw [LinkTimed.cph_e]; exact Nat.le_max_left _ _

theorem phi_le_cph (ρ φ α β : Nat → Nat) (k : Nat) : φ k ≤ cph ρ φ α β (2 * k + 1) := by
  rw [LinkTimed.cph_o]; exact Nat.le_max_left _ _

theorem alpha_le_cph (ρ φ α β : Nat → Nat) (k : Nat) : α k ≤ cph ρ φ α β (2 * k + 1) := by
  rw [LinkTimed.cph_o]; exact Nat.le_max_right _ _

theorem beta_le_cph (ρ φ α β : Nat → Nat) (k : Nat) : β k ≤ cph ρ φ α β (2 * k + 2) := by
  rw [show 2 * k + 2 = 2 * k + 1 + 1 by omega, LinkTimed.cph_e1]; exact Nat.le_max_right _ _

theorem rho0_pos (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0) : 0 < ρ 0 := by
  have h1 := C.H_RST_EARLY; have h2 := C.H_CTL.H_LOOP_POS
  have h3 := CElemTiming.winDelay_le C.H_CTL.H_LUT; have h4 := CElemTiming.winDelay_le C.H_CTL.H_FB
  omega

/-- **`H_X_LEAD` suffices.** If the consumer's request pin sees token `m`'s
request no earlier than `cph(2m) + dlmin + rlo`, then under `LinkLead … M` the
link's latch bit `i` is valid (from `stage_token`'s start
`max (cph(2m)+dlmax+ehi i) (dS m + dhi i)`) at least `M` before that request.
With `ξ = P.ξ`, `M = Lx` and `xS m` the left-hand max, this is exactly
`OpsTimed2.MuxDataEnv.H_X_LEAD` for a link sender (the half `link_x_sender`
in OpsHold left open). -/
theorem link_x_lead
    (D : DataPath O d q val dS dE dlo dhi elo ehi flo fhi W ρ φ α β dlmin dlmax E Erel Sdr Lag)
    (i : Nat) {rlo M : Nat} (ξ : Nat → Nat)
    (hξ : ∀ m, cph ρ φ α β (2 * m) + dlmin + rlo ≤ ξ (2 * m))
    (HL : LinkLead dlmin dlmax rlo (ehi i) (dhi i) Sdr Lag M) :
    ∀ m, max (cph ρ φ α β (2 * m) + dlmax + ehi i) (dS m + dhi i) + M ≤ ξ (2 * m) := by
  intro m
  have h1 := hξ m; have h2 := D.H_DATA_LEAD m; have h3 := rho_le_cph ρ φ α β m
  have h4 := HL.H_X_LEAD_EN; have h5 := HL.H_X_LEAD_D
  omega

/-- **Input port of a `bd_link`.** The request half is `CtlEnv`'s pin trace
(`H_REQ_*`), the acknowledge half is the link-owned `ack_in` wire at the
sender's pin. Interleaving: the "after its cause" inequalities are DERIVED
(the node moves after its phase start); the "before the partner's next
move" inequalities are the sender's own pin-level causality (`H_SND_PIN`).
The data half is the sender's, from `DataPath.H_DATA_VALID` with:
* `H_IN_LEAD`: the data at the link's D pins is valid by the request rise
  at its I0 pin (for a link sender: its `H_X_LEAD`);
* `H_SND_HOLDF`: the sender holds until its own ack pin has fallen
  (B-ops-hold's hold-to-fall contract; `link_hold_fall` for a link sender). -/
theorem link_in_port (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0)
    (D : DataPath O d q val dS dE dlo dhi elo ehi flo fhi W ρ φ α β dlmin dlmax E Erel Sdr Lag)
    {ain : Nat → Bool} {αi : Nat → Nat} {alo : Nat}
    (H_AIN : Tok 0 ain αi (fun _ => true))
    (H_AIN_LATE : ∀ j, cph ρ φ α β j + dlmin + alo ≤ αi j)
    (H_ALO_POS : 1 ≤ dlmin + alo)
    (H_SND_PIN : ∀ k, αi (2 * k) < φ k ∧ αi (2 * k + 1) < ρ (k + 1))
    (H_IN_LEAD : ∀ k, dS k ≤ ρ k)
    (H_SND_HOLDF : ∀ k, αi (2 * k + 1) ≤ dE k) :
    Port ⟨req, ain, fun t => busVal W (fun i => d i t)⟩ (ilv ρ φ) αi (fun k => busVal W (val k)) := by
  refine ⟨tok_ilv C.H_REQ_LOW0 C.H_REQ_HIGH C.H_REQ_LOW, H_AIN, ?_, ?_, ?_, ?_⟩
  · rw [ilv_zero]; exact rho0_pos C
  · refine par_cases (fun j => ilv ρ φ j < αi j) (fun k => ?_) (fun k => ?_)
    · show ilv ρ φ (2 * k) < αi (2 * k)
      rw [ilv_e]; have := H_AIN_LATE (2 * k); have := rho_le_cph ρ φ α β k
      omega
    · show ilv ρ φ (2 * k + 1) < αi (2 * k + 1)
      rw [ilv_o]; have := H_AIN_LATE (2 * k + 1); have := phi_le_cph ρ φ α β k
      omega
  · refine par_cases (fun j => αi j < ilv ρ φ (j + 1)) (fun k => ?_) (fun k => ?_)
    · show αi (2 * k) < ilv ρ φ (2 * k + 1)
      rw [ilv_o]; exact (H_SND_PIN k).1
    · show αi (2 * k + 1) < ilv ρ φ (2 * k + 1 + 1)
      rw [show 2 * k + 1 + 1 = 2 * k + 2 by omega, ilv_e2]; exact (H_SND_PIN k).2
  · intro k t h1 h2
    rw [ilv_e] at h1
    show busVal W (fun i => d i t) = busVal W (val k)
    apply busVal_congr
    intro i hi
    have := H_IN_LEAD k; have := H_SND_HOLDF k
    exact D.H_DATA_VALID k i t hi (by omega) (by omega)

/-- **Output of a `bd_link`: bits at the receiver's D pins, and the output
port.** The data bits are `stage_forward` (valid until the receiver's ack
falls, `β k`) through the data wire (`H_DWIRE`, a window wire), started at the
receiver's request edge by `H_X_LEAD` (`LinkLead … (xhi i)`). The request half
is the link-owned `req_out` wire at the receiver's pin; the acknowledge half
is `CtlEnv`'s I1 trace (`H_ACK_*`). -/
theorem link_out_port (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0)
    (D : DataPath O d q val dS dE dlo dhi elo ehi flo fhi W ρ φ α β dlmin dlmax E Erel Sdr Lag)
    {rout : Nat → Bool} {ρo : Nat → Nat} {rlo : Nat}
    (H_ROUT : Tok 0 rout ρo (fun _ => true))
    (H_ROUT_LATE : ∀ j, cph ρ φ α β j + dlmin + rlo ≤ ρo j)
    (H_RLO_POS : 1 ≤ dlmin + rlo)
    (H_RCV_PIN : ∀ k, ρo (2 * k) < α k ∧ ρo (2 * k + 1) < β k)
    {xpin : Nat → Nat → Bool} {xlo xhi : Nat → Nat}
    (H_DWIRE : ∀ i, i < W → CElemTiming.WinDelay (xlo i) (xhi i) (q i) (xpin i))
    (H_LEAD : ∀ i, i < W → LinkLead dlmin dlmax rlo (ehi i) (dhi i) Sdr Lag (xhi i)) :
    (∀ k i t, i < W → ρo (2 * k) ≤ t → t < β k → xpin i t = val k i) ∧
    Port ⟨rout, ack, fun t => busVal W (fun i => xpin i t)⟩ ρo (ilv α β)
      (fun k => busVal W (val k)) := by
  have bits : ∀ k i t, i < W → ρo (2 * k) ≤ t → t < β k → xpin i t = val k i := by
    intro k i t hi h1 h2
    have hl := link_x_lead D i ρo (fun m => H_ROUT_LATE (2 * m)) (H_LEAD i hi) k
    exact win_stable (H_DWIRE i hi) ((LinkTimed.stage_forward C D k i hi).1) t (by omega) (by omega)
  refine ⟨bits, H_ROUT, tok_ilv C.H_ACK_LOW0 C.H_ACK_HIGH C.H_ACK_LOW, ?_, ?_, ?_, ?_⟩
  · have := H_ROUT_LATE 0; omega
  · refine par_cases (fun j => ρo j < ilv α β j) (fun k => ?_) (fun k => ?_)
    · show ρo (2 * k) < ilv α β (2 * k)
      rw [ilv_e]; exact (H_RCV_PIN k).1
    · show ρo (2 * k + 1) < ilv α β (2 * k + 1)
      rw [ilv_o]; exact (H_RCV_PIN k).2
  · refine par_cases (fun j => ilv α β j < ρo (j + 1)) (fun k => ?_) (fun k => ?_)
    · show ilv α β (2 * k) < ρo (2 * k + 1)
      rw [ilv_e]; have := H_ROUT_LATE (2 * k + 1); have := alpha_le_cph ρ φ α β k
      omega
    · show ilv α β (2 * k + 1) < ρo (2 * k + 1 + 1)
      rw [ilv_o, show 2 * k + 1 + 1 = 2 * k + 2 by omega]
      have := H_ROUT_LATE (2 * k + 2); have := beta_le_cph ρ φ α β k
      omega
  · intro k t h1 h2
    rw [ilv_o] at h2
    show busVal W (fun i => xpin i t) = busVal W (val k)
    exact busVal_congr W _ _ fun i hi => bits k i t hi h1 h2

/-- **C's `LinkEv` from the link's request lower bound.** Token `k` reaches
the receiver's request pin strictly after it reached the link's I0 pin
(`ρ k ≤ cph (2k)`, plus `dlmin + rlo ≥ 1`), and carries the same value. -/
theorem link_ev {rlo : Nat} {ρo : Nat → Nat}
    (H_ROUT_LATE : ∀ j, cph ρ φ α β j + dlmin + rlo ≤ ρo j) (H_RLO_POS : 1 ≤ dlmin + rlo)
    {Ch : Type} {ρC vC : Ch → Nat → Nat} {ci co : Ch}
    (hρi : ρC ci = ilv ρ φ) (hρo : ρC co = ρo)
    (hvi : ∀ k, vC ci k = busVal W (val k)) (hvo : ∀ k, vC co k = busVal W (val k)) :
    LinkEv ρC vC ci co := by
  refine ⟨fun k => ?_, fun k => by rw [hvo, hvi]⟩
  rw [hρi, hρo, ilv_e]
  have := H_ROUT_LATE (2 * k); have := rho_le_cph ρ φ α β k
  omega

/-- **The packaged `bd_link` contract (C's interface, from LinkTimed).**
From exactly LinkTimed's stage contract (`CtlEnv`, `DataPath`), the
link-owned output wires (`H_ROUT*`, `H_AIN*`, `H_DWIRE`), the H_X_LEAD
obligation (`H_LEAD`), and the partners' pin-level facts (`H_SND_PIN`,
`H_RCV_PIN`, `H_IN_LEAD`, `H_SND_HOLDF`):
1. the input channel is a `Port` (request edges `ρ, φ` interleaved);
2. the output channel is a `Port` (acknowledge edges `α, β` interleaved);
3. every output bit at the receiver's D pins is the latched token's bit on
   `[ρo (2k), β k)` (bit-level form, which is what a downstream link's
   `DataPath.H_DATA_VALID` consumes, with `dS = ρo ∘ 2·`, `dE = β`);
4. C's `LinkEv` for any channel map identifying the two ports. -/
theorem link_contract (C : CtlEnv req ack rst O qp ρ φ α β dlmin dlmax dwmin dwmax E t0)
    (D : DataPath O d q val dS dE dlo dhi elo ehi flo fhi W ρ φ α β dlmin dlmax E Erel Sdr Lag)
    {ain rout : Nat → Bool} {αi ρo : Nat → Nat} {alo rlo : Nat}
    (H_AIN : Tok 0 ain αi (fun _ => true))
    (H_AIN_LATE : ∀ j, cph ρ φ α β j + dlmin + alo ≤ αi j) (H_ALO_POS : 1 ≤ dlmin + alo)
    (H_ROUT : Tok 0 rout ρo (fun _ => true))
    (H_ROUT_LATE : ∀ j, cph ρ φ α β j + dlmin + rlo ≤ ρo j) (H_RLO_POS : 1 ≤ dlmin + rlo)
    {xpin : Nat → Nat → Bool} {xlo xhi : Nat → Nat}
    (H_DWIRE : ∀ i, i < W → CElemTiming.WinDelay (xlo i) (xhi i) (q i) (xpin i))
    (H_LEAD : ∀ i, i < W → LinkLead dlmin dlmax rlo (ehi i) (dhi i) Sdr Lag (xhi i))
    (H_SND_PIN : ∀ k, αi (2 * k) < φ k ∧ αi (2 * k + 1) < ρ (k + 1))
    (H_RCV_PIN : ∀ k, ρo (2 * k) < α k ∧ ρo (2 * k + 1) < β k)
    (H_IN_LEAD : ∀ k, dS k ≤ ρ k) (H_SND_HOLDF : ∀ k, αi (2 * k + 1) ≤ dE k)
    {Ch : Type} {ρC vC : Ch → Nat → Nat} {ci co : Ch}
    (hρi : ρC ci = ilv ρ φ) (hρo : ρC co = ρo)
    (hvi : ∀ k, vC ci k = busVal W (val k)) (hvo : ∀ k, vC co k = busVal W (val k)) :
    Port ⟨req, ain, fun t => busVal W (fun i => d i t)⟩ (ilv ρ φ) αi (fun k => busVal W (val k)) ∧
    Port ⟨rout, ack, fun t => busVal W (fun i => xpin i t)⟩ ρo (ilv α β)
      (fun k => busVal W (val k)) ∧
    (∀ k i t, i < W → ρo (2 * k) ≤ t → t < β k → xpin i t = val k i) ∧
    LinkEv ρC vC ci co :=
  ⟨link_in_port C D H_AIN H_AIN_LATE H_ALO_POS H_SND_PIN H_IN_LEAD H_SND_HOLDF,
   (link_out_port C D H_ROUT H_ROUT_LATE H_RLO_POS H_RCV_PIN H_DWIRE H_LEAD).2,
   (link_out_port C D H_ROUT H_ROUT_LATE H_RLO_POS H_RCV_PIN H_DWIRE H_LEAD).1,
   link_ev (W := W) (val := val) H_ROUT_LATE H_RLO_POS hρi hρo hvi hvo⟩

/-- **To C's `OpSpec`.** With every channel of the network a port (`Pall`,
the G1 caveat of `B-contracts.md` applies), `link_contract`'s `LinkEv` gives
C's `OpProto ∧ OpData (linkEq ci co)`. -/
theorem link_opSpec {Ch : Type} {ch : Ch → Chan} {ρC αC vC : Ch → Nat → Nat} {ci co : Ch}
    (Pall : ∀ c, Port (ch c) (ρC c) (αC c) (vC c)) (L : LinkEv ρC vC ci co) :
    OpSpec ch [ci] [co] (linkEq ci co) := link_spec Pall L

end link

/-! ## 3. The N-stage pipe: a generic port theorem

`PipeIO` collects what both N-stage models (6f `PipeTimedN`, FIFO
controllers; 6g `PipePerPin`, per-pin LUTs) prove about the pipe's two ends:
first and last node clean, ordering against the environment, every token
delivered. `pipe_ports` turns that into the two `Port`s. -/

/-- The end-to-end facts of an N-stage pipe (all DERIVED in 6f and 6g). -/
structure PipeIO (W : Nat) (ρ γ τ0 τL : Nat → Nat) (Renv Tf h0 hL : Nat)
    (O0 OL r0 aN : Nat → Bool) (xL : Nat → Bundling.Sig) (val : Nat → Nat → Bool)
    (Sx : Nat → Nat → Nat) : Prop where
  pre0 : ∀ t, h0 ≤ t → t < τ0 0 → O0 t = false
  ph0 : ∀ j t, τ0 j ≤ t → t < τ0 (j + 1) → O0 t = Vph j
  preL : ∀ t, hL ≤ t → t < τL 0 → OL t = false
  phL : ∀ j t, τL j ≤ t → t < τL (j + 1) → OL t = Vph j
  in_lt : ∀ j, ρ j < τ0 j
  out_lt : ∀ j, γ j < τL (j + 1)
  thru : ∀ j, τ0 j ≤ τL j
  flush0 : ∀ j, Tf ≤ τ0 j
  flushL : ∀ j, Tf ≤ τL j
  env_pos : 1 ≤ Renv
  env_first : Renv ≤ ρ 0
  req_low0 : ∀ t, Renv ≤ t → t < ρ 0 → r0 t = false
  req_ph : ∀ j t, ρ j ≤ t → t < ρ (j + 1) → r0 t = Vph j
  ack_low0 : ∀ t, Renv ≤ t → t < γ 0 → aN t = false
  ack_ph : ∀ j t, γ j ≤ t → t < γ (j + 1) → aN t = Vph j
  deliver : ∀ k b t, b < W → Sx k b ≤ t → t < γ (2 * k + 1) → xL b t = val k b

/-- **Generic N-stage pipe ports.** Named hypotheses beyond `PipeIO`:
* `H_AIN_LINE`, `H_ROUT_LINE`: the pipe-owned end wires (stage 0's node →
  sender's ack pin, last node → receiver's request pin, including DACK /
  DELAY) are FIFO read-time maps `Wa`, `Wr` (the same assumption as 6f's
  internal lines); `H_WIRE_FLUSH`: both have flushed their power-up value by
  the first node edge;
* `H_QUIET_*`: the four end wires are low from power-up (reset; `ResetGcd`);
* `H_SND_PIN`, `H_RCV_PIN`: the partners' own pin-level causality (a partner
  moves only after it has seen the pipe's edge at its pin);
* `H_IN_LEAD`, `H_SND_HOLDF`: the sender's data at stage 0's D pins is valid
  from its request rise to its ack-pin fall;
* `H_DWIRE`: the output data wires are window wires;
* `H_X_LEAD`: the last stage's data is valid `xhi` before the receiver's
  request edge (model-specific form derived in `pipe_contract*`). -/
theorem pipe_ports {W : Nat} {ρ γ τ0 τL : Nat → Nat} {Renv Tf h0 hL : Nat}
    {O0 OL r0 aN : Nat → Bool} {xL : Nat → Bundling.Sig} {val : Nat → Nat → Bool}
    {Sx : Nat → Nat → Nat} (I : PipeIO W ρ γ τ0 τL Renv Tf h0 hL O0 OL r0 aN xL val Sx)
    {ain rout : Nat → Bool} (Wa Wr : Ret)
    (H_AIN_LINE : ∀ t, Wa.hi ≤ t → ain t = O0 (Wa.σ t))
    (H_ROUT_LINE : ∀ t, Wr.hi ≤ t → rout t = OL (Wr.σ t))
    (H_WIRE_FLUSH : Wa.hi ≤ Tf ∧ Wr.hi ≤ Tf)
    {Qa Qr : Nat} (H_QA : Wa.hi ≤ Qa ∧ Wa.fst h0 ≤ Qa) (H_QR : Wr.hi ≤ Qr ∧ Wr.fst hL ≤ Qr)
    (H_QUIET_AIN : ∀ t, t < Qa → ain t = false) (H_QUIET_ROUT : ∀ t, t < Qr → rout t = false)
    (H_QUIET_REQ : ∀ t, t < Renv → r0 t = false) (H_QUIET_ACK : ∀ t, t < Renv → aN t = false)
    (H_SND_PIN : ∀ j, Wa.fst (τ0 j) < ρ (j + 1))
    (H_RCV_PIN : ∀ j, Wr.fst (τL j) < γ j)
    {d : Nat → Bundling.Sig} {dS dE : Nat → Nat}
    (H_DATA_VALID : ∀ k b t, b < W → dS k ≤ t → t < dE k → d b t = val k b)
    (H_IN_LEAD : ∀ k, dS k ≤ ρ (2 * k))
    (H_SND_HOLDF : ∀ k, Wa.fst (τ0 (2 * k + 1)) ≤ dE k)
    {xpin : Nat → Nat → Bool} {xlo xhi : Nat → Nat}
    (H_DWIRE : ∀ b, b < W → CElemTiming.WinDelay (xlo b) (xhi b) (xL b) (xpin b))
    (H_X_LEAD : ∀ k b, b < W → Sx k b + xhi b ≤ Wr.fst (τL (2 * k))) :
    Port ⟨r0, ain, fun t => busVal W (fun b => d b t)⟩ ρ (fun j => Wa.fst (τ0 j))
      (fun k => busVal W (val k)) ∧
    Port ⟨rout, aN, fun t => busVal W (fun b => xpin b t)⟩ (fun j => Wr.fst (τL j)) γ
      (fun k => busVal W (val k)) ∧
    (∀ k b t, b < W → Wr.fst (τL (2 * k)) ≤ t → t < γ (2 * k + 1) → xpin b t = val k b) ∧
    (∀ k, ρ (2 * k) < Wr.fst (τL (2 * k))) := by
  have bits : ∀ k b t, b < W → Wr.fst (τL (2 * k)) ≤ t → t < γ (2 * k + 1) → xpin b t = val k b := by
    intro k b t hb h1 h2
    have := H_X_LEAD k b hb
    exact win_stable (H_DWIRE b hb) (I.deliver k b · hb) t (by omega) (by omega)
  refine ⟨⟨tok_vph (fun t ht => ?_) I.req_ph,
      fifo_tok Wa I.pre0 I.ph0 H_AIN_LINE (fun j => by have := I.flush0 j; omega) H_QA H_QUIET_AIN,
      by have := I.env_pos; have := I.env_first; omega,
      fun j => by have := I.in_lt j; have := Wa.fst_ge (τ0 j); omega,
      H_SND_PIN, fun k t h1 h2 => ?_⟩,
    ⟨fifo_tok Wr I.preL I.phL H_ROUT_LINE (fun j => by have := I.flushL j; omega) H_QR H_QUIET_ROUT,
      tok_vph (fun t ht => ?_) I.ack_ph,
      by have := I.in_lt 0; have := I.thru 0; have := Wr.fst_ge (τL 0); omega,
      H_RCV_PIN, fun j => by have := I.out_lt j; have := Wr.fst_ge (τL (j + 1)); omega,
      fun k t h1 h2 => ?_⟩, bits, fun k => ?_⟩
  · by_cases hq : t < Renv
    · exact H_QUIET_REQ t hq
    · exact I.req_low0 t (by omega) ht
  · show busVal W (fun b => d b t) = busVal W (val k)
    exact busVal_congr W _ _ fun b hb => by
      have := H_IN_LEAD k; have := H_SND_HOLDF k
      exact H_DATA_VALID k b t hb (by omega) (by omega)
  · by_cases hq : t < Renv
    · exact H_QUIET_ACK t hq
    · exact I.ack_low0 t (by omega) ht
  · show busVal W (fun b => xpin b t) = busVal W (val k)
    exact busVal_congr W _ _ fun b hb => bits k b t hb h1 h2
  · have := I.in_lt (2 * k); have := I.thru (2 * k); have := Wr.fst_ge (τL (2 * k)); omega

/-- `LinkEv` for a pipe from `pipe_ports`'s last conjunct. -/
theorem pipe_ev {W : Nat} {val : Nat → Nat → Bool} {ρ : Nat → Nat} {ρo : Nat → Nat}
    (hc : ∀ k, ρ (2 * k) < ρo (2 * k))
    {Ch : Type} {ρC vC : Ch → Nat → Nat} {ci co : Ch}
    (hρi : ρC ci = ρ) (hρo : ρC co = ρo)
    (hvi : ∀ k, vC ci k = busVal W (val k)) (hvo : ∀ k, vC co k = busVal W (val k)) :
    LinkEv ρC vC ci co :=
  ⟨fun k => by rw [hρi, hρo]; exact hc k, fun k => by rw [hvo, hvi]⟩

/-! ## 4. 6f `PipeTimedN` (FIFO controllers) -/

section pipeN
open Formal.Cells.PipeTimedN
variable {P : PN} {rst : Nat → Bool} {r a O q : Nat → Nat → Bool} {wl wh : Nat → Nat} {Es Er : Nat}
  {d : Nat → Bundling.Sig} {x : Nat → Nat → Bundling.Sig} {val : Nat → Nat → Bool}
  {dS dE : Nat → Nat} {V : Nat → PipeTimed.Win} {W Erel Sdr Lag : Nat}

theorem tau_thru_N (E : EnvN P (r 0) (a (P.N - 1)) Es Er) (T : TimingN P wh Es Er) (j : Nat) :
    ∀ i, P.τ 0 j ≤ P.τ i j := by
  intro i; induction i with
  | zero => exact Nat.le_refl _
  | succ i ih => have := fwd E T i j; omega

/-- 6f's theorems give `PipeIO` (with `H_LUT_POS`: every controller LUT has a
positive minimum delay, true of every prjxray LUT arc). -/
theorem pipe_io_N (G : GatesN P rst r a O q wl wh) (E : EnvN P (r 0) (a (P.N - 1)) Es Er)
    (T : TimingN P wh Es Er) (D : DataN P O d x val dS dE V W Es Er Erel Sdr Lag)
    (H_LUT_POS : ∀ i, i < P.N → 1 ≤ (P.L i).lo) :
    PipeIO W P.ρ P.γ (P.τ 0) (P.τ (P.N - 1)) P.R P.R (P.L 0).hi (P.L (P.N - 1)).hi
      (O 0) (O (P.N - 1)) (r 0) (a (P.N - 1)) (x (P.N - 1)) val
      (fun k b => P.Sx V dS k b (P.N - 1)) := by
  have hN := T.H_N_POS
  have c0 := nodes_clean G E T 0 (by omega)
  have cL := nodes_clean G E T (P.N - 1) (by omega)
  have l0 := H_LUT_POS 0 (by omega); have lL := H_LUT_POS (P.N - 1) (by omega)
  exact {
    pre0 := c0.1, ph0 := c0.2, preL := cL.1, phL := cL.2
    in_lt := fun j => by have := rho_le E T j; omega
    out_lt := fun j => by have := gam_le E T j; omega
    thru := fun j => tau_thru_N E T j (P.N - 1)
    flush0 := fun j => by have := ge_R E j 0; have := tau_lo E T 0 j; omega
    flushL := fun j => by have := ge_R E j (P.N - 1); have := tau_lo E T (P.N - 1) j; omega
    env_pos := T.H_R_POS, env_first := E.H_RST_EARLY
    req_low0 := E.H_REQ_LOW0, req_ph := E.H_REQ
    ack_low0 := E.H_ACK_LOW0, ack_ph := E.H_ACK
    deliver := fun k b t hb h1 h2 => (pipe_forward G E T D k b hb).1 t h1 h2 }

/-- **The packaged `bd_pipe` contract (6f, FIFO controllers).** 6f's
hypotheses (`GatesN`, `EnvN`, `TimingN`, `DataN`) plus the end wires, the
partner pin facts and the output lead `H_X_LEAD_N`:

    Dl (N-1) b + xhi b ≤ Wr.lo        (in ℤ)

(the last stage's data lateness relative to its own rise, plus the output
data wire, is covered by the request line to the receiver; this is 6f's
`Dl ≤ Er` with the receiver's latency replaced by the request wire, i.e. the
lead is checked at the receiver's PIN). Conclusions: both `Port`s, the
bit-level delivery at the receiver's pins, and C's `LinkEv`. -/
theorem pipe_contract (G : GatesN P rst r a O q wl wh) (E : EnvN P (r 0) (a (P.N - 1)) Es Er)
    (T : TimingN P wh Es Er) (D : DataN P O d x val dS dE V W Es Er Erel Sdr Lag)
    (H_LUT_POS : ∀ i, i < P.N → 1 ≤ (P.L i).lo)
    {ain rout : Nat → Bool} (Wa Wr : Ret)
    (H_AIN_LINE : ∀ t, Wa.hi ≤ t → ain t = O 0 (Wa.σ t))
    (H_ROUT_LINE : ∀ t, Wr.hi ≤ t → rout t = O (P.N - 1) (Wr.σ t))
    (H_WIRE_FLUSH : Wa.hi ≤ P.R ∧ Wr.hi ≤ P.R)
    {Qa Qr : Nat} (H_QA : Wa.hi ≤ Qa ∧ Wa.fst (P.L 0).hi ≤ Qa)
    (H_QR : Wr.hi ≤ Qr ∧ Wr.fst (P.L (P.N - 1)).hi ≤ Qr)
    (H_QUIET_AIN : ∀ t, t < Qa → ain t = false) (H_QUIET_ROUT : ∀ t, t < Qr → rout t = false)
    (H_QUIET_REQ : ∀ t, t < P.R → r 0 t = false)
    (H_QUIET_ACK : ∀ t, t < P.R → a (P.N - 1) t = false)
    (H_SND_PIN : ∀ j, Wa.fst (P.τ 0 j) < P.ρ (j + 1))
    (H_RCV_PIN : ∀ j, Wr.fst (P.τ (P.N - 1) j) < P.γ j)
    (H_IN_LEAD : ∀ k, dS k ≤ P.ρ (2 * k))
    (H_SND_HOLDF : ∀ k, Wa.fst (P.τ 0 (2 * k + 1)) ≤ dE k)
    {xpin : Nat → Nat → Bool} {xlo xhi : Nat → Nat}
    (H_DWIRE : ∀ b, b < W → CElemTiming.WinDelay (xlo b) (xhi b) (x (P.N - 1) b) (xpin b))
    (H_X_LEAD_N : ∀ b, b < W → Dl P V Sdr Lag (P.N - 1) b + (xhi b : Int) ≤ (Wr.lo : Int))
    {Ch : Type} {ρC vC : Ch → Nat → Nat} {ci co : Ch}
    (hρi : ρC ci = P.ρ) (hρo : ρC co = fun j => Wr.fst (P.τ (P.N - 1) j))
    (hvi : ∀ k, vC ci k = busVal W (val k)) (hvo : ∀ k, vC co k = busVal W (val k)) :
    Port ⟨r 0, ain, fun t => busVal W (fun b => d b t)⟩ P.ρ (fun j => Wa.fst (P.τ 0 j))
      (fun k => busVal W (val k)) ∧
    Port ⟨rout, a (P.N - 1), fun t => busVal W (fun b => xpin b t)⟩
      (fun j => Wr.fst (P.τ (P.N - 1) j)) P.γ (fun k => busVal W (val k)) ∧
    (∀ k b t, b < W → Wr.fst (P.τ (P.N - 1) (2 * k)) ≤ t → t < P.γ (2 * k + 1) →
      xpin b t = val k b) ∧
    LinkEv ρC vC ci co := by
  have I := pipe_io_N G E T D H_LUT_POS
  have lead : ∀ k b, b < W → P.Sx V dS k b (P.N - 1) + xhi b ≤ Wr.fst (P.τ (P.N - 1) (2 * k)) := by
    intro k b hb
    have h1 := Sx_le (V := V) E T D.H_DATA_LEAD k b (P.N - 1)
    have h2 := H_X_LEAD_N b hb
    have h3 := Wr.fst_lo (tau_pos E T (P.N - 1) (2 * k))
    omega
  obtain ⟨p1, p2, p3, p4⟩ := pipe_ports I Wa Wr H_AIN_LINE H_ROUT_LINE H_WIRE_FLUSH H_QA H_QR
    H_QUIET_AIN H_QUIET_ROUT H_QUIET_REQ H_QUIET_ACK H_SND_PIN H_RCV_PIN
    (fun k b t hb h1 h2 => D.H_DATA_VALID k b t hb h1 h2) H_IN_LEAD H_SND_HOLDF H_DWIRE lead
  exact ⟨p1, p2, p3, pipe_ev p4 hρi hρo hvi hvo⟩

end pipeN


/-! ## 5b. Non-vacuity: 6f's unit-delay pipe witness meets `pipe_contract`

For every `N ≥ 1`, 6f's witness run (`PipeTimedN.Wit`: every arc one tick,
real `bd_c2n` INIT, real `ODD` latch INIT, one data bit with alternating
token values) plus end wires `Wa = shift 1` (stage 0's node to the sender's
ack pin), `Wr = shift 2` (last node to the receiver's request pin, one tick
of `DELAY`) and a one-tick data wire satisfies EVERY hypothesis of
`pipe_contract`, including `H_X_LEAD_N` (`Dl = 1`, `xhi = 1`, `Wr.lo = 2`:
tight) and the partners' pin facts. So the two `Port`s and C's `LinkEv` are
proved about a concrete live run. -/

namespace Wit
open Formal.Cells.PipeTimedN Formal.Cells.PipeTimedN.Wit Formal.Cells.PipeTimed.Wit

/-- Sender's ack pin: stage 0's node `sq 5` one tick later. -/
def ainW : Nat → Bool := sq 6
/-- Receiver's request pin: the last node `sq (3 + 2N)` two ticks later. -/
def routW (N : Nat) : Nat → Bool := sq (5 + 2 * N)
/-- Receiver's D pin: the last latch one tick later. -/
def xpinW (N : Nat) (_ : Nat) (t : Nat) : Bool := xW (N - 1) (t - 1)
/-- Channel map: `false` = input, `true` = output. -/
def ρCW (N : Nat) : Bool → Nat → Nat := fun c =>
  if c then (fun j => (Ret.shift 2).fst ((Pw N).τ ((Pw N).N - 1) j)) else (Pw N).ρ
def vCW : Bool → Nat → Nat := fun _ k => busVal 1 (valW k)

theorem pipe_witness (N : Nat) (hN : 1 ≤ N) :
    Port ⟨rW 0, ainW, fun t => busVal 1 (fun _ => dW t)⟩ (Pw N).ρ
      (fun j => (Ret.shift 1).fst ((Pw N).τ 0 j)) (fun k => busVal 1 (valW k)) ∧
    Port ⟨routW N, aW ((Pw N).N - 1), fun t => busVal 1 (fun b => xpinW N b t)⟩
      (fun j => (Ret.shift 2).fst ((Pw N).τ ((Pw N).N - 1) j)) (Pw N).γ
      (fun k => busVal 1 (valW k)) ∧
    LinkEv (ρCW N) vCW false true ∧
    busVal 1 (valW 0) ≠ busVal 1 (valW 1) := by
  obtain ⟨p1, p2, _, p4⟩ := pipe_contract (gates_w N) (env_w N hN) (timing_w N hN) (data_w N)
    (fun _ _ => by show 1 ≤ 1; exact Nat.le_refl 1)
    (ain := ainW) (rout := routW N) (Ret.shift 1) (Ret.shift 2)
    (fun t ht => by show sq (5 + 1) t = sq 5 (t - 1); exact sq1 5 t ht)
    (fun t ht => by
      show sq (5 + 2 * N) t = sq (5 + 2 * (N - 1)) (t - 2)
      have ht' : 2 ≤ t := ht
      have := sq_shift (5 + 2 * (N - 1)) 2 (t - 2)
      rw [show 5 + 2 * (N - 1) + 2 = 5 + 2 * N by omega, show t - 2 + 2 = t by omega] at this
      exact this)
    (by show 1 ≤ 4 ∧ 2 ≤ 4; decide)
    (Qa := 2) (Qr := 3)
    (by show 1 ≤ 2 ∧ (Ret.shift 1).fst 1 ≤ 2; rw [Ret.fst_shift 1 1 (by decide)]; decide)
    (by show 2 ≤ 3 ∧ (Ret.shift 2).fst 1 ≤ 3; rw [Ret.fst_shift 2 1 (by decide)]; decide)
    (fun t ht => sq_pre 6 t (by omega))
    (fun t ht => sq_pre _ t (by omega))
    (fun t ht => by show sq (4 + 2 * 0) t = false; have h4 : t < 4 := ht; exact sq_pre _ t (by omega))
    (fun t ht => by
      show sq (8 + 2 * (N - 1)) t = false
      have h4 : t < 4 := ht; exact sq_pre _ t (by omega))
    (fun j => by
      rw [τ_w, Ret.fst_shift 1 _ (by omega)]; show 5 + 2 * 0 + 4 * j + 1 < 4 + 4 * (j + 1); omega)
    (fun j => by
      rw [τ_w, Ret.fst_shift 2 _ (by omega)]
      show 5 + 2 * (N - 1) + 4 * j + 2 < 6 + 2 * N + 4 * j; omega)
    (fun k => by show 2 + 8 * k ≤ 4 + 4 * (2 * k); omega)
    (fun k => by
      rw [τ_w, Ret.fst_shift 1 _ (by omega)]; show 5 + 2 * 0 + 4 * (2 * k + 1) + 1 ≤ 10 + 8 * k
      omega)
    (xpin := xpinW N) (xlo := fun _ => 1) (xhi := fun _ => 1)
    (fun _ _ => CElemTiming.transport_winDelay (Nat.le_refl 1) (Nat.le_refl 1)
      (fun t => by show xW (N - 1) (t + 1 - 1) = xW ((Pw N).N - 1) t; rfl))
    (fun b _ => by rw [Dl_w]; show (1 : Int) + ((1 : Nat) : Int) ≤ ((2 : Nat) : Int); decide)
    (Ch := Bool) (ρC := ρCW N) (vC := vCW) (ci := false) (co := true) rfl rfl
    (fun _ => rfl) (fun _ => rfl)
  exact ⟨p1, p2, p4, by decide⟩

/-- **Negative control: without the request-wire lead the output is not a
port.** Same run, same data wire, but the receiver's request wire is one tick
(`Wr = shift 1`, no `DELAY`): then `H_X_LEAD_N` fails (`Dl + xhi = 2 > 1`), and
indeed the output channel is NOT a `Port` for ANY request/acknowledge traces:
at token 0's request edge (`4 + 2N`) the receiver's D pin still shows the
power-up 0, while token 0's value is 1. -/
theorem no_lead_breaks (N : Nat) (hN : 1 ≤ N) (r a : Nat → Bool) :
    ¬ Port ⟨r, a, fun t => busVal 1 (fun b => xpinW N b t)⟩
      (fun j => (Ret.shift 1).fst ((Pw N).τ ((Pw N).N - 1) j)) (Pw N).γ
      (fun k => busVal 1 (valW k)) := by
  intro P
  have h1 : (Ret.shift 1).fst ((Pw N).τ ((Pw N).N - 1) (2 * 0)) = 4 + 2 * N := by
    rw [τ_w, Ret.fst_shift 1 _ (by omega)]; show 5 + 2 * (N - 1) + 4 * (2 * 0) + 1 = 4 + 2 * N
    omega
  have h := P.dat 0 (4 + 2 * N)
    (by show (Ret.shift 1).fst ((Pw N).τ ((Pw N).N - 1) (2 * 0)) ≤ 4 + 2 * N; omega)
    (by show 4 + 2 * N < 6 + 2 * N + 4 * (2 * 0 + 1); omega)
  have hx : xpinW N 0 (4 + 2 * N) = false := by
    unfold xpinW xW; rw [decide_eq_false_iff_not]; omega
  have hv : valW 0 0 = true := rfl
  simp only [busVal] at h
  rw [hx, hv] at h
  simp at h

end Wit

/-! ## 5. 6g `PipePerPin` (per-pin controller LUTs, no `H_LUT_FIFO`) -/

section pipeP
open Formal.Cells.PipePerPin
variable {P : PP} {rst : Nat → Bool} {r a O q : Nat → Nat → Bool} {wl wh : Nat → Nat} {Es Er : Nat}
  {d : Nat → Bundling.Sig} {x : Nat → Nat → Bundling.Sig} {val : Nat → Nat → Bool}
  {dS dE : Nat → Nat} {V : Nat → PipeTimed.Win} {W Erel Sdr Lag : Nat}

theorem tau_thru_P (E : EnvP P (r 0) (a (P.N - 1)) Es Er) (T : TimingP P wh Es Er) (j : Nat) :
    ∀ i, P.τ 0 j ≤ P.τ i j := by
  intro i; induction i with
  | zero => exact Nat.le_refl _
  | succ i ih => have := fwd E T i j; omega

theorem tau_ge_rho0 (E : EnvP P (r 0) (a (P.N - 1)) Es Er) (T : TimingP P wh Es Er) (i j : Nat) :
    P.ρ 0 ≤ P.τ i j := by
  have := tau_lo E T i j; have := S_lo_r E T i j; have := rho0_Rin E j i; omega

/-- 6g's theorems give `PipeIO`. `H_PIN_POS`: the request (I0) site pin plus
tree of stage 0 and the acknowledge (I1) site pin plus tree of the last stage
have positive minimum delay. -/
theorem pipe_io_P (G : GatesP P rst r a O q wl wh) (E : EnvP P (r 0) (a (P.N - 1)) Es Er)
    (T : TimingP P wh Es Er) (D : DataP P O d x val dS dE V W Es Er Erel Sdr Lag)
    (H_PIN_POS : 1 ≤ (P.pr 0).lo + (P.out 0).lo ∧ 1 ≤ (P.pa (P.N - 1)).lo + (P.out (P.N - 1)).lo) :
    PipeIO W P.ρ P.γ (P.τ 0) (P.τ (P.N - 1)) P.R0 (P.ρ 0) (P.out 0).hi (P.out (P.N - 1)).hi
      (O 0) (O (P.N - 1)) (r 0) (a (P.N - 1)) (x (P.N - 1)) val
      (fun k b => P.Sx V dS k b (P.N - 1)) := by
  have hN := T.H_N_POS
  have c0 := nodes_clean G E T 0 (by omega)
  have cL := nodes_clean G E T (P.N - 1) (by omega)
  exact {
    pre0 := c0.1, ph0 := c0.2, preL := cL.1, phL := cL.2
    in_lt := fun j => by have := rho_le E T j; omega
    out_lt := fun j => by have := gam_le E T j; omega
    thru := fun j => tau_thru_P E T j (P.N - 1)
    flush0 := fun j => tau_ge_rho0 E T 0 j
    flushL := fun j => tau_ge_rho0 E T (P.N - 1) j
    env_pos := T.H_R0_POS
    env_first := by have := T.H_R0_LE; have := E.H_RST_EARLY; omega
    req_low0 := E.H_REQ_LOW0, req_ph := E.H_REQ
    ack_low0 := E.H_ACK_LOW0, ack_ph := E.H_ACK
    deliver := fun k b t hb h1 h2 => (pipe_forward G E T D k b hb).1 t h1 h2 }

/-- **The packaged `bd_pipe` contract (6g, per-pin LUTs).** As
`pipe_contract`, from 6g's hypotheses; the end wires flush by the first
request (`H_WIRE_FLUSH` against `ρ 0`), the environment is quiet before
`R0`, and the output lead is `H_X_LEAD_P` on 6g's `Dl`. -/
theorem pipe_contract_pp (G : GatesP P rst r a O q wl wh) (E : EnvP P (r 0) (a (P.N - 1)) Es Er)
    (T : TimingP P wh Es Er) (D : DataP P O d x val dS dE V W Es Er Erel Sdr Lag)
    (H_PIN_POS : 1 ≤ (P.pr 0).lo + (P.out 0).lo ∧ 1 ≤ (P.pa (P.N - 1)).lo + (P.out (P.N - 1)).lo)
    {ain rout : Nat → Bool} (Wa Wr : Ret)
    (H_AIN_LINE : ∀ t, Wa.hi ≤ t → ain t = O 0 (Wa.σ t))
    (H_ROUT_LINE : ∀ t, Wr.hi ≤ t → rout t = O (P.N - 1) (Wr.σ t))
    (H_WIRE_FLUSH : Wa.hi ≤ P.ρ 0 ∧ Wr.hi ≤ P.ρ 0)
    {Qa Qr : Nat} (H_QA : Wa.hi ≤ Qa ∧ Wa.fst (P.out 0).hi ≤ Qa)
    (H_QR : Wr.hi ≤ Qr ∧ Wr.fst (P.out (P.N - 1)).hi ≤ Qr)
    (H_QUIET_AIN : ∀ t, t < Qa → ain t = false) (H_QUIET_ROUT : ∀ t, t < Qr → rout t = false)
    (H_QUIET_REQ : ∀ t, t < P.R0 → r 0 t = false)
    (H_QUIET_ACK : ∀ t, t < P.R0 → a (P.N - 1) t = false)
    (H_SND_PIN : ∀ j, Wa.fst (P.τ 0 j) < P.ρ (j + 1))
    (H_RCV_PIN : ∀ j, Wr.fst (P.τ (P.N - 1) j) < P.γ j)
    (H_IN_LEAD : ∀ k, dS k ≤ P.ρ (2 * k))
    (H_SND_HOLDF : ∀ k, Wa.fst (P.τ 0 (2 * k + 1)) ≤ dE k)
    {xpin : Nat → Nat → Bool} {xlo xhi : Nat → Nat}
    (H_DWIRE : ∀ b, b < W → CElemTiming.WinDelay (xlo b) (xhi b) (x (P.N - 1) b) (xpin b))
    (H_X_LEAD_P : ∀ b, b < W → Dl P V Sdr Lag (P.N - 1) b + (xhi b : Int) ≤ (Wr.lo : Int))
    {Ch : Type} {ρC vC : Ch → Nat → Nat} {ci co : Ch}
    (hρi : ρC ci = P.ρ) (hρo : ρC co = fun j => Wr.fst (P.τ (P.N - 1) j))
    (hvi : ∀ k, vC ci k = busVal W (val k)) (hvo : ∀ k, vC co k = busVal W (val k)) :
    Port ⟨r 0, ain, fun t => busVal W (fun b => d b t)⟩ P.ρ (fun j => Wa.fst (P.τ 0 j))
      (fun k => busVal W (val k)) ∧
    Port ⟨rout, a (P.N - 1), fun t => busVal W (fun b => xpin b t)⟩
      (fun j => Wr.fst (P.τ (P.N - 1) j)) P.γ (fun k => busVal W (val k)) ∧
    (∀ k b t, b < W → Wr.fst (P.τ (P.N - 1) (2 * k)) ≤ t → t < P.γ (2 * k + 1) →
      xpin b t = val k b) ∧
    LinkEv ρC vC ci co := by
  have I := pipe_io_P G E T D H_PIN_POS
  have lead : ∀ k b, b < W → P.Sx V dS k b (P.N - 1) + xhi b ≤ Wr.fst (P.τ (P.N - 1) (2 * k)) := by
    intro k b hb
    have h1 := Sx_le (V := V) E T D.H_DATA_LEAD k b (P.N - 1)
    have h2 := H_X_LEAD_P b hb
    have h3 := Wr.fst_lo (tau_pos E T (P.N - 1) (2 * k))
    omega
  obtain ⟨p1, p2, p3, p4⟩ := pipe_ports I Wa Wr H_AIN_LINE H_ROUT_LINE H_WIRE_FLUSH H_QA H_QR
    H_QUIET_AIN H_QUIET_ROUT H_QUIET_REQ H_QUIET_ACK H_SND_PIN H_RCV_PIN
    (fun k b t hb h1 h2 => D.H_DATA_VALID k b t hb h1 h2) H_IN_LEAD H_SND_HOLDF H_DWIRE lead
  exact ⟨p1, p2, p3, pipe_ev p4 hρi hρo hvi hvo⟩

end pipeP

/-! ## 6. Proposal for shard C: a link WITH an initial token

A `bd_c2n_set` stage (the rig's `uenv1`; any reset-token buffer) comes up
holding one token. C's `linkEq` (`σ co k = σ ci k`) does not cover it. The
proposed equation and event contract, with the `EarlierDet` proof so that
`net_refines_ports` accepts it unchanged: -/

section init
variable {Ch : Type} {ρ v : Ch → Nat → Nat}

/-- **Proposed equation**: output token 0 is the reset token `init`; output
token `k+1` is input token `k`. -/
def linkInitEq (init : Nat) (ci co : Ch) (σ : Ch → Nat → Nat) : Prop :=
  σ co 0 = init ∧ ∀ k, σ co (k + 1) = σ ci k

/-- **Proposed event contract** of a reset-token link: output token `k+1` is
offered strictly after input token `k` (the token shifts by one place), with
its value; output token 0 is the constant `init`. -/
structure LinkInitEv (ρ v : Ch → Nat → Nat) (init : Nat) (ci co : Ch) : Prop where
  init_val : v co 0 = init
  causal : ∀ k, ρ ci (2 * k) < ρ co (2 * (k + 1))
  value : ∀ k, v co (k + 1) = v ci k

theorem linkInit_det {init : Nat} {ci co : Ch} (L : LinkInitEv ρ v init ci co) :
    EarlierDet ρ v [co] (linkInitEq init ci co) := by
  intro c hc k σ hag hE
  obtain rfl := List.mem_singleton.1 hc
  cases k with
  | zero => rw [hE.1, L.init_val]
  | succ k => rw [hE.2 k, hag ci k (L.causal k), L.value k]

theorem linkInit_spec {ch : Ch → Chan} {α : Ch → Nat → Nat}
    (Pall : ∀ c, Port (ch c) (ρ c) (α c) (v c)) {init : Nat} {ci co : Ch}
    (L : LinkInitEv ρ v init ci co) : OpSpec ch [ci] [co] (linkInitEq init ci co) :=
  opSpec_of_ports Pall (linkInit_det L)

end init

end Formal.Cells.ContractsLink
