import Formal.Cells.ContractsOps
import Formal.Cells.OpsTimed2

/-!
# Probe Cc, part 3: B's timed steer theorem gives the uniform contract

The exemplar operator is the steer (`cond_br` = `bd_join` + `bd_steer`),
because it is the one where C's protocol needs data timing (the select) and
where B's theorem (`OpsTimed.steer_ok_static`, probe Lt/Lt2) is in causal /
static form.

`steer_ok_static` says, for the input-indexed edge sequences of its
`SteerRun P`: the receivers' requests `r0`, `r1` are `Tok` traces on `R0`,
`R1` with gate "token `k` routed here", the sender's acknowledge is a clean
`Tok` on `K`, and `ρ j ≤ Rsel j`, `Rsel j + Er ≤ A j ≤ K j`,
`K j + Es ≤ ρ (j + 1)`. Its hypotheses are the gate relations
(`SteerGates`: real INITs, FIFO arcs), the partners' clean traces, the
partners' causality (`SteerCausal`) and the per-arc static obligations
(`SteerStatic`: `S_S_SETUP` = `bd_steer.bundled_s_setup` and `S_S_HOLD` =
`bd_steer.bundled_s_hold` in `formal/out/cell_constraints.json`; `S_ACK`,
the `uack` pin-skew bound, has NO id in that file (missing entry, reported).

This file turns those conclusions into the uniform contract of
`Formal.Cells.Contracts`:

* `steer_ack_port`: the sender-side acknowledge is a clean four-phase wire
  from time 0 on edges `K` (needs the reset fact that `ack` is low before
  `T2`, H_QUIET_ACK);
* `steer_req_port0/1`: each receiver's request, re-indexed on the tokens
  routed to it (B's `Enum`, `Tok.reindex`), is a clean four-phase wire from
  time 0 (H_QUIET_FWD);
* `steer_order`: the edges of every channel the steer touches interleave
  strictly, so with the partners' traces they are `Port`s;
* `steer_ev`: B's ordering gives C's `SteerEv` (causality of every routed
  token, and its routing index), hence (`steer_spec`) C's
  `OpProto ∧ OpData (steerEq …)`.

Named hypotheses added here (not in B's theorem):
* `H_QUIET_FWD`, `H_QUIET_ACK`: reset quiet. Every steer-driven wire is low
  before B's clean window starts (`T1`, `T2`). This is what the gcd reset
  network gives (`ResetGcd`: all control nets settle low under reset); here
  it is a hypothesis per wire. GLS test: the wire is 0 from power-up until
  its first edge.
* `H_FWD_POS : 1 ≤ Wq.lo + Lm` (the forward path has positive minimum delay)
  and `H_ER`, `H_ES ≥ 1`: every gate/wire has a positive delay. Testable from
  the SDF minima (prjxray: no zero arc).
* `H_SEL_VAL`: the steer's select bit is C's `sel` of the joined token's
  value; `H_STEER_DATA`: the routed output's token value is `f` of the input
  token's (the data wire to the branch, C's H_STEER_DATA; B proves no data
  path for `bd_steer`, which has none: the data is a wire beside it).
-/

namespace Formal.Cells.Contracts
open Formal.Net Formal.Net.Handshake Formal.Net.Ops
open Formal.Cells.OpsTimed
open Formal.Cells.PipeTimed (Ret)
open Formal.Net.Ops.Steer (steerEq)
open Formal.Net.Ops.CM (cnt_congr_lt)

/-! ## Generic: starting a `Tok` at time 0, enumerations, `Ret.fst` order -/

theorem tok_from0 {T : Nat} {x : Trace} {e : Nat → Nat} {g : Nat → Bool} (h : Tok T x e g)
    (hq : ∀ t, t < T → x t = false) (hT : T ≤ e 0) (hm : ∀ j, e 0 ≤ e j) : Tok 0 x e g := by
  refine ⟨fun t _ h2 => ?_, fun k t _ h2 h3 => ?_, fun k t _ h2 h3 => ?_⟩
  · by_cases hT' : T ≤ t
    · exact h.pre t hT' h2
    · exact hq t (by omega)
  · exact h.hi k t (by have := hm (2 * k); omega) h2 h3
  · exact h.lo k t (by have := hm (2 * k + 1); omega) h2 h3

theorem fst_mono (r : Ret) {a b : Nat} (hab : a ≤ b) : r.fst a ≤ r.fst b := by
  apply Nat.le_of_not_lt; intro hlt
  have := r.fst_before hlt; have := r.fst_spec b; omega

theorem enum_cnt {g : Nat → Bool} {κ : Nat → Nat} (hE : Enum g κ) : ∀ m, cnt g (κ m) = m := by
  intro m
  induction m with
  | zero => exact Port.cnt_const g (Nat.zero_le _) (fun u _ h2 => hE.before h2)
  | succ m ih =>
    have h1 := cnt_succ_of (f := g) (hE.hit m)
    have hm := hE.mono m
    rw [Port.cnt_const g (a := κ m + 1) (by omega) (fun u h1 h2 => ?_), h1, ih]
    cases hu : g u
    · rfl
    · obtain ⟨m', rfl⟩ := hE.all u hu
      have a : m < m' := Nat.lt_of_not_le fun hle => by have := hE.le_of_le hle; omega
      have b : m' < m + 1 := Nat.lt_of_not_le fun hle => by have := hE.le_of_le hle; omega
      omega

/-- The re-indexed edges of a monotone sequence start at their minimum. -/
theorem rx_min {e κ : Nat → Nat} (he : ∀ x y, x ≤ y → e x ≤ e y)
    (hκ : ∀ a b, a ≤ b → κ a ≤ κ b) (j : Nat) : rx e κ 0 ≤ rx e κ j := by
  rw [rx_0]; unfold rx; apply he; have := hκ 0 (j / 2) (Nat.zero_le _); omega

/-! ## The steer -/

section steer
variable (P : SteerRun)

/-- The routed branch's request edges, per branch. -/
def Rb (b : Bool) : Nat → Nat := if b then P.R1 else P.R0

/-- B's four-phase ordering (`steer_ok_static`'s last conjunct). -/
def SOrder (Er Es : Nat) : Prop :=
  ∀ j, P.ρ j ≤ P.Rsel j ∧ P.Rsel j + Er ≤ P.A j ∧ P.A j ≤ P.K j ∧ P.K j + Es ≤ P.ρ (j + 1)

variable {P}

theorem rho_strict {Er Es : Nat} (hO : SOrder P Er Es) (hEs : 1 ≤ Es) : Strict P.ρ := fun j => by
  have := hO j; omega

theorem rho_mono {Er Es : Nat} (hO : SOrder P Er Es) (hEs : 1 ≤ Es) :
    ∀ a b, a ≤ b → P.ρ a ≤ P.ρ b := fun _ _ h => (Strict.le_iff (rho_strict hO hEs)).2 h

theorem R_mono {Er Es : Nat} (hO : SOrder P Er Es) (hEs : 1 ≤ Es) (b : Bool) :
    ∀ x y, x ≤ y → Rb P b x ≤ Rb P b y := by
  intro x y h
  have hq := fst_mono P.Wq (rho_mono hO hEs x y h)
  cases b
  · exact fst_mono P.W0 (fst_mono P.L5 hq)
  · exact fst_mono P.W1 (fst_mono P.L6 hq)

theorem K_mono {Er Es : Nat} (hO : SOrder P Er Es) (hEs : 1 ≤ Es) : ∀ a b, a ≤ b → P.K a ≤ P.K b := by
  have hs : Strict P.K := fun j => by have := hO j; have := hO (j + 1); omega
  exact fun _ _ h => (Strict.le_iff hs).2 h

/-- On a token routed to branch `b`, the routed edge is that branch's edge. -/
theorem rsel_eq {b : Bool} {k : Nat} (hs : P.sv k = b) (i : Nat) (hi : i < 2) :
    P.Rsel (2 * k + i) = Rb P b (2 * k + i) := by
  unfold SteerRun.Rsel Rb
  rw [show (2 * k + i) / 2 = k by omega, hs]
  cases b <;> rfl

/-- **The sender-side acknowledge is a clean wire from time 0** (input port's
ack half), from B's `Tok (T2 Ta) ack K`. -/
theorem steer_ack_port {Er Es Ta : Nat} {ack : Trace} (hO : SOrder P Er Es) (hEs : 1 ≤ Es)
    (hK : Tok (P.T2 Ta) ack P.K (fun _ => true))
    (H_QUIET_ACK : ∀ t, t < P.T2 Ta → ack t = false) (H_T2 : P.T2 Ta ≤ P.K 0) :
    Tok 0 ack P.K (fun _ => true) :=
  tok_from0 hK H_QUIET_ACK H_T2 (fun j => K_mono hO hEs 0 j (Nat.zero_le _))

/-- **Each receiver's request, on its own tokens, is a clean wire from 0**
(output port's req half), from B's gated `Tok (T1 Tr) r_b R_b` and B's
`Tok.reindex`. Branch 0 (condition false). -/
theorem steer_req_port0 {Er Es Tr : Nat} {r0 : Trace} {κ0 : Nat → Nat} (hO : SOrder P Er Es) (hEs : 1 ≤ Es)
    (hr : Tok (P.T1 Tr) r0 P.R0 (fun k => !P.sv k)) (hE : Enum (fun k => !P.sv k) κ0)
    (H_QUIET_FWD : ∀ t, t < P.T1 Tr → r0 t = false) (H_T1 : P.T1 Tr ≤ P.R0 (2 * κ0 0)) :
    Tok 0 r0 (rx P.R0 κ0) (fun _ => true) :=
  tok_from0 (hr.reindex hE) H_QUIET_FWD (by rw [rx_0]; exact H_T1)
    (rx_min (R_mono hO hEs false) (fun _ _ h => hE.le_of_le h))

theorem steer_req_port1 {Er Es Tr : Nat} {r1 : Trace} {κ1 : Nat → Nat} (hO : SOrder P Er Es) (hEs : 1 ≤ Es)
    (hr : Tok (P.T1 Tr) r1 P.R1 P.sv) (hE : Enum P.sv κ1)
    (H_QUIET_FWD : ∀ t, t < P.T1 Tr → r1 t = false) (H_T1 : P.T1 Tr ≤ P.R1 (2 * κ1 0)) :
    Tok 0 r1 (rx P.R1 κ1) (fun _ => true) :=
  tok_from0 (hr.reindex hE) H_QUIET_FWD (by rw [rx_0]; exact H_T1)
    (rx_min (R_mono hO hEs true) (fun _ _ h => hE.le_of_le h))

/-- **Strict interleaving of every channel the steer touches.**
Input channel: `ρ j < K j < ρ (j+1)`. Output channel of branch `b`, on its
tokens (`κ`): `R (2κm+i) < A (2κm+i)`, `A (2κm) < R (2κm+1)`,
`A (2κm+1) < R (2κ(m+1))`. -/
theorem steer_order {Er Es : Nat} (hO : SOrder P Er Es) (hEr : 1 ≤ Er) (hEs : 1 ≤ Es)
    {b : Bool} {g : Nat → Bool} {κ : Nat → Nat} (hE : Enum g κ) (hg : ∀ k, g k = true → P.sv k = b) :
    (∀ j, P.ρ j < P.K j ∧ P.K j < P.ρ (j + 1)) ∧
    (∀ j, rx (Rb P b) κ j < rx P.A κ j ∧ rx P.A κ j < rx (Rb P b) κ (j + 1)) := by
  refine ⟨fun j => by have := hO j; omega, fun j => ?_⟩
  have hs : P.sv (κ (j / 2)) = b := hg _ (hE.hit _)
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m := ⟨j / 2, by omega⟩
    have hs' : P.sv (κ m) = b := by simpa using hs
    rw [rx_e, rx_e, rx_o]
    have e0 := rsel_eq hs' 0 (by omega); have e1 := rsel_eq hs' 1 (by omega)
    simp only [Nat.add_zero] at e0
    have := hO (2 * κ m); have := hO (2 * κ m + 1)
    omega
  · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m + 1 := ⟨j / 2, by omega⟩
    have hs' : P.sv (κ m) = b := by
      have : (2 * m + 1) / 2 = m := by omega
      rw [this] at hs; exact hs
    rw [rx_o, rx_o, show 2 * m + 1 + 1 = 2 * m + 2 by omega, rx_e2]
    have e1 := rsel_eq hs' 1 (by omega)
    have hs1 : P.sv (κ (m + 1)) = b := hg _ (hE.hit _)
    have e2 := rsel_eq hs1 0 (by omega); simp only [Nat.add_zero] at e2
    have hm := hE.mono m
    have := hO (2 * κ m + 1)
    have hK1 : P.K (2 * κ m + 1) + Es ≤ P.ρ (2 * κ m + 2) := (hO (2 * κ m + 1)).2.2.2
    have hρ := rho_mono hO hEs (2 * κ m + 2) (2 * κ (m + 1)) (by omega)
    have := hO (2 * κ (m + 1))
    omega

/-- Forward causality of a routed token: its request reaches the branch
strictly after the sender raised it (`steer_R_ge` with `1 ≤ Wq.lo + Lm`). -/
theorem steer_causal {Lm : Nat} (hLm : Lm ≤ P.L5.lo + P.W0.lo ∧ Lm ≤ P.L6.lo + P.W1.lo)
    (H_FWD_POS : 1 ≤ P.Wq.lo + Lm) (hpos : ∀ j, 1 ≤ P.ρ j) {b : Bool} {k : Nat} (hs : P.sv k = b) :
    P.ρ (2 * k) < Rb P b (2 * k) := by
  have := steer_R_ge Lm hLm (2 * k) (hpos _)
  have e := rsel_eq hs 0 (by omega); simp only [Nat.add_zero] at e
  omega

/-- **B's steer theorem ⇒ C's `SteerEv`.** The channel map identifies the
steer's input port edges with B's `ρ` and branch `b`'s with B's routed
edges re-indexed on the tokens routed to `b` (`κ b`). The routing index
(`cnt … = m`) is `enum_cnt`; causality is `steer_causal`. -/
theorem steer_ev {C : Type} {ρ v : C → Nat → Nat} {sel : Nat → Bool} {f : Nat → Nat} {cj : C}
    {cout : Bool → C} {Er Es Lm : Nat} (hO : SOrder P Er Es) (hEs : 1 ≤ Es)
    (hLm : Lm ≤ P.L5.lo + P.W0.lo ∧ Lm ≤ P.L6.lo + P.W1.lo) (H_FWD_POS : 1 ≤ P.Wq.lo + Lm)
    (hpos : ∀ j, 1 ≤ P.ρ j)
    (κ : Bool → Nat → Nat) (hE0 : Enum (fun k => !P.sv k) (κ false)) (hE1 : Enum P.sv (κ true))
    (hρj : ρ cj = P.ρ) (hρo : ∀ b, ρ (cout b) = rx (Rb P b) (κ b))
    (H_SEL_VAL : ∀ i, P.sv i = sel (v cj i))
    (H_STEER_DATA : ∀ b m, v (cout b) m = f (v cj (κ b m))) :
    SteerEv ρ v sel f cj cout := by
  refine ⟨by rw [hρj]; exact rho_strict hO hEs, fun b m => ⟨κ b m, ?_, ?_, ?_, H_STEER_DATA b m⟩⟩
  · cases b
    · have := hE0.hit m; rw [← H_SEL_VAL]; simpa using this
    · have := hE1.hit m; rw [← H_SEL_VAL]; exact this
  · cases b
    · exact (cnt_congr_lt (f := fun i' => sel (v cj i') == false) (g := fun k => !P.sv k) _
        fun i _ => by simp [H_SEL_VAL]).trans (enum_cnt hE0 m)
    · exact (cnt_congr_lt (f := fun i' => sel (v cj i') == true) (g := P.sv) _
        fun i _ => by simp [H_SEL_VAL]).trans (enum_cnt hE1 m)
  · rw [hρj, hρo, rx_e]
    apply steer_causal hLm H_FWD_POS hpos
    cases b
    · have := hE0.hit m; simpa using this
    · exact hE1.hit m

/-- **The packaged steer contract (C's interface, from B's theorem).**
From `steer_ok_static`'s hypotheses (gates, partner traces, `SteerCausal`,
`SteerStatic`), the reset-quiet and positivity facts, the token enumerations
and the data / select identifications: every steer-driven wire is a clean
four-phase wire from time 0 on the identified edges, the touched channels'
edges interleave strictly, and the steer meets C's `SteerEv`. Together with
the partners' halves of the ports this is `Port` on all touched channels, and
`steer_spec` then gives `OpProto ∧ OpData (steerEq …)`. -/
theorem steer_contract {req rqu su o5 o6 r0 r1 a0 a1 a0u a1u ao ack s : Trace}
    {Tr Ta Er Es Lm Wm Ls Hs : Nat} (Ws : Ret) (sS sE : Nat → Nat)
    (G : SteerGates P req rqu su o5 o6 r0 r1 a0 a1 a0u a1u ao ack)
    (hw : ∀ t, Ws.hi ≤ t → su t = s (Ws.σ t))
    (hs : ∀ k t, sS k ≤ t → t < sE k → s t = P.sv k)
    (hreq : Tok Tr req P.ρ (fun _ => true))
    (h0 : Tok Ta a0 P.A (fun k => !P.sv k)) (h1 : Tok Ta a1 P.A P.sv)
    (Cs : SteerCausal P sS sE Er Es Ls Hs) (S : SteerStatic P Ws Er Es Lm Wm Ls Hs)
    (H_ER : 1 ≤ Er) (H_ES : 1 ≤ Es) (H_FWD_POS : 1 ≤ P.Wq.lo + Lm)
    (κ : Bool → Nat → Nat) (hE0 : Enum (fun k => !P.sv k) (κ false)) (hE1 : Enum P.sv (κ true))
    (H_QUIET_ACK : ∀ t, t < P.T2 Ta → ack t = false) (H_T2 : P.T2 Ta ≤ P.K 0)
    (H_QUIET_FWD : ∀ t, t < P.T1 Tr → r0 t = false ∧ r1 t = false)
    (H_T1 : P.T1 Tr ≤ P.R0 (2 * κ false 0) ∧ P.T1 Tr ≤ P.R1 (2 * κ true 0))
    {C : Type} {ρ v : C → Nat → Nat} {sel : Nat → Bool} {f : Nat → Nat} {cj : C} {cout : Bool → C}
    (hρj : ρ cj = P.ρ) (hρo : ∀ b, ρ (cout b) = rx (Rb P b) (κ b))
    (H_SEL_VAL : ∀ i, P.sv i = sel (v cj i))
    (H_STEER_DATA : ∀ b m, v (cout b) m = f (v cj (κ b m))) :
    Tok 0 ack P.K (fun _ => true) ∧
    Tok 0 r0 (rx P.R0 (κ false)) (fun _ => true) ∧ Tok 0 r1 (rx P.R1 (κ true)) (fun _ => true) ∧
    (∀ j, P.ρ j < P.K j ∧ P.K j < P.ρ (j + 1)) ∧
    (∀ b j, rx (Rb P b) (κ b) j < rx P.A (κ b) j ∧ rx P.A (κ b) j < rx (Rb P b) (κ b) (j + 1)) ∧
    SteerEv ρ v sel f cj cout := by
  obtain ⟨_, _, hK, hO⟩ := steer_ok_static Ws sS sE G hw hs hreq h0 h1 Cs S
  have hpos : ∀ j, 1 ≤ P.ρ j := fun j => (Cs.H_POS j).1
  refine ⟨steer_ack_port hO H_ES hK H_QUIET_ACK H_T2, ?_, ?_, (steer_order hO H_ER H_ES hE0
      (b := false) (fun k h => by simpa using h)).1, fun b j => ?_,
    steer_ev hO H_ES S.H_LM H_FWD_POS hpos κ hE0 hE1 hρj hρo H_SEL_VAL H_STEER_DATA⟩
  · obtain ⟨f0, _⟩ := steer_ok_static Ws sS sE G hw hs hreq h0 h1 Cs S
    exact steer_req_port0 hO H_ES f0 hE0 (fun t h => (H_QUIET_FWD t h).1) H_T1.1
  · obtain ⟨_, f1, _⟩ := steer_ok_static Ws sS sE G hw hs hreq h0 h1 Cs S
    exact steer_req_port1 hO H_ES f1 hE1 (fun t h => (H_QUIET_FWD t h).2) H_T1.2
  · cases b
    · exact (steer_order hO H_ER H_ES hE0 (b := false) (fun k h => by simpa using h)).2 j
    · exact (steer_order hO H_ER H_ES hE1 (b := true) (fun k h => h)).2 j

end steer

end Formal.Cells.Contracts
