import Formal.Cells.OpsTimed
import Formal.Net.Ops

/-!
# Probe Cc, part 1: one port contract between B's timed cells and C's networks

Shard B, Phase 3 (composition). C's composition (`Formal.Net.Ops`, C-8f) takes,
for every operator `o`, the pair

    OpProto ch (ins o) (outs o) ∧ OpData ch (ins o) (outs o) (E o)

(`OpSpec` below): a causal assume-guarantee four-phase protocol rule on the
port wires of C's `Chan` (`req ack : Nat → Bool`, `dat : Nat → Nat`), and a
token-level (Kahn) data rule relative to the operator's token equations
`E o` (`forkEq`, `joinEq`, `linkEq`, `steerEq`, `muxEq`, `muxnEq`, `amergeEq`,
`srcEq`, sink `True`). `net_refines` composes them.

B's timed cell theorems speak a different language: event times. A port wire
is a `Tok T x e g` trace (`OpsTimed.Tok`: low before `e 0`, shows `g k` on
`[e (2k), e (2k+1))`, low on `[e (2k+1), e (2k+2))`), and a cell theorem says:
if the partners' wires are such traces with such edges, and the static
per-arc obligations hold, then the cell's own wires are such traces with
derived edges, and the edges obey causality inequalities.

The uniform contract shape is therefore, per channel, the **event port**

    Port c ρ α v  :  c.req is Tok 0 on ρ, c.ack is Tok 0 on α,
                     0 < ρ 0, ρ j < α j < ρ (j+1)   (strict interleaving),
                     c.dat = v k on [ρ (2k), α (2k+1))  (H_BUNDLE, event form),

and, per operator, an **event data contract**: each output token `k` is
offered strictly after the input tokens its value depends on, and its value
`v` is the token equation applied to those input values (`EarlierDet`).

This file proves the bridge (all general, no cell in it):

* `Port.protocol`, `Port.held`, `Port.init_req/init_ack`: a port is a C
  channel obeying C's `Protocol` and `Held` (H_BUNDLE).
* `Port.offAt_iff`: C's `OffAt c k r` (the k-th `req↑` is the step `r → r+1`)
  holds exactly at `r + 1 = ρ (2k)`, and then `c.dat (r+1) = v k`.
* `opSpec_of_ports`: if every channel an operator touches is a port and the
  operator meets `EarlierDet` for its equations, C's `OpProto ∧ OpData` hold.
* `net_refines_ports`: hence (C's `net_refines`) every offered token on every
  channel is the token-semantics value, for every solution of the equations.

Per-operator `EarlierDet` lemmas (fork, join, link, src, sink, steer, mux,
3-way mux, arbitrated merge), each matching C's equation verbatim, are in
`Formal.Cells.ContractsOps`; the instantiation of B's theorems (the `Tok`
facts that build the ports) in `Formal.Cells.ContractsB`.

## What this shape does NOT give (stated, not hidden)

`opSpec_of_ports` assumes the ports on ALL the operator's channels, inputs
and outputs alike, for the whole run. B's theorems give the outputs' ports
from the inputs' ports and the partners' causality. In a closed network these
assumptions are circular (op A's output port needs op B's ack port, which
needs op A's output port). Closing that circle needs every B theorem in a
time-truncated (causal) form: "outputs are ports up to time t if inputs and
partners are ports up to time t - 1". None of B's timed theorems is stated
that way. This is the main item C's interface needs and B has not proved
(notes `B-contracts.md`, item G1).
-/

namespace Formal.Cells.Contracts
open Formal.Net Formal.Net.Handshake Formal.Net.Ops
open Formal.Cells.OpsTimed (Tok)

/-! ## Strictly increasing edge sequences -/

/-- Edges strictly increase. -/
def Strict (e : Nat → Nat) : Prop := ∀ j, e j < e (j + 1)

theorem Strict.lt {e : Nat → Nat} (h : Strict e) : ∀ {a b}, a < b → e a < e b := by
  intro a b hab
  induction b with
  | zero => omega
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le (Nat.le_of_lt_succ hab) with h1 | h1
    · exact Nat.lt_trans (ih h1) (h b)
    · subst h1; exact h a

theorem Strict.le_iff {e : Nat → Nat} (h : Strict e) {a b : Nat} : e a ≤ e b ↔ a ≤ b := by
  constructor
  · intro hab; apply Nat.le_of_not_lt; intro hba; have := h.lt hba; omega
  · intro hab; rcases Nat.lt_or_eq_of_le hab with h1 | h1
    · exact Nat.le_of_lt (h.lt h1)
    · subst h1; exact Nat.le_refl _

/-- Every instant is before the first edge or between two consecutive edges. -/
theorem locate {e : Nat → Nat} (h : Strict e) :
    ∀ t, t < e 0 ∨ ∃ j, e j ≤ t ∧ t < e (j + 1) := by
  intro t
  induction t with
  | zero =>
    by_cases h0 : 0 < e 0
    · exact Or.inl h0
    · exact Or.inr ⟨0, by omega, by have := h 0; omega⟩
  | succ t ih =>
    rcases ih with h0 | ⟨j, h1, h2⟩
    · by_cases h3 : t + 1 < e 0
      · exact Or.inl h3
      · exact Or.inr ⟨0, by omega, by have := h 0; omega⟩
    · by_cases h3 : t + 1 < e (j + 1)
      · exact Or.inr ⟨j, by omega, h3⟩
      · exact Or.inr ⟨j + 1, by omega, by have := h (j + 1); omega⟩

/-! ## A clean four-phase wire (`Tok` from 0 with gate `true`) -/

section wire
variable {x : Trace} {e : Nat → Nat}

/-- Value of a clean four-phase wire between edges `j` and `j+1`. -/
theorem val_between (hx : Tok 0 x e (fun _ => true)) {j t : Nat}
    (h1 : e j ≤ t) (h2 : t < e (j + 1)) : x t = (j % 2 == 0) := by
  rcases Nat.mod_two_eq_zero_or_one j with hj | hj
  · obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k := ⟨j / 2, by omega⟩
    rw [hx.hi k t (Nat.zero_le _) h1 (by simpa using h2)]; simp [hj]
  · obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k + 1 := ⟨j / 2, by omega⟩
    rw [hx.lo k t (Nat.zero_le _) h1 (by simpa [Nat.add_assoc] using h2)]; simp [hj]

theorem val_pre (hx : Tok 0 x e (fun _ => true)) {t : Nat} (h : t < e 0) : x t = false :=
  hx.pre t (Nat.zero_le _) h

/-- Uniform value: before the first edge `false`, else by the parity of the edge. -/
theorem val_of (hx : Tok 0 x e (fun _ => true)) (hs : Strict e) (t : Nat) :
    (t < e 0 ∧ x t = false) ∨ ∃ j, e j ≤ t ∧ t < e (j + 1) ∧ x t = (j % 2 == 0) := by
  rcases locate hs t with h | ⟨j, h1, h2⟩
  · exact Or.inl ⟨h, val_pre hx h⟩
  · exact Or.inr ⟨j, h1, h2, val_between hx h1 h2⟩

/-- A wire changes only across an edge: if `x` changes at `t → t+1`, then
`t + 1 = e j` for some `j`, and before the change `x t = (j odd)`. -/
theorem change_at_edge (hx : Tok 0 x e (fun _ => true)) (hs : Strict e) {t : Nat}
    (hc : x (t + 1) ≠ x t) : ∃ j, t + 1 = e j ∧ x t = (j % 2 == 1) ∧ x (t + 1) = (j % 2 == 0) := by
  rcases locate hs t with h0 | ⟨j, h1, h2⟩
  · rcases locate hs (t + 1) with h0' | ⟨j', h1', h2'⟩
    · exact absurd ((val_pre hx h0').trans (val_pre hx h0).symm) hc
    · have : j' = 0 := by
        rcases Nat.eq_zero_or_pos j' with h | h
        · exact h
        · have := hs.lt h; have := hs.lt (show 0 < j' from h); omega
      subst this
      exact ⟨0, by omega, by rw [val_pre hx h0] <;> rfl, by rw [val_between hx h1' h2'] <;> rfl⟩
  · by_cases h3 : t + 1 < e (j + 1)
    · exact absurd ((val_between hx (by omega) h3).trans (val_between hx h1 h2).symm) hc
    · have h4 := hs (j + 1)
      refine ⟨j + 1, by omega, ?_, ?_⟩
      · rw [val_between hx h1 h2]
        rcases Nat.mod_two_eq_zero_or_one j with hj | hj <;> simp [hj, Nat.add_mod]
      · rw [val_between hx (j := j + 1) (by omega) (by omega)]
end wire

/-! ## The event port -/

/-- **The uniform port contract** (one channel, the whole run).

* `req`/`ack`: both wires are clean four-phase traces from time 0 with edge
  times `ρ`, `α` (B's `Tok` with gate `true`);
* `start`, `ra`, `ar`: the edges interleave strictly,
  `0 < ρ 0 < α 0 < ρ 1 < α 1 < …` (request first; every gate and wire has a
  positive delay, so a response edge is strictly after its cause);
* `dat`: the bus shows the token value `v k` from the request rise of token
  `k` (`ρ (2k)`) until its acknowledge fall (`α (2k+1)`), exclusive. This is
  H_BUNDLE (LIBRARY.md "stable from req-rise to ack-fall") at the channel's
  wires, with zero margins, as C's `Held`.

Every field is a fact about one routed channel that GLS can test directly:
log `req`, `ack`, `dat` at the consumer pins, extract edge times, check the
interleaving and the data window. -/
structure Port (c : Chan) (ρ α v : Nat → Nat) : Prop where
  req : Tok 0 c.req ρ (fun _ => true)
  ack : Tok 0 c.ack α (fun _ => true)
  start : 0 < ρ 0
  ra : ∀ j, ρ j < α j
  ar : ∀ j, α j < ρ (j + 1)
  dat : ∀ k t, ρ (2 * k) ≤ t → t < α (2 * k + 1) → c.dat t = v k

namespace Port
variable {c : Chan} {ρ α v : Nat → Nat}

theorem strictR (P : Port c ρ α v) : Strict ρ := fun j => Nat.lt_trans (P.ra j) (P.ar j)
theorem strictA (P : Port c ρ α v) : Strict α := fun j => Nat.lt_trans (P.ar j) (P.ra (j + 1))

theorem init_req (P : Port c ρ α v) : c.req 0 = false := val_pre P.req P.start
theorem init_ack (P : Port c ρ α v) : c.ack 0 = false := val_pre P.ack (by have := P.ra 0; omega)

/-- **Port ⇒ C's four-phase `Protocol`.** -/
theorem protocol (P : Port c ρ α v) : Protocol c := by
  refine ⟨⟨P.init_req, P.init_ack⟩, fun t => ⟨fun hc => ?_, fun hc => ?_⟩⟩
  · -- SendStep: req moves at an edge `ρ j`; ack shows the same parity then.
    obtain ⟨j, hj, hr, _⟩ := change_at_edge P.req P.strictR hc
    rw [hr]
    rcases Nat.eq_zero_or_pos j with h0 | h0
    · subst h0; rw [val_pre P.ack (by have := P.ra 0; omega)]; rfl
    · obtain ⟨i, rfl⟩ : ∃ i, j = i + 1 := ⟨j - 1, by omega⟩
      have h1 := P.ar i; have h2 := P.ra (i + 1)
      rw [val_between P.ack (j := i) (by omega) (by omega)]
      rcases Nat.mod_two_eq_zero_or_one i with hi | hi <;> simp [hi, Nat.add_mod]
  · -- RecvStep: ack moves at an edge `α j`; req shows the other parity then.
    obtain ⟨j, hj, ha, _⟩ := change_at_edge P.ack P.strictA hc
    rw [ha]
    have h1 := P.ra j; have h2 := P.ar j
    rw [val_between P.req (j := j) (by omega) (by omega)]
    rcases Nat.mod_two_eq_zero_or_one j with hi | hi <;> simp [hi]

/-- While the channel is mid-transaction it is inside a data window. -/
theorem window (P : Port c ρ α v) {t : Nat} (h : inTx c t = true) :
    ∃ k, ρ (2 * k) ≤ t ∧ t < α (2 * k + 1) := by
  rcases val_of P.req P.strictR t with ⟨h0, hr⟩ | ⟨j, h1, h2, hr⟩
  · have := val_pre P.ack (t := t) (by have := P.ra 0; omega)
    simp [inTx, hr, this] at h
  · rcases Nat.mod_two_eq_zero_or_one j with hj | hj
    · obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k := ⟨j / 2, by omega⟩
      exact ⟨k, h1, by have := P.ra (2 * k + 1); omega⟩
    · obtain ⟨k, rfl⟩ : ∃ k, j = 2 * k + 1 := ⟨j / 2, by omega⟩
      have h2' : t < ρ (2 * k + 2) := h2
      have hreq : c.req t = false := by rw [hr]; simp [hj]
      have hack : c.ack t = true := by simpa [inTx, hreq] using h
      rcases val_of P.ack P.strictA t with ⟨_, ha⟩ | ⟨m, m1, m2, ha⟩
      · rw [ha] at hack; cases hack
      · have e1 : α (2 * k) < ρ (2 * k + 1) := P.ar (2 * k)
        have e2 : ρ (2 * k + 2) < α (2 * k + 2) := P.ra (2 * k + 2)
        have e3 : ρ (2 * k) < ρ (2 * k + 1) := P.strictR (2 * k)
        have lo : 2 * k ≤ m := Nat.le_of_not_lt fun hlt => by
          have := (P.strictA.le_iff (a := m + 1) (b := 2 * k)).2 (by omega); omega
        have hi : m < 2 * k + 2 := Nat.lt_of_not_le fun hle => by
          have := (P.strictA.le_iff).2 hle; omega
        have hm : m % 2 = 0 := by
          rw [hack] at ha; cases h : m % 2 == 0
          · rw [h] at ha; cases ha
          · simpa using h
        have : m = 2 * k := by omega
        subst this
        exact ⟨k, by omega, m2⟩

/-- **Port ⇒ C's `Held` (H_BUNDLE).** -/
theorem held (P : Port c ρ α v) : Held c := by
  intro t h0 h1
  obtain ⟨k, a1, a2⟩ := P.window h0
  obtain ⟨k', b1, b2⟩ := P.window h1
  have hk : k = k' := by
    rcases Nat.lt_trichotomy k k' with h | h | h
    · have := (P.strictR.le_iff (a := 2 * k + 2) (b := 2 * k')).2 (by omega)
      have : α (2 * k + 1) < ρ (2 * k + 2) := P.ar (2 * k + 1)
      omega
    · exact h
    · have := (P.strictR.le_iff (a := 2 * k' + 2) (b := 2 * k)).2 (by omega)
      have : α (2 * k' + 1) < ρ (2 * k' + 2) := P.ar (2 * k' + 1)
      omega
  subst hk
  rw [P.dat k (t + 1) (by omega) b2, P.dat k t a1 a2]

/-- A request rise happens exactly one tick before an even edge. -/
theorem rise_iff (P : Port c ρ α v) (u : Nat) :
    riseB c.req u = true ↔ ∃ k, u + 1 = ρ (2 * k) := by
  constructor
  · intro h
    simp [riseB] at h
    obtain ⟨j, hj, _, h1⟩ := change_at_edge P.req P.strictR (t := u) (by rw [h.1, h.2]; decide)
    rw [h.2] at h1
    have : j % 2 = 0 := by have := h1.symm; simpa using this
    exact ⟨j / 2, by rw [hj]; congr 1; omega⟩
  · rintro ⟨k, hk⟩
    have hpos : 0 < ρ (2 * k) := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; exact P.start
      · have := P.strictR.lt (show 0 < 2 * k by omega); have := P.start; omega
    have v1 : c.req (u + 1) = true := by
      rw [val_between P.req (j := 2 * k) (by omega) (by have := P.strictR (2 * k); omega)]; simp
    have v0 : c.req u = false := by
      rcases Nat.eq_zero_or_pos k with h | h
      · subst h; have hk0 : u + 1 = ρ 0 := hk; exact val_pre P.req (by omega)
      · obtain ⟨i, rfl⟩ : ∃ i, k = i + 1 := ⟨k - 1, by omega⟩
        have hk' : u + 1 = ρ (2 * i + 1 + 1) := by rw [hk, show 2 * (i + 1) = 2 * i + 1 + 1 by omega]
        have := P.strictR (2 * i + 1)
        rw [val_between P.req (j := 2 * i + 1) (by omega) (by omega)]
        simp [Nat.add_mod]
    simp [riseB, v0, v1]

/-- No rise strictly between two consecutive even edges' rise steps. -/
theorem cnt_const (f : Nat → Bool) {a b : Nat} (hab : a ≤ b)
    (hf : ∀ u, a ≤ u → u < b → f u = false) : cnt f b = cnt f a := by
  induction b with
  | zero => rw [Nat.le_zero.mp hab]
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le hab with h | h
    · have := hf b (by omega) (by omega)
      simp only [cnt, this]; simpa using ih (by omega) (fun u h1 h2 => hf u h1 (by omega))
    · rw [h]

/-- The `k`-th rise is the step `ρ (2k) - 1 → ρ (2k)`: before it, `k` rises. -/
theorem cnt_at (P : Port c ρ α v) : ∀ k, cnt (riseB c.req) (ρ (2 * k) - 1) = k := by
  have pos : ∀ k, 0 < ρ (2 * k) := fun k => by
    rcases Nat.eq_zero_or_pos k with h | h
    · subst h; exact P.start
    · have := P.strictR.lt (show 0 < 2 * k by omega); have := P.start; omega
  have norise : ∀ k u, ρ (2 * k) ≤ u → u < ρ (2 * (k + 1)) - 1 → riseB c.req u = false := by
    intro k u h1 h2
    cases h : riseB c.req u
    · rfl
    · obtain ⟨k', hk'⟩ := (P.rise_iff u).1 h
      have a := (P.strictR.le_iff (a := 2 * k) (b := 2 * k')).1 (by omega)
      have b : ρ (2 * k') < ρ (2 * (k + 1)) := by omega
      have b' : 2 * k' < 2 * (k + 1) := Nat.lt_of_not_le fun hle => by
        have := (P.strictR.le_iff).2 hle; omega
      have : k' = k := by omega
      subst this; omega
  intro k
  induction k with
  | zero =>
    apply (cnt_const _ (Nat.zero_le _) fun u _ h2 => ?_).trans rfl
    cases h : riseB c.req u
    · rfl
    · obtain ⟨k', hk'⟩ := (P.rise_iff u).1 h
      have := (P.strictR.le_iff (a := 0) (b := 2 * k')).2 (Nat.zero_le _); simp at h2; omega
  | succ k ih =>
    have hr : riseB c.req (ρ (2 * k) - 1) = true :=
      (P.rise_iff _).2 ⟨k, by have := pos k; omega⟩
    have hlt : ρ (2 * k) < ρ (2 * (k + 1)) := P.strictR.lt (by omega)
    rw [cnt_const _ (a := ρ (2 * k)) (by omega) (norise k)]
    have := cnt_succ_of hr
    rw [show ρ (2 * k) - 1 + 1 = ρ (2 * k) by have := pos k; omega] at this
    rw [this, ih]

/-- **C's offers on a port.** The `k`-th request rise is the step
`r → r + 1` exactly when `r + 1 = ρ (2k)`. -/
theorem offAt_iff (P : Port c ρ α v) (k r : Nat) : OffAt c k r ↔ r + 1 = ρ (2 * k) := by
  constructor
  · rintro ⟨h1, h2⟩
    obtain ⟨k', hk'⟩ := (P.rise_iff r).1 h1
    have := P.cnt_at k'
    rw [show ρ (2 * k') - 1 = r by omega, h2] at this
    subst this; exact hk'
  · intro h
    refine ⟨(P.rise_iff r).2 ⟨k, h⟩, ?_⟩
    have := P.cnt_at k; rwa [show ρ (2 * k) - 1 = r by omega] at this

/-- The value C reads at an offer is the port's token value. -/
theorem offer_val (P : Port c ρ α v) {k r : Nat} (h : OffAt c k r) : c.dat (r + 1) = v k := by
  have := (P.offAt_iff k r).1 h
  exact P.dat k (r + 1) (by omega) (by have := P.ra (2 * k); have := P.ar (2 * k); have := P.ra (2 * k + 1); omega)

theorem pos (P : Port c ρ α v) (j : Nat) : 0 < ρ j := by
  rcases Nat.eq_zero_or_pos j with h | h
  · subst h; exact P.start
  · have := P.strictR.lt h; have := P.start; omega

/-- Every token of a port is offered (at `ρ (2k) - 1`). -/
theorem offered (P : Port c ρ α v) (k : Nat) : OffAt c k (ρ (2 * k) - 1) := by
  apply (P.offAt_iff k _).2
  have := P.pos (2 * k); omega

end Port

/-! ## The uniform operator contract and the bridge to C -/

variable {C : Type}

/-- **C's interface for one operator**: the causal four-phase protocol rule
and the token-level data rule for the equations `E`. -/
def OpSpec (ch : C → Chan) (ins outs : List C) (E : (C → Nat → Nat) → Prop) : Prop :=
  OpProto ch ins outs ∧ OpData ch ins outs E

/-- A whole-run port assignment: every channel `c` is a port with request
edges `ρ c`, acknowledge edges `α c` and token values `v c`. -/
def Ports (ch : C → Chan) (ρ α v : C → Nat → Nat) (cs : List C) : Prop :=
  ∀ c ∈ cs, Port (ch c) (ρ c) (α c) (v c)

/-- **The event data contract of one operator** (`EarlierDet`): for every
output `c` and token `k`, every stream assignment `σ` that satisfies the
operator's equations and agrees with the port values on every token (of any
channel) offered strictly before `c`'s token `k` gives that token the port's
value `v c k`. This is what each per-operator lemma proves from B's
causality (output edge strictly after the input edges it reads) and data
(output value = function of input values) conclusions. -/
def EarlierDet (ρ v : C → Nat → Nat) (outs : List C) (E : (C → Nat → Nat) → Prop) : Prop :=
  ∀ c ∈ outs, ∀ k σ, (∀ c' k', ρ c' (2 * k') < ρ c (2 * k) → σ c' k' = v c' k') → E σ →
    σ c k = v c k

/-- **Ports + event data contract ⇒ C's `OpSpec`.** `Pall` gives the port of
EVERY channel (C's `Agree` ranges over all channels of the network). -/
theorem opSpec_of_ports {ch : C → Chan} {ρ α v : C → Nat → Nat} {ins outs : List C}
    {E : (C → Nat → Nat) → Prop}
    (Pall : ∀ c, Port (ch c) (ρ c) (α c) (v c)) (hD : EarlierDet ρ v outs E) :
    OpSpec ch ins outs E := by
  refine ⟨⟨fun t _ _ _ _ => ⟨fun c _ => ((Pall c).protocol.2 t).2, fun c _ => ((Pall c).protocol.2 t).1⟩,
    fun c _ => (Pall c).init_ack, fun c _ => (Pall c).init_req⟩, ?_⟩
  intro _ _ c hc k r hoff σ hag hE
  rw [(Pall c).offer_val hoff]
  have hr := ((Pall c).offAt_iff k r).1 hoff
  refine hD c hc k σ (fun c' k' hlt => ?_) hE
  have ho := (Pall c').offered k'
  have := (Pall c').pos (2 * k')
  rw [hag c' k' _ (by omega) ho, (Pall c').offer_val ho]

/-- **Composition.** If every channel of C's network is a port and every
operator meets its event data contract, C's `net_refines` applies: every
offered token on every channel has the value every solution of the token
equations gives it. (`H_BUNDLE` is discharged by `Port.held`.) -/
theorem net_refines_ports {O : Type} (N : Net C O) (ch : C → Chan) (E : O → (C → Nat → Nat) → Prop)
    {ρ α v : C → Nat → Nat} (Pall : ∀ c, Port (ch c) (ρ c) (α c) (v c))
    (hD : ∀ o, EarlierDet ρ v (N.outs o) (E o))
    (ref : C → Nat → Nat) (href : ∀ o, E o ref) :
    ∀ c k, ref c k = v c k := by
  intro c k
  have hop := fun o => (opSpec_of_ports (ins := N.ins o) Pall (hD o))
  have := net_refines N ch E (fun o => (hop o).1) (fun c => (Pall c).held) (fun o => (hop o).2) ref href
    c k _ ((Pall c).offered k)
  rw [this, (Pall c).offer_val ((Pall c).offered k)]

/-! ## Non-vacuity: a concrete port

Period 8: request rises at `8k+1`, ack at `8k+3`, request falls at `8k+5`,
ack at `8k+7`; the bus shows `k` (= `t / 8`) throughout token `k`'s window.
-/

namespace Witness
def wreq (t : Nat) : Bool := decide (1 ≤ t % 8 ∧ t % 8 < 5)
def wack (t : Nat) : Bool := decide (3 ≤ t % 8 ∧ t % 8 < 7)
def wch : Chan := ⟨wreq, wack, fun t => t / 8⟩

theorem port : Port wch (fun j => 4 * j + 1) (fun j => 4 * j + 3) (fun k => k) where
  req := ⟨fun t _ h => by simp [wch, wreq]; omega,
    fun k t _ h1 h2 => by simp [wch, wreq]; omega,
    fun k t _ h1 h2 => by simp [wch, wreq]; omega⟩
  ack := ⟨fun t _ h => by simp [wch, wack]; omega,
    fun k t _ h1 h2 => by simp [wch, wack]; omega,
    fun k t _ h1 h2 => by simp [wch, wack]; omega⟩
  start := by decide
  ra j := by omega
  ar j := by omega
  dat k t h1 h2 := by simp [wch]; omega

/-- The witness port carries token `k` with value `k`, offered at `8k`. -/
theorem offers (k : Nat) : OffAt wch k (8 * k) ∧ wch.dat (8 * k + 1) = k := by
  have h := (port.offAt_iff k (8 * k)).2 (by omega)
  exact ⟨h, port.offer_val h⟩
end Witness

end Formal.Cells.Contracts
