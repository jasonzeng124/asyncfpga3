import Formal.Cells.LinkExact
import Formal.Cells.LibGapMux
import Formal.Net.OpsLink
import Formal.Net.OpsSteer
import Formal.Net.OpsMux
open Formal.Core.LutList

/-!
# ZeroDelayRefine: physical cell traces ↦ C's zero-delay traces (cell half of Br2 / C-8x)

Probe Bzd (shard B); note `formal/notes/B-zero-delay-refine.md`.

C's capstone states `H_BUNDLE` (`Ops.Held`) on ZERO-DELAY traces: Nat ticks, Bool wires,
the gate fields of `Ops.Link.Link`, `Ops.Steer.Steer`, `Ops.Mux.Mux`. This file proves, for one
token through each data-path cell of gcd_hw, that every PHYSICAL trace of the cell (B's exact
models: real INITs, per-pin read maps in delay windows, environment wires arbitrary inside
their transition windows) is the image of an explicit zero-delay trace that satisfies C's
predicates exactly as C defines them (imported, not restated), under a monotone retiming of
the handshake events, with the latched data equal.

## The refinement notion (named, `Ev` / `Mono` / `WinImg`)

* A physical handshake event is a window `Ev = [lo, hi]`: the wire is surely at its old value
  before `lo` and surely at its new value from `hi` (it may glitch, or be X, in between).
* A retiming assigns each event an abstract step (`tokA kr kf`: an abstract wire that rises at
  step `kr → kr+1` and falls at `kf → kf+1`). It is **monotone** (`Mono`) when an event that
  physically SURELY precedes another (`e.hi < e'.lo`) gets the earlier step.
* `WinImg p lo hi T0 er ef`: the physical wire is DEFINITE and equal to the abstract value in
  every phase between its event windows (from `T0` on), and the high phase is nonempty.
* Data: the abstract bus carries the token value through the whole transaction (so `Held` holds
  on it); the physical side is related at CAPTURE: the latch output equals that value from its
  capture on (`LibGapLatch.Capt`, `LinkExact.Spec.out`). The physical bus is NOT claimed equal
  to the abstract bus sample by sample (it is not: data may arrive after `req↑`).

## Results

* **Link stage** (`bd_link` = `bd_c2n` controller + `bd_latch` bit, `LinkExact`'s model):
  `link_refines`: Wf + the six `bd_link.stage` rows (`LinkExact.Conj`) + `Causal` (the
  environment does not answer before the stage could have spoken) ⇒ the explicit abstract run
  `lI/lO/lC` satisfies C's `Link`, `Protocol` on both channels, `Held` on both channels, and
  the physical behaviour refines it (`LinkRef`: monotone retiming, window images of req_in,
  ack_out and the node, capture of `v`). `link_ref_iff` (exact): under Wf, Split and Causal,
  every behaviour in the box refines **iff** `Conj`. `link_ref_breaks`: for each of the six
  rows, the 1-tick violation `LinkExact.Pv i` has a behaviour with NO such refinement.
* **Steer** (`bd_steer`, `LibGapSteer`'s per-pin model plus the `uack` OR at its real INIT):
  `steer_refines`: `bd_steer.bundled_s_setup/_hold` (read-map form, both outputs) +
  `H_REQ_WIDTH`, `H_ACK_WIDTH` (pulses outlast their read skew), `H_UNSEL_ACK` + `SCausal`
  ⇒ explicit abstract run satisfying C's `Steer`, `Protocol`, `Held`, refined physically.
  `steer_unsel_never` (any retiming): in EVERY run of C's `Steer` in which the select reads `v`
  whenever the request is high, the unselected branch request never rises; so the counter-runs
  `steer_setup_breaks` / `steer_hold_breaks` (LibGapSteer's `spurious_token`,
  `late_hold_glitch`) admit no refinement under ANY retiming.
* **Mux join** (`bd_mux` uj0/uj1, `LibGapMux`'s model, y selected, x waiting):
  `mux_refines`: `bd_mux.bundled_s_setup/_hold` (both joins) + `H_JOIN_RACE` (the selected
  join's own-feedback race, read-map form) + `MCausal` ⇒ explicit abstract run satisfying C's
  whole `Mux` structure, `Protocol` on x, y, c, z and `Held c`, with the physical inputs and
  both joins refined. `mux_unsel_never` (any retiming), `mux_setup_breaks`
  (`wrong_branch_latched`), `mux_hold_breaks` (`selected_early_fall`).

## Answer to "is C's predicate an image at all?"

C's HANDSHAKE fields never demand simultaneity (every gate field is "moves only to the value
of the previous tick"; DI wires may lag independently), so they are images. C's DATA fields
(`H_LATCH_OPEN`, `Steer.dat`, `Mux.dat`, `Join.dat`) are zero-delay equations between buses at
one tick; physically the latch output reaches `v` only at `max (U1 + pe.hi) (Td + pd.hi)`,
possibly after the node opens, so they are images only in the captured-value sense used here.

NOT covered: the network half (consistency of the per-cell retimings across a wire, i.e. that
the downstream cell's capture of this cell's output is this cell's abstract value: Br3 /
`Bridge*`); more than one token; the link's own output wires `ack_in`/`req_out`
(`LinkExact.rout_definite` gives their definite intervals; their cleanliness is `H_ROUT`);
the mux's `zr`, `xa`, `ya`, `ca` nodes (other rows: `MuxRtzTimed`, `bundled_z*`; here they
are only abstract); the mux with x selected (symmetric, not written); refinements that place
the link node's edges outside the input-derived windows `[U0,U1]`, `[V0,V1]`.
Core Lean only.
-/

namespace Formal.Cells.ZeroDelayRefine
open Formal.Cells
open Formal.Cells.CElemFn
open Formal.Cells.LibGapSteer (Rd pulse Stable outB outB_eq SpecOK steer_pin_ok)
open Formal.Cells.LibGapLatch
open Formal.Cells.LinkExact
open Formal.Net (Trace)
open Formal.Net.Handshake (Chan Protocol SendStep RecvStep)
open Formal.Net.Ops (Held inTx)

/-! ## 0. Retiming framework -/

/-- A physical event window: old value surely before `lo`, new value surely from `hi`. -/
structure Ev where
  lo : Int
  hi : Int

/-- **Monotone retiming** of a family of events (each paired with its abstract step): an event
that physically surely precedes another gets the earlier abstract step. -/
def Mono (l : List (Ev × Nat)) : Prop :=
  ∀ p ∈ l, ∀ q ∈ l, p.1.hi < q.1.lo → p.2 < q.2

/-- Abstract one-token wire: high on `(kr, kf]` (rises at step `kr → kr+1`, falls at `kf → kf+1`). -/
def tokA (kr kf : Nat) (n : Nat) : Bool := decide (kr < n ∧ n ≤ kf)

theorem tokA_hi {kr kf n : Nat} (h : kf < n) : tokA kr kf n = false := by
  simp [tokA]; omega

/-- **Window image** of a one-token wire: definite `lo` before the rise window (from `T0`),
definite `hi` between the windows (a nonempty phase), definite `lo` after the fall window. -/
structure WinImg {α : Type} (p : Int → α) (lo hi : α) (T0 : Int) (er ef : Ev) : Prop where
  ne : er.hi < ef.lo
  pre : ∀ x, T0 ≤ x → x < er.lo → p x = lo
  mid : ∀ x, er.hi ≤ x → x < ef.lo → p x = hi
  post : ∀ x, ef.hi ≤ x → p x = lo

theorem winImg_of {α : Type} {p : Int → α} {lo hi : α} {T0 a b c d : Int} (ne : b < c)
    (pre : ∀ x, T0 ≤ x → x < a → p x = lo) (mid : ∀ x, b ≤ x → x < c → p x = hi)
    (post : ∀ x, d ≤ x → p x = lo) : WinImg p lo hi T0 ⟨a, b⟩ ⟨c, d⟩ := ⟨ne, pre, mid, post⟩

/-- Token value on a bus. -/
def vN (v : Bool) : Nat := if v then 1 else 0

/-! ## 1. Link stage: the abstract zero-delay run -/

/-- Abstract step of `req_in↓` and of `ack_out↑`: `sw = true` iff `req_in` surely falls before
`ack_out` starts to rise; the two are then ordered that way, otherwise the other way. -/
def kA : Bool → Nat
  | true => 3
  | false => 4
def kB : Bool → Nat
  | true => 4
  | false => 3

/-- Input channel: `req↑` 0, `ack↑` 2, `req↓` `kA`, `ack↓` 6; bus `w0` (junk) at tick 0, then
the token value. -/
def lI (sw v : Bool) (w0 : Nat) : Chan := ⟨tokA 0 (kA sw), tokA 2 6, fun n => if n = 0 then w0 else vN v⟩
/-- Output channel: `req↑` 2, `ack↑` `kB`, `req↓` 6, `ack↓` 7; the latch holds `u` (old
content) until the node opens, then the token value. -/
def lO (sw v : Bool) (u : Nat) : Chan := ⟨tokA 2 6, tokA (kB sw) 7, fun n => if n ≤ 1 then u else vN v⟩
/-- The controller node: rises at step 1, falls at step 5. -/
def lC : Trace := tokA 1 5

open Formal.Net.Ops.Link (Link) in
open Formal.Cells.LinkHandshake (ctlB) in
/-- **The abstract run satisfies C's `Link` gate model exactly.** -/
theorem abs_link (sw v : Bool) (w0 u : Nat) : Link (lI sw v w0) (lO sw v u) lC := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t
    by_cases h : t < 8
    · simp only [lC, lI, lO]; revert t; cases sw <;> decide
    · cases sw <;> simp only [lC, lI, lO, kA, kB] <;> simp (disch := omega) only [tokA_hi] <;> decide
  · intro t
    by_cases h : t < 8
    · simp only [lC, lI]; revert t; decide
    · simp only [lC, lI] <;> simp (disch := omega) only [tokA_hi] <;> decide
  · intro t
    by_cases h : t < 8
    · simp only [lC, lO]; revert t; decide
    · simp only [lC, lO] <;> simp (disch := omega) only [tokA_hi] <;> decide
  · intro t ht
    have : 2 ≤ t := by
      simp only [lC, tokA] at ht; have := of_decide_eq_true ht; omega
    simp only [lO, lI]; split <;> split <;> first | rfl | omega
  · intro t ht
    have : t + 1 ≤ 1 ∨ 6 ≤ t + 1 := by
      simp only [lC, tokA] at ht; have := of_decide_eq_false ht; omega
    simp only [lO]; split <;> split <;> first | rfl | omega
  · rfl
  · rfl
  · rfl

/-- C's four-phase protocol on both abstract channels. -/
theorem abs_proto (sw v : Bool) (w0 u : Nat) : Protocol (lI sw v w0) ∧ Protocol (lO sw v u) := by
  refine ⟨⟨⟨rfl, rfl⟩, fun t => ?_⟩, ⟨⟨rfl, rfl⟩, fun t => ?_⟩⟩
  · by_cases h : t < 8
    · simp only [SendStep, RecvStep, lI]; revert t; cases sw <;> decide
    · cases sw <;> simp only [SendStep, RecvStep, lI, kA] <;> simp (disch := omega) only [tokA_hi] <;> decide
  · by_cases h : t < 8
    · simp only [SendStep, RecvStep, lO]; revert t; cases sw <;> decide
    · cases sw <;> simp only [SendStep, RecvStep, lO, kB] <;> simp (disch := omega) only [tokA_hi] <;> decide

/-- `Held` (C's H_BUNDLE) on both abstract channels. -/
theorem abs_held (sw v : Bool) (w0 u : Nat) : Held (lI sw v w0) ∧ Held (lO sw v u) := by
  refine ⟨fun t h0 _ => ?_, fun t h0 h1 => ?_⟩
  · have : 1 ≤ t := by
      rcases Nat.eq_zero_or_pos t with h | h
      · subst h; cases sw <;> simp [inTx, lI, tokA] at h0
      · exact h
    simp only [lI]; split <;> split <;> first | rfl | omega
  · have : 2 ≤ t := by
      by_cases h : t < 2
      · exfalso; clear h1; simp only [inTx, lO] at h0; revert h0; revert t; cases sw <;> decide
      · omega
    simp only [lO]; split <;> split <;> first | rfl | omega

/-- The latched value: from the node's opening on, the abstract latch holds the token. -/
theorem abs_latched (sw v : Bool) (u : Nat) : ∀ n, 2 ≤ n → (lO sw v u).dat n = vN v := by
  intro n hn; simp only [lO]; split
  · omega
  · rfl

/-! ## 2. Link stage: the physical side -/

/-- The six events of the stage with their abstract steps (req_in↑, node↑, req_in↓, ack_out↑,
node↓, ack_out↓; the node-driven `ack_in`/`req_out` edges are steps 2 and 6, see NOT covered). -/
def linkEvs (P : Par) (sw : Bool) : List (Ev × Nat) :=
  [(⟨P.Ra, P.Ra1⟩, 0), (⟨P.U0, P.U1⟩, 1), (⟨P.Fa, P.Fa1⟩, kA sw), (⟨P.Rb, P.Rb1⟩, kB sw),
   (⟨P.V0, P.V1⟩, 5), (⟨P.Fb, P.Fb1⟩, 7)]

/-- **H_CAUSAL** (environment, NOT a cell row): the receiver's ack does not surely rise before
the node could start to rise, the sender's request does not surely fall before it either, and
the ack does not surely fall before the node could start to fall. Every closed loop with
nonnegative wire delays meets it (the env answers the stage's outputs, which are driven by the
node). These are exactly the precedence obligations `Mono` adds; nothing else is needed. -/
structure Causal (P : Par) : Prop where
  ack_up : P.U0 ≤ P.Rb1
  req_dn : P.U0 ≤ P.Fa1
  ack_dn : P.V0 ≤ P.Fb1

/-- The retiming choice. -/
def swOf (P : Par) : Bool := decide (P.Fa1 < P.Rb)

/-- **The physical stage refines the abstract run.** -/
structure LinkRef (P : Par) (v : Bool) (pd pe : Rd) (a b c q : Int → K3) : Prop where
  mono : Mono (linkEvs P (swOf P))
  req_in : WinImg a .f .t P.Rhi ⟨P.Ra, P.Ra1⟩ ⟨P.Fa, P.Fa1⟩
  ack_out : WinImg b .f .t P.Rhi ⟨P.Rb, P.Rb1⟩ ⟨P.Fb, P.Fb1⟩
  node : WinImg c .f .t P.Rhi ⟨P.U0, P.U1⟩ ⟨P.V0, P.V1⟩
  capt : Capt v P.V0 pe q
  out : ∀ t, P.U1 + pe.hi ≤ t → P.Td + pd.hi ≤ t → q t = kb v

theorem link_mono {P : Par} (S : Wf P) (HC : Causal P) : Mono (linkEvs P (swOf P)) := by
  have s1 := S.hA; have s2 := S.hB; have s5 := S.ha; have s8 := S.hb
  have c1 := HC.ack_up; have c2 := HC.req_dn; have c3 := HC.ack_dn
  simp only [Par.U0, Par.V0] at *
  intro p hp q hq hlt
  simp only [linkEvs, List.mem_cons, List.mem_nil_iff, or_false] at hp hq
  by_cases hs : P.Fa1 < P.Rb
  · have e : swOf P = true := by simp [swOf, hs]
    rw [e] at hp hq
    simp only [kA, kB] at hp hq
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Par.U0, Par.U1, Par.V0, Par.V1] at hlt ⊢ <;> omega
  · have e : swOf P = false := by simp [swOf, hs]
    rw [e] at hp hq
    simp only [kA, kB] at hp hq
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only [Par.U0, Par.U1, Par.V0, Par.V1] at hlt ⊢ <;> omega

/-- The physical part of the refinement is exactly LinkExact's `Spec` plus the env images. -/
theorem linkRef_spec {P : Par} {v : Bool} {pd pe : Rd} {a b c q : Int → K3}
    (R : LinkRef P v pd pe a b c q) : Spec P v pd pe c q :=
  ⟨R.node.ne, R.node.pre, R.node.mid, R.node.post, R.capt, R.out⟩

theorem linkRef_of_spec {P : Par} {v : Bool} {pa pb pq pr pd pe pf : Rd} {r a b d c q : Int → K3}
    (S : Wf P) (HC : Causal P) (Bh : Beh P v pa pb pq pr pd pe pf r a b d c q)
    (Sp : Spec P v pd pe c q) (hFa : P.Ra1 < P.Fa) (hFb : P.Rb1 < P.Fb) :
    LinkRef P v pd pe a b c q :=
  ⟨link_mono S HC,
   ⟨hFa, fun x _ h => Bh.env.a_lo0 x h, fun x h1 h2 => Bh.env.a_hi x h1 h2,
    fun x h => Bh.env.a_lo x h⟩,
   ⟨hFb, fun x _ h => Bh.env.b_lo0 x h, fun x h1 h2 => Bh.env.b_hi x h1 h2,
    fun x h => Bh.env.b_lo x h⟩,
   ⟨Sp.nonempty, Sp.rst, Sp.hi, Sp.lo⟩, Sp.capt, Sp.out⟩

/-- The two request/ack pulses are nonempty under the race rows. -/
theorem pulses_ne {P : Par} (S : Wf P) (H : Conj P) : P.Ra1 < P.Fa ∧ P.Rb1 < P.Fb := by
  have s1 := S.hA; have s2 := S.hB; have s3 := S.hQ; have s5 := S.ha; have s8 := S.hb
  have h1 := H.H_RACE_UP; have h2 := H.H_RACE_DN
  simp only [Par.U1, Par.Rel, Par.V1] at *
  omega

/-- **Headline (link stage).** Under the scope `Wf`, the six `bd_link.stage` rows (`Conj`) and
`Causal`, EVERY physical behaviour of one `bd_link` stage (any read maps in the box, any
admissible environment and data, any power-up) refines the explicit zero-delay run
`lI/lO/lC`, which satisfies C's `Link`, `Protocol` and `Held` on both channels; the latch holds
the token value `v` physically (`capt`, `out`) and abstractly (`abs_latched`). -/
theorem link_refines {P : Par} {v : Bool} {pa pb pq pr pd pe pf : Rd} {r a b d c q : Int → K3}
    (S : Wf P) (H : Conj P) (HC : Causal P) (Bh : Beh P v pa pb pq pr pd pe pf r a b d c q)
    (w0 u : Nat) :
    Formal.Net.Ops.Link.Link (lI (swOf P) v w0) (lO (swOf P) v u) lC ∧
    Protocol (lI (swOf P) v w0) ∧ Protocol (lO (swOf P) v u) ∧
    Held (lI (swOf P) v w0) ∧ Held (lO (swOf P) v u) ∧
    LinkRef P v pd pe a b c q ∧
    (∀ n, 2 ≤ n → (lO (swOf P) v u).dat n = vN v) := by
  have hp := pulses_ne S H
  exact ⟨abs_link _ _ _ _, (abs_proto _ _ w0 u).1, (abs_proto _ _ w0 u).2, (abs_held _ _ w0 u).1,
    (abs_held _ _ w0 u).2, linkRef_of_spec S HC Bh (sufficient S H Bh) hp.1 hp.2,
    abs_latched _ _ _⟩

/-- Every behaviour refines. -/
def RefinesAll (P : Par) (v : Bool) : Prop :=
  ∀ pa pb pq pr pd pe pf r a b d c q, Beh P v pa pb pq pr pd pe pf r a b d c q →
    LinkRef P v pd pe a b c q

/-- **Exact (link stage).** Under `Wf`, `Split` and `Causal`: every physical behaviour refines
the zero-delay run **iff** the six `bd_link.stage` rows hold. -/
theorem link_ref_iff {P : Par} {v : Bool} (S : Wf P) (hs : Split P) (HC : Causal P) :
    RefinesAll P v ↔ Conj P := by
  constructor
  · intro h
    exact (exact S hs).1 fun pa pb pq pr pd pe pf r a b d c q Bh =>
      linkRef_spec (h pa pb pq pr pd pe pf r a b d c q Bh)
  · intro H pa pb pq pr pd pe pf r a b d c q Bh
    exact (link_refines S H HC Bh 0 0).2.2.2.2.2.1

/-- The six 1-tick violations meet the environment's causality (so `Causal` is not what
breaks them). -/
theorem Pv_causal (i : Fin 6) : Causal (Pv i) := by
  have h : (Pv i).U0 ≤ (Pv i).Rb1 ∧ (Pv i).U0 ≤ (Pv i).Fa1 ∧ (Pv i).V0 ≤ (Pv i).Fb1 := by
    revert i; decide
  exact ⟨h.1, h.2.1, h.2.2⟩

/-- **Counter-runs (link stage).** For each `bd_link.stage` row `i`, at `Pv i` (that row
violated by one tick, every other row, Wf, Split and Causal met) some physical behaviour has NO
refinement onto the zero-delay run. -/
theorem link_ref_breaks (v : Bool) (i : Fin 6) :
    Wf (Pv i) ∧ Split (Pv i) ∧ Causal (Pv i) ∧
    ∃ pa pb pq pr pd pe pf r a b d c q, Beh (Pv i) v pa pb pq pr pd pe pf r a b d c q ∧
      ¬ LinkRef (Pv i) v pd pe a b c q := by
  refine ⟨Pv_wf i, Pv_split i, Pv_causal i, ?_⟩
  have h := Pv_breaks v i
  unfold SafeLink at h
  apply Classical.byContradiction
  intro hn
  apply h
  intro pa pb pq pr pd pe pf r a b d c q Bh
  apply linkRef_spec
  apply Classical.byContradiction
  intro hr
  exact hn ⟨pa, pb, pq, pr, pd, pe, pf, r, a, b, d, c, q, Bh, hr⟩

theorem P0_causal : Causal P0 := ⟨by decide, by decide, by decide⟩

/-- **Non-vacuity (link stage).** At `P0` every hypothesis of `link_refines` holds and a
behaviour exists. -/
theorem link_witness (v : Bool) :
    Wf P0 ∧ Conj P0 ∧ Causal P0 ∧
    ∃ pa pb pq pr pd pe pf r a b d c q, Beh P0 v pa pb pq pr pd pe pf r a b d c q ∧
      LinkRef P0 v pd pe a b c q := by
  obtain ⟨-, -, -, -, pa, pb, pq, pr, pd, pe, pf, r, a, b, d, c, q, Bh, -⟩ := witness v
  exact ⟨P0_wf, P0_conj, P0_causal, pa, pb, pq, pr, pd, pe, pf, r, a, b, d, c, q, Bh,
    (link_refines P0_wf P0_conj P0_causal Bh 0 0).2.2.2.2.2.1⟩

/-! ## 3. Steer: the abstract zero-delay run -/

section steer
open Formal.Net.Ops.Steer (Steer)
open Formal.Cells.LibCtlMergeMux (or2B or2_spec)

/-- Joined input: `req↑` 0, `ack↑` 3, `req↓` 4, `ack↓` 7; the bus carries the token `J`. -/
def sJ (J : Nat) : Chan := ⟨tokA 0 4, tokA 3 7, fun _ => J⟩
/-- Selected branch: `req↑` 1, `ack↑` 2, `req↓` 5, `ack↓` 6. -/
def sOn (f : Nat → Nat) (J : Nat) : Chan := ⟨tokA 1 5, tokA 2 6, fun _ => f J⟩
/-- Unselected branch: idle. -/
def sOff (f : Nat → Nat) (J : Nat) : Chan := ⟨fun _ => false, fun _ => false, fun _ => f J⟩
def sOut (v : Bool) (f : Nat → Nat) (J : Nat) (b : Bool) : Chan := if b = v then sOn f J else sOff f J

/-- **The abstract run satisfies C's `Steer` gate model exactly** (any `sel`, `f`; the token's
condition `sel J` is the select value `v`). -/
theorem sOut_req (v : Bool) (f : Nat → Nat) (J : Nat) (b : Bool) :
    (sOut v f J b).req = if b = v then tokA 1 5 else fun _ => false := by
  unfold sOut; split <;> rfl
theorem sOut_ack (v : Bool) (f : Nat → Nat) (J : Nat) (b : Bool) :
    (sOut v f J b).ack = if b = v then tokA 2 6 else fun _ => false := by
  unfold sOut; split <;> rfl

theorem abs_steer {sel : Nat → Bool} {f : Nat → Nat} {J : Nat} {v : Bool} (hJ : sel J = v) :
    Steer sel f (sJ J) (sOut v f J) := by
  refine ⟨fun b t => ?_, fun t => ?_, fun b t => ?_, rfl, fun b => ?_⟩
  · simp only [sJ, hJ, sOut_req]
    by_cases h : t < 8
    · revert t; cases b <;> cases v <;> decide
    · cases b <;> cases v <;> simp (disch := omega) [tokA_hi]
  · simp only [sJ, sOut_ack]
    by_cases h : t < 8
    · revert t; cases v <;> decide
    · cases v <;> simp (disch := omega) [tokA_hi]
  · simp only [sOut, sJ]; split <;> rfl
  · rw [sOut_req]; split <;> rfl

theorem abs_steer_proto (v : Bool) (f : Nat → Nat) (J : Nat) :
    Protocol (sJ J) ∧ ∀ b, Protocol (sOut v f J b) := by
  refine ⟨⟨⟨rfl, rfl⟩, fun t => ?_⟩, fun b => ?_⟩
  · simp only [SendStep, RecvStep, sJ]
    by_cases h : t < 8
    · revert t; decide
    · simp (disch := omega) only [tokA_hi]; decide
  · simp only [sOut]; split
    · refine ⟨⟨rfl, rfl⟩, fun t => ?_⟩
      simp only [SendStep, RecvStep, sOn]
      by_cases h : t < 8
      · revert t; decide
      · simp (disch := omega) only [tokA_hi]; decide
    · exact ⟨⟨rfl, rfl⟩, fun t => ⟨fun h => absurd rfl h, fun h => absurd rfl h⟩⟩

theorem abs_steer_held (v : Bool) (f : Nat → Nat) (J : Nat) :
    Held (sJ J) ∧ ∀ b, Held (sOut v f J b) := by
  refine ⟨fun _ _ _ => rfl, fun b => ?_⟩
  simp only [sOut]; split
  · exact fun _ _ _ => rfl
  · exact fun _ _ _ => rfl

/-- **Retiming-independent**: in EVERY run of C's `Steer` (any traces, any retiming) in which the
select reads `v` whenever the joined request is high, the unselected branch never requests. -/
theorem steer_unsel_never {sel : Nat → Bool} {f : Nat → Nat} {j : Chan} {out : Bool → Chan}
    (S : Steer sel f j out) {v : Bool} (hv : ∀ t, j.req t = true → sel (j.dat t) = v) :
    ∀ t, (out (!v)).req t = false := by
  intro t
  induction t with
  | zero => exact S.initO _
  | succ t ih =>
    by_cases hm : (out (!v)).req (t + 1) = (out (!v)).req t
    · rw [hm, ih]
    · rw [S.lut _ t hm]
      cases hr : j.req t
      · rfl
      · rw [hv t hr]; cases v <;> rfl

/-! ## 4. Steer: the physical side -/

/-- Physical branch request `b` (`LibGapSteer`'s H_PIN_READ at the real INIT). -/
def sPhys (R F : Int) (s : Int → Bool) (pr ps : Bool → Rd) (b : Bool) (t : Int) : Bool :=
  outB b (pulse R F ((pr b).σ t)) (s ((ps b).σ t))

/-- Physical `uack` (real INIT `or2B`) reading the two branch acknowledges through `pa`. -/
def sAck (kk : Bool → Int → Bool) (pa : Bool → Rd) (t : Int) : Bool :=
  or2B (kk false ((pa false).σ t)) (kk true ((pa true).σ t))

/-- The eight events (j.req↑, O_v↑, ack_v↑, uack↑, j.req↓, O_v↓, ack_v↓, uack↓). -/
def steerEvs (R F Kr Kr1 Kf Kf1 : Int) (pr pa : Rd) : List (Ev × Nat) :=
  [(⟨R, R⟩, 0), (⟨R + pr.lo, R + pr.hi⟩, 1), (⟨Kr, Kr1⟩, 2), (⟨Kr + pa.lo, Kr1 + pa.hi⟩, 3),
   (⟨F, F⟩, 4), (⟨F + pr.lo, F + pr.hi⟩, 5), (⟨Kf, Kf1⟩, 6), (⟨Kf + pa.lo, Kf1 + pa.hi⟩, 7)]

/-- **The physical steer refines the abstract run.** -/
structure SteerRef (v : Bool) (R F Kr Kr1 Kf Kf1 : Int) (s : Int → Bool) (pr ps pa : Bool → Rd)
    (kk : Bool → Int → Bool) : Prop where
  mono : Mono (steerEvs R F Kr Kr1 Kf Kf1 (pr v) (pa v))
  req : WinImg (pulse R F) false true 0 ⟨R, R⟩ ⟨F, F⟩
  sel_out : WinImg (sPhys R F s pr ps v) false true 0 ⟨R + (pr v).lo, R + (pr v).hi⟩
    ⟨F + (pr v).lo, F + (pr v).hi⟩
  unsel : ∀ t, sPhys R F s pr ps (!v) t = false
  ack : WinImg (kk v) false true 0 ⟨Kr, Kr1⟩ ⟨Kf, Kf1⟩
  uack : WinImg (sAck kk pa) false true 0 ⟨Kr + (pa v).lo, Kr1 + (pa v).hi⟩
    ⟨Kf + (pa v).lo, Kf1 + (pa v).hi⟩

theorem Rd.lo_le_hi (p : Rd) : p.lo ≤ p.hi := by have := p.ge 0; have := p.le 0; omega

/-- **H_SCAUSAL** (environment, not a cell row): the selected receiver's ack does not surely rise
before the branch request could; the sender's request does not surely fall before `uack` could
rise; the ack does not surely fall before the branch request could fall. -/
structure SCausal (R F Kr Kr1 Kf Kf1 : Int) (pr pa : Rd) : Prop where
  ack_up : R + pr.lo ≤ Kr1
  req_dn : Kr + pa.lo ≤ F
  ack_dn : F + pr.lo ≤ Kf1
  /-- the sender's request does not surely fall before the branch request could rise. -/
  req_dn_out : R + pr.lo ≤ F

/-- **Headline (steer).** Hypotheses: the two `bd_steer.bundled_s_*` rows for BOTH outputs
(read-map form; the box form implies it), the env wires (one token on the selected branch's ack,
the unselected ack low: its receiver gets no request), `H_REQ_WIDTH` / `H_ACK_WIDTH` (the pulses
outlast their read skews: the image's high phase is nonempty), nonnegative read delays and
`SCausal`. Then the physical steer refines the explicit run, which satisfies C's `Steer`,
`Protocol` and `Held` on all three channels. -/
theorem steer_refines {sel : Nat → Bool} {f : Nat → Nat} {J : Nat} {v : Bool} (hJ : sel J = v)
    {R F S0 S1 Kr Kr1 Kf Kf1 : Int} {s : Int → Bool} {pr ps pa : Bool → Rd}
    {kk : Bool → Int → Bool}
    (H_S_STABLE : Stable s v S0 S1)
    (H_SETUP_PIN : ∀ b, S0 + (ps b).hi ≤ R + (pr b).lo)
    (H_HOLD_PIN : ∀ b, F + (pr b).hi ≤ S1 + (ps b).lo)
    (H_ACK : (∀ t, t < Kr → kk v t = false) ∧ (∀ t, Kr1 ≤ t → t < Kf → kk v t = true) ∧
      (∀ t, Kf1 ≤ t → kk v t = false))
    (H_UNSEL_ACK : ∀ t, kk (!v) t = false)
    (hK : Kr ≤ Kr1 ∧ Kr1 ≤ Kf ∧ Kf ≤ Kf1)
    (H_REQ_WIDTH : R + (pr v).hi < F + (pr v).lo)
    (H_ACK_WIDTH : Kr1 + (pa v).hi < Kf + (pa v).lo)
    (H_DLY : 0 ≤ (pr v).lo ∧ 0 ≤ (pa v).lo)
    (HC : SCausal R F Kr Kr1 Kf Kf1 (pr v) (pa v)) :
    Steer sel f (sJ J) (sOut v f J) ∧ Protocol (sJ J) ∧ (∀ b, Protocol (sOut v f J b)) ∧
    Held (sJ J) ∧ (∀ b, Held (sOut v f J b)) ∧
    SteerRef v R F Kr Kr1 Kf Kf1 s pr ps pa kk := by
  have hRF : R < F := by have := Rd.lo_le_hi (pr v); omega
  have spec : ∀ b, SpecOK b v (pr b) (ps b) R F s := fun b =>
    steer_pin_ok b v _ _ R F S0 S1 s H_S_STABLE (H_SETUP_PIN b) (H_HOLD_PIN b)
  have hsel : ∀ t, sPhys R F s pr ps v t = pulse R F ((pr v).σ t) := by
    intro t; have := spec v t; simp only [sPhys]; rw [this]; cases pulse R F _ <;> simp
  have hun : ∀ t, sPhys R F s pr ps (!v) t = false := by
    intro t; have := spec (!v) t; simp only [sPhys]; rw [this]; cases v <;> simp
  have hack : ∀ t, sAck kk pa t = kk v ((pa v).σ t) := by
    intro t; simp only [sAck, or2_spec]
    cases v
    · rw [show kk (!false) = kk true from rfl] at H_UNSEL_ACK; rw [H_UNSEL_ACK]; simp
    · rw [show kk (!true) = kk false from rfl] at H_UNSEL_ACK; rw [H_UNSEL_ACK]; simp
  have h1 := Rd.lo_le_hi (pr v); have h2 := Rd.lo_le_hi (pa v)
  have c1 := HC.ack_up; have c2 := HC.req_dn; have c3 := HC.ack_dn; have c4 := HC.req_dn_out
  obtain ⟨a1, a2, a3⟩ := H_ACK
  refine ⟨abs_steer hJ, (abs_steer_proto v f J).1, (abs_steer_proto v f J).2,
    (abs_steer_held v f J).1, (abs_steer_held v f J).2, ?_, ?_, ?_, hun, ?_, ?_⟩
  · intro p hp q hq hlt
    simp only [steerEvs, List.mem_cons, List.mem_nil_iff, or_false] at hp hq
    rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only at hlt ⊢ <;> omega
  · exact winImg_of hRF (fun x _ h => by simp [pulse]; omega) (fun x h1 h2 => by simp [pulse]; omega)
      (fun x h => by simp [pulse]; omega)
  · refine winImg_of H_REQ_WIDTH (fun x _ h => ?_) (fun x hx1 hx2 => ?_) (fun x h => ?_) <;> rw [hsel] <;>
      have g1 := (pr v).ge x <;> have g2 := (pr v).le x <;> simp [pulse] <;> omega
  · exact winImg_of (by omega) (fun x _ h => a1 x h) (fun x h1 h2 => a2 x h1 h2) (fun x h => a3 x h)
  · refine winImg_of H_ACK_WIDTH (fun x _ h => ?_) (fun x hx1 hx2 => ?_) (fun x h => ?_) <;> rw [hack] <;>
      have g1 := (pa v).ge x <;> have g2 := (pa v).le x
    · exact a1 _ (by omega)
    · exact a2 _ (by omega) (by omega)
    · exact a3 _ (by omega)

/-- **Counter-run (setup row violated, by 100 ps).** LibGapSteer's `spurious_token`: req
`[1000, 2000)` read through 300 ps, select `v = 1` only from 800, read through 600 ps. The
unselected branch `O5` is high at 1300, so NO retiming refines it (`steer_unsel_never`). -/
theorem steer_setup_breaks (Kr Kr1 Kf Kf1 : Int) (pa : Bool → Rd) (kk : Bool → Int → Bool) :
    ¬ SteerRef true 1000 2000 Kr Kr1 Kf Kf1 (LibGapSteer.sAdv true 800 5000)
      (fun _ => Rd.const 300) (fun _ => Rd.const 600) pa kk := by
  intro h
  have := h.unsel 1300
  revert this; decide

/-- **Counter-run (hold row violated).** LibGapSteer's `late_hold_glitch`: req `[1000, 2000)`
read through 600 ps, select leaves `v = 1` at 2100, read through 300 ps: the unselected branch is
high at 2599. -/
theorem steer_hold_breaks (Kr Kr1 Kf Kf1 : Int) (pa : Bool → Rd) (kk : Bool → Int → Bool) :
    ¬ SteerRef true 1000 2000 Kr Kr1 Kf Kf1 (LibGapSteer.sAdv true 0 2100)
      (fun _ => Rd.const 600) (fun _ => Rd.const 300) pa kk := by
  intro h
  have := h.unsel 2599
  revert this; decide

/-- **Non-vacuity (steer).** Concrete numbers meeting every hypothesis of `steer_refines`
(LibGapSteer's witness: req `[1000, 3000)` through 300, select `[500, 4000)` through 450; the
selected receiver acks on `[2000, 3500)`, the OR reads through 100). -/
theorem steer_witness :
    let pr : Bool → Rd := fun _ => Rd.const 300
    let ps : Bool → Rd := fun _ => Rd.const 450
    let pa : Bool → Rd := fun _ => Rd.const 100
    let kk : Bool → Int → Bool := fun b t => b && pulse 2000 3500 t
    Steer (fun n => n == 1) id (sJ 1) (sOut true id 1) ∧
    SteerRef true 1000 3000 2000 2000 3500 3500 (LibGapSteer.sAdv true 500 4000) pr ps pa kk := by
  intro pr ps pa kk
  have h := steer_refines (sel := fun n => n == 1) (f := id) (J := 1) (v := true) rfl
    (R := 1000) (F := 3000) (S0 := 500) (S1 := 4000) (Kr := 2000) (Kr1 := 2000) (Kf := 3500)
    (Kf1 := 3500) (s := LibGapSteer.sAdv true 500 4000) (pr := pr) (ps := ps) (pa := pa) (kk := kk)
    (LibGapSteer.sAdv_stable true 500 4000)
    (fun b => by simp [pr, ps, Rd.const]) (fun b => by simp [pr, ps, Rd.const])
    ⟨fun t ht => by simp [kk, pulse]; omega, fun t h1 h2 => by simp [kk, pulse]; omega,
     fun t ht => by simp [kk, pulse]; omega⟩
    (fun t => by simp [kk]) (by decide) (by simp [pr, Rd.const]) (by simp [pa, Rd.const])
    ⟨by simp [pr, Rd.const], by simp [pa, Rd.const]⟩
    ⟨by simp [pr, Rd.const], by simp [pa, Rd.const], by simp [pr, Rd.const], by simp [pr, Rd.const]⟩
  exact ⟨h.1, h.2.2.2.2.2⟩

end steer

/-! ## 5. Mux join: the abstract zero-delay run (y selected, x waiting) -/

section mux
open Formal.Net.Ops.Mux (Mux)
open Formal.Cells.LibGapMux (LutEq Rest JSpec join_pin_ok unsel_low int_ind jB specB run run_luteq
  run_rest jf wrong_branch_latched)

/-- Steps of `y.req↑`, `c.req↑` (`sw`: the control's window starts first) and of `c.req↓`,
`y.req↓` (`sw2`: the control's fall window starts first). -/
def mY : Bool → Nat
  | true => 2
  | false => 1
def mC : Bool → Nat
  | true => 1
  | false => 2
def fC : Bool → Nat
  | true => 7
  | false => 8
def fY : Bool → Nat
  | true => 8
  | false => 7

/-- x: a waiting token (offered at step 0, never served in this transaction). -/
def mx (X0 : Nat) : Chan := ⟨fun n => decide (0 < n), fun _ => false, fun _ => X0⟩
/-- y (the selected input): offered, served at step 6, released, ack falls at 12. -/
def my (sw sw2 : Bool) (Y0 : Nat) : Chan := ⟨tokA (mY sw) (fY sw2), tokA 6 12, fun _ => Y0⟩
/-- The control channel (its bus is the select token `C0`). -/
def mc (sw sw2 : Bool) (C0 : Nat) : Chan := ⟨tokA (mC sw) (fC sw2), tokA 6 12, fun _ => C0⟩
/-- The output: `req↑` 4, `ack↑` 5, `req↓` 10, `ack↓` 11; bus = C's `dat` equation. -/
def mz (sel : Nat → Bool) (X0 Y0 C0 : Nat) : Chan :=
  ⟨tokA 4 10, tokA 5 11, fun _ => if sel C0 then Y0 else X0⟩
def j0A : Trace := fun _ => false
def j1A : Trace := tokA 3 9

/-- **The abstract run satisfies C's whole `Mux` gate model exactly.** -/
theorem abs_mux {sel : Nat → Bool} {C0 : Nat} (hC : sel C0 = true) (sw sw2 : Bool) (X0 Y0 : Nat) :
    Mux sel (mx X0) (my sw sw2 Y0) (mc sw sw2 C0) (mz sel X0 Y0 C0) j0A j1A := by
  refine ⟨fun t h => absurd rfl h, fun t => ?_, fun t => ?_, fun t h => absurd rfl h, fun t => ?_,
    fun t => ?_, fun t => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩
  · simp only [my, mc, j1A, hC]
    by_cases h : t < 14
    · revert t; cases sw <;> cases sw2 <;> decide
    · cases sw <;> cases sw2 <;> simp (disch := omega) [tokA_hi, mY, mC, fY, fC]
  · simp only [mz, j0A, j1A]
    by_cases h : t < 14
    · revert t; decide
    · simp (disch := omega) [tokA_hi]
  · simp only [my, mz, j1A]
    by_cases h : t < 14
    · revert t; decide
    · simp (disch := omega) [tokA_hi]
  · simp only [mc, mz]
    by_cases h : t < 14
    · revert t; decide
    · simp (disch := omega) [tokA_hi]

theorem abs_mux_proto (sel : Nat → Bool) (sw sw2 : Bool) (X0 Y0 C0 : Nat) :
    Protocol (mx X0) ∧ Protocol (my sw sw2 Y0) ∧ Protocol (mc sw sw2 C0) ∧
      Protocol (mz sel X0 Y0 C0) := by
  refine ⟨⟨⟨rfl, rfl⟩, fun t => ?_⟩, ⟨⟨rfl, rfl⟩, fun t => ?_⟩, ⟨⟨rfl, rfl⟩, fun t => ?_⟩,
    ⟨⟨rfl, rfl⟩, fun t => ?_⟩⟩
  · simp only [SendStep, RecvStep, mx]
    by_cases h : t < 2
    · revert t; decide
    · refine ⟨fun h' => absurd ?_ h', fun h' => absurd rfl h'⟩
      simp; omega
  · simp only [SendStep, RecvStep, my]
    by_cases h : t < 14
    · revert t; cases sw <;> cases sw2 <;> decide
    · cases sw <;> cases sw2 <;> simp (disch := omega) [tokA_hi, mY, fY]
  · simp only [SendStep, RecvStep, mc]
    by_cases h : t < 14
    · revert t; cases sw <;> cases sw2 <;> decide
    · cases sw <;> cases sw2 <;> simp (disch := omega) [tokA_hi, mC, fC]
  · simp only [SendStep, RecvStep, mz]
    by_cases h : t < 14
    · revert t; decide
    · simp (disch := omega) [tokA_hi]

theorem abs_mux_held (sel : Nat → Bool) (sw sw2 : Bool) (X0 Y0 C0 : Nat) :
    Held (mx X0) ∧ Held (my sw sw2 Y0) ∧ Held (mc sw sw2 C0) ∧ Held (mz sel X0 Y0 C0) :=
  ⟨fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl, fun _ _ _ => rfl⟩

/-- **Retiming-independent**: in EVERY run of C's `Mux` in which the select token reads 1
whenever the control request is high, the x-side join `j0` never fires (even with x waiting). -/
theorem mux_unsel_never {sel : Nat → Bool} {x y c z : Chan} {j0 j1 : Trace}
    (M : Mux sel x y c z j0 j1) (hs : ∀ t, c.req t = true → sel (c.dat t) = true) :
    ∀ t, j0 t = false := by
  intro t
  induction t with
  | zero => exact M.i0
  | succ t ih =>
    by_cases hm : j0 (t + 1) = j0 t
    · rw [hm, ih]
    · have := (M.cj0 t hm).2
      cases hr : c.req t
      · rw [hr] at this; simp at this; exact this
      · rw [hr, hs t hr] at this; simp at this; exact this

/-! ## 6. Mux join: the physical side -/

/-- The selected join's input-derived windows (request read `pr`, control read `pc`). -/
def jU0 (Yr Cr : Int) (pr pc : Rd) : Int := max (Yr + pr.lo) (Cr + pc.lo)
def jU1 (Yr1 Cr : Int) (pr pc : Rd) : Int := max (Yr1 + pr.hi) (Cr + pc.hi)
def jRel (Yf Cf : Int) (pr pc : Rd) : Int := min (Yf + pr.lo) (Cf + pc.lo)
def jV0 (Yf Cf : Int) (pr pc : Rd) : Int := max (Yf + pr.lo) (Cf + pc.lo)
def jV1 (Yf1 Cf : Int) (pr pc : Rd) : Int := max (Yf1 + pr.hi) (Cf + pc.hi)

def muxEvs (Xr Xr1 Yr Yr1 Yf Yf1 Cr Cf : Int) (pr pc : Rd) : List (Ev × Nat) :=
  [(⟨Xr, Xr1⟩, 0), (⟨Cr, Cr⟩, mC (decide (Cr ≤ Yr))), (⟨Yr, Yr1⟩, mY (decide (Cr ≤ Yr))),
   (⟨jU0 Yr Cr pr pc, jU1 Yr1 Cr pr pc⟩, 3), (⟨Cf, Cf⟩, fC (decide (Cf ≤ Yf))),
   (⟨Yf, Yf1⟩, fY (decide (Cf ≤ Yf))), (⟨jV0 Yf Cf pr pc, jV1 Yf1 Cf pr pc⟩, 9)]

/-- **The physical joins refine the abstract run** (inputs x, y, ctl_req, both joins). -/
structure MuxRef (Xr Xr1 Yr Yr1 Yf Yf1 Cr Cf : Int) (pr pc : Rd) (x y j0 j1 : Int → Bool) :
    Prop where
  mono : Mono (muxEvs Xr Xr1 Yr Yr1 Yf Yf1 Cr Cf pr pc)
  x_in : (∀ t, t < Xr → x t = false) ∧ (∀ t, Xr1 ≤ t → x t = true)
  y_in : WinImg y false true 0 ⟨Yr, Yr1⟩ ⟨Yf, Yf1⟩
  c_in : WinImg (pulse Cr Cf) false true 0 ⟨Cr, Cr⟩ ⟨Cf, Cf⟩
  j_sel : WinImg j1 false true 0 ⟨jU0 Yr Cr pr pc, jU1 Yr1 Cr pr pc⟩
    ⟨jV0 Yf Cf pr pc, jV1 Yf1 Cf pr pc⟩
  j_unsel : ∀ t, j0 t = false

/-- **H_MCAUSAL** (environment, not a cell row): the waiting token was offered no later than the
control and the selected request could be seen; neither the control nor the selected request
surely falls before the selected join could fire (both falls answer `z_ack↑`, which follows
`j1↑`). -/
structure MCausal (Xr Yr Yr1 Yf1 Cr Cf : Int) (pr pc : Rd) : Prop where
  x_c : Xr ≤ Cr
  x_y : Xr ≤ Yr1
  c_dn : jU0 Yr Cr pr pc ≤ Cf
  y_dn : jU0 Yr Cr pr pc ≤ Yf1

theorem sp1 : ∀ c : Bool, specB true true false c false = false := by decide
theorem sp2 : ∀ r : Bool, specB true true r false false = false := by decide
theorem sp3 : ∀ q : Bool, specB true true true true q = true := by decide
theorem sp4 : ∀ c : Bool, specB true true true c true = true := by decide
theorem sp5 : ∀ r : Bool, specB true true r true true = true := by decide
theorem sp6 : ∀ q : Bool, specB true true false false q = false := by decide

/-- The selected join (uj1) is the window image of the abstract `j1`, given its spec. -/
theorem sel_join_img {pr pc pq : Rd} {Yr Yr1 Yf Yf1 Cr Cf : Int} {y j : Int → Bool}
    (hS : JSpec true true pr pc pq y (pulse Cr Cf) j) (hR : Rest j)
    (hy : (∀ t, t < Yr → y t = false) ∧ (∀ t, Yr1 ≤ t → t < Yf → y t = true) ∧
      (∀ t, Yf1 ≤ t → y t = false))
    (hd : 0 ≤ pr.lo ∧ 0 ≤ pc.lo ∧ 1 ≤ pq.lo) (hc : 0 ≤ Cr)
    (H_JOIN_RACE : jU1 Yr1 Cr pr pc + pq.hi ≤ jRel Yf Cf pr pc) :
    WinImg j false true 0 ⟨jU0 Yr Cr pr pc, jU1 Yr1 Cr pr pc⟩ ⟨jV0 Yf Cf pr pc, jV1 Yf1 Cf pr pc⟩ := by
  obtain ⟨y1, y2, y3⟩ := hy
  have l1 := Rd.lo_le_hi pr; have l2 := Rd.lo_le_hi pc; have l3 := Rd.lo_le_hi pq
  simp only [jU0, jU1, jRel, jV0, jV1] at *
  refine winImg_of (by omega) ?_ ?_ ?_
  · intro x _ hx
    revert hx
    apply int_ind (fun t => t < max (Yr + pr.lo) (Cr + pc.lo) → j t = false)
      (fun t ht _ => hR t ht)
    intro t ht ih h1
    have g1 := pr.ge t; have g2 := pr.le t; have g3 := pc.ge t; have g4 := pc.le t
    have g5 := pq.ge t; have g6 := pq.le t
    rw [hS t ht, ih _ (by omega) (by omega)]
    by_cases h : t < Yr + pr.lo
    · rw [y1 _ (by omega)]; exact sp1 _
    · rw [show pulse Cr Cf (pc.σ t) = false by simp [pulse]; omega]; exact sp2 _
  · intro x hx1 hx2
    revert hx1 hx2
    apply int_ind (fun t => max (Yr1 + pr.hi) (Cr + pc.hi) ≤ t →
      t < max (Yf + pr.lo) (Cf + pc.lo) → j t = true) (fun t ht h _ => by omega)
    intro t ht ih h1 h2
    have g1 := pr.ge t; have g2 := pr.le t; have g3 := pc.ge t; have g4 := pc.le t
    have g5 := pq.ge t; have g6 := pq.le t
    rw [hS t ht]
    by_cases h : t < min (Yf + pr.lo) (Cf + pc.lo)
    · rw [y2 _ (by omega) (by omega), show pulse Cr Cf (pc.σ t) = true by simp [pulse]; omega]
      exact sp3 _
    · rw [ih _ (by omega) (by omega) (by omega)]
      by_cases h' : t < Yf + pr.lo
      · rw [y2 _ (by omega) (by omega)]; exact sp4 _
      · rw [show pulse Cr Cf (pc.σ t) = true by simp [pulse]; omega]; exact sp5 _
  · intro x hx
    have g1 := pr.ge x; have g3 := pc.ge x
    have hx0 : 0 ≤ x := by omega
    rw [hS x hx0, y3 _ (by omega), show pulse Cr Cf (pc.σ x) = false by simp [pulse]; omega]
    exact sp6 _

/-- **Headline (mux join).** Hypotheses: per join `k ∈ {uj0, uj1}` the two
`bd_mux.bundled_s_*` rows (read-map form), `H_JOIN_RACE` (the selected join's own-feedback race:
it settles high through its feedback before the first release can be read; read-map form of
`bd_mux.uj_env_latency_*`), the env wires (ctl_req one pulse `[Cr, Cf)` with `0 ≤ Cr`; y one
token; x a waiting token; select `1` on `[S0, S1)`, arbitrary elsewhere), nonnegative read delays,
feedback delays `≥ 1`, H_RESET, and `MCausal`. Then the explicit run satisfies C's `Mux`
(every field), `Protocol` on x, y, ctl, z and `Held` on all four, and the physical inputs and
BOTH joins refine it: uj1 is a clean window token, uj0 stays 0. -/
theorem mux_refines {sel : Nat → Bool} {C0 : Nat} (hC : sel C0 = true) (X0 Y0 : Nat)
    {Xr Xr1 Yr Yr1 Yf Yf1 Cr Cf S0 S1 : Int} {pr0 pc0 ps0 pq0 pr1 pc1 ps1 pq1 : Rd}
    {x y s j0 j1 : Int → Bool}
    (H_S_STABLE : Stable s true S0 S1)
    (hL0 : LutEq false pr0 pc0 ps0 pq0 x (pulse Cr Cf) s j0)
    (hL1 : LutEq true pr1 pc1 ps1 pq1 y (pulse Cr Cf) s j1) (hR0 : Rest j0) (hR1 : Rest j1)
    (H_SETUP0 : S0 + ps0.hi ≤ Cr + pc0.lo) (H_HOLD0 : Cf + pc0.hi ≤ S1 + ps0.lo)
    (H_SETUP1 : S0 + ps1.hi ≤ Cr + pc1.lo) (H_HOLD1 : Cf + pc1.hi ≤ S1 + ps1.lo)
    (H_JOIN_RACE : jU1 Yr1 Cr pr1 pc1 + pq1.hi ≤ jRel Yf Cf pr1 pc1)
    (hx : (∀ t, t < Xr → x t = false) ∧ (∀ t, Xr1 ≤ t → x t = true)) (hX : Xr ≤ Xr1)
    (hy : (∀ t, t < Yr → y t = false) ∧ (∀ t, Yr1 ≤ t → t < Yf → y t = true) ∧
      (∀ t, Yf1 ≤ t → y t = false)) (hY : Yr ≤ Yr1 ∧ Yr1 < Yf ∧ Yf ≤ Yf1)
    (hc : 0 ≤ Cr ∧ Cr < Cf)
    (hd : 0 ≤ pr1.lo ∧ 0 ≤ pc1.lo ∧ 1 ≤ pq0.lo ∧ 1 ≤ pq1.lo)
    (HC : MCausal Xr Yr Yr1 Yf1 Cr Cf pr1 pc1) :
    let sw := decide (Cr ≤ Yr)
    let sw2 := decide (Cf ≤ Yf)
    Mux sel (mx X0) (my sw sw2 Y0) (mc sw sw2 C0) (mz sel X0 Y0 C0) j0A j1A ∧
    (Protocol (mx X0) ∧ Protocol (my sw sw2 Y0) ∧ Protocol (mc sw sw2 C0) ∧
      Protocol (mz sel X0 Y0 C0)) ∧
    (Held (mx X0) ∧ Held (my sw sw2 Y0) ∧ Held (mc sw sw2 C0) ∧ Held (mz sel X0 Y0 C0)) ∧
    MuxRef Xr Xr1 Yr Yr1 Yf Yf1 Cr Cf pr1 pc1 x y j0 j1 := by
  intro sw sw2
  have S0' := join_pin_ok false true pr0 pc0 ps0 pq0 Cr Cf S0 S1 x s j0 H_S_STABLE hL0 H_SETUP0 H_HOLD0
  have S1' := join_pin_ok true true pr1 pc1 ps1 pq1 Cr Cf S0 S1 y s j1 H_S_STABLE hL1 H_SETUP1 H_HOLD1
  have l1 := Rd.lo_le_hi pr1; have l2 := Rd.lo_le_hi pc1; have l3 := Rd.lo_le_hi pq1
  have c1 := HC.x_c; have c2 := HC.x_y; have c3 := HC.c_dn; have c4 := HC.y_dn
  refine ⟨abs_mux hC sw sw2 X0 Y0, abs_mux_proto sel sw sw2 X0 Y0 C0,
    abs_mux_held sel sw sw2 X0 Y0 C0, ?_, hx, ?_, ?_, ?_, ?_⟩
  · simp only [jU0, jU1] at *
    intro p hp q hq hlt
    simp only [muxEvs, List.mem_cons, List.mem_nil_iff, or_false] at hp hq
    by_cases e1 : Cr ≤ Yr <;> by_cases e2 : Cf ≤ Yf <;>
      simp only [e1, e2, decide_true, decide_false, mC, mY, fC, fY, jU0, jU1, jV0, jV1] at hp hq <;>
      rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      rcases hq with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
      simp only at hlt ⊢ <;> omega
  · obtain ⟨y1, y2, y3⟩ := hy
    exact winImg_of hY.2.1 (fun t _ h => y1 t h) y2 y3
  · exact winImg_of hc.2 (fun t _ h => by simp [pulse]; omega) (fun t h1 h2 => by simp [pulse]; omega)
      (fun t h => by simp [pulse]; omega)
  · exact sel_join_img S1' hR1 hy ⟨hd.1, hd.2.1, hd.2.2.2⟩ hc.1 H_JOIN_RACE
  · exact unsel_low false true (by decide) pr0 pc0 pq0 hd.2.2.1 x (pulse Cr Cf) j0 S0' hR0

/-- **Counter-run (setup row violated by 100 ps, uj0).** LibGapMux's `wrong_branch_latched`:
x waiting, ctl `[1000, 3000)` read through 300, select `1` only from 800 read through 600,
loop 50: a physical uj0 trace exists (H_PIN_READ, H_RESET) and it latches 1 from 1300 on, so
NO retiming refines it (`mux_unsel_never`). -/
theorem mux_setup_breaks :
    ∃ j0 : Int → Bool,
      LutEq false (Rd.const 0) (Rd.const 300) (Rd.const 600) (Rd.const ((50 : Nat) : Int))
        (fun _ => true) (pulse 1000 3000) (LibGapSteer.sAdv true 800 5000) j0 ∧ Rest j0 ∧
      ¬ ∀ t, j0 t = false := by
  refine ⟨_, run_luteq false 0 300 600 50 (by decide) (fun _ => true) (pulse 1000 3000)
    (LibGapSteer.sAdv true 800 5000), run_rest _ _ _, fun h => ?_⟩
  have := wrong_branch_latched _ (run_luteq false 0 300 600 50 (by decide) (fun _ => true)
    (pulse 1000 3000) (LibGapSteer.sAdv true 800 5000)) 1300 (by decide)
  rw [h] at this; exact Bool.false_ne_true this

/-- **Counter-run (hold row violated by 500 ps, uj1).** y `[0, 2000)`, ctl `[1000, 3000)`, both
read through 300; select `1` on `[500, 2500)` read through 300 (hold: `3000 + 300 > 2500 + 300`);
loop 100. Setup and `H_JOIN_RACE` hold (`1300 + 100 ≤ 2300`). Every uj1 trace obeying H_PIN_READ
is 0 at 2800, inside the phase `[U1, V0) = [1300, 3300)` where the image must be 1. -/
theorem mux_hold_breaks :
    (500 : Int) + 300 ≤ 1000 + 300 ∧ ¬ ((3000 : Int) + 300 ≤ 2500 + 300) ∧
    jU1 0 1000 (Rd.const 300) (Rd.const 300) + 100 ≤ jRel 2000 3000 (Rd.const 300) (Rd.const 300) ∧
    ∃ j1 : Int → Bool,
      LutEq true (Rd.const 300) (Rd.const 300) (Rd.const 300) (Rd.const ((100 : Nat) : Int))
        (pulse 0 2000) (pulse 1000 3000) (LibGapSteer.sAdv true 500 2500) j1 ∧ Rest j1 ∧
      ¬ WinImg j1 false true 0
        ⟨jU0 0 1000 (Rd.const 300) (Rd.const 300), jU1 0 1000 (Rd.const 300) (Rd.const 300)⟩
        ⟨jV0 2000 3000 (Rd.const 300) (Rd.const 300), jV1 2000 3000 (Rd.const 300) (Rd.const 300)⟩ := by
  refine ⟨by decide, by decide, by decide, _, run_luteq true 300 300 300 100 (by decide)
    (pulse 0 2000) (pulse 1000 3000) (LibGapSteer.sAdv true 500 2500), run_rest _ _ _, fun W => ?_⟩
  have hL := run_luteq true 300 300 300 100 (by decide) (pulse 0 2000) (pulse 1000 3000)
    (LibGapSteer.sAdv true 500 2500)
  have h1 := W.mid 2800 (by decide) (by decide)
  rw [hL 2800 (by decide)] at h1
  revert h1
  generalize LibGapMux.run _ _ _ _ = q
  revert q; decide

/-- **Non-vacuity (mux join).** x waiting from 0; y `[500, 2500)`; ctl `[1000, 3000)`; select
`1` on `[500, 4000)`; every pin read through 300 except the select (450) and the feedback (100):
both joins' traces exist and every hypothesis of `mux_refines` holds, so its conclusion applies. -/
theorem mux_witness :
    let pr : Rd := Rd.const 300
    let ps : Rd := Rd.const 450
    let pq : Rd := Rd.const ((100 : Nat) : Int)
    let x : Int → Bool := fun t => decide (0 ≤ t)
    let s := LibGapSteer.sAdv true 500 4000
    ∃ j0 j1 : Int → Bool, LutEq false pr pr ps pq x (pulse 1000 3000) s j0 ∧
      LutEq true pr pr ps pq (pulse 500 2500) (pulse 1000 3000) s j1 ∧ Rest j0 ∧ Rest j1 ∧
      MuxRef 0 0 500 500 2500 2500 1000 3000 pr pr x (pulse 500 2500) j0 j1 := by
  intro pr ps pq x s
  have hL0 := run_luteq false 300 300 450 100 (by decide) x (pulse 1000 3000) s
  have hL1 := run_luteq true 300 300 450 100 (by decide) (pulse 500 2500) (pulse 1000 3000) s
  refine ⟨_, _, hL0, hL1, run_rest _ _ _, run_rest _ _ _, ?_⟩
  have h := mux_refines (sel := fun n => n == 1) (C0 := 1) rfl 0 0 (Xr := 0) (Xr1 := 0)
    (Yr := 500) (Yr1 := 500) (Yf := 2500) (Yf1 := 2500) (Cr := 1000) (Cf := 3000) (S0 := 500)
    (S1 := 4000) (LibGapSteer.sAdv_stable true 500 4000) hL0 hL1 (run_rest _ _ _) (run_rest _ _ _)
    (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const]) (by simp [Rd.const])
    (by decide)
    ⟨fun t h => by simp [x]; omega, fun t h => by simp [x]; omega⟩ (Int.le_refl _)
    ⟨fun t h => by simp [pulse]; omega, fun t h1 h2 => by simp [pulse]; omega,
     fun t h => by simp [pulse]; omega⟩ (by decide) (by decide)
    ⟨by simp [Rd.const], by simp [Rd.const], by simp [Rd.const], by simp [Rd.const]⟩
    ⟨by decide, by decide, by decide, by decide⟩
  exact h.2.2.2

end mux

end Formal.Cells.ZeroDelayRefine
