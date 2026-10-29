import Formal.Cells.ZeroDelayNetPhys

/-!
# ZeroDelayTok: one `bd_link` stage carrying `k` tokens: the exact cross-token row

Probe Bzd3 (shard B); note `formal/notes/B-zero-delay-tok.md`. LinkExact's model of one
`bd_link` stage (`bd_c2n` node at its real INIT in Kleene semantics, every pin through its own
read map in the box, `bd_latch` bit, power-up arbitrary) with an environment that sends `k`
four-phase tokens instead of one.

## Model (every hypothesis named)

* `ParK`: per-token event times `Ra j, Ra1 j, Fa j, Fa1 j` (request), `Rb j, …, Fb1 j`
  (acknowledge), `Td j, Tn j` (data window of token `j`), one reset, ONE per-pin box (shared by
  all tokens). `P.tok j` is token `j` as a LinkExact `Par`, so `U0, U1, Rel, V0, V1` and the
  six rows `Conj` are LinkExact's, per token.
* **H_ENV_K** (`EnvK`): req low before `Ra 0`, high on `[Ra1 j, Fa j)`, low on
  `[Fa1 j, Ra (j+1))` (for ever after the last token); the same for ack; ARBITRARY (X,
  glitches) in every window. **H_D_STABLE_K** (`DStabK`): data `vs j` on `[Td j, Tn j)`.
* Scope `WfK`: `Wf` for every token (LinkExact's scope), `k ≥ 1`, and **H_NEXT** (the env's
  pulses are ordered: `Fa1 j ≤ Ra (j+1)`, `Fb1 j ≤ Rb (j+1)`).

## Spec (`SpecK`): `k` tokens, each a window token on the node and captured by the latch

node 0 on `[Rhi, U0 0)`; for each `j`: 1 on the nonempty `[U1 j, V0 j)`, 0 on
`[V1 j, U0 (j+1))` (for ever after the last token); the latch outputs `vs j` from its capture
(`V0 j ≤ pe.σ t`) and from `max (U1 j + pe.hi) (Td j + pd.hi)` up to the instant the NEXT
token's request can first be read through the enable (`t < U0 (j+1) + Elo`).

## Results

* `latch_tok_ok`: **multi-token latch capture, per token window**. LibGapLatch's three rows
  (setup_pulse, setup_data, hold) for ONE token window give capture of that token up to the
  end of the window in which the enable is known low, whatever the enable does after it
  (`LibGapLatch.EnTok` says "low for ever after `C`" and cannot express a second token).
* `sufficientK`: LinkExact's six rows for EVERY token (`Conj (P.tok j)`) plus the new row
  **H_REARM** `Fb1 j + Bhi ≤ Ra1 (j+1) + Ahi` (the node surely reads the previous acknowledge
  fall by the time it surely reads the next request rise) ⇒ `SpecK` for every behaviour.
* `need_rearm`: if H_REARM fails for some `j` (all else arbitrary except the rise race of token
  `j+1` and the necessity scope `GapK`), some behaviour breaks `SpecK`: at `U1 (j+1)` the node
  reads request 1, acknowledge 1 (still the previous token's) and its own 0, and holds 0
  (`c2nK 1 1 0 0 = 0`, the real INIT), where the spec says 1.
* `exact_rearm` (**the new row is exact**): under `WfK`, `GapK` and the six rows of every
  token, every behaviour meets `SpecK` **iff** H_REARM holds for every `j`.
* `rearm_one_tick`, `rearm_breaks`: two tokens, LinkExact's `P0` delays (nonzero everywhere),
  H_REARM violated by EXACTLY 1 ps, every other row of both tokens, `WfK` and `GapK` met: the
  stage breaks. `witness2`: two tokens (values 1 then 0), every row met: every behaviour meets
  `SpecK`, and a simulated behaviour exists.

NOT covered (see the note): necessity of the six per-token rows INSIDE a `k`-token
environment for `k ≥ 2` (LinkExact proves them for one token; here they are only used as
hypotheses of `exact_rearm`, so the full iff `SafeK ↔ RowsK` is NOT proved); the alternative
spec in which the node's rise window is `max` of the request rise and the previous
acknowledge fall (then H_REARM would be absorbed into the window; not mechanised). Core Lean.
-/

namespace Formal.Cells.ZeroDelayTok
open Formal.Cells
open Formal.Cells.CElemFn
open Formal.Cells.LibGapSteer (Rd Rd.const)
open Formal.Cells.LibGapMux (int_ind)
open Formal.Cells.LibGapLatch
open Formal.Cells.LinkExact

/-! ## 0. Parameters, scope, behaviours, spec -/

/-- `k` tokens through one `bd_link` stage: per-token driver event times, one reset, one box. -/
structure ParK where
  k : Nat
  W : Int
  W1 : Int
  Ra : Nat → Int
  Ra1 : Nat → Int
  Fa : Nat → Int
  Fa1 : Nat → Int
  Rb : Nat → Int
  Rb1 : Nat → Int
  Fb : Nat → Int
  Fb1 : Nat → Int
  Td : Nat → Int
  Tn : Nat → Int
  Alo : Int
  Ahi : Int
  Blo : Int
  Bhi : Int
  Qlo : Int
  Qhi : Int
  Rlo : Int
  Rhi : Int
  Dlo : Int
  Dhi : Int
  Elo : Int
  Ehi : Int
  Flo : Int
  Fhi : Int

/-- Token `j` as a LinkExact one-token parameter set. -/
def ParK.tok (P : ParK) (j : Nat) : Par :=
  { W := P.W, W1 := P.W1, Ra := P.Ra j, Ra1 := P.Ra1 j, Fa := P.Fa j, Fa1 := P.Fa1 j,
    Rb := P.Rb j, Rb1 := P.Rb1 j, Fb := P.Fb j, Fb1 := P.Fb1 j, Td := P.Td j, Tn := P.Tn j,
    Alo := P.Alo, Ahi := P.Ahi, Blo := P.Blo, Bhi := P.Bhi, Qlo := P.Qlo, Qhi := P.Qhi,
    Rlo := P.Rlo, Rhi := P.Rhi, Dlo := P.Dlo, Dhi := P.Dhi, Elo := P.Elo, Ehi := P.Ehi,
    Flo := P.Flo, Fhi := P.Fhi }

/-- **Scope**: LinkExact's `Wf` for every token, at least one token, and **H_NEXT** (the
environment's pulses are in order). -/
structure WfK (P : ParK) : Prop where
  pos : 1 ≤ P.k
  wf : ∀ j < P.k, Wf (P.tok j)
  H_NEXT : ∀ j, j + 1 < P.k → P.Fa1 j ≤ P.Ra (j + 1) ∧ P.Fb1 j ≤ P.Rb (j + 1)

/-- **H_ENV_K**: `k` tokens on the request and acknowledge pins (definite outside the windows,
ARBITRARY inside them), reset as in LinkExact. -/
structure EnvK (P : ParK) (r a b : Int → K3) : Prop where
  r_hi : ∀ x, 0 ≤ x → x < P.W → r x = .t
  r_lo : ∀ x, P.W1 ≤ x → r x = .f
  a_lo0 : ∀ x, x < P.Ra 0 → a x = .f
  a_hi : ∀ j < P.k, ∀ x, P.Ra1 j ≤ x → x < P.Fa j → a x = .t
  a_lo : ∀ j < P.k, ∀ x, P.Fa1 j ≤ x → (j + 1 < P.k → x < P.Ra (j + 1)) → a x = .f
  b_lo0 : ∀ x, x < P.Rb 0 → b x = .f
  b_hi : ∀ j < P.k, ∀ x, P.Rb1 j ≤ x → x < P.Fb j → b x = .t
  b_lo : ∀ j < P.k, ∀ x, P.Fb1 j ≤ x → (j + 1 < P.k → x < P.Rb (j + 1)) → b x = .f

/-- **H_D_STABLE_K**: the data pin carries `vs j` on `[Td j, Tn j)`, arbitrary elsewhere. -/
def DStabK (P : ParK) (vs : Nat → Bool) (d : Int → K3) : Prop :=
  ∀ j < P.k, DStab (vs j) (P.Td j) (P.Tn j) d

/-- A behaviour of the stage (LinkExact's `Beh` with the `k`-token environment). -/
structure BehK (P : ParK) (vs : Nat → Bool) (pa pb pq pr pd pe pf : Rd) (r a b d c q : Int → K3) :
    Prop where
  box : Box (P.tok 0) pa pb pq pr pd pe pf
  env : EnvK P r a b
  dat : DStabK P vs d
  ctl : CtlEq pa pb pq pr r a b c
  lat : LutEq pd pe pf d c q

/-- Before the next token (for ever after the last one). -/
def Bef (P : ParK) (j : Nat) (t : Int) : Prop := j + 1 < P.k → t < (P.tok (j + 1)).U0

/-- **The `k`-token stage spec.** -/
structure SpecK (P : ParK) (vs : Nat → Bool) (pd pe : Rd) (c q : Int → K3) : Prop where
  nonempty : ∀ j < P.k, (P.tok j).U1 < (P.tok j).V0
  rst : ∀ t, P.Rhi ≤ t → t < (P.tok 0).U0 → c t = .f
  hi : ∀ j < P.k, ∀ t, (P.tok j).U1 ≤ t → t < (P.tok j).V0 → c t = .t
  lo : ∀ j < P.k, ∀ t, (P.tok j).V1 ≤ t → Bef P j t → c t = .f
  capt : ∀ j < P.k, ∀ t, 0 ≤ t → (P.tok j).V0 ≤ pe.σ t → Bef P j (t - P.Elo) → q t = kb (vs j)
  out : ∀ j < P.k, ∀ t, (P.tok j).U1 + pe.hi ≤ t → P.Td j + pd.hi ≤ t → Bef P j (t - P.Elo) →
    q t = kb (vs j)

/-- Every behaviour, for every data sequence, meets the spec. -/
def SafeK (P : ParK) : Prop :=
  ∀ vs pa pb pq pr pd pe pf r a b d c q, BehK P vs pa pb pq pr pd pe pf r a b d c q →
    SpecK P vs pd pe c q

/-- **H_REARM** (the new cross-token row): the previous acknowledge fall is surely read by the
time the next request rise is surely read. -/
def Rearm (P : ParK) (j : Nat) : Prop := P.Fb1 j + P.Bhi ≤ P.Ra1 (j + 1) + P.Ahi

/-- The rows: LinkExact's six rows at every token, and H_REARM between consecutive tokens. -/
structure RowsK (P : ParK) : Prop where
  conj : ∀ j < P.k, Conj (P.tok j)
  rearm : ∀ j, j + 1 < P.k → Rearm P j

theorem box_tok {P : ParK} {pa pb pq pr pd pe pf : Rd} (B : Box (P.tok 0) pa pb pq pr pd pe pf)
    (j : Nat) : Box (P.tok j) pa pb pq pr pd pe pf := ⟨B.a, B.b, B.q, B.r, B.d, B.e, B.f⟩

/-! ## 1. Multi-token latch capture, one token window -/

/-- **Multi-token latch capture (per token window).** The enable is definite 1 on `[A, B)` and
definite 0 on `[C, ∞) ∩ Lt` for a downward-closed window `Lt` (the next token's enable may do
anything after the window). LibGapLatch's three rows give: the output is `v` at every `t ≥ 0`
at which the enable is read in its closing window or later AND `t - pe.lo` is still in the
window. With `Lt = True` this is `LibGapLatch.latch_pin_ok`. -/
theorem latch_tok_ok (v : Bool) (A B C Td Tn : Int) (Lt : Int → Prop)
    (hLt : ∀ x y, x ≤ y → Lt y → Lt x) (pd pe pq : Rd) (d e q : Int → K3)
    (hq1 : 1 ≤ pq.lo) (hBC : B ≤ C) (H_T0 : 0 ≤ A + pe.lo)
    (H_EN1 : ∀ x, A ≤ x → x < B → e x = .t) (H_EN0 : ∀ x, C ≤ x → Lt x → e x = .f)
    (H_D_STABLE : DStab v Td Tn d) (H_PIN_READ : LutEq pd pe pq d e q)
    (H_SETUP_PULSE : A + pe.hi + pq.hi ≤ B + pe.lo)
    (H_SETUP_DATA : Td + pd.hi + pq.hi ≤ B + pe.lo)
    (H_HOLD : C + pe.hi ≤ Tn + pd.lo) :
    ∀ t, 0 ≤ t → B ≤ pe.σ t → Lt (t - pe.lo) → q t = kb v := by
  have e1 := Rd.lo_le_hi pe; have e2 := Rd.lo_le_hi pq; have e3 := Rd.lo_le_hi pd
  intro t
  refine int_ind (fun t => 0 ≤ t → B ≤ pe.σ t → Lt (t - pe.lo) → q t = kb v)
    (fun t ht h0 => absurd h0 (by omega)) ?_ t
  intro t ht ih _ hB hW
  have g1 := pe.le t; have g2 := pq.ge t; have g3 := pq.le t; have g4 := pd.ge t
  have g5 := pd.le t; have g6 := pe.ge t
  have hfb : q (pq.σ t) = kb v := by
    have h0 : 0 ≤ pq.σ t := by omega
    have hlt : pq.σ t < t := by omega
    have hW' : Lt (pq.σ t - pe.lo) := hLt _ _ (by omega) hW
    by_cases hu : B ≤ pe.σ (pq.σ t)
    · exact ih _ hlt h0 hu hW'
    · have f1 := pe.ge (pq.σ t); have f2 := pe.le (pq.σ t); have f3 := pd.ge (pq.σ t)
      have f4 := pd.le (pq.σ t)
      rw [H_PIN_READ _ h0, H_EN1 _ (by omega) (by omega), m_t]
      exact H_D_STABLE _ (by omega) (by omega)
  rw [H_PIN_READ t ht, hfb]
  by_cases hc : pe.σ t < C
  · rw [H_D_STABLE _ (by omega) (by omega)]; exact m_same _ v
  · rw [H_EN0 _ (by omega) (hLt _ _ (by omega) hW), m_f]

/-! ## 2. Sufficiency -/

section suff
variable {P : ParK} {vs : Nat → Bool} {pa pb pq pr pd pe pf : Rd} {r a b d c q : Int → K3}

/-- Reset phase (LinkExact's `node_rst` with the `k`-token environment). -/
theorem node_rst_k (S : WfK P) (B : Box (P.tok 0) pa pb pq pr pd pe pf) (E : EnvK P r a b)
    (hc : CtlEq pa pb pq pr r a b c) (H : Conj (P.tok 0)) :
    ∀ t, P.Rhi ≤ t → t < (P.tok 0).U0 → c t = .f := by
  have w := S.wf 0 S.pos
  have s1 := w.hR; have s2 := w.hQ; have s3 := w.hA; have s4 := w.hB; have s5 := w.ha
  have b1 := B.a; have b2 := B.b; have b3 := B.q; have b4 := B.r
  have h1 := H.H_RST_WIDTH; have h2 := H.H_RACE_UP
  simp only [ParK.tok, Par.U0, Par.U1, Par.Rel] at *
  apply int_ind (fun t => P.Rhi ≤ t → t < P.Ra 0 + P.Alo → c t = .f) (fun t ht h => by omega)
  intro t ht ih h3 h4
  rw [hc t ht]
  have g1 := pr.ge t; have g2 := pr.le t; have g3 := pq.ge t; have g4 := pq.le t
  have g5 := pa.le t; have g6 := pb.le t
  by_cases hw : t < P.W + P.Rlo
  · rw [E.r_hi _ (by omega) (by omega), c_rst]
  · rw [E.a_lo0 _ (by omega), E.b_lo0 _ (by omega), ih _ (by omega) (by omega) (by omega), c_idle]

/-- High phase of token `j` (needs H_REARM of the previous token). -/
theorem node_hi_k (S : WfK P) (B : Box (P.tok 0) pa pb pq pr pd pe pf) (E : EnvK P r a b)
    (hc : CtlEq pa pb pq pr r a b c) (H : RowsK P) :
    ∀ j < P.k, ∀ t, (P.tok j).U1 ≤ t → t < (P.tok j).V0 → c t = .t := by
  intro j hj
  apply ZeroDelayNet.node_hi_loc (S.wf j hj) (box_tok B j) hc (H.conj j hj).H_RACE_UP E.r_lo
    (E.a_hi j hj)
  intro x h1 h2
  rcases j with _ | i
  · exact E.b_lo0 x h2
  · have hr := H.rearm i hj
    have hn := S.H_NEXT i hj
    have wb := (S.wf i (by omega)).hb
    simp only [Rearm, ParK.tok, Par.U1] at hr h1 h2 wb
    exact E.b_lo i (by omega) x (by omega) (fun _ => h2)

/-- Low phase of token `j`, up to the next token's earliest request read, from only the local
facts it reads (request low on `[Fa1 j, Ra (j+1))`, acknowledge high on `[Rb1 j, Fb j)`). -/
theorem node_lo_loc_k (S : WfK P) (B : Box (P.tok 0) pa pb pq pr pd pe pf)
    (hc : CtlEq pa pb pq pr r a b c) {j : Nat} (hj : j < P.k)
    (h3 : (P.tok j).V1 + P.Qhi ≤ P.Fb j + P.Blo)
    (a_lo : ∀ x, P.Fa1 j ≤ x → (j + 1 < P.k → x < P.Ra (j + 1)) → a x = .f)
    (b_hi : ∀ x, P.Rb1 j ≤ x → x < P.Fb j → b x = .t) :
    ∀ t, (P.tok j).V1 ≤ t → Bef P j t → c t = .f := by
  have w := S.wf j hj
  have s1 := w.hR; have s2 := w.hQ; have s3 := w.hA; have s4 := w.hB; have s5 := w.ha
  have s8 := w.hb; have s6 := w.hW; have s7 := w.H_RST_EARLY
  have b1 := B.a; have b2 := B.b; have b3 := B.q
  simp only [Bef, ParK.tok, Par.V1, Par.U0] at *
  apply int_ind (fun t => max (P.Fa1 j + P.Ahi) (P.Rb1 j + P.Bhi) ≤ t →
      (j + 1 < P.k → t < P.Ra (j + 1) + P.Alo) → c t = .f)
    (fun t ht h => by omega)
  intro t ht ih h4 h5
  rw [hc t ht]
  have g3 := pq.ge t; have g4 := pq.le t
  have g5 := pa.ge t; have g5' := pa.le t; have g6 := pb.le t; have g7 := pb.ge t
  rw [a_lo _ (by omega) (fun h => by have := h5 h; omega)]
  by_cases h6 : t < P.Fb j + P.Blo
  · rw [b_hi _ (by omega) (by omega), c_follow0]
  · rw [ih _ (by omega) (by omega) (fun h => by have := h5 h; omega), c_hold0]

/-- Low phase of token `j`. -/
theorem node_lo_k (S : WfK P) (B : Box (P.tok 0) pa pb pq pr pd pe pf) (E : EnvK P r a b)
    (hc : CtlEq pa pb pq pr r a b c) (H : RowsK P) :
    ∀ j < P.k, ∀ t, (P.tok j).V1 ≤ t → Bef P j t → c t = .f := fun j hj =>
  node_lo_loc_k S B hc hj (H.conj j hj).H_RACE_DN (E.a_lo j hj) (E.b_hi j hj)

/-- **Spec assembly**: the three node phases (however obtained) plus the latch rows give the
`k`-token spec. -/
theorem spec_of_phases (S : WfK P) (H : RowsK P) (B : Box (P.tok 0) pa pb pq pr pd pe pf)
    (lat : LutEq pd pe pf d c q) (dat : DStabK P vs d)
    (N1 : ∀ t, P.Rhi ≤ t → t < (P.tok 0).U0 → c t = .f)
    (N2 : ∀ j < P.k, ∀ t, (P.tok j).U1 ≤ t → t < (P.tok j).V0 → c t = .t)
    (N3 : ∀ j < P.k, ∀ t, (P.tok j).V1 ≤ t → Bef P j t → c t = .f) :
    SpecK P vs pd pe c q := by
  have be := B.e; have bd := B.d; have bf := B.f
  simp only [ParK.tok] at be bd bf
  have ge1 := Rd.lo_le_hi pe; have ge2 := Rd.lo_le_hi pd
  have hcap : ∀ j < P.k, ∀ t, 0 ≤ t → (P.tok j).V0 ≤ pe.σ t → Bef P j (t - P.Elo) →
      q t = kb (vs j) := by
    intro j hj t ht hB hW
    have w := S.wf j hj; have Hj := H.conj j hj
    have s1 := w.hR; have s2 := w.hQ; have s3 := w.hA; have s4 := w.hB; have s5 := w.ha
    have s6 := w.H_RST_EARLY; have s7 := w.hW; have s8 := w.hb; have s9 := w.hD
    have s10 := w.hE; have s11 := w.hF
    have h1 := Hj.H_RACE_UP; have h2 := Hj.H_SETUP_PULSE; have h3 := Hj.H_SETUP_DATA
    have h4 := Hj.H_HOLD
    have L := latch_tok_ok (vs j) (P.tok j).U1 (P.tok j).V0 (P.tok j).V1 (P.Td j) (P.Tn j)
      (Bef P j) (fun x y hxy hy h => by have := hy h; omega) pd pe pf d c q
      (by simp only [ParK.tok] at *; omega)
      (by simp only [ParK.tok, Par.V0, Par.V1] at *; omega)
      (by simp only [ParK.tok, Par.U1] at *; omega)
      (N2 j hj) (N3 j hj) (dat j hj) lat
      (by simp only [ParK.tok, Par.U1, Par.V0, Par.Rel] at *; omega)
      (by simp only [ParK.tok, Par.U1, Par.V0, Par.Rel] at *; omega)
      (by simp only [ParK.tok, Par.U1, Par.V1, Par.Rel] at *; omega)
    exact L t ht hB (fun h => by have := hW h; omega)
  refine ⟨fun j hj => ?_, N1, N2, N3, hcap, ?_⟩
  · have w := S.wf j hj; have := w.hA; have := w.hB; have := w.hQ; have := w.ha
    have := (H.conj j hj).H_RACE_UP
    simp only [ParK.tok, Par.U1, Par.V0, Par.Rel] at *; omega
  · intro j hj t ht1 ht2 hW
    have w := S.wf j hj; have Hj := H.conj j hj
    have s1 := w.hA; have s2 := w.hB; have s3 := w.ha; have s4 := w.hb
    have s5 := w.hR; have s6 := w.hW; have s7 := w.H_RST_EARLY; have s8 := w.hE; have s9 := w.hD
    have h4 := Hj.H_HOLD
    have g1 := pe.ge t; have g2 := pe.le t; have g3 := pd.ge t; have g4 := pd.le t
    by_cases hB : (P.tok j).V0 ≤ pe.σ t
    · exact hcap j hj t (by simp only [ParK.tok, Par.U1] at *; omega) hB hW
    · rw [lat t (by simp only [ParK.tok, Par.U1] at *; omega),
        N2 j hj _ (by omega) (by omega), m_t]
      simp only [ParK.tok, Par.U1, Par.V0, Par.V1] at *
      exact dat j hj _ (by omega) (by omega)

/-- **Sufficiency (`k` tokens).** LinkExact's six rows at every token plus H_REARM give the
`k`-token spec for EVERY behaviour (any read maps in the box, any admissible environment and
data sequence, any power-up). -/
theorem sufficientK (S : WfK P) (H : RowsK P) (Bh : BehK P vs pa pb pq pr pd pe pf r a b d c q) :
    SpecK P vs pd pe c q :=
  spec_of_phases S H Bh.box Bh.lat Bh.dat (node_rst_k S Bh.box Bh.env Bh.ctl (H.conj 0 S.pos))
    (node_hi_k S Bh.box Bh.env Bh.ctl H) (node_lo_k S Bh.box Bh.env Bh.ctl H)

end suff

/-! ## 3. Pulse trains (adversarial environments) -/

/-- A train of sharp pulses: 1 on `[lo i, hi i)` for `i < k`, 0 elsewhere. -/
noncomputable def ptrain (k : Nat) (lo hi : Nat → Int) (x : Int) : K3 :=
  open Classical in if ∃ i, i < k ∧ lo i ≤ x ∧ x < hi i then .t else .f

theorem ptrain_t {k : Nat} {lo hi : Nat → Int} {x : Int} {i : Nat} (hi' : i < k)
    (h1 : lo i ≤ x) (h2 : x < hi i) : ptrain k lo hi x = .t := by
  unfold ptrain; rw [if_pos ⟨i, hi', h1, h2⟩]

theorem ptrain_f {k : Nat} {lo hi : Nat → Int} {x : Int}
    (h : ∀ i, i < k → x < lo i ∨ hi i ≤ x) : ptrain k lo hi x = .f := by
  unfold ptrain
  rw [if_neg]
  rintro ⟨i, hi', h1, h2⟩
  rcases h i hi' with h3 | h3 <;> omega

/-- In an ordered train every earlier pulse ends before every later one starts. -/
theorem seq_lt {k : Nat} {lo hi : Nat → Int} (h1 : ∀ i < k, lo i ≤ hi i)
    (h2 : ∀ i, i + 1 < k → hi i ≤ lo (i + 1)) :
    ∀ i i', i < i' → i' < k → hi i ≤ lo i' := by
  intro i i' hii' hk
  induction i' with
  | zero => omega
  | succ m ih =>
    rcases Nat.lt_or_ge i m with h | h
    · have := ih h (by omega); have := h1 m (by omega); have := h2 m hk; omega
    · have : i = m := by omega
      subst this; exact h2 i hk

/-- Outside every pulse of an ordered train, between pulse `j`'s end and pulse `j+1`'s start. -/
theorem ptrain_gap {k : Nat} {lo hi : Nat → Int} (h1 : ∀ i < k, lo i ≤ hi i)
    (h2 : ∀ i, i + 1 < k → hi i ≤ lo (i + 1)) {j : Nat} (hj : j < k) {x : Int}
    (hx1 : hi j ≤ x) (hx2 : j + 1 < k → x < lo (j + 1)) : ptrain k lo hi x = .f := by
  apply ptrain_f
  intro i hi'
  rcases Nat.lt_trichotomy i j with h | h | h
  · right; have := seq_lt h1 h2 i j h hj; have := h1 j hj; omega
  · right; subst h; exact hx1
  · left
    have := hx2 (by omega)
    rcases Nat.lt_or_ge (j + 1) i with h' | h'
    · have := seq_lt h1 h2 (j + 1) i h' hi'; have := h1 (j + 1) (by omega); omega
    · have : i = j + 1 := by omega
      subst this; exact this

theorem ptrain_lo0 {k : Nat} {lo hi : Nat → Int} (h1 : ∀ i < k, lo i ≤ hi i)
    (h2 : ∀ i, i + 1 < k → hi i ≤ lo (i + 1)) {x : Int} (hx : x < lo 0) :
    ptrain k lo hi x = .f := by
  apply ptrain_f
  intro i hi'
  left
  rcases i with _ | i
  · exact hx
  · have := seq_lt h1 h2 0 (i + 1) (by omega) hi'; have := h1 0 (by omega); omega

section trains

theorem a_ord1 {P : ParK} (S : WfK P) : ∀ i < P.k, P.Ra1 i ≤ P.Fa i := fun i hi => by
  have := (S.wf i hi).ha; simp only [ParK.tok] at this; omega
theorem a_ord2 {P : ParK} (S : WfK P) : ∀ i, i + 1 < P.k → P.Fa i ≤ P.Ra1 (i + 1) := fun i hi => by
  have := (S.wf i (by omega)).ha; have := (S.wf (i + 1) hi).ha; have := S.H_NEXT i hi
  simp only [ParK.tok] at *; omega
theorem b_ord1 {P : ParK} (S : WfK P) : ∀ i < P.k, P.Rb1 i ≤ P.Fb1 i := fun i hi => by
  have := (S.wf i hi).hb; simp only [ParK.tok] at this; omega
theorem b_ord2 {P : ParK} (S : WfK P) : ∀ i, i + 1 < P.k → P.Fb1 i ≤ P.Rb1 (i + 1) := fun i hi => by
  have := (S.wf (i + 1) hi).hb; have := S.H_NEXT i hi
  simp only [ParK.tok] at *; omega

/-- The sharp trains are an admissible `k`-token environment: request pulses `[Ra1 j, Fa j)`,
acknowledge pulses `[Rb1 j, Fb1 j)` (each held high to the END of its fall window). -/
theorem envK_trains {P : ParK} (S : WfK P) : EnvK P (win 0 P.W) (ptrain P.k P.Ra1 P.Fa) (ptrain P.k P.Rb1 P.Fb1) := by
  have A1 := a_ord1 S; have A2 := a_ord2 S; have B1 := b_ord1 S; have B2 := b_ord2 S
  have w0 := S.wf 0 S.pos
  have := w0.hW; have := w0.ha; have := w0.hb
  simp only [ParK.tok] at *
  refine ⟨fun x h1 h2 => win_t h1 h2, fun x h => win_f2 (by omega),
    fun x h => ptrain_lo0 A1 A2 (by omega), fun j hj x h1 h2 => ptrain_t hj h1 h2,
    fun j hj x h1 h2 => ?_, fun x h => ptrain_lo0 B1 B2 (by omega),
    fun j hj x h1 h2 => ?_, fun j hj x h1 h2 => ?_⟩
  · have := (S.wf j hj).ha; simp only [ParK.tok] at this
    refine ptrain_gap A1 A2 hj (by omega) (fun h => ?_)
    have := h2 h; have := (S.wf (j + 1) h).ha; simp only [ParK.tok] at this; omega
  · have := (S.wf j hj).hb; simp only [ParK.tok] at this
    exact ptrain_t hj h1 (by omega)
  · refine ptrain_gap B1 B2 hj h1 (fun h => ?_)
    have := h2 h; have := (S.wf (j + 1) h).hb; simp only [ParK.tok] at this; omega

end trains

/-! ## 4. Necessity of H_REARM -/

/-- **H_GAP** (scope of the necessity half only): the previous token's request fall and node
fall (with its feedback) are surely read before the next request can be read rising. -/
def GapK (P : ParK) (j : Nat) : Prop :=
  P.Fa1 j + P.Ahi ≤ (P.tok (j + 1)).U0 ∧ (P.tok j).V1 + P.Qhi ≤ (P.tok (j + 1)).U0

/-- Every completed set of traces is a behaviour (latch simulated, data constant `true`). -/
theorem mkBehK {P : ParK} (S : WfK P) {pa pb pr pd pe : Rd} {r a b c : Int → K3}
    (hbox : Box (P.tok 0) pa pb (Rd.const P.Qhi) pr pd pe (Rd.const P.Fhi))
    (hE : EnvK P r a b) (hc : CtlEq pa pb (Rd.const P.Qhi) pr r a b c) :
    ∃ q, BehK P (fun _ => true) pa pb (Rd.const P.Qhi) pr pd pe (Rd.const P.Fhi) r a b
      (fun _ => kb true) c q := by
  have hF : 0 < P.Fhi.toNat := by have := (S.wf 0 S.pos).hF; simp only [ParK.tok] at this; omega
  refine ⟨run (lf pd pe (fun _ => kb true) c) (kb false) P.Fhi.toNat hF,
    hbox, hE, fun j _ x _ _ => rfl, hc, ?_⟩
  intro t ht
  exact run_eqQ _ _ P.Fhi hF t ht

/-- **H_REARM is needed.** If the node can still read the previous acknowledge high when it
surely reads the next request high, the run with every read at its slowest (request pulses
`[Ra1, Fa)`, acknowledge pulses held to `Fb1`) shows, at `U1 (j+1)`: request 1, acknowledge 1,
own feedback 0, so the real INIT holds 0 (`c_both`), where the spec says 1. -/
theorem need_rearm {P : ParK} (S : WfK P) {j : Nat} (hj : j + 1 < P.k) (G : GapK P j)
    (hup : (P.tok (j + 1)).U1 + P.Qhi ≤ (P.tok (j + 1)).Rel) (h : ¬ Rearm P j) : ¬ SafeK P := by
  intro hs
  have hQ : 0 < P.Qhi.toNat := by have := (S.wf 0 S.pos).hQ; simp only [ParK.tok] at this; omega
  obtain ⟨c, hc, -⟩ : ∃ c, CtlEq (Rd.const P.Ahi) (Rd.const P.Bhi) (Rd.const P.Qhi) (Rd.const P.Rhi)
      (win 0 P.W) (ptrain P.k P.Ra1 P.Fa) (ptrain P.k P.Rb1 P.Fb1) c ∧ ∀ t, t < 0 → c t = .f :=
    ⟨_, ctlRun_ctl _ _ _ _ _ _ .f P.Qhi hQ, fun t ht => ctlRun_neg t ht⟩
  have w0 := S.wf 0 S.pos
  have hbox : Box (P.tok 0) (Rd.const P.Ahi) (Rd.const P.Bhi) (Rd.const P.Qhi) (Rd.const P.Rhi)
      (Rd.const P.Dhi) (Rd.const P.Ehi) (Rd.const P.Fhi) := by
    have := w0.hA; have := w0.hB; have := w0.hQ; have := w0.hR; have := w0.hD; have := w0.hE
    have := w0.hF
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      simp only [Rd.const, ParK.tok] at * <;> omega
  obtain ⟨q, Bh⟩ := mkBehK S hbox (envK_trains S) hc
  have sp := hs _ _ _ _ _ _ _ _ _ _ _ _ _ _ Bh
  have A1 := a_ord1 S; have A2 := a_ord2 S
  have wj := S.wf j (by omega); have wk := S.wf (j + 1) hj
  have s1 := wj.ha; have s2 := wj.hb; have s3 := wk.ha; have s4 := wk.hb
  have s5 := wk.hA; have s6 := wk.hB; have s7 := wk.hQ; have s8 := wk.H_RST_EARLY
  have s9 := wk.hW; have s10 := wk.hR; have s11 := wj.hA; have s12 := wj.hR
  have s13 := wj.H_RST_EARLY; have s14 := wj.hB
  have hn := sp.nonempty (j + 1) hj
  have G1 := G.1; have G2 := G.2
  simp only [Rearm, ParK.tok, Par.U0, Par.U1, Par.V0, Par.V1, Par.Rel] at *
  -- the node stays 0 from `V1 j` up to `U1 (j+1)`
  have low : ∀ t, max (P.Fa1 j + P.Ahi) (P.Rb1 j + P.Bhi) ≤ t → t < P.Ra1 (j + 1) + P.Ahi →
      c t = .f := by
    apply int_ind (fun t => max (P.Fa1 j + P.Ahi) (P.Rb1 j + P.Bhi) ≤ t →
        t < P.Ra1 (j + 1) + P.Ahi → c t = .f) (fun t ht h1 => by omega)
    intro t ht ih h1 h2
    by_cases h3 : t < P.Ra (j + 1) + P.Alo
    · exact sp.lo j (by omega) t (by simp only [ParK.tok, Par.V1]; omega)
        (fun _ => by simp only [ParK.tok, Par.U0]; omega)
    · rw [hc t ht]; simp only [Rd.const]
      rw [ptrain_gap A1 A2 (j := j) (by omega) (by omega) (fun _ => by omega),
        ih _ (by omega) (by omega) (by omega), c_hold0]
  have key : c (P.Ra1 (j + 1) + P.Ahi) = .f := by
    rw [hc _ (by omega)]; simp only [Rd.const]
    rw [ptrain_t (i := j + 1) hj (by omega) (by omega),
      ptrain_t (i := j) (by omega) (by omega) (by omega),
      low _ (by omega) (by omega), win_f2 (by omega), c_both]
  have := sp.hi (j + 1) hj (P.Ra1 (j + 1) + P.Ahi) (Int.le_refl _)
    (by simp only [ParK.tok, Par.V0]; omega)
  rw [key] at this
  exact absurd this (by decide)

/-- **The new row is exact.** Under the scope `WfK`, the necessity scope `GapK` and
LinkExact's six rows at every token, every behaviour meets the `k`-token spec **iff** H_REARM
holds between every pair of consecutive tokens. -/
theorem exact_rearm {P : ParK} (S : WfK P) (G : ∀ j, j + 1 < P.k → GapK P j)
    (C : ∀ j < P.k, Conj (P.tok j)) : SafeK P ↔ ∀ j, j + 1 < P.k → Rearm P j := by
  constructor
  · intro hs j hj
    exact Classical.byContradiction fun hn =>
      need_rearm S hj (G j hj) (C (j + 1) hj).H_RACE_UP hn hs
  · intro hr vs pa pb pq pr pd pe pf r a b d c q Bh
    exact sufficientK S ⟨C, hr⟩ Bh

/-! ## 5. Numbers: two tokens, nonzero delays -/

/-- Two tokens, LinkExact's `P0` box (req `[400,520]`, ack `[380,500]`, loop `[300,420]`, rst
`[600,900]`, data `[350,480]`, enable `[450,700]`, latch loop `[280,400]` ps) and token 0 =
`P0`'s token. Token 1's request rises `D` ps after token 0's (`D = 2979`: H_REARM violated by
exactly 1 ps; `D = 3500`: met). -/
def P2 (D : Int) : ParK :=
  { k := 2, W := 2000, W1 := 2001,
    Ra := fun j => if j = 0 then 3000 else 3000 + D,
    Ra1 := fun j => if j = 0 then 3001 else 3001 + D,
    Fa := fun j => if j = 0 then 4500 else 4500 + D,
    Fa1 := fun j => if j = 0 then 4501 else 4501 + D,
    Rb := fun j => if j = 0 then 4300 else 4300 + D,
    Rb1 := fun j => if j = 0 then 4301 else 4301 + D,
    Fb := fun j => if j = 0 then 6000 else 6000 + D,
    Fb1 := fun j => if j = 0 then 6001 else 6001 + D,
    Td := fun j => if j = 0 then 2500 else 5600,
    Tn := fun j => if j = 0 then 5500 else 10000,
    Alo := 400, Ahi := 520, Blo := 380, Bhi := 500, Qlo := 300, Qhi := 420,
    Rlo := 600, Rhi := 900, Dlo := 350, Dhi := 480, Elo := 450, Ehi := 700,
    Flo := 280, Fhi := 400 }

theorem p2k (D : Int) : (P2 D).k = 2 := rfl

theorem p2_wf (D : Int) (h0 : Wf ((P2 D).tok 0)) (h1 : Wf ((P2 D).tok 1))
    (hn : (P2 D).Fa1 0 ≤ (P2 D).Ra 1 ∧ (P2 D).Fb1 0 ≤ (P2 D).Rb 1) : WfK (P2 D) := by
  refine ⟨by rw [p2k]; omega, fun j hj => ?_, fun j hj => ?_⟩
  · rw [p2k] at hj
    rcases j with _ | _ | j
    · exact h0
    · exact h1
    · omega
  · rw [p2k] at hj
    rcases j with _ | j
    · exact hn
    · omega

theorem p2_all {D : Int} {p : Nat → Prop} (h0 : p 0) (h1 : p 1) : ∀ j < (P2 D).k, p j := by
  intro j hj; rw [p2k] at hj
  rcases j with _ | _ | j
  · exact h0
  · exact h1
  · omega

theorem p2_one {D : Int} {p : Nat → Prop} (h0 : p 0) : ∀ j, j + 1 < (P2 D).k → p j := by
  intro j hj; rw [p2k] at hj
  rcases j with _ | j
  · exact h0
  · omega

theorem wfK_bad : WfK (P2 2979) := p2_wf _ (wf_of _ (by decide)) (wf_of _ (by decide)) (by decide)
theorem wfK_ok : WfK (P2 3500) := p2_wf _ (wf_of _ (by decide)) (wf_of _ (by decide)) (by decide)
theorem gap_bad : ∀ j, j + 1 < (P2 2979).k → GapK (P2 2979) j := p2_one (by unfold GapK; decide)
theorem gap_ok : ∀ j, j + 1 < (P2 3500).k → GapK (P2 3500) j := p2_one (by unfold GapK; decide)
theorem conj_bad : ∀ j < (P2 2979).k, Conj ((P2 2979).tok j) :=
  p2_all ((conj_iff _).2 (by decide)) ((conj_iff _).2 (by decide))
theorem conj_ok : ∀ j < (P2 3500).k, Conj ((P2 3500).tok j) :=
  p2_all ((conj_iff _).2 (by decide)) ((conj_iff _).2 (by decide))

/-- At `D = 2979` H_REARM is violated by EXACTLY one tick (`lhs = rhs + 1`), while every other
row of both tokens, the scope and the necessity scope are met. -/
theorem rearm_one_tick :
    (P2 2979).Fb1 0 + (P2 2979).Bhi = (P2 2979).Ra1 1 + (P2 2979).Ahi + 1 ∧
    WfK (P2 2979) ∧ (∀ j, j + 1 < (P2 2979).k → GapK (P2 2979) j) ∧
    (∀ j < (P2 2979).k, Conj ((P2 2979).tok j)) :=
  ⟨by decide, wfK_bad, gap_bad, conj_bad⟩

/-- **Counter-run at slack -1 (real INIT).** At `P2 2979` some behaviour breaks the stage. -/
theorem rearm_breaks : ¬ SafeK (P2 2979) := by
  rw [exact_rearm wfK_bad gap_bad conj_bad]
  intro h
  have := h 0 (by decide)
  revert this; unfold Rearm; decide

/-- The witness's data pin: 1 (token 0) before 5600, then 0 (token 1). -/
def dW (x : Int) : K3 := if x < 5600 then kb true else kb false

/-- **Non-vacuity (two tokens).** At `P2 3500` every hypothesis of `sufficientK` holds, so
every behaviour meets the two-token spec; a behaviour exists (node simulated with every read at
its slowest; data 1 for token 0, then 0 for token 1; latch simulated) and meets it. -/
theorem witness2 :
    WfK (P2 3500) ∧ RowsK (P2 3500) ∧ SafeK (P2 3500) ∧
    ∃ pa pb pq pr pd pe pf r a b d c q,
      BehK (P2 3500) (fun j => decide (j = 0)) pa pb pq pr pd pe pf r a b d c q ∧
      SpecK (P2 3500) (fun j => decide (j = 0)) pd pe c q := by
  have S := wfK_ok
  have H : RowsK (P2 3500) := ⟨conj_ok, p2_one (by unfold Rearm; decide)⟩
  refine ⟨S, H, fun vs pa pb pq pr pd pe pf r a b d c q Bh => sufficientK S H Bh, ?_⟩
  have hQ : 0 < (420 : Int).toNat := by decide
  have hF : 0 < (400 : Int).toNat := by decide
  obtain ⟨c, hc⟩ : ∃ c, CtlEq (Rd.const 520) (Rd.const 500) (Rd.const 420)
      (Rd.const 900) (win 0 2000) (ptrain (P2 3500).k (P2 3500).Ra1 (P2 3500).Fa)
      (ptrain (P2 3500).k (P2 3500).Rb1 (P2 3500).Fb1) c :=
    ⟨_, ctlRun_ctl _ _ _ _ _ _ .f _ hQ⟩
  have Bh : BehK (P2 3500) (fun j => decide (j = 0)) (Rd.const 520) (Rd.const 500)
      (Rd.const 420) (Rd.const 900) (Rd.const 480) (Rd.const 700)
      (Rd.const 400) (win 0 2000) (ptrain (P2 3500).k (P2 3500).Ra1 (P2 3500).Fa)
      (ptrain (P2 3500).k (P2 3500).Rb1 (P2 3500).Fb1) dW c
      (run (lf (Rd.const 480) (Rd.const 700) dW c) (kb false) (400 : Int).toNat hF) := by
    refine ⟨?_, envK_trains S, p2_all ?_ ?_, hc, fun t ht => run_eqQ _ _ _ hF t ht⟩
    · refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide
    · intro x h1 h2
      simp [P2] at h1 h2
      show (if x < 5600 then kb true else kb false) = kb true
      rw [if_pos (by omega)]
    · intro x h1 h2
      simp [P2] at h1 h2
      show (if x < 5600 then kb true else kb false) = kb false
      rw [if_neg (by omega)]
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, Bh, sufficientK S H Bh⟩

end Formal.Cells.ZeroDelayTok
