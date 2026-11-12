import Formal.Cells.LibGapLatch
import Formal.Cells.NecessityReset
import Formal.Cells.CElemFn
import Formal.Cells.ContractsTrunc
open Formal.Core.LutList

/-!
# LinkExact: ONE exact contract for one `bd_link` stage (controller + latch bit + feedbacks)

Probe Blink (shard B); note `formal/notes/B-link-exact.md`. Composes the
per-cell exact results (CElemStrict/CElemStrict2: own-feedback race;
NecessityReset: reset width; LibGapLatch: setup_pulse / setup_data / hold) for
one stage of `cells/rtl/bd_link.v` (`bd_link_ctl` = `bd_c2n`, INIT
`64'h00B2_00B2_00B2_00B2`, I0 = req_in, I1 = ack_out, I2 = c (own feedback),
I3 = rst; latch bit = `bd_latch` odd bit / pair O5 / O6, I1 = en = the node).

## Model (Int ps; every hypothesis named)

* **H_CTL_READ** (`CtlEq`): for `t ≥ 0` the node `c t` is the real INIT
  (Kleene, `CElemFn.c2nK`) of its four pins, EACH read through its own read
  map (`LibGapSteer.Rd`, window `[t - hi, t - lo]`, NOT necessarily monotone).
  Power-up (`t < 0`) arbitrary, X included.
* **H_PIN_READ** (`LibGapLatch.LutEq`): the latch bit reads d, the NODE (its
  enable branch) and its own output through three more read maps.
* **H_BOX** (`Box`): the seven maps in their windows: req `[Alo,Ahi]`, ack
  `[Blo,Bhi]`, controller loop `[Qlo,Qhi]` (`Qlo ≥ 1`), rst `[Rlo,Rhi]`, data
  `[Dlo,Dhi]`, enable `[Elo,Ehi]`, latch loop `[Flo,Fhi]` (`Flo ≥ 1`).
* **H_ENV** (`Env`, one token, open loop): rst 1 on `[0,W)`, 0 from `W1`;
  req 0 before `Ra`, 1 on `[Ra1,Fa)`, 0 from `Fa1`; ack 0 before `Rb`, 1 on
  `[Rb1,Fb)`, 0 from `Fb1`; ARBITRARY (glitches, X) in every gap.
  **H_D_STABLE** (`DStab`): data `v` on `[Td,Tn)`, arbitrary elsewhere.
* Scope `Wf`: ordered windows, **H_RST_EARLY(_ACK)** (rst surely read 0 before
  req or ack can be read moved), **H_ACK_ORDER** (`V1 ≤ Fb + Blo`, implied by
  H_RACE_DN). Necessity additionally assumes **H_REL_SPLIT** (`Split`).

Derived node times (the inputs as read): `U0 = Ra+Alo`, `U1 = Ra1+Ahi`,
`Rel = min (Fa+Alo) (Rb+Blo)`, `V0 = max (Fa+Alo) (Rb+Blo)`,
`V1 = max (Fa1+Ahi) (Rb1+Bhi)`.

## Spec (`Spec`): one four-phase token, captured and held

The node is a window token: 0 on `[Rhi, U0)`, 1 on the NONEMPTY `[U1, V0)`, 0
on `[V1, ∞)` (arbitrary only inside its own inputs' read windows); the latch
captures (`LibGapLatch.Capt` with `B = V0`) and its output is `v` from
`max (U1 + pe.hi) (Td + pd.hi)` on, for ever.

## Results

* `sufficient`: `Conj` ⇒ spec, for every behaviour in the box.
* `exact` (headline): under `Wf` and `Split`, `SafeLink ↔ Conj` with
  `H_RST_WIDTH : Rhi + Qhi ≤ W + Rlo`, `H_RACE_UP : U1 + Qhi ≤ Rel`,
  `H_RACE_DN : V1 + Qhi ≤ Fb + Blo`, `H_SETUP_PULSE : U1 + Ehi + Fhi ≤ V0 + Elo`,
  `H_SETUP_DATA : Td + Dhi + Fhi ≤ V0 + Elo`, `H_HOLD : V1 + Ehi ≤ Tn + Dlo`.
  Necessity: `need_rst`, `need_up`, `need_dn`, `need_pulse`, `need_data`,
  `need_hold`, each an explicit run (simulated controller and latch, read maps
  constant or two-phase) that breaks the spec.
* `no_cross`: the same iff with the per-cell theorems' own left sides
  (`NecessityReset.c2n_box_exact`, `LibGapLatch.SafeBox` at `A,B,C := U1,V0,V1`):
  composition adds NO cross-cell condition; the coupling is only the
  substitution of the node's window token into the latch's enable times.
* `strict_edges`: with one tick of X before every binary edge, all six are strict.
* `witness`: slow-corner-scale numbers `P0` meeting everything, with a run.
  `Pv_one_tick` / `Pv_breaks`: for each conjunct a parameter set violating
  ONLY it, by exactly 1 ps, on which some behaviour breaks the stage.
* `rout_definite`, `out_port`: C's one-token `Contracts.PortUpTo` for the
  output channel, given the named wire hypotheses `H_ROUT` (clean request
  pin), `H_ACK`, `H_ORDER`, `H_X_LEAD`.

NOT covered: the closed loop (the environment's event times are parameters;
the races become latency inequalities only once the partners are composed);
the tie `Fa + Alo = Rb + Blo` (necessity of H_RACE_UP there is NOT decided);
more than one token; a W-bit bus beyond "one Beh per bit, shared node";
the input port (C's Port ⇒ `Env`/`DStab`); cleanliness of the request pin
(not derivable for window wires, `WinFifo`); correlated corners (box).
Core Lean only.
-/

namespace Formal.Cells.LinkExact
open Formal.Cells
open Formal.Cells.CElemFn
open Formal.Cells.LibGapSteer (Rd Rd.const)
open Formal.Cells.LibGapMux (int_ind)
open Formal.Cells.LibGapLatch

/-! ## 0. Kleene facts of the real `bd_c2n` INIT (pins I0 = a, I1 = b, I2 = q, I3 = rst) -/

theorem c_rst : ∀ a b q : K3, c2nK a b q .t = .f := by decide
theorem c_idle : ∀ r : K3, c2nK .f .f .f r = .f := by decide
theorem c_follow1 : ∀ q : K3, c2nK .t .f q .f = .t := by decide
theorem c_holdA : ∀ a : K3, c2nK a .f .t .f = .t := by decide
theorem c_holdB : ∀ b : K3, c2nK .t b .t .f = .t := by decide
theorem c_follow0 : ∀ q r : K3, c2nK .f .t q r = .f := by decide
theorem c_hold0 : ∀ b r : K3, c2nK .f b .f r = .f := by decide

/-! ## 1. Parameters, scope, behaviours, spec -/

/-- One token through one `bd_link` stage. Driver/pin-trace event times
(definite-window convention: a trace is DEFINITE on the stated intervals and
ARBITRARY, X included, in between) and the per-pin read-map box. -/
structure Par where
  W : Int
  W1 : Int
  Ra : Int
  Ra1 : Int
  Fa : Int
  Fa1 : Int
  Rb : Int
  Rb1 : Int
  Fb : Int
  Fb1 : Int
  Td : Int
  Tn : Int
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
deriving DecidableEq, Repr

namespace Par
variable (P : Par)
/-- Earliest instant the node can read the request rise. -/
def U0 : Int := P.Ra + P.Alo
/-- Instant from which the node surely reads the request high. -/
def U1 : Int := P.Ra1 + P.Ahi
/-- Earliest instant the FIRST release (req fall or ack rise) can be read. -/
def Rel : Int := min (P.Fa + P.Alo) (P.Rb + P.Blo)
/-- Earliest instant BOTH releases can be read (the node may start to fall). -/
def V0 : Int := max (P.Fa + P.Alo) (P.Rb + P.Blo)
/-- Instant from which both releases are surely read (the node must be 0). -/
def V1 : Int := max (P.Fa1 + P.Ahi) (P.Rb1 + P.Bhi)
end Par

/-- **Scope** (named, not part of the exact conjunction): well-formed boxes,
`Qlo, Flo ≥ 1` (positive loops), ordered windows, and **H_RST_EARLY**: rst is
surely read 0 before the request can be read 1. -/
structure Wf (P : Par) : Prop where
  hA : 0 ≤ P.Alo ∧ P.Alo ≤ P.Ahi
  hB : 0 ≤ P.Blo ∧ P.Blo ≤ P.Bhi
  hQ : 1 ≤ P.Qlo ∧ P.Qlo ≤ P.Qhi
  hR : 0 ≤ P.Rlo ∧ P.Rlo ≤ P.Rhi
  hD : 0 ≤ P.Dlo ∧ P.Dlo ≤ P.Dhi
  hE : 0 ≤ P.Elo ∧ P.Elo ≤ P.Ehi
  hF : 1 ≤ P.Flo ∧ P.Flo ≤ P.Fhi
  hW : 0 ≤ P.W ∧ P.W ≤ P.W1
  ha : P.Ra ≤ P.Ra1 ∧ P.Ra1 ≤ P.Fa ∧ P.Fa ≤ P.Fa1
  hb : P.Rb ≤ P.Rb1 ∧ P.Rb1 ≤ P.Fb ∧ P.Fb ≤ P.Fb1
  H_RST_EARLY : P.W1 + P.Rhi < P.Ra + P.Alo
  /-- **H_RST_EARLY_ACK**: the same for the acknowledge. -/
  H_RST_EARLY_ACK : P.W1 + P.Rhi < P.Rb + P.Blo
  /-- **H_ACK_ORDER**: the acknowledge fall cannot be read before the node is
  surely low (`V1`). Implied by `H_RACE_DN` (so it costs the iff nothing
  inside the conjunction). -/
  H_ACK_ORDER : P.V1 ≤ P.Fb + P.Blo

/-- **H_ENV** (the environment, one token): rst (I3) high on `[0, W)`, low from
`W1`; req_in (I0) low before `Ra`, high on `[Ra1, Fa)`, low from `Fa1`;
ack_out (I1) low before `Rb`, high on `[Rb1, Fb)`, low from `Fb1`. ARBITRARY
(any Kleene value, glitches and X included) everywhere else, rst also before 0
(power-up). -/
structure Env (P : Par) (r a b : Int → K3) : Prop where
  r_hi : ∀ x, 0 ≤ x → x < P.W → r x = .t
  r_lo : ∀ x, P.W1 ≤ x → r x = .f
  a_lo0 : ∀ x, x < P.Ra → a x = .f
  a_hi : ∀ x, P.Ra1 ≤ x → x < P.Fa → a x = .t
  a_lo : ∀ x, P.Fa1 ≤ x → a x = .f
  b_lo0 : ∀ x, x < P.Rb → b x = .f
  b_hi : ∀ x, P.Rb1 ≤ x → x < P.Fb → b x = .t
  b_lo : ∀ x, P.Fb1 ≤ x → b x = .f

/-- **H_BOX**: every per-pin read map in its window. -/
structure Box (P : Par) (pa pb pq pr pd pe pf : Rd) : Prop where
  a : P.Alo ≤ pa.lo ∧ pa.hi ≤ P.Ahi
  b : P.Blo ≤ pb.lo ∧ pb.hi ≤ P.Bhi
  q : P.Qlo ≤ pq.lo ∧ pq.hi ≤ P.Qhi
  r : P.Rlo ≤ pr.lo ∧ pr.hi ≤ P.Rhi
  d : P.Dlo ≤ pd.lo ∧ pd.hi ≤ P.Dhi
  e : P.Elo ≤ pe.lo ∧ pe.hi ≤ P.Ehi
  f : P.Flo ≤ pf.lo ∧ pf.hi ≤ P.Fhi

/-- **H_CTL_READ**: the controller node `c` (bd_c2n, real INIT, Kleene) reads
each of its four pins through its own read map (non-monotone allowed). Before
time 0 the node is arbitrary (power-up). -/
def CtlEq (pa pb pq pr : Rd) (r a b c : Int → K3) : Prop :=
  ∀ t, 0 ≤ t → c t = c2nK (a (pa.σ t)) (b (pb.σ t)) (c (pq.σ t)) (r (pr.σ t))

/-- A behaviour of the stage: box, environment, data, controller, latch bit
(`LibGapLatch.LutEq`: the latch's enable pin reads the NODE `c` through `pe`). -/
structure Beh (P : Par) (v : Bool) (pa pb pq pr pd pe pf : Rd) (r a b d c q : Int → K3) : Prop where
  box : Box P pa pb pq pr pd pe pf
  env : Env P r a b
  dat : DStab v P.Td P.Tn d
  ctl : CtlEq pa pb pq pr r a b c
  lat : LutEq pd pe pf d c q

/-- **The stage spec (one four-phase token, captured and held).** The node is
a window token with the input-derived edges: reset 0 on `[Rhi, U0)`, high on
the nonempty `[U1, V0)`, low from `V1` for ever (arbitrary only inside the
read windows of its own inputs); the latch bit captures (`LibGapLatch.Capt`)
and its output is the token's value from `max (U1 + pe.hi) (Td + pd.hi)` on,
for ever. -/
structure Spec (P : Par) (v : Bool) (pd pe : Rd) (c q : Int → K3) : Prop where
  nonempty : P.U1 < P.V0
  rst : ∀ t, P.Rhi ≤ t → t < P.U0 → c t = .f
  hi : ∀ t, P.U1 ≤ t → t < P.V0 → c t = .t
  lo : ∀ t, P.V1 ≤ t → c t = .f
  capt : Capt v P.V0 pe q
  out : ∀ t, P.U1 + pe.hi ≤ t → P.Td + pd.hi ≤ t → q t = kb v

/-- Every behaviour in the box meets the spec. -/
def SafeLink (P : Par) (v : Bool) : Prop :=
  ∀ pa pb pq pr pd pe pf r a b d c q, Beh P v pa pb pq pr pd pe pf r a b d c q →
    Spec P v pd pe c q

/-- **The conjunction of the per-cell exact conditions**, instantiated at the
composed stage. -/
structure Conj (P : Par) : Prop where
  /-- bd_c2n reset width (`NecessityReset.c2n_box_exact`). -/
  H_RST_WIDTH : P.Rhi + P.Qhi ≤ P.W + P.Rlo
  /-- own-feedback race of the rise (`CElemStrict`, read-map form). -/
  H_RACE_UP : P.U1 + P.Qhi ≤ P.Rel
  /-- own-feedback race of the fall. -/
  H_RACE_DN : P.V1 + P.Qhi ≤ P.Fb + P.Blo
  /-- latch setup_pulse with `A, B := U1, V0` (`LibGapLatch.box_exact`). -/
  H_SETUP_PULSE : P.U1 + P.Ehi + P.Fhi ≤ P.V0 + P.Elo
  /-- latch setup_data. -/
  H_SETUP_DATA : P.Td + P.Dhi + P.Fhi ≤ P.V0 + P.Elo
  /-- latch hold with `C := V1`. -/
  H_HOLD : P.V1 + P.Ehi ≤ P.Tn + P.Dlo

/-! ## 2. Sufficiency -/

section suff
variable {P : Par} {v : Bool} {pa pb pq pr pd pe pf : Rd} {r a b d c q : Int → K3}

theorem node_rst (S : Wf P) (B : Box P pa pb pq pr pd pe pf) (E : Env P r a b)
    (hc : CtlEq pa pb pq pr r a b c) (h1 : P.Rhi + P.Qhi ≤ P.W + P.Rlo)
    (h2 : P.U1 + P.Qhi ≤ P.Rel) :
    ∀ t, P.Rhi ≤ t → t < P.U0 → c t = .f := by
  have s1 := S.hR; have s2 := S.hQ; have s3 := S.hA; have s4 := S.hB; have s5 := S.ha
  have b1 := B.a; have b2 := B.b; have b3 := B.q; have b4 := B.r
  simp only [Par.U0, Par.U1, Par.Rel] at *
  apply int_ind (fun t => P.Rhi ≤ t → t < P.Ra + P.Alo → c t = .f) (fun t ht h => by omega)
  intro t ht ih h3 h4
  rw [hc t ht]
  have g1 := pr.ge t; have g2 := pr.le t; have g3 := pq.ge t; have g4 := pq.le t
  have g5 := pa.le t; have g6 := pb.le t
  by_cases hw : t < P.W + P.Rlo
  · rw [E.r_hi _ (by omega) (by omega), c_rst]
  · rw [E.a_lo0 _ (by omega), E.b_lo0 _ (by omega), ih _ (by omega) (by omega) (by omega), c_idle]

theorem node_hi (S : Wf P) (B : Box P pa pb pq pr pd pe pf) (E : Env P r a b)
    (hc : CtlEq pa pb pq pr r a b c) (h2 : P.U1 + P.Qhi ≤ P.Rel) :
    ∀ t, P.U1 ≤ t → t < P.V0 → c t = .t := by
  have s1 := S.hR; have s2 := S.hQ; have s3 := S.hA; have s4 := S.hB; have s5 := S.ha
  have s6 := S.H_RST_EARLY; have s7 := S.hW
  have b1 := B.a; have b2 := B.b; have b3 := B.q; have b4 := B.r
  simp only [Par.U1, Par.Rel, Par.V0] at *
  apply int_ind (fun t => P.Ra1 + P.Ahi ≤ t → t < max (P.Fa + P.Alo) (P.Rb + P.Blo) → c t = .t)
    (fun t ht h => by omega)
  intro t ht ih h3 h4
  rw [hc t ht]
  have g1 := pr.ge t; have g3 := pq.ge t; have g4 := pq.le t
  have g5 := pa.le t; have g6 := pb.le t; have g7 := pa.ge t
  rw [E.r_lo _ (by omega)]
  by_cases h5 : t < P.Fa + P.Alo ∧ t < P.Rb + P.Blo
  · rw [E.a_hi _ (by omega) (by omega), E.b_lo0 _ (by omega), c_follow1]
  · rw [ih _ (by omega) (by omega) (by omega)]
    by_cases h6 : t < P.Fa + P.Alo
    · rw [E.a_hi _ (by omega) (by omega), c_holdB]
    · rw [E.b_lo0 _ (by omega), c_holdA]

theorem node_lo (S : Wf P) (B : Box P pa pb pq pr pd pe pf) (E : Env P r a b)
    (hc : CtlEq pa pb pq pr r a b c) (h3 : P.V1 + P.Qhi ≤ P.Fb + P.Blo) :
    ∀ t, P.V1 ≤ t → c t = .f := by
  have s1 := S.hR; have s2 := S.hQ; have s3 := S.hA; have s4 := S.hB; have s5 := S.ha
  have s6 := S.H_RST_EARLY; have s7 := S.hW; have s8 := S.hb
  have b1 := B.a; have b2 := B.b; have b3 := B.q
  simp only [Par.V1] at *
  apply int_ind (fun t => max (P.Fa1 + P.Ahi) (P.Rb1 + P.Bhi) ≤ t → c t = .f)
    (fun t ht h => by omega)
  intro t ht ih h4
  rw [hc t ht]
  have g3 := pq.ge t; have g4 := pq.le t
  have g5 := pa.ge t; have g6 := pb.le t; have g7 := pb.ge t
  rw [E.a_lo _ (by omega)]
  by_cases h5 : t < P.Fb + P.Blo
  · rw [E.b_hi _ (by omega) (by omega), c_follow0]
  · rw [ih _ (by omega) (by omega), c_hold0]

/-- **Sufficiency**: the conjunction gives the stage spec for EVERY behaviour
in the box (any read maps, any admissible environment and data, any power-up). -/
theorem sufficient (S : Wf P) (H : Conj P) (Bh : Beh P v pa pb pq pr pd pe pf r a b d c q) :
    Spec P v pd pe c q := by
  have B := Bh.box
  have N1 := node_rst S B Bh.env Bh.ctl H.H_RST_WIDTH H.H_RACE_UP
  have N2 := node_hi S B Bh.env Bh.ctl H.H_RACE_UP
  have N3 := node_lo S B Bh.env Bh.ctl H.H_RACE_DN
  have s1 := S.hR; have s2 := S.hQ; have s3 := S.hA; have s4 := S.hB; have s5 := S.ha
  have s6 := S.H_RST_EARLY; have s7 := S.hW; have s8 := S.hb; have s9 := S.hD
  have s10 := S.hE; have s11 := S.hF
  have b1 := B.d; have b2 := B.e; have b3 := B.f
  have h1 := H.H_RACE_UP; have h2 := H.H_SETUP_PULSE; have h3 := H.H_SETUP_DATA
  have h4 := H.H_HOLD
  simp only [Par.U0, Par.U1, Par.Rel, Par.V0, Par.V1] at *
  have hT : EnTok (P.Ra1 + P.Ahi) (max (P.Fa + P.Alo) (P.Rb + P.Blo))
      (max (P.Fa1 + P.Ahi) (P.Rb1 + P.Bhi)) c := ⟨N2, N3⟩
  have hcap : Capt v (max (P.Fa + P.Alo) (P.Rb + P.Blo)) pe q :=
    latch_pin_ok v _ _ _ P.Td P.Tn pd pe pf d c q (by omega) (by omega) (by omega) hT Bh.dat
      Bh.lat (by omega) (by omega) (by omega)
  refine ⟨by simp only [Par.U1, Par.V0]; omega, N1, N2, N3, hcap, ?_⟩
  intro t ht1 ht2
  simp only [Par.U1] at ht1
  have g1 := pe.ge t; have g2 := pe.le t; have g3 := pd.ge t; have g4 := pd.le t
  by_cases hB : max (P.Fa + P.Alo) (P.Rb + P.Blo) ≤ pe.σ t
  · exact hcap t (by omega) hB
  · rw [Bh.lat t (by omega), N2 _ (by omega) (by omega), m_t]
    exact Bh.dat _ (by omega) (by omega)

end suff
/-! ## 3. Necessity machinery: adversarial traces and simulators -/

/-- A sharp pulse: 1 on `[lo, hi)`, 0 elsewhere. -/
def win (lo hi : Int) (x : Int) : K3 := if lo ≤ x ∧ x < hi then .t else .f

theorem win_t {lo hi x : Int} (h1 : lo ≤ x) (h2 : x < hi) : win lo hi x = .t := by
  simp [win, h1, h2]
theorem win_f1 {lo hi x : Int} (h : x < lo) : win lo hi x = .f := by
  simp only [win]; rw [ite_eq_right (by omega)]
theorem win_f2 {lo hi x : Int} (h : hi ≤ x) : win lo hi x = .f := by
  simp only [win]; rw [ite_eq_right (by omega)]

theorem env_win {P : Par} (S : Wf P) {la ha lb hb : Int}
    (h1 : P.Ra ≤ la ∧ la ≤ P.Ra1) (h2 : P.Fa ≤ ha ∧ ha ≤ P.Fa1)
    (h3 : P.Rb ≤ lb ∧ lb ≤ P.Rb1) (h4 : P.Fb ≤ hb ∧ hb ≤ P.Fb1) :
    Env P (win 0 P.W) (win la ha) (win lb hb) := by
  have := S.hW
  exact ⟨fun x h5 h6 => win_t h5 h6, fun x h5 => win_f2 (by omega),
    fun x h5 => win_f1 (by omega), fun x h5 h6 => win_t (by omega) (by omega),
    fun x h5 => win_f2 (by omega), fun x h5 => win_f1 (by omega),
    fun x h5 h6 => win_t (by omega) (by omega), fun x h5 => win_f2 (by omega)⟩

theorem two_lt {K lo hi t : Int} {h : lo ≤ hi} (ht : t < K) : (Rd.two K lo hi h).σ t = t - hi := by
  simp [Rd.two, ht]
theorem two_ge {K lo hi t : Int} {h : lo ≤ hi} (ht : K ≤ t) : (Rd.two K lo hi h).σ t = t - lo := by
  simp only [Rd.two]; rw [ite_eq_right (by omega)]

theorem eAdv_ge {A B C x : Int} (h0 : A ≤ B) (h1 : B ≤ C) (h : C ≤ x) : eAdv A B C x = .f := by
  simp only [eAdv]; rw [ite_eq_right (by omega), ite_eq_right (by omega), ite_eq_right (by omega)]

theorem run_eqQ (f : Int → K3 → K3) (q0 : K3) (Q : Int) (hQ : 0 < Q.toNat) (t : Int) (ht : 0 ≤ t) :
    run f q0 Q.toNat hQ t = f t (run f q0 Q.toNat hQ (t - Q)) := by
  rw [run_eq f q0 Q.toNat hQ t ht]
  have : ((Q.toNat : Nat) : Int) = Q := by omega
  rw [this]

/-- The controller's next-state function for given pin read maps. -/
def ctlF (pa pb pr : Rd) (r a b : Int → K3) (t : Int) (qq : K3) : K3 :=
  c2nK (a (pa.σ t)) (b (pb.σ t)) qq (r (pr.σ t))

/-- The controller simulator: feedback read at the constant delay `Q`. -/
def ctlRun (pa pb pr : Rd) (r a b : Int → K3) (c0 : K3) (Q : Int) (hQ : 0 < Q.toNat) : Int → K3 :=
  run (ctlF pa pb pr r a b) c0 Q.toNat hQ

theorem ctlRun_ctl (pa pb pr : Rd) (r a b : Int → K3) (c0 : K3) (Q : Int) (hQ : 0 < Q.toNat) :
    CtlEq pa pb (Rd.const Q) pr r a b (ctlRun pa pb pr r a b c0 Q hQ) := by
  intro t ht
  exact run_eqQ _ c0 Q hQ t ht

theorem ctlRun_eq {pa pb pr : Rd} {r a b : Int → K3} {c0 : K3} {Q : Int} {hQ : 0 < Q.toNat}
    (t : Int) (ht : 0 ≤ t) :
    ctlRun pa pb pr r a b c0 Q hQ t =
      c2nK (a (pa.σ t)) (b (pb.σ t)) (ctlRun pa pb pr r a b c0 Q hQ (t - Q)) (r (pr.σ t)) :=
  run_eqQ _ c0 Q hQ t ht

theorem ctlRun_neg {pa pb pr : Rd} {r a b : Int → K3} {c0 : K3} {Q : Int} {hQ : 0 < Q.toNat}
    (t : Int) (ht : t < 0) : ctlRun pa pb pr r a b c0 Q hQ t = c0 :=
  run_neg _ c0 _ hQ t ht

theorem c_hold_any : ∀ q : K3, c2nK .f .f q .f = q := by decide
theorem c_both : c2nK .t .t .f .f = .f := by decide

/-- Every completed set of traces is a behaviour (the latch simulated with
feedback delay `Fhi`, power-up `!v`). -/
theorem mkBeh {P : Par} (v : Bool) (S : Wf P) {pa pb pr pd pe : Rd} {r a b c : Int → K3}
    (hbox : Box P pa pb (Rd.const P.Qhi) pr pd pe (Rd.const P.Fhi))
    (hE : Env P r a b) (hc : CtlEq pa pb (Rd.const P.Qhi) pr r a b c) (hF : 0 < P.Fhi.toNat) :
    Beh P v pa pb (Rd.const P.Qhi) pr pd pe (Rd.const P.Fhi) r a b (dAdv v P.Td P.Tn) c
      (run (lf pd pe (dAdv v P.Td P.Tn) c) (kb (!v)) P.Fhi.toNat hF) := by
  refine ⟨hbox, hE, dAdv_stab v _ _, hc, ?_⟩
  intro t ht
  exact run_eqQ _ _ P.Fhi hF t ht

/-! ## 4. Necessity, one conjunct at a time -/

section need
variable {P : Par} {v : Bool}

theorem qpos (S : Wf P) : 0 < P.Qhi.toNat := by have := S.hQ; omega
theorem fpos (S : Wf P) : 0 < P.Fhi.toNat := by have := S.hF; omega

/-- **Reset width is needed.** If `W + Rlo < Rhi + Qhi`, the run with rst read
late at its rise and early at its fall (`Rd.two`), the loop at `Qhi` and the
node powered up at 1 shows 1 at `max Rhi (W + Rlo)`, where the spec says 0. -/
theorem need_rst (S : Wf P) (h : P.W + P.Rlo < P.Rhi + P.Qhi) : ¬ SafeLink P v := by
  intro hs
  have s1 := S.hR; have s2 := S.hQ; have s3 := S.hA; have s4 := S.hB; have s5 := S.ha
  have s6 := S.H_RST_EARLY; have s7 := S.hW; have s8 := S.hb; have s9 := S.hD
  have s10 := S.hE; have s11 := S.hF; have s12 := S.H_RST_EARLY_ACK
  let pr := Rd.two (P.W + P.Rlo) P.Rlo P.Rhi s1.2
  obtain ⟨c, hc, h0⟩ : ∃ c, CtlEq (Rd.const P.Ahi) (Rd.const P.Blo) (Rd.const P.Qhi) pr
      (win 0 P.W) (win P.Ra1 P.Fa) (win P.Rb P.Fb) c ∧ ∀ t, t < 0 → c t = .t :=
    ⟨_, ctlRun_ctl _ _ _ _ _ _ .t P.Qhi (qpos S), fun t ht => ctlRun_neg t ht⟩
  have hbox : Box P (Rd.const P.Ahi) (Rd.const P.Blo) (Rd.const P.Qhi) pr (Rd.const P.Dhi)
      (Rd.const P.Elo) (Rd.const P.Fhi) := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      simp only [Rd.const, pr, Rd.two] <;> omega
  have hE := env_win S (la := P.Ra1) (ha := P.Fa) (lb := P.Rb) (hb := P.Fb)
    ⟨s5.1, Int.le_refl _⟩ ⟨Int.le_refl _, s5.2.2⟩ ⟨Int.le_refl _, s8.1⟩ ⟨Int.le_refl _, s8.2.2⟩
  have Bh := mkBeh v S hbox hE hc (fpos S)
  have sp := hs _ _ _ _ _ _ _ _ _ _ _ _ _ Bh
  have hpre : ∀ t, t < P.Rhi → c t = .t := by
    apply int_ind (fun t => t < P.Rhi → c t = .t) (fun t ht _ => h0 t ht)
    intro t ht ih h1
    rw [hc t ht]
    simp only [Rd.const]
    rw [win_f1 (by omega), win_f1 (by omega), ih _ (by omega) (by omega)]
    by_cases hk : t < P.W + P.Rlo
    · rw [two_lt hk, win_f1 (by omega), c_hold_any]
    · rw [two_ge (by omega), win_f2 (by omega), c_hold_any]
  have key : c (max P.Rhi (P.W + P.Rlo)) = .t := by
    rw [hc _ (by omega)]
    simp only [Rd.const]
    rw [win_f1 (by omega), win_f1 (by omega), two_ge (by omega), win_f2 (by omega),
      hpre _ (by omega), c_hold_any]
  have := sp.rst (max P.Rhi (P.W + P.Rlo)) (by omega) (by simp only [Par.U0]; omega)
  rw [key] at this
  exact absurd this (by decide)

/-- **The rise race is needed** (release pins split: their earliest reads
differ). The first release is read at its earliest, the request rise at its
latest, the loop at `Qhi`: at `max U1 (first release)` the node reads its own
pre-rise 0 and holds it, where the spec says 1 (or the high phase is empty). -/
theorem need_up (S : Wf P) (hsplit : P.Fa + P.Alo ≠ P.Rb + P.Blo)
    (h : P.Rel < P.U1 + P.Qhi) : ¬ SafeLink P v := by
  intro hs
  have s1 := S.hR; have s2 := S.hQ; have s3 := S.hA; have s4 := S.hB; have s5 := S.ha
  have s6 := S.H_RST_EARLY; have s7 := S.hW; have s8 := S.hb; have s9 := S.hD
  have s10 := S.hE; have s11 := S.hF; have s12 := S.H_RST_EARLY_ACK; have s13 := S.H_ACK_ORDER
  simp only [Par.Rel, Par.U1, Par.V1] at h s13
  have hE := env_win S (la := P.Ra1) (ha := P.Fa) (lb := P.Rb) (hb := P.Fb)
    ⟨s5.1, Int.le_refl _⟩ ⟨Int.le_refl _, s5.2.2⟩ ⟨Int.le_refl _, s8.1⟩ ⟨Int.le_refl _, s8.2.2⟩
  rcases Int.lt_or_gt_of_ne hsplit with hab | hab
  · -- the request fall is read first
    let pa := Rd.two (P.Fa + P.Alo) P.Alo P.Ahi s3.2
    obtain ⟨c, hc, h0⟩ : ∃ c, CtlEq pa (Rd.const P.Blo) (Rd.const P.Qhi) (Rd.const P.Rhi)
        (win 0 P.W) (win P.Ra1 P.Fa) (win P.Rb P.Fb) c ∧ ∀ t, t < 0 → c t = .f :=
      ⟨_, ctlRun_ctl _ _ _ _ _ _ .f P.Qhi (qpos S), fun t ht => ctlRun_neg t ht⟩
    have hbox : Box P pa (Rd.const P.Blo) (Rd.const P.Qhi) (Rd.const P.Rhi) (Rd.const P.Dhi)
        (Rd.const P.Elo) (Rd.const P.Fhi) := by
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
        simp only [Rd.const, pa, Rd.two] <;> omega
    have Bh := mkBeh v S hbox hE hc (fpos S)
    have sp := hs _ _ _ _ _ _ _ _ _ _ _ _ _ Bh
    have hne := sp.nonempty
    simp only [Par.U1, Par.V0] at hne
    have hpre : ∀ t, t < P.Ra1 + P.Ahi → c t = .f := by
      apply int_ind (fun t => t < P.Ra1 + P.Ahi → c t = .f) (fun t ht _ => h0 t ht)
      intro t ht ih h1
      rw [hc t ht]; simp only [Rd.const]; rw [ih _ (by omega) (by omega)]
      by_cases hk : t < P.Fa + P.Alo
      · rw [two_lt hk, win_f1 (by omega), c_hold0]
      · rw [two_ge (by omega), win_f2 (by omega), c_hold0]
    have key : c (max (P.Ra1 + P.Ahi) (P.Fa + P.Alo)) = .f := by
      rw [hc _ (by omega)]
      simp only [Rd.const]
      rw [two_ge (by omega), win_f2 (by omega), win_f1 (by omega), hpre _ (by omega), c_idle]
    have := sp.hi (max (P.Ra1 + P.Ahi) (P.Fa + P.Alo)) (by simp only [Par.U1]; omega)
      (by simp only [Par.V0]; omega)
    rw [key] at this
    exact absurd this (by decide)
  · -- the acknowledge rise is read first
    obtain ⟨c, hc, h0⟩ : ∃ c, CtlEq (Rd.const P.Ahi) (Rd.const P.Blo) (Rd.const P.Qhi)
        (Rd.const P.Rhi) (win 0 P.W) (win P.Ra1 P.Fa) (win P.Rb P.Fb) c ∧ ∀ t, t < 0 → c t = .f :=
      ⟨_, ctlRun_ctl _ _ _ _ _ _ .f P.Qhi (qpos S), fun t ht => ctlRun_neg t ht⟩
    have hbox : Box P (Rd.const P.Ahi) (Rd.const P.Blo) (Rd.const P.Qhi) (Rd.const P.Rhi)
        (Rd.const P.Dhi) (Rd.const P.Elo) (Rd.const P.Fhi) := by
      refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
        simp only [Rd.const] <;> omega
    have Bh := mkBeh v S hbox hE hc (fpos S)
    have sp := hs _ _ _ _ _ _ _ _ _ _ _ _ _ Bh
    have hne := sp.nonempty
    simp only [Par.U1, Par.V0] at hne
    have hpre : ∀ t, t < P.Ra1 + P.Ahi → c t = .f := by
      apply int_ind (fun t => t < P.Ra1 + P.Ahi → c t = .f) (fun t ht _ => h0 t ht)
      intro t ht ih h1
      rw [hc t ht]; simp only [Rd.const]; rw [ih _ (by omega) (by omega)]
      rw [win_f1 (by omega), c_hold0]
    have key : c (max (P.Ra1 + P.Ahi) (P.Rb + P.Blo)) = .f := by
      rw [hc _ (by omega)]
      simp only [Rd.const]
      rw [win_t (by omega) (by omega), win_t (by omega) (by omega), win_f2 (by omega),
        hpre _ (by omega), c_both]
    have := sp.hi (max (P.Ra1 + P.Ahi) (P.Rb + P.Blo)) (by simp only [Par.U1]; omega)
      (by simp only [Par.V0]; omega)
    rw [key] at this
    exact absurd this (by decide)

/-! ### The "late fall" run (`R_hold`): node high on `[U1, V1)` -/

/-- Acknowledge read map of `R_hold`: rise read at `Bhi`, fall read at `Blo`. -/
def pbH (P : Par) (h : P.Blo ≤ P.Bhi) : Rd := Rd.two (P.Fb + P.Blo) P.Blo P.Bhi h

theorem pbH_f (P : Par) (h : P.Blo ≤ P.Bhi) (t : Int)
    (ht : t < P.Rb1 + P.Bhi ∨ P.Fb + P.Blo ≤ t) : win P.Rb1 P.Fb ((pbH P h).σ t) = .f := by
  unfold pbH
  by_cases hk : t < P.Fb + P.Blo
  · rw [two_lt hk, win_f1 (by omega)]
  · rw [two_ge (by omega), win_f2 (by omega)]

theorem pbH_t (P : Par) (h : P.Blo ≤ P.Bhi) (t : Int) (h1 : P.Rb1 + P.Bhi ≤ t)
    (h2 : t < P.Fb + P.Blo) : win P.Rb1 P.Fb ((pbH P h).σ t) = .t := by
  unfold pbH
  rw [two_lt h2, win_t (by omega) (by omega)]

section rhold
variable {P : Par} (S : Wf P) {c : Int → K3}
  (hc : CtlEq (Rd.const P.Ahi) (pbH P S.hB.2) (Rd.const P.Qhi) (Rd.const P.Rhi) (win 0 P.W)
    (win P.Ra1 P.Fa1) (win P.Rb1 P.Fb) c)
  (h0 : ∀ t, t < 0 → c t = .f)

include hc h0 in
theorem rhold_pre : ∀ t, t < P.U1 → c t = .f := by
  simp only [Par.U1]
  apply int_ind (fun t => t < P.Ra1 + P.Ahi → c t = .f) (fun t ht _ => h0 t ht)
  intro t ht ih h1
  rw [hc t ht]; simp only [Rd.const]
  rw [win_f1 (x := t - P.Ahi) (by omega), ih _ (by have := S.hQ; omega) (by have := S.hQ; omega),
    c_hold0]

include hc h0 in
theorem rhold_hi (h2 : P.U1 + P.Qhi ≤ P.Rel) : ∀ t, P.U1 ≤ t → t < P.V1 → c t = .t := by
  have s1 := S.hR; have s2 := S.hQ; have s3 := S.hA; have s4 := S.hB; have s5 := S.ha
  have s6 := S.H_RST_EARLY; have s7 := S.hW; have s8 := S.hb
  have hpre := rhold_pre S hc h0
  simp only [Par.U1, Par.Rel, Par.V1] at *
  apply int_ind (fun t => P.Ra1 + P.Ahi ≤ t → t < max (P.Fa1 + P.Ahi) (P.Rb1 + P.Bhi) → c t = .t)
    (fun t ht h => by omega)
  intro t ht ih h1 h3
  rw [hc t ht]; simp only [Rd.const]
  rw [win_f2 (x := t - P.Rhi) (by omega)]
  by_cases ha : t < P.Fa1 + P.Ahi
  · rw [win_t (x := t - P.Ahi) (by omega) (by omega)]
    by_cases hq : P.Ra1 + P.Ahi ≤ t - P.Qhi
    · rw [ih _ (by omega) hq (by omega), c_holdB]
    · rw [pbH_f P _ t (Or.inl (by omega)), c_follow1]
  · rw [win_f2 (x := t - P.Ahi) (by omega), pbH_f P _ t (by omega),
      ih _ (by omega) (by omega) (by omega), c_holdA]

include hc h0 in
theorem rhold_lo (h2 : P.U1 + P.Qhi ≤ P.Rel) (h3 : P.V1 + P.Qhi ≤ P.Fb + P.Blo) :
    ∀ t, P.V1 ≤ t → c t = .f := by
  have s1 := S.hR; have s2 := S.hQ; have s3 := S.hA; have s4 := S.hB; have s5 := S.ha
  have s6 := S.H_RST_EARLY; have s7 := S.hW; have s8 := S.hb
  simp only [Par.U1, Par.Rel, Par.V1] at *
  apply int_ind (fun t => max (P.Fa1 + P.Ahi) (P.Rb1 + P.Bhi) ≤ t → c t = .f)
    (fun t ht h => by omega)
  intro t ht ih h1
  rw [hc t ht]; simp only [Rd.const]
  rw [win_f2 (x := t - P.Ahi) (by omega)]
  by_cases hk : t < P.Fb + P.Blo
  · rw [pbH_t P _ t (by omega) hk, c_follow0]
  · rw [pbH_f P _ t (Or.inr (by omega)), ih _ (by omega) (by omega), c_hold0]

include hc h0 in
/-- With both races met, `R_hold`'s node is exactly `eAdv U1 V1 V1`. -/
theorem rhold_eq (h2 : P.U1 + P.Qhi ≤ P.Rel) (h3 : P.V1 + P.Qhi ≤ P.Fb + P.Blo) :
    c = eAdv P.U1 P.V1 P.V1 := by
  have hu : P.U1 ≤ P.V1 := by
    have := S.hQ; have := S.ha; have := S.hA; simp only [Par.U1, Par.Rel, Par.V1] at *; omega
  funext t
  by_cases h1 : t < P.U1
  · rw [rhold_pre S hc h0 t h1, eAdv_lo h1]
  · by_cases h4 : t < P.V1
    · rw [rhold_hi S hc h0 h2 t (by omega) h4, eAdv_on (by omega) h4]
    · rw [rhold_lo S hc h0 h2 h3 t (by omega), eAdv_ge hu (Int.le_refl _) (by omega)]

end rhold

/-! ### The "early fall" run (`R_pulse`): node is `eAdv U1 V0 V0` -/

/-- Request read map of `R_pulse` (and of `need_up`): rise read at `Ahi`,
fall read at `Alo`. -/
def paP (P : Par) (h : P.Alo ≤ P.Ahi) : Rd := Rd.two (P.Fa + P.Alo) P.Alo P.Ahi h

theorem paP_f (P : Par) (h : P.Alo ≤ P.Ahi) (t : Int)
    (ht : t < P.Ra1 + P.Ahi ∨ P.Fa + P.Alo ≤ t) : win P.Ra1 P.Fa ((paP P h).σ t) = .f := by
  unfold paP
  by_cases hk : t < P.Fa + P.Alo
  · rw [two_lt hk, win_f1 (by omega)]
  · rw [two_ge (by omega), win_f2 (by omega)]

theorem paP_t (P : Par) (h : P.Alo ≤ P.Ahi) (t : Int) (h1 : P.Ra1 + P.Ahi ≤ t)
    (h2 : t < P.Fa + P.Alo) : win P.Ra1 P.Fa ((paP P h).σ t) = .t := by
  unfold paP
  rw [two_lt h2, win_t (by omega) (by omega)]

theorem rpulse_eq {P : Par} (S : Wf P) {c : Int → K3}
    (hc : CtlEq (paP P S.hA.2) (Rd.const P.Blo) (Rd.const P.Qhi) (Rd.const P.Rhi) (win 0 P.W)
      (win P.Ra1 P.Fa) (win P.Rb P.Fb) c)
    (h0 : ∀ t, t < 0 → c t = .f)
    (h2 : P.U1 + P.Qhi ≤ P.Rel) (h3 : P.V1 + P.Qhi ≤ P.Fb + P.Blo) :
    c = eAdv P.U1 P.V0 P.V0 := by
  have s1 := S.hR; have s2 := S.hQ; have s3 := S.hA; have s4 := S.hB; have s5 := S.ha
  have s6 := S.H_RST_EARLY; have s7 := S.hW; have s8 := S.hb
  have hu : P.U1 ≤ P.V0 := by simp only [Par.U1, Par.Rel, Par.V0] at *; omega
  funext t
  revert t
  apply int_ind (fun t => c t = eAdv P.U1 P.V0 P.V0 t)
    (fun t ht => by rw [h0 t ht, eAdv_lo (by simp only [Par.U1]; omega)])
  intro t ht ih
  rw [hc t ht]; simp only [Rd.const]
  rw [ih _ (by omega)]
  simp only [Par.U1, Par.Rel, Par.V0, Par.V1] at *
  by_cases h1 : t < P.Ra1 + P.Ahi
  · rw [paP_f P _ t (Or.inl h1), win_f1 (x := t - P.Blo) (by omega),
      eAdv_lo (x := t - P.Qhi) (by omega), eAdv_lo (x := t) (by omega), c_hold0]
  · rw [win_f2 (x := t - P.Rhi) (by omega)]
    by_cases h4 : t < max (P.Fa + P.Alo) (P.Rb + P.Blo)
    · rw [eAdv_on (x := t) (by omega) (by omega)]
      by_cases h5 : t < P.Fa + P.Alo
      · rw [paP_t P _ t (by omega) h5]
        by_cases h6 : t < P.Rb + P.Blo
        · rw [win_f1 (x := t - P.Blo) (by omega), c_follow1]
        · rw [eAdv_on (x := t - P.Qhi) (by omega) (by omega), c_holdB]
      · rw [paP_f P _ t (Or.inr (by omega)), win_f1 (x := t - P.Blo) (by omega),
          eAdv_on (x := t - P.Qhi) (by omega) (by omega), c_holdA]
    · rw [paP_f P _ t (Or.inr (by omega)), eAdv_ge (x := t) hu (Int.le_refl _) (by omega)]
      by_cases h5 : t < P.Fb + P.Blo
      · rw [win_t (x := t - P.Blo) (by omega) (by omega), c_follow0]
      · rw [win_f2 (x := t - P.Blo) (by omega),
          eAdv_ge (x := t - P.Qhi) hu (Int.le_refl _) (by omega), c_hold0]

end need

theorem mkBeh' {P : Par} (v : Bool) (S : Wf P) {pa pb pr pd pe : Rd} {r a b c : Int → K3}
    (hbox : Box P pa pb (Rd.const P.Qhi) pr pd pe (Rd.const P.Fhi))
    (hE : Env P r a b) (hc : CtlEq pa pb (Rd.const P.Qhi) pr r a b c) :
    ∃ q, Beh P v pa pb (Rd.const P.Qhi) pr pd pe (Rd.const P.Fhi) r a b (dAdv v P.Td P.Tn) c q ∧
      ∀ t, t < 0 → q t = kb (!v) :=
  ⟨_, mkBeh v S hbox hE hc (fpos S), fun t ht => run_neg _ _ _ (fpos S) t ht⟩

theorem pdefs (P : Par) : P.U0 = P.Ra + P.Alo ∧ P.U1 = P.Ra1 + P.Ahi ∧
    P.Rel = min (P.Fa + P.Alo) (P.Rb + P.Blo) ∧ P.V0 = max (P.Fa + P.Alo) (P.Rb + P.Blo) ∧
    P.V1 = max (P.Fa1 + P.Ahi) (P.Rb1 + P.Bhi) := ⟨rfl, rfl, rfl, rfl, rfl⟩

/-- **The fall race is needed.** `R_hold` (request fall read late, acknowledge
fall read early, loop at `Qhi`): at `max V1 (Fb + Blo)` the node reads its own
1 and holds it, where the spec says 0. -/
theorem need_dn {P : Par} {v : Bool} (S : Wf P) (h2 : P.U1 + P.Qhi ≤ P.Rel)
    (h : P.Fb + P.Blo < P.V1 + P.Qhi) : ¬ SafeLink P v := by
  intro hs
  have s1 := S.hR; have s2 := S.hQ; have s3 := S.hA; have s4 := S.hB; have s5 := S.ha
  have s6 := S.H_RST_EARLY; have s7 := S.hW; have s8 := S.hb; have s9 := S.hD
  have s10 := S.hE; have s11 := S.hF; have pd := pdefs P
  obtain ⟨c, hc, h0⟩ : ∃ c, CtlEq (Rd.const P.Ahi) (pbH P S.hB.2) (Rd.const P.Qhi) (Rd.const P.Rhi)
      (win 0 P.W) (win P.Ra1 P.Fa1) (win P.Rb1 P.Fb) c ∧ ∀ t, t < 0 → c t = .f :=
    ⟨_, ctlRun_ctl _ _ _ _ _ _ .f P.Qhi (qpos S), fun t ht => ctlRun_neg t ht⟩
  have hbox : Box P (Rd.const P.Ahi) (pbH P S.hB.2) (Rd.const P.Qhi) (Rd.const P.Rhi)
      (Rd.const P.Dhi) (Rd.const P.Elo) (Rd.const P.Fhi) := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      simp only [Rd.const, pbH, Rd.two] <;> omega
  have hE := env_win S (la := P.Ra1) (ha := P.Fa1) (lb := P.Rb1) (hb := P.Fb)
    ⟨s5.1, Int.le_refl _⟩ ⟨s5.2.2, Int.le_refl _⟩ ⟨s8.1, Int.le_refl _⟩ ⟨Int.le_refl _, s8.2.2⟩
  obtain ⟨q, Bh, _⟩ := mkBeh' v S hbox hE hc
  have sp := hs _ _ _ _ _ _ _ _ _ _ _ _ _ Bh
  have hhi := rhold_hi S hc h0 h2
  have key : c (max P.V1 (P.Fb + P.Blo)) = .t := by
    rw [hc _ (by omega)]; simp only [Rd.const]
    rw [win_f2 (x := max P.V1 (P.Fb + P.Blo) - P.Ahi) (by omega),
      pbH_f P _ (max P.V1 (P.Fb + P.Blo)) (Or.inr (by omega)), win_f2 (x := max P.V1 (P.Fb + P.Blo) - P.Rhi) (by omega),
      hhi (max P.V1 (P.Fb + P.Blo) - P.Qhi) (by omega) (by omega), c_hold_any]
  have := sp.lo (max P.V1 (P.Fb + P.Blo)) (by omega)
  rw [key] at this
  exact absurd this (by decide)

/-- **setup_pulse is needed** (controller conditions met). `R_pulse` makes the
node exactly `eAdv U1 V0 V0` (shortest enable pulse the box allows); the
latch's enable rise read at `Ehi`, fall at `Elo` (`LibGapLatch.need_pulse_two`'s
reads): the latch closes on its power-up value. -/
theorem need_pulse {P : Par} {v : Bool} (S : Wf P) (h2 : P.U1 + P.Qhi ≤ P.Rel)
    (h3 : P.V1 + P.Qhi ≤ P.Fb + P.Blo) (h : P.V0 + P.Elo < P.U1 + P.Ehi + P.Fhi) :
    ¬ SafeLink P v := by
  intro hs
  have s1 := S.hR; have s2 := S.hQ; have s3 := S.hA; have s4 := S.hB; have s5 := S.ha
  have s6 := S.H_RST_EARLY; have s7 := S.hW; have s8 := S.hb; have s9 := S.hD
  have s10 := S.hE; have s11 := S.hF; have pd := pdefs P
  obtain ⟨c, hc, h0⟩ : ∃ c, CtlEq (paP P S.hA.2) (Rd.const P.Blo) (Rd.const P.Qhi) (Rd.const P.Rhi)
      (win 0 P.W) (win P.Ra1 P.Fa) (win P.Rb P.Fb) c ∧ ∀ t, t < 0 → c t = .f :=
    ⟨_, ctlRun_ctl _ _ _ _ _ _ .f P.Qhi (qpos S), fun t ht => ctlRun_neg t ht⟩
  have hceq := rpulse_eq S hc h0 h2 h3
  let pe := Rd.two (P.V0 + P.Elo) P.Elo P.Ehi S.hE.2
  have hbox : Box P (paP P S.hA.2) (Rd.const P.Blo) (Rd.const P.Qhi) (Rd.const P.Rhi)
      (Rd.const P.Dhi) pe (Rd.const P.Fhi) := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      simp only [Rd.const, paP, pe, Rd.two] <;> omega
  have hE := env_win S (la := P.Ra1) (ha := P.Fa) (lb := P.Rb) (hb := P.Fb)
    ⟨s5.1, Int.le_refl _⟩ ⟨Int.le_refl _, s5.2.2⟩ ⟨Int.le_refl _, s8.1⟩ ⟨Int.le_refl _, s8.2.2⟩
  obtain ⟨q, Bh, hq0⟩ := mkBeh' v S hbox hE hc
  have sp := hs _ _ _ _ _ _ _ _ _ _ _ _ _ Bh
  have hL : LutEq (Rd.const P.Dhi) pe (Rd.const P.Fhi) (dAdv v P.Td P.Tn)
      (eAdv P.U1 P.V0 P.V0) q := by rw [← hceq]; exact Bh.lat
  have hlow := low v P.U1 P.V0 P.V0 P.Td P.Tn (Rd.const P.Dhi) pe P.Fhi q
    (min (P.U1 + P.Ehi) (P.V0 + P.Elo)) (by omega) hL hq0 (by
      intro t _ ht
      show (if t < P.V0 + P.Elo then t - P.Ehi else t - P.Elo) < P.U1
      rw [ite_eq_left (by omega)]; omega)
  exact bad_fb v P.U1 P.V0 P.V0 P.Td P.Tn (Rd.const P.Dhi) pe P.Fhi q (by omega) (P.V0 + P.Elo)
    (by omega) (by
      show P.V0 ≤ (if P.V0 + P.Elo < P.V0 + P.Elo then P.V0 + P.Elo - P.Ehi else P.V0 + P.Elo - P.Elo)
      rw [ite_eq_right (by omega)]; omega) hL (hlow _ (by omega)) sp.capt

/-- **setup_data is needed** (controller conditions and setup_pulse met):
`R_pulse`, data read at `Dhi`, enable at `Elo`: the latch closes on stale data. -/
theorem need_data {P : Par} {v : Bool} (S : Wf P) (h2 : P.U1 + P.Qhi ≤ P.Rel)
    (h3 : P.V1 + P.Qhi ≤ P.Fb + P.Blo) (h4 : P.U1 + P.Ehi + P.Fhi ≤ P.V0 + P.Elo)
    (h : P.V0 + P.Elo < P.Td + P.Dhi + P.Fhi) : ¬ SafeLink P v := by
  intro hs
  have s1 := S.hR; have s2 := S.hQ; have s3 := S.hA; have s4 := S.hB; have s5 := S.ha
  have s6 := S.H_RST_EARLY; have s7 := S.hW; have s8 := S.hb; have s9 := S.hD
  have s10 := S.hE; have s11 := S.hF; have pd := pdefs P
  obtain ⟨c, hc, h0⟩ : ∃ c, CtlEq (paP P S.hA.2) (Rd.const P.Blo) (Rd.const P.Qhi) (Rd.const P.Rhi)
      (win 0 P.W) (win P.Ra1 P.Fa) (win P.Rb P.Fb) c ∧ ∀ t, t < 0 → c t = .f :=
    ⟨_, ctlRun_ctl _ _ _ _ _ _ .f P.Qhi (qpos S), fun t ht => ctlRun_neg t ht⟩
  have hceq := rpulse_eq S hc h0 h2 h3
  have hbox : Box P (paP P S.hA.2) (Rd.const P.Blo) (Rd.const P.Qhi) (Rd.const P.Rhi)
      (Rd.const P.Dhi) (Rd.const P.Elo) (Rd.const P.Fhi) := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      simp only [Rd.const, paP, Rd.two] <;> omega
  have hE := env_win S (la := P.Ra1) (ha := P.Fa) (lb := P.Rb) (hb := P.Fb)
    ⟨s5.1, Int.le_refl _⟩ ⟨Int.le_refl _, s5.2.2⟩ ⟨Int.le_refl _, s8.1⟩ ⟨Int.le_refl _, s8.2.2⟩
  obtain ⟨q, Bh, _⟩ := mkBeh' v S hbox hE hc
  have sp := hs _ _ _ _ _ _ _ _ _ _ _ _ _ Bh
  have hL : LutEq (Rd.const P.Dhi) (Rd.const P.Elo) (Rd.const P.Fhi) (dAdv v P.Td P.Tn)
      (eAdv P.U1 P.V0 P.V0) q := by rw [← hceq]; exact Bh.lat
  exact bad_fb v P.U1 P.V0 P.V0 P.Td P.Tn _ _ P.Fhi q (by omega) (P.V0 + P.Elo) (by omega)
    (by simp only [Rd.const]; omega) hL
    (transp_bad v P.U1 P.V0 P.V0 P.Td P.Tn _ _ P.Fhi q _ (by omega) (by simp only [Rd.const]; omega)
      (by simp only [Rd.const]; omega) (Or.inl (by simp only [Rd.const]; omega)) hL) sp.capt

/-- **hold is needed** (everything else met): `R_hold` makes the node exactly
`eAdv U1 V1 V1` (latest enable fall the box allows); data read at `Dlo`,
enable at `Ehi`: the next datum walks through before the latch closes. -/
theorem need_hold {P : Par} {v : Bool} (S : Wf P) (h2 : P.U1 + P.Qhi ≤ P.Rel)
    (h3 : P.V1 + P.Qhi ≤ P.Fb + P.Blo) (h4 : P.U1 + P.Ehi + P.Fhi ≤ P.V0 + P.Elo)
    (h : P.Tn + P.Dlo < P.V1 + P.Ehi) : ¬ SafeLink P v := by
  intro hs
  have s1 := S.hR; have s2 := S.hQ; have s3 := S.hA; have s4 := S.hB; have s5 := S.ha
  have s6 := S.H_RST_EARLY; have s7 := S.hW; have s8 := S.hb; have s9 := S.hD
  have s10 := S.hE; have s11 := S.hF; have pd := pdefs P
  obtain ⟨c, hc, h0⟩ : ∃ c, CtlEq (Rd.const P.Ahi) (pbH P S.hB.2) (Rd.const P.Qhi) (Rd.const P.Rhi)
      (win 0 P.W) (win P.Ra1 P.Fa1) (win P.Rb1 P.Fb) c ∧ ∀ t, t < 0 → c t = .f :=
    ⟨_, ctlRun_ctl _ _ _ _ _ _ .f P.Qhi (qpos S), fun t ht => ctlRun_neg t ht⟩
  have hceq := rhold_eq S hc h0 h2 h3
  have hbox : Box P (Rd.const P.Ahi) (pbH P S.hB.2) (Rd.const P.Qhi) (Rd.const P.Rhi)
      (Rd.const P.Dlo) (Rd.const P.Ehi) (Rd.const P.Fhi) := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;>
      simp only [Rd.const, pbH, Rd.two] <;> omega
  have hE := env_win S (la := P.Ra1) (ha := P.Fa1) (lb := P.Rb1) (hb := P.Fb)
    ⟨s5.1, Int.le_refl _⟩ ⟨s5.2.2, Int.le_refl _⟩ ⟨s8.1, Int.le_refl _⟩ ⟨Int.le_refl _, s8.2.2⟩
  obtain ⟨q, Bh, _⟩ := mkBeh' v S hbox hE hc
  have sp := hs _ _ _ _ _ _ _ _ _ _ _ _ _ Bh
  have hL : LutEq (Rd.const P.Dlo) (Rd.const P.Ehi) (Rd.const P.Fhi) (dAdv v P.Td P.Tn)
      (eAdv P.U1 P.V1 P.V1) q := by rw [← hceq]; exact Bh.lat
  have hu := transp_bad v P.U1 P.V1 P.V1 P.Td P.Tn _ _ P.Fhi q (P.V1 - 1 + P.Ehi) (by omega)
    (by simp only [Rd.const]; omega) (by simp only [Rd.const]; omega)
    (Or.inr (by simp only [Rd.const]; omega)) hL
  have hnc := bad_fb v P.U1 P.V1 P.V1 P.Td P.Tn _ _ P.Fhi q (by omega) (P.V1 - 1 + P.Ehi + P.Fhi)
    (by omega) (by simp only [Rd.const]; omega) hL
    (by rw [show P.V1 - 1 + P.Ehi + P.Fhi - P.Fhi = P.V1 - 1 + P.Ehi by omega]; exact hu)
  exact hnc (fun t ht hB => sp.capt t ht (by omega))

/-! ## 5. The exact contract -/

/-- **H_REL_SPLIT** (scope of the necessity half only): the two release
pins' earliest reads differ. At a tie the necessity construction of
`need_up` does not apply, and whether H_RACE_UP is needed there is NOT decided
in this file; `sufficient` does not use this. -/
def Split (P : Par) : Prop := P.Fa + P.Alo ≠ P.Rb + P.Blo

/-- **Headline: one `bd_link` stage, exact.** Under the scope `Wf` and the
split, EVERY behaviour in the per-pin box (non-monotone read maps on all
seven pins, arbitrary power-up, environment and data arbitrary outside their
definite windows) implements the one-token transfer with the data captured
and held **iff** the six per-cell conditions hold. -/
theorem exact {P : Par} {v : Bool} (S : Wf P) (hs : Split P) : SafeLink P v ↔ Conj P := by
  constructor
  · intro hsafe
    by_cases c1 : P.Rhi + P.Qhi ≤ P.W + P.Rlo
    · by_cases c2 : P.U1 + P.Qhi ≤ P.Rel
      · by_cases c3 : P.V1 + P.Qhi ≤ P.Fb + P.Blo
        · by_cases c4 : P.U1 + P.Ehi + P.Fhi ≤ P.V0 + P.Elo
          · by_cases c5 : P.Td + P.Dhi + P.Fhi ≤ P.V0 + P.Elo
            · by_cases c6 : P.V1 + P.Ehi ≤ P.Tn + P.Dlo
              · exact ⟨c1, c2, c3, c4, c5, c6⟩
              · exact absurd hsafe (need_hold S c2 c3 c4 (by omega))
            · exact absurd hsafe (need_data S c2 c3 c4 (by omega))
          · exact absurd hsafe (need_pulse S c2 c3 (by omega))
        · exact absurd hsafe (need_dn S c2 (by omega))
      · exact absurd hsafe (need_up S hs (by omega))
    · exact absurd hsafe (need_rst S (by omega))
  · intro H pa pb pq pr pd pe pf r a b d c q Bh
    exact sufficient S H Bh

/-- Composition adds NO cross-cell condition: the stage is exact iff bd_c2n's
own reset box is safe (`NecessityReset.c2n_box_exact`'s left side, at the
link's idle vector `a = b = 0`), its own two feedback races hold, and
bd_latch's own box is safe (`LibGapLatch.SafeBox`) at the enable times
`A, B, C := U1, V0, V1` that the node's window token delivers. -/
theorem no_cross {P : Par} {v : Bool} (S : Wf P) (hs : Split P) :
    SafeLink P v ↔
      ((∀ pr pq : Rd, P.Rlo ≤ pr.lo → pr.hi ≤ P.Rhi → P.Qlo ≤ pq.lo → pq.hi ≤ P.Qhi →
          ∀ q, NecessityReset.LoopEq NecessityReset.Fc2n0 pr pq P.W q →
            NecessityReset.ResetOK false P.Rhi q) ∧
        P.U1 + P.Qhi ≤ P.Rel ∧ P.V1 + P.Qhi ≤ P.Fb + P.Blo ∧
        LibGapLatch.SafeBox v P.U1 P.V0 P.V1 P.Td P.Tn P.Dlo P.Dhi P.Elo P.Ehi P.Flo P.Fhi) := by
  have s1 := S.hR; have s2 := S.hQ; have s3 := S.hA; have s4 := S.hB; have s5 := S.ha
  have s6 := S.H_RST_EARLY; have s7 := S.hW; have s8 := S.hb; have s9 := S.hD
  have s10 := S.hE; have s11 := S.hF; have pd := pdefs P
  rw [exact S hs, NecessityReset.c2n_box_exact P.W P.Rlo P.Rhi P.Qlo P.Qhi s1.1 s1.2 s2.1 s2.2]
  constructor
  · intro H
    have hAB : P.U1 ≤ P.V0 := by have := H.H_RACE_UP; omega
    refine ⟨H.H_RST_WIDTH, H.H_RACE_UP, H.H_RACE_DN, ?_⟩
    rw [box_exact v _ _ _ _ _ _ _ _ _ _ _ s9.2 s10.2 s11.1 s11.2 hAB (by omega) (by omega)]
    exact ⟨H.H_SETUP_PULSE, H.H_SETUP_DATA, H.H_HOLD⟩
  · rintro ⟨h1, h2, h3, h4⟩
    have hAB : P.U1 ≤ P.V0 := by omega
    rw [box_exact v _ _ _ _ _ _ _ _ _ _ _ s9.2 s10.2 s11.1 s11.2 hAB (by omega) (by omega)] at h4
    exact ⟨h1, h2, h3, h4.1, h4.2.1, h4.2.2⟩

/-- **Binary-edge form, one tick of X on every moving select** (CElemStrict's
convention: each X window ends at the binary edge, `Ra1, Fa1, Rb1, Fb1, W1`
are the binary edges, `Td` the data's binary edge and `Tnew = Tn + 1` the next
datum's): all six conditions are STRICT. -/
theorem strict_edges (P : Par) (hW : P.W1 = P.W + 1) (ha0 : P.Ra1 = P.Ra + 1)
    (ha1 : P.Fa1 = P.Fa + 1) (hb0 : P.Rb1 = P.Rb + 1) (hb1 : P.Fb1 = P.Fb + 1) :
    Conj P ↔
      (P.Rhi + P.Qhi < P.W1 + P.Rlo ∧
       P.Ra1 + P.Ahi + P.Qhi < min (P.Fa1 + P.Alo) (P.Rb1 + P.Blo) ∧
       max (P.Fa1 + P.Ahi) (P.Rb1 + P.Bhi) + P.Qhi < P.Fb1 + P.Blo ∧
       P.Ra1 + P.Ahi + P.Ehi + P.Fhi < max (P.Fa1 + P.Alo) (P.Rb1 + P.Blo) + P.Elo ∧
       P.Td + P.Dhi + P.Fhi < max (P.Fa1 + P.Alo) (P.Rb1 + P.Blo) + P.Elo ∧
       max (P.Fa1 + P.Ahi) (P.Rb1 + P.Bhi) + P.Ehi < (P.Tn + 1) + P.Dlo) := by
  have pd := pdefs P
  constructor
  · intro H
    have := H.H_RST_WIDTH; have := H.H_RACE_UP; have := H.H_RACE_DN; have := H.H_SETUP_PULSE
    have := H.H_SETUP_DATA; have := H.H_HOLD
    omega
  · intro ⟨h1, h2, h3, h4, h5, h6⟩
    exact ⟨by omega, by omega, by omega, by omega, by omega, by omega⟩

/-! ## 6. Numbers: a witness, and one 1-tick violation per conjunct

Illustrative slow-corner-scale numbers in ps, ONE corner (every window is a
spread inside that corner: routed wire + site pin + LUT arc; LUT arcs at most
124 ps SLOW_MAX, the rest wire/site pin), not read from a route. Pins:
req `[400,520]`, ack `[380,500]`, controller loop `[300,420]`, rst
`[600,900]`, latch data `[350,480]`, enable branch `[450,700]`, latch loop
`[280,400]`. Environment: rst high to 2000, req rises 3000 and falls 4500,
ack rises 4300 and falls 6000 (one-tick X windows), data valid on
`[2500, 7000)`. -/

def P0 : Par :=
  { W := 2000, W1 := 2001, Ra := 3000, Ra1 := 3001, Fa := 4500, Fa1 := 4501,
    Rb := 4300, Rb1 := 4301, Fb := 6000, Fb1 := 6001, Td := 2500, Tn := 7000,
    Alo := 400, Ahi := 520, Blo := 380, Bhi := 500, Qlo := 300, Qhi := 420,
    Rlo := 600, Rhi := 900, Dlo := 350, Dhi := 480, Elo := 450, Ehi := 700,
    Flo := 280, Fhi := 400 }

theorem wf_of (P : Par)
    (h : (0 ≤ P.Alo ∧ P.Alo ≤ P.Ahi) ∧ (0 ≤ P.Blo ∧ P.Blo ≤ P.Bhi) ∧ (1 ≤ P.Qlo ∧ P.Qlo ≤ P.Qhi) ∧
      (0 ≤ P.Rlo ∧ P.Rlo ≤ P.Rhi) ∧ (0 ≤ P.Dlo ∧ P.Dlo ≤ P.Dhi) ∧ (0 ≤ P.Elo ∧ P.Elo ≤ P.Ehi) ∧
      (1 ≤ P.Flo ∧ P.Flo ≤ P.Fhi) ∧ (0 ≤ P.W ∧ P.W ≤ P.W1) ∧
      (P.Ra ≤ P.Ra1 ∧ P.Ra1 ≤ P.Fa ∧ P.Fa ≤ P.Fa1) ∧ (P.Rb ≤ P.Rb1 ∧ P.Rb1 ≤ P.Fb ∧ P.Fb ≤ P.Fb1) ∧
      P.W1 + P.Rhi < P.Ra + P.Alo ∧ P.W1 + P.Rhi < P.Rb + P.Blo ∧
      max (P.Fa1 + P.Ahi) (P.Rb1 + P.Bhi) ≤ P.Fb + P.Blo) : Wf P :=
  ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1, h.2.2.2.2.2.1, h.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.1,
    h.2.2.2.2.2.2.2.2.2.2.2.1, h.2.2.2.2.2.2.2.2.2.2.2.2⟩

theorem conj_iff (P : Par) : Conj P ↔
    (P.Rhi + P.Qhi ≤ P.W + P.Rlo ∧ P.Ra1 + P.Ahi + P.Qhi ≤ min (P.Fa + P.Alo) (P.Rb + P.Blo) ∧
     max (P.Fa1 + P.Ahi) (P.Rb1 + P.Bhi) + P.Qhi ≤ P.Fb + P.Blo ∧
     P.Ra1 + P.Ahi + P.Ehi + P.Fhi ≤ max (P.Fa + P.Alo) (P.Rb + P.Blo) + P.Elo ∧
     P.Td + P.Dhi + P.Fhi ≤ max (P.Fa + P.Alo) (P.Rb + P.Blo) + P.Elo ∧
     max (P.Fa1 + P.Ahi) (P.Rb1 + P.Bhi) + P.Ehi ≤ P.Tn + P.Dlo) :=
  ⟨fun H => ⟨H.1, H.2, H.3, H.4, H.5, H.6⟩, fun h => ⟨h.1, h.2.1, h.2.2.1, h.2.2.2.1, h.2.2.2.2.1,
    h.2.2.2.2.2⟩⟩

theorem P0_wf : Wf P0 := wf_of P0 (by decide)
theorem P0_split : Split P0 := by unfold Split; decide
theorem P0_conj : Conj P0 := (conj_iff P0).2 (by decide)

/-- **Non-vacuity.** At `P0` every hypothesis holds, the conjunction holds,
a behaviour exists (simulated controller and latch, every read map at its
slowest), and it meets the spec; so does every other behaviour. -/
theorem witness (v : Bool) :
    Wf P0 ∧ Split P0 ∧ Conj P0 ∧ SafeLink P0 v ∧
    ∃ pa pb pq pr pd pe pf r a b d c q, Beh P0 v pa pb pq pr pd pe pf r a b d c q ∧
      Spec P0 v pd pe c q := by
  refine ⟨P0_wf, P0_split, P0_conj, (exact P0_wf P0_split).2 P0_conj, ?_⟩
  obtain ⟨c, hc, -⟩ : ∃ c, CtlEq (Rd.const P0.Ahi) (Rd.const P0.Bhi) (Rd.const P0.Qhi)
      (Rd.const P0.Rhi) (win 0 P0.W) (win P0.Ra1 P0.Fa) (win P0.Rb P0.Fb) c ∧
      ∀ t, t < 0 → c t = .f :=
    ⟨_, ctlRun_ctl _ _ _ _ _ _ .f P0.Qhi (by decide), fun t ht => ctlRun_neg t ht⟩
  have hbox : Box P0 (Rd.const P0.Ahi) (Rd.const P0.Bhi) (Rd.const P0.Qhi) (Rd.const P0.Rhi)
      (Rd.const P0.Dhi) (Rd.const P0.Ehi) (Rd.const P0.Fhi) := by
    refine ⟨⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩, ⟨?_, ?_⟩⟩ <;> decide
  have hE := env_win P0_wf (la := P0.Ra1) (ha := P0.Fa) (lb := P0.Rb) (hb := P0.Fb)
    (by decide) (by decide) (by decide) (by decide)
  obtain ⟨q, Bh, -⟩ := mkBeh' v P0_wf hbox hE hc
  exact ⟨_, _, _, _, _, _, _, _, _, _, _, _, _, Bh, sufficient P0_wf P0_conj Bh⟩

/-- One parameter set per conjunct: that conjunct violated by EXACTLY one
tick (`lhs = rhs + 1`), every other conjunct and the whole scope met. -/
def Pv : Fin 6 → Par
  | 0 => { P0 with W := 719, W1 := 720 }          -- rst 1 tick short
  | 1 => { P0 with Rb := 3560, Rb1 := 3561 }      -- ack read 1 tick inside the rise race
  | 2 => { P0 with Fb := 5060, Fb1 := 5061 }      -- ack fall read 1 tick inside the fall race
  | 3 => { P0 with Ehi := 1430 }                  -- enable branch 1 tick too slow
  | 4 => { P0 with Td := 4471 }                   -- data 1 tick late
  | 5 => { P0 with Tn := 5370 }                   -- next datum 1 tick early

theorem Pv_wf (i : Fin 6) : Wf (Pv i) := wf_of _ (by revert i; decide)
theorem Pv_split (i : Fin 6) : Split (Pv i) := by unfold Split; revert i; decide

theorem Pv_one_tick :
    (let P := Pv 0; P.W + P.Rlo + 1 = P.Rhi + P.Qhi ∧ P.U1 + P.Qhi ≤ P.Rel ∧
      P.V1 + P.Qhi ≤ P.Fb + P.Blo ∧ P.U1 + P.Ehi + P.Fhi ≤ P.V0 + P.Elo ∧
      P.Td + P.Dhi + P.Fhi ≤ P.V0 + P.Elo ∧ P.V1 + P.Ehi ≤ P.Tn + P.Dlo) ∧
    (let P := Pv 1; P.Rhi + P.Qhi ≤ P.W + P.Rlo ∧ P.Rel + 1 = P.U1 + P.Qhi ∧
      P.V1 + P.Qhi ≤ P.Fb + P.Blo ∧ P.U1 + P.Ehi + P.Fhi ≤ P.V0 + P.Elo ∧
      P.Td + P.Dhi + P.Fhi ≤ P.V0 + P.Elo ∧ P.V1 + P.Ehi ≤ P.Tn + P.Dlo) ∧
    (let P := Pv 2; P.Rhi + P.Qhi ≤ P.W + P.Rlo ∧ P.U1 + P.Qhi ≤ P.Rel ∧
      P.Fb + P.Blo + 1 = P.V1 + P.Qhi ∧ P.U1 + P.Ehi + P.Fhi ≤ P.V0 + P.Elo ∧
      P.Td + P.Dhi + P.Fhi ≤ P.V0 + P.Elo ∧ P.V1 + P.Ehi ≤ P.Tn + P.Dlo) ∧
    (let P := Pv 3; P.Rhi + P.Qhi ≤ P.W + P.Rlo ∧ P.U1 + P.Qhi ≤ P.Rel ∧
      P.V1 + P.Qhi ≤ P.Fb + P.Blo ∧ P.V0 + P.Elo + 1 = P.U1 + P.Ehi + P.Fhi ∧
      P.Td + P.Dhi + P.Fhi ≤ P.V0 + P.Elo ∧ P.V1 + P.Ehi ≤ P.Tn + P.Dlo) ∧
    (let P := Pv 4; P.Rhi + P.Qhi ≤ P.W + P.Rlo ∧ P.U1 + P.Qhi ≤ P.Rel ∧
      P.V1 + P.Qhi ≤ P.Fb + P.Blo ∧ P.U1 + P.Ehi + P.Fhi ≤ P.V0 + P.Elo ∧
      P.V0 + P.Elo + 1 = P.Td + P.Dhi + P.Fhi ∧ P.V1 + P.Ehi ≤ P.Tn + P.Dlo) ∧
    (let P := Pv 5; P.Rhi + P.Qhi ≤ P.W + P.Rlo ∧ P.U1 + P.Qhi ≤ P.Rel ∧
      P.V1 + P.Qhi ≤ P.Fb + P.Blo ∧ P.U1 + P.Ehi + P.Fhi ≤ P.V0 + P.Elo ∧
      P.Td + P.Dhi + P.Fhi ≤ P.V0 + P.Elo ∧ P.Tn + P.Dlo + 1 = P.V1 + P.Ehi) := by decide

/-- **Each 1-tick violation breaks the stage**: for every `i`, some behaviour
in the box (the run built in `need_*`) fails the spec. -/
theorem Pv_breaks (v : Bool) (i : Fin 6) : ¬ SafeLink (Pv i) v := by
  rw [exact (Pv_wf i) (Pv_split i), conj_iff]
  revert i; decide

/-! ## 7. In C's port interface (`Contracts.PortUpTo`, one token)

Observation points as in `ContractsLink` (every channel at its CONSUMER's
pins). The stage owns `req_out` and `data_out` up to the receiver's pins; the
receiver owns `ack_out` up to this stage's I1 pin. -/

section port
open Formal.Net.Handshake (Chan)
open Formal.Cells.Contracts (PortUpTo TokN)

/-- **H_WIRE_READ** (a window wire from a Kleene driver `x` to a binary pin
`y`, Nat ps at the pin): whenever the driver is DEFINITE `w` over the whole
window `[t - hi, t - lo]`, the pin shows `w`. Nothing is said otherwise (the
pin may glitch while the driver is in a window). -/
def WireRead (lo hi : Int) (x : Int → K3) (y : Nat → Bool) : Prop :=
  ∀ (t : Nat) (w : Bool), (∀ s : Int, (t : Int) - hi ≤ s → s ≤ (t : Int) - lo → x s = kb w) → y t = w

/-- **The receiver's request pin is DERIVED to be definite** outside the
node's windows (shifted by the request wire): low on `[Rhi + rhi, U0 + rlo)`,
high on `[U1 + rhi, V0 + rlo)`, low from `V1 + rhi`. Whether it is CLEAN
inside the windows is not derivable for a window wire (`WinFifo`); that is
the named hypothesis `H_ROUT` below. -/
theorem rout_definite {P : Par} {v : Bool} {pd pe : Rd} {c q : Int → K3}
    (Sp : Spec P v pd pe c q) {rlo rhi : Int} {rout : Nat → Bool}
    (H_RWIRE : WireRead rlo rhi c rout) :
    (∀ t : Nat, P.Rhi + rhi ≤ t → (t : Int) < P.U0 + rlo → rout t = false) ∧
    (∀ t : Nat, P.U1 + rhi ≤ t → (t : Int) < P.V0 + rlo → rout t = true) ∧
    (∀ t : Nat, P.V1 + rhi ≤ t → rout t = false) :=
  ⟨fun t h1 h2 => H_RWIRE t false fun s a b => Sp.rst s (by omega) (by omega),
   fun t h1 h2 => H_RWIRE t true fun s a b => Sp.hi s (by omega) (by omega),
   fun t h1 => H_RWIRE t false fun s a b => Sp.lo s (by omega)⟩

/-- **The output channel as C's one-token port.** From the stage spec, the
data wire to the receiver's D pin (`H_XWIRE`), and the named hypotheses
`H_ROUT` (the request pin is a clean wire, edges `ρ`), `H_ACK` (the
receiver's acknowledge at I1 is clean, edges `α`), `H_ORDER` (one token in
`[0, N]`, interleaved `ρ0 < α0 < ρ1 < α1`) and `H_X_LEAD` (the request
reaches the receiver's pin no earlier than the data: bd_link.v's
"req_out LEADS data_out", rule E/I at a link output): the output channel is
`PortUpTo … N` carrying the token's value. -/
theorem out_port {P : Par} {v : Bool} {pd pe : Rd} {c q : Int → K3}
    (Sp : Spec P v pd pe c q) {N : Nat} {rout ackB xpin : Nat → Bool} {ρ α : Nat → Nat}
    {xlo xhi : Int} (H_XWIRE : WireRead xlo xhi q xpin)
    (H_ROUT : TokN 0 N rout ρ (fun _ => true)) (H_ACK : TokN 0 N ackB α (fun _ => true))
    (H_ORDER : 0 < ρ 0 ∧ ρ 0 < α 0 ∧ α 0 < ρ 1 ∧ ρ 1 < α 1 ∧ ∀ j, 2 ≤ j → N < ρ j ∧ N < α j)
    (H_X_LEAD : max (P.U1 + pe.hi) (P.Td + pd.hi) + xhi ≤ (ρ 0 : Int)) :
    PortUpTo ⟨rout, ackB, fun t => if xpin t then 1 else 0⟩ ρ α (fun _ => if v then 1 else 0) N := by
  obtain ⟨o1, o2, o3, o4, o5⟩ := H_ORDER
  refine ⟨⟨H_ROUT, o1, fun j hj => ?_⟩, fun k t ht h1 h2 => ?_, ⟨H_ACK, fun j hj => ?_⟩⟩
  · rcases j with _ | j
    · exact o3
    · have := (o5 (j + 1 + 1) (by omega)).1; omega
  · rcases k with _ | k
    · show (if xpin t then 1 else 0) = (if v then 1 else 0)
      have e0 : ρ (2 * 0) = ρ 0 := rfl
      rw [e0] at h1
      rw [H_XWIRE t v fun s a b => Sp.out s (by omega) (by omega)]
    · have := (o5 (2 * (k + 1)) (by omega)).1; omega
  · rcases j with _ | _ | j
    · exact o2
    · exact o4
    · have := (o5 (j + 1 + 1) (by omega)).2; omega

end port

end Formal.Cells.LinkExact
