import Formal.Cells.Prelim

/-!
# Lib1: every LUT of `bd_ctl.v`, `bd_merge.v`, `bd_mux.v`, binary and Kleene

Real INIT constants and pin maps, copied verbatim from `cells/rtl/` (the pin
each signal sits on is in the doc comment of each definition), evaluated with
Prelim's `lutB`/`o5B`/`o6B` (binary) and `lutK`/`o5K`/`o6K` (Kleene, hypothesis
**H_KLEENE_LUT** of `Prelim`; `MuxTree.lean` reduces it to one per-mux
hypothesis). The Boolean equations in the cell headers are PROVED equal to the
INITs; nothing below evaluates a hand-written equation of a cell.

LUT inventory of the three files (parameter values actually used: `bd_dr2bd`
`HOLD` is 1 in `cells/verify/soak_top.v` and `cells/tb/tb_conv.v`, 0 in
`tb_conv.v`; `bdc/` never instantiates the converters. `bd_mux`'s `FASTFALL`
and every `DELAY`/`W` parameter only reach `bd_delay`/`bd_datamux` in
`bd_latch.v`, not a LUT of these files):

| cell | instance | primitive | INIT |
|---|---|---|---|
| bd_fork / bd_join | (none: `bd_ctree`, proved in `CElemFn`/`CTree`) | | |
| bd_steer  | `u`    | LUT6_2 | 8888_8888_2222_2222 |
| bd_steer  | `uack` | LUT2   | E |
| bd_bd2dr  | `u`    | LUT6_2 | 8888_8888_2222_2222 |
| bd_dr2bd HOLD=1 | `ghold.u` | LUT6_2, O5 fed back to I2 | EEEE_EEEE_B2B2_B2B2 |
| bd_dr2bd HOLD=0 | `gbare.uor` | LUT2 | E |
| bd_merge  | `uor`, `usel` | LUT2 | E |
| bd_merge  | `uxa`, `uya` | bd_c2 (LUT6, O fed back to I2) | 00E8_00E8_00E8_00E8 |
| bd_mux    | `uj0`  | LUT6, O fed back to I3 | 0000_AE08_0000_AE08 |
| bd_mux    | `uj1`  | LUT6, O fed back to I3 | 0000_EA80_0000_EA80 |
| bd_mux    | `uor`  | LUT2 | E |
| bd_mux    | `uxa`, `uya` | bd_c2 | as above |

Model of each feedback cell: the LUT's combinational function with the
feedback pin read as an independent input `q` is the loop's next-state
function; a stable state needs the named hypothesis `H_FB_SETTLED` (see
`Settled`). Timing of the feedback wire is not modelled here.

Sections: 0 helpers; 1 steer/bd2dr; 2 dr2bd; 3 merge; 4 mux; 5 single-X glitch
freedom of every INIT; 6 multi-pin (function) hazards that single-X does not
cover, each with the protocol fact that excludes it.
-/

namespace Formal.Cells.LibCtlMergeMux
open Formal.Cells

set_option linter.constructorNameAsVariable false

/-! ## 0. Helpers (local; Prelim has none of these) -/

instance K3.decForall {P : K3 → Prop} [DecidablePred P] : Decidable (∀ k, P k) :=
  if h : P .f ∧ P .t ∧ P .x then
    isTrue (fun k => by cases k <;> simp_all)
  else
    isFalse (fun H => h ⟨H _, H _, H _⟩)

/-- Binary C-element: all inputs 1 → 1, all 0 → 0, otherwise hold `q`. -/
def cSpec (ins : List Bool) (q : Bool) : Bool :=
  if ins.all id then true else if ins.all (! ·) then false else q

/-- Strong-Kleene AND / OR. -/
def kand : K3 → K3 → K3
  | .f, _ => .f
  | _, .f => .f
  | .t, .t => .t
  | _, _ => .x
def kor : K3 → K3 → K3
  | .t, _ => .t
  | _, .t => .t
  | .f, .f => .f
  | _, _ => .x

/-- Kleene C-element (same closed form as `CElemFn.cK`). -/
def cK (ins : List K3) (q : K3) : K3 :=
  if ins.all (· == .t) then .t
  else if ins.all (· == .f) then .f
  else if q != .x && ins.contains q then q
  else .x

/-- **H_FB_SETTLED.** The feedback net has settled: the value on the feedback
pin equals what the LUT drives for the present inputs (the routed wire `O → I`
has delivered the last transition, nothing in flight). Testable on GLS by
comparing the feedback pin with O once every input has been stable longer than
the loop's slow-corner LUT + net delay. -/
structure Settled (next : Bool → Bool) (q : Bool) : Prop where
  H_FB_SETTLED : next q = q

/-! ## 1. `bd_steer` and `bd_bd2dr` (one shared INIT) -/

/-- `bd_steer.u` / `bd_bd2dr.u`, LUT6_2:
`I0=req I1=s(d) I2=0 I3=0 I4=0 I5=1`; steer: `O5=req0 O6=req1`;
bd2dr: `O5=f O6=t`. -/
def INIT_steer : Nat := 0x8888888822222222
/-- `bd_steer.uack`, `bd_dr2bd.gbare.uor`, `bd_merge.uor/usel`, `bd_mux.uor`: LUT2. -/
def INIT_or2 : Nat := 0xE

def steerPins (req s : Bool) : List Bool := [req, s, false, false, false, true]
def steerPinsK (req s : K3) : List K3 := [req, s, .f, .f, .f, .t]

def req0B (req s : Bool) : Bool := o5B INIT_steer (steerPins req s)
def req1B (req s : Bool) : Bool := o6B INIT_steer (steerPins req s)
def req0K (req s : K3) : K3 := o5K INIT_steer (steerPinsK req s)
def req1K (req s : K3) : K3 := o6K INIT_steer (steerPinsK req s)
def or2B (a b : Bool) : Bool := lutB INIT_or2 [a, b]
def or2K (a b : K3) : K3 := lutK INIT_or2 [a, b]

/-- Header: `req0 = req . ~s`. -/
theorem steer_req0 : ∀ req s : Bool, req0B req s = (req && !s) := by decide
/-- Header: `req1 = req . s`. -/
theorem steer_req1 : ∀ req s : Bool, req1B req s = (req && s) := by decide
/-- Header (bd_bd2dr, same pins): `t = req . d` on O6, `f = req . ~d` on O5. -/
theorem bd2dr_t : ∀ req d : Bool, req1B req d = (req && d) := by decide
theorem bd2dr_f : ∀ req d : Bool, req0B req d = (req && !d) := by decide
/-- Header: `ack = ack0 + ack1` (and every other `LUT2 E` is an OR). -/
theorem or2_spec : ∀ a b : Bool, or2B a b = (a || b) := by decide

/-- The tied pins I2..I4 are don't-cares on both outputs (binary). -/
theorem steer_tied_dontcare : ∀ req s u v w : Bool,
    o5B INIT_steer [req, s, u, v, w, true] = req0B req s ∧
    o6B INIT_steer [req, s, u, v, w, true] = req1B req s := by decide
/-- ... and Kleene: even X on I2..I4 reaches neither output. -/
theorem steer_tied_dontcare_K : ∀ req s u v w : K3,
    o5K INIT_steer [req, s, u, v, w, .t] = req0K req s ∧
    o6K INIT_steer [req, s, u, v, w, .t] = req1K req s := by decide
/-- The I5 tie is NOT a don't-care for O6: with I5 = 0, O6 would be the O5
function (`req . ~s`). The cell needs a solid VCC on I5 (which is what LUT6_2
dual-output mode requires anyway). -/
theorem steer_I5_low : ∀ req s : Bool,
    o6B INIT_steer [req, s, false, false, false, false] = (req && !s) := by decide
/-- Kleene: an X on the I5 tie gives X on O6 exactly when `req` is not `f`
(the two halves disagree); O5 never sees I5. -/
theorem steer_I5_x : ∀ req s : K3,
    o6K INIT_steer [req, s, .f, .f, .f, .x] = (if req = .f then .f else .x) := by decide

/-- Kleene closed form of both branches: strong-Kleene AND. -/
theorem steer_K_closed : ∀ req s : K3,
    req0K req s = kand req (K3.not s) ∧ req1K req s = kand req s := by decide

/-- Header: "outside that window req is already low and req.s is zero whatever
s does": with `req = 0` an X on `s` (s moving) leaves BOTH branches at 0. -/
theorem steer_idle_s_free : req0K .f .x = .f ∧ req1K .f .x = .f := by decide
/-- Header: "a constant cannot glitch a branch": with `s` definite, an X on
`req` (req in transit) leaves the UNSELECTED branch at a definite 0. -/
theorem steer_req_x_unselected : ∀ s : Bool,
    (if s then req0K .x (.ofBool s) else req1K .x (.ofBool s)) = .f := by decide
/-- The bundling contract is needed: `s` moving while `req = 1` puts X on BOTH
branches (each could fire). Hypothesis H_BUNDLED_S (s stable req↑..ack↓) of
the header excludes it. -/
theorem steer_s_x_while_req : req0K .t .x = .x ∧ req1K .t .x = .x := by decide
/-- Mutual exclusion of the branches, binary. -/
theorem steer_excl : ∀ req s : Bool, !(req0B req s && req1B req s) := by decide
/-- Mutual exclusion in Kleene: no input pattern drives both branches to a
definite 1 (with `s = X` both are X, never both `t`). -/
theorem steer_excl_K : ∀ req s : K3, ¬ (req0K req s = .t ∧ req1K req s = .t) := by decide

/-! ## 2. `bd_dr2bd` -/

/-- `bd_dr2bd.ghold.u` (HOLD=1), LUT6_2, `(* keep *)`:
`I0=t I1=f I2=d I3=0 I4=0 I5=1`, `O5=d` (fed back to I2), `O6=either`. -/
def INIT_dr : Nat := 0xEEEEEEEEB2B2B2B2

def drPins (t f d : Bool) : List Bool := [t, f, d, false, false, true]
def drPinsK (t f d : K3) : List K3 := [t, f, d, .f, .f, .t]
/-- next value of `d` (O5) with the feedback pin read as `d`. -/
def dNextB (t f d : Bool) : Bool := o5B INIT_dr (drPins t f d)
def eitherB (t f d : Bool) : Bool := o6B INIT_dr (drPins t f d)
def dNextK (t f d : K3) : K3 := o5K INIT_dr (drPinsK t f d)
def eitherK (t f d : K3) : K3 := o6K INIT_dr (drPinsK t f d)

/-- Header: `O6 = either = t + f`. -/
theorem dr_either : ∀ t f d : Bool, eitherB t f d = (t || f) := by decide
/-- Header: `O5 = d = majority(t, ~f, d)`. -/
theorem dr_d_majority : ∀ t f d : Bool,
    dNextB t f d = ((t && !f) || (t && d) || (!f && d)) := by decide
/-- Header: `d = C(t, ~f)`. Same function as `bd_c2n` with rst = 0
(`CElemFn.c2n_spec`; the low byte B2 is bd_c2n's). -/
theorem dr_d_celem : ∀ t f d : Bool, dNextB t f d = cSpec [t, !f] d := by decide
/-- Header's four codes: valid ONE sets, valid ZERO resets, SPACER holds, and
the illegal code `t = f = 1` also holds ("gives a hold if it ever did"). -/
theorem dr_codes : ∀ d : Bool,
    dNextB true false d = true ∧ dNextB false true d = false ∧
    dNextB false false d = d ∧ dNextB true true d = d := by decide
/-- Tied pins I3, I4 are don't-cares (binary and Kleene). -/
theorem dr_tied_dontcare : ∀ t f d u v : Bool,
    o5B INIT_dr [t, f, d, u, v, true] = dNextB t f d ∧
    o6B INIT_dr [t, f, d, u, v, true] = eitherB t f d := by decide
theorem dr_tied_dontcare_K : ∀ t f d u v : K3,
    o5K INIT_dr [t, f, d, u, v, .t] = dNextK t f d ∧
    o6K INIT_dr [t, f, d, u, v, .t] = eitherK t f d := by decide

/-- Fixed points: `d` is stable iff the code does not force `!d`. -/
theorem dr_fixed_iff : ∀ t f d : Bool,
    dNextB t f d = d ↔ ¬ (t = !d ∧ f = d) := by decide
/-- Under H_FB_SETTLED, a settled decoder on a valid code shows its bit. -/
theorem dr_settled_valid (b d : Bool)
    (h : Settled (fun d => dNextB b (!b) d) d) : d = b := by
  have hs := h.H_FB_SETTLED
  clear h; revert hs; revert b d; decide

/-- Kleene closed form of the decode (cf. `CElemFn.c2nK_closed`). -/
theorem dr_d_K_closed : ∀ t f d : K3, dNextK t f d = cK [t, K3.not f] d := by decide
/-- Kleene: `either` (O6) does not depend on the feedback pin at all, so an X
on `d` (power-up, or a metastable decode) never reaches the request path. -/
theorem dr_either_K : ∀ t f d : K3, eitherK t f d = kor t f := by decide
/-- Header: "with an X on the feedback pin ... on a valid code they always
agree, so d resolves on the first token": X on `d` gives a definite value iff
the code is valid (`t = ~f`, definite), and then it is `t`. -/
theorem dr_meta_resolve : ∀ t f : K3,
    dNextK t f .x ≠ .x ↔ (t = K3.not f ∧ t ≠ .x) := by decide
theorem dr_meta_resolves_to : ∀ b : Bool,
    dNextK (.ofBool b) (.ofBool (!b)) .x = .ofBool b := by decide
/-- Power-up X is held across a spacer (Kleene never resolves it in hold);
the header's argument that it is never READ rests on req rising only behind a
valid code, i.e. on the bundling of `req = delta(either)` against the decode
(hypothesis H_DR_REQ_AFTER_D of the header, not proved here). -/
theorem dr_x_held_on_spacer : dNextK .f .f .x = .x := by decide
/-- Header "THE SPACER EATS THE DATA" (HOLD=0): `d = t` is a wire, so on the
spacer `d = 0` whatever was decoded before; HOLD=1 keeps it. -/
def dBare (t _f _prev : Bool) : Bool := t
theorem dr_hold0_spacer_eats : ∀ prev : Bool,
    dBare false false prev = false ∧ dNextB false false prev = prev := by decide
/-- HOLD=0's request path is the same OR as HOLD=1's O6. -/
theorem dr_hold0_either : ∀ t f d : Bool, or2B t f = eitherB t f d := by decide

/-! ## 3. `bd_merge` -/

/-- `bd_c2` (`bd_ce.v`): `I0=a I1=b I2=q I3=rst I4=0 I5=0`. Verbatim copy of
`CElemFn.INIT_c2`. Merge: `uxa a=x_req b=z_ack q=x_ack`, `uya a=y_req b=z_ack`. -/
def INIT_c2 : Nat := 0x00E800E800E800E8
def c2B (a b q rst : Bool) : Bool := lutB INIT_c2 [a, b, q, rst, false, false]
def c2K (a b q rst : K3) : K3 := lutK INIT_c2 [a, b, q, rst, .f, .f]

theorem c2_spec : ∀ a b q rst : Bool, c2B a b q rst = (!rst && cSpec [a, b] q) := by decide

/-- `bd_merge.usel`: `sel = x_req + x_ack` (`LUT2 E`, I0=x_req I1=x_ack). -/
def selB (xr xa : Bool) : Bool := or2B xr xa
def selK (xr xa : K3) : K3 := or2K xr xa

/-- One x transaction of the merge, as the sequence of (x_req, z_ack, x_ack)
states the header describes: idle; x_req↑; z_ack↑ (after z_req); x_ack↑
(C fires); x_req↓; z_ack↓; x_ack↓ (C fires); idle. -/
def xTxn : List (Bool × Bool × Bool) :=
  [(false, false, false), (true, false, false), (true, true, false), (true, true, true),
   (false, true, true), (false, false, true), (false, false, false)]

/-- Each x_ack step in `xTxn` is a legal move of the real bd_c2 INIT, and every
state is one the C-element holds or moves to (rst = 0). -/
theorem merge_txn_celem :
    (xTxn.zip xTxn.tail).all (fun (s, s') =>
      s'.2.2 = s.2.2 || s'.2.2 = c2B s'.1 s'.2.1 s.2.2 false) = true := by decide
/-- Header: "high across exactly the x transaction": sel is 1 from x_req↑ until
x_ack↓ and 0 in idle. -/
theorem merge_sel_window :
    xTxn.map (fun (xr, _, xa) => selB xr xa) =
      [false, true, true, true, true, true, false] := by decide
/-- Header: "the select cannot be the request": x_req falls at state 4 while
x_ack (and z_ack) are still high. -/
theorem merge_req_as_sel_fails :
    xTxn.map (fun (xr, _, _) => xr) = [false, true, true, true, false, false, false] := by
  decide
/-- Kleene: the select does not glitch when x_req falls while x_ack = 1. -/
theorem merge_sel_xreq_fall_K : selK .x .t = .t := by decide
/-- Kleene: the end of the select window is x_ack's fall (an X there is a real
transition of sel). -/
theorem merge_sel_xack_fall_K : selK .f .x = .x := by decide
/-- Header: "C(0, z_ack) stays at zero" -- the idle input is never acknowledged. -/
theorem merge_idle_not_acked : ∀ za : Bool, c2B false za false false = false := by decide
/-- Kleene form: even an X on z_ack does not move the idle input's acknowledge. -/
theorem merge_idle_not_acked_K : c2K .f .x .f .f = .f := by decide
/-- Header: "The acknowledge cannot be an AND": with AND, x_ack falls as soon as
x_req falls while z_ack is still high; the C-element holds it. -/
theorem merge_ack_holds : c2B false true true false = true ∧ (false && true) = false := by
  decide
/-- Header's obligation: if y asserts while z_ack is still high (first
transaction not complete), `C(y_req, z_ack)` fires and acknowledges a token
the merge never carried. This is why the merge needs hypothesis
H_MERGE_SEQ (second request only after the first transaction completes). -/
theorem merge_early_y_spurious_ack : c2B true true false false = true := by decide

/-! ## 4. `bd_mux` -/

/-- `bd_mux.uj0`, LUT6 `(* keep *)`:
`I0=x_req I1=ctl_req I2=s I3=j0 I4=rst I5=0`, `O=j0` (fed back to I3). -/
def INIT_j0 : Nat := 0x0000AE090000AE08
/-- `bd_mux.uj1`, LUT6 `(* keep *)`:
`I0=y_req I1=ctl_req I2=s I3=j1 I4=rst I5=0`, `O=j1` (fed back to I3). -/
def INIT_j1 : Nat := 0x0000EA800000EA80

def j0B (x c s q rst : Bool) : Bool := lutB INIT_j0 [x, c, s, q, rst, false]
def j1B (y c s q rst : Bool) : Bool := lutB INIT_j1 [y, c, s, q, rst, false]
def j0K (x c s q rst : K3) : K3 := lutK INIT_j0 [x, c, s, q, rst, .f]
def j1K (y c s q rst : K3) : K3 := lutK INIT_j1 [y, c, s, q, rst, .f]

/-- Header: `j0 = C(x_req, ctl_req . ~s)`, cleared by rst. -/
theorem j0_spec : ∀ x c s q rst : Bool,
    j0B x c s q rst = (!rst && cSpec [x, c && !s] q) := by decide
/-- Header: `j1 = C(y_req, ctl_req . s)`, cleared by rst. -/
theorem j1_spec : ∀ y c s q rst : Bool,
    j1B y c s q rst = (!rst && cSpec [y, c && s] q) := by decide
/-- The tied I5 is a don't-care, binary and Kleene. -/
theorem j0_tied_dontcare : ∀ x c s q rst u : Bool,
    lutB INIT_j0 [x, c, s, q, rst, u] = j0B x c s q rst := by decide
theorem j1_tied_dontcare : ∀ y c s q rst u : Bool,
    lutB INIT_j1 [y, c, s, q, rst, u] = j1B y c s q rst := by decide
theorem j0_tied_dontcare_K : ∀ x c s q rst u : K3,
    lutK INIT_j0 [x, c, s, q, rst, u] = j0K x c s q rst := by decide
theorem j1_tied_dontcare_K : ∀ y c s q rst u : K3,
    lutK INIT_j1 [y, c, s, q, rst, u] = j1K y c s q rst := by decide
/-- The two joins are mirror images: swap `s`. -/
theorem j1_is_j0_mirror : ∀ y c s q rst : Bool, j1B y c s q rst = j0B y c (!s) q rst := by
  decide

/-- Kleene closed forms: C-element over the strong-Kleene decode, cleared by rst. -/
theorem j0K_closed : ∀ x c s q rst : K3,
    j0K x c s q rst = kand (K3.not rst) (cK [x, kand c (K3.not s)] q) := by decide
theorem j1K_closed : ∀ y c s q rst : K3,
    j1K y c s q rst = kand (K3.not rst) (cK [y, kand c s] q) := by decide

/-- Fixed points (rst = 0): `q` is stable iff the two C inputs are not both `!q`. -/
theorem j0_fixed_iff : ∀ x c s q : Bool,
    j0B x c s q false = q ↔ ¬ (x = !q ∧ (c && !s) = !q) := by decide
theorem j0_rst_forced : ∀ x c s q : Bool, j0B x c s q true = false := by decide
theorem j1_rst_forced : ∀ y c s q : Bool, j1B y c s q true = false := by decide
/-- Under H_FB_SETTLED a settled j0 with both C inputs high shows 1. -/
theorem j0_settled_fire (q : Bool) (h : Settled (fun q => j0B true true false q false) q) :
    q = true := by
  have hs := h.H_FB_SETTLED
  clear h; revert hs; revert q; decide

/-- Header: "j0 can only fire if the control said x": with `s = 1` a j0 at 0
stays at 0 whatever `x_req`, `ctl_req` do. -/
theorem j0_blocked_by_s : ∀ x c : Bool, j0B x c true false false = false := by decide
theorem j1_blocked_by_s : ∀ y c : Bool, j1B y c false false false = false := by decide
/-- Kleene: even X on `x_req` and `ctl_req` together cannot raise a j0 that
`s = 1` (definite) blocks. -/
theorem j0_blocked_by_s_K : j0K .x .x .t .f .f = .f := by decide
theorem j1_blocked_by_s_K : j1K .x .x .f .f .f = .f := by decide
/-- Kleene: `s` may move freely while ctl_req is low and j0 is at rest (0). -/
theorem j0_s_free_idle : ∀ x : K3, x ≠ .t → j0K x .f .x .f .f = .f := by decide
/-- Exactly when `s` may move with j0 high (rst = 0): the output stays
definite iff x_req is still high (then it stays 1) or ctl_req is already low
(then it is the C-element's own value: 1, or 0 when x_req is low too, the
legitimate fall). If x_req has fallen while ctl_req is high, an X on `s`
reaches j0 (s = 1 would let it fall early): `s` must be held until ctl_req
falls, which the control channel's contract (s held to ctl_ack↓ = z_ack↓) gives. -/
theorem j0_s_free_high : ∀ x c : Bool,
    j0K (.ofBool x) (.ofBool c) .x .t .f ≠ .x ↔ (x = true ∨ c = false) := by decide
theorem j0_s_free_high_xreq : ∀ c : Bool, j0K .t (.ofBool c) .x .t .f = .t := by decide
/-- X on the feedback pin (power-up, or a runt): resolved iff both C inputs
are definite and equal. -/
theorem j0_meta_resolve : ∀ x c s : K3,
    j0K x c s .x .f ≠ .x ↔ (x ≠ .x ∧ x = kand c (K3.not s)) := by decide
/-- A definite reset clears an X j0. -/
theorem j0_rst_clears_x : ∀ x c s : K3, j0K x c s .x .t = .f := by decide

/-! Acknowledge side: `uxa = bd_c2(a=j0, b=z_ack)`, `uya = bd_c2(a=j1, b=z_ack)`,
the same INIT as the merge's (`c2_spec` above). `ctl_ack = z_ack` is a wire. -/

/-- Mutual exclusion of the joins at rest: from j0 = j1 = 0 (rst = 0) at most
one can rise for any one definite `s`. -/
theorem mux_joins_excl : ∀ x y c s : Bool,
    !(j0B x c s false false && j1B y c s false false) := by decide
/-- Kleene version: with `s` definite, not both joins can be driven to `t`. -/
theorem mux_joins_excl_K : ∀ x y c : K3, ∀ s : Bool,
    ¬ (j0K x c (.ofBool s) .f .f = .t ∧ j1K y c (.ofBool s) .f .f = .t) := by decide

/-! ## 5. Single-X glitch freedom of every LUT (all pins, all binary vectors) -/

def allVecs : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allVecs n).map (false :: ·) ++ (allVecs n).map (true :: ·)

/-- `n`-pin form of `CElemFn.SingleX`: X on pin `i`, the rest definite, gives
exactly the join of the two endpoint binary values. -/
def SingleX (n init : Nat) : Prop :=
  ∀ v ∈ allVecs n, ∀ i, i < n →
    lutK init ((v.map K3.ofBool).set i .x)
      = K3.join (.ofBool (lutB init v)) (.ofBool (lutB init (v.set i (!v.getD i false))))

/-- O6 of the LUT6_2s, and the LUT6s: 6 pins. -/
theorem steerO6_singleX : SingleX 6 INIT_steer := by unfold SingleX; decide
theorem dr_O6_singleX    : SingleX 6 INIT_dr    := by unfold SingleX; decide
theorem j0_singleX       : SingleX 6 INIT_j0    := by unfold SingleX; decide
theorem j1_singleX       : SingleX 6 INIT_j1    := by unfold SingleX; decide
theorem c2_singleX       : SingleX 6 INIT_c2    := by unfold SingleX; decide
/-- O5 of the LUT6_2s: the lower LUT5 (`o5K` = `lutK (init % 2^32)` on 5 pins). -/
theorem steerO5_singleX : SingleX 5 (INIT_steer % 2 ^ 32) := by unfold SingleX; decide
theorem dr_O5_singleX    : SingleX 5 (INIT_dr % 2 ^ 32)    := by unfold SingleX; decide
/-- The LUT2 OR. -/
theorem or2_singleX : SingleX 2 INIT_or2 := by unfold SingleX; decide

/-- Glitch freedom from `SingleX`: equal endpoints ⇒ the transit value is that value. -/
theorem glitchFree_of_singleX {n init : Nat} (h : SingleX n init) {v : List Bool}
    (hv : v ∈ allVecs n) {i : Nat} (hi : i < n)
    (heq : lutB init (v.set i (!v.getD i false)) = lutB init v) :
    lutK init ((v.map K3.ofBool).set i .x) = .ofBool (lutB init v) := by
  rw [h v hv i hi, heq]; simp [K3.join]

/-! ## 6. Multi-pin changes (function hazards): where single-X is not enough

Under closure semantics (H_KLEENE_LUT) any two pins in transit together give X
whenever SOME intermediate vector differs, even if both endpoints agree. Each
case below is a cell whose output would be X; the protocol fact that excludes
it is named. -/

/-- dr2bd `either`: a direct ONE→ZERO code change (t↓ and f↑ together, no
spacer) can glitch `either` low although it is 1 at both ends. Excluded by the
dual-rail protocol (H_DR_SPACER: a spacer between any two valid codes). -/
theorem dr_either_hazard :
    eitherB true false false = true ∧ eitherB false true false = true ∧
    eitherK .x .x .f = .x := by decide
/-- dr2bd `d`: ONE→ZERO directly makes `d` X even with d = 0 held before
(endpoints: set vs reset). -/
theorem dr_d_direct_change_x : dNextK .x .x .f = .x := by decide
/-- bd_mux j0: x_req↑ together with ctl_req↓ (with s = 0, j0 = 0): both endpoints
hold 0, the middle (1, 1) fires. Excluded because ctl_req falls only after
ctl_ack = z_ack, which needs j0 or j1 to have fired; with s = 0 j1 cannot
(`j1_blocked_by_s`), so j0 already fired. -/
theorem j0_hazard_x_up_c_down :
    j0B false true false false false = false ∧ j0B true false false false false = false ∧
    j0K .x .x .f .f .f = .x := by decide
/-- With `s = 1` the same double change is harmless for j0 (decode pinned to 0). -/
theorem j0_no_hazard_when_deselected : j0K .x .x .t .f .f = .f := by decide
/-- bd_steer: `req` and `s` moving together put X on both branches (H_BUNDLED_S). -/
theorem steer_req_s_together : req0K .x .x = .x ∧ req1K .x .x = .x := by decide
/-- bd_merge sel: x_req↓ together with x_ack↑ (C firing as the request drops,
impossible since x_ack↑ needs x_req = 1 at the C input) would make sel X. -/
theorem merge_sel_hazard : selK .x .x = .x := by decide

end Formal.Cells.LibCtlMergeMux
