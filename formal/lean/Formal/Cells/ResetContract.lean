import Formal.Cells.Prelim
import Formal.Cells.CElemTiming
import Formal.Cells.CTreeTimed
import Formal.Cells.TernarySound
import Formal.Cells.TernaryPhases

/-!
# Probe Rst (shard B, gcd_hw capstone): the design-level reset contract

Notes: `formal/notes/B-reset-contract.md`.

## What is proved

1. **Per cell type, from the real INITs** (`cells/rtl/bd_ce.v`, `bd_arb.v`,
   `bd_mux.v`, `bd_ctl.v`, `bd_latch.v`, `bd_end.v`, `cells/hw/gcd_rig.v`):
   every reset-carrying LUT that gcd_hw instantiates (`bd_c2`, `bd_c2n`,
   `bd_c2n_set`, `bd_c3`, `bd_c4`, `bd_mux.uj0/uj1`, `bd_arbiter.ustate` O6)
   is FORCED to its reset value by `rst = 1` whatever its other pins carry,
   binary (`*_rstB`, all Boolean pin values) and Kleene (`*_rstK`, every pin
   `f`/`t`/`x`, so in particular from all-X power-up). The post-release hold
   facts (`*_holdK`) and the Kleene GUARD facts for the readers of
   never-reset data (`steer_guardK`, `uj0_guardK`, `uj1_guardK`,
   `rig_cmp_guardK`), and the latch facts (`latch_stays_x`,
   `latch_write`, `latch2_write_*`) are proved the same way.
2. **Generic network theorem** (`ResetSpec`, `reset_iter`, `reset_ternary`,
   `reset_binary`), on 7f's LUT networks (`TernarySound.Circ`, GMW runs with
   per-pin wire delays, bounds `Bounded D W`): if every control node is either
   forced by `rst` (rank 0) or a LUT whose Kleene value, with its control pins
   at their reset values and EVERY other pin `x`, is already its reset value
   (rank = 1 + max rank of its control pins), then (a) Kleene simulation from
   all-X with `rst = t` reaches the reset value on every control node by step
   `rank + 1`, and (b) EVERY bounded binary run, from ANY power-up state, whose
   `rst` source is 1 on `(0, E]`, shows the reset value on every control node
   of rank `< m` on `[(m+1)(D+W+1), E]`. The rst fanout skew is the wire bound
   `W` of the rst pins. This is the reset contract's state part.
3. **Concrete instance** (`rigNet`, 35 nodes, real INITs): the rig's
   environment ring (`uenv0` `bd_c2n`, `uenv1` `bd_c2n_set`, the `ufork`
   `bd_c3`) closed through two link stages (`bd_c2n` + `bd_latch` + DACK
   FASTRISE + rdly) and a `bd_steer` whose select is a link's latch output,
   plus a `bd_src` feeding a link, a `bd_mux` (uj0/uj1 with the select on a
   latch output, uor, uxa/uya), a gated delay stage, a `bd_arbiter` (ustate
   O6/O5, ugrant, ua1/ua2) and a `bd_c4`. `rig_spec` (checked by `decide`)
   gives `rig_reset_binary`; `rig_frontier` computes the post-release
   excitation: exactly the two link controllers fed by a token (env_c, the
   source) move first; every other control node is a fixed point, including
   the steer and mux joins whose select is still X.
4. **Release, timed** (window channels of 5b/5f): `c2n_reset`,
   `c2n_set_reset` (the non-frontier cells hold through release),
   `c2n_frontier` (a link controller with the token at its request pin fires
   exactly once, within its loop bound of its OWN rst pin release, from any
   power-up value), and the generic `first_change`: with min-delay potentials,
   no node leaves its reset value before its potential `P n`; so if every reset
   pin has released before the earliest event from the frontier can reach it
   (`H_RST_SKEW`, an EndpointOK race listed in the notes), the design leaves
   reset in the simultaneous-release state of item 3.

Core Lean only.
-/

namespace Formal.Cells.ResetContract
open Formal.Cells Formal.Cells.TernarySound

/-! ## 0. Real INITs (verbatim from cells/rtl and cells/hw/gcd_rig.v) -/

/-- `bd_c2`: pins `[a, b, q, rst, 0, 0]`. -/
def I_c2 : Nat := 0x00E800E800E800E8
/-- `bd_c2n`: pins `[a, b, q, rst, 0, 0]`, C(a, ~b). -/
def I_c2n : Nat := 0x00B200B200B200B2
/-- `bd_c2n_set` (gcd_rig `uenv1`): pins as `bd_c2n`, reset value 1. -/
def I_c2n_set : Nat := 0xFFB2FFB2FFB2FFB2
/-- `bd_c3`: pins `[a, b, c, q, rst, 0]`. -/
def I_c3 : Nat := 0x0000FE800000FE80
/-- `bd_c4`: pins `[a, b, c, d, q, rst]`. -/
def I_c4 : Nat := 0x00000000FFFE8000
/-- `bd_mux.uj0`: pins `[x_req, ctl_req, s, j0, rst, 0]`. -/
def I_uj0 : Nat := 0x0000AE080000AE08
/-- `bd_mux.uj1`: pins `[y_req, ctl_req, s, j1, rst, 0]`. -/
def I_uj1 : Nat := 0x0000EA800000EA80
/-- `bd_arbiter.ustate` LUT6_2: pins `[r1, r2, q, rst, A0, 1]`; O6 = q, O5 = R0. -/
def I_arb : Nat := 0xFFF0FFB2ACACACAC
/-- `bd_arbiter.ugrant` LUT6_2: pins `[r1, r2, q, 0, 0, 1]`; O5 = g1, O6 = g2. -/
def I_grant : Nat := 0x0C0C0C0CA0A0A0A0
/-- `bd_steer.u` LUT6_2: pins `[req, s, 0, 0, 0, 1]`; O5 = req0, O6 = req1. -/
def I_steer : Nat := 0x8888888822222222
/-- `bd_latch` odd bit LUT6: pins `[d, en, q, 0, 0, 0]`. -/
def I_latch1 : Nat := 0xB8B8B8B8B8B8B8B8
/-- `bd_latch` pair LUT6_2: pins `[d0, en, q0, d1, q1, 1]`; O5 = q0, O6 = q1. -/
def I_latch2 : Nat := 0xFF33CC00B8B8B8B8
/-- `bd_delay` element / `uor` buffer LUT1. -/
def I_buf : Nat := 2
/-- `bd_src.u` LUT1 (req = ~ack). -/
def I_src : Nat := 1
/-- LUT2 OR (`bd_steer.uack`, FASTRISE side stage, `bd_mux.uor` is a LUT2 E). -/
def I_or2 : Nat := 0xE
/-- LUT2 AND (`bd_delay_gated` side stage; gcd_rig `uerr_d`, `uabsn_d`). -/
def I_and2 : Nat := 8
/-- gcd_rig `uok_d`: `~mism & res_req`, pins `[mism, res_req]`. -/
def I_ok : Nat := 4
/-- gcd_rig `ucmpb_d`: pins `[cmp_in[31], cmp_z, cmp_req]`. -/
def I_cmpb : Nat := 0x90

theorem I_c2_same : I_c2 = CElemTiming.INIT_c2 := rfl
theorem I_c2n_same : I_c2n = CElemTiming.INIT_c2n := rfl
theorem I_c3_same : I_c3 = CTree.INIT_C3 := rfl
theorem I_c4_same : I_c4 = CTree.INIT_C4 := rfl

/-! ## 1. Per-cell facts

`forced`: a Kleene value computed with some pins `x` is inherited by every
vector below it in the information order (7f's `lutK_mono`). One `decide` on
the all-`x` vector then gives the statement for every K3 pin value. -/

theorem lx {a : K3} : le a .x := Or.inr rfl
theorem lr {a : K3} : le a a := Or.inl rfl

theorem forced {init : Nat} {zs zs' : List K3} {v : Bool} (h : Pw le zs zs')
    (h' : lutK init zs' = K3.ofBool v) : lutK init zs = K3.ofBool v := by
  have hm := lutK_mono init h
  rw [h'] at hm
  rcases hm with e | e
  · exact e
  · cases v <;> simp [K3.ofBool] at e

theorem pw2 {a b a' b' : K3} (h1 : le a a') (h2 : le b b') : Pw le [a, b] [a', b'] :=
  .cons h1 (.cons h2 .nil)
theorem pw3 {a b c a' b' c' : K3} (h1 : le a a') (h2 : le b b') (h3 : le c c') :
    Pw le [a, b, c] [a', b', c'] := .cons h1 (.cons h2 (.cons h3 .nil))
theorem pw5 {a b c d e a' b' c' d' e' : K3} (h1 : le a a') (h2 : le b b') (h3 : le c c')
    (h4 : le d d') (h5 : le e e') : Pw le [a, b, c, d, e] [a', b', c', d', e'] :=
  .cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 .nil))))
theorem pw6 {a b c d e f a' b' c' d' e' f' : K3} (h1 : le a a') (h2 : le b b') (h3 : le c c')
    (h4 : le d d') (h5 : le e e') (h6 : le f f') :
    Pw le [a, b, c, d, e, f] [a', b', c', d', e', f'] :=
  .cons h1 (.cons h2 (.cons h3 (.cons h4 (.cons h5 (.cons h6 .nil)))))

/-! ### 1a. Reset forcing: `rst = 1` gives the reset value whatever else -/

theorem c2_rstB : ∀ a b q : Bool, lutB I_c2 [a, b, q, true, false, false] = false := by decide
theorem c2n_rstB : ∀ a b q : Bool, lutB I_c2n [a, b, q, true, false, false] = false := by decide
theorem c2n_set_rstB : ∀ a b q : Bool, lutB I_c2n_set [a, b, q, true, false, false] = true := by
  decide
theorem c3_rstB : ∀ a b c q : Bool, lutB I_c3 [a, b, c, q, true, false] = false := by decide
theorem c4_rstB : ∀ a b c d q : Bool, lutB I_c4 [a, b, c, d, q, true] = false := by decide
theorem uj0_rstB : ∀ x c s j : Bool, lutB I_uj0 [x, c, s, j, true, false] = false := by decide
theorem uj1_rstB : ∀ y c s j : Bool, lutB I_uj1 [y, c, s, j, true, false] = false := by decide
/-- The arbiter's state node comes up at 1 (q = rst + C(r1, ~r2), held by A0). -/
theorem arb_rstB : ∀ r1 r2 q a0 : Bool, lutB I_arb [r1, r2, q, true, a0, true] = true := by
  decide

theorem c2_rstK (a b q : K3) : lutK I_c2 [a, b, q, .t, .f, .f] = .f :=
  forced (v := false) (pw6 lx lx lx lr lr lr) (by decide)
theorem c2n_rstK (a b q : K3) : lutK I_c2n [a, b, q, .t, .f, .f] = .f :=
  forced (v := false) (pw6 lx lx lx lr lr lr) (by decide)
theorem c2n_set_rstK (a b q : K3) : lutK I_c2n_set [a, b, q, .t, .f, .f] = .t :=
  forced (v := true) (pw6 lx lx lx lr lr lr) (by decide)
theorem c3_rstK (a b c q : K3) : lutK I_c3 [a, b, c, q, .t, .f] = .f :=
  forced (v := false) (pw6 lx lx lx lx lr lr) (by decide)
theorem c4_rstK (a b c d q : K3) : lutK I_c4 [a, b, c, d, q, .t] = .f :=
  forced (v := false) (pw6 lx lx lx lx lx lr) (by decide)
theorem uj0_rstK (x c s j : K3) : lutK I_uj0 [x, c, s, j, .t, .f] = .f :=
  forced (v := false) (pw6 lx lx lx lx lr lr) (by decide)
theorem uj1_rstK (y c s j : K3) : lutK I_uj1 [y, c, s, j, .t, .f] = .f :=
  forced (v := false) (pw6 lx lx lx lx lr lr) (by decide)
theorem arb_rstK (r1 r2 q a0 : K3) : lutK I_arb [r1, r2, q, .t, a0, .t] = .t :=
  forced (v := true) (pw6 lx lx lx lr lx lr) (by decide)

/-! ### 1b. Hold through release (rst = 0, inputs at their reset values)

The second argument of each is the pin that may still be `x`. -/

theorem c2_holdK (b : K3) : lutK I_c2 [.f, b, .f, .f, .f, .f] = .f :=
  forced (v := false) (pw6 lr lx lr lr lr lr) (by decide)
theorem c2_holdK' (a : K3) : lutK I_c2 [a, .f, .f, .f, .f, .f] = .f :=
  forced (v := false) (pw6 lx lr lr lr lr lr) (by decide)
/-- `bd_c2n` empty, request low: stays empty whatever `c_next` does. -/
theorem c2n_holdK (b : K3) : lutK I_c2n [.f, b, .f, .f, .f, .f] = .f :=
  forced (v := false) (pw6 lr lx lr lr lr lr) (by decide)
/-- `bd_c2n` empty, next stage full: stays empty whatever the request does. -/
theorem c2n_holdK' (a : K3) : lutK I_c2n [a, .t, .f, .f, .f, .f] = .f :=
  forced (v := false) (pw6 lx lr lr lr lr lr) (by decide)
/-- `bd_c2n` with the token at its request pin and the next stage empty FIRES
on release, whatever its feedback pin carries (the frontier). -/
theorem c2n_firesK (q : K3) : lutK I_c2n [.t, .f, q, .f, .f, .f] = .t :=
  forced (v := true) (pw6 lr lr lx lr lr lr) (by decide)
/-- `uenv1` holds its token through release while `env_c0 = 0` (whatever
`in_ack` does). -/
theorem c2n_set_holdK (a : K3) : lutK I_c2n_set [a, .f, .t, .f, .f, .f] = .t :=
  forced (v := true) (pw6 lx lr lr lr lr lr) (by decide)
theorem c2n_set_holdK' (b : K3) : lutK I_c2n_set [.t, b, .t, .f, .f, .f] = .t :=
  forced (v := true) (pw6 lr lx lr lr lr lr) (by decide)
theorem c3_holdK (b c : K3) : lutK I_c3 [.f, b, c, .f, .f, .f] = .f :=
  forced (v := false) (pw6 lr lx lx lr lr lr) (by decide)
theorem c4_holdK (b c d : K3) : lutK I_c4 [.f, b, c, d, .f, .f] = .f :=
  forced (v := false) (pw6 lr lx lx lx lr lr) (by decide)
/-- The arbiter with no request keeps q = 1, whatever A0 does (held or not). -/
theorem arb_holdK (a0 : K3) : lutK I_arb [.f, .f, .t, .f, a0, .t] = .t :=
  forced (v := true) (pw6 lr lr lr lr lx lr) (by decide)
/-- R0 (O5) and both grants are 0 with no request, whatever q, rst, A0. -/
theorem arb_quietK (q r a0 : K3) :
    lutK (I_arb % 2 ^ 32) [.f, .f, q, r, a0] = .f ∧
    lutK (I_grant % 2 ^ 32) [.f, .f, q, .f, .f] = .f ∧
    lutK I_grant [.f, .f, q, .f, .f, .t] = .f :=
  ⟨forced (v := false) (pw5 lr lr lx lx lx) (by decide),
   forced (v := false) (pw5 lr lr lx lr lr) (by decide),
   forced (v := false) (pw6 lr lr lx lr lr lr) (by decide)⟩

/-! ### 1c. Guards: readers of never-reset data are definite while their request is 0 -/

/-- `bd_steer`: request 0 gives both branch requests 0, select anything (X). -/
theorem steer_guardK (s : K3) :
    lutK (I_steer % 2 ^ 32) [.f, s, .f, .f, .f] = .f ∧ lutK I_steer [.f, s, .f, .f, .f, .t] = .f :=
  ⟨forced (v := false) (pw5 lr lx lr lr lr) (by decide),
   forced (v := false) (pw6 lr lx lr lr lr lr) (by decide)⟩
/-- `bd_mux.uj0` with `ctl_req = 0`, `j0 = 0`: 0 whatever `x_req` and the select. -/
theorem uj0_guardK (x s : K3) : lutK I_uj0 [x, .f, s, .f, .f, .f] = .f :=
  forced (v := false) (pw6 lx lr lx lr lr lr) (by decide)
/-- `bd_mux.uj0` with `x_req = 0`, `j0 = 0`: 0 whatever `ctl_req` and the select. -/
theorem uj0_guardK' (c s : K3) : lutK I_uj0 [.f, c, s, .f, .f, .f] = .f :=
  forced (v := false) (pw6 lr lx lx lr lr lr) (by decide)
theorem uj1_guardK (y s : K3) : lutK I_uj1 [y, .f, s, .f, .f, .f] = .f :=
  forced (v := false) (pw6 lx lr lx lr lr lr) (by decide)
theorem uj1_guardK' (c s : K3) : lutK I_uj1 [.f, c, s, .f, .f, .f] = .f :=
  forced (v := false) (pw6 lr lx lx lr lr lr) (by decide)
/-- gcd_rig's sampling LUTs (`uerr_d`, `uok_d`, `uabsn_d`: data on I0, padded
request on I1; `ucmpb_d`: request on I2) are 0 while their request is 0. -/
theorem rig_cmp_guardK (m z : K3) :
    lutK I_and2 [m, .f] = .f ∧ lutK I_ok [m, .f] = .f ∧ lutK I_cmpb [m, z, .f] = .f :=
  ⟨forced (v := false) (pw2 lx lr) (by decide),
   forced (v := false) (pw2 lx lr) (by decide),
   forced (v := false) (pw3 lx lx lr) (by decide)⟩

/-! ### 1c'. Release races: rst and an input moving together

`rst = x` (falling at the pin) together with the pins the first events from
the frontier can move (`x`), every other pin at its reset value, feedback at
the reset value. Where the Kleene value is still the reset value, the
one-cell state is closed under the step, so (7f `A_invariant`) the cell does
not move at all during the race, whatever the order of the two edges. Where
it is `x` (`*_race_movesK`), the event drives the cell to a FORCED new value
(`c2n_firesK`, the follow case of `c2_follow_hold`), which erases any
transient once the inputs persist for the loop bound. -/

/-- A `bd_c2` (join, fork-ack, mux-ack, arbiter-ack) that receives ONE input
while its rst releases: stays 0 (hold at the reset value). -/
theorem c2_race_holdK :
    lutK I_c2 [.x, .f, .f, .x, .f, .f] = .f ∧ lutK I_c2 [.f, .x, .f, .x, .f, .f] = .f := by
  decide
/-- `bd_c3`/`bd_c4` with all but one input moving: stay 0. -/
theorem c3_race_holdK : lutK I_c3 [.x, .x, .f, .f, .x, .f] = .f := by decide
theorem c4_race_holdK : lutK I_c4 [.x, .x, .x, .f, .f, .x] = .f := by decide
/-- An empty link controller whose request is low (ack moving), or whose next
stage is full (request moving): stays 0. -/
theorem c2n_race_holdK :
    lutK I_c2n [.f, .x, .f, .x, .f, .f] = .f ∧ lutK I_c2n [.x, .t, .f, .x, .f, .f] = .f := by
  decide
/-- `uenv1` with `env_c0` moving and `in_ack` low: stays 1. -/
theorem c2n_set_race_holdK : lutK I_c2n_set [.x, .f, .t, .x, .f, .f] = .t := by decide
/-- The mux joins with the request moving but `ctl_req` low (select X): stay 0. -/
theorem uj_race_holdK :
    lutK I_uj0 [.x, .f, .x, .f, .x, .f] = .f ∧ lutK I_uj1 [.x, .f, .x, .f, .x, .f] = .f := by
  decide
/-- The cases that DO move (the first wave): a join whose second input
arrives, and a link controller whose request arrives, during release. Their
new excitation is forced (`c2n_firesK`; `c2_eq` with `a = b = 1`). -/
theorem race_movesK :
    lutK I_c2 [.t, .x, .f, .x, .f, .f] = .x ∧ lutK I_c2 [.t, .t, .x, .f, .f, .f] = .t ∧
    lutK I_c2n [.x, .f, .f, .x, .f, .f] = .x := by
  decide

/-! ### 1d. `bd_latch` is not reset (TernaryOnBits): what that costs -/

/-- An opaque latch holding X stays X: reset does not define it. -/
theorem latch_stays_x : lutK I_latch1 [.x, .f, .x, .f, .f, .f] = .x := by decide
/-- An opaque latch passes its feedback, whatever `d` (binary). -/
theorem latch_holdB : ∀ d q : Bool, lutB I_latch1 [d, false, q, false, false, false] = q := by
  decide
/-- **First write.** A transparent latch with a definite `d` is definite,
whatever its (possibly X) feedback: the first enable pulse erases the
power-up value. -/
theorem latch_write (b : Bool) (q : K3) :
    lutK I_latch1 [K3.ofBool b, .t, q, .f, .f, .f] = K3.ofBool b := by
  cases b
  · exact forced (v := false) (pw6 lr lr lx lr lr lr) (by decide)
  · exact forced (v := true) (pw6 lr lr lx lr lr lr) (by decide)
/-- The same for the low bit of a `bd_latch` pair (O5), whatever the other bit. -/
theorem latch2_write_lo (b : Bool) (q0 d1 q1 : K3) :
    lutK (I_latch2 % 2 ^ 32) [K3.ofBool b, .t, q0, d1, q1] = K3.ofBool b := by
  cases b
  · exact forced (v := false) (pw5 lr lr lx lx lx) (by decide)
  · exact forced (v := true) (pw5 lr lr lx lx lx) (by decide)
/-- And for the high bit (O6). -/
theorem latch2_write_hi (b : Bool) (d0 q0 q1 : K3) :
    lutK I_latch2 [d0, .t, q0, K3.ofBool b, q1, .t] = K3.ofBool b := by
  cases b
  · exact forced (v := false) (pw6 lx lr lx lr lx lr) (by decide)
  · exact forced (v := true) (pw6 lx lr lx lr lx lr) (by decide)

/-! ## 2. The generic network reset theorem -/

/-- All-X (unknown power-up / Kleene start). -/
def allX : Nat → K3 := fun _ => .x

def isIn : Node → Bool
  | .input => true
  | .gate _ _ => false

/-- The state "control nodes of rank `< r` at their reset values, inputs at
`a`, everything else `x`". -/
def Bst (N : Circ) (a : Nat → K3) (ctl : Nat → Bool) (rank : Nat → Nat) (R : Nat → Bool)
    (r i : Nat) : K3 :=
  if ctl i = true ∧ rank i < r then K3.ofBool (R i) else if isIn (N.node i) = true then a i else .x

/-- **The reset specification of a network.** `a` = the input vector during
reset (`rst = t`, every data input `x`); `ctl` marks the control nodes, `R`
their reset values, `rank` their depth below the reset-forced cells. -/
structure ResetSpec (N : Circ) (a : Nat → K3) (ctl : Nat → Bool) (rank : Nat → Nat)
    (R : Nat → Bool) : Prop where
  /-- control inputs (rst) carry their reset value during reset -/
  H_IN : ∀ n, N.node n = .input → ctl n = true → a n = K3.ofBool (R n)
  /-- **H_LOCAL**: each control LUT, with its control pins of lower rank at
  their reset values and EVERY other pin `x` (power-up junk, never-reset
  data), already gives its reset value. For a reset cell this is the forcing
  by `rst` (`*_rstK`, rank 0); for a comb LUT reading data it is the guard
  (`steer_guardK`, ...). -/
  H_LOCAL : ∀ n init pins, N.node n = .gate init pins → ctl n = true →
    lutK init (pins.map (srcK (Bst N a ctl rank R (rank n)))) = K3.ofBool (R n)

section generic
variable {N : Circ} {a : Nat → K3} {ctl : Nat → Bool} {rank : Nat → Nat} {R : Nat → Bool}

theorem eq_of_le_ofBool {z : K3} {b : Bool} (h : le z (K3.ofBool b)) : z = K3.ofBool b := by
  rcases h with h | h
  · exact h
  · cases b <;> simp [K3.ofBool] at h

theorem Bst_mono (S : ResetSpec N a ctl rank R) {r m : Nat} (hrm : r ≤ m) :
    sle (Bst N a ctl rank R m) (Bst N a ctl rank R r) := by
  intro i
  unfold Bst
  by_cases hc : ctl i = true
  · by_cases hr : rank i < r
    · have hm : rank i < m := by omega
      simp only [hc, hr, hm, and_self, ite_true]; exact lr
    · by_cases hm : rank i < m
      · simp only [hc, hr, hm, and_self, and_false, ite_true, ite_false]
        cases hn : N.node i with
        | input => simp only [isIn, ite_true]; rw [S.H_IN i hn hc]; exact lr
        | gate _ _ => simp only [isIn]; exact lx
      · simp only [hc, hr, hm, and_false, ite_false]; exact lr
  · have : ¬ (ctl i = true ∧ rank i < r) := fun h => hc h.1
    have : ¬ (ctl i = true ∧ rank i < m) := fun h => hc h.1
    simp only [*]; exact lr

/-- **Reset, ternary.** After `m + 1` Jacobi steps from all-X with the reset
inputs, the state is at least as defined as `Bst m`. -/
theorem reset_iter (S : ResetSpec N a ctl rank R) :
    ∀ m, sle (iter N a (m + 1) allX) (Bst N a ctl rank R m) := by
  intro m
  induction m with
  | zero =>
    intro n
    rw [iter_succ']
    show le (stepK N a allX n) _
    unfold stepK Bst
    cases hn : N.node n with
    | input => simp only [isIn, Nat.not_lt_zero, and_false, ite_false, ite_true]; exact lr
    | gate _ _ => simp only [isIn, Nat.not_lt_zero, and_false, ite_false]; exact lx
  | succ m ih =>
    intro n
    rw [iter_succ']
    unfold stepK
    cases hn : N.node n with
    | input =>
      simp only
      unfold Bst
      rw [hn]
      by_cases h : ctl n = true ∧ rank n < m + 1
      · simp only [h, and_self, ite_true]; rw [S.H_IN n hn h.1]; exact lr
      · simp only [h, ite_false, isIn, ite_true]; exact lr
    | gate init pins =>
      simp only
      by_cases h : ctl n = true ∧ rank n < m + 1
      · have hB : Bst N a ctl rank R (m + 1) n = K3.ofBool (R n) := by
          unfold Bst; simp only [h, and_self, ite_true]
        rw [hB]
        have hle : sle (iter N a (m + 1) allX) (Bst N a ctl rank R (rank n)) :=
          fun i => le_trans (ih i) (Bst_mono S (by omega) i)
        have := lutK_mono init (pins_le _ _ hle pins)
        rw [S.H_LOCAL n init pins hn h.1] at this
        exact this
      · have hB : Bst N a ctl rank R (m + 1) n = .x := by
          unfold Bst; simp only [h, ite_false, hn, isIn]; rfl
        rw [hB]; exact lx

/-- **Reset contract, Kleene from all-X.** Every control node of rank `< m`
is at its reset value after `m + 1` steps. -/
theorem reset_ternary (S : ResetSpec N a ctl rank R) (m n : Nat) (hc : ctl n = true)
    (hr : rank n < m) : iter N a (m + 1) allX n = K3.ofBool (R n) := by
  have h := reset_iter S m n
  have hB : Bst N a ctl rank R m n = K3.ofBool (R n) := by
    unfold Bst; simp only [hc, hr, and_self, ite_true]
  rw [hB] at h
  exact eq_of_le_ofBool h

/-- **Reset contract, binary, from ANY power-up state.** In every bounded GMW
run (gate bound `D`, wire bound `W`, the latter covering the rst fanout skew)
whose inputs stay inside the reset vector `a` on `(0, E]` (rst source held at
1; data inputs anything), every control node of rank `< m` shows its reset
value at every step of `[(m+1)(D+W+1), E]`. No hypothesis on `v 0`. -/
theorem reset_binary (S : ResetSpec N a ctl rank R) {v : Nat → Nat → Bool} (Rn : Run N v)
    {D W : Nat} (hB : Bounded N v Rn D W) (E : Nat)
    (H_RST_HELD : ∀ k, 0 < k → k ≤ E → TernaryPhases.InputsIn N v a k)
    (m n : Nat) (hc : ctl n = true) (hr : rank n < m) :
    ∀ k, (m + 1) * (D + W + 1) ≤ k → k ≤ E → v k n = R n := by
  intro k hk hkE
  have hpost : sle (stepK N allX allX) allX := fun _ => lx
  have hent : ∀ k, k ≤ 0 → 0 ≤ k + W → covers allX (v k) := fun _ _ _ _ => rfl
  have hu : ∀ k, 0 < k → k ≤ E → TernaryPhases.InputsIn N v allX k :=
    fun _ _ _ _ _ => rfl
  have hc' := (TernaryPhases.phase_cov N allX a allX hpost Rn hB 0 0 E (Nat.le_refl 0)
    hent hu H_RST_HELD).2 (m + 1) k (by omega) hkE n
  rw [reset_ternary S m n hc hr] at hc'
  exact (admits_ofBool_iff _ _).1 hc'

end generic

/-! ## 3. Concrete instance: the rig ring with one of every reset-carrying cell

Node map (pins `[I0, ...]`; `nN` = node `N`; every INIT verbatim):

| n | instance (role) | cell / INIT | pins |
|---|---|---|---|
| 0 | `rst` | input | |
| 1 | vector / upstream data bit | input (X) | |
| 2 | `uenv1` (env_c) | bd_c2n_set | n3, n4, n2, n0 |
| 3 | `uenv0` (env_c0 = res_ack) | bd_c2n | n15, n2, n3, n0 |
| 4 | `ufork` ack tree (in_ack) | bd_c3 | n7, n7, n7, n4, n0 |
| 5 | link A ctl (frontier) | bd_c2n | n2, n10, n5, n0 |
| 6, 7 | link A uack FASTRISE | LUT1 2, LUT2 E | n5; n6, n5 |
| 8 | link A latch bit | bd_latch odd B8.. | n1, n5, n8 |
| 9 | link A rdly | LUT1 2 | n5 |
| 10 | link B uack | LUT1 2 | n11 |
| 11 | link B ctl | bd_c2n | n9, n14, n11, n0 |
| 12 | link B latch bit | bd_latch odd | n8, n11, n12 |
| 13 | link B rdly | LUT1 2 | n11 |
| 14 | steer uack | LUT2 E | n16, n3 |
| 15 | steer req1 (-> res_req) | LUT6_2 O6 8888..2222 | n13, n12, 0,0,0,1 |
| 16 | steer req0 (-> sink: ack0 = req0) | LUT6_2 O5 | n13, n12, 0,0,0 |
| 17 | `bd_src` | LUT1 1 | n19 |
| 18 | source link ctl (frontier) | bd_c2n | n17, n26, n18, n0 |
| 19, 20 | its uack, rdly | LUT1 2 | n18 |
| 21, 22 | `bd_mux` uj0, uj1 (s = link B latch, X) | AE08.., EA80.. | n20/n9, n13, n12, n21/n22, n0 |
| 23 | mux uor | LUT2 E | n21, n22 |
| 24, 25 | gated delay g0, g1 | LUT1 2, LUT2 8 | n23; n24, n23 |
| 26, 27 | mux uxa, uya | bd_c2 | n21/n22, n32, self, n0 |
| 28 | `bd_arbiter` ustate O6 (q) | FFF0FFB2ACACACAC | n25, n20, n28, n0, n32, 1 |
| 29 | ustate O5 (R0) | low 32 bits | n25, n20, n28, n0, n32 |
| 30, 31 | ugrant O5 (g1), O6 (g2) | 0C0C0C0CA0A0A0A0 | n25, n20, n28, 0, 0(, 1) |
| 32 | `bd_c4` (A0) | 00000000FFFE8000 | n29, n30, n31, n10, n32, n0 |
| 33, 34 | arbiter ua1, ua2 | bd_c2 | n30/n31, n32, self, n0 |

The ring part (0..16) is the rig's environment closed through two link
stages and a steer (one channel stands for the three forked ones). The rest
is a zoo: one instance of every other reset-carrying cell type, wired to the
ring's nets so that it sees the token and the X selects. Its wiring is NOT a
working circuit; it exercises each real INIT under the reset rule. -/

def nd (i : Nat) : Src := .node i
def k0 : Src := .const false
def k1 : Src := .const true

def rigNodes : List Node :=
  [ .input, .input,
    .gate I_c2n_set [nd 3, nd 4, nd 2, nd 0, k0, k0],           -- 2 uenv1
    .gate I_c2n [nd 15, nd 2, nd 3, nd 0, k0, k0],              -- 3 uenv0
    .gate I_c3 [nd 7, nd 7, nd 7, nd 4, nd 0, k0],              -- 4 ufork ack
    .gate I_c2n [nd 2, nd 10, nd 5, nd 0, k0, k0],              -- 5 link A ctl
    .gate I_buf [nd 5],                                         -- 6 uack buf
    .gate I_or2 [nd 6, nd 5],                                   -- 7 uack side
    .gate I_latch1 [nd 1, nd 5, nd 8, k0, k0, k0],              -- 8 latch A
    .gate I_buf [nd 5],                                         -- 9 rdly A
    .gate I_buf [nd 11],                                        -- 10 uack B
    .gate I_c2n [nd 9, nd 14, nd 11, nd 0, k0, k0],             -- 11 link B ctl
    .gate I_latch1 [nd 8, nd 11, nd 12, k0, k0, k0],            -- 12 latch B
    .gate I_buf [nd 11],                                        -- 13 rdly B
    .gate I_or2 [nd 16, nd 3],                                  -- 14 steer uack
    .gate I_steer [nd 13, nd 12, k0, k0, k0, k1],               -- 15 req1
    .gate (I_steer % 2 ^ 32) [nd 13, nd 12, k0, k0, k0],        -- 16 req0
    .gate I_src [nd 19],                                        -- 17 bd_src
    .gate I_c2n [nd 17, nd 26, nd 18, nd 0, k0, k0],            -- 18 source link
    .gate I_buf [nd 18],                                        -- 19 uack S
    .gate I_buf [nd 18],                                        -- 20 rdly S
    .gate I_uj0 [nd 20, nd 13, nd 12, nd 21, nd 0, k0],         -- 21 uj0
    .gate I_uj1 [nd 9, nd 13, nd 12, nd 22, nd 0, k0],          -- 22 uj1
    .gate I_or2 [nd 21, nd 22],                                 -- 23 uor
    .gate I_buf [nd 23],                                        -- 24 gated g0
    .gate I_and2 [nd 24, nd 23],                                -- 25 gated g1
    .gate I_c2 [nd 21, nd 32, nd 26, nd 0, k0, k0],             -- 26 uxa
    .gate I_c2 [nd 22, nd 32, nd 27, nd 0, k0, k0],             -- 27 uya
    .gate I_arb [nd 25, nd 20, nd 28, nd 0, nd 32, k1],         -- 28 q
    .gate (I_arb % 2 ^ 32) [nd 25, nd 20, nd 28, nd 0, nd 32],  -- 29 R0
    .gate (I_grant % 2 ^ 32) [nd 25, nd 20, nd 28, k0, k0],     -- 30 g1
    .gate I_grant [nd 25, nd 20, nd 28, k0, k0, k1],            -- 31 g2
    .gate I_c4 [nd 29, nd 30, nd 31, nd 10, nd 32, nd 0],       -- 32 c4
    .gate I_c2 [nd 30, nd 32, nd 33, nd 0, k0, k0],             -- 33 ua1
    .gate I_c2 [nd 31, nd 32, nd 34, nd 0, k0, k0] ]            -- 34 ua2

def rigNet : Circ := ⟨35, fun n => rigNodes.getD n .input⟩

/-- Control nodes: all but the data input and the two latch bits. -/
def rigCtl (n : Nat) : Bool := decide (n < 35) && !(n == 1 || n == 8 || n == 12)

/-- Reset values: `rst` itself, the token (`uenv1`), the source's request, the
arbiter's q; every other control node 0. -/
def rigR (n : Nat) : Bool := n == 0 || n == 2 || n == 17 || n == 28

def rigRankL : List Nat :=
  [0, 0, 0, 0, 0, 0, 1, 2, 0, 1, 1, 0, 0, 1, 3, 2, 2, 2, 0, 1, 1, 0, 0, 1, 2, 3, 0, 0, 0, 4,
   4, 4, 0, 0, 0]
def rigRank (n : Nat) : Nat := rigRankL.getD n 0

/-- During reset: `rst = t`, data `x`. -/
def rigA (n : Nat) : K3 := if n = 0 then .t else .x

def rigChk : Bool :=
  (List.range 35).all fun n =>
    match rigNet.node n with
    | .input => !rigCtl n || decide (rigA n = K3.ofBool (rigR n))
    | .gate init pins =>
      !rigCtl n ||
        decide (lutK init (pins.map (srcK (Bst rigNet rigA rigCtl rigRank rigR (rigRank n))))
          = K3.ofBool (rigR n))

theorem rigChk_ok : rigChk = true := by decide

/-- The same checker on any node list (used by the negative controls). -/
def chkFor (nodes : List Node) : Bool :=
  let N : Circ := ⟨35, fun n => nodes.getD n .input⟩
  (List.range 35).all fun n =>
    match N.node n with
    | .input => !rigCtl n || decide (rigA n = K3.ofBool (rigR n))
    | .gate init pins =>
      !rigCtl n ||
        decide (lutK init (pins.map (srcK (Bst N rigA rigCtl rigRank rigR (rigRank n))))
          = K3.ofBool (rigR n))

theorem chkFor_rig : chkFor rigNodes = true := by decide

/-- **Negative control 1 (unguarded reader).** Replace the steer's `req1`
(an AND of the request and the X select) by an OR of the same two pins: the
X of the never-reset latch escapes into the control network and the check
fails. -/
theorem neg_unguarded : chkFor (rigNodes.set 15 (.gate I_or2 [nd 13, nd 12])) = false := by
  decide

/-- **Negative control 2 (a controller without reset).** Tie link B's rst pin
to 0 (a `bd_c2n` used as if reset were optional): its power-up X is never
cleared and the check fails. -/
theorem neg_norst :
    chkFor (rigNodes.set 11 (.gate I_c2n [nd 9, nd 14, nd 11, k0, k0, k0])) = false := by
  decide

theorem rigCtl_lt {n : Nat} (h : rigCtl n = true) : n < 35 := by
  simp only [rigCtl, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1

/-- **The rig skeleton meets the reset specification** (every control node,
real INITs, X on every data pin and every latch). -/
theorem rig_spec : ResetSpec rigNet rigA rigCtl rigRank rigR where
  H_IN n hn hc := by
    have h := rigChk_ok
    unfold rigChk at h
    rw [List.all_eq_true] at h
    have := h n (List.mem_range.2 (rigCtl_lt hc))
    simp only [hn, hc, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
    exact this
  H_LOCAL n init pins hn hc := by
    have h := rigChk_ok
    unfold rigChk at h
    rw [List.all_eq_true] at h
    have := h n (List.mem_range.2 (rigCtl_lt hc))
    simp only [hn, hc, Bool.not_true, Bool.false_or, decide_eq_true_eq] at this
    exact this

/-- Max rank is 4: five Jacobi steps from all-X define every control node. -/
theorem rigRank_lt {n : Nat} (h : rigCtl n = true) : rigRank n < 5 := by
  have hl := rigCtl_lt h
  have : ∀ n, n < 35 → rigRank n < 5 := by decide
  exact this n hl

theorem rig_reset_ternary (n : Nat) (hc : rigCtl n = true) :
    iter rigNet rigA 6 allX n = K3.ofBool (rigR n) :=
  reset_ternary rig_spec 5 n hc (rigRank_lt hc)

/-- **Rig skeleton, binary**: every bounded run with rst held on `(0, E]`, from
any power-up state, has every control node at its reset value on
`[6(D+W+1), E]`; in particular every link controller is 0 (empty),
`uenv1` is 1 (the token), the source request is 1, the arbiter's q is 1. -/
theorem rig_reset_binary {v : Nat → Nat → Bool} (Rn : Run rigNet v) {D W : Nat}
    (hB : Bounded rigNet v Rn D W) (E : Nat)
    (H_RST_HELD : ∀ k, 0 < k → k ≤ E → TernaryPhases.InputsIn rigNet v rigA k)
    (n : Nat) (hc : rigCtl n = true) :
    ∀ k, 6 * (D + W + 1) ≤ k → k ≤ E → v k n = rigR n :=
  reset_binary rig_spec Rn hB E H_RST_HELD 5 n hc (rigRank_lt hc)

/-- The latch bits are left X by reset (they are not control nodes, and the
Kleene iteration does not define them: opaque, X fed back). -/
theorem rig_latch_x : ∀ q : K3, lutK I_latch1 [.x, .f, q, .f, .f, .f] = q ∨ q = .x := by
  intro q; cases q <;> decide

/-! ### The simultaneous-release state and the frontier -/

/-- Every pin sees `rst = 0`, every control net its reset value, data `x`. -/
def postB (i : Nat) : K3 := if i = 0 then .f else if rigCtl i = true then K3.ofBool (rigR i) else .x

/-- The excitation of node `n` at the simultaneous-release state. -/
def postExc (n : Nat) : K3 :=
  match rigNet.node n with
  | .input => postB n
  | .gate init pins => lutK init (pins.map (srcK postB))

/-- **The frontier.** At the simultaneous-release state (`rst`, node 0, now
0) exactly two control nodes are not at a fixed point: link A's controller (node 5, fed by `uenv1`'s
token) and the source link's controller (node 18, fed by `bd_src`). Both are
`bd_c2n` link controllers with excitation 1: they fill. -/
theorem rig_frontier :
    (List.range 35).filter
        (fun n => n != 0 && rigCtl n && decide (postExc n ≠ K3.ofBool (rigR n))) = [5, 18] ∧ postExc 5 = .t ∧ postExc 18 = .t := by
  decide

/-- Every control node's excitation is definite at release although every
latch and select is X (the guards hold at the release state too). -/
theorem rig_post_definite :
    (List.range 35).all (fun n => !rigCtl n || decide (postExc n ≠ .x)) = true := by
  decide

/-! ## 4. Release, timed (window channels, 5b/5f's `LoopG`) -/

section timed
open CElemTiming CTreeTimed

/-- `bd_c2n_set`'s INIT is `rst + maj(a, ~b, q)`. -/
theorem c2n_set_eq (a b q r : Bool) :
    exc I_c2n_set a b q r = (r || ((a && !b) || (a && q) || (!b && q))) := by
  cases a <;> cases b <;> cases q <;> cases r <;> decide

variable {a b rst O qp : Trace} {dlmin dlmax dwmin dwmax : Nat}

/-- **`bd_c2n` reset and hold through release** (non-frontier link
controller, fork/join `bd_c2n` uses). `rst` at the pin for the loop bound
`Dmax`, from ANY power-up value; then, as long as the request is low or the
next stage is full, the controller reads 0, across the release. -/
theorem c2n_reset
    (L : LoopG (fun t q => exc INIT_c2n (a t) (b t) q (rst t)) O qp dlmin dlmax dwmin dwmax)
    (t0 t2 : Nat)
    (H_RST_PULSE : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → rst s = true)
    (H_QUIET : ∀ s, t0 ≤ s → s ≤ t2 → a s = false ∨ b s = true) :
    (∀ t, t0 + dlmax ≤ t → t ≤ t2 + dlmin → O t = false) ∧
    (∀ t, t0 + (dlmax + dwmax) ≤ t → t ≤ t2 + (dlmin + dwmin) → qp t = false) := by
  have hforce : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) →
      ∀ q, exc INIT_c2n (a s) (b s) q (rst s) = false := by
    intro s h1 h2 q
    rw [c2n_eq, H_RST_PULSE s h1 h2]; rfl
  have hfix : ∀ s, t0 ≤ s → s < t2 + 1 → exc INIT_c2n (a s) (b s) false (rst s) = false := by
    intro s h1 h2
    rw [c2n_eq]
    rcases H_QUIET s h1 (by omega) with h | h <;> rw [h] <;> cases a s <;> cases b s <;>
      cases rst s <;> rfl
  exact ⟨fun t h1 h2 => O_heldG L false t0 (t2 + 1) hforce hfix t h1 (by omega),
    fun t h1 h2 => qp_heldG L false t0 (t2 + 1) hforce hfix t h1 (by omega)⟩

/-- **`bd_c2n_set` (the rig's `uenv1`) holds its token across release.**
Forced to 1 by `rst`, from ANY power-up value; afterwards, as long as
`env_c0 = 1` or `in_ack = 0` (`a ∨ ¬b`), it stays 1 with no glitch: the
excitation is 1 throughout. -/
theorem c2n_set_reset
    (L : LoopG (fun t q => exc I_c2n_set (a t) (b t) q (rst t)) O qp dlmin dlmax dwmin dwmax)
    (t0 t2 : Nat)
    (H_RST_PULSE : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) → rst s = true)
    (H_QUIET : ∀ s, t0 ≤ s → s ≤ t2 → a s = true ∨ b s = false) :
    (∀ t, t0 + dlmax ≤ t → t ≤ t2 + dlmin → O t = true) ∧
    (∀ t, t0 + (dlmax + dwmax) ≤ t → t ≤ t2 + (dlmin + dwmin) → qp t = true) := by
  have hforce : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) →
      ∀ q, exc I_c2n_set (a s) (b s) q (rst s) = true := by
    intro s h1 h2 q
    rw [c2n_set_eq, H_RST_PULSE s h1 h2]; rfl
  have hfix : ∀ s, t0 ≤ s → s < t2 + 1 → exc I_c2n_set (a s) (b s) true (rst s) = true := by
    intro s h1 h2
    rw [c2n_set_eq]
    rcases H_QUIET s h1 (by omega) with h | h <;> rw [h] <;> cases a s <;> cases b s <;>
      cases rst s <;> rfl
  exact ⟨fun t h1 h2 => O_heldG L true t0 (t2 + 1) hforce hfix t h1 (by omega),
    fun t h1 h2 => qp_heldG L true t0 (t2 + 1) hforce hfix t h1 (by omega)⟩

/-- **The frontier stage.** A `bd_c2n` link controller whose request pin
carries the initial token (`a = 1`) and whose next stage is empty (`b = 0`)
through reset and after it: held at 0 while `rst` is high at ITS pin (from
any power-up value, once `rst` has been high for the loop bound), and 1 from
`r + dlmax` on, where `r` is the release instant at its own rst pin. It fires
once; between `r + dlmin` and `r + dlmax` the window channel may show either
value (a FIFO LUT would show one edge). No ordering between the rst and
request selects is needed: the request is static. -/
theorem c2n_frontier
    (L : LoopG (fun t q => exc INIT_c2n (a t) (b t) q (rst t)) O qp dlmin dlmax dwmin dwmax)
    (t0 r t2 : Nat)
    (H_RST_HI : ∀ s, t0 ≤ s → s < r → rst s = true)
    (H_RST_LONG : t0 + (dlmax + dwmax) ≤ r)
    (H_RST_LO : ∀ s, r ≤ s → s ≤ t2 → rst s = false)
    (H_TOKEN : ∀ s, t0 ≤ s → s ≤ t2 → a s = true ∧ b s = false)
    (H_STAY : r + (dlmax + dwmax) ≤ t2 + 1) :
    (∀ t, t0 + dlmax ≤ t → t < r + dlmin → O t = false) ∧
    (∀ t, r + dlmax ≤ t → t ≤ t2 + dlmin → O t = true) := by
  constructor
  · have hforce : ∀ s, t0 ≤ s → s < t0 + (dlmax + dwmax) →
        ∀ q, exc INIT_c2n (a s) (b s) q (rst s) = false := by
      intro s h1 h2 q
      rw [c2n_eq, H_RST_HI s h1 (by omega)]; rfl
    have hfix : ∀ s, t0 ≤ s → s < r → exc INIT_c2n (a s) (b s) false (rst s) = false := by
      intro s h1 h2
      rw [c2n_eq, H_RST_HI s h1 h2]; rfl
    exact fun t h1 h2 => O_heldG L false t0 r hforce hfix t h1 h2
  · have hforce : ∀ s, r ≤ s → s < r + (dlmax + dwmax) →
        ∀ q, exc INIT_c2n (a s) (b s) q (rst s) = true := by
      intro s h1 h2 q
      have ⟨ha, hb⟩ := H_TOKEN s (by omega) (by omega)
      rw [c2n_eq, ha, hb, H_RST_LO s h1 (by omega)]; rfl
    have hfix : ∀ s, r ≤ s → s < t2 + 1 → exc INIT_c2n (a s) (b s) true (rst s) = true := by
      intro s h1 h2
      have ⟨ha, hb⟩ := H_TOKEN s (by omega) (by omega)
      rw [c2n_eq, ha, hb, H_RST_LO s h1 (by omega)]; rfl
    exact fun t h1 h2 => O_heldG L true r (t2 + 1) hforce hfix t h1 (by omega)

/-- A window channel moves only after its input did: an output different from
`c` at `t` was read from an input different from `c` at some `s` with
`s + dmin ≤ t`. -/
theorem win_causal {dmin dmax : Nat} {x y : Trace} (h : WinDelay dmin dmax x y) (c : Bool)
    (t : Nat) (ht : dmax ≤ t) (hy : y t ≠ c) : ∃ s, s + dmin ≤ t ∧ t ≤ s + dmax ∧ x s ≠ c := by
  obtain ⟨s, h1, h2, e⟩ := h t ht
  exact ⟨s, h2, h1, e ▸ hy⟩

/-- A feedback-LUT cell leaves its reset value `v` only after a non-quiet pin
(`¬ quiet s`) or its own feedback did: `quiet s` = every non-feedback pin at
its reset value at `s`, and `H_FIX` = the reset value is a fixed point of the
excitation on quiet pins (for a non-frontier cell this includes `rst = 0`;
`rig_frontier` lists the cells for which it does not). -/
theorem loop_causal {F : Nat → Bool → Bool} (L : LoopG F O qp dlmin dlmax dwmin dwmax)
    (v : Bool) (quiet : Nat → Prop) (H_FIX : ∀ s, quiet s → F s v = v)
    (t : Nat) (ht : dlmax + dwmax ≤ t) (hO : O t ≠ v) :
    ∃ s, s + dlmin ≤ t ∧ t ≤ s + dlmax ∧
      (¬ quiet s ∨ ∃ s', s' + dwmin ≤ s ∧ s ≤ s' + dwmax ∧ O s' ≠ v) := by
  obtain ⟨s, h1, h2, e⟩ := L.H_LUT t (by omega)
  refine ⟨s, h2, h1, ?_⟩
  by_cases hq : quiet s
  · right
    have hqp : qp s ≠ v := by
      intro hqv; apply hO; rw [e]; show F s (qp s) = v; rw [hqv]; exact H_FIX s hq
    exact win_causal L.H_FB v s (by omega) hqp
  · left; exact hq

end timed

/-! ### First change: nothing leaves reset before its potential -/

/-- **First change.** Nodes `n` with binary traces `v n` and reset values
`R n`, settled on `[S0, S)` (from `reset_binary`). `H_CAUSAL` (from
`loop_causal`/`win_causal` per cell and wire): a node away from its reset
value at `t ≥ S` is a frontier node past its own release plus its LUT
minimum, or a predecessor `e.1` was away from reset at some `s ≥ S0` with
`s + e.2 ≤ t` (`e.2` = minimum delay of that edge, positive). A potential
`P` below every frontier release and closed under the edges bounds the first
change: `v n t = R n` for `t < P n`. -/
theorem first_change (v : Nat → Nat → Bool) (R : Nat → Bool) (P : Nat → Nat) (S0 S : Nat)
    (frontier : Nat → Prop) (rel dmin : Nat → Nat) (pred : Nat → List (Nat × Nat))
    (H_SETTLED : ∀ n t, S0 ≤ t → t < S → v n t = R n)
    (H_CAUSAL : ∀ n t, S ≤ t → v n t ≠ R n →
      (frontier n ∧ rel n + dmin n ≤ t) ∨
        ∃ e ∈ pred n, ∃ s, S0 ≤ s ∧ s + e.2 ≤ t ∧ v e.1 s ≠ R e.1)
    (H_POS : ∀ n e, e ∈ pred n → 1 ≤ e.2)
    (H_POT_F : ∀ n, frontier n → P n ≤ rel n + dmin n)
    (H_POT_E : ∀ n e, e ∈ pred n → P n ≤ P e.1 + e.2) :
    ∀ n t, S0 ≤ t → t < P n → v n t = R n := by
  intro n t
  induction t using Nat.strongRecOn generalizing n with
  | _ t ih =>
    intro h0 hP
    by_cases hS : t < S
    · exact H_SETTLED n t h0 hS
    · apply Classical.byContradiction
      intro hne
      rcases H_CAUSAL n t (by omega) hne with ⟨hf, hr⟩ | ⟨e, he, s, hs0, hst, hv⟩
      · have := H_POT_F n hf; omega
      · have hpos := H_POS n e he
        have hpe := H_POT_E n e he
        by_cases hsP : s < P e.1
        · exact hv (ih s (by omega) e.1 hs0 hsP)
        · omega

/-- **Release before the first event (`H_RST_SKEW`).** If a reset cell's rst
pin has released by `relG` and every node `m` that drives one of its pins
through an edge of minimum delay `w` has `relG < P m + w`, then the cell is
released while every one of its pins still shows its reset value: the
design leaves reset in the simultaneous-release state (`postExc`). -/
theorem released_quiet (v : Nat → Nat → Bool) (R : Nat → Bool) (P : Nat → Nat) (S0 : Nat)
    (H_FIRST : ∀ n t, S0 ≤ t → t < P n → v n t = R n)
    (relG : Nat) (pins : List (Nat × Nat))
    (H_RST_SKEW : ∀ e ∈ pins, relG < P e.1 + e.2) :
    ∀ e ∈ pins, ∀ s, S0 ≤ s → s + e.2 ≤ relG → v e.1 s = R e.1 := by
  intro e he s hs hle
  have := H_RST_SKEW e he
  exact H_FIRST e.1 s hs (by omega)

end Formal.Cells.ResetContract
