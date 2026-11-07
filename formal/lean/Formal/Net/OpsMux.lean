import Formal.Net.Ops

/-!
# C-8f: `bd_mux` (Dynamatic `mux`, 2-way: the loop header)

`cells/rtl/bd_mux.v` (INITs proved equal to these equations by B's
`LibCtlMergeMux`: `j0_spec`, `j1_spec`, `c2_spec`, `or2_spec`):

    j0 = C(x_req, ctl_req . ~s)      j1 = C(y_req, ctl_req . s)
    z_req = delta(j0 + j1)           x_ack = C(j0, z_ack)   y_ack = C(j1, z_ack)
    ctl_ack = z_ack                  z_data = s ? y_data : x_data

Gate model `Mux sel x y c z j0 j1` (SI gates, binary; `s = sel c.dat`):
* H_CEL_SI on `j0`, `j1`, `x_ack`, `y_ack`: each moves only to the value both
  its C-element inputs had one tick earlier.
* H_DELAY_LUMPED: the OR and the matched delay line are one unbounded inertial
  node from `j0 ∨ j1` to `z_req`.
* H_WIRE_DI: `ctl_ack` is an unbounded inertial delay of `z_ack`.
* H_DATA_COMB: `z.dat = if s then y.dat else x.dat` at every tick; the real
  data-mux delay and the select-to-data skew are what `Held z` has to cover
  (H_MUX_DATA in the notes).
* `Held c` (the control channel's bundling) keeps `s` still inside each control
  transaction: the mux's select-before-request obligation (H_MUX_SEL).

The state space is finite, so the invariant is not written by hand: it is the
set `tbl` of the 132 reachable states (with three counter differences), found by
`Wip/C8f/mux_reach.py`, and `mux_closed` checks by kernel `decide` that it is
closed under every step the gates and the environment allow (no
native code: `decide +kernel` is checked by the kernel, no extra axiom).

Proved: `mux_proto` (causal assume-guarantee), `mux_op` with the token
equation `σ z k = if sel (σ c k) then σ y (#1s among σ c 0..k-1) else
σ x (#0s among σ c 0..k-1)` (mux SELECTS by the select token; the unselected
input's token stays).
-/

namespace Formal.Net.Ops.Mux
open Formal.Net Formal.Net.Handshake Formal.Net.Ops

/-- One reachable state of the bd_mux model plus three counter differences
(`dc = #c↑ - #z↑`, `dxo = 1 + #x↑ - #c↑(s=0)`, `dyo = 1 + #y↑ - #c↑(s=1)`). -/
structure MS where
  xr : Bool
  xa : Bool
  yr : Bool
  ya : Bool
  cr : Bool
  ca : Bool
  s : Bool
  zr : Bool
  za : Bool
  j0 : Bool
  j1 : Bool
  dc : Nat
  dxo : Nat
  dyo : Nat
  deriving DecidableEq

def tbl : List MS := [
  ⟨false, false, false, false, false, false, false, false, false, false, false, 0, 1, 1⟩,
  ⟨true, false, false, false, false, false, false, false, false, false, false, 0, 2, 1⟩,
  ⟨false, true, false, false, false, false, false, false, false, false, false, 0, 1, 1⟩,
  ⟨false, false, true, false, false, false, false, false, false, false, false, 0, 1, 2⟩,
  ⟨true, false, true, false, false, false, false, false, false, false, false, 0, 2, 2⟩,
  ⟨false, true, true, false, false, false, false, false, false, false, false, 0, 1, 2⟩,
  ⟨false, false, false, true, false, false, false, false, false, false, false, 0, 1, 1⟩,
  ⟨true, false, false, true, false, false, false, false, false, false, false, 0, 2, 1⟩,
  ⟨false, true, false, true, false, false, false, false, false, false, false, 0, 1, 1⟩,
  ⟨false, false, false, false, true, false, false, false, false, false, false, 1, 0, 1⟩,
  ⟨true, false, false, false, true, false, false, false, false, false, false, 1, 1, 1⟩,
  ⟨false, true, false, false, true, false, false, false, false, false, false, 1, 0, 1⟩,
  ⟨false, false, true, false, true, false, false, false, false, false, false, 1, 0, 2⟩,
  ⟨true, false, true, false, true, false, false, false, false, false, false, 1, 1, 2⟩,
  ⟨false, true, true, false, true, false, false, false, false, false, false, 1, 0, 2⟩,
  ⟨false, false, false, true, true, false, false, false, false, false, false, 1, 0, 1⟩,
  ⟨true, false, false, true, true, false, false, false, false, false, false, 1, 1, 1⟩,
  ⟨false, true, false, true, true, false, false, false, false, false, false, 1, 0, 1⟩,
  ⟨false, false, false, false, false, true, false, false, false, false, false, 0, 1, 1⟩,
  ⟨true, false, false, false, false, true, false, false, false, false, false, 0, 2, 1⟩,
  ⟨false, true, false, false, false, true, false, false, false, false, false, 0, 1, 1⟩,
  ⟨false, false, true, false, false, true, false, false, false, false, false, 0, 1, 2⟩,
  ⟨true, false, true, false, false, true, false, false, false, false, false, 0, 2, 2⟩,
  ⟨false, true, true, false, false, true, false, false, false, false, false, 0, 1, 2⟩,
  ⟨false, false, false, true, false, true, false, false, false, false, false, 0, 1, 1⟩,
  ⟨true, false, false, true, false, true, false, false, false, false, false, 0, 2, 1⟩,
  ⟨false, true, false, true, false, true, false, false, false, false, false, 0, 1, 1⟩,
  ⟨false, false, false, false, false, false, true, false, false, false, false, 0, 1, 1⟩,
  ⟨true, false, false, false, false, false, true, false, false, false, false, 0, 2, 1⟩,
  ⟨false, true, false, false, false, false, true, false, false, false, false, 0, 1, 1⟩,
  ⟨false, false, true, false, false, false, true, false, false, false, false, 0, 1, 2⟩,
  ⟨true, false, true, false, false, false, true, false, false, false, false, 0, 2, 2⟩,
  ⟨false, true, true, false, false, false, true, false, false, false, false, 0, 1, 2⟩,
  ⟨false, false, false, true, false, false, true, false, false, false, false, 0, 1, 1⟩,
  ⟨true, false, false, true, false, false, true, false, false, false, false, 0, 2, 1⟩,
  ⟨false, true, false, true, false, false, true, false, false, false, false, 0, 1, 1⟩,
  ⟨false, false, false, false, true, false, true, false, false, false, false, 1, 1, 0⟩,
  ⟨true, false, false, false, true, false, true, false, false, false, false, 1, 2, 0⟩,
  ⟨false, true, false, false, true, false, true, false, false, false, false, 1, 1, 0⟩,
  ⟨false, false, true, false, true, false, true, false, false, false, false, 1, 1, 1⟩,
  ⟨true, false, true, false, true, false, true, false, false, false, false, 1, 2, 1⟩,
  ⟨false, true, true, false, true, false, true, false, false, false, false, 1, 1, 1⟩,
  ⟨false, false, false, true, true, false, true, false, false, false, false, 1, 1, 0⟩,
  ⟨true, false, false, true, true, false, true, false, false, false, false, 1, 2, 0⟩,
  ⟨false, true, false, true, true, false, true, false, false, false, false, 1, 1, 0⟩,
  ⟨false, false, false, false, false, true, true, false, false, false, false, 0, 1, 1⟩,
  ⟨true, false, false, false, false, true, true, false, false, false, false, 0, 2, 1⟩,
  ⟨false, true, false, false, false, true, true, false, false, false, false, 0, 1, 1⟩,
  ⟨false, false, true, false, false, true, true, false, false, false, false, 0, 1, 2⟩,
  ⟨true, false, true, false, false, true, true, false, false, false, false, 0, 2, 2⟩,
  ⟨false, true, true, false, false, true, true, false, false, false, false, 0, 1, 2⟩,
  ⟨false, false, false, true, false, true, true, false, false, false, false, 0, 1, 1⟩,
  ⟨true, false, false, true, false, true, true, false, false, false, false, 0, 2, 1⟩,
  ⟨false, true, false, true, false, true, true, false, false, false, false, 0, 1, 1⟩,
  ⟨false, true, false, false, false, true, false, false, true, false, false, 0, 1, 1⟩,
  ⟨false, true, true, false, false, true, false, false, true, false, false, 0, 1, 2⟩,
  ⟨false, true, false, true, false, true, false, false, true, false, false, 0, 1, 1⟩,
  ⟨false, false, false, true, false, true, true, false, true, false, false, 0, 1, 1⟩,
  ⟨true, false, false, true, false, true, true, false, true, false, false, 0, 2, 1⟩,
  ⟨false, true, false, true, false, true, true, false, true, false, false, 0, 1, 1⟩,
  ⟨false, true, false, false, false, true, false, true, true, false, false, 0, 1, 1⟩,
  ⟨false, true, true, false, false, true, false, true, true, false, false, 0, 1, 2⟩,
  ⟨false, true, false, true, false, true, false, true, true, false, false, 0, 1, 1⟩,
  ⟨false, false, false, true, false, true, true, true, true, false, false, 0, 1, 1⟩,
  ⟨true, false, false, true, false, true, true, true, true, false, false, 0, 2, 1⟩,
  ⟨false, true, false, true, false, true, true, true, true, false, false, 0, 1, 1⟩,
  ⟨true, false, false, false, true, false, false, false, false, true, false, 1, 1, 1⟩,
  ⟨true, false, true, false, true, false, false, false, false, true, false, 1, 1, 2⟩,
  ⟨true, false, false, true, true, false, false, false, false, true, false, 1, 1, 1⟩,
  ⟨true, false, false, false, true, false, false, true, false, true, false, 0, 1, 1⟩,
  ⟨true, false, true, false, true, false, false, true, false, true, false, 0, 1, 2⟩,
  ⟨true, false, false, true, true, false, false, true, false, true, false, 0, 1, 1⟩,
  ⟨true, false, false, false, true, false, false, true, true, true, false, 0, 1, 1⟩,
  ⟨false, true, false, false, true, false, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, true, false, false, true, false, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, false, true, false, true, false, false, true, true, true, false, 0, 1, 2⟩,
  ⟨false, true, true, false, true, false, false, true, true, true, false, 0, 1, 2⟩,
  ⟨true, true, true, false, true, false, false, true, true, true, false, 0, 1, 2⟩,
  ⟨true, false, false, true, true, false, false, true, true, true, false, 0, 1, 1⟩,
  ⟨false, true, false, true, true, false, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, true, false, true, true, false, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, false, false, false, false, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨false, true, false, false, false, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, true, false, false, false, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, false, true, false, false, true, false, true, true, true, false, 0, 1, 2⟩,
  ⟨false, true, true, false, false, true, false, true, true, true, false, 0, 1, 2⟩,
  ⟨true, true, true, false, false, true, false, true, true, true, false, 0, 1, 2⟩,
  ⟨true, false, false, true, false, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨false, true, false, true, false, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, true, false, true, false, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, false, false, false, true, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨false, true, false, false, true, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, true, false, false, true, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, false, true, false, true, true, false, true, true, true, false, 0, 1, 2⟩,
  ⟨false, true, true, false, true, true, false, true, true, true, false, 0, 1, 2⟩,
  ⟨true, true, true, false, true, true, false, true, true, true, false, 0, 1, 2⟩,
  ⟨true, false, false, true, true, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨false, true, false, true, true, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨true, true, false, true, true, true, false, true, true, true, false, 0, 1, 1⟩,
  ⟨false, false, true, false, true, false, true, false, false, false, true, 1, 1, 1⟩,
  ⟨true, false, true, false, true, false, true, false, false, false, true, 1, 2, 1⟩,
  ⟨false, true, true, false, true, false, true, false, false, false, true, 1, 1, 1⟩,
  ⟨false, false, true, false, true, false, true, true, false, false, true, 0, 1, 1⟩,
  ⟨true, false, true, false, true, false, true, true, false, false, true, 0, 2, 1⟩,
  ⟨false, true, true, false, true, false, true, true, false, false, true, 0, 1, 1⟩,
  ⟨false, false, true, false, true, false, true, true, true, false, true, 0, 1, 1⟩,
  ⟨true, false, true, false, true, false, true, true, true, false, true, 0, 2, 1⟩,
  ⟨false, true, true, false, true, false, true, true, true, false, true, 0, 1, 1⟩,
  ⟨false, false, false, true, true, false, true, true, true, false, true, 0, 1, 1⟩,
  ⟨true, false, false, true, true, false, true, true, true, false, true, 0, 2, 1⟩,
  ⟨false, true, false, true, true, false, true, true, true, false, true, 0, 1, 1⟩,
  ⟨false, false, true, true, true, false, true, true, true, false, true, 0, 1, 1⟩,
  ⟨true, false, true, true, true, false, true, true, true, false, true, 0, 2, 1⟩,
  ⟨false, true, true, true, true, false, true, true, true, false, true, 0, 1, 1⟩,
  ⟨false, false, true, false, false, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨true, false, true, false, false, true, true, true, true, false, true, 0, 2, 1⟩,
  ⟨false, true, true, false, false, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨false, false, false, true, false, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨true, false, false, true, false, true, true, true, true, false, true, 0, 2, 1⟩,
  ⟨false, true, false, true, false, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨false, false, true, true, false, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨true, false, true, true, false, true, true, true, true, false, true, 0, 2, 1⟩,
  ⟨false, true, true, true, false, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨false, false, true, false, true, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨true, false, true, false, true, true, true, true, true, false, true, 0, 2, 1⟩,
  ⟨false, true, true, false, true, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨false, false, false, true, true, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨true, false, false, true, true, true, true, true, true, false, true, 0, 2, 1⟩,
  ⟨false, true, false, true, true, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨false, false, true, true, true, true, true, true, true, false, true, 0, 1, 1⟩,
  ⟨true, false, true, true, true, true, true, true, true, false, true, 0, 2, 1⟩,
  ⟨false, true, true, true, true, true, true, true, true, false, true, 0, 1, 1⟩]

def b2n (b : Bool) : Nat := if b then 1 else 0

/-- Successor entry for given next signal values. -/
def nxt (e : MS) (xr xa yr ya cr ca s zr za j0 j1 : Bool) : MS :=
  ⟨xr, xa, yr, ya, cr, ca, s, zr, za, j0, j1,
   e.dc + b2n (!e.cr && cr) - b2n (!e.zr && zr),
   e.dxo + b2n (!e.xr && xr) - b2n (!e.cr && cr && !s),
   e.dyo + b2n (!e.yr && yr) - b2n (!e.cr && cr && s)⟩

/-- What the closure check concludes about one allowed step. -/
def Concl (e : MS) (xr xa yr ya cr ca s zr za j0 j1 : Bool) : Prop :=
  let n := nxt e xr xa yr ya cr ca s zr za j0 j1
  tbl.contains n = true ∧
  n.dc + b2n (!e.zr && zr) = e.dc + b2n (!e.cr && cr) ∧
  n.dxo + b2n (!e.cr && cr && !s) = e.dxo + b2n (!e.xr && xr) ∧
  n.dyo + b2n (!e.cr && cr && s) = e.dyo + b2n (!e.yr && yr) ∧
  (xa ≠ e.xa → e.xa ≠ e.xr) ∧ (ya ≠ e.ya → e.ya ≠ e.yr) ∧ (ca ≠ e.ca → e.ca ≠ e.cr) ∧
  (zr ≠ e.zr → e.zr = e.za) ∧
  ((!e.zr && zr) = true → e.cr = true ∧ e.ca = false ∧ e.za = false ∧ e.dc = 1 ∧
     (if e.s then e.yr = true ∧ e.ya = false ∧ e.dyo = 1
      else e.xr = true ∧ e.xa = false ∧ e.dxo = 1))

instance (e : MS) (xr xa yr ya cr ca s zr za j0 j1 : Bool) :
    Decidable (Concl e xr xa yr ya cr ca s zr za j0 j1) := by
  unfold Concl; exact inferInstance

set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 100000 in
/-- Closure of the reachable set under every step the gate model and the
environment allow (interleaved so that `decide` prunes early). -/
theorem mux_closed : ∀ e ∈ tbl,
    ∀ xr : Bool, (xr ≠ e.xr → e.xr = e.xa) →
    ∀ yr : Bool, (yr ≠ e.yr → e.yr = e.ya) →
    ∀ cr : Bool, (cr ≠ e.cr → e.cr = e.ca) →
    ∀ za : Bool, (za ≠ e.za → e.za ≠ e.zr) →
    ∀ j0 : Bool, (j0 ≠ e.j0 → e.xr = j0 ∧ (e.cr && !e.s) = j0) →
    ∀ j1 : Bool, (j1 ≠ e.j1 → e.yr = j1 ∧ (e.cr && e.s) = j1) →
    ∀ zr : Bool, (zr ≠ e.zr → zr = (e.j0 || e.j1)) →
    ∀ xa : Bool, (xa ≠ e.xa → e.j0 = xa ∧ e.za = xa) →
    ∀ ya : Bool, (ya ≠ e.ya → e.j1 = ya ∧ e.za = ya) →
    ∀ ca : Bool, (ca ≠ e.ca → ca = e.za) →
    ∀ s : Bool, (s ≠ e.s → ¬ ((e.cr || e.ca) = true ∧ (cr || ca) = true)) →
    Concl e xr xa yr ya cr ca s zr za j0 j1 := by
  decide +kernel


set_option synthInstance.maxSize 4096 in
set_option synthInstance.maxHeartbeats 400000 in
set_option maxRecDepth 100000 in
/-- The guarantees need only the mux's own gate conditions at step `t`. -/
theorem mux_guar : ∀ e ∈ tbl,
    ∀ xa : Bool, (xa ≠ e.xa → e.j0 = xa ∧ e.za = xa) →
    ∀ ya : Bool, (ya ≠ e.ya → e.j1 = ya ∧ e.za = ya) →
    ∀ ca : Bool, (ca ≠ e.ca → ca = e.za) →
    ∀ zr : Bool, (zr ≠ e.zr → zr = (e.j0 || e.j1)) →
    (xa ≠ e.xa → e.xa ≠ e.xr) ∧ (ya ≠ e.ya → e.ya ≠ e.yr) ∧ (ca ≠ e.ca → e.ca ≠ e.cr) ∧
    (zr ≠ e.zr → e.zr = e.za) := by
  decide +kernel

theorem mux_init : ∀ s : Bool,
    tbl.contains ⟨false, false, false, false, false, false, s, false, false, false, false, 0, 1, 1⟩
      = true := by decide

structure Mux (sel : Nat → Bool) (x y c z : Chan) (j0 j1 : Trace) : Prop where
  cj0 : ∀ t, j0 (t + 1) ≠ j0 t → x.req t = j0 (t + 1) ∧ (c.req t && !sel (c.dat t)) = j0 (t + 1)
  cj1 : ∀ t, j1 (t + 1) ≠ j1 t → y.req t = j1 (t + 1) ∧ (c.req t && sel (c.dat t)) = j1 (t + 1)
  zr : ∀ t, z.req (t + 1) ≠ z.req t → z.req (t + 1) = (j0 t || j1 t)
  xa : ∀ t, x.ack (t + 1) ≠ x.ack t → j0 t = x.ack (t + 1) ∧ z.ack t = x.ack (t + 1)
  ya : ∀ t, y.ack (t + 1) ≠ y.ack t → j1 t = y.ack (t + 1) ∧ z.ack t = y.ack (t + 1)
  ca : ∀ t, c.ack (t + 1) ≠ c.ack t → c.ack (t + 1) = z.ack t
  dat : ∀ t, z.dat t = if sel (c.dat t) then y.dat t else x.dat t
  i0 : j0 0 = false
  i1 : j1 0 = false
  iz : z.req 0 = false
  ix : x.ack 0 = false
  iy : y.ack 0 = false
  ic : c.ack 0 = false

variable {sel : Nat → Bool} {x y c z : Chan} {j0 j1 : Trace}

def st (sel : Nat → Bool) (x y c z : Chan) (j0 j1 : Trace) (t dc dxo dyo : Nat) : MS :=
  ⟨x.req t, x.ack t, y.req t, y.ack t, c.req t, c.ack t, sel (c.dat t), z.req t, z.ack t,
   j0 t, j1 t, dc, dxo, dyo⟩

/-- #offers on `c` (before `t`) whose select is 0 / 1. -/
def cnt0 (sel : Nat → Bool) (c : Chan) : Nat → Nat :=
  cnt (fun u => riseB c.req u && !sel (c.dat (u + 1)))
def cnt1 (sel : Nat → Bool) (c : Chan) : Nat → Nat :=
  cnt (fun u => riseB c.req u && sel (c.dat (u + 1)))

theorem mem_of_contains {e : MS} (h : tbl.contains e = true) : e ∈ tbl := by
  simpa using h

/-- The invariant: the state at `t` is in `tbl`, with the counters. -/
theorem mux_inv (M : Mux sel x y c z j0 j1) (hx : x.req 0 = false) (hy : y.req 0 = false)
    (hc : c.req 0 = false) (hz : z.ack 0 = false) (hh : Held c) : ∀ t,
    (∀ s, s < t → SendStep x s ∧ SendStep y s ∧ SendStep c s ∧ RecvStep z s) →
    ∃ dc dxo dyo, tbl.contains (st sel x y c z j0 j1 t dc dxo dyo) = true ∧
      cnt (riseB c.req) t = cnt (riseB z.req) t + dc ∧
      cnt (riseB x.req) t + 1 = cnt0 sel c t + dxo ∧
      cnt (riseB y.req) t + 1 = cnt1 sel c t + dyo := by
  intro t
  induction t with
  | zero =>
    intro _
    refine ⟨0, 1, 1, ?_, rfl, rfl, rfl⟩
    simp only [st, hx, hy, hc, hz, M.i0, M.i1, M.iz, M.ix, M.iy, M.ic]
    exact mux_init _
  | succ t ih =>
    intro hp
    obtain ⟨dc, dxo, dyo, hm, h1, h2, h3⟩ := ih (fun s hs => hp s (by omega))
    obtain ⟨sx, sy, sc, rz⟩ := hp t (by omega)
    have K := mux_closed _ (mem_of_contains hm) (x.req (t + 1)) sx (y.req (t + 1)) sy
      (c.req (t + 1)) sc (z.ack (t + 1)) rz (j0 (t + 1)) (M.cj0 t) (j1 (t + 1)) (M.cj1 t)
      (z.req (t + 1)) (M.zr t) (x.ack (t + 1)) (M.xa t) (y.ack (t + 1)) (M.ya t)
      (c.ack (t + 1)) (M.ca t) (sel (c.dat (t + 1)))
      (fun hne ⟨a1, a2⟩ => hne (by rw [hh t a1 a2] <;> rfl))
    obtain ⟨Km, Kc, Kx, Ky, _⟩ := K
    refine ⟨_, _, _, Km, ?_, ?_, ?_⟩
    · have e1 : cnt (riseB c.req) (t + 1) = cnt (riseB c.req) t +
          b2n (!c.req t && c.req (t + 1)) := rfl
      have e2 : cnt (riseB z.req) (t + 1) = cnt (riseB z.req) t +
          b2n (!z.req t && z.req (t + 1)) := rfl
      simp only [st, nxt] at Kc ⊢
      omega
    · have e1 : cnt (riseB x.req) (t + 1) = cnt (riseB x.req) t +
          b2n (!x.req t && x.req (t + 1)) := rfl
      have e2 : cnt0 sel c (t + 1) = cnt0 sel c t +
          b2n (!c.req t && c.req (t + 1) && !sel (c.dat (t + 1))) := rfl
      simp only [st, nxt] at Kx ⊢
      omega
    · have e1 : cnt (riseB y.req) (t + 1) = cnt (riseB y.req) t +
          b2n (!y.req t && y.req (t + 1)) := rfl
      have e2 : cnt1 sel c (t + 1) = cnt1 sel c t +
          b2n (!c.req t && c.req (t + 1) && sel (c.dat (t + 1))) := rfl
      simp only [st, nxt] at Ky ⊢
      omega

theorem mux_proto (M : Mux sel x y c z j0 j1) (hx : x.req 0 = false) (hy : y.req 0 = false)
    (hc : c.req 0 = false) (hz : z.ack 0 = false) (hh : Held c) : ∀ t,
    (∀ s, s < t → SendStep x s ∧ SendStep y s ∧ SendStep c s ∧ RecvStep z s) →
    RecvStep x t ∧ RecvStep y t ∧ RecvStep c t ∧ SendStep z t := by
  intro t hp
  obtain ⟨dc, dxo, dyo, hm, _⟩ := mux_inv M hx hy hc hz hh t hp
  exact mux_guar _ (mem_of_contains hm) (x.ack (t + 1)) (M.xa t) (y.ack (t + 1)) (M.ya t)
    (c.ack (t + 1)) (M.ca t) (z.req (t + 1)) (M.zr t)

/-! ## Network level -/

variable {C : Type}

/-- The mux's token equation. -/
def muxEq (sel : Nat → Bool) (cc cx cy cz : C) (σ : C → Nat → Nat) : Prop :=
  ∀ k, σ cz k = if sel (σ cc k) then σ cy (cnt (fun i => sel (σ cc i)) k)
    else σ cx (cnt (fun i => !sel (σ cc i)) k)

theorem mux_op (ch : C → Chan) (cc cx cy cz : C) (j0 j1 : Trace)
    (M : Mux sel (ch cx) (ch cy) (ch cc) (ch cz) j0 j1) :
    OpProto ch [cc, cx, cy] [cz] ∧ OpData ch [cc, cx, cy] [cz] (muxEq sel cc cx cy cz) := by
  have mc : cc ∈ [cc, cx, cy] := by simp
  have mx : cx ∈ [cc, cx, cy] := by simp
  have my : cy ∈ [cc, cx, cy] := by simp
  have mz : cz ∈ [cz] := List.mem_singleton_self _
  refine ⟨⟨fun t hi ho hhd hp => ?_, ?_, ?_⟩, ?_⟩
  · have h := mux_proto M (hi cx mx).1 (hi cy my).1 (hi cc mc).1 (ho cz mz).2 (hhd cc mc) t
      (fun s hs => ⟨((hp s hs).1 cx mx).1, ((hp s hs).1 cy my).1, ((hp s hs).1 cc mc).1,
        ((hp s hs).2 cz mz).2⟩)
    refine ⟨fun c' hc' => ?_, fun c' hc' => ?_⟩
    · simp at hc'
      rcases hc' with rfl | rfl | rfl
      · exact h.2.2.1
      · exact h.1
      · exact h.2.1
    · rw [List.mem_singleton.1 hc']; exact h.2.2.2
  · intro c' hc'; simp at hc'
    rcases hc' with rfl | rfl | rfl
    · exact M.ic
    · exact M.ix
    · exact M.iy
  · intro c' hc'; rw [List.mem_singleton.1 hc']; exact M.iz
  · intro hin hout c' hc' k r' hoff σ hag hE
    rw [List.mem_singleton.1 hc'] at hoff ⊢
    obtain ⟨hpc, hhc⟩ := hin cc mc
    obtain ⟨hpx, hhx⟩ := hin cx mx
    obtain ⟨hpy, hhy⟩ := hin cy my
    have hpz := (hout cz mz).1
    obtain ⟨dc, dxo, dyo, hm, h1, h2, h3⟩ := mux_inv M hpx.1.1 hpy.1.1 hpc.1.1 hpz.1.2 hhc r'
      (fun s _ => ⟨(hpx.2 s).1, (hpy.2 s).1, (hpc.2 s).1, (hpz.2 s).2⟩)
    have hr0 : (ch cz).req r' = false := by have := hoff.1; simp [riseB] at this; exact this.1
    have hr1 : (ch cz).req (r' + 1) = true := by have := hoff.1; simp [riseB] at this; exact this.2
    have K := mux_closed _ (mem_of_contains hm) _ (hpx.2 r').1 _ (hpy.2 r').1 _ (hpc.2 r').1
      _ (hpz.2 r').2 _ (M.cj0 r') _ (M.cj1 r') _ (M.zr r') _ (M.xa r') _ (M.ya r')
      _ (M.ca r') (sel ((ch cc).dat (r' + 1))) (fun hne ⟨a1, a2⟩ => hne (by rw [hhc r' a1 a2] <;> rfl))
    have Ko := K.2.2.2.2.2.2.2.2
    simp only [st, hr0, hr1] at Ko
    obtain ⟨hcr, hca, _, hdc, hsel⟩ := Ko rfl
    -- the control token
    obtain ⟨rc, ic, hrc, hoffc, hcrc, hcfc, _⟩ := open_offer hpc hcr
    have hic : ic = k := by rw [hoff.2] at h1; omega
    subst hic
    have hcfc' : cnt (fallB (ch cc).ack) (r' + 1) = ic := by simp [cnt, fallB, hca, hcfc]
    have hdc0 := held_at hpc hhc hoffc hrc hcfc
    have hdc1 := held_at hpc hhc hoffc (by omega) hcfc'
    have hσc : σ cc ic = (ch cc).dat (rc + 1) := hag cc ic rc hrc hoffc
    have hag' : ∀ i u, u < r' → OffAt (ch cc) i u → σ cc i = (ch cc).dat (u + 1) :=
      fun i u hu ho => hag cc i u hu ho
    rw [hE ic, M.dat, hσc, hdc1]
    cases hs : sel ((ch cc).dat (rc + 1))
    · -- select 0: input x
      rw [hdc0, hs] at hsel
      simp only [Bool.false_eq_true, ite_false] at hsel ⊢
      obtain ⟨hxr, hxa, hdx⟩ := hsel
      obtain ⟨rx, ix, hrx, hoffx, hcrx, hcfx, _⟩ := open_offer hpx hxr
      have hcfx' : cnt (fallB (ch cx).ack) (r' + 1) = ix := by simp [cnt, fallB, hxa, hcfx]
      have hco : cnt0 sel (ch cc) r' = cnt (fun i => !sel (σ cc i)) (cnt (riseB (ch cc).req) r') :=
        cnt_offers (fun v => !sel v) hag' r' (Nat.le_refl _)
      rw [hcrc] at hco
      have hsucc : cnt (fun i => !sel (σ cc i)) (ic + 1) = cnt (fun i => !sel (σ cc i)) ic + 1 := by
        show cnt (fun i => !sel (σ cc i)) ic + (if (!sel (σ cc ic)) = true then 1 else 0) = _
        rw [hσc, hs]; rfl
      have hix : cnt (fun i => !sel (σ cc i)) ic = ix := by omega
      rw [hix, hag cx ix rx hrx hoffx, held_at hpx hhx hoffx (by omega) hcfx']
    · -- select 1: input y
      rw [hdc0, hs] at hsel
      simp only [ite_true] at hsel ⊢
      obtain ⟨hyr, hya, hdy⟩ := hsel
      obtain ⟨ry, iy, hry, hoffy, hcry, hcfy, _⟩ := open_offer hpy hyr
      have hcfy' : cnt (fallB (ch cy).ack) (r' + 1) = iy := by simp [cnt, fallB, hya, hcfy]
      have hco : cnt1 sel (ch cc) r' = cnt (fun i => sel (σ cc i)) (cnt (riseB (ch cc).req) r') :=
        cnt_offers (fun v => sel v) hag' r' (Nat.le_refl _)
      rw [hcrc] at hco
      have hsucc : cnt (fun i => sel (σ cc i)) (ic + 1) = cnt (fun i => sel (σ cc i)) ic + 1 := by
        show cnt (fun i => sel (σ cc i)) ic + (if (sel (σ cc ic)) = true then 1 else 0) = _
        rw [hσc, hs]; rfl
      have hiy : cnt (fun i => sel (σ cc i)) ic = iy := by omega
      rw [hiy, hag cy iy ry hry hoffy, held_at hpy hhy hoffy (by omega) hcfy']

end Formal.Net.Ops.Mux
