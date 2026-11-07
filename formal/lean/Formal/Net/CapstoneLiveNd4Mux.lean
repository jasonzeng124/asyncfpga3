import Formal.Net.CapstoneNetChk

/-!
# Probe C-8z4 (2): the mux-exception "disables" relation of gcd_hw has depth one

8z3: the only non-persistent gcd_hw gates (outside a contested arbiter) are the input
acknowledges of the 2-way and 3-way muxes, whose falling excitation is withdrawn only by the
mux's `z_ack` rising. For `CapstoneLiveNd4Serial.serial` the relation "`z_ack`'s gate may
disable `x_ack`'s gate" must be ranked. `z_ack` is driven by the consumer of `z`; this file
checks (kernel) that no mux output is consumed by a mux, so no `z_ack` gate is itself a mux
input acknowledge: rank 0 for the mux input acknowledges and 1 for every other gate works
(chains have length one, no cycle).

Scope: a structural fact about the network only. It does not prove the other half of the
serialization condition (each changed gate stays excited in the intermediate states).
-/

namespace Formal.Net.CapNet.Live.Nd4
open Formal.Net Formal.Net.CapNet Formal.Net.CapNet.Gcd

/-- Is this operator a 2-way or 3-way mux? -/
def isMuxB : K NC → Bool
  | .mux _ _ _ _ _ => true
  | .muxn _ _ _ _ _ _ => true
  | _ => false

/-- The consumer of a mux output is not a mux. -/
def muxOutOK : K NC → Bool
  | .mux _ _ _ z _ => !isMuxB (opAt (consOf z))
  | .muxn _ _ _ _ z _ => !isMuxB (opAt (consOf z))
  | _ => true

theorem mux_out_chk : ops.all muxOutOK = true := by decide +kernel

/-- **No mux output feeds a mux** (2-way or 3-way), for all 367 operators. -/
theorem mux_out_not_mux (p : Fin NO) : muxOutOK (opAt p) = true :=
  List.all_eq_true.mp mux_out_chk _ getD_mem

/-- The same, unfolded for a 2-way mux. -/
theorem mux_cons_not_mux {p : Fin NO} {c x y z : Fin NC} {mw : MW}
    (hp : opAt p = .mux c x y z mw) : isMuxB (opAt (consOf z)) = false := by
  have := mux_out_not_mux p
  rw [hp] at this; simpa [muxOutOK] using this

/-- The same, unfolded for the 3-way mux. -/
theorem muxn_cons_not_mux {p : Fin NO} {c x0 x1 x2 z : Fin NC} {nw : NW}
    (hp : opAt p = .muxn c x0 x1 x2 z nw) : isMuxB (opAt (consOf z)) = false := by
  have := mux_out_not_mux p
  rw [hp] at this; simpa [muxOutOK] using this

end Formal.Net.CapNet.Live.Nd4
