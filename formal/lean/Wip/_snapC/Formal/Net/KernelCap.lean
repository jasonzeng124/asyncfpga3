import Formal.Net.KernelCapWalk

/-!
# Probe C-8y2: `kernel_circuit_safe`, the capstone for any kernel

For any kernel `[KD] [KP]` (data and checked obligations, `KernelCapDefs`): for every input
`(a, b)` in the kernel's domain, every run `ch` of the kernel's concrete circuit network whose
operators all meet their gate models (H_CELLS: the 8f/8j/8l cell models, `CapNet.Cell`),
whose channels are all bundled (H_BUNDLE) and whose `start` source is offered at most once
(H_START_ONCE) latches on `out0` only `spec a b`, and the latched list at every time is
`spec a b` repeated once per completed handshake.

This is C-8s's `gcd_hw_circuit_safe3` with every gcd-specific constant made a field; its
proof is the gcd proof (C-8m/8q/8r/8s), transcribed once over the class (`KernelCapHist` ..
`KernelCapWalk`). Instances: gcd_hw (`KernelCapGcd`), ipow (`KernelCapIpow`), collatz
(`KernelCapCollatz`).

What it does NOT cover (unchanged from gcd_hw, see `notes/C-gcd_hw-hypotheses.md`):
liveness (an all-quiet run meets every hypothesis), the binding of the Ops hand models to
B's generated cells (O4), H_BUNDLE's zero-delay statement (8w/8x), and a re-offered `start`
(H_START_ONCE is "start rises once, ever").
-/

namespace Formal.Net.KCap
open Formal.Net Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.Handshake Formal.Net.Ops
open Formal.Net.CapNet hiding R Hh Hh_pr Hh_cn NoEnd JOK FoldOK OpChk
open KD KP

/-- **The capstone, for any kernel.** -/
theorem kernel_circuit_safe [KD] [KP] (a b : Nat) (hd : dom a b) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcVal a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch start).req) t ≤ 1) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = spec a b) ∧
    (∀ t, closedVals (ch out0) t =
      List.replicate (Handshake.cnt (fallB (ch out0).ack) t) (spec a b)) :=
  kernel_circuit_safe3 a b hd ch H_CELLS H_BUNDLE H_START_ONCE

end Formal.Net.KCap
