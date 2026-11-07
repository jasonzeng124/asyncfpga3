import Formal.Net.Compute.GcdShli0K0
import Formal.Net.Compute.GcdShli0K1
import Formal.Net.Compute.GcdShli0K2
import Formal.Net.Compute.GcdShli0K3

/-!
# H_COMPUTE_FN for gcd_hw's left shift `ushli0`

Problem statement. This `bdc_fused_*` unit (bdc Verilog `z = e0 << e1`, 32 bits; in gcd_hw the
final `b << k`), as yosys synthesized it (a 412-cell LUT/MUXF barrel shifter), computes
`Ops.shli 32 a k` for EVERY `a` and every shift amount `k < 32` (`ushli0_fn`).

Proof: for each `k < 32` a `FixShOK` certificate (port `e1` fixed to `k`, constants folded
through LUT cofactors and MUXF selects; each output bit checked over its folded support),
`GcdShli0K0..3`, then `shl_sound`.

NOT shown: shift amounts `k ≥ 32` (Verilog gives 0; gcd_hw's `k` counts common factors of two
of operands below 2^31, so it stays below 31 -- that bound is a token-level fact not restated
here); LUT/MUXF semantics are shard A's models; timing; glitches.
-/

namespace Formal.Net.Compute.GcdD
open Formal.Net.Compute Formal.Net.GcdHw Formal.Gen.Compute.GcdD

/-- **ushli0 computes `e0 << e1`** for every `a` and every shift amount `k < 32`. -/
theorem ushli0_fn (a k : Nat) (hk : k < 32) :
    unitVal Ushli0.cells Ushli0.outs [a, k] = Ops.shli 32 a k := by
  match k, hk with
  | 0, _ => exact shl_sound ushli0_cert0 a
  | 1, _ => exact shl_sound ushli0_cert1 a
  | 2, _ => exact shl_sound ushli0_cert2 a
  | 3, _ => exact shl_sound ushli0_cert3 a
  | 4, _ => exact shl_sound ushli0_cert4 a
  | 5, _ => exact shl_sound ushli0_cert5 a
  | 6, _ => exact shl_sound ushli0_cert6 a
  | 7, _ => exact shl_sound ushli0_cert7 a
  | 8, _ => exact shl_sound ushli0_cert8 a
  | 9, _ => exact shl_sound ushli0_cert9 a
  | 10, _ => exact shl_sound ushli0_cert10 a
  | 11, _ => exact shl_sound ushli0_cert11 a
  | 12, _ => exact shl_sound ushli0_cert12 a
  | 13, _ => exact shl_sound ushli0_cert13 a
  | 14, _ => exact shl_sound ushli0_cert14 a
  | 15, _ => exact shl_sound ushli0_cert15 a
  | 16, _ => exact shl_sound ushli0_cert16 a
  | 17, _ => exact shl_sound ushli0_cert17 a
  | 18, _ => exact shl_sound ushli0_cert18 a
  | 19, _ => exact shl_sound ushli0_cert19 a
  | 20, _ => exact shl_sound ushli0_cert20 a
  | 21, _ => exact shl_sound ushli0_cert21 a
  | 22, _ => exact shl_sound ushli0_cert22 a
  | 23, _ => exact shl_sound ushli0_cert23 a
  | 24, _ => exact shl_sound ushli0_cert24 a
  | 25, _ => exact shl_sound ushli0_cert25 a
  | 26, _ => exact shl_sound ushli0_cert26 a
  | 27, _ => exact shl_sound ushli0_cert27 a
  | 28, _ => exact shl_sound ushli0_cert28 a
  | 29, _ => exact shl_sound ushli0_cert29 a
  | 30, _ => exact shl_sound ushli0_cert30 a
  | 31, _ => exact shl_sound ushli0_cert31 a
  | _ + 32, h => exact absurd h (by omega)

end Formal.Net.Compute.GcdD
