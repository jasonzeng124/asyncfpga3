import Formal.Net.Muller
import Wip.C8c.MullerCert
/-! UNFINISHED (probe 8c): rt mode, n = 4 (6076 states) via the literal
certificate of `MullerCert.lean` and `Muller.cert_sound`. Each 32-bucket chunk
took ~166 s and ~7.5 GB in the kernel on this sandbox (1/8 of the work), so the
whole instance (8 chunks) was not run to completion. To finish: compile
MullerCert to an olean, add chunks 32..255 below, and combine with
`cert_sound` (hK: 0 < 256, h0 = t0, hb from the chunks via `chunkOk_spec`). -/
open Formal.Net.Muller
theorem t0 : memC cert_rt4 256 0 = true := by decide +kernel
theorem t1 : chunkOk .rt 4 cert_rt4 256 0 32 = true := by decide +kernel
