import Formal.Net.CapstoneLiveNd4Mux
open Formal.Net Formal.Net.CapNet Formal.Net.CapNet.Gcd Formal.Net.CapNet.Live.Nd4
-- negative control: the check can fail. Channel 61 (g34-side x input) is consumed by a mux,
-- so a mux whose output were 61 would be rejected by `muxOutOK`.
example : isMuxB (opAt (consOf 61)) = true := by decide
example : muxOutOK (.mux 80 61 83 61 ⟨34, 59, 48, 60, 61, 0, 0, 0, 456, 77, 106, 0, 69, 39, [59, 62, 65]⟩) = false := by decide
