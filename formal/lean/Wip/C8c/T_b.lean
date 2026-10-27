import Formal.Net.Muller
import Formal.Net.MullerCert
open Formal.Net.Muller
theorem t1 : chunkOk .rt 4 cert_rt4 256 0 4 = true := by decide +kernel
