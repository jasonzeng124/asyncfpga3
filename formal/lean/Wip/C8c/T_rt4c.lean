import Formal.Net.Muller
import Formal.Net.MullerCert
open Formal.Net.Muller
theorem t0 : memC cert_rt4 256 0 = true := by decide +kernel
theorem t1 : chunkOk .rt 4 cert_rt4 256 0 32 = true := by decide +kernel
