import Formal.Net.Muller
import Formal.Net.MullerCert
open Formal.Net.Muller
theorem t1 : ((List.range 32).flatMap (bucket cert_rt4)).all (fun s => memC cert_rt4 256 s) = true := by decide +kernel
