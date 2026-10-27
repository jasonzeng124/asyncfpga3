import Formal.Net.CapstoneLiveNdOff
/-! C-8z negative controls: the certificate checker rejects a tightened bound, a wrong
operator rule and a cyclic derivation (not built; run with `lake env lean`). -/
open Formal.Net.CapNet.Live.Nd Formal.Net.CapNet.Gcd
#eval ((entOf 0).al, (entOf 0).be, (entOf 0).ord)
-- the real entry passes
example : ruleOK 0 (entOf 0) (entOf 0).r = true := by decide +kernel
-- tightened constant (be 6 -> 5) is rejected
example : ruleOK 0 ⟨.dn 6 1, 1, 5, 5⟩ (.dn 6 1) = false := by decide +kernel
-- wrong rule kind (channel 0 is not produced from 6) is rejected
example : ruleOK 0 ⟨.up 6, 1, 6, 5⟩ (.up 6) = false := by decide +kernel
-- a derivation from a channel of the same round (cycle) is rejected
example : ruleOK 0 ⟨.dn 6 1, 1, 6, (entOf 6).ord⟩ (.dn 6 1) = false := by decide +kernel
