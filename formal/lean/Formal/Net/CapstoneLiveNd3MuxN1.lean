import Formal.Net.CapstoneLiveNd3MuxN

/-!
# Probe C-8z3 (3a): 3-way mux persistence, select 1 (split to bound kernel memory)
-/

namespace Formal.Net.CapNet.Live.Nd3

set_option maxRecDepth 100000 in
theorem npers1 : NPersS 1 := by decide +kernel

end Formal.Net.CapNet.Live.Nd3
