-- Root of the Formal library. Every module under Formal/ is built (lakefile globs);
-- this file imports Shard A's Core API so `import Formal` gives the shared substrate.
import Formal.Core.Kleene
import Formal.Core.Lut
import Formal.Core.Circuit
import Formal.Core.Substrate
import Formal.Core.XSim
import Formal.Core.Ternary
import Formal.Core.Delay.SAF
import Formal.Core.Delay.GLSPass
import Formal.Core.Delay.CornerCode
import Formal.Core.Delay.InvolutionTransfer
import Formal.Core.TernaryChannels
