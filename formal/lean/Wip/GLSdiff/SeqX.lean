import Formal.Core.Lut
/-!
# GLSdiff: Kleene LDCE / FDRE against the research GLS's SLICE_LATX / SLICE_FFX

The tables are copied from `Formal/Gen/Netlist.lean` (`LDCE_INIT`, `FDRE_M`,
`FFQ_SYNC`, checked there by `prim_tables`), evaluated with Core's Kleene LUT
(`Lut.keval` = `kevalSpec`), as `Formal.Net.CoreLut.kevalL` does.  Cases match
`tools-A/glsdiff/tb_seq_x.v`.  #eval only.
-/
open Formal.Core Formal.Core.K3
namespace GLSdiff
def kevalL (init : Nat) (ins : List K3) : K3 :=
  (⟨BitVec.ofNat (2 ^ ins.length) init⟩ : Lut ins.length).keval (kvec ins ins.length)
def LDCE_INIT : Nat := 0x45554000          -- [CLR, D, G, GE, Q]
def FDRE_M : Nat := 0xAAFBAAEA00510040     -- [C, CE, D, R, Q, M]: master while C = 0
def FFQ_SYNC : Nat := 0xFFFFAAAA55550000   -- [C, CE, R, D, Q, M]: Q' = C ? M : Q
-- L1: closed (G=0), GE = X, D = 1, Q = 0
#eval kevalL LDCE_INIT [zero, one, zero, X, zero]
-- L2: CLR = X, open, D = 0, Q = 0
#eval kevalL LDCE_INIT [X, zero, one, one, zero]
-- L3: CLR = X, closed, D = 1, Q = 0
#eval kevalL LDCE_INIT [X, one, zero, zero, zero]
-- F1: master before the edge: C = 0, CE = 1, D = 1, R = X, Q = 0, M = 0; then Q' = M'
#eval let m := kevalL FDRE_M [zero, one, one, X, zero, zero]
      (m, kevalL FFQ_SYNC [one, one, X, one, zero, m])
-- F2: C = 0, CE = X, D = 0, R = 0, Q = 1, M = 1
#eval let m := kevalL FDRE_M [zero, X, zero, zero, one, one]
      (m, kevalL FFQ_SYNC [one, X, zero, zero, one, m])
end GLSdiff
