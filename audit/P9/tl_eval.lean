import Formal.Cells.SelfAuditB6
open Formal.Net Formal.Net.Handshake Formal.Net.CapNet Formal.Net.CapNet.Gcd Formal.Net.CapNet.Wit Formal.Cells.SelfAuditB6
#eval (List.range 500).filter (fun t => eS (t+1) != eS t)
#eval (List.range 500).filter (fun t => qS (t+1) != qS t)
#eval (List.range 500).filter (fun t => kS (t+1) != kS t)
#eval (List.range 500).filter (fun t => (chS out0).req (t+1) != (chS out0).req t)
#eval (rcd out0)
#eval Formal.Cells.SelfAuditB6.srcOK RA RB [99, 200]
