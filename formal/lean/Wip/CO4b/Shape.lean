import Formal.Net.CellBindOps
import Formal.Net.XorshiftCapData
import Formal.Net.CollatzCapData
import Formal.Net.KernelCapIpow
import Formal.Net.KernelCapGcd
open Formal.Net Formal.Net.CapNet
def kind {n : Nat} : K n → String
  | .forkG _ os => s!"forkG{os.length}"
  | .forkH _ os _ _ _ _ => s!"forkH{os.length}"
  | .join ins _ _ _ _ => s!"join{ins.length}"
  | .bjoin ins _ _ _ => s!"bjoin{ins.length}"
  | .steerC .. => "steerC" | .steerD .. => "steerD" | .mux .. => "mux" | .muxn .. => "muxn"
  | .amerge .. => "amerge" | .link .. => "link" | .src .. => "src" | .sink .. => "sink"
def hist (l : List String) : List (String × Nat) :=
  (l.eraseDups).map (fun s => (s, l.count s))
#eval (1:Nat)
#eval hist (Formal.Net.XorshiftCap.ops.map kind)
#eval hist (Formal.Net.CollatzCap.ops.map kind)
#eval hist (Formal.Net.IpowCap.ops.map kind)
#eval hist (Formal.Net.CapNet.Gcd.ops.map kind)
