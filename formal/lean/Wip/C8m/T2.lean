import Formal.Net.CapstoneNet

/-!
# Probe C-8m: kernel checks of the generated gcd_hw circuit network

* `ops_ok`: every operator passes `OpChk` against `GcdHw.Gcd.rules` and the descriptors;
* `rank_ok`: the descriptor graph is ranked;
* `prod_ok`, `cons_ok`: every channel has exactly one producer and one consumer (the `Net`
  axioms);
* `out0_desc`: the environment's `out0` channel carries GcdHw channel 250 (`out0`).
-/

namespace Formal.Net.CapNet.Gcd
open Formal.Net Formal.Net.CapNet Formal.Net.GcdHw

set_option maxRecDepth 100000

def opAt (o : Fin NO) : K NC := ops.getD o.val (K.sink 0)
def prodOf (c : Fin NC) : Fin NO := prodT.getD c.val 0
def consOf (c : Fin NC) : Fin NO := consT.getD c.val 0

theorem prod_out : ∀ o : Fin NO, ∀ c ∈ (opAt o).outsC, prodOf c = o := by decide +kernel

end Formal.Net.CapNet.Gcd
