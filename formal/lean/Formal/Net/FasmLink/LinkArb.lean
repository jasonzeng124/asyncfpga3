import Formal.Net.FasmLink.Basic
import Formal.Net.Import.Cells

/-!
# Track 11c: the logical design `link_arb` from the yosys-imported cells

`formal/tools/fasm2lean2/link_arb.v`: one `bd_link #(.W(3))` stage and one
`bd_arbiter`, sharing `rst`. Its logical netlist is composed here from 11a's
yosys-imported cell netlists (`Formal.Net.Import.Gen`, generated from yosys
0.62 by `formal/tools/import/import.sh`), unchanged:

* instance 0, `lnk.ctl.u` = `Gen.bd_c2n` (bd_link_ctl's C-element):
  `a = req_in`, `b = ack_out` (`c_next`), `rst`; its output `q` (the node
  `c`) drives BOTH `req_out` and `ack_in` (DELAY = DACK = 0);
* instance 1, `lnk.lat` = `Gen.bd_latch_W3` (one fractured LUT6_2 pair + one
  odd LUT6): `d = data_in`, `en` = STATE 0 of instance 0 (the node `c`,
  internal: it is on no port of the latch);
* instance 2, `arb` = `Gen.bd_arbiter` (ustate / ugrant LUT6_2 + two bd_c2),
  whose state nets `ua1.q`, `ua2.q`, `q` include the internal `q`.

The binding below is transcribed from `link_arb.v` / `bd_link.v`; the
`*_iface` facts pin the imported port order it relies on, and
`fasm2lean2/check.sh` cross-checks the composition against yosys's own
flattening of `link_arb` (same LUT cells, INITs and connections).
-/

namespace Formal.Net.FasmLink.LinkArb
open Formal.Net.FasmLink Formal.Net.Import

def insts : List Inst := [
  ⟨"lnk.ctl.u", Gen.bd_c2n, [.port "req_in", .port "ack_out", .port "rst"],
    [(0, "req_out"), (0, "ack_in")]⟩,
  ⟨"lnk.lat", Gen.bd_latch_W3, [.port "data_in[0]", .port "data_in[1]", .port "data_in[2]", .st 0 0],
    [(0, "data_out[0]"), (1, "data_out[1]"), (2, "data_out[2]")]⟩,
  ⟨"arb", Gen.bd_arbiter, [.port "rst", .port "r1", .port "r2", .port "A0"],
    [(0, "A1"), (1, "A2"), (2, "R0"), (3, "g1"), (4, "g2")]⟩]

theorem c2n_iface : Gen.bd_c2n.inputNames = ["a", "b", "rst"] ∧ Gen.bd_c2n.outputNames = ["q"] ∧
    Gen.bd_c2n.stateNames = ["$iopadmap$q"] := by decide
theorem latch_iface : Gen.bd_latch_W3.inputNames = ["d[0]", "d[1]", "d[2]", "en"] ∧
    Gen.bd_latch_W3.outputNames = ["q[0]", "q[1]", "q[2]"] := by decide
theorem arbiter_iface : Gen.bd_arbiter.inputNames = ["rst", "r1", "r2", "A0"] ∧
    Gen.bd_arbiter.outputNames = ["A1", "A2", "R0", "g1", "g2"] ∧
    Gen.bd_arbiter.stateNames = ["ua1.q", "ua2.q", "q"] := by decide

/-- The design of one routed seed: the logical instances above, the physical
net read from that seed's bits, and the proposed renaming. -/
def design (net : Formal.Net.Fasm.PNet) (ports : List String) (rho : List (List PSrc)) : Design :=
  ⟨insts, net, ports, rho, net.luts.length + 1⟩

end Formal.Net.FasmLink.LinkArb
