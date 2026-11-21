import Formal.Gen.Cells
import Formal.Gen.PrelimSem
import Formal.Cells.Latch
import Formal.Cells.LinkHandshake
import Formal.Cells.Bundling
import Formal.Core.Lut
import Formal.Core.LutCells
open Formal.Core.LutList

/-!
# 11d: generated latches, delay lines and the data mux (`bd_latch.v`)

Same three forms as `ProofsCE` (`_lut`: kind/INIT/pins = B's transcription;
`_gate_*`: gate function = B's; `_next`/`_outs`: unit-step reading = spec).
B's transcriptions matched: `Formal.Cells.Latch` (`ODD`, `PAIR`, `RST0`,
`RST1`, `bmux`), `Formal.Cells.LinkHandshake` (`INIT_LAT`, `INIT_PAIR`,
`latK`), `Formal.Cells.Bundling` (`BUF`, `FF_SIDE`, `FR_SIDE`, `ODD`, `PAIR`);
shard A's `Formal.Core.Lut.Init` and `Formal.Core.LutCells`.

`bd_datamux` has no shard-B transcription; it is checked against the header
equation `z = s ? b : a` and A's `Init.datamux_pair`/`datamux_odd`.

Delay lines are wires in the unit-step reading (`_outs` theorems): what is
checked is the LOGIC of the line (buffers, the FASTFALL AND-taps, the FASTRISE
OR-taps), i.e. that in steady state the line passes its input; the edge
timing is the timing layer's job (B's `Bundling`).
-/

namespace Formal.Gen.ProofsLatch
open Formal.Cells Formal.Gen Formal.Gen.Cells
open Formal.Cells.Latch (bmux ODD PAIR RST0 RST1)

/-! ## `bd_latch` -/

theorem bd_latch_W1_lut : bd_latch_W1.lutIs "odd.u" (.lut 6) ODD ["d", "en", "q", "0", "0", "0"] ["q"] := by
  decide +kernel
theorem bd_latch_W2_lut :
    bd_latch_W2.lutIs "pair[0].u" .lut6_2 PAIR ["d[0]", "en", "q[0]", "d[1]", "q[1]", "1"]
      ["q[0]", "q[1]"] := by decide +kernel
/-- W = 3: one pair and one odd LUT (both generate branches). -/
theorem bd_latch_W3_lut :
    bd_latch_W3.cellNames = ["odd.u", "pair[0].u"] ∧
    bd_latch_W3.lutIs "odd.u" (.lut 6) ODD ["d[2]", "en", "q[2]", "0", "0", "0"] ["q[2]"] ∧
    bd_latch_W3.lutIs "pair[0].u" .lut6_2 PAIR ["d[0]", "en", "q[0]", "d[1]", "q[1]", "1"]
      ["q[0]", "q[1]"] := by decide +kernel
theorem bd_latch_rst_W1_lut :
    bd_latch_rst_W1.lutIs "gbit[0].u" (.lut 6) RST0 ["d", "en", "q", "rst", "0", "0"] ["q"] := by
  decide +kernel
/-- `RESET_VALUE = 2'b10`: per-bit polarity, bit 0 clears (`RST0`), bit 1 presets (`RST1`). -/
theorem bd_latch_rst_W2_R2_lut :
    bd_latch_rst_W2_R2.lutIs "gbit[0].u" (.lut 6) RST0 ["d[0]", "en", "q[0]", "rst", "0", "0"] ["q[0]"] ∧
    bd_latch_rst_W2_R2.lutIs "gbit[1].u" (.lut 6) RST1 ["d[1]", "en", "q[1]", "rst", "0", "0"] ["q[1]"] := by
  decide +kernel

/-- The odd bit is B's `latK` (LinkHandshake, Kleene) and `bmux` (binary). -/
theorem bd_latch_W1_gate_K : ∀ d en q : K3,
    bd_latch_W1.gateN kleeneSemP "odd.u" .O [("d", d), ("en", en), ("q", q)] =
      some (Formal.Cells.LinkHandshake.latK d en q) := by decide +kernel
theorem bd_latch_W1_gate_B : ∀ d en q : Bool,
    bd_latch_W1.gateN boolSem "odd.u" .O [("d", d), ("en", en), ("q", q)] = some (bmux en d q) := by
  decide +kernel

/-- The pair, Kleene, both outputs (all 3^5): each bit is `K3.mux en q d`; X on
one bit's pins never reaches the other (B's `pair_o5_kleene`/`pair_o6_kleene`). -/
theorem bd_latch_W2_gate_K : ∀ d0 en q0 d1 q1 : K3,
    let env := [("d[0]", d0), ("en", en), ("q[0]", q0), ("d[1]", d1), ("q[1]", q1)]
    bd_latch_W2.gateN kleeneSemP "pair[0].u" .O5 env = some (K3.mux en q0 d0) ∧
    bd_latch_W2.gateN kleeneSemP "pair[0].u" .O6 env = some (K3.mux en q1 d1) := by decide +kernel

theorem latch_iface :
    bd_latch_W3.inputNames = ["d[0]", "d[1]", "d[2]", "en"] ∧
    bd_latch_W3.stateNames = ["q[0]", "q[1]", "q[2]"] ∧
    bd_latch_W3.outputNames = ["q[0]", "q[1]", "q[2]"] ∧
    bd_latch_rst_W2_R2.inputNames = ["d[0]", "d[1]", "en", "rst"] ∧
    bd_latch_rst_W2_R2.stateNames = ["q[0]", "q[1]"] := by decide +kernel

theorem bd_latch_W3_next : ∀ d0 d1 d2 en q0 q1 q2 : Bool,
    bd_latch_W3.next boolSem [d0, d1, d2, en] [q0, q1, q2] =
      some [bmux en d0 q0, bmux en d1 q1, bmux en d2 q2] ∧
    bd_latch_W3.outs boolSem [d0, d1, d2, en] [q0, q1, q2] = some [q0, q1, q2] := by decide +kernel

theorem bd_latch_W2_next_K : ∀ d0 d1 en q0 q1 : K3,
    bd_latch_W2.next kleeneSemP [d0, d1, en] [q0, q1] = some [K3.mux en q0 d0, K3.mux en q1 d1] := by
  decide +kernel

theorem bd_latch_rst_W2_R2_next : ∀ d0 d1 en rst q0 q1 : Bool,
    bd_latch_rst_W2_R2.next boolSem [d0, d1, en, rst] [q0, q1] =
      some [if rst then false else bmux en d0 q0, if rst then true else bmux en d1 q1] := by
  decide +kernel

theorem latch_inits_other :
    bd_latch_W1.initOf "odd.u" = some Formal.Cells.LinkHandshake.INIT_LAT ∧
    bd_latch_W2.initOf "pair[0].u" = some Formal.Cells.LinkHandshake.INIT_PAIR ∧
    bd_latch_W1.initOf "odd.u" = some Formal.Cells.Bundling.ODD ∧
    bd_latch_W2.initOf "pair[0].u" = some Formal.Cells.Bundling.PAIR ∧
    bd_latch_W1.initOf "odd.u" = some Formal.Core.Init.latch_odd.init.toNat ∧
    bd_latch_W2.initOf "pair[0].u" = some Formal.Core.Init.latch_pair.init.toNat ∧
    bd_latch_rst_W1.initOf "gbit[0].u" = some Formal.Core.Init.latch_rst0.init.toNat ∧
    bd_latch_rst_W2_R2.initOf "gbit[1].u" = some Formal.Core.Init.latch_rst1.init.toNat := by
  decide +kernel

/-! ## `bd_delay`, `bd_delay_gated` -/

theorem delay_luts :
    bd_delay_N0.cells.isEmpty ∧
    bd_delay_N3.lutIs "chain.g[0].u" (.lut 1) Formal.Cells.Bundling.BUF ["a"] ["chain.s[1]"] ∧
    bd_delay_N3.lutIs "chain.g[1].u" (.lut 1) Formal.Cells.Bundling.BUF ["chain.s[1]"] ["chain.s[2]"] ∧
    bd_delay_N3.lutIs "chain.g[2].u" (.lut 1) Formal.Cells.Bundling.BUF ["chain.s[2]"] ["z"] ∧
    bd_delay_N3_FF.lutIs "chain.g[0].u" (.lut 1) Formal.Cells.Bundling.BUF ["a"] ["chain.s[1]"] ∧
    bd_delay_N3_FF.lutIs "chain.g[1].u" (.lut 2) Formal.Cells.Bundling.FF_SIDE ["chain.s[1]", "a"] ["chain.s[2]"] ∧
    bd_delay_N3_FF.lutIs "chain.g[2].u" (.lut 2) Formal.Cells.Bundling.FF_SIDE ["chain.s[2]", "a"] ["z"] ∧
    bd_delay_N3_FR.lutIs "chain.g[1].u" (.lut 2) Formal.Cells.Bundling.FR_SIDE ["chain.s[1]", "a"] ["chain.s[2]"] ∧
    bd_delay_N3_FR.lutIs "chain.g[2].u" (.lut 2) Formal.Cells.Bundling.FR_SIDE ["chain.s[2]", "a"] ["z"] ∧
    bd_delay_gated_N3.lutIs "chain.g[1].u" (.lut 2) Formal.Cells.Bundling.FF_SIDE ["chain.s[1]", "gate"] ["chain.s[2]"] ∧
    bd_delay_gated_N3.lutIs "chain.g[2].u" (.lut 2) Formal.Cells.Bundling.FF_SIDE ["chain.s[2]", "gate"] ["z"] := by
  decide +kernel

theorem delay_inits_core :
    bd_delay_N3.initOf "chain.g[0].u" = some Formal.Core.Init.delay_buf.init.toNat ∧
    bd_delay_N3_FF.initOf "chain.g[1].u" = some Formal.Core.Init.delay_and.init.toNat ∧
    bd_delay_N3_FR.initOf "chain.g[1].u" = some Formal.Core.Init.delay_or.init.toNat := by
  decide +kernel

/-- In steady state every line passes its input, Kleene included (an X on `a`
is an X on `z`, never a definite value); the gated line passes `a . gate`. -/
theorem delay_outs : ∀ a g : K3,
    bd_delay_N0.outs kleeneSemP [a] [] = some [a] ∧
    bd_delay_N3.outs kleeneSemP [a] [] = some [a] ∧
    bd_delay_N3_FF.outs kleeneSemP [a] [] = some [a] ∧
    bd_delay_N3_FR.outs kleeneSemP [a] [] = some [a] ∧
    bd_delay_gated_N3.outs kleeneSemP [a, g] [] =
      some [lutK Formal.Cells.Bundling.FF_SIDE [lutK Formal.Cells.Bundling.FF_SIDE [a, g], g]] := by
  decide +kernel

theorem delay_gated_outs_B : ∀ a g : Bool,
    bd_delay_gated_N3.inputNames = ["a", "gate"] ∧
    bd_delay_gated_N3.outs boolSem [a, g] [] = some [a && g] := by decide +kernel

/-! ## `bd_datamux` (W = 3: a pair and the odd LUT3) -/

theorem bd_datamux_W3_lut :
    bd_datamux_W3.lutIs "pair[0].u" .lut6_2 Formal.Core.Init.datamux_pair.init.toNat
      ["s", "a[0]", "b[0]", "a[1]", "b[1]", "1"] ["z[0]", "z[1]"] ∧
    bd_datamux_W3.lutIs "odd.u" (.lut 3) Formal.Core.Init.datamux_odd.init.toNat
      ["s", "a[2]", "b[2]"] ["z[2]"] := by decide +kernel

theorem bd_datamux_W3_outs : ∀ a0 a1 a2 b0 b1 b2 s : Bool,
    bd_datamux_W3.inputNames = ["a[0]", "a[1]", "a[2]", "b[0]", "b[1]", "b[2]", "s"] ∧
    bd_datamux_W3.outs boolSem [a0, a1, a2, b0, b1, b2, s] [] =
      some [if s then b0 else a0, if s then b1 else a1, if s then b2 else a2] := by decide +kernel

/-- Kleene, the pair: each bit is `K3.mux s a b`, bits independent. -/
theorem bd_datamux_W3_pair_K : ∀ s a0 b0 a1 b1 : K3,
    let env := [("s", s), ("a[0]", a0), ("b[0]", b0), ("a[1]", a1), ("b[1]", b1)]
    bd_datamux_W3.gateN kleeneSemP "pair[0].u" .O5 env = some (K3.mux s a0 b0) ∧
    bd_datamux_W3.gateN kleeneSemP "pair[0].u" .O6 env = some (K3.mux s a1 b1) := by decide +kernel

end Formal.Gen.ProofsLatch
