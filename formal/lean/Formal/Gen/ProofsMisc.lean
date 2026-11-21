import Formal.Gen.Cells
import Formal.Cells.Latch

/-!
# 11d: generated endpoints, memory port and the two-phase links

`bd_end.v`, `bd_mem.v`, `bd_mlink.v` have NO shard-B transcription in the tree
today, so these netlists are checked against the equations in their RTL
headers (and, for `bd_mem`, the header's design rules), not against B.

`bd_mem` is PARTLY imported: its RAMB18E1 is an opaque cell (every pin and net
recorded, outputs `none`). What is proved is the LUT part (setup line, the one
explicit clock buffer, clock-to-out line) and the RAM's wiring; `rdata` is
provably NOT computable by the interpreter (`bd_mem_rdata_opaque`), so nothing
about it can be claimed by accident.

`bd_flink` uses FDRE (H_FF_MS, see `Netlist.lean`).
-/

namespace Formal.Gen.ProofsMisc
open Formal.Cells Formal.Gen Formal.Gen.Cells
open Formal.Cells.Latch (bmux ODD PAIR)

/-! ## `bd_src`, `bd_snk` -/

/-- `req = ~ack` (the keep LUT1), `data = VAL = 2'b10` as constant ties. -/
theorem bd_src_W2_spec : ∀ ack : Bool,
    bd_src_W2.inputNames = ["ack"] ∧ bd_src_W2.outputNames = ["req", "data[0]", "data[1]"] ∧
    bd_src_W2.lutIs "u" (.lut 1) 0x1 ["ack"] ["req"] ∧
    bd_src_W2.outs boolSem [ack] [] = some [!ack, false, true] := by decide +kernel

/-- `ack = req`, no cells, data unread. -/
theorem bd_snk_W2_spec : ∀ req d0 d1 : Bool,
    bd_snk_W2.cells.isEmpty ∧ bd_snk_W2.inputNames = ["req", "data[0]", "data[1]"] ∧
    bd_snk_W2.outs boolSem [req, d0, d1] [] = some [req] := by decide +kernel

/-! ## `bd_mem` (DSETUP = DCO = 2, USE_BUFG = 0; and USE_BUFG = 1) -/

theorem bd_mem_luts :
    bd_mem.cellNames = ["gplain.ubuf", "uco.chain.g[0].u", "uco.chain.g[1].u", "uram",
                        "usetup.chain.g[0].u", "usetup.chain.g[1].u"] ∧
    bd_mem.lutIs "usetup.chain.g[0].u" (.lut 1) 0x2 ["req"] ["usetup.chain.s[1]"] ∧
    bd_mem.lutIs "usetup.chain.g[1].u" (.lut 1) 0x2 ["usetup.chain.s[1]"] ["strobe"] ∧
    bd_mem.lutIs "gplain.ubuf" (.lut 1) 0x2 ["strobe"] ["ram_clk"] ∧
    bd_mem.lutIs "uco.chain.g[0].u" (.lut 1) 0x2 ["ram_clk"] ["uco.chain.s[1]"] ∧
    bd_mem.lutIs "uco.chain.g[1].u" (.lut 1) 0x2 ["uco.chain.s[1]"] ["ack"] := by decide +kernel

/-- The header's design rules, on the synthesized netlist: the RAM clock and
the acknowledge tap hang off ONE net, driven by exactly one explicit buffer
(the importer rejects multiply driven nets), and no pass inserted a BUFG. -/
theorem bd_mem_clock_rules :
    bd_mem.pinNet "uram" (.other "CLKARDCLK[0]") = some "ram_clk" ∧
    bd_mem.driverName "ram_clk" = some "gplain.ubuf" ∧
    bd_mem.pinNet "uco.chain.g[0].u" .I0 = some "ram_clk" ∧
    bd_mem.cells.all (fun c => match c.kind with | .buf _ => false | _ => true) ∧
    bd_mem_bufg.pinNet "uram" (.other "CLKARDCLK[0]") = some "ram_clk" ∧
    bd_mem_bufg.driverName "ram_clk" = some "gbufg.ubuf" ∧
    (bd_mem_bufg.cell? "gbufg.ubuf").map Cell.kind = some (.buf "BUFG") ∧
    bd_mem_bufg.pinNet "uco.chain.g[0].u" .I0 = some "ram_clk" := by decide +kernel

/-- The payload wiring: `a14 = {addr, 4'b0000}`, port A enabled, `WEA = {we, we}`,
port B unused. -/
theorem bd_mem_ram_pins :
    (List.range 4).all (fun i => bd_mem.pinNet "uram" (.other s!"ADDRARDADDR[{i}]") = some "0") ∧
    (List.range 10).all (fun i =>
      bd_mem.pinNet "uram" (.other s!"ADDRARDADDR[{i + 4}]") = some s!"addr[{i}]") ∧
    (List.range 16).all (fun i => bd_mem.pinNet "uram" (.other s!"DIADI[{i}]") = some s!"wdata[{i}]") ∧
    (List.range 16).all (fun i => bd_mem.pinNet "uram" (.other s!"DOADO[{i}]") = some s!"rdata[{i}]") ∧
    bd_mem.pinNet "uram" (.other "ENARDEN[0]") = some "1" ∧
    bd_mem.pinNet "uram" (.other "WEA[0]") = some "we" ∧
    bd_mem.pinNet "uram" (.other "WEA[1]") = some "we" ∧
    bd_mem.pinNet "uram" (.other "ENBWREN[0]") = some "0" ∧
    bd_mem.pinNet "uram" (.other "CLKBWRCLK[0]") = some "0" := by decide +kernel

/-- `ack`'s cone is `req` alone: evaluated with ONLY `req` bound, it is `req`
(steady state of the two lines and the buffer). -/
theorem bd_mem_ack : ∀ req : Bool,
    evalNet boolSem bd_mem [(bd_mem.netId "req", req)] bd_mem.fuel (bd_mem.netId "ack") = some req ∧
    evalNet boolSem bd_mem_bufg [(bd_mem_bufg.netId "req", req)] bd_mem_bufg.fuel
      (bd_mem_bufg.netId "ack") = some req := by decide +kernel

theorem lookup_zip_none {V : Type} : ∀ (ks : List Nat) (vs : List V) (n : Nat),
    n ∉ ks → (ks.zip vs).lookup n = none
  | [], _, _, _ => rfl
  | _ :: _, [], _, _ => rfl
  | k :: ks, v :: vs, n, h => by
    have hk : n ≠ k := fun e => h (e ▸ List.mem_cons_self ..)
    have hr : n ∉ ks := fun e => h (List.mem_cons_of_mem _ e)
    have hb : (n == k) = false := by simp [hk]
    simp [List.zip_cons_cons, List.lookup, hb, lookup_zip_none ks vs n hr]

/-- The RAM's data output is NOT modelled: for EVERY input, the interpreter
returns `none` (its driver is opaque). -/
theorem bd_mem_rdata_opaque (ins : List Bool) :
    bd_mem.outNamed boolSem "rdata[0]" ins [] = none := by
  have hout : bd_mem.outputs.lookup "rdata[0]" = some (.net (bd_mem.netId "rdata[0]")) := by
    decide +kernel
  have hni : bd_mem.netId "rdata[0]" ∉ bd_mem.inputs.map Prod.snd := by decide +kernel
  have hdrv : bd_mem.driver (bd_mem.netId "rdata[0]") = none := by decide +kernel
  have hfuel : bd_mem.fuel = 6 + 1 := by decide +kernel
  have henv : (bd_mem.env ins []).lookup (bd_mem.netId "rdata[0]") = none := by
    simp only [Netlist.env, List.zip_nil_right, List.append_nil]
    exact lookup_zip_none _ _ _ hni
  unfold Netlist.outNamed
  rw [hout]
  show evalSrc boolSem bd_mem (bd_mem.env ins []) bd_mem.fuel
    (some (.net (bd_mem.netId "rdata[0]"))) = none
  rw [hfuel]
  simp only [evalSrc, evalNet, henv, hdrv]

/-! ## `bd_mlink` (MOUSETRAP) -/

/-- `en = rst | ~(done ^ ack)` (ux, LUT3 F9), `done = latch(req_in, en)`. -/
theorem bd_mlink_ctl_spec : ∀ r ack rst done : Bool,
    bd_mlink_ctl.lutIs "ux" (.lut 3) 0xF9 ["done", "ack", "rst"] ["en"] ∧
    bd_mlink_ctl.lutIs "uq.odd.u" (.lut 6) ODD ["req_in", "en", "done", "0", "0", "0"] ["done"] ∧
    bd_mlink_ctl.next boolSem [r, ack, rst] [done] = some [bmux (rst || (done == ack)) r done] ∧
    bd_mlink_ctl.outs boolSem [r, ack, rst] [done] = some [done, rst || (done == ack)] := by
  decide +kernel

/-- NOPEN = 3: `en = s & (rst | ~(done ^ ack))` with `s` the FASTFALL line on
`en0`; in steady state the same function. -/
theorem bd_mlink_ctl_N3_spec : ∀ r ack rst done : Bool,
    bd_mlink_ctl_N3.lutIs "slow_reopen.uz" (.lut 4) 0xAA82 ["s", "done", "ack", "rst"] ["en"] ∧
    bd_mlink_ctl_N3.lutIs "ux" (.lut 3) 0xF9 ["done", "ack", "rst"] ["en0"] ∧
    bd_mlink_ctl_N3.next boolSem [r, ack, rst] [done] = some [bmux (rst || (done == ack)) r done] ∧
    bd_mlink_ctl_N3.outs boolSem [r, ack, rst] [done] = some [done, rst || (done == ack)] := by
  decide +kernel

theorem bd_mlink_W2_step : ∀ rst r d0 d1 ack done q0 q1 : Bool,
    let en := rst || (done == ack)
    bd_mlink_W2.stateNames = ["ack_in", "data_out[0]", "data_out[1]"] ∧
    bd_mlink_W2.next boolSem [rst, r, d0, d1, ack] [done, q0, q1] =
      some [bmux en r done, bmux en d0 q0, bmux en d1 q1] ∧
    bd_mlink_W2.outs boolSem [rst, r, d0, d1, ack] [done, q0, q1] = some [done, done, q0, q1] := by
  decide +kernel

/-! ## `bd_flink` (flip-flop data, H_FF_MS) -/

/-- `ck = ~rst & (done ^ ack)` (uck 06), `done = ck ? done : req_in` (uq E2). -/
theorem bd_flink_ctl_spec : ∀ r ack rst done : Bool,
    bd_flink_ctl.lutIs "uck" (.lut 3) 0x06 ["done", "ack", "rst"] ["ck"] ∧
    bd_flink_ctl.lutIs "uq" (.lut 3) 0xE2 ["req_in", "ck", "done"] ["done"] ∧
    bd_flink_ctl.next boolSem [r, ack, rst] [done] =
      some [if !rst && (done != ack) then done else r] ∧
    bd_flink_ctl.outs boolSem [r, ack, rst] [done] = some [done, !rst && (done != ack)] := by
  decide +kernel

/-- The bank is two FDRE clocked by `ck`, CE = 1, R = 0. One unit step, state
`[done, q0, q1, m0, m1]` (`m` = synthetic masters): the slave copies the
master while `ck` is high, the master tracks `D` while `ck` is low. -/
theorem bd_flink_W2_step : ∀ rst r d0 d1 ack done q0 q1 m0 m1 : Bool,
    let ck := !rst && (done != ack)
    bd_flink_W2.stateNames =
      ["ack_in", "data_out[0]", "data_out[1]", "data_out[0]$master", "data_out[1]$master"] ∧
    bd_flink_W2.next boolSem [rst, r, d0, d1, ack] [done, q0, q1, m0, m1] =
      some [if ck then done else r, if ck then m0 else q0, if ck then m1 else q1,
            if ck then m0 else d0, if ck then m1 else d1] := by
  decide +kernel

theorem bd_flink_W2_ffs :
    bd_flink_W2.lutIs "$auto$ff.cc:337:slice$2616" .fdre 2
      ["ck", "1", "data_in[0]", "0", "data_out[0]", "data_out[0]$master"]
      ["data_out[0]", "data_out[0]$master"] ∧
    bd_flink_W2.lutIs "$auto$ff.cc:337:slice$2617" .fdre 2
      ["ck", "1", "data_in[1]", "0", "data_out[1]", "data_out[1]$master"]
      ["data_out[1]", "data_out[1]$master"] := by decide +kernel

end Formal.Gen.ProofsMisc
