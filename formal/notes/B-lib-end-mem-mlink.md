# B probe Lib2: cell-library proofs, part 2 (`bd_end`, `bd_mem`, `bd_mlink`, rest of `bd_link`/`bd_latch`)

File: `formal/lean/Formal/Cells/LibEndMemMlink.lean`. It is core Lean, about 770 lines, and imports only
`Formal.Cells.Prelim`. Prelim is unchanged. All helpers are local to namespace
`Formal.Cells.LibEndMemMlink`. They include a local `Decidable (∀ k : K3, P k)` instance named
`k3DecForall`, so it does not clash with CElemFn's.

Check (clean, about 25 s wall, no warnings):

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/LibEndMemMlink.lean

The file contains no `sorry`, `admit`, `axiom` or `native_decide`. The only grep hit is
Prelim's `K3.admits`. I ran `#print axioms` on a scratch copy against `singleX_any`,
`singleX_all`, `db_eq`, `rep_uz_K`, `uz_open_iff`, `mlink_x_stuck`, `db_restore`,
`mlink_req_bit_H`, `flink_req_bit_H`, `mlink_runt_reach`, `mlink_cycle`, `gated_settled`,
`MemPort.rtz_serialised`, `MemPort.hold_ok` and `uz_singleX_dec`. The result is
`[propext]` or `[propext, Quot.sound]` only. Most of the 25 s goes to the 729-vector
Kleene `decide`s in Sections 1 and 2.

## Scope: LUT instances and the parameter values in use

| cell | instance | INIT | pins | used where |
|---|---|---|---|---|
| `bd_src` | `u` | `2'h1` | `[ack]` | emitted by `bdc/emit.py` (`VAL = 0`) |
| `bd_snk` | (none) | | `ack = req` wire | emitted by `bdc/emit.py` |
| `bd_mem` | `gplain.ubuf` | `2'h2` | `[strobe]` | `bdc/mem.py`, always `USE_BUFG(0)` |
| `bd_mem` | `usetup`, `uco` | `2'h2`/hop | symmetric `bd_delay` | `DSETUP_i`, `DCO_i` sized post-route |
| `bd_mlink_ctl` | `ux` | `8'hF9` | `[done, ack, rst]` | library only (not emitted by bdc) |
| `bd_mlink_ctl` | `uz` (NOPEN>1) | `16'hAA82` | `[s, done, ack, rst]` | library only, default NOPEN = 1 |
| `bd_mlink_ctl` | `uq` = `bd_latch W=1` | `B8B8..` | `[req_in, en, done, 0,0,0]` | library only |
| `bd_flink_ctl` | `uck` | `8'h06` | `[done, ack, rst]` | library only |
| `bd_flink_ctl` | `uq` | `8'hE2` | `[req_in, ck, done]` (self-loop) | library only |
| `bd_link_dctl` | `ub` `ua` `uld` `ult` | `F320`, `FA80`, `0F08`, `0101..` (64-bit) | see file | `-DBD_LINK_DC` only; LDN 0 and >0, BROAD 0/1 |
| `bd_delay_gated` | `g0`, `g[i>=1]` | `2'h2`, `4'h8` | `[s_i]`, `[s_i, gate]` | `bdc/compute.py` |

Not repeated, because other files already cover them:
- `bd_link_dctl` binary equations with `rst = 0, s = 1` (`LinkHandshake.dctl_eqs`) and its
  interleaving check (`dctl_ok0/1`, `dctl_si_hazard`).
- `bd_latch` (`Latch.lean`).
- The 4'h8 side stage as a timed fast line (`Bundling.fastfall_line`, `fast_edge`, `slow_not_early`).
- `bd_c2n` (`CElemFn`).

## Theorems (all proved)

### Section 0: single-X glitch freedom is automatic (a methodological finding)
- `singleX_any init v i`: for every INIT, every binary vector of any length and every pin `i`,
  `lutK` with X on pin `i` equals `join` of the two Boolean values with pin `i` at 0 and at 1.
- `singleX_all init`: CElemFn's `SingleX` property (6 pins, endpoints `v` and `v` with pin `i`
  flipped) holds for every INIT.
- `lutK_ofBool`: Kleene equals binary on definite inputs.

Consequence: under Prelim's closure semantics, a per-cell single-X check can never fail, so it
says nothing about the cell. That includes CElemFn's eight `*_singleX` theorems. All of the
glitch-freedom content sits in H_KLEENE_LUT itself, and MuxTree.lean reduces that to the
per-mux 2:1 hypothesis. The per-cell theorems the task asks for (`*_singleX`, Section 3) are
instances of `singleX_all`. `uz_singleX_dec` keeps one independent enumeration as a
cross-check. A cell-specific glitch question only arises with two or more X pins, or with
pin-order and timing effects. Those are the feedback results in Sections 4 and 5.

### Section 1: physical 6-input form (H_REPLICATED_INIT)
`rep_*` (binary) and `rep_*_K` (Kleene, all 3^6 inputs) cover every small LUT: inverter,
buffer, AND2, `ux`, `uz`, `uck`, `fq`. The replicated 64-bit INIT computes the small function
whatever the unused pins carry, X included. Either toolchain realisation (replicate the INIT,
or tie the unused pins to a constant) therefore gives the small function.
`db_i5_K`, `da_i5_K`, `dld_i5_K` and `dlt_tied_K` prove the same for `bd_link_dctl`'s tied
pins (`I5`, and `I3..I5` of `ult`).

### Section 2: binary function = header equation (task item 1)
`inv_eq`, `buf_eq`, `ux_eq`, `uz_eq`, `lat_eq`, `uck_eq`, `fq_eq`, `and_eq`; plus the
`bd_link_dctl` equations below.
- `db_eq`, `da_eq`, `dld_eq` (all 6 pins, rst and `s` included) and `dlt_eq`.
- `dctl_sr_disjoint`: set and reset are never both asserted.
- `mt_en_reopen_from_en0`: `uz = s & ux`.
- `uck_not_ux`: outside reset the flink clock is the complement of the mlink enable.

**No INIT/header mismatch was found.** Every INIT equals its header comment and the
`cells/verify/inits.py` spec (`MT_EN`, `MT_EN_REOPEN`, `MT_CK`, `MT_REQ_LATCH`, `INV`, `BUF`).

### Section 3: single-X per pin (task item 2)
`inv_/buf_/ux_/uz_/lat_/uck_/fq_/and_/db_/da_/dld_/dlt_singleX` are instances of
`singleX_all`. `uz_singleX_dec` is the enumerated cross-check.

### Section 4: Kleene and feedback structure (task item 3)

**`bd_src` closed on a mirror** (`bd_snk`):
- `src_no_fixed`: there is no binary fixed point. The loop is an oscillator, not storage, as the
  header says.
- `src_fixed_K`: the only Kleene fixed point is `x`.
- `src_K`: the cell is `K3.not`.

**`bd_flink.uq`** (self-loop latch):
- `fq_K`: the cell is exactly `K3.mux ck req done`.
- `fq_fixed_iff`: it is stable iff `ck = 1` or `Q = D`.
- `fq_restore`: an X on the feedback pin is restored iff `ck = 0` and `req` is definite. While
  opaque, the X is held.
- `fq_close_clean`: the closing edge with `D = Q` is clean (consensus term).

**`ux`, `uck`, `uz`:**
- Reset forcing: `ux_K_rst`, `uck_K_rst`.
- `ux_x_done`, `uck_x_done`: XOR/XNOR is fully sensitive, so an X on `done` gives X.
- `ux_xrst`: an X reset is harmless when the XNOR already says "open".
- `uz_close_any_s`: the close does not wait for the slow reopen line, even with `s = X`.
- `uz_s_low`: `s` low holds the stage closed.
- `uz_open_iff`: `en = 1` iff `s = 1` and (`rst` or `done = ack`).

**`bd_mlink` composite loop** (`done -> uq.I2` and `done -> ux -> en -> uq.I1`):
- `mlinkF_eq`: if (`rst` or `done == ack`) then `req`, else `done`.
- `mlinkF_fixed_iff`: stable iff the stage is full or `req = done`.
- `mlinkF_idem`: the settled map is idempotent, so the loop has no oscillation.
- `mlink_x_stuck`: **an X on `done` is a fixed point of the settled Kleene loop for every
  `req` and `ack` when `rst = 0`.**
- `mlink_x_rst`: only reset restores it. So the untimed model cannot show that an empty stage
  captures cleanly. That takes the ordering in Section 5.

**`bd_link_dctl`:**
- `db_restore`, `da_restore`, `dld_restore`: X on a state bit's own feedback pin is restored
  iff `rst`, its set term or its reset term is asserted.
- `db_hold`, `da_hold`, `dld_hold`: with neither set nor reset asserted, the bit holds (binary).
- `dctl_rst_K`: `rst = 1` clears all three state bits even with X on every other pin.
- `dld_s_low_blocks`: with LDN > 0, `s` low blocks the `ld` set even when `lt` is X. This is the
  header's "an lt pulse too short to set ld is simply lost".

### Section 5: the MOUSETRAP request bit and which feedback path must win (new finding)

**Model.** One stage, one token, using the real INITs: `bd_mlink_ctl` with `uq` = `B8B8..` and
`ux` with `rst = 0`, and `bd_flink_ctl` with `uq` = `E2` and `uck`. The two wires out of
`done` are separate state bits:
- `qp` is the latch's own feedback pin.
- `dn` is the enable LUT's pin.

Every interleaving is explored. The reachable sets were computed by a BFS run outside the file
and are re-checked in the file by `decide` (`closedB`), so a wrong mask can only make the check
fail.

**H_QFB_FIRST.** The enable LUT does not move while `qp ≠ done`. Physically, the max of
`done -> uq.I2` is less than the min of `done -> ux.I0` + the `ux` arc + `en -> uq.I1`.

**Results:**
- `mlink_req_bit_H v`, `flink_req_bit_H v` (both polarities, under H_QFB_FIRST). In every
  reachable state:
  - (a) There is no runt: once `done` (= `ack_in`) has toggled it never toggles back.
  - (b) Every step lowers a potential, so a run takes at most 4 steps.
  - (c) The only state with nothing enabled is the intended final state, where the stage is
    closed on the new token (`fin_closed`).
- `mlink_runt`, `mlink_runt_reach`, `flink_runt`, `flink_runt_reach` (without H). The trace
  `L D E L` makes `done` toggle and toggle back. The enable LUT sees the new `done` and closes
  before the latch's own pin has it, so the latch re-latches the old value. The result is a
  runt on `ack_in`, and on `req_out` after its delay line.
- `mlink_cycle`, `flink_cycle`: the trace `L D E` repeats from the start state, so an unbounded
  runt train (an oscillation) is allowed.
- `masks_fail_without_H` (negative control): the masks that pass under H are not closed without
  it, so the check is able to fail.

**Finding on the header.** The `bd_mlink.v` header gives two arguments that the evidence does
not support:
- Its setup argument for the request bit is "its own D is the toggle that made done toggle, so
  it is stable by construction". That covers D, but not the latch's own feedback loop.
  H_QFB_FIRST is proved both needed and sufficient in this model, and it is a separate
  condition. The `bd_flink` comment does describe this exact failure: a seed was rejected
  because the `uq` feedback took 434 ps and `ck` closed in 424.
- The header says both timing assumptions are "checked on the route (mtrap: hold)". **No
  `mtrap` check exists anywhere in this checkout.** `grep -rn mtrap` finds only the header.
  `tighten.py`'s `loop_wire` is applied only to `bd_link_dc` latches (`input_lead`), and no
  rule names `bd_mlink` or `bd_flink`. Either the audit lives outside the tree or it is
  missing. The cells are standalone and not emitted by `bdc`, so this does not affect the
  shipped flow.

### Section 6: `bd_delay_gated`
- `buf_K`, `and_tap_low`, `and_tap_high`, `and_tap_x_chain_low`: stage facts.
- `gatedK` is the settled line, for any N.
- `gated_settled`: with `a = gate`, the output is `a` (for all of f, t and x).
- `gated_gate_low` and `gated_dip_flushes`: a low `gate` forces `z` low whatever `a` is. This
  is the header's warning that if `gate` dips while `a` stays high, the line flushes and
  re-ripples.

The timed behaviour is Bundling.lean's FASTFALL theorems with the tap net renamed. Its H_FLUSH
condition then concerns `gate`'s low phase, plus **H_GATE_LEADS**: `a` is a buffered copy of
`gate` (gate falls, then `a`; gate rises, then `a`). I did not re-prove it in the timed model.

### Section 7: `bd_mem`
LUT facts: `buf_eq`, `buf_K`, `rep_buf`. The RAMB18E1 is not modelled as a gate. It enters
only through the datasheet parameters `tSU`, `tHD` and `tCO` in the structure `MemPort`, whose
named hypotheses are:

- **H_SETUP_LINE**: bounds on `req -> usetup -> ubuf -> CLKARDCLK` for both edges, including
  the next access's rise. It includes **H_NO_INFERRED_BUF**: `ram_clk` has exactly one driver,
  the `ubuf` LUT. Test: netlist or FASM inspection, and the routed SDF.
- **H_CO_LINE**: lower bounds on `ram_clk -> uco -> ack`, measured from the same net that clocks
  the RAM.
- **H_FOUR_PHASE_ENV**: the requester has the payload settled by req rise, drops req only after
  ack rose, and holds the payload and the next req until ack fell.

Theorems:
- `setup_ok` (`tSU ≤ dsLo`): the payload is settled `tSU` before `CLKARDCLK` rises.
- `hold_ok` (`tHD ≤ dcLo + dsLoF + dcLoF`): hold is met by the protocol round trip.
- `rdata_before_ack` (`tCO ≤ dcLo`): read data is valid before ack rises.
- `clk_high_width`: the clock high time is at least `dsLo + dcLo + dsLoF − dsHi`.
- `rtz_serialised`: the next clock rise is at least `dcLoF + dsLo` after this clock fall.
  "Pipelined return-to-zero overlap" is therefore excluded by H_FOUR_PHASE_ENV alone, which
  matches the header's "sequencing, not timing".

Not included: **H_RDATA_ROUTE**, the skew between the consumer's `rdata` route and its `ack`
route. That has to be added to `tCO` before comparing with `dcLo`.

## What did not work / not done
- Nothing claimed is unproved.
- The first attempt at `singleX_any` closed the case split with `rfl`, which failed because
  `lutB` sat inside a `List.map`. Fixed with `simp only [List.map_cons]`.
- Not done:
  - A timed (trace-level) version of Section 5, where H_QFB_FIRST becomes a delay inequality on
    pin windows in Bundling.lean's `Gate` model. The interleaving result is the discrete
    version. Estimate: half a day.
  - The data bits of the bank under the same race. Each data bit is the same lemma with
    `req_in` replaced by a D that H_SETUP keeps stable. I did not instantiate it separately.
  - NOPEN > 1 in the race model: `uz` and the FASTFALL reopen line are characterised only
    statically, in Section 4.
  - Timed `bd_delay_gated` (H_GATE_LEADS).
  - The BUFG branch of `bd_mem` (unused by bdc).
  - Analog resolution of a held X. The Kleene results show it is never resolved logically.

## Verdict
**Works.** Every LUT in scope is proved equal to its header equation from the real INIT, with
no mismatch found, and its Kleene and feedback structure is characterised.

Three results go beyond the checklist:
1. Single-X glitch freedom is a theorem about the LUT semantics, true of every INIT. Per-cell
   single-X checks carry no information, and future probes should not spend effort on them.
2. The MOUSETRAP request bit (mlink and flink) needs a feedback-ordering hypothesis that its
   header does not state. It is proved both needed (runt and oscillation traces) and sufficient.
   The route audit the header cites (`mtrap`) is not in the tree.
3. `bd_mem`'s RTZ-overlap freedom follows from the four-phase protocol alone, and setup, hold
   and clock-to-ack reduce to three named inequalities on the two delay lines.

Effort to finish the open items: about one day (timed Section 5 and timed `bd_delay_gated`).
What it buys the project:
- A machine check of every remaining library INIT.
- A concrete audit rule to add to `tighten.py` for the mlink/flink request bit
  (`loop_wire(uq)` < the enable path), if those cells are ever integrated.
- The BRAM boundary obligations as checkable inequalities.

## Fidelity per primitive
- **LUT (binary):** exact. This is the steady-state function of the real INIT with I0 as the
  LSB.
- **LUT (Kleene):** relies on H_KLEENE_LUT, Prelim's closure semantics. MuxTree.lean shows it
  equals the per-mux reading for any read-once tree order. Single-X results follow from the
  semantics alone (Section 0).
- **Small LUTs on a 6-LUT BEL:** H_REPLICATED_INIT, proved harmless for both realisations.
- **Feedback wires:** in Sections 4 and 7 they are settled (untimed fixed points). In Section 5
  they are separate state bits with arbitrary relative delay (interleaving), restricted only by
  the named H_QFB_FIRST. No delay values are used.
- **RAMB18E1:** not modelled as a gate. It appears only as datasheet setup, hold and
  clock-to-out parameters in `MemPort`, a black box. BUFG is not modelled.
- **Delay lines:** taken as bound hypotheses (H_SETUP_LINE, H_CO_LINE) whose justification is
  Bundling.lean's `sym_edge`. They are not re-derived here.
