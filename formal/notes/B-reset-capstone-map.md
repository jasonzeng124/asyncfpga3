# B-reset-capstone-map: gNet regenerated from bdc's Verilog, and the C-channel map

Probe Bmap (shard B), 2026-10-29. Follows B-reset-capstone.md (probe Brz), whose headline
`gcd_hw_safe_after_reset` took the channel map `μ` and `MapOK μ` (H_MAP) as hypotheses,
and audit P5 / row 60 (the generator of `ResetGcdNet.lean` lived in a lost scratchpad).

No yosys, no route, no board. Nothing here is about a synthesized or routed netlist (that
is B-reset-gcd-net.md, probe Bnet). Everything is about the RTL that `ResetGcdNet.lean`
describes.

## Regenerate (the audit's command)

From the repository root (`-B`: no `.pyc` is written into `bdc/` or `formal/tools/`):

    python3 -B formal/tools-B/gcdnet_gen.py net OUT
    python3 -B formal/tools-B/gcdnet_gen.py map OUT formal/lean/Formal/Cells/ResetCapstoneMapData.lean

- `net` runs `bdc/emit.py cloud/fixtures/frontend/gcd/comp/handshake_transformed.mlir
  --no-top --probe n138` with every `BDC_*` / `BD_*` variable unset (default sizes). Kernel
  sha256 `65e61848b2506c3e92cb03cb6ca002295b46c5d7bcc45bf811a774b8db3db936`. It then
  elaborates `cells/hw/gcd_rig.v` (defaults CMPD 16, PRBD 2, WFILT 2, IDXW 4; no
  `GCD_RIG_CMP_PROBE`, `GCD_DUT_PARAMS` or `BD_LINK_DC`) over that kernel and
  `cells/rtl/*.v`, and writes `OUT/ResetGcdNet.lean`, `OUT/net.json` and `OUT/gcd.v`. Last,
  it compares the result with `formal/lean/Formal/Cells/ResetGcdNet.lean`.
- `map` reruns C's own generator `formal/lean/Wip/C8m/netgen.py` in-process, read-only, with
  its output redirected to `OUT/CapstoneNet.regen.lean`. It checks that output against the
  committed `CapstoneNet.lean`, then writes the table.
- Time: about 2 s for `net` and 5 s for `map`.

yosys and iverilog are not on PATH here, so `formal/tools-B/vsub.py` is a small Verilog
front end for the subset these files use. It handles:
- the preprocessor;
- ANSI modules and parameters;
- wires and assigns;
- named instances;
- generate if/else and for blocks.

It raises on anything else.

## (1) The network: ResetGcdNet.lean reproduced byte for byte

`net` prints `IDENTICAL (byte for byte)`, and `cmp` agrees, for the whole 365,996-byte
file:
- 3322 nodes: 1 rst, 64 data inputs and 3257 control LUT outputs;
- every INIT, pin list, rank and reset value;
- the Braun tree;
- every comment name.

The 17 reset-1 nodes equal `onesL`, and the maximum rank is 21.

The definition is now exact, and stated in the generator's header:
- **Control LUT.** Every LUT is control except those in `bd_latch` or `bd_datamux` and the
  `uz_*` LUT1s.
- **LUT6_2.** Gives two nodes, O5 and O6.
- **The muxn3 `|j`.** A reduction OR of control nets that a control pin reads becomes an
  inferred gate (H_INFER_OR3). On gcd_hw this is only the muxn3 `|j`.
- **Pins.** A control pin reads one of:
  - its driver node, through every pure alias;
  - k0 or k1;
  - a free data input.
- **Data inputs.** They are keyed by the net that the pin reaches through port connections
  only. This is why the fork copies `n5__0/1/2_data` are three data inputs.

Some things are conventions, not semantics. I recovered them by comparing with the
committed file:
- **Order.** Kernel LUTs appear in elaboration order. A LUT6_2 lists O6 first when O6 feeds
  back to its own pins: the arbiter's q.
- **Inferred gate.** It is placed just before its first reader.
- **Data inputs.** They are numbered by first read.
- **The rig.** It is ordered by function:
  1. the ring;
  2. the probe delays;
  3. the samplers;
  4. each sampler's `_w` and `_a`.
- **Comment names.** Some generate labels are dropped. `chunk[i]` is written `chunkI`. A
  C-element's LUT `u` is dropped, except for the rig's `uenv0/1`.

The header prose is a fixed template inside the generator, so it is not evidence.

**Negative control.** In `cells/rtl/bd_ce.v` I swapped I0 and I1 of `bd_c2n_set`, in memory
only. The comparison then fails at exactly one line: node 3275, `urig.uenv1`. An INIT that
has no name is refused.

## (2) The table, and H_MAP as a theorem

**Data (`ResetCapstoneMapData.lean`, generated).** For each of C's 465 channels, in C's
order, it gives the gNet node of the request wire (`reqL`) and of the acknowledge wire
(`ackL`). Each row also lists the RTL nets that were read. The channel naming rules are in
the header of `capmap.py`:

| C channel | RTL nets read |
|---|---|
| `gR.k` | bdc's `vname` nets `_u_*` and plain, and `ulink_*.many.{r,a}[i]` inside a bd_pipe; the SSA alias chain and zero-delay comps are followed |
| `jL` | `ucond_brN_req/_ack` |
| `zR`, `accR` | the amerge's `z_*` and `acc1_*` |

Every row resolves to a gate node. When two nets stand for one C channel, they must resolve
to the same node, and the generator checks this.

**`ResetCapstoneMap.lean`.** It checks OK with
`/tmp/claude-0/btools/bcheck.py Formal/Cells/ResetCapstoneMap.lean`, in about 100 s. It
imports the data file and `ResetCapstone`. It contains:
- `names_ok`: `mapNames = chanNames`, by kernel decide. The rows are C's channels.
- `μT_ok : MapOK μT`. This is **H_MAP proved**, by kernel decide over 465 rows.
- `gcd_hw_safe_after_reset_map`: Brz's headline with `μ := μT` and H_MAP discharged.
  H_MAP_T0 is now stated over `reqL` and `ackL`.
- `reset_capstone_map_nonvac`: all the remaining hypotheses hold jointly, with `wRun`
  (D = 40, W = 1, E = 967) and `frzC chW`. The conclusion is vacuous on that frozen family.
- `hot_rows`: the first 8 rows. All 7 hot requests are `urig.uenv1`, node 3275.

### MapOK is too weak, so there is `WireOK`

`μW`, a map that reads everything cold from node 65, also meets `MapOK`. `WireOK μ` is
`MapOK μ` together with "μ is injective on wires", except where the RTL makes two C wires
one net of one driver. Each exception is tied to a C operator in C's own `ops` list:
- fork output requests are the fork's input request (`{N{req}}`);
- join and bjoin input acknowledges are the output acknowledge (`{N{ack}}`);
- a kernel `bd_snk` has acknowledge = request (this excludes the rig's sinks for channel 3
  and `out0`);
- mux and muxn select acknowledges are the output acknowledge (`ctl_ack = z_ack`);
- for a link with both delays 0, the input acknowledge and the output request are the same
  C-element;
- the three sources' requests are one node (the rig's fork), and it drives no other wire.

`copyOK` checks that each exception's identity holds. The remaining 657 "driven" wire nodes
must be duplicate-free. Results:
- `μT_wire : WireOK μT`;
- `μW_not_wire : MapOK μW ∧ ¬ WireOK μW`.

Literal injectivity on all wires is **false** for the real RTL, because forks, joins and
sinks are pure wiring. That is why the exceptions are listed, not waived.

`#print axioms`, run in a scratch file that was then deleted:
- `names_ok` and `hot_rows` depend on no axioms;
- `μT_ok` depends on propext and Quot.sound;
- `μT_wire`, `μW_not_wire`, `gcd_hw_safe_after_reset_map` and `reset_capstone_map_nonvac`
  depend on propext, Classical.choice and Quot.sound.

`formal/scan.py` passes on both files.

## Not covered

- **Correctness of the identification.** That row `c` is really the RTL driver of C's wire
  `c` is the generator's claim, read from bdc's net names. It is not a Lean theorem. Lean
  checks the table's alignment with C's names, `MapOK` and `WireOK`. The node table of gNet
  is mechanised only up to the generator's byte-identical output.
- **H_MAP_T0.** C's wires at `T0` are taken to be the values of the driving nodes. This is
  still a hypothesis.
- **Unchanged and open:** H_CELLS_AFTER (C's O4), H_START_AFTER, liveness, and the bd_src
  frontier.
- **No reader certificate.** `WireOK` does not say which gate pin reads each wire. A fork's
  input request has no reader pin of its own: it is read only through its copies.
- **`Formal.lean`.** The lead must add `ResetCapstoneMapData` and `ResetCapstoneMap` to it.
