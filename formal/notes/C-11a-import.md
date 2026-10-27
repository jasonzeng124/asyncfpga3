# C-11a: netlist import from yosys JSON

## Verdict: works

One command synthesizes eleven library cells with the project's own yosys flow, imports the
`write_json` output into Lean, and fails loudly on drift. A generic interpreter, kernel-checked by
`decide`, proves that every imported netlist's next-state function equals shard B's cell
specification. It is also equal to B's own hand-transcribed cell function, so B's theorems carry over
to the synthesized cells. All of this works for single cells. Whole designs need more primitives in
the importer (see Effort).

## Producer (fidelity of the input)

- **yosys:** `Yosys 0.62 (git sha1 7326bb7d6)`, at `$TC/openxc7/bin/yosys`. This is the project's
  toolchain, restored from cache. It first failed to start with `libtcl8.6.so: not found`. I fixed
  that with `apt-get install libtcl8.6`; the binary itself was not changed. I did not use
  yowasp or apt's yosys.
- **Flow:** exactly the one in `cells/flow.sh` and `cells/verify/lutcost.py`:
  `read_verilog -lib -specify cells_sim.v; read_verilog rtl/*.v; [chparam]; synth_xilinx -family xc7
  -flatten -nosrl -nolutram -nobram -noclkbuf -top T; write_json`. Each cell is the top module.
  `bd_latch` is built with W=2 and W=3, and `bd_latch_rst` with W=1, via `chparam`.
- **INITs survive.** All INITs come through bit-exact, `(* keep *)` included. The importer records
  the keep flag. The arbiter's `ugrant` has no keep, and it also survives intact as LUT6_2
  0x0C0C0C0CA0A0A0A0.
- **IBUF/OBUF.** Because each cell is a top module, `synth_xilinx` inserts IBUF/OBUF pads. They are
  modelled as identity (H_PAD_IDENTITY). Inside a real design they do not exist.
- **`$scopeinfo`.** These cells (hierarchy bookkeeping, no connections) are skipped. Any other
  unknown cell type is an import error.

## Files

- `formal/tools/import/import.sh`: the one command.
  - `import.sh` re-synthesizes and writes `json/*.json` and `Formal/Net/Import/Cells.lean`.
  - `import.sh --check` re-synthesizes into a temp dir and diffs. It exits 1 and prints `DRIFT` on
    any difference.
  - `import.sh --check-json` regenerates from the committed JSON only, with no yosys needed.
  - It exits 2 if yosys is missing.
- `formal/tools/import/yosys2lean.py`: the generator. Its output is deterministic: no timestamps,
  and `src` paths reduced to basenames.
  - It fails (exit 1) on any of: an unknown cell type, an x/z constant, a multiply driven net, an
    undriven net that is read, a pin set that does not match the primitive, or an INIT that is not
    2^k binary digits.
  - It cuts feedback nets as the targets of DFS back edges, visited in deterministic order.
- `formal/tools/import/json/*.json`: the yosys output that was imported (11 cells).
- `formal/lean/Formal/Net/Import/Netlist.lean` (hand-written):
  - types `Pin`, `Src`, `Kind`, `Cell` (name, kind, INIT : Nat, keep, pin -> net map) and
    `Netlist` (ports, state nets, net names, cells);
  - `Sem V` with `boolSem` (`Formal.Cells.lutB`) and `kleeneSem` (`lutK`);
  - the evaluators `evalNet`, `Netlist.next` (one step, feedback nets as state), `Netlist.outs`
    and `Netlist.run`;
  - everything returns `Option`, so a `= some _` theorem also certifies that the netlist is well
    formed.
- `formal/lean/Formal/Net/Import/Cells.lean`: GENERATED, one `Netlist` per cell.
- `formal/lean/Formal/Net/Import/Proofs.lean`: the theorems.

## Theorems (all `decide +kernel`, no sorry/axiom/native_decide)

Namespace `Formal.Net.Import.Proofs`.

**Interface.** These pin the generated port and state order, so a reordering fails here first:
- `bd_c2_iface`, `bd_c3_iface`, `bd_c4_iface`, `bd_latch_W3_iface`, `bd_arbiter_iface`.

**C-elements:**
- **Headline:** `bd_c2_next_spec`: `next = some [clr rst (cSpec [a,b] q)]`. This is shard B's
  `c2_spec` statement, made about the synthesized netlist.
- `bd_c2_next_maj`: with rst = 0, the next state is maj(a,b,q).
- `bd_c2_outs`: the output port shows the state.
- `bd_c2_next_B`: equals B's `c2B`. `bd_c2_next_K`: equals B's `c2K`, for all K3 inputs.
- `bd_c2_set`, `bd_c2n`, `bd_c2n_set`: each has a `_next_spec` (binary) and a `_next_K` (equals
  B's Kleene function).
- `bd_c3_next_spec`, `bd_c4_next_spec`: binary.

**Latches:**
- `bd_latch_W3_next_spec`: every bit is `bmux en d q`. W=3 covers both the LUT6_2 pair and the
  odd LUT6.
- `bd_latch_W2_next_K`: each bit is `K3.mux en q d`, so X never crosses between the two bits of a
  pair.
- `bd_latch_rst_W1_next_spec`.

**Arbiter:**
- `bd_arbcell_next_K`, `bd_arbcell_outs_K`.
- `bd_arbiter_next_spec`, `bd_arbiter_outs_spec`: binary, against the equations in the `bd_arb.v`
  header, with the three loops q, A1, A2.
- `bd_arbiter_next_K`, `bd_arbiter_outs_K`: all 3^7 Kleene inputs, equal to B's `cK`/`g1K`/`g2K`/
  `qArbK`/`r0K`.

**Transfer:** `arbiter_kleene_exclusion` states that the imported arbiter's grant ports are never
both a definite 1. It is B's `kleene_exclusion`, carried over by rewriting with
`bd_arbiter_outs_K`.

**Audit.** I ran `Lean.collectAxioms` over all 290 `Formal.Net.Import.*` constants. Only
propext/Quot.sound/Classical.choice appear. `formal/scan.py` passes.

**Negative control.** I flipped INIT bit 7 of `bd_c2` (a=b=q=1, rst=0) in a copy of the JSON and
regenerated. `bd_c2_next_spec` then fails: "decide proved that the proposition ... is false". The
drift check also fires on any change; I saw it fire when the generator's net-naming changed.

## Run

```
formal/tools/import/import.sh --check        # drift check (needs yosys); --check-json without
cd formal/lean && export PATH=$HOME/.elan/bin:$PATH
# Formal.Cells.{CElemFn,Latch,ArbKleene} oleans must exist (shard B); then
for f in Netlist Cells; do ../slot.sh lean -o .lake/build/lib/lean/Formal/Net/Import/$f.olean Formal/Net/Import/$f.lean; done
../slot.sh lean Formal/Net/Import/Proofs.lean     # ~75 s user, ~2 GB
```

When I ran this, `.lake/build` did not have B's Latch/ArbKleene oleans. I built them into a private
LEAN_PATH (scratchpad) and checked there. A `lake build` that includes `Formal.Net.Import.Proofs`
builds them anyway.

Lead:
- add `import Formal.Net.Import.Proofs` to the root `Formal.lean`;
- optionally run `formal/tools/import/import.sh --check` from `check.sh`.

## What does not work / notes

- **Plain `decide` timed out** (200000 heartbeats) on `bd_arbiter_next_K` (2187 cases). The
  elaborator's Meta-level evaluation is what times out. `decide +kernel` evaluates only in the
  kernel. It adds no axiom, and it is not `native_decide`. I used it everywhere; the whole file
  takes about 75 s.
- **Kleene for `bd_c3`/`bd_c4`** (3^5 and 3^6 cases) was not attempted. It is probably feasible
  with `+kernel`, but it was not needed for the goal.
- **The state cut is a modelling choice.** The importer picks the feedback nets. For every library
  cell they are exactly the LUT outputs that are routed back to their own LUT, and the `*_iface`
  theorems pin which nets they are. Physically every net has a delay, and the unit-step `next` says
  nothing about races between nets. That is the job of the trace and delay tracks (2/3/5b). The
  natural next step is `Netlist.run` lifted to `Formal/Net/Prelim` traces with one bounded-delay
  channel per cell output.
- **Cells only.** Imported in isolation, a cell's non-keep LUTs could still be merged by yosys with
  their neighbours in a flattened design. The import says nothing about the cell in context. The
  same importer runs on `flow.sh`'s `soak.json`, but that file contains FDRE, CARRY4, MUXF7/8,
  BUFG, DSP48 and others, and today the importer rejects them loudly.

## What the JSON loses, and how 11b covers it

The yosys JSON is post-synthesis and pre-place-and-route. It loses:

1. **Placement.** It does not record the site, the BEL (A-D LUT, O5/O6 pair), or the relative
   placement that `hw/rloc_stamp.py` adds later.
2. **Routing.** It has none of the pips, wires, R/C or delays, including the feedback wire `O6 ->
   A?` of every C-element and latch. Its delay is real: 295 ps on the patched nextpnr (see
   `patches/README.md`, lut-perm-sink).
3. **LUT pin permutation (the INIT changes).** nextpnr-xilinx's router enters a LUT on any physical
   pin through `PIP_LUT_PERMUTATION` pseudo-pips and rewrites INIT to match. `cells/docs/TOOLING.md`
   says the same: "Do not try to match FASM INITs".
   - Measured on 11b's fixture: `formal/tools/fasm2lean/fixture/ce_pair_s1.fasm` has BLUT INIT
     `0x3220322032203220` for the logical `bd_c2` (`0x00E800E800E800E8`), and ALUT
     `0x0A0F000A0A0F000A` for `bd_c2n` (`0x00B2...`).
   - A brute-force search (Python, in this probe) finds exactly 12 pin permutations that map the c2
     INIT to the FASM one, and 4 for c2n. The extra matches come from the a/b symmetry and the tied
     pins.
   - So "some permutation matches" is too weak a check: it does not pin which net is on which
     pin. And "the INIT bits are equal" is simply false.
4. **How constants are tied.** In the JSON, `I4=I5=0` and the LUT6_2's `I5=1`. Physically this is
   a VCC/GND route or an INIT rewrite. B proved the tied pins are don't-cares (`*_tied_dontcare`),
   so binary and Kleene semantics do not depend on it. The A6 = VCC requirement of a fractured
   LUT6_2 is a fabric fact that the JSON states only as `I5 = 1'b1`.
5. **Which nextpnr produced the cell** (patch set and fingerprint). This is a CLAUDE.md requirement
   and must be recorded by 11b.

**Proposal for 11b.** Emit the SAME `Formal.Net.Import.Netlist` type from FASM plus the routed
netlist:
- each LUT gets its physical INIT from FASM;
- its conn is the physical A1..A6 pins, mapped to the nets the routing actually lands there. For
  in-site permutation pips, read the `CLB*.?LUT.A?` -> site-wire pips from FASM. For intertile
  pips, use prjxray-db.

Then prove by `decide +kernel`, with no hand reasoning, that the physical netlist and the JSON
netlist have the same next-state and output functions, up to the bijection between net names (or
directly against B's spec). That is the right statement under pin permutation: function equality,
not INIT equality. The routing half of 11b then attaches a delay interval to each net (fast/slow
min/max from prjxray timing). That gives the bounded-delay channels, which plug into the trace
semantics instead of the unit step used here.

## Effort to finish

- Lift `run` to bounded-delay traces: about 1 day.
- Add FDRE/CARRY4/MUXF7/8 to the importer and interpreter (with their fabric semantics): 1-2 days
  each to model faithfully. The FFs need the CK->Q and setup/hold story, not just a function.
- Whole-design import (`soak.json`, about 10^3 cells): `decide` over all inputs is impossible
  there. It needs compositional proofs: per-cell lemmas (as here) plus a structural matching of
  the netlist against a hierarchy. About 1 week.
- 11b physical import against this one: about 2-3 days once fasm2lean exists.

## What it buys the project

- The proofs are about what yosys 0.62 actually emitted, not about a transcription.
- The drift check turns any change to `cells/rtl/` or to the toolchain into a loud failure, not a
  stale proof. It also covers yosys version changes, because the producer string is in the
  generated header.
- All of B's cell theorems apply to the synthesized netlist with a one-line rewrite.
- It is the bridge 11b needs to go down to the bitstream.

## Fidelity of the primitive models used

- **LUTk / LUT6_2:** `lutB`/`lutK` from `Formal.Cells.Prelim` (shard B), the same semantics as
  B's proofs. The Kleene results rest on H_KLEENE_LUT, as there. O5 = INIT[31:0] over I0..I4 is
  exact for the fabric when A6 = 1, and the netlist ties I5 = 1.
- **IBUF/OBUF:** identity, zero delay (H_PAD_IDENTITY). This is unfaithful for pads, but the pads
  are an artifact of synthesizing a cell as a top level.
- **Nets:** zero delay within one step, and feedback nets are a unit-delay state. This is the
  unit-step reading, not a physical model (see the state cut above).
