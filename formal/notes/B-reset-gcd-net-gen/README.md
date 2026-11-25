# B-reset-gcd-net-gen: gcd_hw's control network from the real build

Regenerates the control network used by `ResetGcd` / `ResetGcdWave` /
`ResetGcdVec` from the yosys JSON of a real gcd_hw build, writes it as
`Formal/Cells/ResetGcdNetRe.lean`, and compares it with the committed
`ResetGcdNet.lean`. `routed.py` checks the same network against the routed
design as read back from the bitstream. Findings: `../B-reset-gcd-net.md`.

## Inputs

A gcd_hw build made with the project's own flow. The C-10e recipe (probe Bar):

    cd <private copy>/cells && BDC_SELECT_PADS=$PWD/hw/gcd_hw_pads.json BD_RLOC=v4 \
        [NEXTPNR_SEED=N] ./hw/build_hw.sh gcd_hw

Run `cells/verify/toolchain.sh` first. Every output below is from nextpnr
9c732bc6303458df, toolchain.sh 9/9 ok.

- `cells/build/hw/gcd_hw/gcd_hw.json`: the synthesized netlist that nextpnr
  reads. It is the same for every seed: sha256 f0a7f326..., seeds d/2/3/4.
- `gcd_hw_routed.json`: used by `routed.py` only for BEL placement.
- `gcd_hw.bit`, read back with prjxray's `bit2fasm.py --bitread`, then
  `formal/tools/fasm2lean3/fasm2lean3.py FASM XDC --json phys.json`. That is
  shard C's extractor, read-only here.

## Run

    G=formal/notes/B-reset-gcd-net-gen
    python3 -I $G/gen.py net   .../gcd_hw.json OUT/net.json --flat OUT/flat.json
    python3 -I $G/gen.py match OUT/net.json formal/lean/Formal/Cells/ResetGcdNet.lean OUT/order.json
    python3 -I $G/gen.py lean  OUT/net.json OUT/order.json formal/lean/Formal/Cells/ResetGcdNetRe.lean \
                               formal/lean/Formal/Cells/ResetGcdNet.lean
    /tmp/.../bchk.sh formal/lean/Formal/Cells/ResetGcdNetRe.lean          # ~2 min, 1.9 GB peak

    # routed (per seed): read the bits back, extract, compare
    python3 -W ignore $PRJ/utils/bit2fasm.py --db-root $DB --part xc7z010clg400-1 \
        --bitread $TC/openxc7/bin/bitread gcd_hw.bit > fromBit.fasm
    python3 formal/tools/fasm2lean3/fasm2lean3.py fromBit.fasm gcd_hw.xdc --json phys.json
    python3 -I $G/routed.py OUT/net.json OUT/flat.json gcd_hw_routed.json phys.json [res.json]
    #   negative controls: append  --mutate NAME  (flip one physical INIT bit)
    #                      or      --swap NAME    (swap two physical pin sources)

With `-` in place of the last argument, `gen.py lean` leaves out the
comparison part and writes only the term and the reset-contract re-check.
This is how the R5 (`BD_SIZES=research/data/gcd_hw_sizes_R5.vh`) netlist
was checked; that netlist does not match ResetGcdNet node for node.

Regenerating from the seed-d synth JSON gives a `ResetGcdNetRe.lean` that is
byte-identical to the checked-in one (checked with `cmp`).

## What `gen.py net` takes as the control network

The definition is ResetGcdNet's, applied to the synthesized netlist, which is
flattened with the toolchain's yosys. The `$scopeinfo` cells give each LUT's
RTL module.

- **Scope.** Cells under `urig.` only. gcd_hw.v's clocked logic, its
  samplers and the dhk/invhk oscillators are outside it.
- **Node 0.** The net `urig.rst`.
- **Control LUTs.** Any LUT whose innermost module is one of `bd_arbiter`,
  `bd_c2`, `bd_c2n`, `bd_c2n_set`, `bd_c3`, `bd_c4`, `bd_delay`,
  `bd_delay_gated`, `bd_mux`, `bd_src` or `bd_steer`. Also any LUT
  instantiated directly in a `bdc_*` module or in `gcd_rig` whose name does
  not start with `uz_` (these are the `uor` LUT1s and the rig's samplers and
  filters).
- **Inferred LUTs.** A synthesized (scope-less) LUT counts as control when
  all its non-constant inputs are control nets AND it drives a control pin.
  This rule is a fixed point followed by pruning. On gcd_hw it selects
  exactly one LUT, the `|j` OR3 of `bdc_muxn3_32`. It rejects the amerge
  index encoders, which feed only latches.
- **Data.** Everything else is data: `bd_latch`, `bd_datamux`, `uz_*`,
  datapath, the muxn3 decode. A control pin that reads a net that is neither
  rst nor a control output becomes a free DATA input node.
- **Outputs and pins.** One node per LUT output. A LUT6_2 gives two nodes:
  O5 (`INIT % 2^32` on I0..I4) and O6. Pins are listed in the order
  `[I0, I1, ...]`, with constants as k0/k1.

`match` renumbers the result onto ResetGcdNet's indices, using name variants
(an untrusted heuristic). Real-only nodes are numbered after 3321. `lean`
computes the rank and reset-value certificates (Kleene from all-X, the way
ResetGcd checks them). On the committed term this reproduces every committed
rank and reset value. `lean` then emits the term together with
`thm.lean.tmpl`.
