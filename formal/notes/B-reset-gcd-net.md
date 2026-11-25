# B-reset-gcd-net: is ResetGcdNet the network actually built?

Probe Bnet (shard B), 2026-10-27. Background: audit pass 5 found that
`Formal/Cells/ResetGcdNet.lean` (3322 nodes) was generated from bdc RTL,
cells/rtl INITs and gcd_rig.v at default sizes. The generator lived in a
scratchpad that no longer exists, and the term was never compared with a
synthesized or routed netlist.

This probe adds:
- a committed, re-runnable generator, `formal/notes/B-reset-gcd-net-gen/`
  (`gen.py`, `thm.lean.tmpl`, `routed.py`, `README.md`);
- its output, `formal/lean/Formal/Cells/ResetGcdNetRe.lean`, which also holds
  the comparison theorems and a re-check of the reset contract.

## Builds used (toolchain.sh 9/9 ok, nextpnr 9c732bc6303458df)

- **C-10e (probe Bar), seeds d/2/3/4.** Recipe: `BDC_SELECT_PADS=hw/gcd_hw_pads.json
  BD_RLOC=v4 hw/build_hw.sh gcd_hw`. This is research/JOURNAL 21:40, the
  board-queue #1 recipe, and the sizes are unsized.
  - The synthesized `gcd_hw.json` is identical for all four seeds (sha256
    f0a7f326...).
  - These builds had no `--freq` (12 MHz default target). That changes
    placement, not the netlist.
- **R5, seed d (built here).** Same recipe plus
  `BD_SIZES=research/data/gcd_hw_sizes_R5.vh` (220 sizes). Bit sha256
  5914898f...; fasm_audit PASS.

## 1. Regenerated term vs committed term (Lean, `ResetGcdNetRe.lean`)

The generator works from the synthesized netlist, flattened by the
toolchain's yosys. It classifies cells by `$scopeinfo` module type and does
not read ResetGcdNet; the README gives the rule. It reproduces ResetGcdNet
exactly, except for three structural differences:

1. **Data inputs merged (29).** The RTL has one wire per fork copy of a
   latched select bit (`n5__0/1/2_data[0]`, ...). Synthesis merges them into
   one net. The real network therefore has 35 data inputs where the
   committed term has 64. `phiL` lists the 29 merges, and each pin that read
   a merged input reads its representative instead.
2. **Longer select delays (16 new nodes, 6 rewired pins).** The real build
   uses `gcd_hw_pads.json` (13/14/13), so the `rdly` chain of
   `ulink_n32__2`, `ulink_n166__0` and `ulink_n166__1` stage[1] has 13, 13
   and 14 elements instead of 8.
   - The new elements are nodes 3322..3337 (`newT`, each LUT1 INIT 2).
   - Six mux joins now read the new chain end instead of g[7] (`diffT`):
     `umux2.uj0/uj1` 2175→3326, `umux19.uj0/uj1` 2014→3331 and
     `umux20.uj0/uj1` 2039→3337.
3. **One pin permutation.** In the inferred `umux21.|j` (OR3, INIT 0xFE,
   node 1641) the pins are in the order [j1, j2, j0] (`permT`). OR is
   symmetric, so the function is the same.

Everything else matches exactly: INIT, pin list, control flag, and (as a
generator check, not a Lean theorem) every rank and reset value.

Checked in Lean, namespace `Formal.Cells.ResetGcdRe`:
- `re_matches`: for every n < 3322, `rNode n = expect n ∧ rCtl n = gCtl n`.
  `expect n` is the committed node with data pins renamed by phi, plus the
  diffT/permT edit at those 7 nodes. Proved from 9 chunks of `decide +kernel`.
- `diff_real`: the 7 edits are not no-ops.
- `new_nodes`: the indices ≥ 3322 are exactly the 16 listed gates.
- `unused_ok` / `unused_unread`: the 29 merged indices are non-control
  inputs that no gate reads.

Negative control (scratch `Mut.lean`): flipping one INIT bit of node 1696
(`ulink_n1__1.ctl`) in the generated file makes `chunkSame 1600 400`,
`re_frontier_fire` and `re_census` fail.

## 2. What this means for ResetGcd / ResetGcdWave / ResetGcdVec

- **ResetGcd: re-proved on the real network** in `ResetGcdNetRe.lean`, with
  the same statements and hypotheses:
  - `re_spec`, `re_reset_ternary`, `re_reset_binary`, `re_reset_ones`,
    `re_frontier`, `re_frontier_fire`, `re_post_definite`, `re_census`,
    `re_release_quiet`, `re_reset_release`;
  - maxRank 21, reset-1 set = the committed 17 (`ones_same`), frontier = the
    committed 10, census 153/185/1/10/14/21/21/9/9 with 423 rst pins.

  The committed theorems are not wrong. They describe a network that differs
  from the build, and the build satisfies them too. The hypotheses are
  unchanged (H_RST_HELD, Bounded D W, H_FRONT_HOLD, ...). No new non-vacuity
  witness was built; the hypothesis shapes are ResetGcd's.
- **ResetGcdWave and ResetGcdVec were NOT re-proved on the real network.**
  Evidence they transfer, from a Python mirror (not a proof):
  - The first wave from the release state, with steers cut to 0, reaches its
    fixed point in 33 Jacobi steps on both networks (= B2..B34) and changes
    the same 108 nodes.
  - The 6 steer excitations at the fixed point are equal.
  - All 423 rst readers see the same pin vector in the reset state.
  - The 23 changed or new nodes are not wave nodes. They stay at reset value
    0 through the first wave, and the old and new chain ends are both 0.

  Re-proving both files needs ResetGcdWave/Vec rewritten over `rNet`. That
  is a mechanical port, not done here.

## 3. Against the routed design, read back from the bits

`routed.py` uses the FASM from `bit2fasm --bitread` of `gcd_hw.bit`, shard
C's `fasm2lean3.py` (read-only), and `NEXTPNR_BEL` as the placement hint. It
does NOT use `X_ORIG_PORT`.

For every control node it checks that the physical LUT at its BEL computes
the logical function of the physical images of its logical sources, for
every assignment. Physical pins whose source is no image must not matter.
The image of a net is the site output of its driver's BEL, and the check
also requires distinct logical nets to have distinct images.

| build | control nodes equal as functions | fail | nets with distinct images |
|---|---|---|---|
| C-10e d | 3273/3273 | 0 | 3309 |
| C-10e 2 | 3273/3273 | 0 | 3309 |
| C-10e 3 | 3273/3273 | 0 | 3309 |
| C-10e 4 | 3273/3273 | 0 | 3309 |
| R5 d | 1790/1790 | 0 | 1826 |

These hold despite what nextpnr really does to the LUTs. It splits a LUT6_2
into a LUT6 and a LUT5. It folds tied pins: the steer O6 with I5 tied to 1
becomes a LUT5 with INIT 0x88888888. It puts several tied pins on one
physical pin, and it permutes pins.

Negative controls on seed d: `--mutate` (one physical INIT bit) and `--swap`
(two physical pin sources) of `ulink_n1__1.ctl`. Each is the only failure.

**Do the logical theorems transfer?** In the GMW model, yes, by the
following argument, which is NOT a Lean theorem:
- Each physical control LUT is the same Boolean function of the same nets
  (pins permuted, constants folded).
- A permutation or a merged tied pin leaves `lutK`'s Kleene extension
  unchanged as long as the non-constant pins are distinct. That is the case
  here: a routed check failure would show a merge of non-constant pins.
- So a run of the physical network is a run of `rNet`, with the per-pin
  wire times taken from the routed delays.

What is not covered:
- The delays themselves (the D and W bounds of `Bounded`).
- Glitches inside the physical LUT when a permuted pin moves.
- A Lean-checked physical term. This would be `routed.py`'s per-node check
  run as `decide`. C's fasm2lean3/gen3 Rho is the natural place for it.

## R5 (sized) network

`gen.py net` on the R5 synthesized netlist gives 1826 nodes, against 3309
for C-10e:
- 1511 committed delay elements are gone and 44 are added;
- the same 35 data inputs, 29 merges and inferred `|j`.

A scratch Lean file, `Bnet/r5/ResetGcdNetR5.lean`, holds the R5 term with
part 2 only (`gen.py lean ... -`, namespace renamed). It compiles cleanly
(56 s), so the reset contract (spec, reset, ones, frontier, release) also
holds on the R5 netlist, with maxRank 21. It is not in the repo: the probe
was allowed one Lean file.

## Checks

- `bchk.sh formal/lean/Formal/Cells/ResetGcdNetRe.lean` → `[bchk] OK`.
  125 s for the whole file, 1.9 GB peak; each chunk is far under 2 min.
- `scan.py` is clean.
- Axioms: `re_census` none; the decided structural facts `propext`; the
  others `propext`, `Quot.sound`, and `Classical.choice` for
  reset_ternary/binary, release_quiet and reset_release.
- Re-running the generator gives a byte-identical `ResetGcdNetRe.lean`.
- `ResetGcdNetRe` must be added to `Formal.lean` by the lead.
