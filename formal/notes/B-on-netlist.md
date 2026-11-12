# B-on-netlist (probe Bn): shard B's cell theorems on the netlist read back from the bits

Shard B x shard C. 2026-10-27. File: `formal/lean/Formal/Cells/OnNetlist.lean` (core Lean, no Mathlib).

## Verdict

**Works.** For the four routed `link_arb` bitstreams of C-11c (one `bd_link #(.W(3))` and one
`bd_arbiter`; seeds 1..4, nextpnr sha256 9c732bc6303458df, `toolchain.sh` ok, as stamped by
C's `fasm2lean2/check.sh`), every one of the 10 physical LUT outputs is proved to compute
exactly shard B's function for that node: B's INIT on B's pin order (`lutK`/`o5K`/`o6K`),
applied to the physical values of the nodes its physical pins are routed from. The proofs
are in the Kleene semantics, which also gives the binary case. No yosys netlist and no RTL
transcription sit in between. B's headline results are then restated directly on the bits
for every seed:
- `ArbKleene.kleene_exclusion`
- the whole `ArbKleene` step/settle/run model (any scenario theorem transfers)
- `ArbBinary.settled_exclusion`
- `CElemFn.c2_spec` and `c2n_spec`
- `Latch.pair_o5/o6/odd_kleene`

Nothing in this file is trusted from C's renaming. The node map comes from C's `rho` and the
output ports, and is checked:
- a wrong renaming fails (negative control);
- the map agrees with the ports the bits drive;
- the map is injective.

This also checks B's hand transcription against the bits independently. Had B transcribed a
wrong INIT or pin order, `checkAll_s*` would fail.

## Check command

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/OnNetlist.lean

Result: clean, no output. The run takes ~1 min 53 s user (1 min 28 s wall), and most of it is
the 4 `checkAll` decides plus 2 negative controls. Imports use existing oleans only:
- `Formal.Net.Fasm.Basic`
- `Formal.Net.FasmLink.S1..S4`
- `Formal.Cells.{Prelim,CElemFn,Latch,ArbBinary,ArbKleene}`

Nothing was compiled or rebuilt. `#print axioms` was run locally and the lines were then
removed:
- `checkAll_s1`, `mut_init_caught`, `swap_rho_caught` and `read_once_s3` show `[propext]`;
- `arb_step`, `sc_tie_acked_bits`, `settled_exclusion_s4` and `c2_spec_bits` show
  `[propext, Classical.choice, Quot.sound]`.

There is no `sorry`, `admit`, `axiom` or `native_decide`. Only plain `decide` is used, never
`+kernel`.

## Model

- **Node.** Node is the 19 logical nodes of `link_arb`:
  - 9 ports;
  - the link C node `c`;
  - the latch `q0 q1 q2`;
  - the arbiter `q`, `R0`, `g1`, `g2`, `A1`, `A2`.

  `Seed.m n` is its physical source:
  - ports by the common port order (`ports_s*`: all four seeds use the same order);
  - state nodes from C's `rho`;
  - g1/g2/R0 from the output ports the bits drive.
- **Physical state.** It is `w : Nat → LOut → K3`, one value per physical LUT output, plus
  `pv : Nat → K3` per port. A pin reads its routed source; a tie is a constant.
- **`excK` (new, Kleene).** `fnK L o (L.pins.map (srcK pv w))`, i.e. `o6K`/`o5K` of the
  physical INIT on the physical pin vector A1..A6 (H_KLEENE_LUT).
- **`PNet.exc` (binary).** C/11b's own binary semantics, used unchanged. `Seed.next_ofBool`
  proves `excK` restricted to Boolean values equals `PNet.exc`, via
  `lutK_ofBool: lutK init (v.map ofBool) = ofBool (lutB init v)`.
- **Granularity.** One value per LUT output, updated each step, as in `ArbKleene.Net`.
  Combinational outputs (g1, g2, R0) are nodes in their own right, as in B.

### Proof method
`Seed.check n args F` does two things:
1. It resolves each physical pin of the LUT at `m n` to a node or a tie.
2. It enumerates all K3 assignments of the dedup'd support. The support is the nodes on
   either side, at most 5 here, so at most 243 cases.

`Seed.check_sound` proves that this covers every `pv`, `w`.

## Theorems (namespace `Formal.Cells.OnNetlist`)

| name | statement |
|---|---|
| `checkAll_s1..s4` | all 10 node claims hold on seed n (decided) |
| `next_c`, `next_q0/q1/q2`, `next_q`, `next_r0`, `next_g1/g2`, `next_a1/a2` | for any seed passing `checkAll`, for all `pv w`: the physical next value of the node = B's function. In turn: `CElemFn.c2nK`; `o5K/o6K Latch.PAIR [..., t]`; `lutK Latch.ODD`; `ArbKleene.qArbK`, `r0K`, `g1K`, `g2K`; `cK` (ua1/ua2 reading the PHYSICAL g1/g2 node) |
| `kleene_exclusion_bits`, `kleene_exclusion_s1..s4` | physical g1, g2 next values are never both `t` (any K3 state) |
| `latch_bits` | each physical latch LUT output = `K3.mux c q_i d_i` (X on the other bit of the pair never leaks) |
| `arb_step`, `arb_step_s1..s4` | **commuting square**: `S.arb (excK net pv w) = ArbKleene.step (arbIn pv) (S.arb w)` |
| `arb_settle`, `arb_run` | the same for B's `settle k` and `run k` |
| `sc_reset_bits`, `sc_tie_acked_bits` | two of B's scenarios stated on the bits: reset from all-x reaches `idle1`, a fixed point; the acked near-tie ends with both physical ack LUTs at `x`, a fixed point |
| `nextB_g1/g2/a1/a2/c/q` | the binary forms of the claims, on 11b's `PNet.exc` |
| `settled_exclusion_bits`, `settled_exclusion_s1..s4` | `(nextB g1 && nextB g2) = false` for every input list and every Boolean physical state |
| `c2_spec_bits`, `c2n_spec_bits` | ack LUTs are `~rst . C(g_i, A0)`; the link C node is `~rst . C(req_in, ~ack_out)` |
| `q_moves_only_if_alone_bits` | with rst = 0, the physical q LUT changes q only when r1 ≠ r2 |
| `map_consistent_s1..s4` | A1, A2, ack_in, req_out and data_out[0..2] are driven by the mapped LUT outputs; the map is injective on the 19 nodes |
| `shared_sites_s1..s4` | g1/g2, latch q0/q1 and R0/q are O5/O6 of ONE LUT6_2 site on every seed |
| `read_once_s1..s4` | on every physical LUT no node reaches two pins, and every fractured LUT6_2 has A6 tied to 1 |
| `mut_init_caught` | negative control: seed 1 with ugrant INIT bit 36 flipped (C's MutInit). The g2 claim is refuted by an explicit counterexample (r1 = r2 = q = 0), and `check` returns false |
| `swap_rho_caught` | negative control: q0 and q1 swapped in the renaming. The q0 claim is refuted (en = 1, d0 = 0, d1 = 1), and `check` returns false |

Hypotheses: H_KLEENE_LUT (Prelim) for the Kleene statements, and 11b's H_TIE (a tie is a
constant). The binary ones need nothing beyond 11b's `PNet.exc` reading. There are no timing
hypotheses, because none of these statements is timed.

## What lines up, what does not

### Lines up
- **Pin permutation.** Every seed permutes the pins differently, and the physical INITs all
  differ from the RTL's. For example, seed 1 ugrant is `0x0000FF00AAAA0000` on
  `[r1, 0, 1, r2, q, 1]`, against RTL `0x0C0C0C0CA0A0A0A0` on `[r1, r2, q, 0, 0, 1]`. All are
  equal as functions of the nodes, in K3 as well. That is expected: `read_once` holds, and
  B's `MuxTree.evalK_eq_lutK` shows closure semantics is mux-order independent for read-once
  trees. So B's Kleene results do not depend on the router's pin order.
- **O5/O6 packing.**
  - Each fractured LUT6_2 has A6 = VCC on all seeds (checked).
  - O5 of the pair is q0 and O6 is q1 on every seed (also checked indirectly: swapping them
    fails).
  - g1/g2 come from one site, and so do R0/q.
- **Tied pins.**
  - Some unused pins are tied to VCC, not GND (seed 1 latch odd D4, ugrant A3).
  - The latch odd bit on seed 3 has physical INIT `0xFF33CC00FF33CC00`, the pair's upper half
    re-used on `[0, c, 1, d2, q2, 0]`.

  The claims cover all of this, because ties are resolved as constants.
- **Physical facts behind B's statements.**
  - g1 and g2 are one LUT6_2 site sharing one q pin. That is the physical fact behind
    `ArbBinary.settled_exclusion`'s premise ("both grant outputs read the SAME q"): with
    per-pin traces, both outputs see one routed pin. This is now a checked fact of the bits,
    not an assumption.
  - The latch pair shares one en pin.

### Does not line up / not ported
1. **A0 fork skew.** B's `ArbKleene.Inp` has two A0 readings (`a0` at the state LUT, `a0c` at
   the ack C-elements). Here every pin reads its source's single value, so only `a0 = a0c`
   (B's `I`) is covered. B's `sc_a0_fall_ordered` and `sc_a0_fall_runt` use distinct values
   and are NOT ported. The fix is per-pin values (one `K3` per (LUT, pin)), with B's `Inp`
   recovered by assigning the A0 pins of the ustate LUT and of the two ack LUTs separately.
   About half a day.
2. **Timed / trace theorems are not ported.** These include:
   - `ArbBinary.exclusion_transport`;
   - `Latch.holds_value`, `LinkTimed`, `PipeTimed*`;
   - `ArbHeldTimed*`, `CElemTiming`, `ArbHandover`.

   Two separate things block them. First, they need 11b's `Behaves` (per-pin `WinDelay`
   traces) and a lemma that `Behaves` on the physical net implies B's own gate relation on
   node traces. The node claims here supply the function equality that lemma needs; the
   delay plumbing is per theorem, because B's delay structures differ (one delay per gate,
   per pin, or per arc). Second, `ArbBinary`'s trace theorems are about **`bd_arbcell`**
   (`stF`, `C2N_SET` state LUT), which is not in `link_arb`. A routed `bd_arbcell` design is
   needed first.
3. **Cells not in `link_arb` are not covered.** These are c3, c4, the `_set` variants,
   merge, mux, mlink, mem, ctree, pipe, `bd_latch_rst` and `bd_arbcell`. The checker is
   generic, but `Node` and `Seed.m` are written for this design. To cover more:
   - route more designs through C's `fasm2lean2` flow;
   - generalise `Node` to strings, or emit it per design;
   - emit the claim list per cell instance.

   Each instance costs ≤ 3^6 cases.
4. **Mathlib analog results are not touched** (`ArbAnalog`, `ArbResolve`). They take the INIT
   only at the rails, so the binary claims here would instantiate them directly.

## How much of shard B ports this way

- **Function-level lemmas.** This means the INIT = equation lemmas, the Kleene tables,
  exclusion and fixed points in CElemFn, Latch part 1, ArbKleene part 1 and ArbBinary §1–2.
  They port directly for every cell instance on the bits, by rewriting with `next_*`. This
  is mechanical, and shown here for the headline ones.
- **Discrete Kleene step models.** These are ArbKleene §3 and similar models in
  TernaryPhases and LinkHandshake, where they use one step per node. They port via a
  commuting square like `arb_step`. All of ArbKleene's scenarios that use `I` follow as
  corollaries (two shown). The two A0-fork scenarios need per-pin values (item 1).
- **Timed trace theorems.** These are most of B by line count: the *Timed*, Handover,
  Corners, Bundling and CElemTiming files. They do NOT port without the `Behaves` →
  B-gate-relation bridge. The function part of that bridge is done here. The delay part is
  estimated at 1–3 days per family, and the arbcell family needs a routed arbcell design.

Rough share: maybe 30–40% of B's theorem statements (all function-level, plus the discrete
Kleene ones) now port with little effort; the timed majority does not yet.

## Fidelity per primitive

- **LUT6 / LUT6_2.**
  - Kleene: `o6K`/`o5K` (closure semantics, H_KLEENE_LUT) of the PHYSICAL INIT on the
    PHYSICAL pins. The per-mux tree reading equals this here because `read_once` holds
    (B's `MuxTree`).
  - Binary: 11b's `o6B`/`o5B`.
  - O5 = INIT[31:0] over A1..A5. A6 = 1 is read from the bits.
  - Glitches and delays are not modelled: these are next-value (excitation) functions.
- **Routing.** A pure connection; every pin fed from one source reads the same value, so
  there is no per-pin skew (see item 1). Per-pin delays exist in C's `pinDelay` and are
  unused here.
- **Ties.** Constant (H_TIE; C's tool checks for a single driver).
- **IOB/IOI.** As in C-11c: an identity bypass, checked non-inverting by the importer.
- **Feedback.** A C-element or latch LUT reading its own output is just a pin whose source
  is that LUT output. The loop's delay is not modelled (step semantics).

## Effort to finish

- Per-pin values, porting the two A0-fork scenarios: about 0.5 day.
- Generic `Node` from C's emitted design, plus claims per instance, for more designs: 1–2 days.
- The `Behaves` → B-trace bridge for one timed family (e.g. Latch `holds_value` / LinkTimed):
  1–3 days per family.

## What it buys the project

B's function-level and Kleene step results now hold for the LUTs as the board runs them in
four real bitstreams, after the placer's pin permutation, re-encoded INITs, VCC ties and O5/O6
packing. This includes internal nets that no port shows. It also independently confirms B's
transcription of the cells' INIT constants and pin maps. A one-bit INIT change and a mislabelled
pair output are both caught.
