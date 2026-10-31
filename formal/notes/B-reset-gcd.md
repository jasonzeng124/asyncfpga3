# B-reset-gcd: the gcd_hw reset contract on the RTL-level control netlist, in Lean

> Scope (audit pass 5, OVERSTATED wording):from bdc's RTL + cells/rtl INITs + gcd_rig.v at default sizes; not the synthesized or routed netlist, nor the board build's parameters; its generator was in a lost scratchpad: audit pass 5.

Probe Rst2 (shard B, gcd_hw capstone), 2026-10-27. This follows
`B-reset-contract.md`. There, the whole-design facts (414 reset cells, the
fixed point, 10 first-firing links, the extra tokens from the 4 `bd_src`)
came only from a Python scan. Here they are kernel-checked theorems about a
Lean import of gcd_hw's control netlist.

No route, no board, no toolchain run. Nothing here is a routed number, and no
nextpnr fingerprint applies. The netlist is the bdc-emitted Verilog with
default matched-delay sizes, plus `cells/hw/gcd_rig.v`. It is not a
synthesized or routed netlist.

## Files and check

- `formal/lean/Formal/Cells/ResetGcdNet.lean` (3518 lines, GENERATED, core
  Lean). It holds the network: one `def nN : NInfo` per node, each with its
  instance name in a comment, and a Braun tree `gTree` for logarithmic lookup
  in the kernel.
- `formal/lean/Formal/Cells/ResetGcd.lean` (420 lines, core Lean). It holds
  the checks and the theorems. It imports `ResetGcdNet`, which imports
  `ResetContract` (read-only; its olean was already in `.lake`).
- Check (two steps, because `ResetGcdNet` is not yet in `Formal.lean`; the
  first step writes its olean):

      cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean -o .lake/build/lib/lean/Formal/Cells/ResetGcdNet.olean Formal/Cells/ResetGcdNet.lean
      cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/ResetGcd.lean

  Both are clean with no output.
  - `ResetGcdNet`: about 26 s wall, 1.0 GB peak.
  - `ResetGcd`: about 55 s wall, 1.45 GB peak. That is nine chunk checks of
    400 nodes at about 4 s each, the census at about 12 s, and the rest.
  - The two files need to be added to `Formal.lean` by the lead; I did not
    edit it.
- `formal/scan.py` passes on both files. There is no sorry, admit, axiom,
  native_decide or bv_decide. The `admit` hits are the identifier
  `admits_ofBool_iff`.
- `#print axioms` (run on a scratch copy, then removed):
  - `gcd_spec`, `gcd_reset_ones`, `gcd_links_empty'`, `gcd_frontier`,
    `gcd_post_definite`: propext, Quot.sound.
  - `gcd_reset_ternary`, `gcd_reset_binary`, `gcd_release_quiet`,
    `gcd_reset_release`: propext, Classical.choice, Quot.sound.
  - `gcd_frontier_fire`, `neg_norst`, `neg_unguarded`: propext.
  - `gcd_census`: none.
- Every certificate is checked with `decide +kernel`: kernel evaluation only,
  no elaborator pre-evaluation, no extra axiom.
- Scratchpad only, not in the repo (scratchpad =
  `/tmp/claude-0/-home-user-asyncfpga3/7f52a4bc-3f11-5919-b34a-537c5f812fdf/scratchpad`):
  - `rst/gen_reset_gcd.py`: Verilog → `gen/net.json`.
  - `rst/emit_lean.py`: → `ResetGcdNet.lean`.
  - `rst/emit_thm.py` + `rst/gen/ResetGcd.lean.tmpl`: → `ResetGcd.lean`.
  - `rst/xcheck_yosys.py`: the independent cross-check, below.
  - The input `rst/gcd_kernel.v` is the same file Rst used (`python3
    bdc/emit.py cloud/fixtures/frontend/gcd/comp/handshake_transformed.mlir
    --no-top --probe n138`).
  - Regenerate with:

        python3 -I gen_reset_gcd.py gcd_kernel.v gen
        python3 -I emit_lean.py gen/net.json OUT/ResetGcdNet.lean
        python3 -I emit_thm.py gen/net.json OUT/ResetGcd.lean 400

## The imported network (`gNet`, 3322 nodes)

- **Node 0: `rst`.** An input node, so every rst pin reads it through its
  own wire. In bounded runs the rst fanout skew is inside the wire bound `W`.
- **Nodes 1..64: data nets** read by control LUTs, each a FREE input with
  value `x` during reset. Any waveform is allowed in the binary theorems.
  They are:
  - 38 steer selects and 21 mux selects (latched link data);
  - the three outputs of `bdc_muxn3_32`'s yosys-inferred decode
    `sel[k] = ctl_req & (s == k)`;
  - the rig's `mism` and `abs_data[31]`.

  Making the decode a free input needs no H_GUARD_MAP. Rst assumed yosys
  keeps `ctl_req` in the decode LUT. Every result below holds without that,
  so **H_GUARD_MAP is not needed for reset or release.**
- **Nodes 65..3321: every control LUT output** of bdc_gcd plus the rig's ring
  and samplers (3257 gates). Each has its REAL INIT and pin list `[I0, ...]`
  from `cells/rtl`. LUT6_2 outputs are separate nodes (O5 = `INIT % 2^32` on
  I0..I4). Delay lines are modelled element by element:
  - `bd_delay` sym: LUT1 2;
  - FASTRISE (DACK): LUT1, then LUT2 E(s, a);
  - `bd_delay_gated`: LUT1, then LUT2 8(s, gate).

  By kind:
  - 185 `bd_c2n` (link/pipe stage controllers and `uenv0`), 1 `bd_c2n_set`
    (`uenv1`), 153 `bd_c2`, 10 `bd_c3`, 14 `bd_c4`, 21 + 21 `bd_mux`
    uj0/uj1, and 9 + 9 + 9 + 9 arbiter ustate O6/O5 and ugrant O5/O6;
  - 38 × 3 steer LUTs, 21 mux `uor`, 4 `bd_src`;
  - delay elements: 663 sym, 169 + 845 FASTRISE, 29 + 927 gated;
  - 20 fused `uor`, 8 amerge `uor`, muxn3 `uor` and `|j`;
  - 7 rig samplers (`uerr_d`, `uok_d`, `uabsn_d`, `uabss_d`, `ucmpb_d`,
    `ucmps_d`, `ucmpb0_d`) and their 7 filter ANDs.
- **Not in the network:**
  - `bd_latch`, `bd_datamux`, the fused datapaths, the `uz_*` LUT1s and the
    amerge index logic. They are data, and every data net that control reads
    is a free input, which covers any behaviour of these blocks.
  - Everything clocked in gcd_hw.v. `rig_rst` is the input node 0.
- **Parameters.**
  - The kernel's default matched-delay sizes (`DELAY_*` defaults in
    bdc_gcd, no `GCD_DUT_PARAMS`).
  - gcd_rig with CMPD = 16, PRBD = 2, WFILT = 2 and no `GCD_RIG_CMP_PROBE`,
    so `cmp_req_raw = 0` and the cmp samplers read constants.
  - A board build with tightened `GCD_DUT_PARAMS` has different chain lengths
    and needs a regeneration, which takes about 2 min. The result does not
    depend on chain lengths beyond `maxRank`.
- **One `NInfo` per node:** its node, a control flag, a rank and a reset
  value. Rank and reset value are an UNTRUSTED certificate written by the
  generator; Lean re-checks them.

### What the import trusts, and the cross-check

The Verilog → Lean step is unverified Python: my reading of `cells/rtl` and
of the generated modules. I checked it independently against yosys's own
elaboration, using the toolchain's yosys at
`~/dev2/lib/fpgatoolchain/openxc7/bin/yosys`. This is NOT the openXC7
synthesis flow: it is `read_verilog` of cells/rtl + gcd_kernel.v +
gcd_rig.v, then `proc`, unset `keep_hierarchy`, `flatten`, `opt_clean
-purge`.

`xcheck_yosys.py` builds yosys's LUT-output graph:
- it drops the data LUTs (latch INITs, datamux INITs, `uz_*`);
- it treats every other driver as data;
- it maps the muxn3 `$reduce_or` to an OR LUT (two identical `$reduce_or`,
  merged as `opt_merge` would);
- it compares that graph with the generated one by Weisfeiler–Lehman colour
  refinement over INITs, ORDERED pin colours (rst/const/data labels) and
  fanout.

Results:
- 3257 = 3257 gates.
- The INIT histograms are equal.
- The WL histograms are equal for all 40 rounds, ending with 3239 distinct
  colours out of 3257.
- Negative control: swapping the two request/ack pins of one link controller
  in the generated graph makes the WL comparison fail.

This is strong evidence of an isomorphism that preserves INIT and pin order.
It is not a proof: WL does not tell whether two data pins read the same data
net, which is irrelevant here.

## Theorems (namespace `Formal.Cells.ResetGcd`)

All of them follow from `all_ok : ∀ n < gM, nodeOK n = true`, which is
assembled from nine chunk certificates `ck0..ck8 : chunkOK lo 400 = true` (by
`decide +kernel`). `nodeOK n` checks, for each node:
- `H_LOCAL`/`H_IN`, under `ResetContract.Bst` at the node's rank;
- rank ≤ 21;
- a definite post-release excitation;
- membership in the frontier (iff);
- membership in the reset-1 set (iff);
- the release-race excitation.

| theorem | statement | hypotheses |
|---|---|---|
| `gcd_spec` | `ResetSpec gNet gA gCtl gRank gR`: every control node of gcd_hw, real INITs, every data net `x` | none (decided) |
| `gcd_reset_ternary` | Kleene from all-X with rst = t: every control node is at its reset value after `maxRank + 2 = 23` Jacobi steps | H_KLEENE_LUT (lutK semantics) |
| `gcd_reset_binary` | every bounded GMW run, ANY power-up state, rst = 1 on `(0, E]`, data arbitrary: every control node is at its reset value on `[23(D+W+1), E]` | `Bounded D W` (H_GATE_BOUND, H_WIRE_BOUND), H_RST_HELD |
| `gcd_reset_ones` | the control nodes with reset value 1 are exactly 17: rst, 9 arbiter q (`ucontrol_merge2/3/4/6/9/10/11/12.uarb1`, `12.uarb2`), 4 `bd_src` requests (`usource3/5/7/13`), `urig.uenv1` (the token) and both `urig.upsnk` elements (p_end already consumed) | none |
| `gcd_links_empty`, `gcd_links_empty'` | every `bd_c2n` (every link and pipe stage, `uenv0`) has reset value 0: all links empty | none |
| `gcd_frontier` | at the simultaneous-release state (rst 0, control at reset values, data `x`), a control node other than rst has excitation ≠ its value iff it is one of 10 nodes: `ulink_n1__1`, `ulink_n155__0/1`, `ulink_n36__0/1/2`, `ulink_n68__0/1`, `ulink_n94__0/1` | none |
| `gcd_frontier_fire` | each of the 10 is a `bd_c2n` (own feedback on I2, rst on I3), reset 0, with excitation 1 at release; its I0 (request) is a control node at 1 during reset: `uenv1` for `ulink_n1__1`, the source requests `usource13` (n155), `usource3` (n36), `usource5` (n68) and `usource7` (n94) for the others | none |
| `gcd_post_definite` | every control excitation at release is definite, with all 64 data nets X | none |
| `gcd_census` | 153 c2, 185 c2n, 1 c2n_set, 10 c3, 14 c4, 21 uj0, 21 uj1, 9 ustate O6 read rst (= 414 reset cells, the scan's numbers), plus the 9 ustate O5: 423 rst pins | none |
| `gcd_release_quiet` | **NEW, whole network.** In a GMW run with wires at most `W` old: if every control node is at its reset value on `[k0 − W, k0]` and no frontier controller has moved on `[k0, T]`, then NO control node moves on `[k0, T]`, whatever rst and the data do from `k0` on (any per-pin release skew, glitches) | H_WIRE_BOUND, H_SETTLED, H_FRONT_HOLD |
| `gcd_reset_release` | the composition: bounded run, any power-up state, rst = 1 on `(0, E]` with `E ≥ 23(D+W+1) + W`, anything afterwards: every control node is at its reset value on `[23(D+W+1), T]` as long as the 10 frontier controllers have not moved on `[E, T]` | `Bounded D W`, H_RST_HELD, H_HOLD_LONG, H_FRONT_HOLD |
| `neg_norst`, `neg_unguarded` | negative controls: with `ulink_n1__1`'s rst pin tied to 0, or with `ucond_br9`'s req1 an OR instead of the steer's AND, the node check is `false` | none |

The kernel check behind `gcd_release_quiet` is the whole-network form of
Rst's `*_race_holdK`:
- In the state where rst is `x` at every pin and every other control net is
  at its reset value (data `x`), the nodes whose excitation is not their own
  reset value are exactly the 10 frontier controllers.
- Every other cell, including every first-wave join, is excited to its reset
  value however rst releases.

So **H_RST_SKEW is not needed for the statement "nothing moves before a
frontier link fires"**. It is proved for every skew. What is still
unproved is what happens AFTER a frontier controller fires while other
cells' rst is still high: the lost-event hazard, H_NO_RETURN.

## What this closes, and what it does not

- Closed:
  - Rst's "the scan is not a proof" for the reset state, the reset-1 set (the
    tokens), the empty links, the frontier and the definiteness of the
    release excitations. All are now decided on the imported netlist.
  - Rst's "the composition is not one Lean theorem", for the part up to the
    first frontier event. `gcd_reset_release` is one GMW theorem from any
    power-up state through release with arbitrary rst skew.
  - H_GUARD_MAP is not needed for any of this, because the muxn3 decode
    outputs are free inputs.
- The Jacobi count differs from Rst. Rst reported 4 handshake-level Jacobi
  steps with delay lines collapsed. With delay lines expanded LUT by LUT,
  the least ranks give `maxRank = 21` and the theorem bound is 23 steps.
  Python reaches the fixed point after 23 changing steps plus one
  confirming step. In GMW terms, rst must be held
  `≥ 23(D + W + 1) + W` model steps, where D is the LUT bound and W the wire
  bound. This is the `design.rst_hold` + `design.rst_flush` EndpointOK pair
  of Rst §3 in model units. A route is needed for ps.
- NOT done:
  - **The first wave after a frontier fires** (`ulink_n1__1` enabling
    `ucond_br9/10/11_j`) is still scan-only. In Lean it needs either a timed
    argument or a closure certificate over a bounded window. A Kleene
    closure with rst `x` forever is useless, because the ring keeps running
    and everything becomes `x`.
  - **H_NO_RETURN** (a cell whose rst is still high misses a complete input
    pulse) is unproved. `gcd_release_quiet` reduces it to events caused by
    the 10 frontier links.
  - **Timing.** The window-channel lemmas (`c2n_frontier`, `first_change`)
    are still separate from the GMW network theorem.
  - **The import is not verified in Lean.** It rests on the generator,
    cross-checked by yosys WL; see above.
  - **Synthesized and routed netlist.** These results are about the
    elaborated RTL netlist, not about what openXC7 maps and routes. Every
    control LUT is `(* keep *)`, except the muxn3 `|j` (H_INFER_OR3: any
    LUT computing OR3 of the three joins has the same `lutK`, by symmetry)
    and the decode, which is free here. Running the same import on a
    `fasm2lean2` netlist of a routed gcd_hw (C-11c) would close this.

## Verdict

**Works.**
- The asked results are proved on the RTL-level control netlist (from bdc's RTL + cells/rtl INITs + gcd_rig.v at default sizes; not the synthesized or routed netlist, nor the board build's parameters; its generator was in a lost scratchpad: audit pass 5):
  - `ResetSpec`, and with it `reset_ternary`/`reset_binary`, for the whole
    gcd_hw control network (3322 nodes, 414 reset cells, real INITs and pin
    maps);
  - the initial state at release (all links empty, the 17 reset-1 nodes,
    hence the tokens: the rig token on `uenv1` plus 4 standing source
    tokens, 9 arbiter q = 1, the p_end sink already consumed);
  - the exactly-10 first-firing link controllers, each firing.
- Beyond the brief: `gcd_release_quiet`/`gcd_reset_release` remove H_RST_SKEW
  from the "nothing moves first" step, and the muxn3 decode no longer needs
  H_GUARD_MAP.
- Cost: about 1.5 min of checking at under 1.5 GB.
- To finish the reset story:
  - the first wave and H_NO_RETURN: about 1 day, with a bounded-window
    closure certificate per frontier event;
  - running the same generator on a routed netlist: about half a day once
    C-11c's import covers gcd_hw.
- What it buys: the capstone can cite one theorem for the state the kernel
  starts its first transaction from, on the actual netlist, with no
  rst-skew assumption until the first frontier event.

## Fidelity per primitive

- **LUT (every control cell):** `lutK`/`lutB` of the REAL INIT on the real pin
  list, so H_KLEENE_LUT for the ternary results.
  - The binary results use 7f's GMW `Run`: a gate takes its LUT value of any
    mixture of per-pin read times, which covers mux-tree transients.
  - LUT6_2 O5/O6 are separate nodes with independent pin reads. This
    over-approximates the shared input buffer, and is sound for every
    theorem here.
- **C-elements, arbiter q, `bd_c2n(_set)`:** a LUT whose own output is one of
  its pins, read through its own wire like any other routed pin.
- **Delay lines:** each element is a LUT node (LUT1 buffer, LUT2 OR / AND
  side stages) with its real INIT. The ranks count them.
- **rst:** one input node. Each of the 423 rst pins has its own read time
  (skew ≤ W in bounded runs). In `gcd_release_quiet` rst is completely free
  after `k0`.
- **Data** (latches, datapaths, data muxes, the muxn3 decode, the rig's
  compare): free inputs. They are never assumed definite, so latches that
  are not reset need nothing.
- **Inferred logic:** only the muxn3 `|j` (OR3 LUT, H_INFER_OR3) is modelled
  as a gate. The decode is a free input.
- **Time:** discrete steps (7f); D and W are not tied to SDF here.
