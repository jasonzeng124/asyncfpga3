# B-reset-gcd-wave: gcd_hw from rst release through the first wave, in Lean

Probe Rst3 (shard B, gcd_hw capstone), 2026-10-27. This follows
`B-reset-gcd.md` (Rst2). Rst2 stopped at "nothing moves before one of the 10
frontier links fires". This probe carries every run on through the whole
first wave, up to the first request into the loop, and settles H_NO_RETURN
for that window.

No route, no board, no toolchain run. Nothing here is a routed number, and no
nextpnr fingerprint applies. The network is Rst2's `gNet`: bdc-emitted
Verilog with default matched-delay sizes, plus `cells/hw/gcd_rig.v`. It is
the elaborated RTL netlist, not a synthesized or routed one.

## Files and check

- `formal/lean/Formal/Cells/ResetGcdWave.lean` (about 790 lines, core Lean).
  It is GENERATED from a template so the certificate lists can be refreshed,
  but every proof in it was written by hand. It imports `Formal.Cells.ResetGcd`
  and `Formal.Cells.TernaryPhases`, both read-only, with oleans already in
  `.lake`.
- Check:

      cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/ResetGcdWave.lean

  - Clean, with no output.
  - About 30 s wall, 0.71 GB peak.
  - 17 chunk certificates of 200 nodes, each about 1.5 s of kernel time.
    Everything else takes under a second each.
  - The file still has to be added to `Formal.lean` by the lead. I did not
    edit it.
- `formal/scan.py` passes. There is no sorry, admit, axiom, native_decide or
  bv_decide. Every certificate is checked with `decide +kernel`.
- `#print axioms` (run on a scratch copy, then removed):
  - `gcd_first_wave`, `gcd_wave_only`, `gcd_wave_settled`, `gcd_boot`,
    `gcd_loop_late`, `gcd_clean_release`, `iter_le_bst`: propext,
    Classical.choice, Quot.sound.
  - `gcd_wave_moves`, `gcd_wave_quiet`, `rst_reads_low`: propext, Quot.sound.
  - `gcd_steer_req`, `steerPaths_ok`, `neg_nocut`, `neg_rank`, `neg_chain`:
    propext.
  - `wL_shape`: none.
- Scratchpad only, not in the repo (scratchpad =
  `/tmp/claude-0/-home-user-asyncfpga3/7f52a4bc-3f11-5919-b34a-537c5f812fdf/scratchpad`):
  - `wave/net.py`: loads Rst2's `rst/gen/net.json`, with exact ternary LUTs.
  - `wave/ev.py`: one interleaving of the event simulation, as an
    exploration.
  - `wave/ab.py`: the Algorithm A closure on the cut network, then B.
  - `wave/ranks.py`: the B ranks.
  - `wave/emit.py` + `wave/Wave.lean.tmpl`: write the Lean file.
  - Regenerate with:

        python3 ab.py && python3 ranks.py && python3 emit.py OUT/ResetGcdWave.lean

## Method

The tool is multi-phase ternary soundness (`TernaryPhases.phase_cov`), as in
TernaryOnBits, applied to a CUT network.

1. **The cut.** `gCut = cut gNet zB` turns the 6 LUT outputs of the
   loop-entry steers into inputs:
   - `ucond_br9.u` O5/O6 = nodes 100/101;
   - `ucond_br10.u` O5/O6 = 104/105;
   - `ucond_br11.u` O5/O6 = 108/109.

   A run of `gNet` is a run of `gCut` with the same wires (`cutRun`,
   `cutBounded`: fewer gate constraints). Up to the step before a steer
   output first leaves 0, those inputs read 0. This is the definition of
   the segment's end ("the first time the loop's compute units are
   requested"), not a timing assumption. Cutting there is what makes the
   ternary analysis work. Without a cut the ring keeps running and every
   node ends up `x` (Rst2's observation). With the cut, the whole first
   wave is acyclic.
2. **Phase A** (the rst window: rst `x`, every data net `x`, steers 0).
   - `sA` keeps every control node at its reset value except rst and 108
     "wave" nodes, which are `x`.
   - `sA` is closed under the window step: `sA_closed`, decided node by
     node.
   - So any rst waveform on `(S, F]` is covered: per-pin skew, glitches,
     even re-assertion.
3. **Phase B** (rst final 0). The Jacobi iterates from `sA` are bounded by
   a RANKED certificate, a new generic lemma `iter_le_bst`:
   - node `n` is `x` up to iterate `wR n` and `wF n` from then on;
   - each ranked node is checked once, at iterate `wR n - 1`;
   - monotonicity of `lutK` gives every later iterate for free.

   This avoids evaluating `iter` 34 levels deep in the kernel, which would
   be exponential.
4. **Composition** with Rst2's `gcd_reset_binary`.
5. **A causal chain** for the timing of the end of the segment
   (`hold_one`, `chain_hold`, `gcd_loop_late`).

## The first wave: phases and what is definite at each phase end

Phase A, on `[S, E]`:
- Every control node is definite at its reset value, EXCEPT rst and the 108
  wave nodes, which are `x`.
- The 6 steers are 0.
- All 64 data nets are `x`.

Phase B_m, on `[F + m(D+W+1), E]`: the wave nodes with rank ≤ m are
definite at their final value. All others are as in A.

| B phase | nodes that become definite (final value 1 for all of them; rst ends at 0) |
|---|---|
| B1 | rst |
| B2 | the 10 frontier link controllers: `ulink_n1__1`, `ulink_n155__0/1`, `ulink_n36__0/1/2`, `ulink_n68__0/1`, `ulink_n94__0/1` |
| B3 | `ucmpi0.uor`, plus the 6 ack-delay elements `uack.g[0..5]` of each of the 10 links (61 nodes) |
| B4 | `ucmpi0.udly.g[0]`, and the fork ack sub-trees `ufork11`, `ufork19`, `ufork24`, `ufork39` |
| B5 .. B33 | `ucmpi0.udly.g[1]` .. `g[29]`, one per phase. This is the matched delay of the compare `ucmpi0`. |
| B34 | the three steer joins `ucond_br9_j`, `ucond_br10_j`, `ucond_br11_j` |

- After B34 every control node is definite, at `sigB` (`sB_max`).
- `gcd_wave_moves`: `sigB` differs from the reset state exactly on rst
  (1 → 0) and the 108 wave nodes (0 → 1).
- The four source tokens' sub-waves stop at B4. Their links have fired and
  hold their data, but the source acks (`ufork10` etc.) wait on the
  compute-unit joins (`ucmpi3.ujoin`, `uaddi0.ujoin`, ...) that consume the
  data from the loop.
- The rig token's sub-wave (`uenv1` → `ulink_n1__1` → `ucmpi0` → the three
  joins) runs to B34.
- `gcd_wave_quiet`: at `sigB`, in the UNCUT `gNet` (rst 0, data `x`), every
  control node other than the 6 steers is excited to its own value. The
  network is quiescent apart from the steers.
- Each steer is excited to `x`, and only through its data select:
  - `gcd_steer_req`: the three joins are 1;
  - with a definite select bit `b`, O6 (the true branch) is excited to `b`
    and O5 (the false branch) to `!b`. So exactly one branch is requested;
  - the selects are `n5__2/1/0_data[0]`, the compare result.

## Theorems (namespace `Formal.Cells.ResetGcdWave`)

| theorem | statement | hypotheses |
|---|---|---|
| `iter_le_bst` (generic) | a ranked B certificate bounds every Jacobi iterate from an A-closed state | decided side conditions |
| `cutRun`, `cutBounded` (generic) | a (bounded) run of `N` is a (bounded) run of any cut of `N` | none |
| `gcd_first_wave` | bounded run, control at reset on `[S−W, S]`, rst anything on `(S, F]` and 0 on `(F, E]`, data anything, steers 0 on `(S, E]`: `sA` covers `[S, E]`, `sB m` covers `[F + m(D+W+1), E]` | `Bounded D W`, H_SETTLED, H_RST_LOW, H_STEER_HOLD |
| `gcd_wave_only` | on `[S, E]` every control node outside `wL` is at its reset value | same |
| `gcd_wave_settled` | on `[F + 34(D+W+1), E]` every control node is at `sigB`, for EVERY rst waveform in the window | same |
| `gcd_wave_moves` | `sigB n ≠ gR n` iff `n` is in the certificate (rst + 108 wave nodes) | none |
| `gcd_wave_quiet`, `gcd_steer_req` | quiescence at `sigB` except the steers, and the steers' excitation as a function of the select bit | none |
| `gcd_boot` | `gcd_first_wave` from ANY power-up state (rst 1 on `(0, S]`, `S ≥ 23(D+W+1) + W`) | `Bounded`, H_RST_HELD, H_HOLD_LONG, H_RST_LOW, H_STEER_HOLD |
| `gcd_loop_late` | if the rst source is 1 on `[S−W, T]`, no steer leaves 0 before `T + 35`. The request must cross 34 real LUTs (`steerPaths_ok`): `ulink_n1__1`, `ucmpi0.uor`, `udly.g[0..29]`, a join, the steer. | H_WIRE_BOUND, H_SETTLED, H_RST_HIGH |
| `gcd_clean_release` | **the initial segment**, below: clean rst edge at `F`, any power-up state. H_STEER_HOLD is needed only after `F + 34`. | `Bounded`, H_RST_CLEAN, H_HOLD_LONG, H_RST_LOW, H_STEER_HOLD after `F+34` |
| `rst_reads_low` | every rst PIN reads 0 at every `k ∈ (F + W, E]` | `Bounded`, H_RST_LOW |
| `neg_nocut` | without the cut, phase A is not closed (`ucond_br9` O6 excited to `x` while `sA` says 0) | none |
| `neg_rank` | ranking `ucond_br9_j` one phase early fails the B check | none |
| `neg_chain` | the chain check fails with rst at 0, and when a delay element is skipped | none |

## The initial segment the capstone can start from

Take every bounded GMW run of gcd_hw's control network, from ANY power-up
state, where:
- rst is 1 on `(0, F]` with `F ≥ 23(D+W+1) + W`, then 0;
- data does anything;
- `E` is any step before the first loop request (the 6 steers are 0 on
  `(F + 34, E]`; up to `F + 34` this is proved, not assumed).

Then:

1. On `[F, E]`: control is covered by `sA`. Every node outside the 109-entry
   `wL` (rst + 108 wave nodes) is at its reset value.
2. On `[F + m(D+W+1), E]`: the wave nodes ranked ≤ m are at their final
   value 1. If `E ≥ F + 34(D+W+1)`, the control state on
   `[F + 34(D+W+1), E]` is exactly `sigB`.
3. The first loop request comes after `F + 34` (`gcd_loop_late`).
4. If `W < 34`, every rst pin reads 0 at the first loop request
   (`rst_reads_low` with `k ∈ (F+W, E]`, which is non-empty since
   `E ≥ F + 34`).
5. At `sigB`, the only excited control nodes are the 6 steers. With the
   compare bit `b` on their selects, the steers request the true branch
   (O6) iff `b`.

The capstone's first loop phase therefore starts from:
- every cell out of reset (if `W < 34`);
- control state `sigB` (if the wave has settled, `E ≥ F + 34(D+W+1)`),
  else `sA` refined by the elapsed `sB m`;
- data `x` except what the capstone proves about the latched data.

## H_NO_RETURN

**Proved for the reset-release window.** H_NO_RETURN is the hazard that a
cell still held in reset misses a complete input pulse. `gcd_first_wave`
covers every rst waveform on `(S, F]` at once: any per-pin skew (inside
`W`), glitches, re-assertion. In every case the state after `F + 34(D+W+1)`
is the same `sigB`, which is also the simultaneous-release result. So no
event of the first wave is lost to a cell that is still in reset.

The reason is visible in the certificate. On the cut network every wave
input is persistent: no ack returns before the steers move. A cell held in
reset therefore sees the same input levels when it is released.

**What remains is moved to an explicit, checkable condition:**
- **Nothing is held in reset when the loop starts.**
  - With a clean rst edge, `gcd_clean_release` + `gcd_loop_late` +
    `rst_reads_low` show this when `W < 34` (H_RST_BEFORE_LOOP).
  - In physical terms: max rst-net wire delay (the routed spread over the
    423 rst pins) < 34 GMW steps, where a step is at most the minimum
    LUT+wire delay. That is the fast-corner delay of the 34-LUT path
    `ulink_n1__1 → ucmpi0 → join → steer`.
  - **Test:** routed SDF. Compare max over rst pins (slow) with the sum of
    34 fast-min LUT delays on that path, guardbanded (`GUARD_LO`/`GUARD_HI`).
    With the default 30-element compare delay this is very likely
    satisfied, but it is NOT a routed number here.
  - After that, as long as rst stays 0, no cell is in reset, so the hazard
    cannot occur in the loop.
- **A glitchy rst source** (H_RST_CLEAN fails) is still covered by
  `gcd_first_wave` up to the first steer move. But `gcd_loop_late` then
  only counts from the first fall.
- **Where rst comes from.** In `cells/hw/gcd_hw.v`,
  `rig_rst = ~por_done | rst_sr[15]`: a LUT OR of two `hk_ck` flops.
  - Its falling edge is a single clean edge unless both flops switch, in
    opposite directions, on the same `hk_ck` edge. H_RST_CLEAN is exactly
    that condition. **Test:** GLS of the housekeeping logic, or a check
    that `por_done` never rises on the edge where `rst_sr[15]` falls.
  - rst is re-asserted at every window edge while the kernel is still
    running. That re-entry is covered: `gcd_reset_binary`, and so `gcd_boot`
    and `gcd_clean_release`, start from ANY state.

## Named hypotheses and what they stand for

- **`Bounded D W`**, from 7f:
  - H_GATE_BOUND: LUT ≤ D+1 steps;
  - H_WIRE_BOUND: wire ≤ W steps.

  Test: routed SDF.
- **H_GMW_GATE** (the `Run` itself): a gate moves only to its LUT value of
  some mixture of pin reads, and takes at least one step. So **the step
  must be at most the minimum LUT+wire delay**. The 34-step bound of
  `gcd_loop_late` is only physical under that step size.
- **H_SETTLED**: control at reset values on `[S−W, S]`. It is discharged by
  `gcd_reset_binary` in `gcd_boot`/`gcd_clean_release`.
- **H_RST_HELD / H_RST_CLEAN**: the rst source is 1 on `(0, S]` / `(0, F]`.
  Test: gcd_hw.v reset FSM, and GLS.
- **H_HOLD_LONG**: rst is held at least `23(D+W+1) + W` steps (Rst2).
- **H_RST_LOW**: the rst source is 0 on `(F, E]`.
- **H_STEER_HOLD**: no loop-entry steer has left 0 by `E`. This is the
  definition of the segment end, not a physical assumption. Up to `F + 34`
  it is a theorem (`gcd_loop_late`).
- **H_RST_HIGH** (`gcd_loop_late`): the rst source is 1 on `[S−W, T]`.

## What did not work / not done

- **No ternary analysis of the uncut network.** A plain multi-phase
  ternary analysis (Rst2's "closure with rst `x`") does not work on the
  uncut network: the steer outputs go `x` and the A closure would grow
  around the ring. `neg_nocut` records the first failure. The cut at the
  steers is the essential idea. The next segment (the loop) needs data:
  the steers' selects are free here.
- **No "fast phases before slow ones" ordering.** GMW has no lower delay
  bound beyond one step per gate. So nothing orders the end of B4 (the
  source sub-waves) before the first loop request, except
  `D`/`W`-dependent arithmetic. When `E < F + 34(D+W+1)`, the capstone
  must carry the `sA` cover for the nodes not yet settled.
- **The import is still unverified in Lean** (Rst2's generator, with the
  yosys WL cross-check). The cut set, the ranks and the chain are
  untrusted Python output, but every one of them is re-checked by the
  kernel.
- **This is the elaborated RTL netlist, not a routed one.** The `W < 34`
  condition needs a routed SDF to become a number.
- **Data:** the steer selects come from `ucmpi0`'s output latch. That the
  select is valid when the join fires is the bundling constraint of
  `ucmpi0`'s matched delay (30 elements). It is a data/timing fact that is
  NOT proved here; the select is a free `x` input.

## Verdict

**Works.**
- The first wave is proved on the whole 3322-node network, for every rst
  waveform:
  - the phase-by-phase definite sets (A, B1..B34);
  - the final state `sigB` (108 nodes moved, quiescent except the 6 steers);
  - the steers requesting exactly one branch per select bit.
- H_NO_RETURN is proved for the reset-release window. The residual is
  reduced to one SDF-checkable inequality (`W < 34` steps), given a clean
  rst edge.
- Cost: about 30 s of checking, 0.7 GB, 17 chunks at about 1.5 s each.
- Effort to finish:
  - the loop phases need the latched-data interface (the selects), probably
    built with the same cut + ranked-certificate machinery per loop
    iteration: about 1–2 days;
  - a routed netlist import plus SDF, to turn `W < 34` into a measured
    margin: about half a day once C-11c covers gcd_hw.
- What it buys: the capstone can start its first loop transaction from one
  theorem (`gcd_clean_release` + `gcd_wave_settled` + `gcd_steer_req`),
  with no rst-skew assumption except `W < 34`.

## Fidelity per primitive

- **LUT (every control cell):**
  - `lutK`/`lutB` of the REAL INIT on the real pin list (Rst2's import),
    so H_KLEENE_LUT, mux-tree semantics, for the ternary certificates;
  - the binary statements use 7f's GMW `Run`. Per-pin reads cover mux-tree
    transients and LUT6_2 O5/O6 with independent reads (over-approximating
    the shared input buffer: sound).
- **C-elements, link controllers, joins:** LUTs whose own output is a pin,
  read through its own wire. `hold_one` handles the self-read explicitly:
  the self pin may see any value of the last `W` steps.
- **Delay lines** (`ucmpi0.udly`, the links' `uack`): element by element,
  real INITs. The gated elements `g[1..29]` (AND with the link) are why the
  rise path is 30 LUTs long.
- **Steers:** the real `bd_steer` LUT6_2 INIT. Cut into inputs for the
  segment. `gcd_steer_req` evaluates them in the uncut network.
- **rst:** one input node, a per-pin read time for each of its 423 pins.
  Free in the window.
- **Data:** free inputs, `x` throughout. Nothing depends on data values.
- **Time:** discrete GMW steps. D, W and the step size are not tied to an
  SDF here.
