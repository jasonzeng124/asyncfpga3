# B probe Bx2: early ack, tie + ack, shared O5/O6 reads, certificate generator

File: `formal/lean/Formal/Cells/TernaryOnBits2.lean` (964 lines, core Lean, no Mathlib).
It imports only `Formal.Cells.TernaryOnBits` (Bx), read-only. Bx's olean was missing; it was
compiled with the command in the brief (`lean ... -o .lake/build/lib/lean/Formal/Cells/TernaryOnBits.olean`),
about 30 s. Nothing else was rebuilt. No shared definitions were added outside this file.

Check (clean: no errors; only `if_neg`-deprecation and one unused-name lint warning;
about 50 s user, 60 s wall):

    cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/TernaryOnBits2.lean

`python3 formal/scan.py lean/Formal/Cells/TernaryOnBits2.lean`: clean (no sorry, admit, axiom,
native_decide, bv_decide). `#print axioms`, run on a scratch file importing the compiled module:
- decided certificates and witness facts (`cert2_s*`, `neg_no_early_ack`, `wB_s1`, `tie_s1`,
  `slow_pin_s1`): `[propext]`;
- `txn2`, `early_ack_latched`, `early_ack_runt`, `tie_ack_both`, `bx_witness_overlap`,
  `bx_witness_not_sync`: `[propext, Quot.sound]`;
- `contested_sync`, `contested_sync_s1`: `[propext, Classical.choice, Quot.sound]`. The choice comes
  only from the `→` direction, which reuses Bx's `contested_exact`, which uses 7l's construction.
  The new witness itself is choice-free.

Decides use `decide +kernel`, as in Bx. Costs:
- `cert2_s*`: about 10 s per seed, generator included;
- `neg_no_early_ack`: about 10 s;
- every other decide: under 1 s.

Bitstreams: the same four routed `link_arb` bitstreams as Bx (C-11c `FasmLink.S1..S4`,
seeds 1..4, nextpnr sha256 `9c732bc6303458df`, `toolchain.sh` ok as stamped by C). This probe
routed nothing.

## Model (unchanged from Bx, plus two additions)

- **Network and runs.** The network is Bx's `circ`: the whole physical netlist as one 7f
  `Circ`. Nodes 0..8 are the ports A0, ack_out, d0..2, r1, r2, req_in, rst. Node `9+2i` is O6
  and node `10+2i` is O5 of LUT `i`. The runs are 7f's `Run` / `Bounded`.
- **New: fixed-delay transport runs** `dv N e L inp c` / `dRun`.
  - Pin `p` of gate `n` reads the state of step `k - e n p`, so every routed pin has its own
    FIXED transport delay `e n p ≤ L`. Every gate takes its LUT value one step later.
  - The state is a history list of the last `L+1` steps, so the kernel can evaluate it.
  - Proved: it is a 7f `Run` (`dRun`), `Bounded … 0 L` (`dRun_bounded`), and FIFO
    (`dRun_fifo`).
  - Proved: if the inputs are constant from `t0` and the history repeats with period `P`, the
    run is periodic for ever (`hist_period`, `dv_period`, `dv_reduce`). This gives
    `dv_never` (period 2, two values: never settles), `dv_settle` and `dv_true2`.
  - All infinite-time claims about the witnesses come from a decided finite prefix plus this
    periodicity lemma. Nothing is "simulated and trusted".
- **New: H_LUT62_SHARED_READ** (`SiteSync N R`). For every site `i` and every pin `p < 5`,
  the read times of O6 (`pidx i .o6`) and O5 (`pidx i .o5`) are equal.
  - **Physical fact:** O5 and O6 are taps of one mux tree behind one input buffer per pin
    A1..A5. The residual skew inside the tree is ignored.
  - **Test:** on GLS or the board, drive one pin of a fractured LUT and measure the O5-vs-O6
    delta; it must stay below one model step.
  - `sync_of_site`: any delay function that depends only on the site and the pin index gives
    `SiteSync`.

## (1) The two missing scenarios, all four seeds

**Schedule.** `specs2` has 16 phases. Phases 0..8 are Bx's: reset, release, link transaction,
then client 1's r1 up, A0 up, r1 down. The rest:

| phase | window | A table (moves) | B table (after) |
|---|---|---|---|
| 9 | r2 up while A0 = 1 (client 2 **waits**) | only r2. q is frozen by A0, so g2 = r2·~q stays 0 (hazard-free) | r2 = 1, all else unchanged |
| 10 | **A0 falls, client 2 waiting** | A0, A1, A2, q, g2, R0 are x | A1 = 0, q = 0, g2 = R0 = 1, **A2 = x** |
| 11 | A0 rises (the server serves client 2) | A0, A2 | A2 = 1 |
| 12, 13 | r2 down, A0 down | — | idle, q = 0 |
| 14 | **tie**: r1 and r2 rise in one window | q, g1, g2, R0 are x; acks 0 | q, g1, g2 = x; R0 = 1 (Kleene: q + ~q) |
| 15 | **server ack after the tie** | A0, A1, A2, q, g1, g2 are x | **A1 = A2 = x** |

- **Tables.** `expTables2` was written from the cell equations (q = rst + C(r1,~r2) frozen while
  A0 = 1; g1 = r1·q; g2 = r2·~q; R0 = r1·q + r2·~q; A_k = C(g_k, A0)) before any run. It matched
  the generated certificates on all four seeds on the first try.
- **Theorems.**
  - `cert2_s1..s4` decide `certB S specs2 (gen (circ S.net) specs2) expTables2`.
  - `txn2` (generic in the seed) is the soundness statement: every bounded run that follows
    `specs2` with `TimesOK` times is covered by `expTables2`. The per-seed forms are
    `txn2_s1..s4`.
- **Negative control.** `neg_no_early_ack`: claiming that A2 stays 0 in the A0-fall window is
  refuted on seed 1.

### Early ack: explicit runs, and which pins carry it

7l's exactness promises *some* run for every `x`. Instead of instantiating 7l's `wv`, which
needs non-FIFO reads, I built explicit runs that are better behaved:
- one clean A0 edge;
- FIXED per-wire delays;
- FIFO;
- shared O5/O6 reads.

Setup:
- **Start:** `wait_k`, the phase-9 state. `wB` checks that it is binary, stable under every
  LUT, and equal to the phase-9 B table on all 19 logical nodes. In it, client 1 is done
  (A1 = 1), client 2 waits (r2 = 1), A0 = 1 and q = 1.
- **Inputs:** A0 falls at step 1 and stays 0 for ever. The server never acknowledges.
- **Delays:** every pin has delay 1, except the pins of **ua2's site that read A0**, which have
  delay `L` (`eA`).

Results:
- `early_ack_latched` (`L = 8`): A2 = 0 up to step 6, then **A2 = 1 from step 16 for ever**,
  with A0 = 0 since step 1. In the run A2 rises at step 7. Client 2 is acknowledged by a server
  that never acknowledged.
- `early_ack_runt` (`L = 6`): **A2 never settles.** A 1-step overlap leaves a pulse in ua2's
  feedback loop. This is the binary shadow of a runt into the C-element, and it matches the
  B-table `x` on A2.
- Both hold on all 4 seeds (`wB_s1..s4`; generic theorems instantiated as `example`s).

**The race.** The A0 branch into ua2 loses to the chain A0 → ustate (q falls) → ugrant (g2
rises) → ua2. That chain is 3 gate steps and 3 unit wires. With every other wire at 1 step, a
branch delay of 6 already gives a never-settling A2, and 8 gives a latched early ack. This
agrees with 7g (`ArbA0Fork`): early ack iff the ua2 branch is slower than the chain.

**The physical pin** (`slow_pin_s*`, decided: exactly one pin of ua2's site reads A0):

| seed | ua2 = A2 node | LUT / site | A0 pin on ua2 (slow branch) | A0 pin on ustate (fast branch) |
|---|---|---|---|---|
| 1 | 21 | LUT 6, SLICE_X42Y95 | A2 (index 1) | LUT 3 SLICE_X42Y94, A2 |
| 2 | 21 | LUT 6, SLICE_X42Y92 | A1 (index 0) | LUT 4 SLICE_X42Y89, A4 |
| 3 | 15 | LUT 3, SLICE_X43Y93 | A2 (index 1) | LUT 4 SLICE_X42Y93, A4 |
| 4 | 17 | LUT 4, SLICE_X43Y91 | A1 (index 0) | LUT 3 SLICE_X42Y88, A2 |

The ustate column was read from the netlist dump; it is not a theorem. What carries the early
ack is the A0 fork: branch (ustate pin) against branch (ua2 pin). On the board this is the
routed-delay difference between these two site pins of the A0 net. That difference is the
quantity H_A0_FORK must bound.

### Tie followed by a server ack: the acks latch, both of them

`tie_ack_both`:
- **Start:** Bx's idle state (checked by `contestB`).
- **Inputs:** r2 rises at step 1 and r1 at step 2. A0 rises at step 10; R0 has been 1 since
  step 4, so the server's ack is legal.
- **Delays:** 1 step everywhere except the two ack sites (ua1, ua2), whose pins have delay 2
  (`eT`).
- **Conclusion:**
  - q, g1 and g2 never settle;
  - A1 = A2 = 0 before step 10;
  - **A1 = A2 = 1 from step 18 for ever.**

So the B-table `x` on both acks after a tie is realised as a mutual-exclusion failure: both
clients acknowledged, permanently, by one server ack. The bounded run has clean edges, FIFO
wires, fixed delays and shared reads. With uniform delay 1 everywhere (not in the file), the
acks oscillate in antiphase instead of latching.

## (2) Shared O5/O6 reads: what changes

- **Universal results are unchanged.** A `SiteSync` run is a run. Bx's `reset_s*`, `txn_s*`,
  the soundness halves of `contested_*`, and this file's `txn2`, therefore all hold for
  shared-read runs verbatim.
- **Existential results must be rebuilt.** Bx has one: the `←` direction of
  `contested_exact` / `contested_exact_fifo`.
- **Bx's witness is outside the class.** `bx_witness_overlap` (seed 1; decided `ov_s1..s4`):
  in Bx's run (7l's `wv`), g1 = g2 = 0 at step 6 and g1 = g2 = 1 at step 7. So at step 6 both
  grant outputs took a fresh LUT value 1. `bx_witness_not_sync` (all seeds via `ov_s*`): no
  `Run` of that trace satisfies `SiteSync`.
  - **Proof:** with equal reads on A1..A5, O5 reads the first five bits of O6's pin vector.
    `exclB` decides, over all completions of the grant site's tie pins, that the physical grant
    INIT never gives O5 = O6 = 1.
  - **Meaning:** Bx's witness shows both grants high, which one shared q read cannot produce.
    A GMW run with shared reads can still show g1 = g2 = 1 when the two outputs update at
    different steps (the handover overlap of ARBITER.md). This theorem rules out only
    simultaneous fresh evaluation.
- **The contested iff survives, with a new witness.** `contested_sync` (all seeds): for every
  physical gate node `n`, some bounded run with **shared reads, FIFO wires** and inputs inside
  `uC`, final from step 2, never settles at `n` iff `n` ∈ {q, g1, g2}.
  - The witness has delay exactly 1 on every wire, unit gate delay, and r2 rising one step
    before r1. One clean edge each.
  - q's transport loop carries a 1-step pulse for ever. The two grants decode the same q read,
    and **are never both 1** (`cv_excl`).
  - This witness is FIFO with clean edges and bounded gates, a combination 7l left open in
    general (its two witnesses each drop one of these). Here it is obtained for this netlist by
    a one-step input skew.
  - Because every wire has the same delay, the run splits into two independent parity chains.
    That is a property of this witness, not of the circuit.
- **Not checked: per-node exactness of every `x` in the A/B tables under `SiteSync`.** Bx did
  not claim it either. Under shared reads some table `x`'s could in principle become
  unrealisable, wherever the realisation needs O5 and O6 of one site to disagree on a shared
  pin at the same step. Candidates: the latch site, whose O5 and O6 read each other, and the
  grant site. For the arbiter `x`'s the explicit runs above show that q, g1, g2, A2 and both
  acks remain realisable.

## (3) The certificate generator (no `#eval` needed)

The generator is a definition in the file: `gen N sp = genCerts N 8 sp (all-x)`.
- **Algorithm A.** `fixA` runs `l ↦ joinL l (stepL N u l)` from the previous phase's B result
  and stops early at a fixed point.
- **Algorithm B.** `iterL N a M` (`M = 3`) from the A state.

The output is never trusted: `certB` (Bx) re-checks closure, recomputes B, checks the links
and compares the tables. `gen` reproduces Bx's literal `cert1` exactly (checked by `#eval`
during development).

To re-run the checker on another design that C imports:
1. Get the design's `PNet` from C's importer (`formal/fasm2lean2`, see C-11c), e.g.
   `Formal.Net.FasmLink.Sx.net`. The network is `circ net`. Ports are nodes `0 .. 8`, and
   `circ` hard-codes 9 ports (`pidx`, `circ`): a design with a different port count needs a copy
   of `circ` with that constant changed.
2. Write the schedule as `List Spec` (`u` with `x` exactly on the changing inputs; `a` final),
   in the design's port order.
3. Physical-level check (no logical map needed): in a scratch file,

       theorem c : chk (circ net) M (specs.zip (gen (circ net) specs)) = true := by decide +kernel

   then apply `TernaryOnBits.build_good` and `good_holds` (generic in the `Circ`). This gives
   7i's `Good` / `HoldsL` on physical nodes.
4. Logical-level check (as here): this also needs a Bn-style `Seed` with a map `Seed.m` to
   logical nodes. `logical`, `certB` and `HoldsT` are tied to Bn's 19 `link_arb` nodes.
5. To print the generated tables while writing the expected ones (do NOT paste them into the
   expected tables; write those from the spec and compare), compile this module to an olean
   outside the repo and `#eval` in a scratch file. The exact commands used:

       SP=<scratch dir>; cp -rs /home/user/asyncfpga3/formal/lean/.lake/build/lib/lean $SP/olean
       cd /home/user/asyncfpga3/formal/lean
       LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/TernaryOnBits2.lean \
         -o $SP/olean/Formal/Cells/TernaryOnBits2.olean
       LEAN_PATH=$SP/olean ../slot.sh lean $SP/print.lean

   `print.lean`:

       import Formal.Cells.TernaryOnBits2
       open Formal.Cells Formal.Cells.TernaryOnBits Formal.Cells.TernaryOnBits2
       def k3s : K3 → String | .t => "t" | .f => "f" | .x => "x"
       def ls (l : List K3) : String := String.join (l.map k3s)
       #eval (gen (circ seed1.net) specs2).map (fun (a, b) => (ls (logical seed1 a), ls (logical seed1 b)))

   (A symlinked copy of the build tree is needed because Lean resolves the `Formal` package
   from the first `LEAN_PATH` entry that contains it.)
6. Explicit witnesses for another design: `dv` / `dRun` take any `Circ`, delay function
   `e ≤ L`, input trace and start list. A delay function of the site and pin gives `SiteSync`
   (`sync_of_site`). Decide a finite prefix plus `hist (T+P) = hist T`, then use
   `dv_never` / `dv_settle` / `dv_true2`.

## What did not work / limits

- **No 7l iff for the A0-fall window.** The `A_exact` / `B_exact` "x iff some run moves / never
  settles" for every node was not instantiated for phases 10 and 15, only explicit runs at A2
  (and at both acks for the tie). It is mechanical: generalise Bx's `contestB` over `u` and `a`,
  about 30 min. For phase 15 it is not directly available, because 7l needs a binary stable
  start and phase 15 starts from q = x. `tie_ack_both` is a two-window explicit run instead.
- **Not tied to the schedule.** The explicit runs start from checked states (`wB`: stable and
  equal to the phase-9 B table; `contestB`: phase 9 of Bx). They are not proved to satisfy
  `Follows` for `specs2`, but their inputs are stated exactly.
- **Delays are in model steps.** "8 steps on the ua2 A0 branch versus 1 elsewhere" is a
  witness, not a measured delay. Whether the routed A0 fork can be that skewed is 7g's
  question; the table above names the pins to measure.
- **Same limits as Bx.**
  - The witnesses need transport delays: they carry 1-step pulses, and inertial wires would
    swallow them.
  - Mid-rail levels and metastability are outside the binary model; "never settles" is the
    binary shadow of metastability.
  - The environment is open, and `TimesOK` spacing is assumed.
- **Kernel cost.** The whole file is 50 s user (Bx: 31 s). Most of it is `cert2_s*` and
  `neg_no_early_ack`, which run the generator inside the kernel. Bx-style literal certificates
  printed from `gen` would cut this to about 4–5 s per seed, at the price of literal blobs.

## Verdict

**Works.** All three asks are done and check clean on all four seeds:
1. **The two scenarios.**
   - Soundness tables: A2 is `x` after the A0 fall; both acks are `x` after tie + ack.
   - Explicit bounded runs: a latched early ack, a never-settling A2, and both acks latched
     after a tie.
   - The pins are named: the A0 branch into ua2's site, at the given pin per seed.
2. **Shared O5/O6 reads.**
   - Universal results unchanged.
   - Bx's contested witness provably outside the class.
   - The contested iff re-proved with a shared-read FIFO fixed-delay witness.
3. **The generator** is a checked Lean definition, and the re-run recipe is above.

What it buys:
- The early-ack defect and the tie+ack exclusion failure are realised on the real routed bits
  of all four seeds, by runs whose only liberty is a fixed per-wire delay.
- The A0-fork skew is reduced to one named pair of physical pins per seed, to measure.

To extend:
- per-node 7l iff for any window: about 30 min each;
- a generic port count in `circ`: about 1 h;
- `Follows` proofs for the explicit runs: about 1 h.

## Fidelity per primitive

- **LUT6 / LUT6_2.**
  - The physical INIT on the physical routed pins, from the bits; the ternary side is `lutK`
    (H_KLEENE_LUT), the binary side `lutB` / GMW.
  - O5 is `INIT[31:0]` on A1..A5.
  - **New:** `SiteSync` optionally ties O5's and O6's reads of A1..A5 together. All witnesses
    in this file satisfy it. Skew after the shared input buffer is ignored.
- **Routing.**
  - Soundness: one read time per (gate, pin), at most `W` old (7f).
  - Witnesses: a fixed transport delay per (gate, pin), FIFO.
- **Feedback** (C-element, latch, arbiter q). A routed pin from the LUT's own output, with
  delay 1 in the witnesses (2 on the ack sites in `tie_ack_both`).
- **Ties.** Constants (H_TIE). `exclB` enumerates completions with the tie pins fixed.
- **IOB / IOI.** Ports are input nodes (C-11c's bypass). Witness inputs make one clean edge
  per changing input.
- **Gates in the witnesses.** Unit delay, always taking the fresh LUT value (`D = 0`).
- **Time.** Discrete steps.
