# C-8w: mechanising O6 (tcheck verdicts → the capstone's bundling hypotheses)

Shard C, probe 8w, 2026-10-27. About 3 h.

STATUS: PARTIAL. The data side (1, 2) is DONE and drift-checked. The Lean bridge (3) is proved
for the physical bundling of a channel at its capture point, for both of tcheck's verdict forms.
It does NOT reach the capstone's `H_BUNDLE`, because that hypothesis is about a different trace
model. That mismatch is the main finding.

## Verdict

1. **Obligations emitted from the Lean network: done.** `formal/tools/oblgen/oblgen.py` re-runs
   C-8m's `netgen.py` into a scratch file. The run must reproduce `Formal/Net/CapstoneNet.lean`
   byte for byte (drift check). The script then parses the Lean `ops` term and checks it against
   the generator operator by operator. From that term it emits **1212 Ops-named obligations**
   (`out/obligations.tsv`):
   - 465 × H_BUNDLE, one per channel;
   - 38 H_STEER_SEL, 21 H_MUX_SEL, 1 H_MUXN_SEL;
   - for each of the 175 link stages: Sep+SetupHold, Hold and the open width;
   - for each of the 9 arbiter stages: H_ARB, H_AMERGE_RTZ, the A3 pulse, and H_FF_DRAINED where
     the stage has a delay line;
   - for each mux: H_MUX_RTZ, X4 and M3;
   - for each join: C7;
   - 42 request-line drains;
   - the H_CEL_SI premise (aggregate).

   Each record carries the Lean reference (channel or operator index, producer and consumer kind),
   the bdc Verilog instance (from bdc's own `instname`/`vname`/`linked`/`depth`) and the tcheck
   rule(s) expected to check it. Every instance name except the environment's (env:...) is present
   in the emitted `gcd_kernel.v`.
2. **Mapping to tcheck rows: done, both directions** (`out/matches.tsv`, `out/unmatched_obl.tsv`,
   `out/unmatched_rows.tsv`, `out/summary.txt`). Every row of the 4 gcd_hw routes is read:
   - files: compare5 (A, E/E0, F, J0/Jx/Jp), compare (H, I), r10k (Fd, Z, X, Xi), r10l (K, Xc, Xic,
     Xm);
   - 4572 rows in all. 4500 of them match at least one obligation.
   - **Rows with no obligation: 72, all explained.** They are rules H and I on the 9 link stages
     of the eternal source chains, × 4 seeds. H_SOURCE_ETERNAL: those values are not channels of
     CapstoneNet.
   - **Obligations a rule should check but no row does: 1.** H_MUXN_SEL of `umux21` (bdc_muxn3's
     index). No E row exists for umux21 on any route, so the select of the 3-input mux is
     unchecked by tcheck. (C-gcd_hw-hypotheses §2 says "rule E on umux21's select"; that holds
     for the project's skew.py, not for tcheck.)
   - Obligations with no rule at all: C7 (20), M3 (21) and the bus of the 3-input control merge's
     stage 1 (`acc251`: no matched delay, C-8l).
3. **Lean bridge: proved, for the physical channel.** `Formal/Timing/OblBridge.lean`:
   - `held_of_tx` is the generic form.
   - `held_of_checkArr` instantiates it with the DAG verdict (`Tcheck.verdict` is
     `decide net.WF && checkArr ..`).
   - `held_of_cert` instantiates it with the cert verdict: its hypotheses are the four conjuncts
     of `Tcheck.cverdict`.
   - `held_of_many` covers a channel checked by several instances.
   - `held_needs_close` is a counterexample showing the launch-ordering hypothesis cannot be
     dropped.

   The correspondence hypothesis is stated as a structure, **`TxCover`** (H_TXRUN).
4. **Main finding: O6 as posed has the wrong target.** The capstone's channel traces `ch`
   satisfy the cells' zero-delay data equations (`Join.dat : o.dat t = g (inputs at t)`, the
   link's H_LATCH_OPEN, ...). They therefore cannot be the physical bus, so tcheck, which talks
   about physical data arrival against physical request arrival, cannot discharge `Held (ch c)`
   directly. On those zero-delay traces H_BUNDLE is a **protocol** fact, cell by cell:
   - `Formal/Net/CapstoneBundle.lean` proves `join_held`, `fork_held`, `steer_held` and
     `src_held`;
   - 8l's `link_held` gives the link stage.

   The timing content sits in the **refinement** from the physical run to the zero-delay run. Its
   shape is stated below (R1-R4); `held_of_tx` is its R1 step.

## What checks (exact commands)

    cd /home/user/asyncfpga3/formal/lean && export PATH=$HOME/.elan/bin:$PATH
    FORMAL_SLOT_CWD=$PWD ../slot.sh lake build Formal.Timing.OblBridge Formal.Net.CapstoneBundle
    cd .. && ./check.sh Formal/Timing/OblBridge.lean Formal/Net/CapstoneBundle.lean
    python3 tools/oblgen/oblgen.py            # regenerates tools/oblgen/out/*, prints summary
    python3 tools/oblgen/oblgen.py --check    # drift check: netgen reproduces CapstoneNet.lean,
                                              # Lean ops == generator ops, out/ unchanged

RESULTS: see "Check log" at the end.

## Files (all new, all mine)

| file | what |
|---|---|
| `formal/lean/Formal/Timing/OblBridge.lean` | `TxCover` (H_TXRUN), **`held_of_tx`**, **`held_of_checkArr`**, **`held_of_cert`**, `held_of_many`, `held_needs_close` (+ `badCh`, `badCh_not_held`) |
| `formal/lean/Formal/Net/CapstoneBundle.lean` | **`join_held`**, **`fork_held`**, **`steer_held`**, **`src_held`**; `tx_of_jinv`, `tx_of_finv`, `tx_of_sinv` |
| `formal/tools/oblgen/oblgen.py` | obligation emitter + tcheck row matcher (`--check` = drift check) |
| `formal/tools/oblgen/out/obligations.tsv` | 1212 obligations: id, Ops name, Lean reference, bdc instance, expected rule, instance present in gcd_kernel.v |
| `formal/tools/oblgen/out/matches.tsv` | per matched obligation, per seed, per rule flavour: PASS / BANDFAIL / FAIL, with the worst fastG/slowG margin and the worst unguarded fast/slow margin |
| `formal/tools/oblgen/out/unmatched_obl.tsv`, `unmatched_rows.tsv`, `summary.txt` | both directions of the mismatch, classified |
| `formal/notes/C-8w-bundle.md` | this note |

No pre-existing file was edited. The Lean modules are not in `Formal.lean`; the lead adds them.

## The Lean (no sorry, no axiom, no native-decide)

**`TxCover c D R`** (H_TXRUN, the gate/timing correspondence for one channel `c`, with `D k u` /
`R k v` meaning "a data / request node of the k-th transaction's run changes at run time u / v"):
- `τ k`: launch time of transaction `k`;
- `idle`: at `τ k` the channel is idle (`req = ack = 0`);
- `count`: before `τ k` exactly `k` requests have risen (`idle` + `count` = H_LAUNCH_AFTER_CLOSE:
  the k-th token is launched after the (k-1)-th closed and before the k-th offer);
- `reqIn`: the k-th request rise is a request-node change of run `k` at `r - τ k`;
- `datIn`: every bus change is a data-node change of SOME run `k` with `τ k` not after it.

**`held_of_tx`**: `TxCover c D R`, the receiver rule `∀ t, RecvStep c t`, and per-run separation
`D k u → R k v → u ≤ v` give `Held c`. Proof: a bus change at `s` attributed to run `k` is no later
than the k-th request rise. From `τ k` (idle, count `k`) to `s` no request rises (the first rise
after `τ k` would be the k-th offer, which comes at or after `s`) and the ack cannot rise while the
request is low, so the channel is idle at `s`.

**`held_of_checkArr`** (`checkArr_sound` per run) and **`held_of_cert`** (`potOK_sound` +
`changes_in_winArr` per run; the same proof as `Tcheck.cverdict_sound`). `xverdict` (credited, C-10l)
fits `held_of_tx` the same way: its soundness theorem also concludes a per-run separation, under its
extra H_CLEAN_EDGE / H_ONE_SAMPLE_PER_WIRE / H_ALL. Not instantiated here: `Tcheck.*` lives in the
separate `formal/tools/tcheck` package, which is not built in this tree (no `.lake`), so I restated
the verdict's conjuncts against the main project's `checkArr_sound` / `potOK_sound` instead.

**`held_needs_close`**: a protocol-correct one-token channel whose bus moves mid-transaction.
The separation, `reqIn`, `datIn` and `RecvStep` all hold; only `idle`/`count` fail. So
H_LAUNCH_AFTER_CLOSE is not decoration.

**`CapstoneBundle`**: on traces that satisfy the zero-delay data fields,
`Held` of the inputs ⇒ `Held` of the output, for `Join` (any `g`; includes bjoin), `Fork`, `Steer`
and `Src`. The proofs use only the cells' handshake invariants (`JInv`, `FInv`, `SInv`: output
mid-transaction ⇒ input mid-transaction). There is no timing argument in them.

What these do NOT prove:
- that any real run meets `TxCover` (it is the correspondence hypothesis);
- the network-level "H_BUNDLE follows from the sources". Each cell lemma needs the inputs' `Held`
  at the same step, so on a cycle the dependency is circular, and mux / muxn / amerge lemmas are
  not written;
- that tcheck's front end built the right netlist (H_NETLIST, unchanged).

## Main finding: two different "H_BUNDLE"s

- **Ops H_BUNDLE** (`Held (ch c)` in `gcd_hw_circuit_safe''`). It is stated on traces where
  every bus is a zero-delay function of upstream latch contents (H_DATA_COMB, H_LATCH_COMB are
  FIELDS of `H_CELLS`). There, "the bus moves mid-transaction" can only mean "an upstream latch
  changed while this channel was busy": an event-order property. `join_held` / `fork_held` /
  `steer_held` / `src_held` / `link_held` show it propagates through every cell kind except mux,
  muxn and arbiter (not attempted). No delay number can confirm or refute it.
- **Physical bundling** (LIBRARY.md's "data stable from req↑ to ack↓", at the capture pins). This
  is what tcheck checks, and what `held_of_tx` delivers from tcheck's verdicts.

So "discharge H_BUNDLE(c) by tcheck" is a category error for the capstone as stated. What tcheck
can discharge is the refinement from the physical circuit to the zero-delay model, which the
hypothesis list files under H_DATA_COMB / H_LATCH_COMB ("C: discharged channel by channel by §3").
That refinement is not stated anywhere in the capstone. Stated precisely, it is:

- **R1, capture bundling.** At every capture point, the physical channel is Held. Proved here from
  tcheck (A for compute, mux and arbiter outputs into a link; E for steer/mux selects at the LUT),
  under `TxCover`.
- **R2, settled value.** At the request's arrival the physical bus equals the zero-delay value of
  its cone. This follows from the Run semantics: after the last data change, H_ZERO_DELAY_FN +
  BoundedDelay.settle make every node `g` of its settled pins. That holds IF the data side's
  changes all precede the request, which is A's separation again. Not mechanised here.
- **R3, latch.** The physical latch closes on that value and holds it until the next open. These
  are the link's Sep/SetupHold (rule I) and Hold (rule H), plus the open width (W), i.e.
  H_LATCH_COMB's two halves.
- **R4, control.** Each control LUT that reads data (the steer branch AND, the mux joins) reads
  the settled select (E), and the arbiter's grant reaches both of its clients consistently (J).

With R1-R4, the physical run's req/ack traces plus the zero-delay buses form an Ops run meeting
H_CELLS. The capstone then applies, and its H_BUNDLE is a protocol consequence (modulo the
network-level closure above). I did not prove this composition. It is the honest replacement for
O6.

**Gate/timing-model correspondence (H_TXRUN), the hard part.** `TxCover` is a per-transaction
windowing of a single-launch semantics, and Run's **H_QUIESCENT** must hold at every launch: the
previous transaction's waves have died out before the next one starts.
- **Data side.** This follows from the previous transaction's own A separation plus
  H_LAUNCH_AFTER_CLOSE: all data changes of run k-1 precede req↑ of k-1, which precedes τ k.
- **Request side.** The return-to-zero wave through the matched delay line must have drained.
  - For FASTFALL lines (the 29 comp/arbiter/muxn lines) that is exactly rule F/Fd (H_FF_DRAINED).
    oblgen therefore maps F/Fd to `H_QUIESCENT_REQ` of the channel's A instance.
  - For the 21 plain bd_mux lines (FASTFALL = 0, checked in gcd_kernel.v) it is argued from the
    protocol: a plain chain's tail falls last. It is not checked.
- **H_BUNDLED_T0 (A, bundled form).** It says all of a cell's input boundary nets launch together.
  It is another TxCover premise and the open composition step of C-gcd_hw §3.

## Which capstone hypotheses are discharged, and on which route

"Discharged on route X" below means: the tcheck verdict passes at fastG and slowG (H_ONE_CORNER +
the 0.772/1.155 band), so by `held_of_checkArr` / `held_of_cert` the PHYSICAL obligation holds on
that route under `TxCover` and tcheck's global hypotheses (H_NETLIST, H_RC_EXACT,
H_FALLBACK_BAND, H_BIDIR, the Run semantics, the per-rule shape hypotheses). Unguarded = the plain
fast and slow corners. Per-obligation, per-seed verdicts are in `out/matches.tsv`.

| capstone hypothesis (Ops name) | n | checked by | d | 2 | 3 | 4 | status |
|---|---|---|---|---|---|---|---|
| physical bundling (R1) of compute / mux / arbiter outputs | 50 | A | 50/50 | 50/50 | 49/50 | 50/50 | discharged except seed 3 `ushrsi1` (g74.0): −339 ps fastG (unguarded +2340). Needs TxCover + H_BUNDLED_T0 |
| request-line drain (TxCover's H_QUIESCENT) for those 50 | 29 rows | F / Fd | ucmpi8: F fails, Fd passes | ok | cm12: F and Fd fail | cm12 F and Fd, ushrsi3 Fd fail | band-only failures. The 21 plain mux lines: argued, unchecked |
| H_STEER_SEL (38 branches; select part of `jL`) | 38 | E (and E0) | ok | ok | ok | ok | discharged on all 4 (worst +2179 ps E, +1777 E0) |
| H_MUX_SEL (21 two-input muxes) | 21 | E | g203.1 | g91.2 | g91.2 | g62.1, g89.2 | band-only failures (worst −603). E0 fails 10 pairs |
| H_MUXN_SEL (umux21) | 1 | none | | | | | **OPEN: no tcheck row** |
| bus of cm12 stage 1 (`acc251`) | 1 | none | | | | | **OPEN** (C-8l: no matched delay) |
| Sep+SetupHold (H_LATCH_COMB setup) | 170 (+5 W=0, vacuous) | I | ok | ok | ok | ok | discharged where computed (680 (stage, seed) pairs, worst +213). Many I rows are "not audited" by the project but carry tcheck numbers |
| Hold (H_LATCH_COMB hold) | 170 (+5 W=0) | H | g145.1→g145.2 | g209.1→g209.2 | ok | ok | band-only failures (worst −207) |
| open width | 175 | W (aggregate only) | min +476 fastG | ok | ok | ok | discharged in aggregate; no per-stage rows on disk |
| H_ARB (A0 fork) | 9 | Jx | ok | ok | ok | cm12.uarb2 −9 | band-only; J0/Jp fail 10 pairs (no credit) |
| H_AMERGE_RTZ | 9 | Z | ok | ok | ok | ok | discharged (worst +383) |
| A3 pulse (arbiter) | 9 | X/Xc/Xm | ok | ok | ok | ok | discharged (worst +970) |
| H_MUX_RTZ | 22 | X, Xc, Xm, Xi, Xic | X fails, credited pass | | | | discharged under credit (Xic: 0 failures; Xc/Xm: umux11 fails band on all 4) |
| X4 (ctl_req → uj fork) | 21 | K | 11 muxes FAIL unguarded | | | | **FAILS on every route even unguarded** (worst −9473 ps). Either the K model is too pessimistic or X4 is violated; C-10l left this undiscussed |
| M3, C7 | 21, 20 | none | | | | | OPEN |
| H_CEL_SI premise (C2) | all C-elements | R/Rc aggregate | | | | | kernel ok; rig uenv1 band-only (C-10f) |
| capstone `H_BUNDLE` on its zero-delay traces | 465 | not a timing obligation | | | | | per cell a protocol fact (join/fork/steer/src/link proved); network closure OPEN |

## Unmatched, both directions (exact; from out/summary.txt)

- **Rows with no obligation: 72.** H and I on the 9 eternal-chain link stages (`ulink_n36__0..2`,
  `n68__0/1`, `n94__0/1`, `n155__0/1`), × 4 seeds. They are not channels of CapstoneNet
  (H_SOURCE_ETERNAL). They are checked by tcheck but invisible to the capstone, which needs them
  only for liveness.
- **Obligations a rule should check that have no row: 1** (H_MUXN_SEL, umux21).
- **Obligations with no rule:**
  - 20 C7, 21 M3, 1 `acc251`.
  - The 21 plain-line drains, argued instead of checked.
  - W and R, which tcheck reports only as per-route minima (`results/unchecked3.tsv`): 175 + 1
    aggregate obligations whose per-row results are not on disk.
- Not rows by design: the 376 H_BUNDLE obligations whose class is derived (fork, link, steer,
  src) or ghost (W = 0), and the Sep/Hold of the 5 W = 0 pipe stage[0]s. tighten's `latch_data_pins`
  is empty there, so extract.py skips them.

## Fidelity

| model | grade | why |
|---|---|---|
| obligation list (oblgen) | A while `--check` passes | generated from the Lean term; drift-checked against netgen; every instance name found in gcd_kernel.v |
| row ↔ obligation matching | B | by instance-name prefix and rule letter; the rule→obligation table is mine, from C-gcd_hw §3 and C-10g/10k/10l |
| `TxCover` (H_TXRUN) | B as a hypothesis | the per-transaction windowing is how every tcheck rule is meant; its H_QUIESCENT and H_BUNDLED_T0 parts are the weak points |
| `RecvStep c` in the bridge | A in the circuit, but see below | the consumer's ack rises only while req is high |
| zero-delay propagation lemmas | A (proved) | exact consequences of the Ops gate models |

**`RecvStep` is a separate hypothesis on purpose.** The capstone derives `Protocol` from H_CELLS
**and H_BUNDLE** (`net_protocol`). Using that derivation to obtain H_BUNDLE would be circular. A
time-bounded `net_protocol` (Held up to t ⇒ protocol up to t) would remove it.

## Surprises

- The capstone's H_BUNDLE carries no timing at all. Every cell lemma is two lines plus a Boolean
  case split. The timing obligations belong to the refinement physical → zero-delay, which was
  never written down.
- tcheck's K (X4) rows fail by microseconds on 11 of 21 muxes on every route, even unguarded.
  Either the K late-side model is wrong (the select's latch-enable cut, H_LATCH_D), or B's X4 is
  really violated on silicon. Nobody has looked; the C-10l note's Results section is empty.
- umux21's select has no tcheck row, although the hypothesis list says rule E covers it.
- 9 linked stages (eternal chains) are checked by tcheck and absent from the capstone network.

## Check log

(filled in after the runs; see below)
