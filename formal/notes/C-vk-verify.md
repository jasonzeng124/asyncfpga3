# C-vk: `verify.sh`, one command from a kernel to a proof or a counterexample

Probe C-vk, 2026-10-29. North-star goal 3 ("given any routed design from this flow, it proves
it correct or prints a counterexample trace"). Tool: `formal/tools/verify/`. Before this probe
the pieces existed separately (dfimport, the hand-written token proofs, capnet, tcheck,
C-10n's how-to `formal/notes/C-howto-new-kernel.md`). There was no single entry point, and the
token level printed no counterexample.

## Run it

    export PATH=$HOME/.elan/bin:$PATH
    formal/tools/verify/verify.sh gcd                      # ~10 min (Lean on gcd's 1174-line file)
    formal/tools/verify/verify.sh ipow --route build/verify/routes/ipow/s1   # + timing on a route
    formal/tools/verify/verify.sh ipow --mlir mutant.mlir  # any MLIR in place of the fixture
    formal/tools/verify/verify.sh ipow --c other.c         # any C reference in place of kernels/<k>/<k>.c
    formal/tools/verify/verify.sh xorshift --no-lean       # seconds: search only
    formal/tools/verify/selftest.sh [--quick]              # positives + negative controls

Exit code: 0 = PASS (a token-level theorem for ALL inputs checked on this MLIR, nothing FAILed),
1 = FAIL (a counterexample or a failed check is printed), 2 = not proved for all inputs (no
counterexample; at best the per-vector theorems of stage 2d). Work files go to
`build/verify/<kernel>-<time>/` (gitignored; `--out DIR` to choose).

## What each stage proves, and what it does not

| stage | engine | PASS proves | does NOT cover |
|---|---|---|---|
| 1 import | `dfimport/mlir2lean.py` (C-8i, called unchanged) | bdc's own parser, fusion plan and lowering accept the MLIR; the exported graph equals the committed `Formal/Net/<K>Hw*.lean`, or differs (printed) | bdc's Verilog emission; H_SOURCE_ETERNAL (source/constant chains as always-valid channels) |
| 2a lean | `leanstage.py`: fresh graph + certificates + the committed hand proof, in ONE file, `slot.sh lake env lean`, axioms audited | the hand theorem (`gcd_hw_graph_computes_gcdC`, `ipow_hw_graph_computes_ipowC`, `collatz_hw_graph_computes_collatzC`) holds for the graph THIS MLIR produces: every complete run, any schedule and arbiter outcome, ends with the transcription's result | that the transcription is the C (2c tests it); termination of the C; gates, delays, cells |
| 2b search | `tokensearch.py`: BFS over every interleaving, persistent-set reduction, Python copy of `Rule.fire` | on each listed vector, every terminal store is exactly `[C result]` on the output and the end token, and no schedule runs forever | other inputs; the Python semantics is a transcription (2d removes that trust) |
| 2d vectors | `vecgen.py`: one generated Lean theorem per vector, no hand proof | on each vector, EVERY complete run ends with exactly the compiled C's value (witness schedule re-executed by the Lean kernel + C-8i's `determinate`). Works for any kernel dfimport accepts | other inputs |
| 2c transcr | `#eval` of the hand transcription vs the compiled C | agreement on the vectors | other inputs (testing, not proof) |
| 3 circuit | `capstage.py`: capnet (C-8y, called unchanged) regenerates links/ring/net from THIS MLIR | the committed circuit theorem (`gcd_hw_circuit_safe3`, `ipow_circuit_safe3`) is about exactly this network, its module is up to date, axioms audited | its hypotheses (H_CELLS, H_BUNDLE, H_START_ONCE); routed delays; bits |
| 4 timing | `tstage.py`: tcheck snapshot (sync.sh --check, self-tests), on `obl.tc(.gz)` or a pnr dir (extract.py first) | every fastG/slowG obligation row PASSes `Tcheck.verdict_sound` | the front end (extract.py) is untrusted; fallback-band arcs; one route is a sample |

C reference: `cref.py` compiles `kernels/<k>/<k>.c` unchanged (gcc -O0 -fwrapv, `CALL_KERNEL`
stubbed, the file's `main` renamed) with a generated harness. Expected values therefore come
from the C, never from a circuit run or from the MLIR. gcd has no `kernels/gcd/gcd.c` (its C is
Dynamatic's binary gcd, not in the repo), so `formal/tools/verify/ref/gcd.c` is textbook Euclid:
a different algorithm, used on 0 <= a, b < 2^31 only.

Counterexamples are printed as: the input, the C value, the output token(s) this schedule
ends with, the channels that differ from the expected final store, and the schedule, one firing
per line (rule number, kind, bdc op name, tokens taken and given, by channel number and bdc SSA
name). For an infinite run it prints the schedule up to a store that repeats, then the loop.

Files: `verify.sh` (wrapper) -> `verify.py` (driver); `kernels.py` (per-kernel table); `cref.py`;
`tokensearch.py`; `leanstage.py`; `vecgen.py`; `capstage.py`; `tstage.py`; `mutate.py` (negative-control
mutants); `route.sh` (kcheck's route flow, own build dir); `selftest.sh`; `ref/gcd.c`;
`test/ipow_wrong.c`, `test/pass.tc`. A sample generated per-vector theorem file is kept in
`formal/lean/Wip/Cvk/XorshiftHwVec0.lean`. It is WIP, not claimed: verify regenerates and checks these
files on every run, and they are not under `Formal/`.

## Adding a kernel

One entry in `formal/tools/verify/kernels.py`: fixture name, C file and function, vectors (avoid
degenerate ones), domain, Lean names (K, ns, dfimport naming options), and optionally the hand
proof (file, theorem, a Lean term evaluating the transcription) and the capstone (capnet
profile, module, theorem, generated files). With only the first group, stages 1, 2b and 2d run
and give per-vector theorems or a counterexample; an all-inputs theorem needs a hand proof
(follow `Formal/Net/IpowHwProof.lean`), and the circuit level needs a capnet profile.

## Results (2026-10-29, `formal/tools/verify/selftest.sh` plus the runs named)

The last full `selftest.sh` run (log: build/verify/selftest/*.log) printed `ok` for every case
except gcd and the equivalent mutant. Both were then fixed in vecgen.py (`maxHeartbeats 0` for a
392-firing witness) and verify.py (a 2a-only FAIL now means NOT PROVED), and re-run alone with the
final code: gcd exit 0, the equivalent mutant exit 2, both as the selftest expects. Nobody has run the
whole selftest again end to end since those fixes. Wall time on the shared 4-core machine: gcd ~35 min
(2a ~8 min, 2d ~3 min per vector, one Lean process at a time through slot.sh), ipow/collatz/xorshift
~10-15 min each, `--no-lean` runs seconds; `selftest.sh --quick` is ~1 min.

All Lean through `formal/slot.sh`, Lean 4.35.0, core only (imports `Formal.Net.GcdHwLib`; the
circuit stage imports the committed capstone modules). Every theorem's `#print axioms` is
checked to be within {propext, Classical.choice, Quot.sound}.

| run | 1 | 2a | 2b | 2d | 2c | 3 | 4 | verdict |
|---|---|---|---|---|---|---|---|---|
| gcd | PASS | PASS | PASS | PASS 8/8 (9th not attempted: witness 1384 firings > 600) | PASS | PASS | PASS (toy `test/pass.tc`) | PASS |
| ipow | PASS | PASS | PASS | PASS 9/9 | PASS | PASS | - | PASS |
| collatz | PASS | PASS | PASS | PASS 5/5 | PASS | SKIP (no capnet profile) | - | PASS |
| xorshift | PASS (new kernel) | SKIP (no hand proof) | PASS | PASS 5/5 | SKIP | SKIP | - | proved on the 5 vectors only (exit 2) |
| NEG gcd, subi1 operands swapped | PASS (drift) | FAIL | **FAIL: cex** | 1/3 | - | FAIL (net differs) | - | FAIL |
| NEG ipow vs wrong C (`test/ipow_wrong.c`) | PASS | PASS | **FAIL: cex** | FAIL | **FAIL: cex** | - | - | FAIL |
| NEG ipow, shift constant 1 -> 2 | PASS (drift) | FAIL | **FAIL: cex** | FAIL | - | FAIL (net differs) | - | FAIL |
| NEG timing (tcheck `toy.tc`) | | | | | | | **FAIL: 2 rows** | FAIL |
| equivalent mutant gcd subi0 swapped | PASS (drift) | FAIL | PASS | PASS 3/3 | - | - | - | NOT PROVED (exit 2) |
| ipow + 4 routed seeds | PASS | PASS | PASS | PASS 9/9 | PASS | SKIP (IpowCapMain .olean stale at that moment: other probes' files changed; it was PASS 40 min earlier) | **FAIL** (below) | FAIL |

Search sizes (persistent-set reduced; every cm in these graphs is uncontested, so the reduced
graph is one path): gcd 12-1385 states per vector, ipow 16-124. Unreduced, ipow (3,33) has
68574 states / 265541 edges and gives the same terminal stores as the reduced search (checked in
`selftest.sh` on 3 vectors); unreduced gcd did not finish within 2 minutes (state explosion), which
is why the reduction exists.

### Sample counterexamples

Wrong C reference (`--c test/ipow_wrong.c`, loop test `e > 1`):

    COUNTEREXAMPLE  input (3,7)
      C reference (ipow_wrong.c:ipow) returns 27  (as the 32-bit output token: 27)
      this schedule ends with out = [2187]  (signed: [2187])
      channels that differ from the expected final store: 57:34 has [2187], expected [27]
      schedule (69 firings; terminal: no rule enabled):
         1. rule   0 fork   [fork0]  takes 2:arg2=0  gives 3:0#0=0, 4:0#1=0, 5:0#2=0
         2. rule   1 fork   [fork1]  takes 1:arg1=7  gives 6:1#0=7, 7:1#1=7
         ...
        68. rule  34 mux    [mux3]  takes 56:index_15=1, 54:falseResult_11=2187  gives 57:34=2187
        69. rule  37 sink   [sink4]  takes 58:result_14=0  gives -
      final store: 4:0#1=[0], 57:34=[2187]
    [2c transcr] FAIL   (3,7): Lean transcription some 2187, compiled C some 27

Stage 2a still PASSes here, correctly: the hand theorem is about the Lean transcription, and the
transcription is right; 2b and 2c catch that the C file says something else.

Mutated MLIR (gcd, `subi1` = `0 - diff` became `diff - 0`, `mutate.py --swap subi1`): the
graph never terminates on (12,18), a livelock, printed as a lasso:

    COUNTEREXAMPLE  input (12,18)  (infinite run)
      C reference (gcd.c:gcd) returns 6
      this schedule reaches a store and then returns to it after 72 firings, forever
      schedule to the repeating store (276 firings): ...
      the loop (72 firings, back to the same store):
         1. rule 125 fork   [fork34]  takes 210:index_79=1  gives 199:129#0=1, ...
         7. rule 126 comp   [fused subi0+cmpi11+subi1+select1]  takes 202:125#1=3,
            206:127#1=4294967287  gives 211:138=12
         ...

(35,14) still computes 7 on that mutant, and stage 2d proves it, so a per-vector PASS is not
evidence for other inputs.

Mutated MLIR (ipow, shift amount `constant2` 1 -> 2): (3,7) ends with out = [27], C 2187; stage 3
prints the network diff (`.lit 1` -> `.lit 2` in the `shrsi` operator).

### Findings

1. **The hand proofs are syntactic.** Swapping `subi0`'s operands in gcd changes nothing
   semantically (`|b - a| = |a - b|`). Search and the generated per-vector theorems pass, but
   `GcdHwProof` breaks (its `e13` `simp only` closes `sig13 ... = absd a b` only syntactically).
   verify reports NOT PROVED (exit 2), not FAIL: a 2a/3 failure means "no proof applies", and
   only 2b/2c/2d/4 refute.
2. **`formal/tools/dfimport/check.sh` reports a false DRIFT whenever `build/frontend/<k>` exists**
   (it does now: the lead's toolchain restore created it). The generated docstring's `Source:` line
   names the MLIR path, `build/frontend/...` vs the committed `cloud/fixtures/...`; the MLIR files are
   byte-identical (checked for gcd, ipow, collatz, xorshift). verify's drift check ignores that one
   line. Fix for the dfimport owner: normalise the line, or always pass the fixture path.
3. **ipow, 4 placer seeds routed by `verify/route.sh`** (kcheck's flow: kcheck/kernels.tsv sizes
   T9, BD_DSP=1, `--freq 100`, nextpnr sha256 9c732bc6303458df, toolchain.sh 9/9 ok; every
   flow.sh exit 0; obligations from the WORKTREE extract.py): 533 obligations x 6 variants per seed.
   Verdict rows (fastG/slowG) not PASS: s1 43, s2 41, s3 26, s4 27 (mean 34.3, range 26-43).
   Obligations that also fail at an unguarded prjxray corner: 4, 2, 2, 2. The worst rows are rule A
   on `uselect0`/`umuli1` with ~99% SDF-fallback arcs (DSP48E1 nets, H_FALLBACK_BAND: a front-end
   gap, flagged as such in the output). Without fallback arcs, s1 has `I uut.ulink_n7 stage[1]`
   (slowG -1536 ps; C-10n's kcheck classified the same obligation as spread-only on its own
   seed-1 route, which has a different SDF) and `A uut.umux2 src=uj0/O6`
   (slowG -381 ps). This agrees with C-10n (`kcheck/results/ipow*`). verify prints the rows and
   their arcs; it does not classify them. kcheck's `summarize.py`, `pointcheck.py` and
   `constsrc.py` do that, and verify does not call them.

## What verify does NOT do (yet)

- **No all-inputs theorem without a hand proof.** Stage 2d proves listed vectors only. An
  all-inputs theorem for a new kernel still needs `Formal/Net/<K>HwProof.lean` by hand: a C
  transcription plus one lemma per schedule segment.
- **Circuit level only where it already exists.** Stage 3 only checks that the committed gcd/ipow
  circuit theorem is about this exact network. For a changed network it cannot re-instantiate
  the proof (capnet/instantiate.py + a Lean build of ~15 modules, not automated). collatz and
  xorshift have no capnet profile (probe 8y2 is extending capnet; verify reads `capnet.PROFILES`
  at run time, so a new profile is picked up once its entry is added to kernels.py).
- **Stage 4 trusts extract.py** (graph, intervals, obligation choice) and verify does not route.
  `verify/route.sh` is a copy of kcheck's route.sh with its own build directory. One route is a
  sample: give >= 4 seeds.
- **Netlist/bitstream import** (fasm2lean*) is not a stage: it refuses whole kernels (MUXF7/F8,
  CARRY4, FFs). xaudit (shard A, `formal/out/HOWTO-new-kernel.md`) is not wired in.
- **Python semantics.** 2b's Rule.fire copy is not proved equal to Lean's. 2d removes that trust
  for the vectors it proves: the Lean kernel re-executes the schedule.
- **gcd's C reference is not the hardware's C** (that is not in the repo). It is Euclid, on non-negative
  inputs.
