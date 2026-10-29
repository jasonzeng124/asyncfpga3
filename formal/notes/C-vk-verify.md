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

## Adding a kernel

One entry in `formal/tools/verify/kernels.py`: fixture name, C file and function, vectors (avoid
degenerate ones), domain, Lean names (K, ns, dfimport naming options), and optionally the hand
proof (file, theorem, a Lean term evaluating the transcription) and the capstone (capnet
profile, module, theorem, generated files). With only the first group, stages 1, 2b and 2d run
and give per-vector theorems or a counterexample; an all-inputs theorem needs a hand proof
(follow `Formal/Net/IpowHwProof.lean`), and the circuit level needs a capnet profile.

RESULTS-PLACEHOLDER
