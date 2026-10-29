# C-vk2: automatic all-inputs token proofs for loop kernels (`formal/tools/autoproof/`)

Probe C-vk2, 2026-10-29. North-star goal 3 ("given any routed design from this flow, it proves
it correct or prints a counterexample trace"). Before this probe, `verify.sh` (C-vk) proved a
kernel for ALL inputs only through a committed hand proof (`Formal/Net/<K>HwProof.lean`), and
C-vk found those proofs syntactic: swapping `subi0`'s operands in gcd (`|b-a| = |a-b|`, an
equivalent mutant) broke `GcdHwProof` although the graph is still correct.

## Verdict
The all-inputs token-level theorem is now GENERATED, with no hand proof, for loop kernels of
the shape dfimport cuts into one-fact segments: from the handshake MLIR and the C function,
`autoproof.py` writes a Lean file whose main theorem has the statement of the hand theorems
(`every complete run, any schedule and arbitration, ends with [r] where r is what the C
transcription returns; such a run exists; none is longer`). Checked by `./check.sh` (axioms
within propext/Classical.choice/Quot.sound, no native_decide, no bv_decide) for gcd, ipow,
collatz, xorshift and isprime (the first all-inputs theorems for xorshift and isprime, neither has a
hand proof; isprime has nested loops and early returns) and for C-vk's equivalent gcd mutant, which
now PROVES. Real mutants do not prove (a counterexample from the co-simulation, or Lean rejects the
proof when it is forced through). Integrated as stage 2e of `verify.sh`; on the equivalent mutant
`verify.sh` now ends `VERDICT: PASS` (exit 0) where C-vk's ended NOT PROVED.

## Run it

    export PATH=$HOME/.elan/bin:$PATH
    formal/tools/autoproof/gen_claimed.sh                # regenerate the claimed files (Python, seconds)
    cd formal && ./check.sh Formal/Net/AutoLib.lean Formal/Net/AutoIpow.lean Formal/Net/AutoCollatz.lean \
        Formal/Net/AutoXorshift.lean Formal/Net/AutoGcd.lean Formal/Net/AutoGcdSubi0Hw.lean \
        Formal/Net/AutoGcdSubi0HwSeg.lean Formal/Net/AutoGcdSubi0.lean Formal/Net/AutoIsprimeHw.lean \
        Formal/Net/AutoIsprimeHwSeg.lean Formal/Net/AutoIsprime.lean
    formal/tools/autoproof/selftest.sh [--quick]         # positives, negative controls, operand-swap sweeps
    # any MLIR + C, one self-contained Lean file (graph + segments + proof):
    python3 formal/tools/autoproof/autoproof.py MLIR C_FILE FUNC --name N --graph-ns Formal.Net.AutoNG \
        --combined OUT.lean --dfargs "--ns Formal.Net.AutoNG --graph-module X --label N --short N"
    formal/slot.sh lake env lean OUT.lean
    formal/tools/verify/verify.sh KERNEL [...]          # stage 2e runs the above on the fresh import
    python3 formal/tools/autoproof/sweep.py KERNEL       # every operand swap: equivalent ones must prove

## How it works

| piece | file | trusted? |
|---|---|---|
| C front end: C subset -> test-point automaton `CProg` | `autoproof/cfront.py` | YES, like the hand transcriptions were: it is the reading of the C. Tested against the compiled C (verify 2f `auto-tr`; `witness` theorems) |
| graph + symbolic segments (template automaton) | dfimport `mlir2lean.py --segments` (C-8i, unchanged) | no: `seg*` are kernel-checked certificates |
| co-simulation, correspondence guessing, numerical pre-check | `autoproof/autoproof.py` | no: guesses only; Lean checks |
| generic simulation theorem `sim_call`, abstraction lemmas, tactic `auto_ops` | `Formal/Net/AutoLib.lean` | proved once (no kernel-specific content) |
| determinacy over all schedules | C-8i's `determinate` / `no_longer` (GcdHwLib) | proved |

1. **C side.** `cfront.py` parses a small C subset (int/unsigned scalars, assignments incl. `op=`,
   `++`, `if`/`else`, `while`, `do`, `for`, `return`; `+ - * & | ^ ~ << >> ` comparisons `! && || ?:`
   and casts; no `/ %`, arrays, calls, `break`) and cuts the function at its tests. A test point is
   a loop condition, or an `if` containing a loop/return/test; assignment-only `if`s and `?:` become
   `E.sel` (pure, exact). Values: i32 bit patterns with wraparound, exactly `Formal.Net.GcdHw.Ops`
   (C leaves signed overflow undefined; the transcription takes the circuit's two's complement),
   `>>` arithmetic on int (gcc's choice), logical on unsigned; uninitialised locals start at 0.
   `CProg.run` is fuelled (`none` = fuel ran out): termination is never claimed.
2. **Graph side.** dfimport's symbolic segments: template `src` with environment `env` reaches template
   `dst` with `sig env` when the branch fact has outcome `br`.
3. **Correspondence (guessed, then proved).** Both automata consume exactly one test per step, so
   co-simulating them on 360 inputs plus the given vectors (the kernel's vectors, boundary values, small and random 32-bit
   numbers; 400 steps each) aligns them step by step. From the alignment: `L k`, the C test point of
   template k; `ρ k`, each template variable as an expression over the C state there (first candidate,
   in a pool of C variables, the point's test, its negation and the subexpressions of the outgoing code,
   that matches every observation; `search` repairs wrong picks by blaming the variables of a failing
   obligation); `Is k`, invariants (C variables constant at k, or equal to an earlier variable: e.g.
   gcd's `k = 0` before the twos loop, xorshift's `x = seed` at entry); `M`, the pairing of C edges with
   graph edges. A template the co-simulation never reaches (a graph path that is infeasible: isprime's
   first `s <= half` test is always true when `d*d <= n`, but the graph has the other branch) is
   DERIVED from its predecessor: its test point is the C edge's destination, its ρ is the segment's
   `sig` over the predecessor's ρ (allowed only if that C edge leaves those variables unchanged), and the
   pairing of its edges follows the polarity of its fact against the C test, measured numerically.
   Every obligation is then checked on 3000 random C states satisfying the invariant and the C outcome;
   a failure stops with NOT PROVED (and prints the state).
4. **Lean.** The generated file proves, per pairing, that under the invariant and the C outcome the
   segment's fact has the matching outcome, its new environment equals ρ of the C's new state, and the
   target invariant holds. Each equality is closed by `auto_ops` after **abstraction of common
   subterms**: subterms of the two sides that agree numerically are proved equal separately (recursively)
   and replaced by a fresh variable (`abs_eq`, with a range fact `< 2^w` from `bev_lt` when the subterm
   is a `bin` node), so the final `omega` calls are small. `auto_ops`: unfold `addi..extui` to Nat
   arithmetic (`% 2^w`, literal shifts as `*`/`/ 2^k`, `x &&& 1 = x % 2`; xor/or/products of variables
   stay atoms), turn comparisons/selects/arithmetic shifts into `if`s via propositional lemmas
   specialised to widths 1 and 32, split every `if` (`ite_case`, a 12-line elaborator: `by_cases` on
   the condition of an innermost `if`, then `simp only [hc, ↓reduceIte]`), `omega`.
   `Cover` (every C edge from every template's point is paired, destinations agree) is `decide`d.
   `sim_call` (induction on the C fuel) then gives `Reach (St T0 ins) (St Tfin [r])`, and
   `determinate` / `no_longer` give every schedule.

Why not `bv_decide`: it exists in core here (`import Std.Tactic.BVDecide`), but its SAT certificate is
checked with `Lean.ofReduceBool` (`#print axioms` of a nontrivial `bv_decide` proof lists
`..._native.bv_decide.ax_1_5`), the native_decide trust the rules exclude. A trivial goal closed by its
preprocessor alone shows only the standard axioms, which is misleading (both checked in a scratch
file during this probe). `decide` cannot do 32-bit universally quantified
goals; `omega` with the unfolding above does.

Two Lean pitfalls found and handled (they cost most of the time): (a) a definitional rewrite (dsimp,
or a simproc such as `Nat.reducePow`) inside the condition of an existing `if` leaves its `Decidable`
instance at the old type, after which neither `split` nor `if_pos` can reduce the `if` ("not
type-correct at implicit transparency"); so `if`s are introduced only by propositional lemmas, after all
unfolding; (b) `Nat.reduceAdd` on such terms produced proofs on which the kernel hits "deep recursion";
it is not used.

## The theorems (claimed; plain language)

For K in {Ipow, Collatz, Xorshift, Gcd, GcdSubi0, Isprime}, `Formal.Net.Auto<K>.auto_computes`:

* **Assumes**: `kC fuel x₀ .. = some r`, i.e. the generated transcription of the C function returns `r`
  on the input bit patterns within `fuel` tests (non-vacuous: `witness`, e.g. `kC 10000 3 7 = some 2187`
  for ipow, `kC 10000 12 18 = some 6` for gcd, kernel-checked in the same file).
* **Proves**: from the store with one token per input and the start token, (i) a complete run reaching
  `[r]` on the output and the end token (and nothing else: the final template) exists; (ii) every
  complete run, under any schedule and any arbitration of the control_merges, ends in exactly that
  store; (iii) no run (complete or not) is longer. The graph is dfimport's export of the MLIR
  (`rules`, `T*`, `seg*` in `<K>HwSeg.lean`; for GcdSubi0 in `AutoGcdSubi0HwSeg.lean`, exported from
  `formal/tools/autoproof/test/gcd_subi0.mlir` = the gcd fixture with subi0's operands swapped by
  `verify/mutate.py`; for Isprime in `AutoIsprimeHwSeg.lean`, exported from the committed fixture
  `cloud/fixtures/frontend/isprime/comp/handshake_transformed.mlir`).
* **Does NOT cover**: that `kC` is the C beyond cfront's reading (testing only); termination of the C;
  the hand transcriptions (`ipowC`, `gcdC`, ...) are NOT referenced: the statement is the hand
  theorems' with the generated transcription in their place; H_SOURCE_ETERNAL (dfimport's modelling of
  source/constant chains); bdc's Verilog, gates, delays, cells.
* **gcd's C** is `formal/tools/autoproof/ref/gcd_binary.c`, written from the committed CF-level MLIR
  (`cf_transformed.mlir`), block by block, as the hand `gcdC` was, because Dynamatic's gcd.c is not in the
  repo and C-vk's `verify/ref/gcd.c` (Euclid) is a different algorithm with no step correspondence. So
  for gcd the C side is not independent of the compiler front end (stated in the file); it agrees with
  Euclid on the tested vectors (compiled with gcc). It loops forever on some negative inputs (e.g.
  (-2,-1)), as the hand `gcdC` does: the theorem is conditional on termination.

## Results

| run | generator | Lean | notes |
|---|---|---|---|
| ipow (fixture) | 3 templates, 4 segments, 1 C test point, 4 pairings; `T1 ~ [r, b, e, e > 0]` (as in the hand proof) | PASS (check.sh) | inv `r = 1` at entry |
| collatz | 4 pairings; `T2 ~ [n, steps, (n != 1) == 0]` | PASS | strength reduction `n + (n << 1)` vs `3 * n` and the i1 rewrite proved by `auto_ops` |
| xorshift | 4 pairings; inv `x = seed, i = 0` at entry | PASS | first all-inputs theorem for xorshift; xor terms equal syntactically after substitution |
| gcd | 10 templates, 18 segments, 8 C test points, 18 pairings, L = [0,0,1,2,2,3,4,5,6,7] | PASS | rotated loops: T3 and T4 both map to the twos loop's test |
| gcd, subi0 swapped (C-vk's equivalent mutant) | same correspondence | **PASS** | hand proof fails on it (C-vk); the generated one proves `|b-a|` = `|a-b|` by case splits |
| isprime (new kernel, no hand proof) | 10 templates, 18 segments, 5 C test points, 18 pairings, L = [0,-,1,2,3,2,4,3,3,1]; T4 derived (infeasible path) | PASS | nested loops, two early returns, `d*d <= n` (product of variables: an omega atom) |
| collatz64 | refused: `in_int_t` is `long long` in collatz64.h | - | cfront reads the header typedefs and refuses non-32-bit types (before this fix it read `in_int_t` as int and printed a FALSE counterexample at n = INT_MIN: the 64-bit datapath and a 32-bit transcription differ) |
| gcd, subi1 swapped (livelock) | COUNTEREXAMPLE (1,5): graph does not finish in 400 segments, C returns 1 | - | exit 1 |
| ipow, shift constant 1 -> 2 | COUNTEREXAMPLE (12,12): graph 144, C 4043309056 | Lean REJECTS the proof forced through with the correct graph's correspondence (`--corr-from`): `omega` fails on `e >> 2` vs `e >> 1` | negative control that Lean, not Python, is the judge |
| ipow vs `verify/test/ipow_wrong.c` | COUNTEREXAMPLE (65536,65536) | - | wrong C side |

### Operand-swap sweep (`sweep.py`, every two-operand op of each fixture; mutate.py cannot swap `cmpi`)

Generator verdicts (`sweep.py K --no-lean`, all four kernels: `sweep: OK`):

| kernel | equivalent swaps (must prove) | real swaps (must not) |
|---|---|---|
| ipow | andi0, muli0, muli1: Lean file written | shrsi0: COUNTEREXAMPLE |
| collatz | andi0, addi0, addi1, addi2: Lean file written | shrsi0, shli0: COUNTEREXAMPLE |
| xorshift | xori0, xori1, xori2, addi0: Lean file written | shli0, shli1, shrui0: COUNTEREXAMPLE |
| gcd | ori0-4, andi0-4, addi0, subi0 (`|b-a| = |a-b|`): Lean file written | shrsi0-4, shli0, subi1: COUNTEREXAMPLE |

With Lean (`formal/tools/autoproof/selftest.sh`, which runs the sweeps with Lean on every generated
file): queued at hand-off (log build/vk2fin2/selftest.log); each equivalent swap must end `PROVED`. Before
hand-off the equivalent mutant subi0 (the one C-vk found) was checked with Lean three times (combined file,
claimed files, verify 2e), and the forced proof of the ipow constant mutant was rejected by Lean.

### `verify.sh` with stage 2e (logs: build/verify/vk2/, build/vk2fin2/)

| run | 2a hand | 2e generated | 2b search | 2d vectors | 2f auto-tr | verdict |
|---|---|---|---|---|---|---|
| gcd, subi0 swapped (`--no-cap --vecs "12,18 35,14 48,180"`) | FAIL (syntactic proof) | **PASS** | PASS | PASS 3/3 | PASS | **PASS, exit 0** (C-vk: NOT PROVED, exit 2) |
| ipow, shift constant 1 -> 2 (`--no-cap`) | FAIL | FAIL: cex (3,7): graph 27, C 2187 | FAIL: cex | FAIL | - | FAIL, exit 1 |
| xorshift (fixture, no hand proof) | SKIP (no hand proof) | **PASS** (`AutoXorshiftHwV.auto_computes`) | PASS | PASS 5/5 | PASS | **PASS, exit 0** (C-vk: proved on the vectors only, exit 2) |
| isprime (new `kernels.py` entry) | SKIP | run queued in build/vk2fin2/v-isprime.log at hand-off | | | | |

Stage 2e needs no per-kernel configuration beyond C-vk's `kernels.py` entry (`autoc` only when the
reference C is a different algorithm, as for gcd). A 2a FAIL is excused by a 2e PASS; a stage-3 FAIL
(circuit network differs from the proved one) is not. 2e's counterexamples come from the Python
co-simulation and count as refuting, like 2b's.

## What it does NOT do (yet)

* **Shapes it refuses** (NOT PROVED, never wrong): a segment with zero or two branch facts; several
  final templates or a final template with more than the result; a template variable that no pool
  expression matches (e.g. a value the graph carries that is not a function of the current C state);
  C with division, arrays, memory, calls, `break`; graph and C test points that do not align one to
  one (e.g. an `if` the hardware did not if-convert while cfront did, or vice versa: cfront converts
  every assignment-only `if`).
* **C types**: 32-bit `int`/`unsigned` only (`in_int_t` read from the included header). collatz64
  (64-bit) is refused; widening cfront and `auto_ops` (lemmas specialised to widths 1 and 32) to 64 is
  mechanical but not done.
* **The tactic** proves equalities of `Ops` expressions modulo linear arithmetic, case splits and
  syntactic equality of atoms: an equivalence that needs xor/or/and algebra on non-constant operands, or
  a nonlinear identity (e.g. `a*(b+c) = a*b + a*c` mod 2^32), is beyond it (NOT PROVED).
* **The C transcription is trusted** (as the hand ones were); cfront is ~650 lines of Python, tested by
  the vectors (2f) and the `witness` theorems, not proved. No theorem relates `kC` to the hand
  transcriptions (`ipowC`, `gcdC`, ...): doing that per kernel would be hand work again.
* **WIP**: `formal/lean/Wip/Cvk2/Tac.lean`, unit tests of `auto_ops`; its last example is false on purpose
  and must fail, so the file does not check (not claimed).
* Termination, the circuit level (stage 3), timing: unchanged from C-vk.
