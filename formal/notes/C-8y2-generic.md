# C-8y2: the circuit-safety capstone, generic in the kernel; xorshift and collatz through it

**Status: see the verdict; numbers in "Commands that check" are from 2026-10-29.**
Shard C, probe 8y2, 2026-10-29, 07:25 to about 10:00 UTC. Core Lean only (no Mathlib). No sorry,
no axiom, no native_decide.

## Verdict

1. **One theorem for every kernel: `Formal.Net.KCap.kernel_circuit_safe`** (`KernelCap.lean`).
   A kernel is two type classes: `[KD]` (data: bdc's token graph, the C reference as the token
   run's initial/final stores and spec value, the generated circuit network with bdc's link
   placement, the walk certificate) and `[KP]` (54 obligations, each a decidable check on the
   data or one of the C-reference facts). The proof is C-8m/8q/8r/8s's gcd proof transcribed
   ONCE over the classes (`KernelCap{Defs,Hist,Sound,Safe,CutSpine,Cut,WalkRun,Walk}.lean`,
   about 2950 lines), replacing gcd's ~3000-line text copy per kernel (C-8y).
2. **gcd_hw and ipow are instances** (`KernelCapGcd`, `KernelCapIpow`): every obligation is
   discharged by the EXISTING per-kernel theorem of the same statement (the generic
   definitions are gcd's with constants turned into fields, so they agree up to unfolding);
   `gcd_hw_circuit_safe_generic` / `ipow_circuit_safe_generic` have exactly the statements of
   `gcd_hw_circuit_safe3` / `ipow_circuit_safe3`. Their existing theorems are untouched.
3. **Two more kernels at token AND circuit level, with no copied proof text:**
   - **xorshift** (the steer case): token level new here (`XorshiftHwProof`: bdc's graph
     computes the C xorshift32 on every schedule, for every seed and every i32 `rounds`, no
     input restriction); circuit level `xorshift_circuit_safe`. Needed one generalisation of
     the checker: a reshape folded into ONE output of a data steer (`FoldOK`'s second case,
     sound when the steered data is a constant the reshape fixes; proved in `sound_steerD`).
   - **collatz** (one data argument; C function partial): token level C-8v's; circuit level
     `collatz_circuit_safe` (conditional on the C loop returning, as the token theorem is),
     `collatz_circuit_safe_small` unconditional for `1 ≤ n < 256`.
4. **Negative controls fail as they must** (`Wip/C8y2/negctl.sh`, on collatz): a mutated MLIR
   constant regenerated through bdc's front end (rejected by `KP.ops_ok`), a wrong C
   reference (rejected: `KP.good_run` unprovable), a mutated walk-certificate row (rejected by
   kernel `decide`); plus an unmutated sanity overlay that checks.

## The theorem

```
theorem kernel_circuit_safe [KD] [KP] (a b : Nat) (hd : dom a b) (ch : Fin NC → Chan)
    (H_CELLS : ∀ o : Fin NO, Cell ch (srcVal a b) (opAt o))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch start).req) t ≤ 1) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = spec a b) ∧
    (∀ t, closedVals (ch out0) t = List.replicate (Handshake.cnt (fallB (ch out0).ack) t) (spec a b))
```

**Assumed (named, per run):** H_CELLS (every operator of the generated network meets its
8f/8j/8l gate model, `CapNet.Cell`, which carries §2 of `C-gcd_hw-hypotheses.md`), H_BUNDLE
(every channel bundled, §3), H_START_ONCE (start rises at most once, ever). **Assumed per
kernel (the class):** `[KD]` and `[KP]`; every `KP` field is proved for each instance below,
so nothing per-kernel is assumed in the instance theorems.

**Proved:** every value the circuit latches on `out0` is `spec a b`, and the latched list at
every time is that value repeated once per close.

**Not covered (unchanged from gcd_hw):** liveness (an all-quiet run meets every hypothesis);
O4 (the Ops hand models are not bound to B's generated cells); H_BUNDLE is stated on
zero-delay traces (8w/8x); a re-offered start (the rig's every-result question, 8s2); DSP48E1
(ipow's muli: combinational model); bdc knobs other than the defaults.

**Non-vacuity:** the hypotheses are jointly satisfiable by a run that delivers a value for
gcd_hw (C-8t's `gcd_hw_joint_witness3`: a = 12, b = 18 latches 6) and for ipow (the audit's
`audit/lean/P7/IpowWit.lean`, 3^7 = 2187, CONFIRMED in `audit/REPORT.md`); both are runs of
exactly the networks the gcd/ipow instances use, so they witness the instance theorems too.
For collatz and xorshift no delivering run is exhibited yet (the all-quiet run satisfies the
hypotheses and latches nothing): their hypotheses are not contradictory, but a witness that
latches a value is open (the liveness question).

## The instances

| kernel | instance file | domain `dom a b` | `spec` | obligations from |
|---|---|---|---|---|
| gcd_hw | `KernelCapGcd` | `a, b < 2^31` | `Nat.gcd a b` | existing `GcdHw*`/`Capstone*` theorems |
| ipow | `KernelCapIpow` | `e < 2^32` | `ipowSpec b e` | existing `IpowHw*`/`IpowCap*` theorems |
| collatz | `KernelCapCollatz` | `(collatzC fuel n).isSome` | the C result | `decide +kernel` + C-8v's `CollatzHwProof` |
| xorshift | `KernelCapXorshift` | `rounds < 2^32` | `xsSpec seed rounds` | `decide +kernel` + `XorshiftHwProof` |

- collatz: one data argument and start on channel 1 (`nIn = 2`); the C function is partial, so
  the kernel's second argument is the fuel (`spec n fuel` = the C result, `dom` = it returns);
  the circuit ignores it (`srcC n _ 0 = n`, start offers 0).
- Cascade constants: only gcd_hw has a 3-input control_merge; ipow, collatz and xorshift point
  them at a 2-input control_merge (as C-8y did for ipow), with `acc` on a non-spine channel, so
  the walk never takes the cascade branches; every cascade fact stated is still true and is
  kernel-checked (`r154`, `r155`, `lab_chk`, `cq*`).

## xorshift at token level (`XorshiftHwProof.lean`)

- C transcription `xorshiftC fuel seed rounds` of `kernels/xorshift/xorshift.c` (by hand; not the
  MLIR, not a run's output): `x ^= x<<13; x ^= x>>17; x ^= x<<5` with `<<` truncating, `>>`
  LOGICAL on the unsigned `x` (`Ops.shrui`), `i < rounds` SIGNED.
- Dynamatic's rewrites: loop rotation (entry tests `rounds > 0` = `0 < rounds`, `sgt_slt`, by
  `rfl`); the round fused into two comps (`gX_eq`, by `rfl`); `i = 0` as `extui(i1 false)`.
- `xorshift_hw_graph_computes_xorshiftC`: whenever the C returns `r`, every complete run on
  every schedule and arbitration ends with exactly `[r]` on `out0`; one exists; no run is longer.
- `xorshiftC_total`: the C loop returns within fuel `rounds + 1` on every i32 `rounds` (a
  negative one runs zero rounds), with `xsSpec seed rounds` = `rounds` rounds of `roundC` when
  `rounds < 2^31`, else `seed`; so `xorshift_hw_graph_computes` is unconditional.
- Not covered: liveness theorems (as `IpowHwLive` has) were not written for xorshift.

## The steer case (one-sided fold)

bdc folds `extui0` into the TRUE output of `cond_br2` only (the loop counter's initial i1
`false`, extended to i32 where it enters the loop; the false output goes to a sink). C-8m's
`FoldOK` needed the same reshape on both outputs. The generic `FoldOK` adds the case
`lf = lt ∧ gf' = gf ∧ rules[lt] = comp [gt] gt' fd ∧ … ∧ ConstFix jd fd`: the steered data is
a constant (`jd = .const`) that `fd` fixes (`extui 1 0 = 0`), so the unfolded false output,
which the gate model also passes through `fd`, carries the same values as the token history.
`sound_steerD` proves it from the run's `CpI` invariant of the constant's rule. capnet.py
emits it only under exactly these conditions and refuses anything else (a false-side-only
fold, a non-constant, a reshape that moves the constant).

## Commands that check

```
formal/tools/capnet/check.sh         # gcd regression byte-identical to C-8l/8m/8r/8s, ipow drift
                                     # (14 files), walkcheck + its negative controls  -> [capnet] OK
formal/tools/dfimport/check.sh       # 8 generated files incl. XorshiftHw/Seg match  -> all "ok"
python3 formal/tools/capnet/capnet.py --kernel collatz  kdata | diff - formal/lean/Formal/Net/CollatzCapData.lean
python3 formal/tools/capnet/capnet.py --kernel xorshift kdata | diff - formal/lean/Formal/Net/XorshiftCapData.lean
cd formal && ./check.sh Formal/Net/KernelCapDefs.lean Formal/Net/KernelCapChk.lean \
  Formal/Net/KernelCapHist.lean Formal/Net/KernelCapSound.lean Formal/Net/KernelCapSafe.lean \
  Formal/Net/KernelCapCutSpine.lean Formal/Net/KernelCapCut.lean Formal/Net/KernelCapWalkRun.lean \
  Formal/Net/KernelCapWalk.lean Formal/Net/KernelCap.lean \
  Formal/Net/KernelCapGcd.lean Formal/Net/KernelCapIpow.lean \
  Formal/Net/CollatzCapData.lean Formal/Net/KernelCapCollatz.lean \
  Formal/Net/XorshiftHw.lean Formal/Net/XorshiftHwSeg.lean Formal/Net/XorshiftHwProof.lean \
  Formal/Net/XorshiftCapData.lean Formal/Net/KernelCapXorshift.lean
formal/lean/Wip/C8y2/negctl.sh       # N0 sanity checks; N1 graph, N2 C reference, N3 walk rejected
```

## Files

| file | what |
|---|---|
| `Formal/Net/KernelCapDefs.lean` | NEW. `class KD`, `class KP`, the kernel-dependent definitions (`OpChk`, `FoldOK`+`ConstFix`, `SpOK`, the walk checker `cOK`, ...) |
| `Formal/Net/KernelCapChk.lean` | NEW. `KP`'s network fields from Boolean checks (`ops_ok_of`, `rank_ok_of`, ...) |
| `Formal/Net/KernelCap{Hist,Sound,Safe,CutSpine,Cut,WalkRun,Walk}.lean` | NEW. The gcd chain transcribed over `[KD] [KP]` (drafted by `Wip/C8y2/mkgeneric.py` from the gcd sources, then fixed by hand) |
| `Formal/Net/KernelCap.lean` | NEW. `kernel_circuit_safe` |
| `Formal/Net/KernelCap{Gcd,Ipow,Collatz,Xorshift}.lean` | NEW. The four instances |
| `Formal/Net/CollatzCapData.lean`, `XorshiftCapData.lean` | GENERATED by `capnet.py kdata` |
| `Formal/Net/XorshiftHw.lean`, `XorshiftHwSeg.lean` | GENERATED by `mlir2lean.py` (unchanged tool) |
| `Formal/Net/XorshiftHwProof.lean` | NEW. xorshift token level |
| `formal/tools/capnet/capnet.py` | EDITED: n-argument environments (start = last argument), the one-sided fold, profiles collatz/xorshift, `kdata`, `CAPNET_MLIR_<k>` override (negative controls only). gcd/ipow outputs byte-identical (check.sh). |
| `formal/tools/dfimport/check.sh` | EDITED: xorshift added; names the fixture when `build/frontend` holds a byte-identical copy (the header records the path: the restored `build/frontend` made every file report a false drift) |
| `formal/lean/Wip/C8y2/{mkgeneric.py,lc.sh,negctl.sh}` | WIP tools: draft generator, private-olean compile, negative controls |

The lead has to add the new modules to `Formal.lean` (I do not own it).

## Generic vs per-kernel (measured)

| part | lines |
|---|---|
| generic proof (`KernelCap{Defs,Chk,Hist,Sound,Safe,CutSpine,Cut,WalkRun,Walk,}`) | about 3100 |
| per kernel, hand-written: the instance file | gcd 175, ipow 170, collatz 190, xorshift 190 (most of it the 54-field record) |
| per kernel, generated: `capnet.py kdata` | one file |
| per kernel, token level (step 1 of the howto) | xorshift: about 250 lines |

C-8y's per-kernel cost was a 3081-line text copy driven by a ~45-site substitution table.
