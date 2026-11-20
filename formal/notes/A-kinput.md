# A: ring fusion on packed cells with 3 inputs (2026-11-20)

Shard A. Context: A-joinext.md, open item (1). fuse_check proved BDC_RING_FUSE per kernel on 19 of 26 importable
kernels. The three it refused (iterative_division, iterative_sqrt, nest3) have fused cells with 3 or 4 inputs, and
`rf_unpack` handled only 1 or 2 (forkcomm / forkcomm2), and `unjoin` only removes the second of two inputs.

## Route: reduce to the 2-input steps (no k-input ForkComm / JoinExt)

New script step `unabsorb lq bs as p f g` in `Steps/ScriptRF.lean` (`applyUA`, `applyUA_sound`, wired into
`applyStepRF_sound` and so into `runScriptRF_sound`). It is Absorb read backward. The comp at `lq` reading
`bs ++ as` becomes `comp (bs ++ [p]) q g`, and `comp as p f` is appended on a fresh channel `p`. Lean does not trust
the factoring. It runs `absorb` (of the new comp into `lq`) and then `drop` (of the sink that leaves) on the result,
and requires the old rule list back exactly. Soundness is then `(runScript_sound _).symm`. The proof is about 15
lines, because no new simulation is needed.

Planner (`fuse_check.py`, `rf_prefactor` / `rf_factor`): a 3-input packed cell with two slices. Its inputs `as` are
the ones the update part reads (exactly two) and `bs` is the remaining one (the wait). `f` is a subterm of the cell's
expression over `as` only, chosen so that every read of `as` lies inside a copy of `f` and every slice still unpacks
(no part becomes `f` itself, so each part keeps its `bwp` bound). The largest such subterm is tried first. Then the
existing 2-input flow runs: forkcomm2 on `comp [n, p]`, absorb and unpack the slices, then unjoin the update's wait.
After that, forkcomm2 runs on `comp as p f`, whose output now feeds a 2-way fork. Finally the input forks are
flattened into their parent forks (`rf_flatten`, lifted out of `rf_split`) and put in canonical order (`rf_order`).

## Results
* nest3: PROVED. The script is `.unabsorb 53 [96] [92, 78] 253 (trunci 2 (xori 32 v0 v1)) (pack ...)`, then
  forkcomm2, absorb/unpack, unjoin, and forkcomm2 again. Axioms: propext, Classical.choice, Quot.sound.
* Controls on nest3: `--ctl slice_low` REFUSED rc 2, and `--ctl part_plus1` REFUSED rc 2. For a third control, the
  generated file with `f`'s `xori` changed to `ori` fails in the kernel (`decide +kernel` on the script).
* iterative_sqrt: its 3-input cell (`mid = (lo+hi)>>1` and the test `mid*mid == n`) now unpacks. It is still REFUSED
  because of its 4-input cell `comp [mid, n, lo, hi]`, which packs `sel(c, mid+1, lo)` and `sel(c, hi, mid-1)`.
* iterative_division: still REFUSED. Its 3-input cell packs `|a|` and `|b|`, where `|x| = sel(x >s -1, x, 0 - x)`.
* Census: no regression. 20 PROVED (19 earlier + nest3), 4 same rules, 2 REFUSED (ringfuse_census.txt).

## Why the remaining two are not a missing local step
For a part that passes an input through (`sel c x y` returns `x` itself), the slice `trunci 32 (shrui 64 pack 0)`
equals the part only if the token is `< 2^32`. In iterative_sqrt, `hi` starts as the kernel input (fork 0 → branch →
mux 23). It can reach the output mux (branch 82 → 83 → mux 87) unchanged, so the fused graph outputs `hi mod 2^32`
where the unfused one outputs `hi`. The two agree only if input tokens fit their declared width. The token model
(Nat tokens, no width typing) has no such hypothesis, so no rewrite step can prove it. Closing this needs a typed
store invariant: every token on a channel of width w is `< 2^w`, preserved by every rule, and assumed of the inputs.
That would be a named hypothesis in a new `Sound` variant. Not done. A k-input ForkComm would not help either:
the obstacle is the slice identity, not the fork.

Also not done: a cell with 4 or more inputs (one `unabsorb` folds into two inputs, and the second forkcomm2 needs the
folded comp to have exactly two). This would need an `unabsorb` per extra input. No kernel in the census needs it
except iterative_sqrt's, which the width issue blocks first.
