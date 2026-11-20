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

# Update (2026-11-20 02:30 UTC): the token-width assumption, iterative_division PROVED under it

Correction to the section above: for iterative_sqrt, widths are necessary but not sufficient (see "Still open").

## What is assumed
The new theorems state one hypothesis on top of the old ones: `hW : ∀ ch v, v ∈ σ0 ch → InW Wi ch v`. In plain terms,
every input token fits its declared width (`v < 2^Wi[ch]`, where `Wi` holds the MLIR argument types as read by bdc's
emitter; a control token has width 0, which means no constraint). Nothing is assumed about any other channel. Inside,
the planner proposes a width map for each intermediate graph, and Lean checks it: every rule keeps tokens within the
map (`safeB_ok`), and on the inputs the map is never narrower than declared (`agreeB`).

## Lean (`Steps/Width.lean`, Core only; the old files are unchanged)
* `bwv` / `bwpv` / `unsliceW` / `unsliceNW` are the width bounds and slice rules of ScriptRF, now also using the
  variables' widths. `unsliceNW_eval` shows they keep the value in any environment whose variables fit (`EnvOK`).
* `safeB` / `safeB_ok` check a rule against a map. For a comp, the bound computed from its inputs' widths must fit
  its output's width. For fork, branch, mux and cm, widths may only grow along the data path. `sel` and pass-through
  variables get the bound of their input's width, never more.
* `SoundP P` is `Sound` restricted to initial stores satisfying `P`. `soundP_of_inv`: if every rule keeps the
  invariant and the two graphs fire alike on every invariant store, their complete runs correspond.
* Two new steps. `applyUW_sound` (`unpackw l W`) narrows slices using the widths, after checking every rule against
  `W`. `applyUD_sound` (`undedupe`) is Dedupe read backward, checked by deduping back.
* `runScriptW_sound`: every StepRF step plus the two new ones, under `InP NA Wi` (inputs only, each within its
  declared width).
* Template: when width steps are used, the generated file proves `pass_forward_w` / `pass_backward_w` with `hW`.

## Planner
Pass 1 is the old planner, unchanged, and gives unconditional theorems. Pass 2 runs only if pass 1's normal forms
differ. It infers a width map (`infer_W`: forward fixpoint, then any channel whose writer fails `safeB` loses its
bound) and uses `unpackw` where the plain `unpack` is not enough. For iterative_division's cell `comp [a, b, k]`
(test `|a| <s |b|`, parts `|a|` and `|b|`, with `k` a wait no part reads), pass 2 goes:
1. undedupe: the cell reads a second copy `k2` of `k`.
2. Two gates: `[k, a]` is folded into `x = a` (gated by `k`) and `[k2, b]` into `y`, each by unabsorb with `f = var 1`.
3. The existing 2-input, 3-slice flow, with `unpackw`.
4. unjoin on each update, then forkcomm2 on each gate.
On the unfused side, `rf_litpush` moves the `lit 0` comp through its fork, so that each reader waits on its own copy of
the control token, as the fused cell does. `rf_canon_forks` sorts the comp readers of each fork by structure only
(the reader's expression, and where its other inputs come from, traced through forks to the inputs). It is a stable
sort, so forks the two sides already agree on are not reordered.

## Results
* iterative_division: PROVED UNDER THE WIDTH ASSUMPTION, Wi = [32, 32, 0]. Axioms: propext, Classical.choice,
  Quot.sound.
* Controls: `--ctl slice_low` REFUSED rc 2; `--ctl part_plus1` REFUSED rc 2. The generated certificate with `Wi`
  changed to [64, 64, 0] is rejected by the kernel at h2.
* Census: 21 PROVED (20 unconditional, the same as before; 1 under the width assumption), 4 same rules,
  1 REFUSED (iterative_sqrt).
* A first version that ran the new planner moves unconditionally made 10 of the 20 REFUSED. That is why pass 2 runs
  only when pass 1 fails.

## Still open: iterative_sqrt
Widths are necessary here but not sufficient. The 4-input cell `comp [mid, n, lo, hi]` packs `lo' = sel(c, mid+1, lo)`
and `hi' = sel(c, hi, mid-1)`, and the loop test `sgt(lo', hi')` reads both outputs. To match the unfused graph, the
`lo'` part must stop waiting for `hi`, and the `hi'` part must stop waiting for `lo`. The only consumers of `lo'` are
its branch (steered by the test) and the test itself, and the test reaches `hi` through `hi'`'s producer, not through
a sibling copy of `hi`. That is a join extension through another update. A route with the existing proof: rf_split
both outputs, so that the test absorbs copies of both parts and reads copies of mid, n, lo, hi directly. Then pack the
other inputs into one word (needs a width-checked rewrite step that introduces slices, i.e. `unpackw` read backward)
so that `unjoin`'s 2-input shape applies to each part. This also needs ForkComm2 read backward, so that the packed
word is one forked channel shared by the test and the part. Not done.
