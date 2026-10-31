# A-envfast: a scalable, proved-once checker for Env certificates

Shard A. Namespace `Formal.Core.EnvFast`. Toolchain: Lean v4.35.0 (no Mathlib import; core only).
No routed numbers are involved, so no nextpnr fingerprint applies.

## Files

| file | status | content |
|---|---|---|
| `formal/lean/Formal/Core/EnvFast.lean` | proved | compiled gates (`CGate`, LUT truth table `tt` + hazard table `hz`), table checks `ttOK`/`hzOK`, fast evaluation with shared masks, equivalence with `Env`, `check` + `check_sound` |
| `formal/lean/Formal/Core/EnvFast/Kernel.lean` | proved | the same checker in kernel-friendly form (raw GMP `Nat` ops, recursors), each piece proved equal; chunked certificates; `kcheck_sound` / `kcheck_Sound` |
| `formal/lean/Formal/Core/EnvFast/Tables.lean` | proved, generated | tables for 7 LUT outputs, each checked against `LutAudit.outB` / `classify` by `decide +kernel` |
| `formal/lean/Formal/Core/EnvFast/Models.lean` | definitions | `link2Model` (verbatim copy of `Env.Wip.link2Model`), `link2Q`, `mergeModel`, `mergeQ` |
| `formal/lean/Formal/Core/EnvFast/Link2Cert.lean`, `MergeCert.lean` | data, generated | certificates (untrusted) |
| `formal/lean/Formal/Core/EnvFast/Link2.lean` | proved | bd_link W = 2 results, W = 1 cross-check, negative control |
| `formal/lean/Formal/Core/EnvFast/Merge.lean` | proved | bd_merge control-path results and controls |
| `formal/lean/Wip/EnvFast.lean` | not built | open items |
| `formal/tools-A/envfast/Gen.lean` | tool | untrusted generator: tables, certificates (balanced-BST preorder, chunks of 128) |
| `formal/tools-A/envfast/memtime.py` | tool | wall time and peak RSS (`/usr/bin/time` is not installed here) |

## How to check

    cd /home/user/asyncfpga3/formal/lean && ../check.sh Formal/Core/LutTree.lean Formal/Core/LutCells.lean \
      Formal/Core/LutAudit.lean Formal/Core/Env.lean Formal/Core/EnvFast.lean Formal/Core/EnvFast/Models.lean \
      Formal/Core/EnvFast/Tables.lean Formal/Core/EnvFast/Kernel.lean Formal/Core/EnvFast/Link2Cert.lean \
      Formal/Core/EnvFast/MergeCert.lean Formal/Core/EnvFast/Link2.lean Formal/Core/EnvFast/Merge.lean

The dependencies are listed too: with a file list, `check.sh` writes oleans to `.lake/checkfile`, and Lean
then resolves every `Formal.*` module there. Result: `[check] OK`, `[audit] 1070 declarations checked`.
That covers the whole chain including LutAudit and Env, with no `sorry` and no `native_decide`
(only `decide +kernel`). Wall time is 174 s; LutAudit and Env take 100 s of it.

## Design

**Semantics.** Unchanged. Every theorem is stated with `Env.Reach`, `Env.succs`, `Env.stepOK`, `Env.live` and
`Env.Sound`, imported from `Env.lean`, which is not edited.
- The state is `Env`'s own `Nat`: the signal bits, then the in-flight `pend` records. So the state needs no
  re-encoding.
- What changes is how the kernel evaluates the semantics. Each change is proved equal to the original:
  - `cval_eq`: the table lookup is `Gate.val`. This is decode ∘ encode of the pin vector through `addrOf`.
  - `excMaskF_eq`, `enMaskF_eq`.
  - `postF_eq`: the successor with shared masks is `Env.post`.
  - `succsF_eq`: the fast successor list is `Env.succs`.
  - `lutOKF_eq`, `stepOKF_eq`, `liveF_eq`.
  - In `Kernel.lean`: `kb_eq`, `kaddr_eq`, `kexc_eq`, `kenOf_eq`, `kpost_eq`, `koldAddr_eq`, `klutOK_eq`,
    `kstepOK_eq`, `kcontains_eq`, `kinsert_eq`, `kstateOK_eq`, `klive_eq`.

**What the kernel no longer does:**
1. **Reachability search.** The certificate is a list of states computed outside the kernel by `Gen.lean`,
   using `Env.reachTree` in the interpreter. It is untrusted.
2. **`classify` (Kleene cube enumeration) on every MIC.** Each LUT output gets a hazard table
   `hz` (`2^(2k)` bits) and a truth table `tt` (`2^k` bits). `hzOK`/`ttOK` check them once per LUT output against
   `LutAudit.classify`/`outB` on every vector of the right length. A lookup is then a single `testBit`.
3. **Recomputing masks.** The excitation and enable masks are computed once per state and once per successor,
   not once per in-flight slot.
4. **The instance chain and `brecOn`.** The hot path uses raw `Nat.land`/`shiftRight`/`beq`/`blt`/`add`/`pow`/`mod`,
   `cond`, and folds written with `List.rec`/`Tree.rec`. These functions are `noncomputable`; only the kernel
   evaluates them.

**Soundness (proved once, for every model).** `check_sound` / `kcheck_sound`, under these hypotheses:
- `KCompiled M C`: the compiled gates are `M.gates` and their tables are valid; the guards are extensionally
  `M`'s; `n`, `settle` and `prio` are copied.
- `Q'` agrees with `Q`.
- The initial states are in the tree of the certificate.
- Every chunk passes `kchunk`.

Conclusion: every `Reach`-able state is in the certificate, satisfies `Q`, and every transition from it passes
`Env.stepOK` (a hazard-free MIC at every non-firing LUT, and persistence). `kcheck_Sound` gives `Env.Sound M Q`,
the same predicate the `Env` theorems use, so their meaning carries over unchanged.

**Chunking.** The kernel's caches are per declaration. A certificate split into chunks of 128 states is checked
by one `decide +kernel` per chunk. Each chunk rebuilds the BST of the whole certificate (about 0.1 s for 1048
states) and checks only its own states. Peak memory is then bounded by the chunk size, not the model size.

## Results (all in `Formal.Core.EnvFast`)

**bd_link, W = 2** (LUT6_2 latch pair, en fanning out to both outputs; 1048 states). This is the former conjecture
`Env.Wip.link2_sound`.
- `link2_sound : Sound (link2Model ⟨true, true, true, false⟩) (live …)`: hazard-free, persistent and live, under
  rules H, L and isoEn.
- `link2_reach_in_cert`: every reachable state is in the certificate.
- `link2_data_sound : Sound (link2Model ⟨true, true, true, true⟩) (link2Q …)`: with rxBundle, the receiver always
  acknowledges both of the sender's bits (752 states). This is the W = 2 analogue of `Env.link_data_sound`.
- `link2_cut_rejected`: **negative control**. The certificate with one reachable state removed is rejected.
- `link1_sound`: `Env.link_sound` (W = 1, 142 states) re-proved by the new checker. It is a cross-check of the
  two checkers on the same model.

**bd_merge, control path** (request OR, `bd_delay` as one wire, two `bd_c2` acknowledges, select OR; 33 states).
- `merge_sound`: under `excl` (the header's obligation: an input requests only after the other's transaction
  has fully completed) and `selFast`, the control path is hazard-free, persistent and live. It also never
  acknowledges an input whose token it did not carry (`mergeQ`).
- `merge_needs_excl_token`: without `excl`, after `x_req↑ y_req↑ either↑ z_req↑ z_ack↑`, `y_ack` is excited for
  x's token.
- `merge_needs_excl_hazard`: without `excl`, y withdraws its request while x's rise is still in flight at the
  request OR. This is a static-1 MIC on `either`, i.e. a possible `z_req` glitch.
  - Together with the item above, this derives the header's "exclusivity is not enough".
- `merge_needs_selFast`: **new finding.** `selFast` is needed. The checker found it.
  - Without it, a whole x transaction can complete before `sel` follows `x_ack↑`; `x_ack↓` then withdraws `sel`'s
    excitation, a runt on the mux select.
  - Separately, `x_req↑` can arrive before `sel` has fallen, a static-1 MIC on the select OR.
  - In silicon this is a race between one LUT and the full x-side round trip, so it almost certainly holds.
    It is, however, an assumption, and the RTL header does not state it.
- `merge_free_rejected`: **negative control of the fast checker.** It returns `false` on the reachable set
  (867 states) of the model without `excl`.

## Measurements (bd_link W = 2, 1048 states)

Machine shared by 12 agents. Peak RSS is that of the lean process, from `memtime.py`. Lake-wrapped runs show a
floor of about 800 MB, which is lake's own; direct `lean` runs show the true value.

| checker | wall | peak RSS |
|---|---|---|
| `Env.certify` + in-kernel `reachTree` (A-env) | killed at ~60 s | > 6 GB |
| `EnvFast.check`: tables + shared masks + external cert, one declaration | 108 s | 5.5 GB |
| same, 4 chunks | 79 s | 2.2 GB |
| `Kernel` form, one declaration | 24 s | 1.9 GB |
| **`Kernel` form, 9 chunks of 128** (whole `Link2.lean` file, before `link2_data_sound` was added) | **20 s** | **736 MB** |
| whole `Link2.lean` incl. `link2_data_sound` (752 more states) | 33 s | 738 MB |
| `Tables.lean` (7 LUT outputs, 1024-pair hazard tables for the 5-input ones) | 8.5 s | < 800 MB |
| `Merge.lean` | 3 s | < 800 MB |

Microbenchmarks (1048 states, one `decide +kernel` each), which explain the gains:
- `addrOf (pinVec s pins)` for 5 pins: 2.4 s, i.e. 2.3 ms per state.
- The same with `foldl`: 0.93 s.
- With a hand-written structural recursion: 0.57 s.
- With `List.rec`: 0.39 s.
- With `List.rec` plus raw `Nat.*`: 0.20 s.
- A single `bit` through the instance chain costs about 70 µs; a raw `Nat` op about 8 µs.
- `List.map` plus `length` on 4 elements: about 0.6 ms.

Scaling: time is linear in the number of (state, transition) pairs, at about 20 ms per state for this model
(4 gates, 10 signals, about 4 transitions per state). Memory is set by the chunk size.
- A 10^4-state model would take about 3-4 min with 80 chunks, at under 1 GB.
- 10^5 states would take about 35 min. That is the practical limit of kernel `decide`.
- The certificate file grows at about 70 B per state: 75 kB for link2.

## What does not check / was not done

- **bd_mux and bd_arb were not modelled** (time box). bd_mux follows the same recipe as bd_merge. bd_arb needs a
  model of the arbiter's nondeterministic resolution.
- **`kpersist` still loops over `n` signals.** A bit-parallel form would cut about 30 % at these sizes (sketched in
  `Wip/EnvFast.lean`).
- **The data mux of bd_merge is not modelled**, so the matched delay of `z_req` against the data is not covered.
- **`Wip/Env.lean` still states `link2_sound` with `sorry`.** It is now proved here as `EnvFast.link2_sound`. I may
  not edit that file; the lead can point it at `Formal.Core.EnvFast.Link2`.

## Verdict

**It works.**
- The proved-once checker turns Env certificates from "about 10^3 states, more than 6 GB" into "linear time,
  bounded memory". The W = 2 link (the conjecture) checks in 20 s at 0.74 GB, and its data-validity variant
  in 13 s more.
- A new cell (bd_merge) took about 30 minutes end to end. It produced one new named timing assumption
  (`selFast`) and two derivations of the header's prose.
- **Effort to finish.**
  - bd_mux: about 1 h.
  - bd_mlink / bd_flink controllers: about 1 h each.
  - bd_arb: about half a day (modelling the resolution).
  - Multi-cell compositions (two links in a pipe, about 10^4-10^5 states): mostly certificate generation, at
    minutes of kernel time each.
- **What it buys.** Env-style SI + hazard + persistence certificates for whole cells and small compositions,
  kernel-checked, without `native_decide`. The trusted part is unchanged: `Env`'s semantics, `LutAudit`'s
  `classify`, and the proofs in these files. Tables and certificates are untrusted data.

## Fidelity

- **Semantics.** Identical to `Env`, as proved, so `A-env.md`'s fidelity notes apply verbatim: H_SETTLE,
  H_FB_FUND, H_BUNDLE, atomic/inertial firing, and the hazard notion of LutAudit.
- **bd_merge model, new primitives and assumptions:**
  - **`bd_delay` is one wire element** with an unbounded delay. A chain of LUT1 buffers is modelled as a single
    inertial element: no runts propagate, and a withdrawn excitation is reported. This is faithful for an
    unbounded-delay check. The matched-delay property (z_req after data) is not modelled, because data is absent.
  - **`rst` is held at 0** and the start state is all-zero, i.e. reset was released after the loop cleared
    (H_RST_LONG, as in `A-env`).
  - **`excl`** is the cell's documented obligation. Test: assertion monitors in GLS/board, or the compiler's
    guarantee that bd_merge is used only where the inputs are exclusive.
  - **`selFast`** says that `sel` (one LUT2 behind `x_ack`) settles before the x sender's next request, and before
    `x_ack` falls again. Test: GLS with the routed SDF, comparing the max delay of `x_ack→sel` against the min
    delay of `x_ack→(sender)→x_req` and of the full x round trip. Expected margin: one LUT against a whole
    handshake loop.
