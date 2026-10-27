# A-envfast-2: bd_mux, bd_merge with its data mux, and bd_steer, by the EnvFast recipe

Shard A. Namespace `Formal.Core.EnvFast`. Toolchain: Lean v4.35.0, core only (no Mathlib import).
No routed numbers are involved, so no nextpnr fingerprint applies.

## Obligations the RTL headers do not state (read these first)

1. **bd_mux needs `rtz`** (`mux_needs_rtz`, `muxD_needs_rtz`).
   - After `z_ack↓`, the previous token's acknowledge (`x_ack`, excited to fall) must fall before `z_ack`
     rises again for the next token.
   - Otherwise: x and y both request, the control selects x, x's transaction runs until `z_ack↓`, a new
     control token selects y, `j1` fires on y's waiting request, and the receiver raises `z_ack`.
     `x_ack`'s excitation to fall is then withdrawn: a runt on `x_ack`, or an acknowledge that never
     returns to zero.
   - bd_mux is therefore not speed-independent even with every fork isochronic. Shard B found the same
     race (`H_MUX_RTZ`, `formal/notes/B-merge-mux-si.md`) in a gate-atomic model. This derivation is
     independent and at LUT level, and it fails as a withdrawn excitation at `uxa`.
   - Slack: one LUT (`uxa`) against `z_ack↓ → control sender → ctl_req → join → uor → DELAY → receiver
     → z_ack↑`.
2. **At the join pins, the select must be held until `ctl_req`'s fall has propagated through the join,
   not just until `ctl_ack↓`** (`sHold`, `muxCr_needs_hold`).
   - The header argues that `s` is "held … from ctl_req-rise until ctl_ack-fall", so "the select is
     valid across exactly the output window". That argument treats the `ctl_req` fork as isochronic.
   - With the `ctl_req` branch at `uj1` delayed, `s` can move while `ctl_req↓` is still in flight
     inside `uj1` (y requesting). The MIC `(ctl_req@uj1↓ ∥ s↑)` crosses the vertex `ctl_req·s = 1`.
     That is a static-0 function hazard on `j1`, i.e. a spurious join for y.
   - The same model needs `crSettle`: the branch settles before `ctl_req` toggles again
     (`muxCr_needs_settle`, a runt into the deselected join).
3. **The `z_ack` fork of bd_mux** (`muxZa_needs_settle`, `muxZa_needs_iso`).
   - Each branch (at `uxa`, at `uya`, and `ctl_ack`) must settle before `z_ack` toggles again.
   - The branch at `uxa` (`uya`) must also settle before `j0` (`j1`) changes. Otherwise a stale
     `z_ack@uya` meets `j1↑` as the MIC `(z_ack@uya↓ ∥ j1↑)`, a static hazard on `y_ack`, i.e. a
     spurious `y_ack` pulse.
   - Shard B's `mux_needs_iso_za` is the same race.
4. **Correction to A-envfast's `selFast` finding for bd_merge** (`mergeD_sound`).
   - Once `sel` is treated as what it is, a data-path signal feeding only `bd_datamux`, **`selFast` is
     not needed**. Both of its violations (a runt on `sel`, and the static-1 MIC on `usel`) occur with
     the output window closed, where `sel` steers data nobody samples.
   - `Merge.merge_needs_selFast` stays true for the control-only reading.
   - What remains is weaker and is a fidelity hypothesis, not a theorem: a runt on `sel` outside the
     window dies out before the next window opens. The next window is a whole handshake away.
   - This reconciles A-envfast with Shard B's `merge_ok`, which exempted the select cone as data and
     needed no select-timing assumption.

The matched delay (`bundle`, `verify/tighten.py` rule A) is stated in the headers. It is derived necessary
here for both cells (`muxD_needs_bundle`, `mergeD_needs_bundle`), as are merge exclusivity
(`mergeD_needs_excl`, with data) and the steer's setup (`steer_needs_setup`).

## Files (all new; no existing file edited)

| file | status | content |
|---|---|---|
| `formal/lean/Formal/Core/EnvFast/Data.lean` | proved | `DSpec`, `stepOKD`, `SoundD` (Env.Sound with a bundled-data window), its kernel checker `kcheckD_sound`/`kcheckD_SoundD`, witness lemmas |
| `formal/lean/Formal/Core/EnvFast/MuxModels.lean` | definitions | `muxModel`, `muxZaModel`, `muxCrModel`, `muxDModel`, `mergeDModel`, their assumption structures, `muxQ`, `muxDQ`, `mergeDQ`, `muxDSpec`, `mergeDSpec` |
| `formal/lean/Formal/Core/EnvFast/Tables2.lean` | proved, generated | tables of `bd_mux_uj0/uj1/uor`, `bd_datamux` LUT3 and LUT6_2 O5/O6, each checked against `outB`/`classify` |
| `formal/lean/Formal/Core/EnvFast/MuxCompiled.lean` | proved | compiled models, `KCompiled` proofs, kernel forms of the Q's with equality proofs |
| `formal/lean/Formal/Core/EnvFast/{MuxCert,MuxDataCert,MergeDataCert}.lean` | data, generated | certificates (untrusted) |
| `formal/lean/Formal/Core/EnvFast/Mux.lean` | proved | bd_mux control path, three fork variants, five negative controls |
| `formal/lean/Formal/Core/EnvFast/MuxData.lean` | proved | bd_mux with `bd_datamux` |
| `formal/lean/Formal/Core/EnvFast/MergeData.lean` | proved | bd_merge with `bd_datamux` |
| `formal/lean/Formal/Core/EnvFast/Steer.lean` | proved | bd_steer (bd_ctl.v), via `Env.certify` directly |
| `formal/tools-A/envfast/Gen2.lean` | tool | untrusted generator: tables, certificates, chunk-theorem text |

`Gen.lean` was not modified. Gen2 regenerates `MuxCert.lean`/`MergeDataCert.lean` byte-identically
(checked with `cmp`).

## How to check

    cd /home/user/asyncfpga3/formal/lean && ../check.sh Formal/Core/EnvFast/Data.lean \
      Formal/Core/EnvFast/MuxModels.lean Formal/Core/EnvFast/Tables2.lean Formal/Core/EnvFast/MuxCompiled.lean \
      Formal/Core/EnvFast/MuxCert.lean Formal/Core/EnvFast/Mux.lean Formal/Core/EnvFast/MergeDataCert.lean \
      Formal/Core/EnvFast/MergeData.lean Formal/Core/EnvFast/MuxDataCert.lean Formal/Core/EnvFast/MuxData.lean \
      Formal/Core/EnvFast/Steer.lean

The committed modules (Env, EnvFast, Kernel, Tables, Models) are taken from lake's build. The result is
recorded at the end of this file.

To regenerate (from formal/lean, with the oleans of Data and MuxModels on LEAN_PATH):

    GEN2_CHUNKS=/tmp/ch ../slot.sh lake env sh -c 'LEAN_PATH=<overlay>:$LEAN_PATH lean ../tools-A/envfast/Gen2.lean'

## The relaxation for data paths (`Data.lean`): what is new in the trusted part

`Env.Sound` asks every LUT to see a hazard-free MIC and every excited element to persist, on every
reachable transition. That is right for control and wrong for a bundled-data mux. Every honest
environment loads the next data and the next select concurrently while the output is idle, and the
LUT may glitch then; nobody samples it.

`DSpec` names the data outputs (`dout`) and the output hold window (`win`: `z_req ∨ z_ack`, the
library's `req↑ … ack↓`). `stepOKD` is `stepOK`, except that a data element is exempt from both the
MIC check and persistence on a transition whose window is closed before and after.

- Control elements are never exempt. `SoundD.lutOK_ctl` and `SoundD.persist_ctl` give exactly the
  `Env.Sound` guarantee on the control path.
- Data elements are checked whenever the window is open on either side (`SoundD.lutOK_data_win`).
- With no data elements the two notions coincide (`soundD_none_iff`).

Data validity is part of each model's `Q`: in the window the mux output is not excited and equals the
selected (merge: live) input's bit.

The kernel checker reuses every evaluation piece of `Kernel.lean` and its equality proofs. Only
`kpersistD`, `kstepOKD` and `kstateOKD` are new; each is proved equal to its spec (`kpersistD_eq`,
`kstepOKD_eq`), and `kcheckD_sound` is proved once. This is the one new piece of trusted specification:
whoever reads `SoundD` must agree that `exempt` is the right notion (see Fidelity).

## Results (exact theorem names)

**bd_mux, control path** (`Mux.lean`; LUTs `bd_mux_uj0`, `bd_mux_uj1`, `bd_mux_uor` and two `bd_c2_u`
from LutCells; `bd_delay` is one wire):
- `mux_sound : Sound (muxModel ⟨true⟩) (muxQ …)`. Every fork is isochronic; `rtz` holds. 436 states.
  - `muxQ` checks four things: liveness; `x_ack↑` only with `s = 0` and `y_ack↑` only with `s = 1`;
    the receiver may acknowledge only while `ctl_req` is high; and exactly the selected join has fired.
- `muxZa_sound`. The three branches of `z_ack` are separate unbounded wires; `rtz`, `zaSettle` and
  `zaIso` hold. 3832 states.
- `muxCr_sound`. The `ctl_req` branch at `uj1` is a wire; `rtz`, `crSettle` and `sHold` hold. 911
  states.
  - The x/y, s/¬s symmetry of the cell covers the `uj0` branch alone.
  - Both branches lagging at once is not covered: the explorer ran past 60000 states.
- Negative controls, one per assumption, each an explicit trace replayed by the kernel:
  - `mux_needs_rtz`
  - `muxZa_needs_settle`
  - `muxZa_needs_iso`: the hazard at `uya` and a withdrawn `y_ack` excitation
  - `muxCr_needs_settle`
  - `muxCr_needs_hold`: a static-0 hazard at `uj1`

**bd_mux with its data mux** (`MuxData.lean`, W = 1, `bd_datamux` odd-bit LUT3, `z = s ? y : x`):
- `muxD_sound : SoundD (muxDModel ⟨true, true, false⟩) muxDSpec (muxDQ …)`. `rtz` and `bundle` hold.
  4788 states.
  - x's data moves; y's bit is held at 1 and x's starts at 0, so a wrong selection is visible and the
    vectors are not degenerate.
  - **The header's "converts a timing obligation into a data one" holds.** No select-timing assumption
    is needed beyond the control channel's contract and the matched delay.
- `muxD_needs_bundle`: without the matched delay the window opens while the mux output still holds
  y's 1.
- `muxD_needs_rtz`.
- **Not kernel-checked: the model with both data senders free** (`muxDModel ⟨true, true, true⟩`).
  - The explorer found 27680 states and no violation.
  - The certificate is generated (`GEN_MUXD_FULL`, about 4 MB).
  - The kernel check measured 26 s per 128-state chunk (init + 4 chunks: 111 s, 2.3 GB RSS). That
    extrapolates to about 90 min, too much for the shared build. It is an explorer-only (untrusted)
    result.
  - Most of the per-chunk cost is rebuilding the 27680-state BST in each declaration. The remedy is in
    "what does not check".

**bd_merge with its data mux** (`MergeData.lean`, W = 1, `z = sel ? x : y`, both senders carry data):
- `mergeD_sound : SoundD (mergeDModel 1 ⟨true, false, true⟩) mergeDSpec (mergeDQ 1 …)`. `excl` and
  `bundle` hold; `selFast` does not. 2630 states.
  - `mergeDQ` checks `EnvFast.mergeQ` (no acknowledge for a token the merge did not carry; liveness).
  - It also checks that in the window `z_data` is not excited and equals the live input's bit.
- `mergeD_needs_bundle`: `z_req` rises before `sel` follows `x_req`, so the window opens on y's data.
- `mergeD_needs_excl`: y's token is acknowledged for x, with data.
- (The variant with `selFast` as well has 2386 states and also passed the explorer. It is not claimed:
  it adds an assumption the claimed theorem shows unnecessary.)

**bd_steer** (`Steer.lean`, part 3 of the task; LUT6_2 `bd_steer_u` O5/O6 and LUT2 `bd_steer_uack`):
- `steer_sound`. The only assumption is the bundling contract (`s` before `req`, encoded causally).
  34 states (`steer_cert`).
  - This is the header's "a constant cannot glitch a branch … return to zero is immediate and
    unconditional", derived. No hold assumption is needed.
- `steer_needs_setup`: `s↑ ∥ req↑` is a static-0 hazard on `req0`.

bd_end was not modelled. `bd_src` (req = ¬ack through a LUT1) against a four-phase receiver is a
two-element ring with no MIC, so nothing to find.

## Measurements

Wall times are from `memtime.py`, with the machine shared by about 12 agents (two `xaudit` processes at
100 % throughout). Peak RSS is that of lake-wrapped `lean`.

| file | states | wall | peak RSS |
|---|---|---|---|
| `Mux.lean` | 436 + 3832 + 911 | 250 s | 1.04 GB |
| `MuxCompiled.lean` + `MuxDataCert.lean` + `MuxData.lean` | 4788 | 362 s | 1.20 GB |
| `MergeDataCert.lean` + `MergeData.lean` | 2630 | 123 s | 0.95 GB |
| `Steer.lean` (in-kernel reachTree) | 34 | 4 s | < 0.8 GB |
| full mux data model, 4 of 217 chunks | 27680 | 111 s | 2.3 GB |

That is about 45 ms per state for these models (6-7 gates, 14-18 signals). That is twice link2's per-state
cost, because there are more gates and more pins per state.

**`maxRecDepth`.** `kmkTree` over more than about 1000 states hit the kernel's "deep recursion" limit.
`kfoldl kinsert` builds a chain of lazy `kinsert` thunks as long as the certificate. The files with
certificates set `maxRecDepth 100000`, which the kernel honours.

## What does not check / was not done

- **The full-freedom mux data model (27680 states), not kernel-checked.** See above. Remedy: give the
  certificate as a literal balanced `Tree` (depth 15), prove once that `kmkTree cert.flatten` equals it,
  and state the chunks against the literal.
  - This removes the per-chunk rebuild, which is most of the 26 s.
  - Estimated total after the fix: about 20 min (27680 × 45 ms). That is still heavy.
- **bd_merge W = 2** (LUT6_2 pair). The explorer passed 241313 states (stopped at 200000 explored) with
  no violation. That is beyond what this checker can claim; it needs data-bit symmetry reduction
  (`latch_bit_isolation`-style).
- **Forks not modelled, i.e. implicit isochrony assumptions:**
  - bd_mux: `j0 → {uor, uxa}`, `j1` likewise, `x_ack → {x sender, uxa feedback}`, `y_ack` likewise,
    and `s → {uj0, uj1, datamux}`. The setup of `s` at the joins is H_BUNDLE, encoded causally by
    `rdc`; its hold is `sHold`.
  - In `muxDModel` every fork is isochronic.
  - bd_merge (`mergeDModel`): every fork. Shard B shows the `z_ack → {uxa, uya}` and
    `x_ack → {usel, sender}` forks matter.
  - bd_steer: the `req` and `s` forks to O5/O6 are one LUT6_2, so they share pins (isochronic by
    construction).
- **The two `ctl_req` branches lagging together; all mux forks lagging together.** These are state-count
  limits (more than 60000 states), not failures.
- `FASTFALL` of bd_delay is not modelled (one wire, both edges).
- `bdc_muxn` (N-way) was not modelled.

## Verdict

**It works.**
- The recipe (model, generated tables plus untrusted certificate, chunked kernel check, `Env.Sound`) carried
  over to bd_mux with no change to the trusted checker.
- For data paths it needed one new, small, proved-once relaxation (`SoundD`).
- bd_mux took about 1 h of modelling, the data relaxation about 30 min, merge-with-data about 20 min,
  and steer about 10 min. The rest was explorer runs and kernel time.

Findings:
- `rtz` and the pin-level select hold (`sHold`) are not in the bd_mux header.
- The `z_ack` and `ctl_req` fork conditions are derived and named.
- `selFast` turns out not to be needed for bd_merge's data correctness.

**Effort to finish:**
- The full-freedom mux data model, with the tree-literal remedy: about 2 h plus about 20 min of kernel
  time.
- W = 2 merge/mux: needs bit-symmetry reduction, about half a day.
- All-forks-delayed variants: a symbolic or partial-order-reduced explorer, about 1 day.

**What it buys.** Each assumption is a named, kernel-necessary obligation that maps to a GLS or
`tighten.py` check, at LUT-MIC level for the real INITs. A changed INIT in `cells/rtl` regenerates
LutCells and Tables2 and re-runs these certificates.

## Fidelity

All of `A-env.md`'s fidelity notes apply verbatim: H_SETTLE, H_FB_FUND (the join and C-element feedback
pins are zero-delay), atomic/inertial firing, LutAudit's hazard notion, and H_RST_LONG (rst held 0, every
signal 0 at start). Specific to this probe:

- **Data exemption (`SoundD`).** A glitch or runt on a data element while the output window is closed is
  allowed. This is faithful if the consumer's latch is closed outside `z_req↑ … z_ack↓`, which is the
  library's protocol (LIBRARY.md: data stable from `req↑` to `ack↓`).
  - It also assumes that a runt there has died out before the window opens: an inertial-delay assumption
    on the data LUTs.
  - Test: GLS with routed SDF, injecting the select/data MIC just before `z_req↑` at the minimum
    handshake spacing.
- **`rtz`.**
  - Meaning: the max delay of `z_ack↓ → x_ack↓` (one LUT) is less than the min of
    `z_ack↓ → ctl sender → ctl_req↑ → uj1 → uor → delay line → receiver → z_ack↑`.
  - Test: GLS assertion "`x_ack` and `y_ack` both low at every `z_ack↑`".
  - Expected margin: one LUT against a full round trip including DELAY.
- **`zaSettle`, `zaIso`, `crSettle`.** These are fork skew against a half or full handshake through the
  environment.
  - Test: routed max skew of the `z_ack` and `ctl_req` nets against the min loop delay.
- **`sHold`.**
  - Meaning: `ctl_req`'s fall reaches and settles in `uj1` (`uj0`) before `s` changes at that pin.
  - In silicon the control sender sees `ctl_ack↓`, which needs `z_req↓`, which needs `j0↓`/`j1↓`, which
    need `ctl_req↓` at the selected join only. So the margin at the deselected join is the full
    `ctl_req → selected join → uor → delay → receiver → ctl sender → s` path against the `ctl_req` branch
    skew.
  - Test: the `cell_constraints.json` hold check on `s` at both join pins.
- **`bundle`** is rule A of `tighten.py` (the delay line's rise after `sel`/`s` and the data mux output).
  It is modelled as a priority of the data element over the `z_req` wire, so it covers both edges; the
  fall direction is vacuous here, because data and select are held through the fall.
- **Environment.**
  - Mux control sender: `s` moves only while `ctl_req = ctl_ack = 0` and before `rdc`. That is the
    header's contract.
  - Data senders likewise.
  - Receiver: any four-phase partner. Merge senders: `excl` as in A-envfast.
  - These are the protocol, not timing.

## Check result

- `../check.sh` on the ten files from Data.lean to MuxData.lean, in the order of "How to check" without
  Steer.lean:
  - Result: `[audit] 1433 declarations checked`, `[check] OK`.
  - Wall 720 s, peak RSS 1.56 GB.
- `../check.sh Formal/Core/EnvFast/Steer.lean`: `[audit] 689 declarations checked`, `[check] OK`.
- No `sorry`, `admit`, `axiom`, `native_decide` or `bv_decide`; only `decide +kernel`.
- After the final run, Gen2 regenerated `Tables2`, `MuxCert`, `MuxDataCert` and `MergeDataCert`
  byte-identically (`cmp`).
