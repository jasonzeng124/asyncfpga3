# A-events7: U3, n-ary merges, guarded delay lines and the cascade — gcd_hw CLEAN at one corner (shard A)

## Verdict

**Works. Every gcd_hw seed is CLEAN at slow, at fast and (3 of 4 seeds) at gb.** A CLEAN row
is a theorem (`Events7.design_verdict7`) about every per-pin behaviour of the routed netlist, with
no residual item, under five named hypotheses:

- per-pin `SatPin` (the netlist semantics; no H_ATOMIC_LUT);
- H_ARB (`HARB7`, the arbiter cores as virtual mux cores, unchecked);
- SelOK (bundling of the selects, E6);
- **SelPart** (new: the pattern groups of one multi-bit select are never true together);
- **GuardOK** (the guarded-pin timing, W-E4g, still open).

| item of the task | result | residual items removed per seed and corner |
|---|---|---|
| (1) U3: labels through merges | **done** (`uW` lines through a merge's `r3` line) | 28 |
| (2) guarded multi-copy pin kind | **done** (`Beh7`, `Net4.OK7`) | 6; their obligation is now GuardOK, no longer a false `PinOK` |
| (3) W-E4g: GuardOK from ENTRY/EXIT | **not done**. Reduction stated in `Wip/Events7.lean` | — (GuardOK stays a hypothesis) |
| (4) W-E4x: the 3-way merge | **done** (n-ary R3 / SUB / exclusivity under SelPart) | 7 |
| (5) the cascade `control_merge12` | **done: it composes** under H_ARB as already stated (see §3) | 4 |

The per-item counts are from the ablation on seed d slow (§4). They sum to 45 = A-events6's
structural residual. The 4 cascade items fall to search alone: every R3 candidate of a merge is now
tried, not only ana's first one. No new Lean rule was needed for them.

**Residual items per seed and corner** (A-events6 → A-events7; strict margins):

| seed | slow | fast | mixed (indep) | gb |
|---|---|---|---|---|
| d | 45 → **0 CLEAN** | 45 → **0 CLEAN** | 54 → 9 | 45 → **0 CLEAN** |
| 3 | 45 → **0 CLEAN** | 45 → **0 CLEAN** | 58 → 13 | 45 → **0 CLEAN** |
| 4 | 45 → **0 CLEAN** | 45 → **0 CLEAN** | 55 → 10 | 45 → **0 CLEAN** |
| 5 | 45 → **0 CLEAN** | 45 → **0 CLEAN** | 53 → 8 | 46 → 1 |

What remains is a timing finding, not a gap in the judgements:
- **mixed:** the per-pin margin failures of A-events6 §3: 6 to 8 Back pins and 2 to 7 lines
  per seed, each with the same name and margin as before.
- **seed 5 gb:** the rig environment `uenv1 ← uenv0`, Back −61 ps.

The structural classes are 0 on every row.

**Toolchain, for every routed number above:** builds and bands are A-events5's (nextpnr sha256
9c732bc6303458df, 9/9 fingerprints; md5s in `events5/builds.txt`), the same inputs as A-events6.
There was no new build. Every row is one route of one placer seed; the 4 seeds are the spread.

## Files

| file | status |
|---|---|
| `formal/lean/Formal/Core/XAudit/Events7Core.lean` | **proved**. `Net4.OK7`, `Beh7` (guard pins may have many copies, read as the AND/OR of all), `Beh7.safe`, count lemmas |
| `formal/lean/Formal/Core/XAudit/Events7Excl.lean` | **proved**. Labels `lx`, **SelPart**, `fsum_filt_le` (n-ary conservation), `fodd_filt_le`, `excl_stepN`, **`merge_exclN`**, negative control `selpart_neg` |
| `formal/lean/Formal/Core/XAudit/Events7Cert.lean` | **proved**. The derivation LOG (`Jd`, `Ln`, `concl`), `sem_r3` / `sem_sub` (any arity), `sem_uT`, **`concl_sound`**, **`runLog_sound`**, `backOK7` / `lineOK7` / `exclOK7` with soundness, **`verdict7`** |
| `formal/lean/Formal/Core/XAudit/Events7Beh.lean` | **proved**. `ND7`, `HARB7`, `ndReal7`, `init0_7`, **`design_beh7`**, **`design_verdict7`** |
| `formal/lean/Formal/Core/XAudit/Events7Main.lean` | executable **`xevents7`**, audited |
| `formal/lean/Wip/Events7.lean` | W-E4g reduction (`guardOK_of_entry_exit`, `sorry`). `guardCnt_mono` is proved there. It compiles |
| `formal/tools-A/xaudit/events7/cert7.py` | UNTRUSTED certificate emitter (cert6 nodes + log search; flags `--no-u3 --no-nary --no-gline`) |
| `…/events7/run7.sh`, `abl7.sh`, `neg7.sh`, `guard7.py`, `table7.py`, `mk.sh`, `xe7.sh` | runs, ablation, negative controls, the guard evidence, the table, the olean overlay, `lean --run` |
| `…/events7/xe7_<seed>_<corner>.txt` (16), `cert7_*.txt` (16), `xe7_d_slow_ABL*.txt` (4), `xe7_d_slow_NEG*.txt` (6), `table7.txt`, `guard7.txt` | results |

### Check

From `formal/lean`:

    ../check.sh Formal/Core/XAudit/Events7Core.lean Formal/Core/XAudit/Events7Excl.lean \
      Formal/Core/XAudit/Events7Cert.lean Formal/Core/XAudit/Events7Beh.lean \
      Formal/Core/XAudit/Events7Main.lean

Result:
- `[audit] 2358 declarations checked`;
- then `[audit] 2588 declarations checked` (the executable's own run);
- `[check] OK`.

There is no sorry, admit, axiom, native_decide or bv_decide. Events6* and Events5 are in lake's
build now, so they need not be listed.

### Lakefile stanza (for the lead; I did not edit the lakefile)

```toml
[[lean_exe]]
name = "xevents7"
root = "Formal.Core.XAudit.Events7Main"
```

**Usage:** `xevents7 SKEL.json BANDS.json CERT.json [--fuel F]`.
- `CERT.json` comes from `python3 tools-A/xaudit/events7/cert7.py SKEL.json BANDS.json CERT.json`.
- Until the stanza exists, `run7.sh` runs it with `lean --run` on `/tmp/events7/olean` (built by
  `mk.sh` through `slot.sh`).
- One run takes about 21 s.

## 1. What is proved

### `Beh7`: guarded delay lines (task 2)

**The change.** `Net4.OK` forced a guarded pin to one copy. In `Beh7`, a `guard` pin's `hpin`
reads the AND (FASTFALL) or OR of all its copies, exactly as a `multi` pin. `Net4.OK7` drops the
one-copy condition for guard pins only.

**Why nothing else changes.**
- The count of a guarded pin is still the behaviour's `gc`.
- `safe`'s guard case never uses `hpin`. So `Beh7.safe` is `Beh4.safe` with the same proof.
- `Recog6` is unchanged: the copies of a guard pin are `chkT`-checked like any tree pin.
- `ndReal7` proves the guard case of `hpin` as the multi case.

**The 6 `umux3/4/5` acknowledges.**
- Before: they entered `Net4` as `multi` pins, and their residual obligation was a `PinOK` that is
  false in general.
- Now: they are `guard` pins covered by GuardOK, the same hypothesis as the other 57 guarded pins.
- `xevents7` prints "guarded delay-line pins 6" on every row.

### The derivation log (tasks 1, 4)

**The format.** A certificate is a flat list of lines. Each line derives one judgement `Jd` from
earlier lines. There are two judgement kinds:
- **walk:** `M u a ≤ M (u−d) bb + t`, or the same with `filt (sel g) β (M u a)` on the left;
- **U-bound:** `M u a ≤ filt (sel g) β (M (u−d) bb)`.

**The rules.**

| rule | what it derives |
|---|---|
| `refl` / `r1` / `fpin` / `lift` | as in `Events5.WD` |
| `r3` | a merge of ANY arity: each arm is U-bounded, directly (steered arm) or by a U-bound line, with pairwise exclusive labels of one source |
| `sub` | SUB at a merge of any arity |
| `uT` | a stage's filtered pin is a U-bound |
| `uW` | a token-free walk followed by a U-bound is a U-bound |

**How the log removes the residuals.**
- **U3.** A U-label passes through an inner merge because the walk part of a `uW` line may itself
  be an `r3` line. Example: `cond_br42`'s acknowledge OR reads `cond_br38`'s acknowledge OR.
- **Search.** The log replaces A-events6's `DW` tree, whose `UA` witnesses walked through stage
  pins only. It also lets the search share U-bound lines: 3338 lines on seed d.

**Soundness.**
- `concl_sound`: if every earlier line holds for a behaviour, the new line holds, under SelPart.
- `runLog_sound`: every line of an accepted log holds, for every behaviour `x : Beh7`.

**n-ary merges.**
- `sem_r3` uses `fsum_filt_le`: pairwise exclusive branch counts of `m` sum to at most `m`.
- `sem_sub` uses the same lemma, with the target arm's term split off (`fsum_split`). Exact
  conservation (`filt_add`) is not needed, so SUB holds for any arity.
- `merge_exclN` is the n-ary `Events4.merge_excl`. The step `excl_stepN` argues by
  `Σ x ≤ Σ f ≤ m ≤ Σ y + 1`: either the arms did not move, or they equal the branch counts, of
  which at most one is odd (`fodd_filt_le`).

**SelPart.**
- The 3-way merge `umux21` is steered by a 2-bit select. Each pattern (00, 01, 10) is its own
  group with branch `true`, as in A-events6.
- The three groups are exclusive only because they are indicators of ONE select value. That is
  SelPart: two groups of one partition are never true at the same index.
- It holds for every `sel` derived from one select-value sequence per select bundle, which is
  the `sel` that SelOK ties to the steer gates.
- The partitions are read from the certificate and printed. On gcd there is one: `[16, 56, 57]`,
  the three patterns of `ulink_n_index_97`'s select.
- A wrong partition would make SelPart a false hypothesis, just as a wrong group assignment
  already does for SelOK. This reading is trusted.

### The netlist-level verdict

**`design_verdict7`.** Hypotheses:
- `Recog6`, `Net4.OK7`;
- `runLog … = some J`, and the per-item checks against `J`;
- `SatPin`, constant wires, reset, `HARB7`;
- for every `sel` and every monotone `gc`.

Conclusion: there is a `Beh7` realising `x` such that, if it satisfies SelOK, SelPart, GuardOK and
the residual obligations, every real LUT wire equals `ph (v j) (M t j)` at every time.

## 2. What is open: W-E4g (task 3)

GuardOK stays a hypothesis. `Wip/Events7.lean` states the reduction I would prove next. It is
different from A-events6's.

**Why A-events6's choice of `gc` is not enough.**
- A-events6 read `gc` off the pin's value (`toggles + [pin ≠ feedback]`). That makes the
  read-value conjunct true by construction and leaves only monotonicity.
- But it also makes the guarded count say nothing about the guarded source `D`. A stale `z_ack`
  firing `x_ack` early would be "count-consistent".

**The proposed choice: `gc := guardCnt`, the branch count `filt (sel grp) br` of `D` read
through all copies.** Its monotonicity is proved (`guardCnt_mono`). Three log facts per guarded
pin are then needed:
- **BACK-G** (upper, local): `backOK7` for the pin seen as filtered.
- **ENTRY** (lower, global): a U-bound of the guard to `S`, plus `S`'s pin reading `D` inverted,
  with STRICT `hiC < loP(guard) + dU + loF S + loC S q`.
  - Read backwards, this is the "lower-bound walk judgement" that A-events6 said was missing.
  - It is a U-bound followed by an inverted pin, both already expressible as log lines.
- **EXIT** (upper, global): a walk from `D` with STRICT `hiC − loC + hiF + hiQ < d`.

**What remains, about 1 to 1.5 days.**
- Construct the `Beh7` whose `gc` is `guardCnt`. This is a joint recursion of `gc` and `M` in time.
- Prove the read-value conjunct copy by copy.

**Evidence meanwhile** (untrusted, `guard7.txt`: ana's ENTRY / EXIT, with W recomputed by
cert7's search):
- At slow and fast, all 63 guarded pins of every seed pass both rules. The minimum ENTRY is 195 ps
  (seed 3 fast) and the minimum EXIT is 493 ps.
- The 6 guarded delay lines have ENTRY ≥ 2026 ps and EXIT ≥ 4272 ps at every one-corner row.
- At gb, seed d has 3 ENTRY failures: the arbiter re-arm items of A-events5, down to −52 ps.
- At mixed there are 7 to 17 ENTRY failures and up to 1 EXIT failure per seed.

**So a CLEAN row is conditional on GuardOK.** At slow and fast, the analysis's own guard rules
hold on every seed. At d gb they do not.

## 3. The cascade composes (task 5)

**What the Wip of A-events6 assumed.** It said the cascade needs a 3-way virtual core. It does not.

**What H_ARB states.** `HARB` / `HARB7` is one hypothesis over ALL virtual nodes at once, both
cores of `control_merge12` included. Each core's virtual `ctl` reads its own `A0`, which for the
inner arbiter is the outer arbiter's real acknowledge `uarb2.ua1`. The composed network is just
the two virtual cores wired together.

**Why it failed before.** ana's R3 at the inner `R0` merge chose the source `ucond_br10_j`. That
group reached the grants' U-sets through their request pins, and it is the wrong source: no walk
leads back from it.

**What certifies it now.** The R3 through the inner core's own `vctl` (the arbiter group) gives
all 4 items:
- `uarb2.ua1` pin 0: `r1` into the outer grant → `r3` at the inner `R0` to `vctl1` → `r1` into
  `uarb2.ua1` (one token), margin positive at every corner;
- the two virtual Back pins;
- the inner `R0`'s exclusivity: walk `vctl1 → uarb2.ua1 → outer grant → R0`, one token.

A-events5 saw the same walks with an unpinned hash seed. Nothing new is assumed.

**Fidelity of the composition.** H_ARB abstracts an arbiter whose server acknowledges every
request in 4-phase. The inner arbiter's server is the outer arbiter's channel 1
(`A_1 = C(g_1, A0)`), which does. Whether either core is faithful at all is still the H_ARB
question: contention GLS and MTBF.

## 4. Runs, ablation and negative controls

**Runs.** `run7.sh` covers 4 seeds × 4 corners. Every row has:
- `Recog6` with 0 node failures out of 465 real nodes;
- `Net4.OK7` true;
- the log accepted (3338 lines on seed d slow);
- 69/69 merges certified, including the 3-arm one.

Per row, `table7.txt` lists:
- Back 830/830 (836 minus the 6 guarded lines, which are guard pins now);
- lines 158/158;
- every residual item.

**The minimum margins are A-events6's.** At slow, Back is 937 / 748 / 755 / 186 ps and the line
minimum is 2645 / 1818 / 2929 / 2344 (d / 3 / 4 / 5). At fast, Back is 423 / 332 / 334 / 107.

**One mixed-corner difference.** Seed 3's `umux4.uya` pin 1 is a Back pin at mixed (ana finds a
walk there, so it is not a guard pin), with margin −217. It is residual, as in A-events6.

**Ablation (`abl7.sh`, seed d slow; residual items):**

| extensions on | residual |
|---|---|
| none (A-events6 judgements, all R3 candidates) | 41 (33 Back, 7 Excl, 1 Line) |
| all but U3 | 28 |
| all but n-ary | 7 |
| all but guarded lines | 6 |
| all | **0** |

**Negative controls (`neg7.sh`, seed d slow; each must fail, and does):**

| control | injected | result |
|---|---|---|
| NEG-fb | +1500 ps on `ucontrol_merge4.uarb1.ua2`'s feedback arc | residual Back at **−382** (A-events6: −382); verdict not CLEAN |
| NEG-u3 | an `r3` line that a U-bound passes through gets two arms with one label | `concl` rejects line 75; the log is not accepted, so nothing is certified |
| NEG-nary | the select partition dropped | the 3-way lines are rejected (line 1160); log not accepted |
| NEG-narx | the 3-way merge's exclusivity gives two arms one pattern | `exclOK7` fails: 1 residual Excl |
| NEG-gline | a guarded delay line declared OR instead of AND | `Recog6` rejects exactly `umux3.uxa`: NOT RECOGNISED |
| NEG-casc | the inner `R0`'s two grants given one branch | `exclOK7` fails: 1 residual Excl |

**Lean-level control:** `selpart_neg`. Without SelPart, two groups of one partition both true
give `Σ filt = 2 > 1`.

## 5. Fidelity (gate-fidelity rule)

These rows are as in A-events6 §4: LUT, routes, delay lines, merges, steers, skeleton. The rest
changes as follows:

| item | model | status | test |
|---|---|---|---|
| guarded delay lines | the guard pin reads the AND of all copies, `chkT`-checked (exact); count from GuardOK | the structure is checked; the timing is GuardOK (W-E4g) | GLS of `bd_mux` with the `z_ack` line skewed |
| n-ary merges | stateless OR of 3 arms; exclusivity from `merge_exclN` under SelPart | SelPart is a hypothesis on `sel`, a consequence of bundling (E6) | GLS: the 2-bit select against the three steer gates |
| U through merges | `uW` through `r3`: proved | no new hypothesis | — |
| cascade | two H_ARB cores, composed | H_ARB, unchecked as before | contention GLS of `control_merge12` |

## 6. Effort and what it buys

**Effort.** About 4.5 h:
- reading: 0.7 h;
- Lean: 2 h. Core 0.2 h, Excl 0.4 h, Cert 0.8 h, Beh 0.2 h, Main 0.3 h, Wip 0.1 h;
- cert7.py: 0.5 h;
- runs, controls and notes: 1.3 h.

**To finish W-E4g:** about 1 to 1.5 days (the `guardCnt` realisation plus the three Bool checks
and their soundness). After that, a CLEAN row would hold under SatPin, H_ARB, SelOK and SelPart
only.

**What it buys.**
- On all four routed seeds, the gcd control is a theorem about every per-pin behaviour of the
  netlist at slow and fast (and at gb on 3 of 4 seeds), with no residual item.
- The A-events6 verdict was conditional on a false hypothesis (the 6 `PinOK` obligations). That is
  gone.
- What is left is explicit and short: GuardOK (with ana's evidence positive at one corner), the
  bundling hypotheses SelOK and SelPart, and H_ARB.
- The mixed-corner and seed-5 gb residuals are timing findings with names and margins, unchanged
  from A-events6.
