# A-events9 (probe HDsub): HDsub proved by a first-reach SUB rule (shard A)

STATUS (2026-10-29, probe HDsub): Lean DONE in a private overlay (0 errors, no sorry), 16 rows
rerun; xevents8 comparison and negative controls: see "Runs" (filled in as they finish).
check.sh: see "Check" below.

## Verdict

**HDsub is no longer a hypothesis.** `Events9.design_verdict9` is `Events8.design_verdict8`
with the 126 `dsub` hypothesis judgements PROVED by a new log rule `dsub9`, instead of
assumed. On gcd_hw R5 (seeds d/3/4/5) every one of the 126 judgements carries a valid
first-reach walk on all 16 rows, so the rows are exactly the Events8 rows (same certified
items, same margins, same verdict) with HDsub removed from the hypothesis list.

**Hypotheses of `design_verdict9` (exact; `Formal/Core/XAudit/Events9Beh.lean`).**
Given `Recog6 d net b rn rank rw fuel`, `net.OK7`, `runLog net b parts log = some J`, and the
checker's per-item results (`hcp`/`hcx`/`hcl`/`hcg`: `backOK7`/`exclOK7`/`lineOK7`, and
`guardOK8 … (hl.map (san J)) …` on the SANITIZED hypothesis lines) — all evaluated by
`xevents9` — then for every per-pin behaviour `x` of the parsed netlist with
- `SatPin d plG x` (the per-pin netlist semantics),
- constant wires (`x (wire 0) = false`, `x (wire 1) = true`), reset `x (wire rw) t = decide (t < T)`, `1 ≤ T`,
- `HARB7 net b rn x cv` (H_ARB),

and every select sequence `sel`, there is a `Beh7` `bh` realising `x` (its counts give `x`'s
control wires, its guarded count is `gcnt`) such that
- `SelPart sel parts` → `bh.SelOK` → (residual obligations of the items NOT certified: Back
  `P ≤ M+1`, merge `fodd ≤ 1`, line `ContigF`, guard `GuardPin`) →
  every real LUT wire equals its reset value flipped `M t j` times, at every time `t`.

On a CLEAN row the residual obligations are vacuous, so the verdict rests on: **SatPin,
constants + reset, H_ARB, SelOK, SelPart**. Neither GuardOK nor HDsub is a hypothesis.
Trusted (not proved): the JSON/netlist parsers, the certificate reader and its mapping to
`Net4`/`Bands4`/`RNode`/`Ln`/`GD`/`HLn9`, the printed numbers, and Lean's `--run`
interpreter/compiler. `design_guardOK9`: on a row with every guarded pin certified,
`Beh7.GuardOK` holds (same hypotheses).

**What it does NOT cover.** H_ARB, SelOK, SelPart remain hypotheses (E8Hyp's subject). The
bands are the committed ones (xray_delay 99b10a6d), which omit the slice OUTMUX hop on
O5/F7/F8 arcs (audit row; probe E8Mux); a CLEAN row is a statement about THOSE bands. The
indep/gb residual rows are unchanged from Events8 (margin failures, not HDsub).

## The rule `dsub9`

A `dsub` judgement (Events8) is a SUB conclusion for a labelled walk that starts at the
guarded source `a = D` instead of the label source `S`. Rule `dsub9` adds one premise:
a log line `wS`, an unlabelled walk `S → a` with at most one token (any delay):
`M v S ≤ M (v − dW) a + tW`, `tW ≤ 1` (`Events9Cert.WSOK`: `J[wS].u = false`, `c = none`,
`a = S`, `bb = a`, `t ≤ 1`).

Soundness, by strong induction on time `u` (`Events9Cert.first_reach`, abstract; instantiated
in `dsub9_sound`): with `m = M u a` and `s = F xm (u − d1)` the merge sample,
- if `M s S ≤ m`, conservation (`filt_ℓ m + Σ_{i≠ab} filt_i m ≤ m`) and `w1` give
  `filt_ℓ m ≤ P xm ab s + t1` (as the Events7 SUB rule);
- if `M s S ≥ m + 1`, `wS` says `a` had already reached `m` at `u' = s − dW < u`
  (strict because `F xm v < v`, `F 0 = 0`); monotonicity gives `M u' a = m`, and the induction
  hypothesis at `u'` plus monotonicity of `P xm ab ∘ F xm` give the bound at `u`.
Then `w2` finishes exactly as the Events7 SUB rule. This is the "first time S reaches 2k+1"
argument of A-events8 as a well-founded descent; no parity or timing margin is needed.

`san J : HLn9 → HLn` keeps a `dsub` line only if `wsOK J S a wS`; otherwise it becomes
`copy J.size` (no judgement, so a guard certificate citing it is rejected). `hdsub_san`:
`Events8.HDsub` holds for `hl.map (san J)` for EVERY behaviour. `verdict9` = `verdict8` on the
sanitized list with that proof.

Lean-level negative controls (in `Events9Cert`):
- `first_reach_two_tok_neg`: with `Sc v ≤ Dc (v − dW) + 2` (a 2-token walk) every other premise
  of `first_reach` holds and its conclusion fails (concrete counts). So `t ≤ 1` is needed.
- `dsub_counts_neg`: counts at ONE time satisfying `w1`, the other arm's U-bound and even the
  1-token walk at that time violate the conclusion: the descent in time is essential.

## Lean files (Mathlib-free)

- `Formal/Core/XAudit/Events9Cert.lean`: `first_reach`, `filt_tf`, the two controls, `HLn9`,
  `HLn9.isD`, `WSOK`/`wsOK`, `san`, **`dsub9_sound`**, **`hdsub_san`**, **`verdict9`**.
- `Formal/Core/XAudit/Events9Beh.lean`: **`design_verdict9`**, `design_guardOK9`.
- `Formal/Core/XAudit/Events9Main.lean`: the `xevents9` executable (Events8Main + `HLn9`
  reader with field `wS`, sanitizing with `san` before `guardOK8`).

Fixes made this session to the 2026-10-28 snapshot (Wip/_snapA): the `h3` monotonicity step
in `dsub9_sound` had its arguments reversed (a false `omega` goal); `let d1` blocked `omega`
(inlined); `HLn9.isD` moved from Main into `Events9` (field notation); two tactic fixes in the
`first_reach_two_tok_neg` proof; a dead `exact` removed. No statement changed.

## For the lead

Lakefile stanza (NOT added; lakefile.toml untouched):

```toml
[[lean_exe]]
name = "xevents9"
root = "Formal.Core.XAudit.Events9Main"
```

Root imports if wanted: `Formal.Core.XAudit.Events9Cert`, `…Events9Beh` (not `Events9Main`,
which defines `main`). Until the stanza exists, `tools-A/xaudit/events9/xe9.sh` runs it with
`lake env lean --run Formal/Core/XAudit/Events9Main.lean` against an overlay `$OL` of oleans
(built by `mk9.sh`, or here by the probe's scratch `bdeps.sh`; the lead's `.lake/build` had no
XAudit oleans yet this session).

## Runs
