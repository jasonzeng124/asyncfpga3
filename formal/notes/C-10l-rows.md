# C-10l: finishing the capstone timing rows (shared-prefix credit, max nodes, X4/M3/C7, cm12 Fd)

Shard C, probe 10l, 2026-10-27. About 3 h. Core Lean only; no sorry, axiom or native_decide.
STATUS: Lean done and checked; tcheck extended (self-tests pass); route runs: see Results.

## Verdict

(filled in below, section Results; this section is rewritten last)

## What checks (exact commands)

    cd formal && ./check.sh Formal/Timing/MaxNode.lean Formal/Timing/SharedPrefix.lean   # [check] OK
    cd formal/tools/tcheck
    ./run10l.sh d 2 3 4     # sync --check; lake build (FORMAL_SLOT_CWD); toy, toycert, toypair,
                            # toycredit self-tests; per seed in parallel: extract.py --no-hi
                            # --rules10l CKD -> build/obl10l_S.tc/.json, tcheck -> build/t10l_S.out;
                            # summarize10l.py -> results/r10l_rows.tsv, results/summary10l.txt
    FORMAL_SLOT_CWD=$PWD ../../slot.sh lake env lean test/Axioms.lean   # incl. xverdict_sound

- `sync.sh` now also copies `Formal/Timing/MaxNode.lean` and `Formal/Timing/SharedPrefix.lean`
  (verbatim, `--check` passes). `run4.sh` / `run10k.sh` are untouched: the old instances use
  neither `credit` nor `maxn`, so their verdicts cannot change.
- The routes are C-10e's `build/tree_*` (same as C-10h/10k). No rerouting.

## Files (all mine)

| file | what |
|---|---|
| `formal/lean/Formal/Timing/MaxNode.lean` | `AllBefore` (H_ALL), `PotMaxOK`, **`potMax_sound`**, **`cel_needs_pin`**, **`ctl_needs_pin`**, `allBefore_of_pins`, `celFn`/`celNFn` hold lemmas, `celFn_half_excited` |
| `formal/lean/Formal/Timing/SharedPrefix.lean` | `CondB`, `CondA`, `Pot2OK`, **`pot2_sound`**, `pot2_sound_or`, `toy_ok` |
| `formal/tools/tcheck/Tcheck/Cert.lean` | `pot2OKb`, **`pot2OKb_sound`**, `xM`, `XInst`, **`xverdict`**, **`xverdict_sound`** |
| `formal/tools/tcheck/Main.lean` | parses `credit`, `aarc`, `xpair`, `acap`, `apot`, `maxn`; `reportX` |
| `formal/tools/tcheck/rules10l.py` | rules Xc, Xic, Xm (credited X/Xi; max nodes), K (X4 ctl fork), D (Fd diagnostics) |
| `formal/tools/tcheck/extract.py` | `--rules10l` hook only |
| `formal/tools/tcheck/run10l.sh`, `summarize10l.py` | pipeline and report |
| `formal/tools/tcheck/test/toycredit.tc`, `.expected` | self-test: uncredited FAIL, credited PASS, a lying potA refused (CERTBAD), OR FAIL vs max-node PASS |
| `formal/tools/tcheck/test/Axioms.lean` | adds `xverdict_sound`, `pot2_sound`, `potMax_sound`, `cel_needs_pin`, `ctl_needs_pin` |
| `formal/tools/tcheck/sync.sh` | MODS += MaxNode, SharedPrefix |

## The Lean

**`SharedPrefix.pot2_sound`** (the credit). Netlist `net` (cyclic allowed), 10a `Run`, a node
`e ≠ 0` (the late-side copy of the shared node X in phase 0), two potentials:
`potB` checked on every arc except those out of `e` (`CondB`), `potA` checked on every arc
except those out of the launch, with arcs out of `e` counting from 0 (`CondA`). Hypothesis
**H_CLEAN_EDGE(X)**: `e` changes only at `τ`. Conclusion: every change of `v ≠ 0` happens no
earlier than `min (potB v) (τ + potA v)`. Proof: strong induction on (time, node) as in
`pot_sound`; the cause arc comes from the launch (use B), from `e` (use A at `τ`), or from
another node (both, then `min`). Max nodes ride along: one arc of the group must satisfy both
conditions.

**`Tcheck.xverdict_sound`** (what tcheck's credited PASS means). Hypotheses: three `Run`s (data
from D = `dagD`, data from X = `dagA`, late side = the unchanged `lateNet`), H_CLEAN_EDGE (`hcl`),
**H_ONE_SAMPLE_PER_WIRE** (`hshift`: each change of a paired data node is `τ` plus a change of
its copy in the X-launched run; i.e. X dominates the data and its one edge drives both sides),
H_ALL at the max nodes. Conclusion: per pair, every data change precedes every target change
by `setup`. The shared prefix's `hi` (in `lD` only) and `lo` (in `potA` only, counted from `τ`)
never meet in one inequality: that is the "credit once".

This is the cyclic, certificate form of 10b's `race_sound_clean`. Necessity of H_CLEAN_EDGE:
10b's `prefix_credit_needs_clean_edge` (a glitch at the divergence node breaks the credit) is
the same mechanism; not re-proved here.

**`MaxNode.potMax_sound`**: a potential in which a max node (non-empty group `M v`) needs only
one group arc to satisfy the arc condition is sound for every `Run` with **H_ALL** at its max
nodes (every change of `v` comes no earlier than some change of every group pin).

**`MaxNode.cel_needs_pin`** (H_ALL is a theorem of the bounded-delay Run, per pin): node
function holds `w` while pin `ka` reads `wa` and the feedback pin reads `w` (true of `maj`,
`bd_c2n`'s inverted input with `wa = !w`, any C-element LUT with reset inactive); output `w`
and pin `ka` = `wa` at the origin (pin agrees: it does not already enable the next edge);
**H_FB_FIRST** in Run form (at each output change the feedback pin reads the output: B's C2,
which rule Rc discharges through `FbFirstRt.fbFirst_of_resp`). Then every output change needs
a prior change of `ka`. No assumption on the OTHER pins. `celFn_half_excited` shows why the
agreeing pin must be known: a half-excited C-element fires on its other pin alone.

**`MaxNode.ctl_needs_pin`**: the same for a combinational gate held by a controlling pin
(the steer's branch LUT `req ∧ sel` with `req` low; H_CONTROLLING + H_ZERO_DELAY_FN).

Axioms of every theorem above: propext, Classical.choice, Quot.sound.

## The rules (shape, hypotheses, fidelity)

The prjxray numbers, Elmore, site hops, H_ONE_CORNER, the 0.772/1.155 band and
H_FALLBACK_BAND are C-10h's, unchanged.

**Xc / Xic / Xm (credited X and Xi).** Same data side and per-pair targets as 10k's X (launch
= a storage root D of z; data D -> z pin -> u -> u's feedback pins; target (z pin, phase 1)).
Per corner variant the front end:
1. runs the uncredited late Dijkstra (with the row's phase rule and max nodes) and walks the
   critical path back;
2. takes as candidates the phase-0 nodes of that path that dominate every paired data node in
   the data DAG (shallowest first; if the shallowest fails, all candidates are tried and the
   best kept; if none is on the path, the deepest dominator, which is still sound);
3. writes dagD (whole), dagA (suffix from X), potB (X blocked), potA (from X), `maxn`.
tcheck checks everything (`xverdict`); a bad choice can only FAIL or CERTBAD.
- **Xc**: rule X's phase rule (switch at D's latest handshake input, H_CEL_NEXT; at the other
  roots' outputs). Extra hypothesis vs X: H_CLEAN_EDGE(X), H_ONE_SAMPLE_PER_WIRE.
- **Xic**: Xi's (other roots: switch at their latest input, **H_OR_IDLE**).
- **Xm**: max nodes. (D, 1) over ALL of D's handshake inputs (D just fired: all agree,
  `cel_needs_pin` + H_FB_FIRST(D) = its Rc row). Each other root r: switch at r's REQUEST pin
  only, (r, 1) a max node over it, and the steer's branch LUT driving it a phase-0 max node
  over the steer's own request pin (`ctl_needs_pin`). Hypothesis **H_REQ_AGREE** instead of
  H_OR_IDLE: at the launch (D's fall) the steer's request has fallen at r's branch LUT, so
  r's request pin and r are both low. This is a protocol fact plus a weak-isochrony condition
  on the steer's request fork (the steer's request fall reaching r's branch LUT before D's fall
  is launched), i.e. B's X3 hold half, which no rule checks yet. Grade B.

**K (B's X4 second half: ctl_req -> {uj0, uj1(, uj2)}).** Launch = C, the common storage root
of every join's ctl pin. One instance per join: data = C -> that join's ctl pin; target = any
change of that join's select pin; late = one phase, the whole graph, with the select latch's
enable arcs cut (**H_LATCH_D**: the latch closed with D = Q, which rule H checks, so its output
moves only after its D input moves). PASS = the ctl pulse at the join has ended before s can
change there (no stale pulse can fire a newly selected join, B's `mux_needs_iso_cr`).

**D (diagnostics, no verdict).** For the Fd lines of cm12 and ushrsi3: the least-margin pairs,
the data and late critical paths, and the arcs they share.
