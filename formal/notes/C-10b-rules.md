# C-10b: would a verified checker make rules E / A / J exact?

## Verdict

**Works, as a model; blocked for silicon by the input data.** All three rules
check one property (a two-sided race from one launch: the late side settled
before the early side moves). That property is formalized over the
bounded-delay traces of `Formal/Net/Prelim`, and interval static timing analysis
is proved sound for it (`race_sound`). So a verified checker can be exact
*relative to a stated delay model*. None of the three rules as implemented is
exact even relative to its own data, and each failure is a theorem with a
concrete netlist and concrete traces:

| rule | sound when (proved) | fails (counterexample, proved) |
|---|---|---|
| E (skew.py) | per-element band 0.772/1.155 holds and the divergence node makes one clean edge (`ruleE_sound`) | (1) the SDF drops LUT site-pin delays: rule E passes by +37 ps and **every** slow-corner delay choice violates (`ruleE_sitepin_fails_all`, with `ruleE_sitepin_nonvacuous`). (2) The band is not a corner bound (`ruleE_corner_counterexample`; the shape is not routable, see below). (3) The t_c credit is unsound if the shared prefix can glitch (`prefix_credit_needs_clean_edge`). |
| A (tighten.py) | `t_l <= 402 ps` (`ruleA_band_sound_small`) | for every `t_l >= 404 ps` a passing margin is not covered by the band skew.py uses (`ruleA_not_band_sound`); concrete traces (`ruleA_counterexample`) |
| J (arb_fork.py) | exact shared prefix + band + clean edge (same as `ruleE_sound`) | the pip-count estimate of the shared delay over-credits: passes by +30 ps, violated inside the rule's own band (`ruleJ_pass`, `ruleJ_exact_fails`, `ruleJ_counterexample`) |

**What a checker needs.** Not nextpnr's SDF. It needs per-sink intervals per
corner, built from the routed JSON's `ROUTING` (the pip list of each sink, with
physical LUT pins after permutation) and prjxray-db (pip, site-pin and cell-arc
4-tuples, and wire R/C through `prjxray/timing.py`'s Elmore model). It also
needs two stated correlation hypotheses (one PVT corner for the whole die; one
sample per shared physical wire) and a measured on-die variation band. The
repo's own ring data refutes the SDF as an upper bound on silicon, so the data
is the blocker, not the proof.

## What checks

```
cd formal && ./check.sh Formal/Timing/Rules.lean        # -> [check] OK (119 declarations audited)
cd formal/lean && export PATH=$HOME/.elan/bin:$PATH LEAN_PATH=$PWD/.lake/build/lib/lean
../slot.sh lean -o .lake/build/lib/lean/Formal/Timing/Rules.olean Formal/Timing/Rules.lean
../slot.sh lean Wip/C10b/Audit.lean                      # #print axioms of every result
python3 -I formal/tools/timing/prjxray_intervals.py      # the delay data quoted below
```
Core Lean only, about 2 s. No sorry, no axiom, no native_decide. Axioms used:
propext, Quot.sound, and Classical.choice (from `simp`/`decide` on the
existential counterexamples). `Formal.lean` (shard A's root) does not import
`Formal.Timing.Rules` yet; the lead should add it.

Theorems in `formal/lean/Formal/Timing/Rules.lean`:
- Semantics: `arc_window`, `chain_window`, `gate_window`, `race_sound`,
  `race_sound_clean`, `shift_bd`, `shift_window`, `shiftChain_chain`,
  `shiftChain_step`, `step_window`.
- Rules: `bandLo_sum`, `bandHi_sum`, `ruleE_sound`, `ruleA_band_sound_small`,
  `ruleA_not_band_sound`.
- Counterexamples: `ruleA_counterexample`, `ruleE_corner_pass`,
  `ruleE_corner_counterexample`, `ruleE_sitepin_pass`,
  `ruleE_sitepin_fails_all`, `ruleE_sitepin_nonvacuous`, `ruleJ_estimate`,
  `ruleJ_pass`, `ruleJ_exact_fails`, `ruleJ_counterexample`, `glitchy_bd`,
  `prefix_credit_needs_clean_edge`.

## The model (and its fidelity)

- **Trace:** `Nat → Bool`, 1 tick = 1 ps (shared with shard B/C).
- **Arc (wire, or one sensitized gate pin):** H_BOUNDED_DELAY (`BoundedDelay`
  from Formal/Net/Prelim). Every output change copies an input value from
  `d ∈ [lo, hi]` earlier, and the output settles once the input has been
  stable for `hi`. This channel is **not FIFO**: one input edge may come out
  as several (`glitchy_bd`). That is right for a gate with a hazard. A real
  wire (monotone RC) is closer to a pure delay (`shift`), which satisfies the
  relation (`shift_bd`).
- **Gate:** per-pin input delay into a zero-delay Boolean function
  (`gate_window`). That is how prjxray splits it (site-pin intrinsic delay
  per pin + one LUT arc) and how the SDF IOPATHs are read. It is binary, not
  shard B's Kleene `lutK`: the windows carry no values in between, so X is
  subsumed by "anything may happen inside the window".
- **H_SENSITIZED (single launch):** a path through a multi-input gate is a
  `Chain` arc only while the side inputs are stable. Every STA and all three
  rules assume this. `gate_window` is the general form; a full DAG checker
  is 10a's.
- **H_CLEAN_EDGE:** the divergence node makes one transition (`Window v w τ τ`).
  This is what licenses crediting the shared prefix (skew.py t_c, arb_fork.py
  c). It holds for a pure-delay wire prefix (`shift_window`). It fails when the
  prefix contains a gate with reconvergent inputs from the launch. skew.py's
  divergence prefix can contain LUTs.
  Test: GLS with per-transition random delays on the prefix gates.
- **H_BAND_772_1155 (`BandLo 772`, `BandHi 1155`):** each element's real delay
  is in [0.772 D, 1.155 D] of its SDF number D. That is skew.py's 95/95
  tolerance band from five rings, applied per element. The 128-ring data in
  cells/hw/README.md (|resid| p90 25%, p99 34%, 76/128 slower than predicted)
  already exceeds it.
- **H_ONE_CORNER:** every element lies in the interval of the same prjxray
  corner. The counterexamples use all-fast or all-slow assignments, which
  satisfy it.

## The rules, precisely

All three parse the **first number** of each SDF triple (`\((\d+):`). From the
IOPATHs they take only the first (rise) triple. nextpnr-xilinx writes
min = typ = max, so the shortest and the longest walks use the **same
single number** per arc, and rise = fall.

**Where the SDF number comes from** (openXC7/nextpnr-xilinx `xilinx/arch.h`
getPipDelay, `arch.cc` xc7_cell_timing_lookup, `common/sdf.cc` "FIXME: min/max
routing delay"; `$TC/openxc7/lib/python/xilinx_device.py` 415-434,
`nextpnr_structs.py` scales):
- tile pip: `max(slow_min, slow_max)` + `int((src_len*R_src + R_pip)*C_pip/1e9)`
  (about 10-12 ps, the pip's own R times its own input C: not an Elmore delay
  over the net's fanout), floored at 35 ps;
- site entry/exit and LUT-permutation pips: a **flat 25 ps**; LUT route-through
  300 ps; global clock pips 100/250;
- cell arcs: max over prjxray's two triples = slow-corner max (LUT6 124 ps,
  every pin).
- The fast corner and every min are discarded at chipdb export
  (`min_delay = min(fast_min, fast_max)` is exported but getPipDelay never
  reads it).

**prjxray-db (zynq7) data the SDF does not carry** (`prjxray_intervals.py`):
- LUT site input pins A1..A6, (fast_min, fast_max, slow_min, slow_max) in ps:
  A1 (172,214,416,516), A2 (170,212,409,507), A3 (107,133,278,344),
  A4 (86,107,229,284), A5 (33,42,91,112), A6 (2,2,4,5). In the SDF each is
  25 ps. Which physical pin a net lands on (nextpnr permutes) moves the real
  delay by up to ~0.5 ns, invisibly. This may be part of why the shortest ring
  ran +35% over its SDF (cells/hw/README.md, ro_top rebuild, ring 0). That is
  untested: rerun the 128-ring predictions with site pins and compare.
- Corner spread: slow_min/slow_max is 0.82-0.87 for every class (the
  within-corner spread), and fast/slow is 0.24-0.49 depending on the class
  (pips 0.24-0.45, LUT 0.36/0.45). The ratio is class-dependent, so a single
  multiplicative band cannot track a corner change when the two legs mix
  element classes.

**Rule E** (cells/verify/skew.py). For each bd_steer / bd_mux join LUT
(`select_consumers`) it pairs the request pin with the select pin on the same
LUT, and picks launches: storage nodes backward-reachable from both, the first
4 sorted by select crossing count, plus the C node of any link whose latch is
a nearest launch (comment (3)). For each launch, `walk` gives per-level
(storage-crossing count, K <= 6) shortest arrivals on fast-fall-pruned arcs
(request) and longest arrivals on all arcs (select). `at()` takes the
**first level** at which the pin appears. `t_c` is the arrival at the last
node common to the two replayed predecessor chains (`divergence`, after the
seeded-stop overwrite fix that test_skew_walk.py pins down). Verdict: min
over the launches of `int(0.772 (t_req - t_c) - 1.155 (t_sel - t_c)) > 0`.
Semantic property: `Bundled sel w req` at the LUT. Conservative / unsound /
heuristic:
- sound given its hypotheses: `ruleE_sound` (band per element, clean edge at
  the divergence node, sensitized paths).
- **unsound, data:** site pins (above): `ruleE_sitepin_fails_all`. Rule E
  passes by +37 ps (request: five SW2BEG-class pips into A6; select: three
  IMUX pips into A1). At the slow corner the request has arrived by 740 ps
  and the select cannot arrive before 794 ps, for **every** delay choice.
  The shape is ordinary.
- **not corner-safe:** `ruleE_corner_counterexample` passes by +26 ps and
  fails at the fast corner. Its shape (8 first-hop pips against 5 LUT arcs
  + 1 pip) is not routable. For routable compositions the corner condition
  is `ρ_req * 1.496 >= σ_sel`, with ρ = fast_min/SDF over the request's
  elements and σ = fast_max/SDF over the select's. It is thin but mostly met
  (pips ρ ≈ 0.29-0.40, LUT σ 0.45, NN/SS pips σ up to 0.49). Corner
  safety is a property of composition that the band does not check.
- **unsound, model:** the t_c credit needs H_CLEAN_EDGE
  (`prefix_credit_needs_clean_edge`: a legal glitching prefix, +19 ps
  guarded, violated).
- **heuristic, permissive:** (a) `at()` returns the fewest-crossings level,
  not the earliest arrival over levels. In test_skew_walk's first graph the
  request reaches G/A1 at 160 at level 1 and at 80 at level 2 (via T->S/A2),
  and rule E uses 160. Against the plain graph minimum that is permissive,
  and it is right only if the deeper path is a lap (the next token), which is
  a protocol fact the timing graph does not contain. Against the true
  semantics it depends on the storage type: a C-element fires on its LAST
  input, so its earliest firing is a max over its inputs, and the walk's
  min-over-inputs crossing is itself over-conservative. A verified checker
  would replace both with the cell's actual firing rule.
  (b) Only cand[:4] + (3) launches are evaluated. (c) "orphan" gates are
  reported as not checked. (d) Fast-fall side arcs are dropped from the
  request walk on the claim that they carry only falls; this is checkable
  from the LUT INIT (unateness), and nothing checks it.
- **heuristic, conservative:** the select walk crosses the transparent latch
  only via its enable (d assumed stable by the sender's contract, which is
  rule A/I's job, an assume-guarantee nobody composes).

**Rule A** (cells/verify/tighten.py, `check` / `check_bundled`, `req_guard`).
For each cell with a request chain, the walks are confined to the cell (plus
upstream bd_links). It computes `t_e` = shortest from a common source to the
request tail and `t_l` = longest to every peer output. It passes when
`t_e - t_l - max(0.2 t_l, 200) >= 0` (`rule_a_links` pads only on a negative
margin). Without a common source (generated units) it pairs the
earliest-anywhere request with the latest-anywhere data, all launched at t=0
(`check_bundled`), and subtracts `upstream_data_lag`. Property:
`Bundled peer w req` for every peer. Findings:
- **The guard is inconsistent with rule E's band.** Under H_BAND_772_1155,
  rule A's verdict implies the property only for `t_l <= 402 ps`
  (`ruleA_band_sound_small`). For every `t_l >= 404` there is a passing
  margin the band does not cover (`ruleA_not_band_sound`), with concrete
  traces at 2400/2000 ps (`ruleA_counterexample`). The project quotes margins
  "with GUARD_LO/GUARD_HI applied" (CLAUDE.md), yet the gate that sizes every
  matched delay uses a weaker, eyeballed guard (tighten.py says so itself).
  research/JOURNAL.md reports rule A with 0 violations on many seeds, so
  this is a statement about the check, not a defect found in a build: no
  routed SDF is on disk here (`build/` is absent).
- The same SDF data problems as E (site pins, single number, no fast corner).
- `check_bundled`'s t=0 pairing is conservative only if the upstream
  guarantee holds *at this cell's input pins*. The upstream cell's rule A
  checks at its own outputs, and inter-cell nets lie between. That is an
  uncomposed assume-guarantee.
- `confine`: paths leaving the cell are not timed. That is by design (a
  matched delay covers one cell); it is a scope decision, not a proof.

**Rule J** (cells/verify/arb_fork.py). Per arbiter and client k, along
fixed single paths: `late` = A0 net to ua_k + ua_k's A0 arc; `early` = A0 net
to ustate + arc + q net + ugrant arc + g net + ua_k's g arc.
`c = min(d_a*shared/hops_a, d_b*shared/hops_b)` comes from the routed
`ROUTING` pip counts (no per-pip delays in the SDF). It passes when
`int(0.772 (early-c) - 1.155 (late-c)) > 0`. Property:
`Bundled (A0 at ua_k) false (g_k at ua_k)`, the handover race of
bd_arb.v. Findings:
- With the exact shared delay it is `ruleE_sound`'s shape: sound under band
  + clean edge (the A0 trunk is a wire, so H_CLEAN_EDGE is physical there).
- **The estimate is permissive.** The guarded margin grows by 0.383 c, and a
  cheap shared pip followed by dear divergent ones gives `c` > the real shared
  delay: `ruleJ_counterexample` (c estimated 166, true 40; passes by +30 ps,
  violated inside the rule's own band). The fix needs per-pip delays, which
  only the chipdb / prjxray model has, not the SDF.
- Only the rise number is read and rise = fall in this SDF, so polarity is
  moot. A prjxray-based checker would use the A0-fall and g-rise intervals
  separately.

## Would a verified checker make them exact?

1. **Relative to a stated model, yes, for all three.** They are instances of
   `race_sound`: per launch, `b + Σhi(late) < a + Σlo(early)` over the
   sensitized paths, generalized to a DAG by `gate_window` (10a's checker).
   Exactness then means "check passes iff no trace of the model violates",
   and the only gap is H_SENSITIZED (false paths make it conservative).
2. **The rules' own heuristics would go:** fewest-crossings levels and launch
   truncation (E), the pip-fraction c (J), the eyeballed guard (A), and the
   clean-edge credit through gates (E). The level/lap question needs a
   protocol input: which storage nodes fire within one transaction. A pure
   timing checker cannot decide that. It has to come from the handshake model
   (tracks 6/8: Formal/Net Handshake/Muller), e.g. a per-launch set of
   concurrent storage events derived from the STG.
3. **Relative to silicon, only as good as the intervals, and here the data is
   the blocker.**
   - nextpnr SDF: unusable as the interval source. It has one number
     (slow max), no lower bound at all, site pins flattened to 25 ps (up to
     491 ps missing per LUT input), a non-Elmore RC (no fanout loading: the
     latch-enable net in rule E's select path drives one LUT per bit or
     bit pair of the latch bank), and no
     per-pip breakdown (needed for J's c and E's t_c).
   - prjxray-db per-pip/site-pin 4-tuples + wire R/C via timing.py, per sink
     from the routed JSON's ROUTING: has the information, and gives
     per-corner intervals. Fully independent [fast_min, slow_max] per
     element is vacuous: it needs the request to be ~3-4x the select, and
     every bundled pair would fail. So the checker must assume H_ONE_CORNER
     (within a corner the spread is 0.82-0.87, close to rule E's band
     ratio 0.668) plus an on-die variation band.
   - That band must be measured, and the existing measurement contradicts
     both the SDF and the 5-ring band: per-route residuals reach 34% (p99),
     and 76/128 rings ran slower than an SDF built from prjxray *slow max*.
     Either the site-pin and Elmore terms explain it (testable now: recompute
     the 128 ring predictions with the full prjxray model) or prjxray's
     "slow max" is not a bound for this die. Until one of the two is
     settled, a proof's hypothesis "every element lies in its prjxray
     interval" is unvalidated.

## Effort and what it buys

- Checker over the real netlist: 10a's generic DAG checker plus this file's
  race lemmas, 1-2 weeks of Lean. A Python front end (untrusted) emits
  per-sink per-corner intervals from ROUTING + prjxray-db: 3-5 days. The
  Lean side checks a certificate (per-node windows), which keeps the proof
  small. At 10^4-10^5 arcs, kernel `decide` is too slow, and native_decide
  is banned by PROGRAM.md, so a production run would use compiled `#eval`.
  That trusts the compiler: fine for engineering, not "proved" under the
  project rules.
- Protocol-aware launch sets (replacing E's levels/laps): weeks; it depends
  on track 8.
- Data validation (site pins + Elmore against the 128 rings): 1-2 days of
  Python on existing measurements. **It is the highest-value next step,**
  and it needs no Lean: if site pins explain the short-ring excess, rule E's
  SDF is missing a first-order term today.
- What it buys now, without a full checker: three concrete defects in
  shipped gates, each a two-line fix in Python (add per-pin site delays
  from prjxray-db by physical pin; compute J's c from per-pip delays; use
  GUARD_LO/GUARD_HI in rule A, or state why not).

## Decisions taken (no one to ask)
- Did not import 10a's Checker (Formal/Timing/ had no Checker*.lean when this
  ran); defined windows/chains locally on top of Formal/Net/Prelim.
- Counterexample SDF numbers are what nextpnr-xilinx's formula produces from
  the cited prjxray entries (tool prints them). The netlists are constructed,
  not taken from a routed design, because no routed SDF exists in this
  sandbox (`build/` absent). Whether shipped routes contain the site-pin
  pattern is unmeasured. To measure: the routed JSON gives each select/request
  sink's physical pin (arb_fork.py already resolves physical pins), so a
  20-line script over existing routes would say.
- Did not run git (brief).
