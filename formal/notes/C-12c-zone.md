# C-12c: zone-based (dense-time) timed-automata checking with TChecker

> **Correction (2026-10-29, probe C-12d; details in `C-12d-corner.md`).** The arbiter rows
> below use "O6 56/124, O5 52/28 ps" as rise/fall: a corner mix (56/124 are FAST_MAX/SLOW_MAX of
> one arc, prjxray has no rise/fall split, 28 has no prjxray source). Re-run with this
> probe's own model at one consistent corner (`formal/tools/zone/onecorner.py`, one interval
> per output for both edges; 15 corner settings incl. A's corner model, 264 s total):
> - **Server latency s_lo > 56 ps (amutex): ARTEFACT.** Holds for every s_lo >= 0 at FAST,
>   SLOW and every rise = fall point. New under the corner model: 2 s_lo >= max(2 h6, h5+h6)
>   - 2 l5 - l6 (fits every row; at s = 0 holds iff kappa <= 0.069..0.215 by reading/corner).
> - **A0 fork wa < 112 + c_lo: form stands as wa < 2 O6lo + c_lo**: 94 ps FAST, 204 SLOW,
>   116 FAST_MAX points (the old number), 252 SLOW_MAX; c_lo dependence confirmed (+36 at c_lo = 40).
> - **HELD q->ugrant route "wq_g < 56 ps": form changes** to wq_g < min{l5 if h5 > l6; l6 if
>   h6 > l5}: 42 FAST, 100 SLOW, 56 FAST_MAX points, 150 SLOW_MAX. H_GRANT_FORK itself stands.
> - **UNHELD 16 ps: ARTEFACT** (no overlap at zero routing at any consistent corner).
> - **Transport "mutex_nr fails for every wq_g > 0": stands** at one corner (reachable at
>   0.1 ps at FAST_MAX/SLOW_MAX/FAST_MIN points; the overlap is |O6 - O5|, not stretching).
>   The holding transport rows (`*_nr`, ovf_nr = 0) could NOT be re-established: at rise = fall
>   every unreachable exploration timed out (>= 200 s, > 550 MB) where the mixed arcs took
>   0.7-5 s -- with no asymmetry, pure delay never shrinks runts. Treat them as corner-mix results.
> - C-element (item 1): unaffected (symmetric arcs); per-corner numbers in C-12d.

Files (mine): `formal/tools/zone/tckmodel.py` (front end + runners),
`formal/tools/zone/celem.py`, `formal/tools/zone/arb.py`, this note. Build
output: `formal/tools/zone/build/tchecker/` (gitignored). No Lean in this probe.

## Verdict

**Works.** TChecker builds from a git clone in under 5 min. The 12b
generator ports to it in ~450 lines. Every C-element and arbiter question
12b asked is re-answered **exactly in dense time** (thresholds checked at 0.1
ps and 0.01-tick resolution). Typical checks take 0.05-4 s and use 15-150 MB.
The one case 12b could not finish (transport + arc spread) is answered in
part:
- Its headline property, mutex, is **violated, in 1.9 s at 62 MB**. The
  violation needs no runt on q.
- The full exploration (needed for the properties that hold) still runs out
  of memory: `bad_alloc` at the 3.5 GB cap after 81 min, even with K=2.
- Every reduced variant finishes in 2-71 s.

Surprises:
1. C-element, inertial channel: the spec bound depends on the LUT delay,
   e_lo > dw_hi - dl_lo. 12b's "independent of dl" was a tick-grid artefact.
2. Shipped (held) arbiter: **mutex depends on the q->ugrant route, wq_g**.
   - Inertial: mutex needs wq_g < 56 ps (the ugrant O6 rise arc).
   - Pure delay: mutex fails for every wq_g > 0, even with no runt on q.
   - This is a grant-LUT runt that the A0 hold does not cover. 12b's HELD
     rows never used wq_g >= 56 ps, and used wq_g = 0 in transport.
   - Cross-checked with 12b's Storm model: 13 ticks holds, 14 ticks (56 ps)
     fails.

## Tool acquisition (2026-10-27)

| step | result |
|---|---|
| `git clone --depth 1 https://github.com/ticktac-project/tchecker` into `$S/ext/tchecker` | **works**. Commit d711ace9ff754d8d952f5d491a31591115300c7f (2025-12-09). This is the route 12b could not try |
| apt | flex 2.6.4, libboost-all-dev 1.83.0, catch2 3.4.0 installed. bison 3.8.2, cmake 3.28.3 and g++ 13 (Ubuntu 24.04) were already there |
| build | `cmake -DCMAKE_BUILD_TYPE=Release -DCMAKE_INSTALL_PREFIX=formal/tools/zone/build/tchecker`, then `make -j2 install`. 268 s with LTO. `install` errors only at the doxygen `html` docs, after `tck-reach`, `tck-liveness`, `tck-simulate`, `tck-syntax` and `libtchecker.a` are installed |
| alternatives | not needed. UPPAAL, IMITATOR, theta and LTSmin were not tried |

`$S` = `/tmp/claude-0/-home-user-asyncfpga3/1e7618db-96c2-5b39-8e46-9778d8fa891b/scratchpad`.

To rebuild after a fresh checkout:

```
git clone --depth 1 https://github.com/ticktac-project/tchecker $S/ext/tchecker
apt-get install -y flex libboost-all-dev catch2
mkdir $S/ext/tchecker-build && cd $S/ext/tchecker-build
cmake $S/ext/tchecker -DCMAKE_BUILD_TYPE=Release \
      -DCMAKE_INSTALL_PREFIX=/home/user/asyncfpga3/formal/tools/zone/build/tchecker
make -j2 install
```

`tckmodel.py` finds the binary at `build/tchecker/bin/tck-reach`, or at
`$TCK_REACH`.

## Model (`tckmodel.py`): what changed from 12b

The semantics are 12b's `tamodel.py`, per node, with these changes:
- **Dense time.** Real-valued clocks with integer bounds in any unit (arb.py
  uses ps, or 0.1 ps with `u=10`). There is no tick, so there is no tie
  artefact: equal instants are interleaved in both orders, which is exact.
- **One process per node.**
  - Inertial: locations S, ER and EF, with invariant `c <= hi` in ER and EF
    only. The invariants are constant, so TChecker's LU clock bounds stay
    tight. A non-constant `if` bound would make them MAX_VALUE.
  - Transport (FIFO): locations `T<x><len>` with one clock per queue slot.
    In-flight edges alternate in value, so (x, len) determines the whole
    queue. Delivery shifts the clocks (`c0=c1; c1=c2`). The cancel and
    annihilate rules are 12b's, and so are the `ovf_x` and `mlt_x` monitors.
- **Synchronisation.** A node firing is event `f_x`, strongly synchronised
  with `u_x` edges in every reader. Each reader has an exhaustive set of
  `u_x` edges from every location, with guards evaluated in the pre-state
  and x substituted, so the synchronisation never blocks.
- **Expressions.** TChecker expressions are conjunctions only, so LUTs and
  monitors are emitted as 0/1 integer terms with nested `if-then-else`, from
  the same real-INIT Shannon expansion.
- **Properties.** There are two ways to check them:
  - (a) A monitor process `ok -> bad{labels:bad}` and `tck-reach -a covreach
    -l bad`, one run per property.
  - (b) `explore_all`: ONE full covering-reachability exploration with
    `-C graph`, then every int-valued state property is evaluated on the
    distinct discrete states. This is sound because covering only relates
    nodes with equal locations and ints. One exploration costs about one
    unreachable-property run, and it answers 16 properties.
- **Witnesses.** `-C concrete` fails on this model ("concretization failed",
  probably the clock-copy assignments). `-C symbolic` works, gives the event
  sequence with zones, and was used for the wq_g witness.
- **Not usable.** `-a concur19` (local-time zones, the algorithm meant for
  loosely coupled networks) refuses: "not sound for systems with shared
  variables". Gate values are shared ints. Moving them into locations would
  need a sync per reader value, which was not attempted.
- **Bug found while porting.** TChecker `do:` statements are sequential.
  Monitor flags must be assigned before the node's own value changes, so that
  they read the pre-state. The first port got this wrong, and celem's spec
  then fired on legal moves.

Exactness: closed TA with integer constants, ExtraLU+ abstraction and
inclusion covering. Reachability is exact for dense time. As in 12b, the
transport results are exact only where `ovf` (or `ovf_nr`) is unreachable.

## Item 1: C-element (bd_c2, INIT 64'h00E8_00E8_00E8_00E8), DONE

Run: `cd formal/tools/zone && python3 -I celem.py thr`.
- 61 s in total: 20 (dl, dw) pairs x about 30 e_lo values x 2 channels x 2
  properties.
- At most 258 zones and 13 MB per check.
- `python3 -I celem.py` runs 12b's original table (4 s).
- Units are 1/10 of a 12b tick. The row dl=(100,100), dw=(100,300) was
  re-checked at 1/100: same thresholds, **identical zone counts** (22/33/17).
  Zones do not grow with the constant scale; digital clocks grow linearly.

| channel | spec (O moves only when a = b != O) | hazard-free (no swallowed excitation) |
|---|---|---|
| inertial | **e_lo > dw_hi - dl_lo** (strict; always holds if dw_hi < dl_lo) | **e_lo > dw_hi** (strict) |
| transport (FIFO) | **e_lo >= dw_hi** (closed) | n/a |

Answer to "is e_lo >= dw_hi exact in dense time?":
- **Yes for the FIFO transport channel**, as a closed bound. At equality the
  reversal has zero width and is cancelled.
- **For inertial, the safe form is strict**: e_lo > dw_hi. At equality there
  is a zero-width excitation, which is swallowed. That is hazard-free as a
  spec, but it is an output-persistency violation.
- The inertial *spec* bound is weaker, e_lo > dw_hi - dl_lo. The LUT has to
  fire its wrong edge before qp lands.
- 12b's sweep always used dl_lo = 1 tick = one grid step, so it read
  "e_lo >= dw_hi, independent of dl" (that is, e_lo > dw_hi - 1 tick).
- For shard B's Lean target, the FIFO theorem with hypothesis
  E >= dw_hi is the tight one. B's WinDelay version needs
  E >= dw_hi + (dl_hi - dl_lo).

## Item 3: the two 12b timing conditions, exact in dense time, DONE

Run:
- `python3 -I arb.py srv inertial|transport`
- `python3 -I arb.py wa inertial|transport`
- `python3 -I arb.py basic inertial|transport` (12b's sections 1-3, in ps)

Setup:
- Nominal arcs O6 56/124 and O5 52/28 ps. Zero routing except the swept wire.
- Server window [s_lo, s_lo+20] ps. Clients fall [c_lo, c_lo+20] ps after
  their A, with c_lo = 4.
- Resolution 0.1 ps (u=10).

Cost:
- Inertial: < 0.3 s per check, <= 300 zones, ~16 MB.
- Transport: 1-8 s per check, <= 9 k zones, <= 100 MB.
- Server latency 4-24 ps is the slowest case: 45 k zones, 150 MB, 26 s per
  full exploration.

Results:
- **Server latency (HELD ack exclusion, amutex):**
  - inertial: holds iff **s_lo > 56 ps** (strict).
  - transport, no q runt (amutex_nr, and tx_nr too): holds iff
    **s_lo >= 56 ps** (closed).
  - 12b's "about 60 ps" is exactly 56 ps. 12b saw 14 ticks fail, which is
    the tie.
  - ho and mutex hold at every s_lo tried, down to 4 ps.
- **A0 fork, rising edge (HELD):** everything holds iff
  **wa < 112 + c_lo ps**, where c_lo is the client's minimum r-fall response.
  - Checked at c_lo = 0, 4, 20 and 40: thresholds 112, 116, 132 and 152. The
    failure at the bound is closed.
  - So 12b's 116 ps = A2 O6 rise (56) + c_lo (4) + q O6 rise (56). The new
    information is the dependence on c_lo: a faster client tightens it.
  - Same in transport (`*_nr`). `ovf_nr` = 0, so the transport result is
    exact for K=3.
- **UNHELD (for completeness):**
  - mutex iff wq_g > 16 ps (strict). This is the header's 16 ps; 16.0 fails
    and 16.1 holds.
  - ho/tx fail iff s_lo >= 60 ps (59.9 holds), inertial.
- **NEW: the HELD q->ugrant route.**
  - Inertial: mutex holds iff **wq_g < 56 ps**.
  - Transport: mutex_nr **fails for every wq_g > 0** (0.1 ps fails). With no
    runt anywhere (`mutex_nra`), it holds at every wq_g tried (0-32).
  - Symbolic witness (`-C symbolic`, HELD, spread 8, wq up to 32), as a
    sequence:
    1. r1 rises and q rises.
    2. r2 rises after q has committed (no runt on q), but before the new q
       reaches ugrant.I2.
    3. ugrant sees r2 & ~qg(old), so g2 gets an excitation of width
       <= wq_g. `mlt_g2` is set: a runt at the grant LUT.
    4. Pure delay passes that pulse and stretches it by the fall-rise
       asymmetry.
    5. g1 rises 52 ps after qg arrives, while g2 falls only 124 ps after it.
  - The A0 hold cannot help, because A0 is low.
  - **Refinement (wq_s != 0).**
    - Transport: what matters is the skew wq_g - wq_s. With
      wq_s = wq_g = 16, mutex_nr holds; with wq_g = 16.1 it fails. When the
      ustate copy is just as late, a late r2 makes a q runt instead, which is
      tier 3.
    - Inertial: the bound is absolute, wq_g < 56 ps, for wq_s = 0, 20 and 40.
      ustate swallows its own reversal, so q stays put while ugrant still
      reads the old q.
  - Equivalent hypothesis: H_GRANT_FORK. The fork of r1/r2 into ustate and
    ugrant must be isochronic with respect to q's route to ugrant. That is:
    no request edge may reach ugrant inside the window in which ustate has
    committed but ugrant still reads the old q. Under inertial delay the
    window must be narrower than ugrant's O6 rise arc. Under pure delay it
    must be empty.
  - Real routing puts "a full hop" (hundreds of ps, per the header) on that
    route. So on the chip this is a real race unless the clients' r2 edge is
    ordered against q by the protocol. It is not: clients are free.
  - The header's tier table puts handover races in tier 2 and runts on q in
    tier 3. This one is a runt on the GRANT LUT, caused by routing skew, with
    a SETTLED q. It belongs in the cell's obligations.
  - **Not yet checked on board or GLS.** A GLS with the routed delay of
    q->ugrant.I2 and r2 timed in that window would test it.

## Item 2: HELD transport + arc spread (12b's OOM case)

The row is 12b's section 4: spread ±8 ps on every LUT arc,
wq_s, wq_g in [0,32] ps, wa in [0,16] ps, srv [160,180] ps. There are 9
transport nodes with 3 slots each plus 4 environment clocks, so 31 clocks.

Run: `python3 -I arb.py spread transport` (the reduced rows) or
`python3 -I arb.py spread transport full` (the full row: OOM). Use
`spread inertial` for the inertial rows.

| variant (HELD, transport, srv [160,180]) | result | cost |
|---|---|---|
| full: spread 8, wq in [0,32], wa in [0,16], K=3, one `-l bad` run for mutex_nr | **mutex_nr reachable** (grant-LUT runt, see Item 3) | 1.9 s, 3.0 k zones, 62 MB |
| same, per-property runs (12b style) | the first unreachable property (ovf_nr) was still running at 2.9 GB after 30 min; killed by the background time limit | -- |
| same, `explore_all`, K=2 | **std::bad_alloc at the 3.5 GB ulimit after 81 min wall** (57 min CPU, CPU-contended) | OOM |
| spread 8, all wires 0 | every `_nr` / `_nra` property holds; ovf_nr = 0 (exact); mutex/amutex need a q runt | 1.7 s, 3.4 k zones, 64 MB |
| spread 8, wires fixed wq_s = wq_g = 16, wa = 8 | every `_nr` / `_nra` holds, ovf_nr = 0 | 71 s, 149 k zones, 219 MB |
| spread 2, wq in [0,8], wa in [0,4] | mutex_nr = 1 (wq_g can exceed wq_s); every `_nra` and other `_nr` holds; ovf_nr = 0 | 24 s, 58 k zones, 157 MB |
| inertial, full spread row (12b section 4) | HELD: all hold; UNHELD: all fail. Agrees with 12b | 0.1 s / 0.3 s, 92 / 746 zones (Storm: 13 k / 257 k states) |

Conclusions for item 2:
- Under pure delay with arc spread, the shipped arbiter keeps every
  property in runs with no runt anywhere.
- Mutex and the ack properties are lost only through runts:
  - q runts (tier 3, as in 12b);
  - grant-LUT runts, whenever the q copy reaching ugrant can lag the copy
    reaching ustate's own I2 (wq_g > wq_s; see Item 3).
- The blow-up comes from the wide *wire* windows in transport mode, not from
  the arc spread. Several in-flight edges per wire, each with its own clock,
  give 31 clocks and a combinatorial number of queue shapes. Fixed wires plus
  spread arcs are cheap.
- The full model stays out of reach in 3.5 GB. Possible next steps:
  - fewer transport wires (make the wires inertial and keep transport on the
    LUTs);
  - DFS with a bounded store;
  - a K=1 wire channel;
  - UPPAAL, which is blocked.

## TChecker (zones) vs Storm (digital clocks), same models

| model | Storm 2.0 (12b, ticks of 4 ps) | TChecker (this probe, 0.1-1 ps) |
|---|---|---|
| C-element, one row | 1-17 k states, 0.02-0.2 s | 11-258 zones, 0.05 s; scale-free |
| HELD inertial, srv 40-45 ticks | 2.3 k states, 0.3 s (all properties) | 76 zones, 0.01 s per exploration |
| HELD transport, srv [40,45] ticks | 71 k states, 2.6 s | 1.4 k zones, 0.7 s exploration (1.8 s wall incl. graph print) |
| HELD transport, wa = 29 ticks | 221 k states, 5 s | 3.2 k zones, 1.4 s |
| HELD transport, srv [1,6] ticks / [4,24] ps | (not run at this latency) | 45.6 k zones, 26 s, 150 MB |
| HELD/UNHELD inertial, spread ±2 ticks | 13 k / 257 k states, 0.6 / 6.8 s | 92 / 746 zones, 0.1 / 0.3 s |
| HELD transport + spread (full) | **OOM at 5.3 GB / >20 min** | violation found in 1.9 s; full exploration OOM at 3.5 GB / 81 min (K=2) |
| HELD transport, spread, wires fixed 16/8 | not run | 149 k zones, 71 s, 219 MB |

Overall:
- Zones are 20-70x fewer than digital states and do not grow with time
  resolution. That is what lets thresholds be found at 0.1 ps.
- Per check, wall time is similar for small models.
- TChecker's cost is one run per label. `explore_all` removes that.

## Fidelity of the primitives (unchanged from 12b unless noted)

- **LUT:** real INIT. Boolean function per output, one rise and one fall arc
  per output (not per pin). No mux-tree glitches, no X. Arcs are from the
  header's zero-routing trace, not from prjxray-db corners. These are named
  hypotheses for shard B.
- **Inertial channel:** optimistic. It swallows any pulse shorter than the
  rise/fall lo.
- **Transport channel:** pessimistic. It passes and stretches every pulse.
  The real LUT lies between the two. The wq_g finding shows the gap matters:
  56 ps vs 0 ps.
- **Wires:** same channels. Only the q feedback copies and the A0 fork carry
  delays; r1/r2 reach both LUTs with zero skew. The r-fork skew is exactly
  what H_GRANT_FORK is about, and it is not modelled separately.
- **Environment:** idealised. Free clients; the server is a pure-delay
  follower of R0.
- **Dense time:** exact for these TA. There is no digitisation hypothesis
  any more, unlike 12b's HMP digital-clock argument.

## What this buys / effort to finish

- **For shard B (Lean)**, exact targets with the exact strictness:
  - C-element FIFO: E >= dw_hi.
  - Inertial: E > dw_hi - dl_lo for the spec, E > dw_hi hazard-free.
  - Ack exclusion: s_lo > 56 ps (inertial) / >= 56 ps (FIFO).
  - A0 fork: wa < O6R(A) + c_lo + O6R(q).
  - New obligation H_GRANT_FORK, with wq_g < 56 ps inertial.
- **Tooling:** a dense-time checker usable on whole small cells in seconds,
  which scales better than digital clocks.
- **To finish:**
  - Parametric thresholds, i.e. symbolic in the arcs. That needs IMITATOR
    (not tried) or a sweep.
  - Per-pin arcs.
  - Moving shared ints into locations to try concur19.
  - About 1 day.
