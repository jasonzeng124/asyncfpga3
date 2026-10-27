# C-8h: per-link end-to-end theorem (tracks 8 + 10)

Shard C, probe 8h, 2026-10-27. Builds on 8a (`muller_pipeline`) and 8e (`end_to_end`);
their files are imported, not edited.

## Verdict

**Works.** Goals 1 to 3 are proved in core Lean. Goal 4 is answered with numbers.
There is no sorry, admit, axiom or native_decide. `#print axioms` on every main theorem
lists only `propext`, `Classical.choice` and `Quot.sound` (some list fewer).
About 1300 lines and about 2.5 h of work. Each file checks in 1 to 3 s.

1. **Per-link margins.** `muller_pipeline2` lets each link j have its own `m j` and
   `h j`. On top of it, `end_to_end2` uses a check with no free parameter
   (`checkPipe2 R n W`). Each race compares the two real paths of one link. On a toy,
   8e's global check rejects a route for every `(m, h)` and the per-link check accepts
   it (`split_global_rejects`, `split_check2`, `split_fifo`).
2. **Rise/fall-asymmetric delay lines.** Every control path has two interval lists, one
   for rises and one for falls. A FASTRISE DACK line (DACK >= 2) can now be checked.
   On a toy, the per-edge check accepts it (`dack_check2`) and the single band rejects
   it (`dack_band_rejects`). The two-tap FASTRISE line is proved to be such a pin
   (`or2_epin`).
3. **Per-event delays.** Control pins may have a different delay for each event, as
   long as the events keep their order (`EPin`). The change-count invariant survives
   (`ELink.inv`). A per-event transport channel is an `EPin` under the pulse-width
   condition: every input pulse is longer than hi - lo, or per edge,
   `σ1 + hi(k) < σ2 + lo(k+1)` (`event_epin`). Data pins may glitch arbitrarily
   (`DPin`). Prelim's `BoundedDelay` is NOT enough under any input pulse condition,
   because it allows echoes (`bd_echo`).
4. **Latch open width, W=32.** The answer depends on the corner model, see below. With
   one corner for every delay it holds: about 2050 ps of round trip against about
   1275-1675 ps of enable rise. If the checker mixes fast-corner minima with
   slow-corner maxima (no corner model), it fails, by about 450-850 ps. The obligation
   is partly an artifact of how 8a decomposes `Sep`.

## Files and run command

| file | content |
|---|---|
| `formal/lean/Formal/Net/PerLink.lean` | `StageCtl`, `pipeline_protocol2`, `chain_transfers`, **`muller_pipeline2`**, `muller_pipeline_of_2` (8a's global-margin theorem is the constant case) |
| `formal/lean/Formal/Net/PerLinkPin.lean` | `ed` (edge-indexed bound), **`EPin`** (control pin), `N_shift`, `shift_epin`, `epin_comp`, `N_after_fall`, **`ELink`** with `inv`, `bounds`, `send_eq`, `at_recv`, `protocol`, `sep`, `hold`, `openWidth`, `srcData`; **`DPin`** (data pin), `shift_dpin`, **`latch_bit2`** |
| `formal/lean/Formal/Net/PerLinkEvent.lean` | `echoIn`/`echoOut`, `echo_bd`, **`bd_echo`**; counting lemmas; `evCnt`/`evOut` (per-event transport), `OrderPres`, `Pulse` (H_PULSE), `InBounds`, `orderPres_of_pulse`, `ev_char`, `ev_step`, `N_evOut`, `event_epin_op`, **`event_epin`**; `or2`, `or2_eq_ev`, **`or2_epin`** |
| `formal/lean/Formal/Net/EndToEnd2.lean` | `EB`, `Pipe2`, `PipeRun2`, `Route2`, `Realizes2`, **`checkPipe2`**, `Timing2`, `timing2_of_check`, `mOf`/`hOf`, `links2`, `latch_contract2`, `src_setupHold2`, `sep_ok2`, `hold_ok2`, `stage2`, **`end_to_end2`**; `symR`, `toP2`, `pipeRun2_of`, `realizes2_of`, **`end_to_end_fixed`** (8e's runs) |
| `formal/lean/Formal/Net/EndToEnd2Toy.lean` | `split`, `split_check2`, `splitP_realizes`, **`split_global_rejects`**, `split_fifo`, `good_check2`, **`bad_check2`**, `dack`, **`dack_check2`**, **`dack_band_rejects`** |
| `formal/lean/Wip/C8h/Axioms.lean` | `#print axioms` on the main theorems (it proves nothing) |

    cd /home/user/asyncfpga3/formal/lean && export PATH=$HOME/.elan/bin:$PATH
    export LEAN_PATH=$PWD/.lake/build/lib/lean
    # deps: 8a (Handshake, HandshakeMuller), 10a (Timing/Semantics, Checker), 8e (EndToEndRace, EndToEnd, EndToEndToy)
    for f in PerLink PerLinkPin PerLinkEvent EndToEnd2 EndToEnd2Toy; do
      ../slot.sh lean -o .lake/build/lib/lean/Formal/Net/$f.olean Formal/Net/$f.lean; done
    ../slot.sh lean Wip/C8h/Axioms.lean

The files must be compiled in this order. The lead has to add the five modules to the
root `Formal.lean` and to `check.sh`.

## What is proved, in plain words

**`muller_pipeline2` (PerLink).** Assumed: n Muller stages, stage j with the latch
contract at link j's margins (`m j`, `h j`); a causal source and sink; the source's data
meets `SetupHold (m 0) (h 0)`; every internal link j+1 meets `Sep (m (j+1))` and
`Hold (h (j+1))`. Proved: every link obeys the four-phase protocol, tokens out never
outnumber tokens in, and the k-th token out is the k-th token in. 8a's `Pipeline` fixes
one `(m, h)` for every stage, so the protocol induction is re-proved over a control-only
stage spec (`StageCtl`).

**`end_to_end2` (EndToEnd2).** Assumed:
- `PipeRun2`: the real `bd_c2n` and `bd_latch` INITs on explicit pin traces;
- every control pin is an `EPin` of its source node;
- every data pin is a `DPin` of its source bit;
- `Realizes2`: the bounds the theorem uses are sums of per-arc values inside the routed
  intervals.

If `checkPipe2 R n W = true`, the 8a conclusion holds for the node-level channels.

`checkPipe2` asks three races per stage j and bit b. Each race is 10a's verified
`check` on a `fan2` netlist:

| race | 8a obligation | edges used |
|---|---|---|
| setup j=0: `race2 (reqR 1 ++ [(1,1)]) (dat 0 b) 0` | source SetupHold + stage-0 latch setup | request RISE (source data moves with req↑) |
| setup j>=1: `race2 (reqF (j+1)) (dat j b) 0` | Sep at link j + stage-j latch setup | request FALL (Sep is close-to-close) |
| hold: `race2 (dat j b ++ ackF j ++ [(1,1)]) (enF j b) 0` | Hold at link j + latch hold | enable FALL vs acknowledge FALL (DACK) + data lo |
| open: `race2 (reqR (j+2) ++ ackR (j+1) ++ [(1,1)]) (enR j b) 0` | latch open width | enable RISE vs next stage's round trip (RISE edges) |

The margins are read off the run: `m 0 = rl(R1) + 2`, `m (j+1) = fl(R(j+2)) + 1`, and
`h j = fl(A j) + 1`. So 8e's `Sep`, `Hold`, source-setup and source-hold races hold by
construction, and only the races that compare two real paths remain. With a single
global m, the data wire of stage j had to be checked against the slowest request path
in the pipe (8e: "data <= m-1 <= req"). That is the source of the conservatism in the
8e finding.

**`end_to_end_fixed`.** 8e's exact-shift runs (`PipeRun`, `Realizes`) are an instance:
`shift_epin` and `shift_dpin`. So the per-link check proves the same conclusion as 8e's
`end_to_end` on 8e's runs. The new check is never needed on a weaker model.

**`ELink` lemmas (PerLinkPin).** The proof uses only the `lo` bound of each pin (its
`early` field), and only the lo bound of the edge that matters:
- `sep`: the request pin's fall bound;
- `hold`: the ack pin's fall bound;
- `openWidth`: both rise bounds;
- `srcData`: request rise and ack fall.

The hi bounds enter only through the latch (`latch_bit2`): the enable pin's rise hi
bound (open width) and fall hi bound (hold).

**`latch_bit2`.** A latch with enable pin `EPin gl gh x πG` and D pin `DPin dl dh D πD`
outputs `D e` from `e+1` until the node reopens, provided that:
- the node closed at e after an open phase from r;
- `r + gh(rise) + 1 <= e`;
- `dh + 1 <= m`;
- `gh(fall) <= dl + h`;
- D is stable on `[e+1-m, e+h]`.

The D pin may glitch however it likes while D moves. So per-event, glitchy data wires
are fully covered. Only control wires need the ordered `EPin`.

**Per-event delays (PerLinkEvent).**
- `bd_echo`: `BoundedDelay 1 3` from an input with ONE change (rise at 4) to an output
  that changes three times (at 5, 6 and 7: follow, echo the old value, follow). Every
  `Pulse lo hi` condition on that input holds vacuously, and the output is no `EPin`
  for any bounds. The fix has to be on the channel (no echo), not on the input.
- `event_epin`: model each input change σ as delivered at `σ + D σ`, with `D σ` inside
  the bounds of its edge, and take the output as the parity of the delivered count
  (`evOut`). Under `H_PULSE`, the delivered events keep their order
  (`orderPres_of_pulse`). The output then changes exactly once per delivered event
  (`N_evOut`), and it is an `EPin` (`ev_char`: the delivered events are always a
  prefix).
- `or2_epin`: the two-tap FASTRISE line `s(t-d1) || s(t-d2)` equals `evOut` with rise
  delay d1 and fall delay d2, when every pulse of s is longer than `d2 - d1`. So it is
  an `EPin (ed d1 d2) (ed d1 d2)`. Order preservation alone needs only the LOW pulses
  to be longer than `d2 - d1`. Equality with the two-tap OR also needs the high pulses,
  because otherwise a short high pulse fits between the two taps and is lost. A real
  N-tap chain (taps between d1 and d2) does not lose it; that case is not proved.

## Goal 4: the latch open-width obligation, with numbers

The obligation (8e's `lat_open`, here the `open` race): the enable pin of every latch
bit of stage j must have RISEN before the node can close again. The earliest close is
the next stage's round trip after the node rose:

    gR(j, b)  <=  rl(req path into stage j+1) + rl(ack path back from stage j+1) + 1 tick

Numbers (estimates assembled from three sources, not one route):
- **Enable fan-out**, W=32 (bd_link.v header, LIBRARY.md): the enable net reaches its
  first latch at 150 ps and its last 1125 ps after that, so about 1275 ps at the last
  bit. (If "1125 ps" is read as the absolute arrival, it is 1125 ps.) These are SDF
  numbers. 10b/10d found that the SDF's flat 25 ps site pin hides up to about 400 ps
  per sink (prjxray slow-corner site pins 420-531 ps). So the slow-max arrival at the
  last latch may be about 1675 ps.
- **One node-to-LUT-pin hop** (10d, routed ce_pair, prjxray): 262..859 ps over both
  corners (fast corner 262..385, slow corner 650..859). One LUT input plus O6:
  307..983 (fast 307..441, slow 750..983).
- **Round trip**, bd_pipe defaults (SDELAY = 1, DACK = 0):
  - request rise = node → SDELAY LUT1 → wire → C-LUT pin: about (307..983) + (262..859);
  - acknowledge rise = node → wire → C-LUT pin: about 262..859.

  Minimum: about 831 ps at the fast corner and about 2050 ps at the slow corner.

| reading of the delays | enable rise (hi) | round trip (lo) | verdict |
|---|---|---|---|
| no corner model (hi = slow max, lo = fast min: what `checkPipe2` on raw prjxray intervals does) | 1275-1675 | 831 | **violated by about 450-850 ps** |
| one corner, slow | 1275-1675 | about 2050 | holds, about 375-775 ps of slack |
| one corner, fast (enable scaled by about 385/859) | about 575-750 | about 831 | holds, about 80-250 ps of slack |
| last stage, fast sink (ack in one hop, no SDELAY on req_out) | about 575-750 (fast) | about 2 × 262 = 524 | **can be violated at a single corner** |

So: a shipped W=32 link passes at a single corner, with a few hundred ps of slack,
inside a bd_pipe (SDELAY on the request). An interval checker without corner
correlation rejects it. A stage whose consumer acknowledges quickly (the pipe's last
stage, or a bd_link fed to a one-LUT sink) can violate it outright at the fast corner.
The real verdict needs `checkPipe2` run on a routed W=32 pipe with per-sink prjxray
intervals. The netlist export exists (10d/11c), but feeding `Route2` from it is not done
here.

**How real is this obligation?** It is partly an artifact of 8a's decomposition. 8a's
latch contract (`H_LATCH`) demands the latch output be the new value at EVERY tick after
the upstream close e. The downstream setup race (`Sep`) is measured from that close.
Physically, a latch whose enable rises late still captures the right value, as long as
its enable pulse at the pin is not swallowed (`gR - gF < round trip`, a pulse-shrink
condition, trivially true for a symmetric enable branch). Its output is just late. What
breaks is the downstream setup, which assumed the data valid from the upstream close.
A decomposition that measures the downstream setup from the enable pin's rise plus the
latch D→Q arc would replace the open-width race by a longer setup race. That is not
done. Until then, the open-width race is a sound and conservative sufficient condition.

## Fidelity of every primitive model used

- **Time:** ℕ ticks, as in Net/Prelim. Edges are atomic.
- **Control pins (H_PIN = `EPin`):** ordered per-event transport. The k-th change of
  the pin is within `[lo k, hi k]` of the k-th change of its source, with separate
  rise and fall bounds. This covers:
  - exact shifts (8e);
  - asymmetric lines (FASTRISE/FASTFALL `bd_delay`, the two-tap form proved);
  - any per-event delay meeting H_PULSE.

  It excludes echoes, runts and swallowed pulses on control wires. Echoes are what
  `BoundedDelay` allows (`bd_echo`). Swallowed pulses happen when a pulse is shorter
  than hi - lo. In a protocol run every control pulse is a full handshake phase
  (hundreds of ps or more), against hi - lo spreads of tens to a few hundred ps per
  wire, so H_PULSE is expected to hold. **It is not discharged here from the protocol.**
  Discharging it needs a minimum-phase-length lemma (each phase >= the round-trip
  lower bound, essentially `openWidth`) compared with each pin's hi - lo. That is a
  check `checkPipe2` could add. Test: GLS at both corners with SDF min/max, counting
  pin transitions against source transitions on every control net.
- **Data pins (H_DPIN = `DPin`):** whenever the source bit was stable over
  `[t-hi, t-lo]`, the pin shows it. Arbitrary glitches are allowed otherwise. One band
  covers both edges, because the latch only needs stability and a data bit moves
  either way. Faithful for any delay model that settles within hi (pure, inertial,
  involution with a settling bound). Test: as above, on the latch D pins.
- **Path convention (H_NONINV_PATH):** every arc of a control path is non-inverting
  (wire, pip, LUT1/LUT2 buffer of `bd_delay`, LUT input-pin arc), so the edge at every
  arc is the source node's edge. True for `bd_link`/`bd_pipe`. An inverting arc on a
  control path would need the rise and fall lists swapped after it; that is not
  supported.
- **Composite bounds (H_ROUTE):** a path's rise (fall) bound is a sum of per-arc rise
  (fall) values inside the routed intervals. For per-event arcs, this is justified by
  `epin_comp` (EPins compose, and the bounds add edge by edge). Interval source: as
  in 8e, use prjxray-db min/max with site pins, not nextpnr's SDF (10b).
- **C-element (H_CEL):** as in 8e, the real `bd_c2n` INIT on the pins, SI (keeps its
  value or takes the function value). The LUT's internal loop and runts are shard B's
  business.
- **Latch (H_LATCH_CELL):** as in 8e, the real `bd_latch` INIT on its pins, one tick,
  deterministic. B's K3 latch contract is still not bridged.
- **Source/sink:** pin-level four-phase parties. Source data changes only with its
  request rise.

## Not done / open

- Discharge H_PULSE from the protocol: a minimum phase length per control net,
  compared with each pin's hi - lo. About half a day. Without it, `end_to_end2` with
  per-event pins still has H_PULSE as a hypothesis on every control pin (through
  `event_epin`).
- An N-tap FASTRISE chain (`or2_epin` is two taps). It needs dense taps (tap spacing
  less than the shortest pulse) or the high-pulse condition. About half a day.
- Whether a `BoundedDelay` echo actually corrupts a pipe, not just the invariant. The
  mechanism exists: an echo on the sender's ack pin can let the sender's C-element
  re-rise before the receiver's ack has fallen. A concrete run is not built. About
  half a day.
- Feeding `Route2` from a real routed W=32 pipe (10d's export, with per-sink enable
  intervals) and running `checkPipe2` with `decide`. That settles goal 4 on silicon
  data. About 1 day, mostly exporter.
- A corner-correlated `checkPipe2` (shared corner + local κ): this is what decides goal
  4's first row versus its other rows. It depends on shard A's corner model.
- The setup decomposition that would remove the open-width race (see above).

## What it buys the project

- `checkPipe2` is the check rules I and H should be. It has no free margin, and it has
  one race per stage and bit for setup (data wire vs request FALL path, or rise at the
  source), hold (enable FALL vs acknowledge FALL + data), and open width. A PASS is a
  theorem for every per-event, per-edge delay behaviour inside the intervals.
- DACK (FASTRISE) and RFAST/FASTFALL request lines can now be checked. Without per-edge
  intervals, a FASTRISE DACK line looks like a fast line and the hold race fails
  (`dack_band_rejects`).
- It identifies exactly which per-event behaviours the composition needs ruled out
  (echoes on control wires) and which it tolerates (any glitch on data wires).
