# B probe Bov2: do pessimistic LUT models explain the arbcell 8% filtered overlap?

Shard B, 2026-10-29. This follows Bov (`B-arb-overlap-race.md`, `ArbOverlapRace.lean`) and
Bmt (`B-arb-mtbf-copies.md`), and uses Bpess's models (`B-kleene-pess.md`, `KleenePess.lean`).

- **Question (PROGRAM.md).** Does a race trace explain the bd_arbcell overlap on
  `hw/arb_mtbf.v`? The board saw FILTERED 15/192 and RAW 139/192, with W = 2.
- **Already known.** Under binary transport, Bov and Bmt predict 0/192 at a consistent
  corner, because the filter threshold with site pins is Dw ~ 1.35 ns (median, SLOW_MAX)
  and at least 425 ps.
- **This probe.** Does any KleenePess policy change that answer? The policies are `kle`,
  `weak1`, `weak0`, `strict`, or any per-pin mix. Each model `x` is resolved adversarially,
  tick by tick.

File: `formal/lean/Formal/Cells/ArbOverlapPess.lean`. It is core Lean and imports
`KleenePess` and `ArbOverlapRace`. It checks with
`/tmp/claude-0/btools/bcheck.py Formal/Cells/ArbOverlapPess.lean`: OK, 0 warnings, a few
seconds. The file has no sorry, admit, axiom, native_decide, implemented_by, extern or
unsafe. `#print axioms` on the 14 headline theorems gives at most
`[propext, Classical.choice, Quot.sound]`. `pess_fires` uses none, `st_hold1_r2` only
`propext`. The print lines were removed afterwards.

## Answer in one paragraph

**The pessimistic models do not explain the 8%. They make the filtered bit stop meaning
"long overlap".**

1. **Zero-width edges (`w0_rig`).** If every edge has zero width, no pin is ever `x`.
   Every policy then *is* Bov's binary model, so Bov's caps and Bmt's 0/192 hold under all
   four models. Pessimism can act only through a mid-rail select, which needs an edge
   window `w ≥ 1`.
2. **Detector path passes 0 (`kle`, `weak1`).** When the detector and filter pins pass 0,
   the filter is still a width filter with slack `w` (`filter_isolated`). A filtered event
   then needs an isolated raw run longer than `Dw − w`, or two raw 1s `Dw` apart.
3. **`weak0` or `strict` on an upwand pin (`pess_trace`, `fires_iff`).** The filter fires
   from a single raw edge.
   - The explicit trace has every gate relation proved, real INITs, Bov's SLOW_MAX delays,
     Dw = 1348 ps and w = 1 ps. Its raw signal is one 305 ps run, so the binary filter can
     never fire on it (`pess_raw_short`).
   - The upwand AND reads `[x, 0]`. Kleene gives 0, but `weak0` gives `x` (`and_x0`), and
     the sticky can be set.
   - On this trace family, a filtered event is possible **iff an upwand pin fails to pass
     0** (`fires_iff`). The control is `ctrl_kle_clean`.
4. **`weak1` at ustate's r2 pin (`st_hold1_r2`, `weak1_chain`).** One request edge into a
   both-high hold puts `x` on q and on both grants. No race is needed.
   - Whether that `x` lasts long enough in the timed model to give a filter-sized raw run
     is **not proved** either way. §6 gives the necessary conditions.

Every model that permits firing permits it in **every** copy whose raw has an edge. So no
policy accounts for the selectivity of 15/192. The fraction could only come from *per-pin*
policies interacting with per-copy pin assignment, and that is untested. The verdict "8% not
explained" stands. A new caveat applies: under a weak-0 LUT the FILTERED bit is not evidence
of an overlap of the measured size.

## Model (`PRig`)

- **Gates.** These are the real INITs, through KleenePess `lutM` (the closed form of the
  per-pin mux-tree model; `lutP_eq_lutM`):
  - `ustate` = `C2N_SET` `FFB2…`, pins `[r1, r2, q, rst = 0, 0, 0]`;
  - `ugrant` O5/O6 = `GRANT`, pins `[r1, r2, q, 0, 0, 1]`;
  - detector and `upwand` = LUT2 `8`.
- **Policies.** One `Pol` family per LUT, indexed by pin (`Pols`).
- **Pins** (`pinW x d w t`). A pin reads its source through Bov's per-pin transport delay
  (`Dl`: route + site pin + arc). It reads `x` while the delayed source is not constant
  over the last `w + 1` ticks, i.e. a mid-rail select while an edge passes (H_EDGE_X). The
  edge width `w` is unmeasured.
  - The two-link chain `bd_delay(2)` is lumped into one pin of delay `c0 + Dw` and window
    `wd`.
- **Adversarial resolution** (H_PESS_ANY). Each LUT output at each tick is any binary value
  that its model output admits. A model `x` may be read as 0 or 1 by each reader, tick by
  tick. This is the reading the board asked for. It is the right reading for a pessimistic
  `x` (a runt or mid-rail level read by different thresholds), and too generous for a
  Kleene/GMW `x` (delay uncertainty on one net).
- **Observable.** `Fires flt` means the filter output is 1 at some tick (as in Bov and Bmt).
- **Correspondence to Ternary{Sound,Exact}.**
  - Soundness transfers: `admits_of_kle` and `prig_of_kle` show that every all-Kleene trace
    is a trace of every policy family (the bracket `lutM ⊑ lutK`). A pessimistic model only
    adds traces.
  - Exactness does **not** transfer: §4's firing trace has no all-Kleene counterpart
    (`fires_iff` vs `ctrl_kle_clean`), so the extra `x`s are not binary GMW behaviour.
  - PRig's window semantics is a variant. I did not prove it equal to TernarySound's
    `Run`.

## Theorems (namespace `Formal.Cells.ArbOverlapPess`)

| theorem | assumed | proved |
|---|---|---|
| `w0_rig` | PRig, any policies, w = wd = 0 | it is Bov's `Rig`, and flt = raw(t−c0) ∧ raw(t−c0−Dw) |
| `w0_raw_cap`, `w0_cell_never_203`, `w0_filter_iff` | the same | Bov's raw cap \|s+b\|; the cell's g1∧g2 run is < 203 ps (prjxray box); filter iff Dw < run |
| `prig_of_kle` | an all-Kleene PRig | it is a PRig of every policy family |
| `filter_two_point`, `det_two_point` | the AND's (or detector's) pins 0 and 1 pass 0 | output 1 at t ⇒ each input has a 1 in its window |
| `filter_isolated` | upwand pins pass 0; every raw 1 is in [lo, hi) | Fires ⇒ Dw < (hi − lo) + w |
| `pess_trace`, `pess_fires`, `pess_raw_short` | slowD, c0 = 429, Dw = 1348, w = wd = 1; ustate, ugrant and detector Kleene; upwand I0 weak0 | every gate relation holds for all t; it fires at t = 2132; raw is exactly [1703, 2008), and the binary filter is 0 everywhere |
| `ctrl_kle_clean`, `ctrl_witness` | the same signals; both upwand pins pass 0 | no admissible flt fires; flt ≡ 0 is a trace (non-vacuous) |
| **`fires_iff`** | the same signals; ustate, ugrant and detector Kleene; any upwand policy | ∃ firing trace ⇔ (fa 0).p0 = false ∨ (fa 1).p0 = false |
| `and_x0`, `and_0x`, `and_xx` | LUT2 8, any policy | [x,0] gives x iff I0 fails 0; [0,x] gives x iff I1 fails 0; [x,x] gives x |
| `st_hold1_r2`, `st_hold1_r1`, `st_hold0_r1`, `st_hold0_r2` | bd_c2n_set, one moving request, q held | x iff that request's pin fails the held value (Kleene: definite) |
| `st_xhold`, `st_restore0`, `st_restore1`, `restore_weak` | q pin x | held as x on r1 = r2 (every model); (0,1) restores 0 iff I2 passes 0; (1,0) restores 1 iff I2 passes 1 |
| `grants_both_x`, `weak1_chain`, `weak0_chain` | q = x, r1 = r2 = 1 | both grants x in every model; under weak1 at I1 the chain r2 edge → q x → hold x → g1, g2, raw, flt all x (Kleene keeps q = 1) |
| `raw_needs_both` | ugrant and detector pass 0; any ustate policy | raw(t) = 1 ⇒ q = 1 within 2w before t−(e1+b5) and q = 0 within 2w before t−(e2+b6) |
| `toggle_echo` | requests constant over ustate's pin windows; any ustate policy | a q toggle at u ⇒ a q toggle in [u−1−L−w, u−L] |
| `w0_witness`, `isolated_witness`, `raw_needs_both_witness`, `echo_witness` | | the hypotheses above are jointly satisfiable (Bov's trace; a 1 ps runt circulating in a both-high hold) |

## The firing trace, concretely

- **Delays.** These are Bov's SLOW_MAX delays (`slowD`; SLICEL, zero SDF skew):
  - s1 = s2 = 636, L = 640;
  - a1 = 1068, b5 = 525, b6 = 531;
  - e1 = 940 (g1c on detector A1), e2 = 536 (g2c on A5).
- **Requests.** r1 falls at 0 and r2 stays high: the handover r1 → r2.
- **Signals.** q falls at 636, g1 = [.., 1068), g2 = [1167, ..), raw = [1703, 2008)
  (305 ps).
- **Filter.**
  - upwand.I0 reads raw after c0 = 429 ps (300 route + A6 site pin 5 + arc 124).
  - I1 reads raw after c0 + Dw = 1777 ps. Dw = 1348 is Bmt's median per-copy SLOW_MAX
    threshold. Bmt's minimum is 425, also above 305.
- **Firing.** At t = 2132 the raw rising edge sits on I0 (`x` for w = 1 tick) while I1
  still reads 0. Kleene gives AND = 0, `weak0` on I0 gives `x`, and flt = 1 is admissible.
- **Symmetric case.** The same holds on I1 at t = 3480 when I1's level fails 0.
- **Every edge counts.** Any raw edge fires, of any width. So this mechanism is available
  in every RAW-firing copy (RAW 139/192 on the board).
- **The detector itself.** Under `weak0` on a detector pin, `and_x0` gives a raw runt at
  every grant edge while the other grant is 0. That would make even D ≤ 0 copies fire.

**Enabling condition (which pin passes which value):** the physical upwand pin carrying raw,
or the chain output, must fail to pass 0 under a mid-rail select (`weak0` or `strict` on
that level). Its edge window must also be at least 1 tick. With `w = 0`, or with that pin
passing 0, the trace cannot fire (`w0_filter_iff`, `ctrl_kle_clean`).

## Board tests

1. **Pass test on the filter AND (confirms or kills §4).** Add, per copy, a
   `(* keep *)` LUT2 `8` with I0 = raw and I1 a 0 that synthesis cannot fold (for example
   a flop with INIT 0 and CE tied low, kept). It feeds its own sticky, with no delayed
   input at all. Use LOCK_PINS to rotate raw over A1..A6 across copies.
   - Binary, Kleene and weak1 predict that it never fires.
   - weak0 or strict on pin j predicts firing on RAW copies with raw on pin j.
   - This is KleenePess experiment 1 restricted to (LUT2, v = 0).
2. **Pin-swap rebuild of arb_mtbf.** Keep the FASM this time. Swap upwand's physical pins
   for raw and raw_d. Under §4 the FILTERED set follows the physical pin. Under Bov's
   mechanism it does not.
3. **Necessary check on any future run.** Under §4, FILTERED ⊆ RAW per copy (the AND needs
   a raw edge). The same holds under Bov. So this check is not discriminating, but it is
   free.
4. **For §5 (the weak-1 cell runt).** Lock `ustate`'s r2 pin per copy. If FILTERED tracks
   r2's ustate pin, the weak-1 hold runt is implicated. No rate is predicted: the timed
   duration is open.

## What did not work / open

- **The weak-1 timed run is open.** §5 shows that one r2 edge during (q, r1) = (1, 1) puts
  `x` on q and on both grants under weak1, and `st_xhold` keeps it through the hold. In the
  timed window model the `x` then circulates in q's loop:
  - `toggle_echo`: with quiet requests every toggle is an echo of one L earlier.
  - `raw_needs_both`: a raw run longer than |s+b| + 2w needs q toggling in every window
    of span |s+b| + 2w.

  I argue, but have not proved, that with w much less than L (640 ps) the echo train is far
  too sparse to give a ≥ 1 ns raw run within one both-high phase of ≤ 1.46 ns. It would
  take a large `w` (edge width comparable to the loop). The general echo-growth bound
  (`x` region growing by at most w per loop) is not proved.
- **The sticky latch is not modelled.** Fires means flt = 1 for at least one tick. A
  one-tick set pulse may not latch a LUT3 loop in binary transport. Under the adversarial
  window semantics it circulates and can widen. Not proved.
- **The chain is lumped.** `bd_delay(2)` is one pin. Its two LUT1s each add a window
  (`wd`, a parameter).
- **Locality.** The trace uses one request edge (r2 ≡ 1), as Bov's did. On the board the
  rings are square waves with half-periods of about 1.46 and 1.92 ns. The trace depends
  only on a window of about 4 ns. That is argued, not proved.
- **Neither the rate nor the selectivity is explained.** Every model here says "may". No
  model forbids firing in the 177 clean copies, and none forces it in the 15. Explaining
  15/192 needs per-pin policies plus the measured bitstream's pin map, which was not
  archived (Bmt).

## Proposed journal paragraph (JOURNAL-B)

- ARBCELL UNDER PESSIMISTIC LUTS (Bov2, ArbOverlapPess): KleenePess's models do not
  explain the 8%; they can make the FILTERED bit fire without an overlap of the measured
  size.
  - With zero-width edges every policy collapses to Bov's binary model (`w0_rig`), so
    Bov/Bmt's 0/192 stands under kle/weak1/weak0/strict.
  - With a 1 ps edge window and upwand's raw pin failing to pass 0 (weak0/strict), an
    explicit full-copy trace (real INITs, SLOW_MAX, Dw = 1348) fires on a single 305 ps raw
    run. Firing is possible iff an upwand pin fails 0 (`fires_iff`; control
    `ctrl_kle_clean`).
  - Under weak1 one request edge into a both-high hold puts x on q and both grants
    (`weak1_chain`). Its timed duration is open.
  - Soundness of the Kleene reading transfers (`prig_of_kle`); exactness does not.
  - Test: an AND(raw, 0) control LUT per copy with locked pins.
