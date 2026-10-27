# A-kapres2: the cell lemma in Lean, the inverted fast bands, and KapRes with xevents7 (shard A)

Follow-up to `A-kapres.md`. There are three parts:
1. the cover lemma, proved;
2. the inverted FAST bands, traced to the source and corrected;
3. the KapRes grid rerun with xevents7.

## Verdict

RESULTS_VERDICT

## 1. The cell lemma, proved (`Formal/Core/Delay/CornerCell.lean`)

**Check.** From `formal/lean`:

    ../check.sh Formal/Core/Delay/CornerCell.lean

Result: `[audit] 1306 declarations checked`, then `[check] OK`. The file has no sorry, admit,
axiom, native_decide or bv_decide. The `decide +kernel` spot checks use kernel reduction only;
they add no `ofReduceBool` axiom, and the audit confirms this.

**The model.** It is exactly `Formal.Core.Corner`:
- `lerp F S c`;
- one shared `c`;
- `Scat κ D d`, i.e. `(1-κ)D ≤ d ≤ (1+κ)D`.

The integer form transcribes `kapres/cornerband.py` line by line (`cellLo` / `cellHi`):
- the fast band file pair `[f0, f1]` is read as its hull `[min, max]`, and the slow pair likewise;
- κ, `ca`, `cb` are rationals;
- the arithmetic is exact over ℚ (Python's `Fraction`);
- the lo end is `⌊(1-κ)·min(lerp(flo,slo,ca), lerp(flo,slo,cb))⌋`;
- the hi end is `⌈(1+κ)·max(lerp(fhi,shi,ca), lerp(fhi,shi,cb))⌉`.

Eight `example`s check the transcription against the Python output (`kapres2/spot.py`). They
cover an inverted fast pair and an arc with `S < F`.

| theorem | statement (plain language) |
|---|---|
| `lerp_min_le`, `lerp_le_max` | for `ca ≤ c ≤ cb`, `lerp F S c` lies between its values at `ca` and `cb` (no sign condition) |
| `cell_band` | the statement proposed in A-kapres §2. It needs `ca ≤ c ≤ cb` and `0 ≤ κ ≤ 1`; the proposal's `0 ≤ ca`, `cb ≤ 1` are not needed |
| `cell_band_mem` | for any endpoints `F ∈ [Fl,Fh]`, `S ∈ [Sl,Sh]`, any `c ∈ [ca,cb] ⊆ [0,1]` and any `d` with `Scat κ (lerp F S c) d`: `(1-κ)·min(lerp Fl Sl ca, lerp Fl Sl cb) ≤ d ≤ (1+κ)·max(lerp Fh Sh ca, lerp Fh Sh cb)` |
| **`cell_band_int`** | the same with cornerband's integer band: `cellLo ≤ d ≤ cellHi`. Here `d`, `F`, `S`, `c` are real, the endpoints lie in the hulls of the band-file integers, and `ca, cb, κ` are rationals with `0 ≤ ca`, `cb ≤ 1`, `0 ≤ κ ≤ 1` |
| `cell_band_nat` | the same for the ℕ model `Substrate.CornerNat`: an ℕ delay satisfying the decidable `Substrate.Scat k c a d` at an ℕ corner whose value `w1/(w0+w1)` is in `[ca,cb]` lies in `[cellLo, cellHi]` with κ = num/den. The proof goes through `Substrate.scat_real` |
| **`cellLo_anti`, `cellHi_mono`** | widening, for nonnegative endpoints: if `κ ≤ κ' ≤ 1` and `[ca,cb] ⊆ [ca',cb'] ⊆ [0,1]`, then `cellLo(κ',ca',cb') ≤ cellLo(κ,ca,cb)` and `cellHi(κ,ca,cb) ≤ cellHi(κ',ca',cb')`. This is the containment the sweep's `implied_clean` uses |

**Assumed:**
- the corner model (H-affine, SharedCorner, symmetric relative scatter `0 ≤ κ ≤ 1`);
- each arc's true fast and slow endpoints lie in the hull of its band-file pair.

Gate bands, which are aggregates over IOPATH rows, satisfy the second assumption as they stand:
every row's endpoints lie in the aggregate hull.

**Not covered:**
- whether the model is true of silicon;
- whether the band files hold prjxray's numbers correctly. Section 2 shows that for the fast
  corner they did NOT on the BRKH arcs;
- the global `lut` / `route` summary fields that cornerband also writes;
- anything about the checker.

**Lakefile / root import.** Nothing is needed in the lakefile. If the lead wants it in the root,
add `import Formal.Core.Delay.CornerCell` to `Formal.lean`. It imports `Formal.Core.Delay.Corner`,
`Formal.Core.Substrate.Real` and Mathlib's `Algebra.Order.Floor.Ring`, `Data.Rat.Cast.Order` and
`Data.Rat.Floor`.

## 2. The inverted FAST bands

### Where they come from

The chain is:

    xray_delay.py (research branch, md5 99b10a6d)  -- arcs.tsv, the four columns summed per element
      -> routed2x.py --corner fast                   -- bands_<seed>_fast.json (committed)
      -> (pinbands.py reads the same TSV columns)

**The source is in the prjxray database itself, not in a sum and not in a sign.**
- `prjxray-db/zynq7/tile_type_BRKH_INT.json` gives 14 pips the 4-tuple
  `[FAST_MIN, FAST_MAX, SLOW_MIN, SLOW_MAX] = [0.202, 0.105, 0.231, 0.312]` ns, i.e.
  FAST_MIN > FAST_MAX.
- The 14 pips are `NL1BEG0-2`, `NR1BEG0-3`, `SL1END0-3` and `SR1END1-3` through the horizontal
  clock-region break, tiles `BRKH_INT_X*Y49 / Y104`.
- They are the only inverted 4-tuples in the whole zynq7 db. I scanned every pip
  (`src_to_dst` and `dst_to_src`) and every site pin of every tile type.

**How it reaches the band files.**
- `xray_delay.py` sums the 4-tuples column by column along a route, plus one RC term that is the
  same in every column.
- So an arc through k such pips has its FAST_MIN raised by 202k and its FAST_MAX by 105k.
- When the rest of the route's fast spread is below 97k ps, the arc comes out inverted.

**The signature in the band files.**
- Ordinary elements have a fast spread of about 0.33 to 0.45 × their slow spread.
- A BRKH pip adds −97 to the fast spread and +81 to the slow spread.
- So `r = (FAST_MAX−FAST_MIN) − 0.375·(SLOW_MAX−SLOW_MIN)` is about 127k lower on a crossing arc.

On every seed the flagged arcs are cleanly separated from the rest:

| seed | arcs with the signature | of which inverted | r of the flagged | r of all other arcs |
|---|---|---|---|---|
| d | 22 | 20 | −117 … −128 | [−11, 56] |
| 3 | 7 | 7 | −121 … −132 | [−11, 75] |
| 4 | 8 | 8 | −118 … −122 | [−12, 45] |
| 5 | 2 | 2 | −122 | [−12, 60] |

All flagged arcs have k = 1; nothing lies near −254.

**Arcs that cross a BRKH pip but are not inverted.** Two arcs on seed d (`ulink_n141.lat.pair[18]`
LUT5/LUT6 I1, fast `[711, 711]`) cross the break without coming out inverted. A lo ≤ hi check
cannot see such arcs, but their bands are wrong all the same.

**Where the flagged arcs are.** All of them are LUT5/LUT6 pins of data latches (`lat.pair`,
`udat.pair`) plus one `lut1` on seed 3.

**Collatz (k2) also has them.** Its `/root/k2out/<seed>/arcs.tsv` has inverted IC rows: d 1,
4 13, 5 8, 6 3. Those bands are not committed. They are not treated here.

**Limit of the detection.** The routes are not available, because the gcd routed JSONs were
removed with the build worktree. So the BRKH arcs are found from the band files by this signature.
It is evidence, not proof: a crossing arc whose ordinary part had r > +67 would be missed. The
largest ordinary r seen is +75.

### The sound treatment (decided)

**The rule.** Read the BRKH element's fast delay as the hull of its two prjxray numbers,
`[0.105, 0.202]` ns.

**What it does to each band, for an arc with k crossings:**
- fast `[FAST_MIN, FAST_MAX]` becomes `[FAST_MIN − 97k, FAST_MAX + 97k]`. This is exact in whole
  ps, because 202 − 105 = 97;
- mixed / indep `[FAST_MIN, SLOW_MAX]` becomes `[FAST_MIN − 97k, SLOW_MAX]`. Note that the indep
  lo of these arcs was 97 ps too high, with no inversion to show it;
- slow and gb do not change.

**Why the KapRes readings were not enough.**
- Taking the hull of the ARC's two numbers, as `kapres/cornerband.py` did, is not sufficient. On
  `[494, 487]` it gives `[487, 494]`, but the element hull gives `[397, 584]`.
- `Parse.toSteps`'s `[lo, lo]` reading is narrower still.

**The validator, `kapres2/check_bands.py`.**
- `check FILE…` rejects any `lo > hi` (exit 1) in `cells`, `arcs`, `pins`, `sitepins`, `lut`
  and `route`. It is the gate to put in front of the Lean reader.
- `brkh FAST SLOW [--skel …]` lists the signature arcs.
- `fix FAST SLOW INDEP OUT` writes the corrected fast and indep files and re-checks them.

On the committed files, `check` rejects exactly the four fast files: d 20, 3 7, 4 8, 5 2. Every
slow, indep, gb and smax file passes.

### Which committed results used them, and does any verdict change?

| result | reads the full-netlist band file? | BRKH arcs used? | rerun with corrected bands | verdict change |
|---|---|---|---|---|
| Events4/5/6/7/8 rows, A-kapres (xevents5), this sweep | no: the control skeleton (`events4/skel.py`) | **no.** The skeleton keeps none of the 39 BRKH arcs. The skeleton bands built from the corrected fast and indep files are **identical** to the originals on all 4 seeds (cells, arcs, lut, route) | the pipeline on the corrected bands reproduces `events7/xe7_3_slow.txt` and `xe7_3_fast.txt` byte for byte | **none, by construction** (identical checker input) |
| `gcd/results/fbrace.txt` (static own-feedback race, fast and indep, 4 seeds) | yes | read | `kapres2/rerun/fb_fix_<seed>_<fast,indep>.txt`. The originals reproduce the committed file exactly | **none.** Every line is identical |
| `pin/results/gcd_summary.txt` (gcdpin, per-pin margins) | full bands, but only skeleton pins are looked up | no (0 hits) | not needed | none |
| `gcd/results/d_fast_v1` (xaudit X-sim, full netlist, fast) | yes | read (the 22 seed-d BRKH cells are printed nodes, all already flagged "final X") | **not rerun.** It takes about 6 min with a native `xaudit` that is not built here; `lean --run` would take hours | its verdict is already negative (187 clean / 227 flagged control nodes). Corrected bands are wider on 22 data-latch arcs, by 97 ps (at most 4 steps of 25 ps) a side. This can only add behaviours, so the run stays a non-sign-off. The flag counts might move |
| `gcd/samples` (csim concrete samples, fast and indep) | yes | element values drawn in the inverted band | not rerun | evidence only, no claim depends on it |

## 3. KapRes with xevents7

RESULTS_SECTION3

## Files

| file | what |
|---|---|
| `formal/lean/Formal/Core/Delay/CornerCell.lean` | **proved**: the cell lemma, cornerband's integer band, the ℕ bridge, widening |
| `formal/tools-A/xaudit/kapres2/spot.py` | cornerband's formula on 4 arcs, emitted as the Lean `example`s |
| `…/kapres2/check_bands.py` | validator (lo ≤ hi), BRKH signature finder, corrector |
| `…/kapres2/rerun/fb_fix_*.txt` | fbrace on the corrected fast and indep bands |
| `…/kapres2/kapres2.py` | kapres.py's sweep with cert7 + xevents7, corrected fast bands, band validation, header checks |
| `…/kapres2/mk.sh`, `xe7.sh`, `run.sh` | private overlay `/tmp/kapres2/olean` (committed Events7 modules recompiled into a copy of E7r's overlay), `lean --run` with at most 2 at once, the driver |
| `…/kapres2/runs/<seed>/` | xevents7 outputs per cell and `summary.json` |
| `…/kapres2/table2.py` → `table2.txt` | per seed and κ: the cover, residual items, point-corner failures |
