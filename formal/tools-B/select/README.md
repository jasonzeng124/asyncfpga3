# tools-B/select — select-mux captures on THE target (shard B, untrusted Python)

* `muxsrc.py`, `muxsrc.log`, `summary.json`, `uncovered_mux.json.xz`, `selchk.py`: measurement (2026-11-15) of the
  latches whose data source is a 2:1 mux LUT; 1,070 not covered by LatchHold(Pin)PS*, 933 of them `umux*.udat`
  (select and both inputs are latches at depth 0).
* `gen_selhold_ps.py`: emitter of `SelectHold.SelRow` rows -> `Formal/Cells/SelHoldPS.lean`.

## gen_selhold_ps.py

```
python3 -I tools-B/target/simb.py NET.json BND.json --pairs 0x49e9c618,0x35bf992e --corner 0 \
    --datachange broad --tmax 60000000 --dump DUMP.json          # ~1 min, result 2 (correct)
MAXROWS=20 CHECKVARIANT=/scratch/SelHoldPSV.lean \
python3 -I tools-B/select/gen_selhold_ps.py NET.json DUMP.json tools-B/select/uncovered_mux.json.xz \
    lean/Formal/Cells OUTDIR
```

NET.json / BND.json: `tools/cview/lean2json.py` on NetPS (as for muxsrc.py). Per umux latch (LatchViewPS row q,
enable pin e, data pin d = the mux) it takes a close of the enable source es in the dump (es leaving the open value
`!pe`), and at t0 = close - 1:

* the mux row: controlling pins [select, selected input], the selected input being the one that with the select
  value forces the mux INIT to its value at t0 (other pins free, tied pins held);
* two chains es -> select latch and es -> selected input latch: structural search (`bestchain`): simple paths of
  at most MAXD (8) LUT steps, each step with a controlling set (path pin + static pins, memory row only if needed;
  `ctlset` as gen_certs_ps.py) whose static pins do not change in the run on [t0, close + HOR (20 ns)]. Chosen:
  margin at κ = 0, then fewest premises (statics + memory rows), then the largest margin;
* margin ratios kA/kB per chain = min(ΣFmin(path)/(ΣFmax(e)+1), ΣSmin(path)/(ΣSmax(e)+1)) reduced (the largest
  κ range `(1+κ)kB ≤ kA(1-κ)`, i.e. κ ≤ (kA-kB)/(kA+kB));
* the latch's LRow literal copied from LatchViewPS.

Outputs: the Lean file (rows `rNN`, per-row `rNN_certs`/`rNN_sel` by `decide +kernel`, `certs_ok`, `sel_ok`),
`OUTDIR/SelHoldPS_report.json` (per latch: close time, select/selected nodes, chain steps, statics, sums, kA/kB,
κ ranges, or the failure reason), and optionally CHECKVARIANT: the same file with SelectHold's definitions copied
verbatim instead of importing it (for a `lake env lean` check while SelectHold.olean is not built).

Why not ctlcert.py: in this run the selected input latches almost never change after the closes (ctlcert needs the
target to change, and its window would span microseconds). The structural chains are therefore not the causal
paths of the run; they are only certificates whose premises (cause, statics, memory rows) the run satisfies on the
window used. Only 259 of the 933 umux latches have an enable close after reset in this one run.

Trust: everything here is untrusted; Lean checks `certOK` for both chains and `selOK` (wiring, mux forcing,
values, latch row, the four margin facts) by kernel decide. Premises of the certificates are not checked.

## State 2026-11-15 (first emission)

`Formal/Cells/SelHoldPS.lean`: 20 rows (PERINST=3 rows per umux instance, CLOSES=3; 9 instances: umux12-19 and the
X30Y51 / X30Y64 ones), every attempted latch with an enable close got a row. Row κ ranges (min of the two chains):
0.606 - 0.855, median 0.694. Per-row data: `selhold_report.json` (close time, select / selected latch, chain steps,
static premises, arc sums, kA/kB). Most data chains use the reset node (186905, value false) as a static premise.

Lean check: SelectHold.olean is not built (nothing imports it yet), so the file was checked through the generator's
CHECKVARIANT (SelectHold's definitions verbatim, rows and theorems byte-identical) split per row (CHECKPARTS=20):
all 20 parts pass `lake env lean` (27-123 s each, peak RSS 3.2-6.3 GB per part); the 20-row combination theorems
were elaborated with the decides stubbed (12 s). The whole 20-row file in one process was OOM-killed three times
(shared memory with a running build), so a `lake build Formal.Cells.SelHoldPS` remains to be run.
