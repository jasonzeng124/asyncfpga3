# How to regenerate and re-check shard B's driver-bound gate-level witnesses (Bwit, Bwit2)

2026-10-31. What these files prove is in `notes/B-finite-net-bound.md`. This page is the
procedure: what to run, in what order, and what each step checks.

## The pipeline

| step | command (from the repo root) | output | trusted? |
|---|---|---|---|
| 1 gate-timed run | `python3 -B formal/tools-B/bwit/bsim.py 12 18` (links, forks, joins, steers) or `bsim2.py` (plus every `bd_mux`) | prints C's checker verdict and the wiring census | no (Python) |
| 2 C-level data | `python3 -B formal/tools-B/bwit/gen_cdata.py` / `gen_cdata2.py` | `Cells/BWitData.lean` / `BWit2Data.lean` | no (data) |
| 3 network data | `python3 -B formal/tools-B/bwit/gen_bdata.py` / `gen_bdata2.py` | `Cells/BWitNData.lean` / `BWit2NData.lean` (pin wire delays, token tables, internal mux node lists) | no (data) |
| 4 C's hypotheses | Lean: `Cells/BWitCells.lean` / `BWit2Cells.lean` | `b_cells`, `b_held`, `b_start_once`, `b_forced`, `b_out0` (C's own checkers, by kernel) | yes |
| 5 B's network | Lean: `Cells/BWitNChk.lean` / `BWit2NChk.lean` (kernel checks), `BWitNet.lean` / `BWit2Net.lean` (proofs) | `bwit_ok`, `gcd_hw_fin_netB_witness`; `bwit_okM`, `gcd_hw_fin_netBM_witness` | yes |

`--check` on any generator regenerates in memory and compares with the committed file
(drift = exit 1). Steps 4-5 run in `formal/check.sh` (they are ordinary modules).

## What each checker decides (and why a passing run is not trusted before the kernel)

* `wireChk` (per channel): each of the channel's two pins is the node list of the cell the
  netlist names (`FiniteNetBound.reqSrc`/`ackSrc`, or the `M` versions), shifted by the pin's
  wire delay minus one; the delay is at least one.
* `lkChk`, `faChkB`, `jrChkB`, `stChkB`, `muxChk` (per operator): Bfin3's cell checkers
  (`linkB`, `celB`, `stB`, `orB`) and the mux checkers (`mjB`, `maB`, `bufB`, `BWit2Lib`) at
  every tick up to `NB` (with the tail constant after), plus each node's edge times
  (`celTm`, `stTm`, `orTm`, the link's `τ1`, `cjT`, `bufT`) at every existing edge.
* The soundness lemmas (`*_spec'`, `mjB_spec`, `maB_spec`, `bufB_spec`) turn a passing check into
  the corresponding `FiniteNetMixed` / `AssumeGuaranteeMuxNFin` spec, so the network theorem's
  hypotheses are met by construction, not by the simulator's say-so.

## Porting to another run or kernel

* Another input pair of gcd_hw: steps 1-3 take `a b`; step 4 also needs C's token-level walk
  for that pair (`b_forced` uses C's `yW` for 12/18).
* A longer run: raise `FiniteRunsWit.NB` (now 768) above the last event; the old witnesses
  re-check (it only bounds the tick range the checkers scan).
* Another kernel: the Lean side is written against `Formal.Net.CapNet.Gcd` (`opAt`, `prodOf`,
  `consOf`, `NC`, `NO`) and C's simulator reads `CapstoneNet.lean`. A port duplicates
  `FiniteNetBound`/`BWit*` against that kernel's `CapNet` module and points `bsim.py` at its net
  file. Not done.

## Negative controls (run 2026-10-31)

* `bsim.py --neg` / `bsim2.py --neg` (steer branch drivers swapped): 63 pins flagged.
* `BWitNData`: channel 20's request wire delay 2 -> 1: `bw_c1` fails by kernel.
* `BWit2NData`: first entry of one `uj0` node list +1: `BWit2NChk.bop_c1` fails by kernel.
