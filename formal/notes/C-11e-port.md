# C-11e: port shard C off `Formal/Cells/Prelim.lean`

**Verdict: works.** 22 shard-C modules no longer import `Formal.Cells.Prelim` at all
(directly or through anything). They now use shard A's Core (`Formal.Core.Lut`:
`Lut.eval`, `Lut.keval`, `Lut62`, `Formal.Core.K3`). The modules that still reach
Prelim do so only through shard B modules that are themselves still Prelim-based. Each of
those is listed below with the B names it uses, so the swap is mechanical once B has
ported. No theorem was weakened. Statements whose type changed (Prelim `K3` to Core `K3`)
keep their pre-port form too, proved from the bridge. No sorry, axiom or native_decide.
The axiom audit over 3055 declarations in the 38 touched modules found only propext,
Classical.choice and Quot.sound.

## How it is done

* **`Formal/Net/CoreLut.lean`** (new, imports only `Formal.Core.Lut`). This is the list
  view of Core that shard C's netlists need (Nat INIT, pin list `[I0, I1, ...]`). Nothing is
  redefined: `evalL init ins = (lutOf init ins.length).eval (bvec ins ins.length)` with
  `lutOf init k = ⟨BitVec.ofNat (2^k) init⟩`. Likewise `kevalL` = `Lut.keval`, `o6L`/`o5L`
  (`o6KL`/`o5KL`) = `Lut62.o6`/`o5`, and `kmux` is the node of Core's `kevalT` mux tree.
  It also adds a `Decidable (∀ k : Core.K3, _)` instance.
  Lemmas: `evalL_eq_testBit`, `kevalL_ofBool`, `kevalTL_cons`, `kevalT_congr`,
  `kevalL_eq_kevalTL`, `kmux_eq_kevalL`, `o6L_eq_evalL`, `o5L_eq_evalL`.
* **`Formal/Net/CoreLutPrelim.lean`** (new). The bridge to Prelim. **Delete it together with
  Prelim.** It covers every INIT and every pin list:
  `lutB_eq_evalL`, `o6B_eq_o6L`, `o5B_eq_o5L`, `lutK_eq_kevalL`
  (`lutK init (ins.map toP) = toP (kevalL init ins)`, through B's `MuxTree.muxTree_eq_lutK`),
  `lutK_eq_kevalL'`, plus `toP`/`ofP` (the bijection `zero one X` ↔ `f t x`), `toP_merge`
  and `toP_kmux`. It is the list form of A's `Core.Bridge.cells_lutB_eq_eval` and
  `cells_lutK_eq_keval`. I did not use `Core.Bridge` itself: it needs the LutTree, Ternary and
  MuxTree oleans and it imports Prelim too.
* **`Formal/Gen/PrelimSem.lean`, `Formal/Net/Import/PrelimSem.lean`** (new). These are porting
  aids, deleted with Prelim. They hold `kleeneSemP` (the same interpreter with Prelim's
  `lutK`) and `boolSemP` (Prelim `lutB`).
  `boolSem_eq_boolSemP : boolSem = boolSemP` holds as an equation (`Bool` is shared).
  `kleeneSemP_lut` and `kleeneSemP_const` show the two Kleene readings agree through `toP`.
  The Gen file also has `prim_tables_prelim`, `mux_kleene_prelim` and
  `prims_muxf_kleene_prelim`, the pre-port statements derived from the Core ones (the last
  is by `decide`).
* **`Formal/Net/Fasm/CoreView.lean`** (new). `PLut.fnCore` is the Core reading of a physical
  LUT, and `PLut.fn_eq_fnCore` says it equals `PLut.fn` on 6-pin vectors.

Why `Fasm/Basic.lean` is NOT changed: shard B's `Formal/Cells/OnNetlist.lean`
(`fnK_ofBool`, line ~556) does `simp only [..., PLut.fn, o5B, ...]`. Redefining `PLut.fn`
would break a B file that C cannot edit. `CoreView` is the replacement, ready for B.

## Files changed (exact)

Edited (C-owned):
- `Formal/Gen/Netlist.lean`: imports `Formal.Net.CoreLut`. `boolSem := ⟨evalL, id⟩`,
  `kleeneSem : Sem Formal.Core.K3 := ⟨kevalL, K3.ofBool⟩`. `prim_tables` is stated with
  `evalL`, `mux_kleene` with `kevalL`/`kmux`. The Prelim `K3.decForall` moved to `PrelimSem`.
- `Formal/Gen/ProofsPrims.lean`: Core throughout (`evalL`, `kmux`, Core `K3`).
- `Formal/Gen/Proofs{CE,Latch,Link,Ctl,Arb}.lean`: `kleeneSem` → `kleeneSemP`, plus
  `import Formal.Gen.PrelimSem`. Statements are otherwise unchanged. Five symbolic `rfl`
  proofs (`bd_merge_W2_step`, `bd_mux_W2_step`, `bd_link_W2_DC_step`, `bd_link_dc_W2_step`,
  `bd_pipe_dc_W1_N2_step`) needed `rw [boolSem_eq_boolSemP]` first. Their statements are
  unchanged. `ProofsMisc` needed no edit.
- `Formal/Net/Import/Netlist.lean`: same as Gen/Netlist. `Formal/Net/Import/Proofs.lean`:
  `kleeneSem` → `kleeneSemP`, plus the import.
- `Formal/Net/HandshakeMuller.lean`: `celN` uses `evalL` and imports `CoreLut`.
  `HandshakeLive.lean` and `EndToEnd2.lean` drop `open Formal.Cells`.
  `EndToEnd.lean`: `latchF` uses `evalL`, and `latch_pair` uses `o5L`/`o6L`.
- `Formal/Net/Muller.lean`: imports `CoreLut` and `Core.LutCells` instead of Prelim and
  `CElemFn`. The node function is `evalL INIT_bd_c2n`, with
  `INIT_bd_c2n := Formal.Core.LutCells.bd_c2n_u.init` (A's RTL extraction; equal to B's
  `CElemFn.INIT_c2n` and to yosys by `Gen.ProofsCE.bd_c2n_lut`/`ce_inits_lutcells`, and to
  `0x00B200B200B200B2` by `INIT_bd_c2n_val`). `MullerTimed.lean` and `MullerTimedCx.lean`
  were updated to match (`boundary_function_hazard` now uses `evalL INIT_bd_c2n`).
- `Formal/Net/Fasm/CePair.lean`: adds `q1_kleene_s1_core` (Core twin of `q1_kleene_s1`).
- `formal/tools/fasm2lean/check.sh` (builds `CoreLut` if missing; audits
  `q1_kleene_s1_core`) and `formal/tools/fasm2lean2/check.sh` (dependency list gains `MuxTree`,
  `CoreLut`, `CoreLutPrelim`, `Import/PrelimSem`).

New: `Formal/Net/CoreLut.lean`, `Formal/Net/CoreLutPrelim.lean`, `Formal/Gen/PrelimSem.lean`,
`Formal/Net/Import/PrelimSem.lean`, `Formal/Net/Fasm/CoreView.lean`.

Generators: no change needed. `Gen/Cells.lean` and `Import/Cells.lean` contain only data, with
no Prelim names. Drift checks pass: `formal/tools/gen/gen.sh --check-json` gives "no drift",
and so does `formal/tools/import/import.sh --check-json`. I did not run the full yosys
`--check`: no JSON or generator changed.

Untouched on purpose: `Net/Prelim.lean` and `Timing/Semantics.lean`. They mention
Cells.Prelim only in comments, and tcheck's `sync.sh --check` requires them byte-identical.

## Now Prelim-free (closure contains no `Formal.Cells.*` except via Core)

`Net.CoreLut`, `Gen.Netlist`, `Gen.Cells`, `Gen.ProofsPrims`, `Net.Import.Netlist`,
`Net.Import.Cells`, `Net.HandshakeMuller`, `PerLink`, `PerLinkPin`, `PerLinkEvent`, `EndToEnd`,
`EndToEndToy`, `EndToEnd2`, `EndToEnd2Toy`, `HandshakeLive`, `HandshakeWitness`, `Muller`,
`MullerRun`, `MullerSI`, `MullerTimed`, `MullerTimedInst`, `MullerTimedCx`.

## Still depending on Prelim, and why (the list for when B ports)

| C module | via B module(s) | B names used | when B lands |
|---|---|---|---|
| `Gen.ProofsCE` | CElemFn, CTree, CElemTiming | `c2B..c3norstB`, `c2K..c3norstK`, `INIT_*`, `cSpec clr set`, CTree `t5 t8 gen*`, CElemTiming consts | `kleeneSemP`→`kleeneSem`; drop PrelimSem import |
| `Gen.ProofsLatch` | Latch, LinkHandshake, Bundling | `bmux ODD PAIR RST0 RST1`, `latK`, `Bundling.BUF/PAIR/ODD/FF_SIDE`, Prelim `K3.mux`, `lutK` | same; `K3.mux`→`kmux`, `lutK`→`kevalL` |
| `Gen.ProofsLink` | CElemFn, Latch, LinkHandshake, Bundling | `ctlB`, `INIT_D*`, `dNext diNext`, `pair_eq lat_eq` (stated on `o5B/o6B/lutB`), `BUF FF_SIDE FR_SIDE` | `rfl` proofs: drop `rw [boolSem_eq_boolSemP]`; B's `pair_eq`/`lat_eq` in Core form |
| `Gen.ProofsCtl` | LibCtlMergeMux | `INIT_steer INIT_or2 req0B req1B req0K req1K or2B or2K selB c2B j0K j1K dmux_pair` (on `o5B/o6B/lutB`) | as ProofsLink |
| `Gen.ProofsArb` | CElemFn, ArbKleene, ArbBinary, ArbHandover, ArbHeldTimed, ArbA0Fork | `g1K g2K qArbK r0K qCellK cK kleene_exclusion *_INIT`, `ArbBinary.stF/stA`, `ArbHandover.stateF`, `ArbHeldTimed.FS/FR/CE` | `kleeneSemP`→`kleeneSem` |
| `Gen.ProofsMisc` | Latch | `bmux ODD PAIR` | none on C's side (Bool only) |
| `Gen.All`, `Gen.PrelimSem` | (the above) / Prelim by design | | delete PrelimSem |
| `Net.Import.Proofs` | CElemFn, Latch, ArbKleene | `cSpec clr set c2B..c4B c2K..c2nsetK`, `bmux PAIR`, `g1K g2K qArbK r0K qCellK cK kleene_exclusion`, Prelim `K3.mux` | `kleeneSemP`→`kleeneSem`; delete Import/PrelimSem |
| `Net.FasmLink.Proofs` | via Import.Proofs | | follows Import.Proofs |
| `Net.Fasm.Basic` (and `CePair*`, `CoreView`, `FasmLink.*`, `Timing.RoutedCePair`) | CElemTiming (`Trace`, `WinDelay`) + Prelim `o6B/o5B` in `PLut.fn` | B's `OnNetlist*` unfold `PLut.fn` to `o5B` | set `PLut.fn := fnCore` once OnNetlist* is ported; `WinDelay`→Core `Substrate.Win` (Iff.rfl, `win_iff_winDelay`); delete CoreView |
| `Net.Fasm.CePair` | CElemTiming | `Loop` theorems, `INIT_c2`; `q1_kleene_s1` (Prelim `lutK`) | keep `q1_kleene_s1_core`, delete the Prelim one |
| `Net.Ring`, `BridgeRing`, `BridgeWire` | CElemFn | `c2nB c2nsetB`, `c2nK c2nsetK`, Prelim `Formal.Cells.K3` (BridgeRing `pos`) | port with B's Core `c2n*K` |
| `Net.CoreLutPrelim` | Prelim, MuxTree | by design | delete |

## Run / check

```
cd formal/lean && export PATH=$HOME/.elan/bin:$PATH && export LEAN_PATH=$PWD/.lake/build/lib/lean
# dependency order (oleans already installed in .lake/build by this probe):
for m in Net/CoreLut Cells/MuxTree Net/CoreLutPrelim Gen/Netlist Gen/Cells Gen/PrelimSem \
  Gen/ProofsCE Gen/ProofsLatch Gen/ProofsLink Gen/ProofsCtl Gen/ProofsArb Gen/ProofsMisc Gen/ProofsPrims Gen/All \
  Net/Import/Netlist Net/Import/Cells Net/Import/PrelimSem Net/Import/Proofs \
  Net/FasmLink/Basic Net/FasmLink/LinkArb Net/FasmLink/Proofs Net/Fasm/CoreView Net/Fasm/CePair \
  Net/HandshakeMuller Net/EndToEnd Net/PerLink Net/PerLinkPin Net/EndToEnd2 Net/EndToEndToy Net/EndToEnd2Toy \
  Net/HandshakeLive Net/HandshakeWitness Net/PerLinkEvent \
  Net/Muller Net/MullerRun Net/MullerSI Net/MullerTimed Net/MullerTimedInst Net/MullerTimedCx; do
  ../slot.sh lean -o .lake/build/lib/lean/Formal/$m.olean Formal/$m.lean; done
```
Everything was compiled in a private copy of `.lake/build` (scratchpad) and then copied in,
so the shared tree was never left half-built. The private copy was compared with the shared
tree before installing: only `Net/OpsMux.olean` had changed upstream meanwhile, and it is
outside these modules' closures. Axiom audit: `collectAxioms` over every declaration of the
38 modules (3055 declarations) found 0 outside {propext, Classical.choice, Quot.sound}, both
in the private tree and after installing. `formal/scan.py` passes on every touched file. `bash formal/tools/fasm2lean/check.sh` prints PASS, including
`q1_kleene_s1_core` depends on axioms: [propext]. The script rebuilt `Fasm/Basic` and
`CePairS1-4` from their unchanged sources.

Costs (loaded machine, other probes running): ProofsPrims 163 s (was 166-181 s), ProofsCE
418 s, ProofsArb 408 s, Import/Proofs 581 s (slot waits included), MullerSI 305 s with a
4.6 GB peak (was 190 s and 6 GB). The first MullerSI attempt was OOM-killed while three
other jobs ran; it passed alone. Core `evalL` under `decide +kernel` costs about the same
as Prelim `lutB`.

## Fidelity

No new primitive model. The LUT semantics is now A's Core model (`Lut.eval`; `Lut.keval`
= H_KLEENE_LUT's mux tree with `merge` on an `X` select, = `kevalSpec`). It is proved
equal to the Prelim model it replaces for every INIT and every pin list
(`lutB_eq_evalL`, `lutK_eq_kevalL`), so every fidelity statement in the C-11a, 11b, 11d,
8a, 8c, 8e, 8g and 8h notes carries over unchanged. One point to record: `o5L`/`o6L` read
pins 0-4 / 0-5 and ignore any further pins, while Prelim's `o6B` reads every pin it is
given. They agree on 6-pin vectors (`o6B_eq_o6L` needs `length = 6`), which is every use.

## For the lead / other shards

- Shard A: `Formal/Core/Bridge.lean` also imports `Formal.Cells.Prelim` (A already plans to
  remove that section). The root `Formal.lean` and lakefile globs should pick up the five
  new modules. `Gen/PrelimSem`, `Import/PrelimSem`, `CoreLutPrelim` and `Fasm/CoreView`
  are meant to be deleted when Prelim is.
- Shard B: when porting `OnNetlist*.lean`, use `Formal.Net.Fasm.PLut.fnCore` /
  `fn_eq_fnCore`; C will then redefine `PLut.fn`.
- Time box: about 2 h of the 3 h. Effort for the remaining swap after B ports: about 1 h of
  renames (the table above), plus recompiling (about 30 min of machine time).
