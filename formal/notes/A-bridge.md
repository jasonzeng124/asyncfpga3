# A-bridge: core unification without editing anything (track 4, shard A)

## Files

- `formal/lean/Formal/Core/Bridge.lean` (proved, 591 lines, core Lean only, about 4 s). It imports
  `Formal.Core.{Kleene, Lut, LutTree, Ternary}` and shard B's `Formal.Cells.{Prelim, MuxTree}`, all read-only.
  Namespace: `Formal.Core.Bridge`.
- There is no Wip file because nothing was left unproved.

Check (from `formal/lean`):

    ../check.sh Formal/Core/Bridge.lean     # [audit] 835 declarations checked, [check] OK

There is no sorry, admit, axiom, native_decide or bv_decide. The audit allows only propext, Classical.choice and Quot.sound.

## Conventions (stated once, used everywhere)

- A Core `Lut k` holds `init : BitVec (2^k)`. Pin `I0 = x 0` is the **LSB** of the address, and `eval x = INIT[Σ x_i 2^i]`.
  Its table as a `Nat` is `N := L.init.toNat`, and `L.entry a = N.testBit a` (`entry_eq_testBit`, which holds by rfl).
- **Ternary**: `kext k (Ternary.initTbl N)` on the same `Fin k` tuple, mapped by `toTern`. `Ternary.addr = Core.addr` (`tern_addr_eq`).
- **LutTree** lists are root first. There are two readings:
  - `lsbList v = [I0,…,I(k-1)]` with the table `t ∘ lsbAddr` (LSB-first). This is the GLS / Core tree order, with I0 at the root.
  - `silList v = (lsbList v).reverse = [I(k-1),…,I0] = [A6,…,A1]` with LutTree's own `initFun N` (MSB-first `addrOf`). This is the silicon order, with A6 at the root.
    `addrOf w = lsbAddr w.reverse` (`addrOf_eq_lsbAddr_reverse`).
- **Cells.Prelim** (shard B) lists are `List.ofFn (toCells ∘ v) = [I0,…]`, the table is `N`, and `lutIdx = lsbAddr` (`lsbAddr_eq_lutIdx`).

## What checks (all in `Formal.Core.Bridge`)

**(1) The K3 equivalences.** Each one is packaged as a `K3Iso` record with both inverse laws:

| local K3 | iso | inverse laws | ofBool | order | glb | Kleene mux |
|---|---|---|---|---|---|---|
| `LutTree.K3` | `isoLT` (`toLT`/`ofLT`) | `ofLT_toLT`, `toLT_ofLT` | `toLT_ofBool` | `toLT_le_iff` | `toLT_merge` (= `kmux X`) | `toLT_cmux` (= `kmux`) |
| `Ternary.K3` | `isoTern` | `ofTern_toTern`, `toTern_ofTern` | `toTern_ofBool` | `toTern_le_iff` | `toTern_merge` (= `meet`) | `toTern_cmux` (= `sel`) |
| `Cells.K3` (f/t/x) | `isoCells` | `ofCells_toCells`, `toCells_ofCells` | `toCells_ofBool` | `toCells_admits` (Prelim has no `⊑`; `admits a b ↔ a ⊑ ofBool b`) | `toCells_merge` (= `join`) | `toCells_cmux` (= `K3.mux`), `toCells_not` |

Core has no named mux, because `kevalT` inlines it. So `Bridge.cmux` is defined, and `kevalT_succ` restates `kevalT` with it.

**(2) The LUT evaluations agree.** This holds for every `k`, every INIT and every K3 vector:

| theorem | statement |
|---|---|
| `tern_kext_eq_kevalT` / `tern_kext_eq_keval` / `tern_kext_eq_kevalSpec` | `kext k (initTbl N) (toTern ∘ v) = toTern (L.keval v) = toTern (L.kevalSpec v)` |
| `lt_evalTree_lsb_eq_kevalT` / `_keval` | `evalTree (lsbList v) (N.testBit ∘ lsbAddr) = toLT (L.keval v)`. This is a structural equality: the trees are the same. |
| `lt_evalTree_sil_eq_keval` | `evalTree (silList v) (initFun N) = toLT (L.keval v)`. The silicon order is proved via `tableEval_reverse`. |
| `lt_tableEval_sil_eq_kevalSpec` | LutTree `tableEval` = Core `kevalSpec` |
| `lt_lut6O6_eq_keval`, `lt_lut6O5_eq_keval` | LutTree `lut6O6 N (v 5) [v 4..v 0]` = `L.keval v`. `lut6O5 N (silList v)` = `L62.o5.keval v`. |
| `cells_muxTree_eq_kevalT` / `_keval`, `cells_lutK_eq_keval` / `_kevalSpec` | B's `muxTree` and `lutK` (H_KLEENE_LUT) = Core |
| `tern_initTbl_eq_eval`, `cells_lutB_eq_eval`, `lsbAddr_ofFn` | the Boolean LUTs agree |
| `lsbList_surj`, `silList_surj` | every LutTree list is covered |

**Supporting lemmas:**
- LutTree `Consistent` and lists: `consistent_append` and `consistent_reverse`.
- Table semantics: `tableEval_ext` (a value is fixed by its "all = b" facts), `tableEval_reverse`, and `lt_evalTree_congr`.
- Addresses: `addrOf_lt`.

**(3) Transfers.**
- `phys_glitch_free_of_core`: wire a LutTree `PhysTree k` to a Core LUT in silicon order and assume `H_sram` and `H_mux_kleene`. Then any Core fact
  `L.keval v = ofBool c` gives "output = c at every instant, for all delays".
- `phys_sic_of_core`: the INIT side condition of the physical SIC glitch-freedom is discharged by **Core's
  `Lut.no_static_hazard_single`**. The only hypothesis left is the Boolean one `L.eval (flip j) = L.eval x`.
- `phys_hull_of_core`: the multi-input version, via `keval_hull_eq_ofBool_iff` (subcube condition).
- `phys_bd_c2_contain`: the physical C-element `bd_c2` with feedback pin `q` arbitrary, `a = b` steady and `rst = 0` outputs `a` at every
  instant. It comes from `Init.bd_c2_contain`.
- `tern_bdc2_F_eq_core`: Ternary's `bdc2Net` (a LUT4 with table `0x00E8`) is Core's `Init.bd_c2` (a LUT6 with `I4 = I5 = 0`) in Kleene
  semantics, for every ternary input and state. `bdc2_lut4_eq_lut6` checks 81 cases by `decide`.
  `tern_bdc2_fb_eq_core` is the Boolean form. `core_bdc2_no_static_hazard` is Ternary's theorem with the stability
  hypothesis stated on `Core.Init.bd_c2.eval`.

## What does not check / not attempted

- I did not translate Ternary's algorithm-B result `rB` (in `core_bdc2_no_static_hazard`'s `hsame`) into Core terms. It is a
  fixed-point over a network, not a single-LUT fact. `Ternary.bdc2_single_input_ok` decides it.
- `kext` is related to Core only for tables of the form `t ∘ addr`, which covers every LUT. An arbitrary `f : (Fin k → Bool) → Bool`
  is a LUT too, but constructing its `BitVec` INIT was not needed.
- The Cells `Tree`/`build` arbitrary-order results (MuxTree part 2) are not bridged. They already equal `lutK`, which is bridged.

## Verdict

**Works.** The bridge took about 1 hour. All four copies of K3 and all five Kleene LUT evaluators are proved equal, in both tree
orders. Combined with LutTree's physical model, every Core Kleene fact about a library INIT becomes a timed statement about any delay
assignment.

## Recommendation: canonical API

- **Canonical:** `Formal.Core.K3` (Kleene.lean) and `Formal.Core.Lut` (`Lut k`, `Lut62`, `eval`, `keval`, `kevalSpec`, `Init.*`).
  New files state results in these terms, and the pin order is I0 = LSB on `Fin k` tuples.
- **Keep, reach through Bridge:** `LutTree` (timed physical tree, silicon order), `Ternary` (network soundness, `Causal`), and
  shard B's `Prelim`/`MuxTree`. Editing them is unnecessary. A file that needs both sides imports `Formal.Core.Bridge` and rewrites with the
  theorems above. If a later cleanup wants one `K3`, the isos show a rename is semantics-preserving. The lowest-cost first step is
  Ternary: its `Net` interface (`mono`, `ext`) is exactly `Lut.keval_mono` and `keval_ofBoolVec`.
- Recommended pattern for cell proofs (shard B): compute with Core `keval` by `decide`, then transfer:
  - use `phys_glitch_free_of_core` for timed glitch freedom;
  - use `cells_lutK_eq_keval` to reuse existing `lutK` proofs.
- Bridge imports `Formal.Cells.Prelim` and `MuxTree`, so Core now depends on shard B for this one file. If shard B's Prelim is ever
  deleted or replaced by Core, delete the `Cells` section (§1 Cells and §2 Cells.Prelim) and nothing else breaks.

## Fidelity

Bridge adds no modelling assumptions. All of its theorems are equalities between models. The physical transfers carry LutTree's
explicit hypotheses `H_sram` and `H_mux_kleene` unchanged (see A-lut-tree.md for the tests, a board counter on a pin whose cofactors are
equal). Bridge also adds `hinit`: the SRAM holds the INIT in silicon order, with A6 at the root and `initFun`. This is
the UG474 INIT convention, and the Kleene results do not depend on the tree order (`lt_evalTree_lsb_eq_keval` vs `_sil_`). Tree order
matters only for path delays, which these theorems do not use.

## What it buys

- One semantic object behind every LUT claim in the project.
- Shard B's H_KLEENE_LUT closure semantics, Core's `keval`, the Ternary network model and the LutTree silicon tree are proved
  identical. So a cell fact proved in any of them is usable in all of them.
- Core's cheap `decide` facts about INIT constants become physical, all-delays glitch freedom (`phys_*`).
