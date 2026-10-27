# A-lutlist: moving Prelim's list-based LUT API into Core (probe LutList)

Shard A, probe LutList. Goal: make `Formal/Cells/Prelim.lean` deletable
(PROGRAM.md Phase 1; JOURNAL-B progress 08:16; notes/B-port-core.md "What
remains to delete Prelim").

## 1. What was written

| file | status | content |
|---|---|---|
| `Formal/Core/LutList.lean` | claimed (A) | Prelim's whole API, same names and bodies, namespace `Formal.Core.LutList`; imports only `Core.Kleene`, `Core.Lut` |
| `Formal/Core/Bridge.lean` | claimed (A) | imports `Core.LutList` instead of `Cells.Prelim` + `Cells.MuxTree` |
| `Wip/LutList/PrelimEq.lean` | not claimed | each LutList name = its Prelim namesake (imports Prelim) |
| `Wip/LutList/trial/*.lean` | not claimed | C's four files with the switch applied (module names `Wip.LutList.trial.*`) |

`Formal.Core.LutList` provides: `K3` (= `abbrev` of `Formal.Core.K3`),
`K3.f/t/x` (`@[match_pattern, reducible]` names for `zero/one/X`),
`K3.ofBool` (abbrev of Core's), `K3.join`, `join_eq_merge`, `K3.mux`,
`K3.not`, `not_eq_core`, `K3.admits`, `admits_iff_le`, `lutIdx`, `lutB`,
`completions`, `muxTree`, `lutK`, `o6B o5B o6K o5K`, and the Core agreement
lemmas `mux_eq lutIdx_ofFn entry_eq_testBit lutB_ofFn muxTree_ofFn
muxTree_congr lutK_ofFn lutK_ofFn_spec`. New: `muxTree_eq_lutK` (`rfl`, the
same statement as `Formal.Cells.MuxTree.muxTree_eq_lutK`), so that importers
that only needed MuxTree for that lemma (Bridge, C's CoreLutPrelim) drop the
MuxTree import too.

Plain-language statement. Assumed: nothing beyond Core's definitions
(`Lut.eval`, `Lut.keval`, `kevalT`); the physical reading of `lutK` is
H_KLEENE_LUT exactly as for Core's `Lut.keval`. Proved: on `List.ofFn` of a
`Fin k` vector, `lutB` = `Lut.eval`, `muxTree g` = `kevalT k g`, `lutK` =
`Lut.keval` = `Lut.kevalSpec`. Not covered: lists whose length is not the
LUT width (the functions are total, the agreement theorems are for
`List.ofFn`), silicon pin order (that is Bridge §2), timing.

`Wip/LutList/PrelimEq.lean` proves `Formal.Core.LutList.X = Formal.Cells.X`
for every X above (functions, as equalities of constants): `rfl` for the
non-recursive ones; `lutIdx`, `completions`, `muxTree` by `funext` + list
induction (elaborator `rfl` does not unfold the structural recursion of two
distinct constants), the others by rewriting with those. So a switch from
`Formal.Cells.X` to `Formal.Core.LutList.X` changes no statement's meaning.

## 2. A's Core/Bridge.lean (done)

Import lines `import Formal.Cells.Prelim` + `import Formal.Cells.MuxTree`
replaced by `import Formal.Core.LutList`; every `Formal.Cells.X` replaced by
`Formal.Core.LutList.X`, `Formal.Cells.MuxTree.muxTree_eq_lutK` by
`Formal.Core.LutList.muxTree_eq_lutK`; doc text adjusted. No proof changed.
CAVEAT, for the lead: the statement TEXT of these declarations changed in
the namespace prefix of the constants they mention (`BK`, `toCells_ofBool`,
`toCells_admits`, `toCells_merge`, `toCells_cmux`, `toCells_not`,
`lsbAddr_eq_lutIdx`, `cells_muxTree_eq_kevalT`, `cells_muxTree_eq_keval`,
`cells_lutK_eq_keval`, `cells_lutK_eq_kevalSpec`, `cells_lutB_eq_eval`).
They now mention `Formal.Core.LutList.lutK` etc. instead of
`Formal.Cells.lutK`, which are different constants, proved equal in
PrelimEq. Their meaning is unchanged, but strictly the statements name
different constants. No other module imports `Formal.Core.Bridge`. If the
lead's rule is that statements must be identical even in this sense, revert
Bridge to HEAD (`git show HEAD:formal/lean/Formal/Core/Bridge.lean`); it
then still needs Prelim, and Prelim cannot be deleted while it does.
Bridge's closure is now Prelim-free:
`Kleene Lut LutList LutTree Ternary Bridge`.

## 3. Patches for shard C (exact)

Rule for each file: the import line, and in CODE (not doc comments)
`Formal.Cells.X` -> `Formal.Core.LutList.X` for X in the API above,
`Formal.Cells.MuxTree.muxTree_eq_lutK` -> `Formal.Core.LutList.muxTree_eq_lutK`.
Fasm/Basic additionally qualifies `o6B`/`o5B`: it does `open Formal.Cells`
and still imports B's `CElemTiming` (for `Trace`/`WinDelay`), which still
brings Prelim in until B switches, so an unqualified `o6B` would keep
meaning `Formal.Cells.o6B` (and `open Formal.Core.LutList` next to
`open Formal.Cells` would make it ambiguous). Gen/PrelimSem and
Import/PrelimSem keep `import Formal.Net.CoreLutPrelim` (unchanged); only
names change. No downstream file of C needs a change (section 4).

DIFF_C

## 4. Checks

TRIALS

## 5. Shard B: recipe (not applied; for B to do)

RECIPE_B

## 6. Order of deletion

1. Commit `Core/LutList.lean`, `Core/Bridge.lean` (A, done here).
2. C applies section 3 (independent of B: works with Prelim still present).
3. B applies section 5 to all Cells files and deletes `Cells/Prelim.lean`
   (and then `Cells/MuxTree.muxTree_eq_lutK` may stay or alias LutList's).
4. Optional, later: C's porting aids (`Net/CoreLutPrelim`, `Gen/PrelimSem`,
   `Net/Import/PrelimSem`) are now about `LutList.K3` = `Core.K3`, so `toP`
   is the identity and `kleeneSemP` could be replaced by `kleeneSem`; that
   is C's call, not needed for the deletion.

Lakefile / root import: none needed (`Formal/Core/LutList.lean` is under
`Formal/`, picked up by the `Formal.+` glob; add `import Formal.Core.LutList`
to `Formal.lean` if the root lists Core modules explicitly).
