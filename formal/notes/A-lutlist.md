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
names change.

COUPLING (found by the checks, section 4): the C switch is NOT independent of
B. (a) `Net/Fasm/CoreView` rewrites `PLut.fn` (Fasm/Basic) with
`o6B_eq_o6L` (CoreLutPrelim), so CoreLutPrelim and Fasm/Basic must switch
together. (b) B's `Cells/OnNetlist` unfolds `PLut.fn` and then rewrites with
`Formal.Cells.o6B`, so Fasm/Basic and B's Cells switch must land together.
(c) Once Prelim is gone, every C file that reaches Prelim's names through
`open Formal.Cells` (Gen/Proofs*, Net/BridgeRing, Net/Ring, Net/Fasm/CePair,
Net/FasmLink/Basic, Net/Import/Proofs, Timing/GrantFork, Timing/RuntAck)
needs `Formal.Core.LutList` added to that `open` (step 2 below). So: ONE
commit with A (done) + C step 1 + C step 2 + B's section 5, then delete
Prelim. (Step 1 alone, with B unchanged, breaks only OnNetlist ->
TernaryOnBits -> TernaryOnBits2; see section 4.)

### Step 1: the four direct importers (`Wip/LutList/C-step1.diff`, script `Wip/LutList/switch_C.py`)

```diff
--- a/formal/lean/Formal/Net/CoreLutPrelim.lean
+++ b/formal/lean/Formal/Net/CoreLutPrelim.lean
@@ -1,6 +1,5 @@
 import Formal.Net.CoreLut
-import Formal.Cells.Prelim
-import Formal.Cells.MuxTree
+import Formal.Core.LutList
 
 /-!
 # Probe 11e: shard C's Core LUT view = shard B's `Formal.Cells.Prelim`
@@ -26,7 +25,7 @@
 open Formal.Net.CoreLut
 
 abbrev CK := Formal.Core.K3
-abbrev PK := Formal.Cells.K3
+abbrev PK := Formal.Core.LutList.K3
 
 def toP : CK → PK
   | .zero => .f
@@ -41,46 +40,46 @@
 @[simp] theorem toP_ofP (a : PK) : toP (ofP a) = a := by cases a <;> rfl
 @[simp] theorem ofP_toP (a : CK) : ofP (toP a) = a := by cases a <;> rfl
 
-@[simp] theorem toP_ofBool (b : Bool) : toP (Formal.Core.K3.ofBool b) = Formal.Cells.K3.ofBool b := by
+@[simp] theorem toP_ofBool (b : Bool) : toP (Formal.Core.K3.ofBool b) = Formal.Core.LutList.K3.ofBool b := by
   cases b <;> rfl
 
-theorem toP_merge (a b : CK) : toP (Formal.Core.K3.merge a b) = Formal.Cells.K3.join (toP a) (toP b) := by
+theorem toP_merge (a b : CK) : toP (Formal.Core.K3.merge a b) = Formal.Core.LutList.K3.join (toP a) (toP b) := by
   cases a <;> cases b <;> rfl
 
-theorem toP_kmux (s a b : CK) : toP (kmux s a b) = Formal.Cells.K3.mux (toP s) (toP a) (toP b) := by
+theorem toP_kmux (s a b : CK) : toP (kmux s a b) = Formal.Core.LutList.K3.mux (toP s) (toP a) (toP b) := by
   cases s <;> cases a <;> cases b <;> rfl
 
-theorem lutIdx_eq_lsbIdx : ∀ w : List Bool, Formal.Cells.lutIdx w = lsbIdx w
+theorem lutIdx_eq_lsbIdx : ∀ w : List Bool, Formal.Core.LutList.lutIdx w = lsbIdx w
   | [] => rfl
-  | b :: w => by cases b <;> simp [Formal.Cells.lutIdx, lsbIdx, lutIdx_eq_lsbIdx w]
+  | b :: w => by cases b <;> simp [Formal.Core.LutList.lutIdx, lsbIdx, lutIdx_eq_lsbIdx w]
 
 /-- **Boolean: Prelim's `lutB` is Core's `Lut.eval`.** -/
-theorem lutB_eq_evalL (init : Nat) (ins : List Bool) : Formal.Cells.lutB init ins = evalL init ins := by
-  rw [evalL_eq_testBit, Formal.Cells.lutB, lutIdx_eq_lsbIdx]
+theorem lutB_eq_evalL (init : Nat) (ins : List Bool) : Formal.Core.LutList.lutB init ins = evalL init ins := by
+  rw [evalL_eq_testBit, Formal.Core.LutList.lutB, lutIdx_eq_lsbIdx]
 
 theorem o6B_eq_o6L (init : Nat) (ins : List Bool) (h : ins.length = 6) :
-    Formal.Cells.o6B init ins = o6L init ins := by
-  rw [o6L_eq_evalL _ _ h, Formal.Cells.o6B, lutB_eq_evalL]
+    Formal.Core.LutList.o6B init ins = o6L init ins := by
+  rw [o6L_eq_evalL _ _ h, Formal.Core.LutList.o6B, lutB_eq_evalL]
 
 theorem o5B_eq_o5L (init : Nat) (ins : List Bool) (h : ins.length = 6) :
-    Formal.Cells.o5B init ins = o5L init ins := by
-  rw [o5L_eq_evalL _ _ h, Formal.Cells.o5B, lutB_eq_evalL]
+    Formal.Core.LutList.o5B init ins = o5L init ins := by
+  rw [o5L_eq_evalL _ _ h, Formal.Core.LutList.o5B, lutB_eq_evalL]
 
 theorem muxTree_eq_kevalTL : ∀ (t : Nat → Bool) (ins : List CK),
-    Formal.Cells.muxTree t (ins.map toP) = toP (kevalTL t ins)
-  | t, [] => by simp [Formal.Cells.muxTree, kevalTL_nil]
+    Formal.Core.LutList.muxTree t (ins.map toP) = toP (kevalTL t ins)
+  | t, [] => by simp [Formal.Core.LutList.muxTree, kevalTL_nil]
   | t, a :: as => by
       rw [kevalTL_cons, toP_kmux, ← muxTree_eq_kevalTL _ as, ← muxTree_eq_kevalTL _ as]
       rfl
 
 /-- **Kleene (H_KLEENE_LUT): Prelim's closure `lutK` is Core's `Lut.keval`.** -/
 theorem lutK_eq_kevalL (init : Nat) (ins : List CK) :
-    Formal.Cells.lutK init (ins.map toP) = toP (kevalL init ins) := by
-  rw [← Formal.Cells.MuxTree.muxTree_eq_lutK, muxTree_eq_kevalTL, kevalL_eq_kevalTL]
+    Formal.Core.LutList.lutK init (ins.map toP) = toP (kevalL init ins) := by
+  rw [← Formal.Core.LutList.muxTree_eq_lutK, muxTree_eq_kevalTL, kevalL_eq_kevalTL]
 
 /-- The same, for a Prelim pin list. -/
 theorem lutK_eq_kevalL' (init : Nat) (ins : List PK) :
-    Formal.Cells.lutK init ins = toP (kevalL init (ins.map ofP)) := by
+    Formal.Core.LutList.lutK init ins = toP (kevalL init (ins.map ofP)) := by
   rw [← lutK_eq_kevalL, List.map_map]
   congr 1
   conv => lhs; rw [← List.map_id ins]
--- a/formal/lean/Formal/Net/Fasm/Basic.lean
+++ b/formal/lean/Formal/Net/Fasm/Basic.lean
@@ -1,4 +1,4 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
 import Formal.Cells.CElemTiming
 
 /-!
@@ -51,8 +51,8 @@
 /-- LUT function of a physical pin vector `[A1..A6]`: O6 = INIT[A6..A1],
 O5 = INIT[31:0][A5..A1] (7-series LUT6_2). -/
 def PLut.fn (L : PLut) : LOut → List Bool → Bool
-  | .o6, v => o6B L.init v
-  | .o5, v => o5B L.init v
+  | .o6, v => Formal.Core.LutList.o6B L.init v
+  | .o5, v => Formal.Core.LutList.o5B L.init v
 
 def Src.val (ins : List Bool) (st : Nat → LOut → Bool) : Src → Bool
   | .const v => v
--- a/formal/lean/Formal/Gen/PrelimSem.lean
+++ b/formal/lean/Formal/Gen/PrelimSem.lean
@@ -26,19 +26,19 @@
 open Formal.Net.CoreLut Formal.Net.CoreLutPrelim
 
 /-- Decidability of `∀` over Prelim's `K3` (Prelim has none). -/
-instance K3.decForall {P : Formal.Cells.K3 → Prop} [DecidablePred P] : Decidable (∀ k, P k) :=
+instance K3.decForall {P : Formal.Core.LutList.K3 → Prop} [DecidablePred P] : Decidable (∀ k, P k) :=
   if h : P .f ∧ P .t ∧ P .x then
     isTrue (fun k => by cases k <;> simp_all)
   else
     isFalse (fun H => h ⟨H _, H _, H _⟩)
 
 /-- Kleene reading with shard B's Prelim `lutK` (pre-port `kleeneSem`). -/
-def kleeneSemP : Sem Formal.Cells.K3 := ⟨Formal.Cells.lutK, Formal.Cells.K3.ofBool⟩
+def kleeneSemP : Sem Formal.Core.LutList.K3 := ⟨Formal.Core.LutList.lutK, Formal.Core.LutList.K3.ofBool⟩
 
 /-- Binary reading with Prelim's `lutB`. It IS `boolSem` (`boolSem_eq_boolSemP`,
 `Bool` is shared), so a theorem about one is a theorem about the other; it is
 only here so that proofs by `rfl` against B's `lutB`-valued lemmas keep working. -/
-def boolSemP : Sem Bool := ⟨Formal.Cells.lutB, id⟩
+def boolSemP : Sem Bool := ⟨Formal.Core.LutList.lutB, id⟩
 
 theorem boolSem_eq_boolSemP : boolSem = boolSemP := by
   unfold boolSem boolSemP
@@ -55,16 +55,16 @@
 
 /-- `prim_tables` in Prelim's `lutB`, from the Core statement. -/
 theorem prim_tables_prelim :
-    (∀ a b s : Bool, Formal.Cells.lutB MUX_INIT [a, b, s] = (if s then b else a)) ∧
-    (∀ a b : Bool, Formal.Cells.lutB OR2_INIT [a, b] = (a || b)) ∧
-    (∀ a : Bool, Formal.Cells.lutB NOT_INIT [a] = !a) ∧
-    (∀ a b : Bool, Formal.Cells.lutB XOR2_INIT [a, b] = (a ^^ b)) := by
+    (∀ a b s : Bool, Formal.Core.LutList.lutB MUX_INIT [a, b, s] = (if s then b else a)) ∧
+    (∀ a b : Bool, Formal.Core.LutList.lutB OR2_INIT [a, b] = (a || b)) ∧
+    (∀ a : Bool, Formal.Core.LutList.lutB NOT_INIT [a] = !a) ∧
+    (∀ a b : Bool, Formal.Core.LutList.lutB XOR2_INIT [a, b] = (a ^^ b)) := by
   simp only [lutB_eq_evalL]
   exact ⟨prim_tables.1, prim_tables.2.1, prim_tables.2.2.1, prim_tables.2.2.2.1⟩
 
 /-- `mux_kleene` in Prelim's terms (`lutK`, `K3.mux`), from the Core statement. -/
-theorem mux_kleene_prelim : ∀ a b s : Formal.Cells.K3,
-    Formal.Cells.lutK MUX_INIT [a, b, s] = Formal.Cells.K3.mux s a b := by
+theorem mux_kleene_prelim : ∀ a b s : Formal.Core.LutList.K3,
+    Formal.Core.LutList.lutK MUX_INIT [a, b, s] = Formal.Core.LutList.K3.mux s a b := by
   intro a b s
   have h := lutK_eq_kevalL MUX_INIT [ofP a, ofP b, ofP s]
   simp only [List.map, toP_ofP] at h
@@ -72,11 +72,11 @@
   simp
 
 /-- Pre-port form of `ProofsPrims.prims_muxf_kleene` (Prelim `K3`, `K3.mux`). -/
-theorem prims_muxf_kleene_prelim : ∀ a b s : Formal.Cells.K3,
+theorem prims_muxf_kleene_prelim : ∀ a b s : Formal.Core.LutList.K3,
     Cells.prims_muxf8.gateN kleeneSemP "u0" .O [("l[0]", a), ("l[1]", b), ("sel[0]", s)] =
-        some (Formal.Cells.K3.mux s a b) ∧
+        some (Formal.Core.LutList.K3.mux s a b) ∧
     Cells.prims_muxf8.gateN kleeneSemP "u2" .O [("m0", a), ("m1", b), ("sel[1]", s)] =
-        some (Formal.Cells.K3.mux s a b) := by
+        some (Formal.Core.LutList.K3.mux s a b) := by
   decide +kernel
 
 end Formal.Gen
--- a/formal/lean/Formal/Net/Import/PrelimSem.lean
+++ b/formal/lean/Formal/Net/Import/PrelimSem.lean
@@ -18,12 +18,12 @@
 open Formal.Net.CoreLut Formal.Net.CoreLutPrelim
 
 /-- Kleene reading with shard B's Prelim `lutK` (pre-port `kleeneSem`). -/
-def kleeneSemP : Sem Formal.Cells.K3 := ⟨Formal.Cells.lutK, Formal.Cells.K3.ofBool⟩
+def kleeneSemP : Sem Formal.Core.LutList.K3 := ⟨Formal.Core.LutList.lutK, Formal.Core.LutList.K3.ofBool⟩
 
 /-- Binary reading with Prelim's `lutB`. It IS `boolSem` (`boolSem_eq_boolSemP`,
 `Bool` is shared), so a theorem about one is a theorem about the other; it is
 only here so that proofs by `rfl` against B's `lutB`-valued lemmas keep working. -/
-def boolSemP : Sem Bool := ⟨Formal.Cells.lutB, id⟩
+def boolSemP : Sem Bool := ⟨Formal.Core.LutList.lutB, id⟩
 
 theorem boolSem_eq_boolSemP : boolSem = boolSemP := by
   unfold boolSem boolSemP
```

### Step 2: files that use Prelim names via `open Formal.Cells` (`Wip/LutList/C-step2.diff`, script `Wip/LutList/switch_other.py`)

Rule: in each `open ...` line that opens the namespace `Formal.Cells`
(not a selective `open Formal.Cells (..)`), add `Formal.Core.LutList` after
it; qualify any remaining `Formal.Cells.<API name>` as
`Formal.Core.LutList.<name>` (Net/BridgeRing has three). Diff against the
10:55 snapshot of the tree:

```diff
--- a/formal/lean/Formal/Gen/ProofsArb.lean
+++ b/formal/lean/Formal/Gen/ProofsArb.lean
@@ -29 +29 @@
-open Formal.Cells Formal.Gen Formal.Gen.Cells
+open Formal.Cells Formal.Core.LutList Formal.Gen Formal.Gen.Cells
--- a/formal/lean/Formal/Gen/ProofsCE.lean
+++ b/formal/lean/Formal/Gen/ProofsCE.lean
@@ -33 +33 @@
-open Formal.Cells Formal.Gen Formal.Gen.Cells
+open Formal.Cells Formal.Core.LutList Formal.Gen Formal.Gen.Cells
--- a/formal/lean/Formal/Gen/ProofsCtl.lean
+++ b/formal/lean/Formal/Gen/ProofsCtl.lean
@@ -19 +19 @@
-open Formal.Cells Formal.Gen Formal.Gen.Cells
+open Formal.Cells Formal.Core.LutList Formal.Gen Formal.Gen.Cells
--- a/formal/lean/Formal/Gen/ProofsLatch.lean
+++ b/formal/lean/Formal/Gen/ProofsLatch.lean
@@ -29 +29 @@
-open Formal.Cells Formal.Gen Formal.Gen.Cells
+open Formal.Cells Formal.Core.LutList Formal.Gen Formal.Gen.Cells
--- a/formal/lean/Formal/Gen/ProofsLink.lean
+++ b/formal/lean/Formal/Gen/ProofsLink.lean
@@ -24 +24 @@
-open Formal.Cells Formal.Gen Formal.Gen.Cells
+open Formal.Cells Formal.Core.LutList Formal.Gen Formal.Gen.Cells
--- a/formal/lean/Formal/Gen/ProofsMisc.lean
+++ b/formal/lean/Formal/Gen/ProofsMisc.lean
@@ -21 +21 @@
-open Formal.Cells Formal.Gen Formal.Gen.Cells
+open Formal.Cells Formal.Core.LutList Formal.Gen Formal.Gen.Cells
--- a/formal/lean/Formal/Net/BridgeRing.lean
+++ b/formal/lean/Formal/Net/BridgeRing.lean
@@ -191 +191 @@
-open Formal.Cells in
+open Formal.Cells Formal.Core.LutList in
@@ -193,2 +193,2 @@
-def pos (v : Bool) : Nat → Formal.Cells.K3
-  | 0 => Formal.Cells.K3.ofBool v
+def pos (v : Bool) : Nat → Formal.Core.LutList.K3
+  | 0 => Formal.Core.LutList.K3.ofBool v
@@ -196 +196 @@
-  | _ => Formal.Cells.K3.ofBool (!v)
+  | _ => Formal.Core.LutList.K3.ofBool (!v)
@@ -198 +198 @@
-open Formal.Cells Formal.Cells.CElemFn in
+open Formal.Cells Formal.Core.LutList Formal.Cells.CElemFn in
@@ -212 +212 @@
-open Formal.Cells Formal.Cells.CElemFn in
+open Formal.Cells Formal.Core.LutList Formal.Cells.CElemFn in
--- a/formal/lean/Formal/Net/Fasm/CePair.lean
+++ b/formal/lean/Formal/Net/Fasm/CePair.lean
@@ -43 +43 @@
-open Formal.Net.Fasm Formal.Cells Formal.Cells.CElemTiming
+open Formal.Net.Fasm Formal.Cells Formal.Core.LutList Formal.Cells.CElemTiming
--- a/formal/lean/Formal/Net/FasmLink/Basic.lean
+++ b/formal/lean/Formal/Net/FasmLink/Basic.lean
@@ -59 +59 @@
-open Formal.Cells
+open Formal.Cells Formal.Core.LutList
--- a/formal/lean/Formal/Net/Import/Proofs.lean
+++ b/formal/lean/Formal/Net/Import/Proofs.lean
@@ -41 +41 @@
-open Formal.Cells Formal.Net.Import Formal.Net.Import.Gen
+open Formal.Cells Formal.Core.LutList Formal.Net.Import Formal.Net.Import.Gen
--- a/formal/lean/Formal/Net/Ring.lean
+++ b/formal/lean/Formal/Net/Ring.lean
@@ -56 +56 @@
-open Formal.Cells Formal.Cells.CElemFn
+open Formal.Cells Formal.Core.LutList Formal.Cells.CElemFn
--- a/formal/lean/Formal/Timing/GrantFork.lean
+++ b/formal/lean/Formal/Timing/GrantFork.lean
@@ -55 +55 @@
-open Formal.Cells Formal.Cells.ArbBinary
+open Formal.Cells Formal.Core.LutList Formal.Cells.ArbBinary
--- a/formal/lean/Formal/Timing/RuntAck.lean
+++ b/formal/lean/Formal/Timing/RuntAck.lean
@@ -61 +61 @@
-open Formal.Cells Formal.Cells.ArbBinary Formal.Timing.GrantFork
+open Formal.Cells Formal.Core.LutList Formal.Cells.ArbBinary Formal.Timing.GrantFork
--- a/formal/lean/Formal/Net/Fasm/Basic.lean
+++ b/formal/lean/Formal/Net/Fasm/Basic.lean
@@ -29 +29 @@
-open Formal.Cells Formal.Cells.CElemTiming
+open Formal.Cells Formal.Core.LutList Formal.Cells.CElemTiming
```

## 4. Checks

All compiles below: plain `lean -DautoImplicit=false FILE -o OUT/..olean`
through `formal/slot.sh`, with `LEAN_PATH=OUT` a private olean dir in the
scratchpad (`.lake/build` did not exist: Mathlib was still building), in
topological order, every module recompiled; this is equivalent to `lake env
lean` on these Mathlib-free modules. Scripts: scratchpad `lutlist/comp.sh`,
`keepgoing.sh` (continue past failures, skip dependents).

1. Claimed files: `formal/check.sh Formal/Core/Kleene.lean Formal/Core/Lut.lean
   Formal/Core/LutList.lean Formal/Core/LutTree.lean Formal/Core/Ternary.lean
   Formal/Core/Bridge.lean` -> `[audit] 738 declarations checked`,
   `[check] OK` (Bridge's closure no longer contains Prelim or MuxTree).
2. `Wip/LutList/PrelimEq.lean`: compiles (rc=0), no sorry.
3. Trials in `Wip/LutList/trial/` (C's four files, step 1, module names
   `Wip.LutList.trial.{CoreLutPrelim,FasmBasic,GenPrelimSem,ImportPrelimSem}`;
   the PrelimSem trials import the trial CoreLutPrelim): all four rc=0.
   CoreLutPrelim, GenPrelimSem, ImportPrelimSem have Prelim-free closures;
   FasmBasic still gets Prelim through B's `CElemTiming` until B switches.
4. Transitional state (A + C step 1, B unchanged; tree snapshot 10:55 UTC):
   the 75-module closure of everything downstream of the changed files:
   72 rc=0; `Cells.OnNetlist` FAILS (it unfolds `PLut.fn` to
   `Formal.Cells.o6B`, now `LutList.o6B`), `TernaryOnBits`, `TernaryOnBits2`
   skipped as its dependents. With Fasm/Basic left unswitched instead,
   `Net.Fasm.CoreView` fails (coupling (a)). Hence the one-commit plan.
5. END STATE (A + C steps 1-2 + B section 5, `Cells/Prelim.lean` DELETED;
   snapshot 10:55, with `Cells/RigContract.lean` taken from HEAD 807448a
   because the snapshot caught it mid-edit, an error unrelated to LutList):
   all 189 modules that depend on `Formal.Core.LutList` and do not need
   Mathlib compile, rc=0, including every Cells file, Bridge, Gen.All,
   Net.Import.Proofs, Net.FasmLink.Proofs, the Capstone and Timing modules.
   NOT CHECKED (need Mathlib, not built yet): `Cells.ArbAnalog`,
   `ArbAnalog2`, `CElemCore`, `CElemInvolution`, `ArbInvolution`,
   `ArbInvolution2`, `Core.Delay.{Involution,Pure,Inertial,Corner}`,
   `Core.Discretize`, `Core.Substrate{,.Real,.CornerNat}`, `Core.Fidelity`,
   `Core.TernaryChannels`. Risk: `CElemCore` has `open Formal.Core` and,
   after the patch, `open Formal.Core.LutList`, so an unqualified `K3` there
   would be ambiguous; grep finds Prelim names in CElemCore only in a
   comment, so I expect it to pass, but it is unverified.
6. B's files moved on after the snapshot (new files CElemStrict, ForkData,
   LibGapMux, LibGapSteer, OnGcdArb, RigIdx, SelfAuditB*, WinFifo, and
   edits). The diffs below are against the snapshot; re-run the scripts on
   the live tree rather than applying the diffs blindly.

## 5. Shard B: recipe (not applied; for B to do)

Rules (script `Wip/LutList/switch_B.py ROOT`, run on a copy; it also
deletes `Cells/Prelim.lean`), for every `Formal/Cells/*.lean`:

1. `import Formal.Cells.Prelim` -> `import Formal.Core.LutList` (27 files).
2. After EVERY line `namespace Formal.Cells...` insert
   `open Formal.Core.LutList` (opens are scoped to the namespace block and
   several files reopen it; an unneeded open is harmless).
3. `Formal.Cells.<API name>` -> `Formal.Core.LutList.<API name>` for the
   names of section 1, which also turns `open Formal.Cells.K3` into
   `open Formal.Core.LutList.K3` (ArbKleene, others).
4. Delete `Cells/Prelim.lean`. `MuxTree.muxTree_eq_lutK` may stay (it is
   now about LutList's constants) or be replaced by
   `Formal.Core.LutList.muxTree_eq_lutK`.

No proof or statement text changes besides those. Result: section 4 item 5.
Full per-file diff (against the 10:55 snapshot; `Wip/LutList/B.diff`):

<details><summary>B.diff (85 files)</summary>

```diff
--- a/formal/lean/Formal/Cells/AMerge2.lean
+++ b/formal/lean/Formal/Cells/AMerge2.lean
@@ -54,0 +55 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/AMerge2Proof.lean
+++ b/formal/lean/Formal/Cells/AMerge2Proof.lean
@@ -9,0 +10 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/AMerge3.lean
+++ b/formal/lean/Formal/Cells/AMerge3.lean
@@ -44,0 +45 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/AMerge3Proof.lean
+++ b/formal/lean/Formal/Cells/AMerge3Proof.lean
@@ -15,0 +16 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/AMergeGates.lean
+++ b/formal/lean/Formal/Cells/AMergeGates.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -54,0 +55 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/AMergeSys.lean
+++ b/formal/lean/Formal/Cells/AMergeSys.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -32,0 +33 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/AMergeTimed.lean
+++ b/formal/lean/Formal/Cells/AMergeTimed.lean
@@ -43,0 +44 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/AMergeTimedC.lean
+++ b/formal/lean/Formal/Cells/AMergeTimedC.lean
@@ -27,0 +28 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/AMergeTimedW.lean
+++ b/formal/lean/Formal/Cells/AMergeTimedW.lean
@@ -22,0 +23 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ArbA0Fork.lean
+++ b/formal/lean/Formal/Cells/ArbA0Fork.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -78,0 +79 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ArbAnalog.lean
+++ b/formal/lean/Formal/Cells/ArbAnalog.lean
@@ -5 +5 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -51,0 +52 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ArbAnalog2.lean
+++ b/formal/lean/Formal/Cells/ArbAnalog2.lean
@@ -34,0 +35 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ArbBinary.lean
+++ b/formal/lean/Formal/Cells/ArbBinary.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -33,0 +34 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ArbCorners.lean
+++ b/formal/lean/Formal/Cells/ArbCorners.lean
@@ -41,0 +42 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ArbCornersPin.lean
+++ b/formal/lean/Formal/Cells/ArbCornersPin.lean
@@ -39,0 +40 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ArbHandover.lean
+++ b/formal/lean/Formal/Cells/ArbHandover.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -69,0 +70 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ArbHeldTimed.lean
+++ b/formal/lean/Formal/Cells/ArbHeldTimed.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -58,0 +59 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ArbHeldTimed2.lean
+++ b/formal/lean/Formal/Cells/ArbHeldTimed2.lean
@@ -49,0 +50 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ArbInvolution.lean
+++ b/formal/lean/Formal/Cells/ArbInvolution.lean
@@ -47,0 +48 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ArbInvolution2.lean
+++ b/formal/lean/Formal/Cells/ArbInvolution2.lean
@@ -42,0 +43 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ArbKleene.lean
+++ b/formal/lean/Formal/Cells/ArbKleene.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -47,0 +48 @@
+open Formal.Core.LutList
@@ -49 +50 @@
-open Formal.Cells.K3
+open Formal.Core.LutList.K3
--- a/formal/lean/Formal/Cells/ArbOverlapRace.lean
+++ b/formal/lean/Formal/Cells/ArbOverlapRace.lean
@@ -48,0 +49 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/Bundling.lean
+++ b/formal/lean/Formal/Cells/Bundling.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -46,0 +47 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/CElemCore.lean
+++ b/formal/lean/Formal/Cells/CElemCore.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -38,0 +39 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/CElemFn.lean
+++ b/formal/lean/Formal/Cells/CElemFn.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -37,0 +38 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/CElemInvolution.lean
+++ b/formal/lean/Formal/Cells/CElemInvolution.lean
@@ -58,0 +59 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/CElemTiming.lean
+++ b/formal/lean/Formal/Cells/CElemTiming.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -84,0 +85 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/CTree.lean
+++ b/formal/lean/Formal/Cells/CTree.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -73,0 +74 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/CTreeTimed.lean
+++ b/formal/lean/Formal/Cells/CTreeTimed.lean
@@ -72,0 +73 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ConstraintsFastFall.lean
+++ b/formal/lean/Formal/Cells/ConstraintsFastFall.lean
@@ -49,0 +50 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ConstraintsLatchRst.lean
+++ b/formal/lean/Formal/Cells/ConstraintsLatchRst.lean
@@ -41,0 +42 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ConstraintsMore.lean
+++ b/formal/lean/Formal/Cells/ConstraintsMore.lean
@@ -47,0 +48 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ConstraintsMux.lean
+++ b/formal/lean/Formal/Cells/ConstraintsMux.lean
@@ -21,0 +22 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ConstraintsSel.lean
+++ b/formal/lean/Formal/Cells/ConstraintsSel.lean
@@ -46,0 +47 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/Contracts.lean
+++ b/formal/lean/Formal/Cells/Contracts.lean
@@ -64,0 +65 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ContractsB.lean
+++ b/formal/lean/Formal/Cells/ContractsB.lean
@@ -53,0 +54 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ContractsLink.lean
+++ b/formal/lean/Formal/Cells/ContractsLink.lean
@@ -52,0 +53 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ContractsMux.lean
+++ b/formal/lean/Formal/Cells/ContractsMux.lean
@@ -56,0 +57 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ContractsOps.lean
+++ b/formal/lean/Formal/Cells/ContractsOps.lean
@@ -34,0 +35 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ContractsTrunc.lean
+++ b/formal/lean/Formal/Cells/ContractsTrunc.lean
@@ -46,0 +47 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ContractsTruncCel.lean
+++ b/formal/lean/Formal/Cells/ContractsTruncCel.lean
@@ -27,0 +28 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ContractsTruncSteer.lean
+++ b/formal/lean/Formal/Cells/ContractsTruncSteer.lean
@@ -52,0 +53 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ContractsTruncWit.lean
+++ b/formal/lean/Formal/Cells/ContractsTruncWit.lean
@@ -17,0 +18 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/FifoFidelity.lean
+++ b/formal/lean/Formal/Cells/FifoFidelity.lean
@@ -37,0 +38 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/GcdCells.lean
+++ b/formal/lean/Formal/Cells/GcdCells.lean
@@ -69,0 +70 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/Latch.lean
+++ b/formal/lean/Formal/Cells/Latch.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -25,0 +26 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/LibCtlMergeMux.lean
+++ b/formal/lean/Formal/Cells/LibCtlMergeMux.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -44,0 +45 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/LibEndMemMlink.lean
+++ b/formal/lean/Formal/Cells/LibEndMemMlink.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -38,0 +39 @@
+open Formal.Core.LutList
@@ -303,0 +305 @@
+open Formal.Core.LutList
@@ -424,0 +427 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/LinkHandshake.lean
+++ b/formal/lean/Formal/Cells/LinkHandshake.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -52,0 +53 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/LinkTimed.lean
+++ b/formal/lean/Formal/Cells/LinkTimed.lean
@@ -47,0 +48 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/MergeMuxSI.lean
+++ b/formal/lean/Formal/Cells/MergeMuxSI.lean
@@ -50,0 +51 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/MuxN3.lean
+++ b/formal/lean/Formal/Cells/MuxN3.lean
@@ -42,0 +43 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/MuxN3Proof.lean
+++ b/formal/lean/Formal/Cells/MuxN3Proof.lean
@@ -11,0 +12 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/MuxN3Timed.lean
+++ b/formal/lean/Formal/Cells/MuxN3Timed.lean
@@ -48,0 +49 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/MuxRtzTimed.lean
+++ b/formal/lean/Formal/Cells/MuxRtzTimed.lean
@@ -55,0 +56 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/MuxTree.lean
+++ b/formal/lean/Formal/Cells/MuxTree.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -33,0 +34 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/OnNetlist.lean
+++ b/formal/lean/Formal/Cells/OnNetlist.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -59,0 +60 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/OnNetlistArb.lean
+++ b/formal/lean/Formal/Cells/OnNetlistArb.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -60,0 +61 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/OnNetlistTimed.lean
+++ b/formal/lean/Formal/Cells/OnNetlistTimed.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -66,0 +67 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/OnNetlistTimed2.lean
+++ b/formal/lean/Formal/Cells/OnNetlistTimed2.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -38,0 +39 @@
+open Formal.Core.LutList
@@ -330,0 +332 @@
+open Formal.Core.LutList
@@ -627,0 +630 @@
+open Formal.Core.LutList
@@ -763,0 +767 @@
+open Formal.Core.LutList
@@ -814,0 +819 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/OpsCounter.lean
+++ b/formal/lean/Formal/Cells/OpsCounter.lean
@@ -36,0 +37 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/OpsExact.lean
+++ b/formal/lean/Formal/Cells/OpsExact.lean
@@ -29,0 +30 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/OpsExact2.lean
+++ b/formal/lean/Formal/Cells/OpsExact2.lean
@@ -31,0 +32 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/OpsHold.lean
+++ b/formal/lean/Formal/Cells/OpsHold.lean
@@ -38,0 +39 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/OpsTimed.lean
+++ b/formal/lean/Formal/Cells/OpsTimed.lean
@@ -33,0 +34 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/OpsTimed2.lean
+++ b/formal/lean/Formal/Cells/OpsTimed2.lean
@@ -51,0 +52 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/OpsTimedMux.lean
+++ b/formal/lean/Formal/Cells/OpsTimedMux.lean
@@ -32,0 +33 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/OpsTimedWit.lean
+++ b/formal/lean/Formal/Cells/OpsTimedWit.lean
@@ -20,0 +21 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/PinAssign.lean
+++ b/formal/lean/Formal/Cells/PinAssign.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -40,0 +41 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/PipePerPin.lean
+++ b/formal/lean/Formal/Cells/PipePerPin.lean
@@ -45,0 +46 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/PipeTimed.lean
+++ b/formal/lean/Formal/Cells/PipeTimed.lean
@@ -54,0 +55 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/PipeTimedN.lean
+++ b/formal/lean/Formal/Cells/PipeTimedN.lean
@@ -42,0 +43 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/PipeWitness.lean
+++ b/formal/lean/Formal/Cells/PipeWitness.lean
@@ -41,0 +42 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/Prelim.lean
+++ /dev/null
(file deleted)
--- a/formal/lean/Formal/Cells/ResetContract.lean
+++ b/formal/lean/Formal/Cells/ResetContract.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -60,0 +61 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ResetGcd.lean
+++ b/formal/lean/Formal/Cells/ResetGcd.lean
@@ -44,0 +45 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ResetGcdNet.lean
+++ b/formal/lean/Formal/Cells/ResetGcdNet.lean
@@ -22,0 +23 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/ResetGcdWave.lean
+++ b/formal/lean/Formal/Cells/ResetGcdWave.lean
@@ -64,0 +65 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/RigContract.lean
+++ b/formal/lean/Formal/Cells/RigContract.lean
@@ -63,0 +64 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/RulesKL.lean
+++ b/formal/lean/Formal/Cells/RulesKL.lean
@@ -55,0 +56 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/TernaryExact.lean
+++ b/formal/lean/Formal/Cells/TernaryExact.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -77,0 +78 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/TernaryOnBits.lean
+++ b/formal/lean/Formal/Cells/TernaryOnBits.lean
@@ -66,0 +67 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/TernaryOnBits2.lean
+++ b/formal/lean/Formal/Cells/TernaryOnBits2.lean
@@ -33,0 +34 @@
+open Formal.Core.LutList
@@ -885,0 +887 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/TernaryPhases.lean
+++ b/formal/lean/Formal/Cells/TernaryPhases.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -50,0 +51 @@
+open Formal.Core.LutList
--- a/formal/lean/Formal/Cells/TernarySound.lean
+++ b/formal/lean/Formal/Cells/TernarySound.lean
@@ -1 +1 @@
-import Formal.Cells.Prelim
+import Formal.Core.LutList
@@ -77,0 +78 @@
+open Formal.Core.LutList
```
</details>

## 6. Order of deletion

1. Commit `Core/LutList.lean`, `Core/Bridge.lean` (A, done here).
2. In ONE commit (coupling, section 3): C step 1 + C step 2 + B section 5,
   delete `Cells/Prelim.lean`; then a full `lake build` / `check.sh` (the
   Mathlib-dependent modules of section 4 item 5 are still unchecked).
4. Optional, later: C's porting aids (`Net/CoreLutPrelim`, `Gen/PrelimSem`,
   `Net/Import/PrelimSem`) are now about `LutList.K3` = `Core.K3`, so `toP`
   is the identity and `kleeneSemP` could be replaced by `kleeneSem`; that
   is C's call, not needed for the deletion.

Lakefile / root import: none needed (`Formal/Core/LutList.lean` is under
`Formal/`, built by the `Formal.+` glob; `Formal.lean` does not list Core's
modules individually).
