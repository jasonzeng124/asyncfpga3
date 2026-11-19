import Formal.Rewrite.Steps.CollatzEq2Pass

/-!
# Formal.Rewrite.Steps.Eq2Controls — negative controls for the pre_eq2 script check (shard A, 2026-11-19)

Each control is a mutation that makes the rewrite WRONG; each must be refused (Lean evaluates the checks).
* `ctl_width2`: the identity at width 2 (where it is false, `Eq2` docstring: n = 2 is -2 and -2 >> 1 = -1): the
  `ident` step refuses (`runScript` = none).
* `ctl_shrui`: the original's step with a logical shift (`shrui`) instead of the arithmetic one: the folded test is
  not the library's identity, the `ident` step refuses.
* `ctl_lit3`: research's rewritten graph with the test `n == 3` instead of `n == 2`: its script still runs, but its
  normal form is not the original's under the certified renaming (`renCheck` = false). (rules_iso.py, untrusted,
  also finds no renaming at all: NOT ISOMORPHIC.)
-/

namespace Formal.Rewrite.Steps.Eq2Controls

open Formal.Net.GcdHw Formal.Rewrite.IncCmp Formal.Rewrite.Steps Formal.Rewrite.Steps.CollatzEq2Pass

def s1w2 : List Step := [.reorder 19 [26, 34, 27], .absorb 13 19, .reorder 19 [26, 23, 34], .absorb 18 19,
  .reorder 19 [23, 24, 25, 26], .forkjoin 12 19, .forkcomm 12 20 49 50, .absorb 32 22, .ident 22 2,
  .drop 32, .drop 19, .drop 18, .drop 13]

theorem ctl_width2 : runScript Formal.Net.CollatzHw.rules s1w2 = none := by decide +kernel

def origShrui : List Rule := Formal.Net.CollatzHw.rules.set 19
  (.comp [27, 26, 34] 35 (.sel (.bin (.cmpi .eq) 1 (.bin .andi 1 (.var 0) (.lit 1)) (.lit 0))
    (.bin .shrui 32 (.var 1) (.lit 1)) (.var 2)))

theorem ctl_shrui : runScript origShrui s1 = none := by decide +kernel

def rwLit3 : List Rule := Formal.Rewrite.CollatzPreeq2Hw.rules.set 21
  (.comp [27] 38 (.bin (.cmpi .eq) 32 (.var 0) (.lit 3)))

def r3 : Res := (runScript rwLit3 s2).getD ([], [], [])
theorem ctl_lit3_runs : runScript rwLit3 s2 = some r3 := by decide +kernel
theorem ctl_lit3 : renCheck r1.1 r3.1 P Ti = false := by decide +kernel

/-- The mutation sites are really what the controls say (the unmutated rules there). -/
theorem site19 : Formal.Net.CollatzHw.rules[19]? = some (.comp [27, 26, 34] 35 (.sel (.bin (.cmpi .eq) 1
    (.bin .andi 1 (.var 0) (.lit 1)) (.lit 0)) (.bin .shrsi 32 (.var 1) (.lit 1)) (.var 2))) := by decide +kernel
theorem site21 : Formal.Rewrite.CollatzPreeq2Hw.rules[21]? =
    some (.comp [27] 38 (.bin (.cmpi .eq) 32 (.var 0) (.lit 2))) := by decide +kernel

end Formal.Rewrite.Steps.Eq2Controls
