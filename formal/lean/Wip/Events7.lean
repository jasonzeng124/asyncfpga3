import Formal.Core.XAudit.Events7Beh

/-!
# Wip/Events7 — what is still open after probe A-events7 (NOT claimed; `sorry` marks each)

Proved in `Formal/Core/XAudit/Events7{Core,Excl,Cert,Beh}.lean` (check OK): `Beh7` (guarded
pins may be delay lines) and `safe`; `merge_exclN` (n-ary exclusivity under SelPart);
the derivation log (`concl_sound`, `runLog_sound`) with U-bounds through merges (U3)
and R3 / SUB at merges of any arity; `design_beh7`, **`design_verdict7`** (what
`xevents7` checks). On gcd_hw every seed is CLEAN at slow, fast and gb: no residual
item, under per-pin SatPin, H_ARB, SelOK, SelPart and **GuardOK**.

Open: **W-E4g**, discharging GuardOK. Below is the reduction I would prove next,
stated as precisely as I can. It differs from `Wip/Events6.lean`'s: there `gc` was
read off the pin's VALUE (`toggles + [pin ≠ feedback]`), which makes GuardOK's
read-value conjunct true by construction and leaves only monotonicity, but also
makes the guarded count say nothing about the guarded source `D` (a stale `z_ack`
firing `x_ack` early is then "count-consistent"). Here the guarded count is a
COUNT of `D`: the BRANCH count of `D` in the guard's label.
-/

namespace Formal.Core.XAudit.Events7.Wip

open Formal.Core.XAudit.Events (ph)
open Formal.Core.XAudit.Events3 (filt)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events7

variable {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool}

/-- The guarded pin's count as a count of its source `D = src j p`: the number of
events of `D` in the transactions of the guard's label `(grp j p, br j p)` (as a
filtered pin counts, but read through all copies of the line). -/
def guardCnt (x : Beh7 net b sel) (j : Fin N) (p : Fin (net.ar j)) (s : Nat) : Nat :=
  filt (sel (net.grp j p)) (net.br j p) (fmax (net.nc j p) (x.cm j p s))

/-- **W-E4g (not proved).** Suppose the realisation's `gc` IS `guardCnt` (a `Beh7`
with that `gc` exists by a joint recursion of `gc` and `M` in time: `gc j p s`
needs `M` only at the copy times `G j p i s < s`; constructing it is part of the
work), and three log facts per guarded pin `p` of stage `j`, guard pin `g = gp j p`,
source `D`:

* **BACK-G** (upper, local): log line `iB` is a walk `(false, D, some (grp, br), j, dB, tB)`
  with `tB + off ≤ 1` and `hiQ j < loP j p + dB` (STRICT): the branch count of `D`
  is at most one ahead of the feedback. This is `backOK7` for the pin seen as
  filtered, and gives GuardOK's first conjunct exactly as `backOK7_sound`.
* **ENTRY** (lower, global): log line `iU` is a U-bound `(true, src j g, some (grp, br), S, dU, 0)`
  of the guard (the guard fires only in the label's transactions of `S`), `S` has a
  pin `q` reading `D` inverted (`off = 1`), and STRICTLY
  `hiC j p i < loP j g + dU + loF S + loC S q` for every copy `i`: when the guard
  has advanced, every copy of `D` has completed the previous transaction of `S`
  (`M_D ≥ 2k` for the guard's transaction `k`). This is ana's ENTRY rule; the U-bound
  is the needed LOWER bound on `D` (read backwards: `S` cannot start `k` before
  `D`'s `2k`-th event reached it).
* **EXIT** (upper, global): log line `iX` is a walk `(false, D, none, j', dX, tX)` to a
  stage `j'` downstream of `j`'s output, with `tX ≤ 1` and STRICTLY
  `hiC j p i - loC j p i' + hiF j + hiQ j < dX` (the copies of `D` do not see `D`'s
  transaction `k` end before `j` has fired and seen its own feedback).

Then GuardOK holds: the bound conjunct by BACK-G; the read-value conjunct because
under ENTRY and EXIT every copy count `M_D (G j p i s)` lies in `{2k, 2k+1}` for the
guard's transaction `k`, whose label is the guard's, so `ph (M_D) = ph (filt … M_D)`
copy by copy, the copies are contiguous (EXIT), and the line value is
`ph (andCnt …)` = `ph (guardCnt …)` (`Events5.andF_val`). -/
theorem guardOK_of_entry_exit (x : Beh7 net b sel) (hOK : net.OK7) {parts : List (List Nat)}
    (hp : SelPart sel parts) {J : Array Jd} (hJ : AllH x J)
    (hgc : ∀ j p s, net.pk j p = PK.guard → x.gc j p s = guardCnt x j p s)
    (iB iU iX : (j : Fin N) → Fin (net.ar j) → Nat)
    (hentry : ∀ j p, net.pk j p = PK.guard → True) (hexit : ∀ j p, net.pk j p = PK.guard → True) :
    x.GuardOK := by
  sorry -- W-E4g: the three log facts above are stated in the docstring; their Bool checks
        -- (`backG7`, `entry7`, `exit7`) and soundness are the work. Estimated 1 to 1.5 days.

/-- **Monotonicity of the count choice (proved here).** If no copy of `D` is in an odd
count of a transaction `≠ k` at the stage's samples between the guard's advance and
the feedback's move, the stage's guarded count is monotone there. With `gc :=
guardCnt` monotonicity is automatic (`filt` and `M` are monotone): the content moves
from `gcmono` to the read-value conjunct, which is where ENTRY / EXIT enter. -/
theorem guardCnt_mono (x : Beh7 net b sel) (j : Fin N) (p : Fin (net.ar j)) (a s : Nat) (h : a ≤ s) :
    guardCnt x j p a ≤ guardCnt x j p s := by
  unfold guardCnt
  apply Formal.Core.XAudit.Events3.filt_mono
  apply fmax_mono _ _ _ (net.nc_pos j p)
  intro i; unfold Beh7.cm; exact x.M_mono _ _ _ ((x.wG j p i).mono _ _ h)

end Formal.Core.XAudit.Events7.Wip
