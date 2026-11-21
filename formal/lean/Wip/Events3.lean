import Formal.Core.XAudit.Events3Ring

/-!
# Wip/Events3 — open items of probe A-events3 (NOT claimed; `sorry` marks each)

Proved: `Formal/Core/XAudit/Events3.lean`, `Events3Ring.lean`, `Events2Main.lean`
(see `formal/notes/A-events3.md`). None of the statements below is used by a
claimed file.
-/

namespace Formal.Core.XAudit.Events3.Wip

open Formal.Core.XAudit.Events2
open Formal.Core.XAudit.Events3

/-- Largest `n` whose branch-`b` count is at most `m` (the inverse of `filt`):
the number of transactions a mux output can have carried when its branch-`b`
input has delivered `m` events. -/
def unfilt (sel : Nat → Bool) (b : Bool) (m : Nat) : Nat → Nat
  | 0 => 0
  | n + 1 => if filt sel b (n + 1) ≤ m then n + 1 else unfilt sel b m n

/-- W-E5a, the MERGE kind (about 1.5 days): `bd_mux`. Its joins are
`j_b = C(src_b, ctl · [s = b])` (a C-element with a steered pin: already a
choice pin of `Events3` whose source is `ctl`) and `z_req = Δ(j0 + j1)` is an
OR of two DIFFERENT C-elements, exclusive because each fires only in its
branch's transactions: count `M_z = M_j0 + M_j1` with `M_jb ≤ filt sel b M_ctl`.
Shape: a third pin kind "merge" whose count is `M a (G0 s) + M b (G1 s)`, with
exclusivity from `M_ja + M_jb ≤ M_ctl`-type conservation (`filt_add`) instead
of `Skew`; the dual of `filt` is `unfilt` (the source's count bounds the
output's through it). With W-E5a and the steer of `Events3`, gcd's loop header
(mux) and exit (steer) are both in the domain. -/
theorem merge_shape : True := by
  sorry -- W-E5a

/-- W-E5b, precision (about 1 day): `Skew` uses the merged band `[min lo,
max hi]`; `Events3Ring.skew_neg` rejects an else-arm that the simulation shows
is safe, because the source cannot fire again before the slow arm's event has
reached the merge. A per-arm walk bound (the walk back to the source through
arm `b` only, counting branch-`b` events with `filt`) would accept it. -/
theorem per_arm_skew_shape : True := by
  sorry -- W-E5b

/-- W-E5c, netlist link (about 1 day): recognise `bd_steer` (LUT6_2 INIT
`0x8888888822222222`, O5 = arm 0, O6 = arm 1, pins `req`, `s`) and the merge
OR (LUT2 INIT `0xE`), compose each arm (route → AND → chain → OR → route) into
ONE monotone warp with `chain_warp`-style lemmas, and prove `design_beh3`:
every `Circuit.Sat` behaviour of a recognised design is a `Beh3`, with `sv`
the select wire through its route. Then `xevents2` gets a choice recogniser and
prints `Skew` margins next to the `Back` margins. -/
theorem design_beh3_shape : True := by
  sorry -- W-E5c

/-- W-E5d (about 1 day): loop entry and exit — the token leaves the ring on
the exit arm (to the environment) and a new one enters through the mux. The
ring's count is then not conserved; with the environment as a channel (as in
`Events2`, E2) and W-E5a, entry = merge from the environment, exit = choice pin
whose consumer is the environment. -/
theorem loop_entry_exit_shape : True := by
  sorry -- W-E5d

/-- W-E5e: the arbiter (`bd_arbiter`) is choice whose `sel` is decided by the
arbitration, not by data: the same per-branch counters, with `SelOK` replaced
by the arbiter's mutual-exclusion and hold properties (shard B's arbiter
models). `xevents2` refuses `bd_arbiter` today (`events3/cell_bd_arbiter.txt`). -/
theorem arbiter_shape : True := by
  sorry -- W-E5e

end Formal.Core.XAudit.Events3.Wip
