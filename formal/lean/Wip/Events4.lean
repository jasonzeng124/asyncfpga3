import Formal.Core.XAudit.Events4

/-!
# Wip/Events4 — open items of probe A-events4 (NOT claimed; `sorry` marks each)

Proved: `Formal/Core/XAudit/Events4.lean` (lemmas) and the recogniser
`Events4Main.lean` (trusted code). The analysis of the routed gcd_hw control
(`tools-A/xaudit/events4/ana.py`, untrusted) applies the rules below; each
rule's arithmetic core is proved in `Events4`, but the INTEGRATION into one
soundness theorem over behaviours is open. Until W-E4i and W-E4n check, the
gcd_hw verdicts of `formal/notes/A-events4.md` are "the domain's rules hold
on the routed netlist", NOT a kernel-checked certificate.
-/

namespace Formal.Core.XAudit.Events4.Wip

open Formal.Core.XAudit.Events3 (filt)

/-- W-E4i (integration, ~1.5 days): one `Beh4` structure with node kinds
`cel | merge` and pin kinds `tap (plain | filtered) | multi (and | or)`, the
count recursion `M` (cel: `fmin` of pin counts; merge: SUM of tap counts;
filtered tap: `filt`; multi: `andCnt/orCnt` of the copies' extreme counts),
and `Beh4.safe`: under (a) Back certificates built from the steps R1 (any
single-source pin), R3 (`reconv`) and SUB (`sub_step`), (b) per merge the
exclusivity data of `merge_excl` (arms U-bounded by distinct branches of one
source + a ≤1-token walk back to the merge), (c) per delay line a contiguity
certificate (`contig_union` per gate, window ≤ the source's per-window bound
`cycle_le`), (d) guarded pins with `GuardOK` (W-E4g), (e) `SelOK` per filtered
tap: every node of every behaviour is `ph v (M t j)` at every time. The proof
is `Events3.Beh3.safe`'s induction with four pin cases; exclusivity and
contiguity are facts about `M` alone, proved BEFORE the induction (as
`arms_close` is in Events3). -/
theorem beh4_safe_shape : True := by
  sorry -- W-E4i

/-- W-E4g (guard timing, ~1 day): discharge `cel_guard_ph`'s `hguard` from
the two timing conditions the analysis checks: ENTRY
`hi(D→j) ≤ lo(D→S) + loF S + lo(S → … → guard pin)` (when the guard has
advanced into a branch-`b` transaction, `j` already sees `D` at the count `S`
saw) and EXIT `hi(D→j) − lo(D→j) + hiF j + hiQ j ≤ W(D)` (`j` has fallen and
its feedback settled before `D`'s next event reaches it). Needs a LOWER-bound
walk judgement (`M_D (G s) ≥ …`), which no Events file has yet. -/
theorem guard_ok_shape : True := by
  sorry -- W-E4g

/-- W-E4n (netlist link, ~1 day): `design_beh4`: every `Circuit.Sat`
behaviour of a design recognised by `Events4Main` (with its role maps checked
by a decidable `Recog4`, as `Recog2`) is a `Beh4`; physical-pin INITs need
`spec` over a role map instead of `Events2Design.layout`; delay lines and
steers compose like `chain_warp` but through AND/OR gates (each copy is a
composition of warps). -/
theorem design_beh4_shape : True := by
  sorry -- W-E4n

/-- H_ARB (stated, not proved; out of the domain by design): each
`bd_arbiter` core (state LUT + grant LUTs) behaves as a virtual mux core:
`g_b = C(r_b, ctl · [σ = b])`, `ctl = ¬A0` delayed by
`[lo(A0→state) + lo(state) + lo(q→grant), ∞)`, `R0 = g1 + g2` (a merge) —
i.e. mutual exclusion of the grants, grants that copy their request once
granted, and no new grant before `A0` falls. `σ` (who wins) is an
environment choice. A board/GLS test: the arbiter's grant order under
contention must be explainable by some `σ` (no double grant, no grant before
`A0` falls, `R0` = OR of grants within the stated band). -/
theorem h_arb_statement : True := by
  sorry -- H_ARB (hypothesis, documented)

/-- Exclusivity for n-ary merges with arms of one group (3-way mux): the
binary `merge_excl` generalised to `nOdd ≤ 1` (needs `filt` with branch labels
in `Fin n` and an n-ary `filt_add`). ~0.5 day. -/
theorem merge_excl_nary_shape : True := by
  sorry -- W-E4x

end Formal.Core.XAudit.Events4.Wip
