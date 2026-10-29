# C-8z3: H_NO_DEADLOCK'' -- persistence proved except at the mux input acknowledges, where it is FALSE

Shard C, probe 8z3, 2026-10-29. About 3.5 h. Core Lean only (no Mathlib), no sorry/axiom/native_decide.

**Status: PARTIAL.** H_NO_DEADLOCK'' is **still OPEN**. No counterexample to it was found.
What changed: the first pillar of C-8z2's suggested route (persistence as an invariant of
all reachable states, then Keller confluence) is now settled, both ways.

## Verdict

1. **Persistence, proved for every gate but the mux input acknowledges.**
   - The theorems: `gcd_hw_persistent` and `gcd_hw_mux_persistent` (`CapstoneLiveNd3Pers`),
     plus the 3-way mux (`CapstoneLiveNd3MuxN`, `CapstoneLiveNd3`).
   - The setting: a, b < 2^31 and every run meeting H_CELLS, H_BUNDLE and H_START_ONCE. No
     timing hypothesis is used.
   - What holds: every gate of the 465-channel network is persistent. An excited gate stays
     excited until it fires. This covers forks, joins, steers, links, sources, sinks,
     arbiter-stage `z_req` and input acknowledges, and the arbiter **grants**. The grants are
     persistent because no stage is ever contested (8r's `gcd_hw_never_contested`).
   - The one exception: the input-acknowledge C-elements of the 21 two-way muxes and of the
     one 3-way mux. Each is persistent except that its *falling* excitation can be withdrawn
     by `z_ack` *rising* in the same step (`ZRise`).
2. **The exception is real, so the persistence invariant is FALSE for gcd_hw.**
   - Local (kernel-checked): the state is in the mux's reachable table
     (`mux_ack_not_pers`):
     - `x`'s previous token is returning (`x_req` low, `x_ack` high, `j0` low);
     - `z_ack` is low;
     - the back-edge token `y` is already through `j1` and `z_req`.
     Here `x_ack` is excited to fall. If `z_ack` rises first, `x_ack` is no longer excited.
     The `decide` over the whole table that claimed full persistence was **refuted by the
     kernel**: an unweakened `mux_pers_tbl` does not check.
   - Whole network (simulation, untrusted): `Wip/C8z3/persim_slowack.py`.
     - Setup: 8z2's bounded-delay harness, except the mux input acknowledges get delay 300
       and every other gate gets [1, 4].
     - Result for a = 12, b = 18: 8 persistence violations at 8 different loop-header
       muxes, out0 = 6, no deadlock.
     - So the hazard is reachable under the hypotheses of `gcd_hw_live_final2` with
       H ≥ 300. It takes a whole loop traversal racing one C-element.
   - Consequence: Keller's theorem (persistent ⇒ all maximal runs confluent ⇒ one schedule
     per input decides deadlock) **does not apply as sketched in C-8z2**. The route needs a
     weaker confluence notion that tolerates a C-element that just holds (below).
   - Physically the race is one LUT delay against a full loop, so it is a relative-timing
     fact that the fabric meets with a huge margin. In the gate model (H_CELLS +
     bounded delay) it is allowed.
3. **H_NO_DEADLOCK'': still open; no counterexample.**
   - The only non-persistent gate holds its output, it does not drop a token: the next
     `z_ack` fall re-excites it.
   - The slow-acknowledge runs, like 8z2's 320 runs, never deadlock.
   - What remains is stated at the end.

## The theorems

```
-- CapstoneLiveNd3Pers (namespace Formal.Net.CapNet.Live.Nd3)
def Pers (S : Nat → GS) (g : Gate) : Prop :=
  ∀ v t, g.exc v (S t) → g.out (S t) ≠ v → g.exc v (S (t + 1)) ∨ g.out (S (t + 1)) = v
def PersB (S) (B : Nat → Prop) (g) : Prop := ∀ v t, ... → ... ∨ ... ∨ B t
def ZRise (ch) (z) (t) : Prop := (ch z).ack t = false ∧ (ch z).ack (t + 1) = true

theorem gcd_hw_persistent (a b) (ha : a < 2^31) (hb : b < 2^31) (ch itr)
    (H_CELLS : ∀ p, CellI ch (srcV a b) itr p (opAt p)) (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1) :
    ∀ p, (opAt p is not a mux) → (opAt p is not a 3-way mux) →
      ∀ g ∈ gatesK p (opAt p) ++ grantsK p (opAt p), Pers (gsAt ch itr) g
theorem gcd_hw_mux_persistent (a b ch itr) (H_CELLS) (H_BUNDLE) :
    ∀ p c x y z mw, opAt p = .mux c x y z mw → ∀ g ∈ gatesK p (opAt p), PersB (gsAt ch itr) (ZRise ch z) g
-- CapstoneLiveNd3: the same for the 3-way mux, and the combined statement
theorem gcd_hw_muxn_persistent ...
theorem gcd_hw_persistent_all (a b) (ha hb) (ch itr) (H_CELLS) (H_BUNDLE) (H_START_ONCE) :
    ∀ p, ∀ g ∈ gatesK p (opAt p) ++ grantsK p (opAt p),
      PersB (gsAt ch itr) (fun t => ∃ z, MuxOut (opAt p) z ∧ ZRise ch z t) g
-- CapstoneLiveNd3Loc: per-cell lemmas; mux_ack_not_pers (the exception, kernel)
```

`gatesK`/`grantsK` are 8u's gate lists, the same ones `gcd_hw_live_final2` uses (C-8z2's
`gates_eq` ties them to the syntax `gatesE`). So "persistent" here is about exactly the gates
whose quiescence H_NO_DEADLOCK'' talks about.

## How the proof works

- **Per cell (`CapstoneLiveNd3Loc`).** Each cell's existing inductive invariant (8f/8j/8l)
  holds at `t`. Add one step allowed by the cell's gate model and by the protocol of its
  channels. Persistence of each gate then follows by `decide`:
  - fork `FInv`, join `JInv`, steer `SInv`: small Boolean lemmas `f1 f2 j1 j2 st1 st2 st3`;
  - mux `tbl` (132 states), arbiter `atbl` (38), link `ltbl` (20): `decide +kernel` over the
    tables, with exactly the step hypotheses of the cells' own closure theorems
    (`mux_closed`, `amerge_closed`, `link_closed`);
  - 3-way mux `TB` (648 states): split by select value, like 8l.
  - Arbiter grants: `grant_pers_tbl` needs the extra hypothesis "not contested at `t`". In a
    contested state one grant firing disables the other, and that is the arbiter's job.
  - Source LUT and sink wire: the protocol alone.
  - The steer and mux selects are steady because of `Held` on the select channel.
- **Network (`CapstoneLiveNd3Pers`).**
  - Protocol of every channel: 8o's `gcd_hw_protocol`.
  - No contest at any arbiter: 8r/8s's `gcd_hw_never_contested`, using `good_run` and
    `walk_ok` for the token run. This is where a, b < 2^31 and H_START_ONCE enter.
  - Then a case split over the 12 operator kinds, matching each gate of `gatesK`/`grantsK`
    to its cell lemma.

## The exception, exactly

`mux_pers_tbl` proves, for the 2-way mux, all six gates persistent except one weakening.
For `x_ack = C(j0, z_ack)` and `y_ack = C(j1, z_ack)`, a falling excitation may end with
`z_ack` rising instead (`(v = false ∧ za = true)` in `MPers`). The Python mirror
`Wip/C8z3/muxcheck.py` finds exactly these two failing cases (`xa`↓ and `ya`↓, each with
`za`↑) and no others. `Wip/C8z3/muxncheck.py` finds the same three cases (`in_k_ack`↓ with
`za`↑) in the 3-way mux's 648-state table, and the Lean `npers0..3` prove nothing else fails.

Which gates break, and why. The input acknowledge is a C-element of the join node `j_k` and
`z_ack`.
1. After `x`'s token has passed, `j0` falls (once `x_req` and the control token have
   returned). Then `z_req` falls, then `z_ack` falls.
2. Now `x_ack` is excited to fall.
3. If the next token, from `y` (the loop back-edge) or a new entry, is through `j1` and
   `z_req` and its consumer raises `z_ack` before `x_ack` has fallen, then `x_ack`'s inputs
   disagree again and it holds high. It falls only after the next `z_ack` fall.
4. Meanwhile `x`'s producer cannot offer: `x_req` may rise only once `x_ack` is low. That is
   a delay, not a lost token.

## What remains for H_NO_DEADLOCK'' (precise)

H_NO_DEADLOCK'' (C-8z2): for every run meeting the hypotheses of `gcd_hw_live_final2`, at
every `t` before out0's first close, `Quiet2` fails or `start`'s LUT is excited.

**Route A, Keller repaired.** Persistence now holds everywhere except at `ZRise` events on
mux outputs. Two things are still needed.
- (A1) A confluence theorem for "persistent up to C-elements that hold". The usual trick is
  to treat each mux input acknowledge as excited toward `0` exactly when `j_k = 0` (dropping
  the `z_ack` conjunct for the fall), or to show that every interleaving can be reordered so
  that the acknowledge fall comes before the `z_ack` rise. Either way it has to be proved
  for timed traces with simultaneous changes.
- (A2) Per input, a single-schedule argument that out0 closes. It must be symbolic over
  a, b < 2^31. The unit-delay run is concrete only for (12, 18), and the binary-gcd loop
  counts vary with the input (bounded by about 62 iterations, but the data paths differ).

**Route B, walk simulation (8u's plan).** It does not need persistence. Show that at any
quiescent state before out0 closes, the spine token's next producer (8r's walk: `Inv t`
gives the walk position) is excited. Needed:
- data arrival on the non-spine join/steer inputs;
- capacity on the link chains: 8o's two-front invariant, and 8z's offer bounds already give
  `off c ≤ off d + 2`;
- the start release (H_START_REL).

8u estimated 2-3 days. This probe did not attempt it.

**Evidence that it holds.** C-8z2: 320 random bounded-delay runs. This probe: 3 runs with
slow mux acknowledges (a = 12/18, 0/5, 7/0). No deadlock in either set.

## Hypotheses and non-vacuity

| hypothesis | in | status | non-vacuity |
|---|---|---|---|
| H_CELLS (`CellI`), H_BUNDLE, H_START_ONCE | `gcd_hw_persistent`, `_all` | as 8r/8u | C-8z2's joint witness (`gcd_hw_live2_joint_witness`) meets all three, at a = 12, b = 18 |
| a, b < 2^31 | same | range (replaces H_WALK, 8s) | — |
| H_CELLS, H_BUNDLE | `gcd_hw_mux_persistent`, `_muxn_` | — | same witness |

No new hypothesis is introduced. The theorems are unconditional up to the existing gate
models.

## Files

| file | contents |
|---|---|
| `formal/lean/Formal/Net/CapstoneLiveNd3Loc.lean` | `AllB`, `send_stay`, `recv_stay`, `src_pers`, `sink_pers`, fork/join/steer lemmas (`f1 f2 j1 j2 st1 st2 st3`, `fork_*_pers`, `join_*_pers`, `steer_*_pers`), `MPers`, **`mux_pers_tbl`**, `mux_step_pers`, **`mux_ack_not_pers`**, `APers`, `GPers`, `amerge_pers_tbl`, **`grant_pers_tbl`**, `amerge_step_pers`, `grant_step_pers`, `LPers`, `link_pers_tbl`, `link_step_pers` |
| `formal/lean/Formal/Net/CapstoneLiveNd3MuxN.lean` | `NPers`, `NPersAt`, `npers0..3` (kernel, by select), `npers_all`, `muxn_step_pers` |
| `formal/lean/Formal/Net/CapstoneLiveNd3Pers.lean` | `Pers`, `PersB`, `ZRise`, `pers_fork/join/steer/link/amerge/mux/src/sink`, **`gcd_hw_persistent`**, **`gcd_hw_mux_persistent`** |
| `formal/lean/Formal/Net/CapstoneLiveNd3.lean` | `pers_muxn`, **`gcd_hw_muxn_persistent`**, **`gcd_hw_persistent_all`** |
| `formal/lean/Wip/C8z3/muxcheck.py`, `muxncheck.py` | Python mirrors of the table checks (which gates fail) |
| `formal/lean/Wip/C8z3/persim_slowack.py` | 8z2's harness with slow mux acknowledges: whole-network persistence violations |
| `formal/lean/Wip/C8z3/Axioms.lean` | `#print axioms` |

No existing file was edited. The lead must add the 4 modules to `Formal.lean`.

## Commands

    cd /home/user/asyncfpga3/formal
    for m in CapstoneLiveNd3Loc CapstoneLiveNd3MuxN CapstoneLiveNd3Pers CapstoneLiveNd3; do
      ./slot.sh lake build Formal.Net.$m; done
    ./check.sh Formal/Net/CapstoneLiveNd3Loc.lean Formal/Net/CapstoneLiveNd3MuxN.lean \
      Formal/Net/CapstoneLiveNd3Pers.lean Formal/Net/CapstoneLiveNd3.lean
    ./slot.sh lake env lean Wip/C8z3/Axioms.lean
    cd lean && python3 -I Wip/C8z3/muxcheck.py && python3 -I Wip/C8z3/muxncheck.py
    python3 -I Wip/C8z3/persim_slowack.py 3 4        # SLOW=300 default; ~2 min

Results: see "Check results" below.

## What it does NOT show

- H_NO_DEADLOCK'' is not proved. `gcd_hw_live_final2` is still a reduction.
- Persistence is not confluence. Even with the exception handled, no confluence theorem for
  these traces is proved here.
- The whole-network reachability of the mux exception is shown by simulation only. The Lean
  shows only that the local reachable table allows it. Lean refutes only the *local*
  persistence claim.
- Nothing about the physical circuit. The exception needs a loop traversal faster than one
  C-element, which the fabric does not do.
