# C-8z4: H_NO_DEADLOCK'' -- still open; a timed-to-interleaving bridge, and an exhaustive search that finds no deadlock (incomplete)

Shard C, probe 8z4, 2026-10-29. About 3.5 h. Core Lean only (no Mathlib), no sorry/axiom/native_decide.

**Status: PARTIAL.**
- H_NO_DEADLOCK'' is **still OPEN**. No deadlock was found, and no proof was found.
- Route B (8u's walk simulation) was assessed and **not carried out**. Reasons and the exact
  open pieces are below.
- New in Lean:
  - a generic theorem that turns a timed run into interleaving steps (`serial`,
    `trace_reach`, `trace_nodead`);
  - a structural fact about the network that this theorem needs for the mux exception
    (`mux_out_not_mux`).
- New evidence (untrusted Python): an exhaustive interleaving search with partial-order
  (stubborn-set) reduction. It covers concrete vectors, and an abstract-data mode that covers
  every input at once. It found no deadlock in any state it visited. **No run finished**
  (numbers below), so this is not a completed exhaustive check.

## Verdict

1. **Route B is a multi-day proof. I did not attempt it.** NoDeadlock2 is a statement about
   single states (quiescence at `t`), so any invariant of reachable states may be used.
   Walking the obstacles in order:
   - The spine part is in reach. 8r's `Inv` gives the walk position: a spine offer count
     equals the walk's `W`, and the next spine rise is on `cur`. 8z's `dn` rules bound the lag.
   - **Data arrival needs a new global induction.** When the control token waits at a join or
     bjoin, some data input is not offered. Following the producers backwards gives a chain of
     "token k not offered" facts.
     - Muxes and links can carry this chain around a loop.
     - It ends only because the demanded token index drops at each loop back-edge. That is a
       well-founded descent along the token run's causal order. Nothing in the repository
       states it.
   - **The return-to-zero (RTZ) waits form a second kind of chain.** A channel stuck at
     req = ack = 1 waits for its producer's input to return to zero. Links break these chains
     only because their C-element stores the token.
     - A first, buggy version of the explorer produced exactly such a cycle through a loop
       header (amerge → forkG → bjoin → steerC → 3 links → amerge, every channel at 11). That
       cycle is unreachable once the bug is fixed. It shows that a route-B proof must rule
       these cycles out, and that is the "capacity" part.
   - Both chains must be combined into one well-founded measure over (channel, token index,
     phase). This is 8u's estimate of 2-3 days.
2. **Lean, kernel-checked: a timed run is interleaving-reachable when its disabling relation is
   acyclic.** The generic theorems are in `CapstoneLiveNd4Serial`.
   - `serial`: suppose every bit that changes in one timed tick `s → s'` stays excited in each
     intermediate state where none of its possible disablers has fired yet. Suppose also that
     the disabling relation, restricted to the changed bits, has a rank. Then `s'` is
     reachable from `s` by single firings.
   - `trace_reach`: the same for a whole trace.
   - `trace_nodead`: hence, if no interleaving-reachable state before the goal is dead, the
     timed run has no dead state before the goal either.
   - `arb_not_reach` shows the rank hypothesis cannot be dropped. Two gates that disable each
     other (a contested arbiter) do not serialize: `11` is unreachable from `00`.
   - Why this is the right bridge for gcd_hw. By 8z3, the only gates that can be disabled are:
     - the mux input acknowledges, disabled only by the mux's own `z_ack` rising;
     - contested grants, which never occur (8r/8s).
   - `mux_out_not_mux` (`CapstoneLiveNd4Mux`, kernel `decide` over all 367 operators): no mux
     output is consumed by a mux. So no `z_ack` gate is itself a mux input acknowledge, and the
     disabling relation has depth one. Rank 0 for mux input acknowledges and 1 for every other
     gate works.
   - **Not done:** instantiating the "stays excited in intermediate states" half (`hex`) for
     the 465-channel network. See "What remains".
3. **Evidence: exhaustive interleaving search with stubborn sets** (`Wip/C8z4/explore.py`).
   - **Model:** the gate lists are those of `gatesE`, the same as 8z2's `persim.gates2`. One
     excited gate fires per step. `start` offers once and may release (H_START_ONCE,
     H_START_REL). The a/b sources run free. out0's sink never lowers its acknowledge, so the
     search stops at out0's first close.
   - **Reduction:** Valmari stubborn sets with static read/write sets. This reduction keeps
     every reachable deadlock.
   - **Abstract mode** (`--abstract`): every `join` output is a fresh nondeterministic bit,
     chosen when its request rises. Steer and mux selects depend on data only through join
     outputs and grants. So this over-approximates every a, b, including loop paths that never
     terminate.
   - **Negative control** (`--hold`, start never released, which is 8z2's counterexample): a
     deadlock is found after 496 firings. The independent replay (`replay.py`: 8z2's
     `gates2`, 8t's data functions, transparent latches) confirms it: in the final state only
     start's release is excited.
   - **Bug caught by the replay:** the first version of the explorer reported a "deadlock" for
     12/18. The replay showed that a grant fired while it was not excited, because a Python
     closure bound the wrong `z`. After the fix, every run so far is deadlock-free.
   - Results: see the table below.

| run | states visited | out0-closed leaves | deadlocks | complete? |
|---|---|---|---|---|
| concrete 12/18 | 955 259 (stopped by me to free CPU) | not counted | 0 | no |
| concrete 1/1 | 427 939 (stopped after 672 s) | 1 | 0 | no |
| abstract (all inputs) | 1 328 454 (stopped after 2212 s) | not counted | 0 | no |
| `--hold` control, 12/18 | (stops at the first deadlock) | -- | 1, replay-confirmed | -- |

For 1/1, the first out0 close is reached after about 9 000 states. The next 418 000 states
reached no further close, and no state repeated often enough to converge. The likely cause is
the free-running a/b sources: they cycle independently of the rest, and the static-conflict
stubborn sets do not separate them. The reduction is weak here. Most visited states lie on branches that have not yet reached
out0, and the visited set grows at about 600 states/s without converging. **A complete run
needs a stronger reduction** (persistent sets that use 8z3's persistence facts instead of
static conflicts) **or a faster implementation.** Until a run completes, the table says only
"no deadlock among the states visited".

## The theorems

```
-- CapstoneLiveNd4Serial (namespace Formal.Net.CapNet.Live.Nd4), N bits, gate i writes bit i
def Step (ex : Fin N → Bool → (Fin N → Bool) → Prop) (s s' : Fin N → Bool) : Prop :=
  ∃ i, ex i (!s i) s ∧ s' = upd s i (!s i)
inductive Reach ex : (Fin N → Bool) → (Fin N → Bool) → Prop   -- refl, head
def mixL (s s' : Fin N → Bool) (L : List (Fin N)) := fun j => if j ∈ L then s j else s' j
theorem serial (ex) (s s') (Dis : Fin N → Fin N → Prop) (r : Fin N → Nat)
    (hrank : ∀ i j, s i ≠ s' i → s j ≠ s' j → Dis j i → r i < r j)
    (hex : ∀ L i, s i ≠ s' i → i ∈ L → (∀ j, j ∉ L → s j ≠ s' j → ¬ Dis j i) →
      ex i (s' i) (mixL s s' L)) : Reach ex s s'
def SerOK ex s s' := ∃ Dis r, hrank ∧ hex
theorem trace_reach (ex) (S : Nat → Fin N → Bool) (h : ∀ t, SerOK ex (S t) (S (t+1))) :
    ∀ t, Reach ex (S 0) (S t)
theorem trace_nodead (ex S Goal Dead)
    (H_INTERLEAVE : ∀ u, Reach ex (S 0) u → ¬ Goal u → ¬ Dead u)
    (h : ∀ t, SerOK ex (S t) (S (t+1))) : ∀ t, ¬ Goal (S t) → ¬ Dead (S t)
theorem arb_not_reach : ¬ Reach arbEx (fun _ => false) (fun _ => true)
-- CapstoneLiveNd4Mux
def muxOutOK : K NC → Bool   -- for mux/muxn: the consumer of z is not a mux/muxn
theorem mux_out_chk : ops.all muxOutOK = true          -- decide +kernel
theorem mux_out_not_mux (p : Fin NO) : muxOutOK (opAt p) = true
theorem mux_cons_not_mux, muxn_cons_not_mux             -- unfolded forms
```

How `serial` is proved:
- The changed bits are kept in a pending list `L`. The current state is `mixL s s' L`.
- Fire a minimal-rank pending bit (`exists_min`). Every bit already fired has rank ≤ its
  rank, so none of them can disable it (`hrank`).
- Induct on the length of `L`.

## Hypotheses and non-vacuity

| hypothesis | in | status | non-vacuity |
|---|---|---|---|
| `hrank`, `hex` (`SerOK`) | `serial`, `trace_reach`, `trace_nodead` | generic; **not instantiated for gcd_hw** | trivially met by a trace that changes one bit per tick: rank 0, `Dis` empty, `hex` is that bit's excitation. `arb_not_reach` shows the rank part has teeth |
| H_INTERLEAVE | `trace_nodead` | for gcd_hw: Python evidence only (incomplete search) | -- |
| none | `mux_out_not_mux` | unconditional (kernel `decide`) | `Wip/C8z4/Neg.lean`: a mux whose output were channel 61 (consumed by a mux) is rejected |

## What remains for H_NO_DEADLOCK'' (precise)

**Route "bridge + finite search"** (this probe's suggestion; each piece is smaller than
route B):
- (R1) **`hex` for gcd_hw.** Take one tick of a run meeting H_CELLS, H_BUNDLE and
  H_START_ONCE. Every gate output that changes must:
  - have been excited toward its new value at `t`;
  - stay excited in every intermediate state, unless its own `z_ack` (mux input
    acknowledges) has already fired.

  The way to prove it:
  - per cell, a table check like 8z3's `mux_pers_tbl` / `ltbl` / `atbl`, but over *subsets* of
    one step's changes rather than whole steps;
  - plus "no output changes unless excited" (the SI conformance of each cell model). This was
    never stated as such; `follow_rises` covers part of it.

  The projection `pj` (8z) takes care of junk state. `mux_out_not_mux` gives the rank.
- (R2) **Interleaving state.** The Lean state `gsAt` includes data buses. The serial bridge
  works on bits. It must be shown that the selects read by steers and muxes are fixed between
  firings (they are, by H_BUNDLE).
- (R3) **H_INTERLEAVE.** Either a completed abstract-data search, or a kernel check of one. A
  kernel check is probably out of reach at this state count. A completed search would give:
  - an all-inputs statement for the interleaving model, but untrusted;
  - with R1-R2, H_NO_DEADLOCK'' modulo that one computation.

**Route B** (8u). Three open pieces:
- the data-arrival descent;
- the RTZ-capacity argument, combined with the data-arrival descent into one well-founded
  measure;
- the spine case analysis on 8r's `Inv`.

The cycle found by the buggy explorer is a concrete instance that the capacity argument must
exclude.

## Files

| file | contents |
|---|---|
| `formal/lean/Formal/Net/CapstoneLiveNd4Serial.lean` | `upd`, `Step`, `Reach`, `Reach.trans`, `mixL`, `exists_min`, **`serial`**, `SerOK`, **`trace_reach`**, **`trace_nodead`**, `arbEx`, **`arb_not_reach`** |
| `formal/lean/Formal/Net/CapstoneLiveNd4Mux.lean` | `isMuxB`, `muxOutOK`, `mux_out_chk`, **`mux_out_not_mux`**, `mux_cons_not_mux`, `muxn_cons_not_mux` |
| `formal/lean/Wip/C8z4/explore.py` | exhaustive stubborn-set search (concrete / `--abstract` / `--hold`) |
| `formal/lean/Wip/C8z4/replay.py` | independent replay of a found path in 8z2's encoding |
| `formal/lean/Wip/C8z4/ex_*.log`, `ex_hold.log`, `dead_12_18.pkl` | run logs; the `--hold` deadlock path |
| `formal/lean/Wip/C8z4/Axioms.lean`, `Neg.lean` | `#print axioms`; negative control for `mux_out_chk` |

No existing file was edited. The lead must add the 2 modules to `Formal.lean`.

## Commands

    cd /home/user/asyncfpga3/formal
    ./slot.sh lake build Formal.Net.CapstoneLiveNd4Serial Formal.Net.CapstoneLiveNd4Mux
    ./check.sh Formal/Net/CapstoneLiveNd4Serial.lean Formal/Net/CapstoneLiveNd4Mux.lean
    ./slot.sh lake env lean Wip/C8z4/Axioms.lean
    ./slot.sh lake env lean Wip/C8z4/Neg.lean        # silent = control holds
    cd lean/Wip/C8z4
    python3 -I -u explore.py 12 18 --hold --maxstates 300000   # control: deadlock, then:
    python3 -I replay.py 12 18 dead_12_18.pkl                  # only start's release excited
    python3 -I -u explore.py --abstract --maxstates 8000000    # all-inputs search (hours)
    python3 -I -u explore.py 1 1 --maxstates 6000000

Results (2026-10-29):
- `check.sh` on both files: `[audit] 3069 declarations checked`, `[check] OK`. There are only
  deprecation warnings (`if_pos` / `if_neg`).
- Axioms:
  - `serial`, `trace_reach`, `trace_nodead`: {propext, Classical.choice, Quot.sound};
  - `arb_not_reach`, `mux_out_not_mux`: {propext, Quot.sound}.

## What it does NOT show

- H_NO_DEADLOCK'' is not proved. `gcd_hw_live_final2` is still a reduction.
- `serial` is generic. Its hypothesis `hex` is not proved for gcd_hw, so no gcd_hw timed run is
  yet shown to be interleaving-reachable.
- The search is untrusted Python, it is not complete, and it runs the interleaving model
  (single firings). The link latch captures on `c` rising, which is equivalent to a
  transparent latch only on runs meeting H_BUNDLE. States are stored as 128-bit hashes, so a
  collision could hide a state (negligible, but not zero).
- Nothing about the physical circuit.
