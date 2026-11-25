# C-witgen: ACTIVE witnesses for the generated-cell capstones (O4, O4b)

Shard C, probe witgen, 2026-10-29. Core Lean only (no Mathlib), no sorry / axiom /
native_decide. Status: DONE (gcd_hw as asked, plus ipow, xorshift, collatz).

## Verdict

- **The generated-cell hypotheses are satisfiable together with activity: works, for all four
  kernels.** Before this probe the only joint witnesses for O4's `gcd_hw_circuit_safe_gen` and
  O4b's `*_circuit_safe_genK` / `*_genP` were quiet runs (nothing moves), and ipow had none.
- **gcd_hw (a = 12, b = 18): `gcd_hw_gen_all_witness`.** One unit-delay run of the concrete
  465-channel network at the generated-netlist level satisfies, jointly, every hypothesis of
  `gcd_hw_circuit_safe_gen` (O4: `GenCell` on all 367 operators), `gcd_hw_circuit_safe_genK`
  (O4b: `GenCellK`) and the PersistK instance `gcd_hw_circuit_safe_genP` (`GenCellKP`), plus
  H_BUNDLE and H_START_ONCE, and out0 closes a token carrying 6 (tick 1147). The internal nodes
  are real and move: 5424 internal-node toggles (2252 channel toggles), every compute unit's
  13-node `uor` + bd_delay_gated chain, every bd_mux udly chain, the muxN `|j` node and chain,
  8 of 9 arbiter R0 chains, 141 of 175 bd_link `rdly`/`uack` chains, the bd_ctree internal
  nodes of both fork N = 5 and the fork N = 6. `gcd_hw_gen_witness_consistent`: the three
  theorems applied to the run give 6.
- **ipow (b = 3, e = 7, ipow.c's own main): `Ipow.ipow_gen_joint_witness`**, the first
  witness of any kind for ipow's generated-cell theorems (`GenCellK`, `GenCellKP`; O4's
  `GenCell` is unsatisfiable there, `ipow_O4_vacuous`). out0 closes with 2187 =
  `ipowSpec 3 7` (decided) = gcc on kernels/ipow/ipow.c (`capwit3/expected.sh`). The 3-input
  compute unit's bd_join_N3 node moves.
- **xorshift (seed 2463534242, rounds 4) and collatz (n = 7): active witnesses** for O4b's
  `GenCellK` / `GenCellKP` theorems, latching 2008045182 and 16 (C-wit's inputs; values from
  gcc via `capwit2/expected.sh`, decided as `xsSpec` / `collatzC` here).
- **No hypothesis turned out unsatisfiable with activity.** The plainest schedule (every LUT
  node, chain stage and route = 1 tick) met H_CHAIN_SETTLED on every side-tapped chain, end-only
  persistence on every buffer chain, H_LEAF_PERSIST, H_R0_ISO, H_AMERGE_RTZ and H_BUNDLE at once.
- **The extra content is load-bearing (negative controls, kernel-rejected):** slowing ONE
  delay-chain node (bd_link op 192's `uack` head, inertial delay 291 ticks) keeps the lumped Ops
  models (`Cell`, H_CELLS) true on every operator but breaks H_CHAIN_SETTLED, and the
  generated-level check rejects it; one flipped INIT bit in fork op 67's chunk C-element is
  rejected too.

## Run

    cd /home/user/asyncfpga3/formal
    ./check.sh Formal/Net/GenWitLib.lean Formal/Net/GenWitData.lean Formal/Net/GenWitOx.lean \
      Formal/Net/GenWitCells1.lean Formal/Net/GenWitCells2.lean Formal/Net/GenWit.lean \
      Formal/Net/GenWitLibK.lean Formal/Net/GenWitIpowData.lean Formal/Net/GenWitIpow.lean \
      Formal/Net/GenWitXorshiftData.lean Formal/Net/GenWitXorshift.lean \
      Formal/Net/GenWitCollatzData.lean Formal/Net/GenWitCollatz.lean
    ./slot.sh lake env lean Wip/Cwitgen/Axioms.lean      # #check / #print axioms (needs the oleans)
    lean/Wip/Cwitgen/negctl.sh                           # 2 negative controls, must print negctl: ok
    tools/capwit3/check_drift.sh                         # generated Lean == generator output
    tools/capwit3/expected.sh                            # ipow(3, 7) = 2187 from gcc
    python3 tools/capwit3/simgen.py gcd 12 18            # untrusted mirror: 0 violations
    python3 tools/capwit3/simgen.py ipow 3 7

Result 2026-10-29: `[audit] 6749 declarations checked`, `[check] OK` (4 min 20 s wall, one
slot). Axioms of all eight witness / consistency theorems: [propext, Classical.choice,
Quot.sound]. `negctl: ok`. Drift: ok.

Oleans for building on these (one at a time, in this order):
`cd formal && for f in GenWitLib GenWitData GenWitOx GenWitCells1 GenWitCells2 GenWit GenWitLibK
GenWitIpowData GenWitIpow GenWitXorshiftData GenWitXorshift GenWitCollatzData GenWitCollatz; do
./slot.sh lake env lean -o .lake/build/lib/lean/Formal/Net/$f.olean Formal/Net/$f.lean; done`.
I built `CellBindPersistK.olean` (O4b's file, unchanged) the same way; it was missing.

Cost per file (peak RSS of the slot process, ~0.8 GB of it is the import baseline):

| file | time | peak |
|---|---|---|
| GenWitCells1 (ops 0..183) | 13 s | 1.57 GB |
| GenWitCells2 (ops 184..366, Held, start, out0) | 19 s | 1.84 GB |
| GenWitCollatz (11 chunks of 6 ops) | 69 s | 1.91 GB |
| GenWitIpow, GenWitXorshift | 6-7 s | 1.0-1.1 GB |
| every other file | < 7 s | 0.8 GB |

Collatz is the slow one: its loop makes every signal toggle ~34 times and each event check
reads signals by a linear scan, so the check is quadratic in that; one 66-operator `decide`
took 6.1 GB, hence the chunks. **The lead must add the 13 modules to `Formal.lean`** (I do not
own it), after O4's and O4b's modules (`CellBind*`, themselves not yet in `Formal.lean`).

## Files

| file | contents |
|---|---|
| `Formal/Net/GenWitLib.lean` | `OX` (per-operator internal-node toggle lists + chain stage list), `sG`/`sG_eq` (stages = the generated LUT1/LUT2 functions), **`chainChk`/`chain_sound`** (→ `GenChain`, H_CHAIN_SETTLED included), **`bufChk`/`buf_sound`** (→ `GenBufChain`), `leafChk`/`leaf_sound` (H_LEAF_PERSIST), `cnode_mk`/`cnode_of`, per-kind checks, **`kChkG`, `kChkG_sound`** (→ O4's `GenCell`, all 12 kinds), `genK_of_gen`, `genKP_of_gen` (`GenCell` → `GenCellK` → `GenCellKP`) |
| `Formal/Net/GenWitLibK.lean` | `joinXChkK` (compute joins N = 1..3, bd_join_N3's `j3_gate`), **`kChkGK`, `kChkGK_sound`** (→ O4b's `GenCellK`) |
| `Formal/Net/GenWitData.lean`, `GenWitOx.lean` | GENERATED (`capwit3/gen_genwit.py`): gcd_hw channels (`gcds`, C-8t's `CD` format) and internal nodes (`goxs`), stage lists `stJ stN stA stK` |
| `Formal/Net/GenWitCells1.lean`, `GenWitCells2.lean` | kernel checks: `gcells1..4`, **`g_gen`** (H_GEN), `g_held`, `g_start_once`, `g_out0` |
| `Formal/Net/GenWit.lean` | **`gcd_hw_gen_joint_witness`** (O4), `gcd_hw_genK_joint_witness`, `gcd_hw_genP_joint_witness`, **`gcd_hw_gen_all_witness`** (all three at once), `gcd_hw_gen_witness_consistent` |
| `Formal/Net/GenWit{Ipow,Xorshift,Collatz}Data.lean` | GENERATED (`gen_genwit.py ipow|xorshift|collatz`) |
| `Formal/Net/GenWit{Ipow,Xorshift,Collatz}.lean` | `*_genK`, `*_held`, `*_start_once`, `*_out0`, `*_expected`, **`{ipow,xorshift,collatz}_gen_joint_witness`** (`GenCellK` ∧ `GenCellKP`), `*_gen_witness_consistent` |
| `formal/tools/capwit3/simgen.py` | generated-level unit-delay simulator + Python mirror of every `GenCell` condition (untrusted); `mut` (controls), `delay` (random inertial delays, exploration) |
| `formal/tools/capwit3/gen_genwit.py`, `gen_neg3.py`, `check_drift.sh`, `expected.sh` | generators, drift check, gcc reference for ipow |
| `formal/tools/capwit3/explore.py` | random-delay exploration (untrusted; below) |
| `formal/tools/capwit3/sim.py`, `leanparse.py` | copies of capwit2's (sim.py: ipow added to `NETS`/`START`, nothing else changed) |
| `formal/lean/Wip/Cwitgen/negctl.sh`, `neg/Neg{Settled,Init}.lean` | negative controls (GENERATED by gen_neg3.py) |
| `formal/lean/Wip/Cwitgen/Axioms.lean` | `#check` / `#print axioms` |

capwit and capwit2 are unchanged. No pre-existing file was edited.

## The run (what "generated level" means here)

`simgen.py` simulates exactly the node structure `GenCell` quantifies over, with bdc's own
shapes (cells/rtl/bd_latch.v, bd_link.v, the emitted `bdc_fused_*` / `bdc_amerge*` units):

| operator | nodes simulated (each 1 tick) |
|---|---|
| fork N ≤ 4 | one C-element LUT on the branch acks; `req_out[k]` a 1-tick route (H_WIRE_DI) |
| fork N = 5 / 6 | bd_ctree: chunk C4 node `m` + top C2 / C4 `m1`, C2 `m2`, top C2 |
| compute unit | bd_join node (N = 2, 3) or the input (N = 1); `uor` LUT1; `bd_delay_gated #(.N(12))`: x1 = buf x0, x2 = buf x1, x_k = x_{k-1} ∧ x0 (13 nodes); ack routes 1 tick |
| bjoin, steer, src, sink | as C-8t (the lumped node IS the generated LUT) |
| mux | uj0/uj1/uxa/uya C-elements, `uor` OR node, plain `bd_delay #(.N(12))` |
| muxN | 3 join + 3 ack `bd_c2`, `|j` OR node, `uor` + `bd_delay_gated #(.N(12))` |
| amerge | grants as C-8t; R0 = g1 ∨ g2 at the same tick (H_R0_ISO literally); `uor` + `bd_delay_gated #(.N(4))` |
| link | controller LUT `c`; `rdly` = 3 LUT1 + 1 route (4 nodes); `uack` = bd_delay FASTRISE N = 6 (buf c, then x_k = x_{k-1} ∨ c) + 1 route (7 nodes) |

Lengths: 12 is the smallest DELAY bdc's tightened gcd_kernel.v (formal/tools/rulek/build/tree_d)
gives a compute unit (range 12..94) and every bd_mux's DELAY; 4 is the amerge default; of the
link parameters set there, 104 of 109 DACK values are 6, and DELAY = 3 is the commonest non-zero
link DELAY (63 of 172; 87 are 0). I could
not map CapNet operators to emitted instance names, so the lengths are per kind, not per
instance. Untrusted Python: the unit-delay run also has 0 violations with (compute, mux, muxN,
amerge, link DELAY, DACK) = (94, 12, 94, 4, 14, 6), (1, 1, 1, 1, 0, 2) and (30, 30, 30, 30, 8, 6).

The checker (`kChkG`) is C-8t's lumped `kChk` (which supplies every field `GenCell` shares with
`Cell`: wires, data, latch, arbiter, reset) plus `xChk` for the internal nodes. Every LUT field
(`CNode` = H_LUT_SI + H_FB_FIRST, `LutSI` on `genF` of the yosys netlist) is derived inside the
soundness proof through the generated gate lemmas (`f2_gate`..`f6t_gate`, `j2_gate`, `j3_gate`,
`mux_gate`, `arb_gate`, `link_gate`, `steer_gate`, `src_gate`, `uor_gate`, `sym_gate`,
`ff_gate`, `fr_gate`), so the yosys INITs are what the kernel checks against.

## Negative controls (`Wip/Cwitgen/negctl.sh`)

| file | mutation | passes | rejected |
|---|---|---|---|
| `NegSettled` | bd_link op 192's `uack` head (LUT1 buf c) has an inertial delay of 291 ticks; it still moves only to its LUT of the previous tick | lumped `kChk` (H_CELLS) on all 367 operators | `kChkG` on op 192 (Python: only `SETTLED` fails: c falls while the slow head never rose) |
| `NegInit` | fork op 67 (N = 5): chunk C-element INIT bit (leaves 1,0,1,1, q = 0) flipped; the run follows the mutant | | `kChkG` on op 67 |

291 is the smallest such delay that breaks H_CHAIN_SETTLED in this run (bisected in Python):
link 192's controller stays high ~290 ticks waiting downstream. So H_CHAIN_SETTLED is a real
timing condition beyond the lumped models (as O4's `fastfall_hazard` showed on a single chain),
and it is satisfiable in an active whole-network run; this run satisfies it with slack.

## Hypotheses and non-vacuity after this probe

| theorem | hypotheses | active witness |
|---|---|---|
| `CellBind.Gcd.gcd_hw_circuit_safe_gen` (O4) | H_GEN (`GenCell`: H_LUT_SI, H_FB_FIRST, H_CHAIN_SETTLED, H_REQ_PERSIST, H_LEAF_PERSIST, H_WIRE_DI, copied data/select/arbiter/latch/reset fields, H_MUXN_OR, H_R0_ISO, H_PORT_ORDER), H_BUNDLE, H_START_ONCE, a, b < 2^31 | **`gcd_hw_gen_joint_witness`** (12/18 → 6) |
| `CellBind.K.gcd_hw_circuit_safe_genK` | `GenCellK` + same | `gcd_hw_genK_joint_witness` |
| `CellBind.PersistK.gcd_hw_circuit_safe_genP` | `GenCellKP` + same | `gcd_hw_genP_joint_witness` |
| `CellBind.K.ipow_circuit_safe_gen`, `PersistK.ipow_circuit_safe_genP` | `GenCellK` / `GenCellKP`, H_BUNDLE, H_START_ONCE, e < 2^32 | **`Ipow.ipow_gen_joint_witness`** (3, 7 → 2187); before: none |
| `K.xorshift_circuit_safe_gen`, `PersistK.xorshift_circuit_safe_genP` | same | `Xorshift.xorshift_gen_joint_witness` (→ 2008045182) |
| `K.collatz_circuit_safe_gen`, `PersistK.collatz_circuit_safe_genP` | same + `collatzC fuel n = some r` | `Collatz.collatz_gen_joint_witness` (7 → 16) |

H_PIN_EQ is a convention (pins read the driving net's trace; only listed routes are nodes),
not a hypothesis of the Lean statements; the run uses it as stated.

## What it does NOT show

- **One input and one schedule per kernel**: non-vacuity, not testing, not liveness. Every
  node 1 tick (R0 0 ticks), arbiter wins x on a tie, sources offer once, sinks ack in 1 tick.
- **Chain lengths are not pinned by the theorems**: `GenChain` / `GenBufChain` quantify the
  number and wiring of stages, so a 1-stage chain would also satisfy them. The witness uses
  bdc's shapes and representative lengths to make the internal nodes non-trivial; it does not
  show anything about bdc's per-instance tightened lengths.
- **The gate models, not hardware**: zero-delay buses for H_BUNDLE (the tcheck question), no
  glitches (per-node SI), the select / data / grant fields copied from Ops as in O4.
- **Not the rig theorem** (`gcd_rig_all_gen`, `GenCellR`): needs start high at reset (C-wit's
  `r0` channel layer); not attempted.
- Coverage: in gcd_hw, 34 of 175 links, 1 of 9 arbiters (`acc251`) and the 58 untaken-branch
  channels never move (as in 8t's run); fork N ≤ 4, bjoin, steer, src, sink have no internal
  nodes beyond the lumped one.
