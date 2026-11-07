# A-env: mechanised environment model for the LUT hazard audit

Files:
- `formal/lean/Formal/Core/Env.lean`: proved (namespace `Formal.Core.Env`). It imports `Formal.Core.LutAudit`,
  which brings in `LutCells` and `LutTree`.
- `formal/lean/Wip/Env.lean`: the W = 2 bd_link model, plus one conjecture (`sorry`). It is not built.
- Scratch (not in the repo): `/tmp/env/proto2.py` and `/tmp/env/wit2.py`, a Python prototype of the same
  semantics. It was used to find the witness traces and to cross-check the state counts.

## How to check

    cd /home/user/asyncfpga3/formal/lean && ../check.sh Formal/Core/Env.lean

The check needs `LutAudit.olean` in `.lake/build`. That file now exists; `../check.sh Formal/Core/LutAudit.lean
Formal/Core/Env.lean` rebuilds both. Result: `[check] OK`, axiom audit clean, no
`sorry`/`native_decide`. Env.lean alone takes 55 s wall and about 46 s CPU. The kernel `decide +kernel` runs are below.

## The model (what replaces LutAudit's prose)

- **Cell**: the LUTs taken verbatim from `LutCells` (generated from `cells/rtl`). Each LUT's Boolean function is
  `LutAudit.outB`, applied to its free pins in root-first order. Fork branches whose delay matters are explicit `wire`
  elements, each with its own unbounded delay.
- **Environment**: guarded toggles that encode a four-phase handshake. Bundled data may move only inside its window.
- **Semantics**: untimed speed-independent interleaving. One signal changes per step. Any excited element or enabled
  environment move may fire, with unbounded delays (GMW).
- **Timing knowledge**: only the list `prio` of relative-timing assumptions `(fast, slow)`. While `fast` is excited,
  `slow` does not fire. Each assumption is a named Bool field of `LatchAsm`/`LinkAsm`. Every positive theorem is stated
  for one concrete assignment of those fields. For each assumption there is a witness theorem showing that dropping
  it gives a reachable violation.
- **Multi-input changes (MICs)**: the state records, for each LUT pin, whether the pin's last change may still be in
  flight inside the mux tree. It also records `pend`, the set of transitions that were enabled when that change
  happened and have stayed enabled since. A later transition `t` meets the in-flight change at the LUT iff
  `t ∈ pend`, i.e. iff their excitation intervals overlapped. The MIC that a non-firing LUT sees is then
  `old → new`, where `old` is the current pin vector with the in-flight pins flipped back.
- **Check** (`lutOK`): `LutAudit.classify old new ∈ {sic, sHF, dHF}`, and no excitation is withdrawn inside the MIC.
  `lutOK_sem` / `reach_mic_hazard_free` turn this into LutAudit's `StaticHF`/`DynHF` (Eichelberger, Unger/Nowick–Dill)
  on every reachable transition.
- **`persistOK`**: semi-modularity / output persistence. No excited gate or wire is disabled by any other transition,
  and no gate disables an enabled environment move. Environment-vs-environment conflicts count as choices and are
  allowed.
- **Per state**: liveness (some transition is enabled). For bd_link with `linkQ`, also data validity at the receiver.
- **Soundness**: `certify_sound` is the only trusted step. A set `T` (a BST of state codes) must contain the initial
  states, be closed under `succs`, and pass every check; then the checks hold on every `Reach`-able state.
  `reachTree` computes `T` in Lean, and its correctness is never assumed. Negative controls use `witness_sound`
  (it replays an explicit trace and evaluates the failing check) and `not_sound_of_witness`.

Named hypotheses built into the semantics (all in the module docstring):
- **H_SETTLE**: the mux tree settles an input change before any element responds to a transition that was not yet
  excited when that change occurred.
  - Ablation: setting `settle := false` (pure unbounded internal delays) gives `latch_needs_settle`.
- **H_FB_FUND**: a LUT's own firing completes the settling of the changes that caused it. The feedback pin is zero
  delay. This is LutAudit's fundamental mode.
- **H_BUNDLE**: data before request. It is encoded causally by the sender's private `rdy` event, which comes after
  the data moves and before `req`/`e`.
- **H_RST_LONG** (c2 only): reset is released only after q = 0.

## Theorems that check (all in `Formal.Core.Env`)

General: `Tree.mem_of_contains`, `certify_sound`, `mem_succs`, `reach_run`, `witness_sound`, `not_sound_of_witness`,
`classify_sic`, `lutOK_sem`, `reach_mic_hazard_free`.

**bd_c2** (signals a, b, q, rst; two four-phase senders share q, i.e. a join):
- `c2_cert`, `c2_sound`: speed-independent and every MIC is hazard-free; live. 10 states (`c2_states`).
- `c2_mics`: the only MICs are both requests rising together (q = 0) and both falling together (q = 1). Both are
  classified `.dHF`. This is LutAudit's "same direction" case, now derived.
- Negative control: `c2_freeB_hazard` / `c2_freeB_not_sound`. With b unconstrained (a misused merge acknowledge),
  the checker finds a reachable opposite-direction MIC hazard and a withdrawn excitation. 16 states.

**bd_latch pair** (LUT6_2 `bd_latch_u_L38`; signals e = controller node, en = enable branch wire, d0, d1, q0, q1, rdy):
- `latch_cert`, `latch_sound`: with `ruleH` and `ruleL` it is hazard-free, persistent and live. 208 states.
- `latch_mics`: q0 sees 16 distinct MICs, all with en = 0 before and after (data moving while the latch is closed).
  The enable never takes part in a MIC.
- `latch_needs_H`: rule H, as an explicit timing assumption. Without it, d0 moves while the enable branch is still
  falling. This gives a function hazard on q0 (= `latch_close_while_d_moves`).
- `latch_needs_L`: rule L. Without it, the enable falls while q0 is still following D, and the excitation is
  withdrawn. With a zero-delay feedback pin this shows up as non-persistence (= `latch_close_while_q_settles`).
- `latch_needs_settle`: H_SETTLE ablation. Under pure unbounded mux-tree delays, a data change made while the latch
  was closed can still be in flight when en rises. This is the setup half of bundled data, at LUT level.

**bd_link** (Muller stage, `bd_c2n_u` controller plus odd-bit latch `bd_latch_u_L44`, W = 1; signals req, c, ack, en
(wire), d, q, rdy, rst):
- `link_cert`, `link_sound`: with `ruleH`, `ruleL` and `isoEn` it is hazard-free, persistent and live, against an
  arbitrary four-phase receiver. 142 states.
- `link_ctl_mics`: the controller LUT's MICs are exactly LutAudit's two, `req_in↓ ∥ c_next↑` (c = 1) and
  `req_in↑ ∥ c_next↓` (c = 0). The hazardous `req_in↑ ∥ c_next↑` is not reachable. That was prose plus
  `link_unreachable_mic_hazard`; it is now derived.
- `link_data_sound`: with `rxBundle` as well, the receiver always acknowledges the sender's bit. 122 states.
- `link_L_implied_by_rx`: **finding.** If the receiver waits for the data (`rxBundle`), rule L is implied: c falls
  only after ack rises. In a pipe the receiver is the next controller, which does not wait for this latch, so rule L
  stands there.
- `link_needs_H`, `link_needs_L`, `link_needs_isoEn`: each assumption is necessary.
  - Without H: a latch function hazard.
  - Without L: a withdrawn latch excitation.
  - Without isoEn: c can rise and fall before the enable branch follows. The enable wire's excitation is withdrawn,
    which means a runt or a token that is never written. This is Shard B's H_ISO_FORK on the latch-enable
    branch. B's `di_pipe` delays only the control branches and treats the enable branch in its section 5.
- `link_req_leads_data`: the documented "req_out LEADS data_out" (bd_link.v header), derived. Without receiver
  bundling the receiver can acknowledge while q has not yet followed D.

So every exception in LutAudit's prose comes out as an explicit, named, necessary timing assumption. No new hazard was
found in these three cells.

## What does not check, and why

- **bd_link with a W = 2 latch pair** (`Wip/Env.lean`, `link2_sound`, `sorry`). Python finds 1048 states and no
  violation. Compiled `#eval certify` returned `true` on the rxBundle variant (752 states). The kernel run used more
  than 6 GB of RSS within about 60 s, so I killed it (the machine has 15 GB shared by 12 agents).
- **The other cells** (bd_arb, bd_merge, bd_mux, bd_mlink) were not modelled. The time box was spent on the three
  that were asked for. bd_arbiter would need a model of the arbiter's metastable choice (an environment-like
  nondeterministic resolution) and is the most valuable next one, because of LutAudit's two arbiter findings.

## Scaling of `decide +kernel`

| model | states | kernel time (approx.) |
|---|---|---|
| c2 (incl. MIC list, witness) | 10 / 16 | < 2 s |
| latch pair (cert + count + MICs + 3 witnesses) | 208 | about 30 s (c2 + latch file prefix: 38 s wall) |
| link W = 1 (3 certificates + 4 witnesses) | 142 / 122 / 122 | about 15 s |
| link W = 2 | 1048 | > 6 GB RSS, aborted |

Cost per state grows with (LUTs × pins × signals), because every `post` recomputes the excitation masks for each
in-flight slot. The kernel's whnf cache keeps every intermediate term, so memory grows with total work, not with the
state count. Remedies, from cheapest to most work:
1. Pass precomputed `enMask` values through a single `post`, and cache the LUT outputs per state.
2. Split a certificate into chunks across several theorems. The reachable list can be given as a literal (a
   certificate computed outside Lean), so no theorem recomputes the BFS.
3. Write a proved-once reflective checker on `Array`/`ByteArray` that the kernel evaluates with GMP-backed Nat
   operations.
4. Reduce symmetric data bits: by `latch_bit_isolation` the two bits of a pair are independent, which would justify a
   W = 1 compositional argument formally.
The W = 1 link plus the standalone pair already cover the pair LUT's behaviour under the same environment discipline.
What is NOT covered is the pair inside the link, where en is shared by both outputs (a fan-out of 2).

## Comparison with Petrify / Workcraft

This is the standard speed-independence check on a state graph: output persistence (semi-modularity) plus
deadlock freedom, against an environment STG, with relative-timing assumptions as in Cortadella et al.'s
lazy-transition-system RT methodology. The differences:
- **Gate model.** Petrify/Workcraft check complex gates as atomic (no internal hazards). Here a LUT is a mux tree:
  concurrent input changes are checked for Eichelberger/Unger function hazards against the exact INIT from the RTL,
  under H_SETTLE. The latch-pair results depend on this.
- **Trust.** The tools are unverified C++ programs. Here the kernel checks the certificate, and the semantics is a
  few dozen lines of Lean definitions.
- **Scale.** This is much smaller. Workcraft/MPSat handles 10^6+ states via unfoldings, while this approach is
  practical to about 10^3 states per certificate today.
- **Input language.** No STG language here; the environment is hand-written guards. A translator from Workcraft
  `.g` files would be a sensible next step.

## Verdict

**It works.** bd_c2, bd_link (W = 1) and the bd_latch pair are done. All of LutAudit's protocol prose for these cells
is replaced by kernel-checked state-graph results, and the timing exceptions (rules H and L, the isochronic enable
branch, receiver bundling) appear as named, provably necessary assumptions.
- Effort to finish the W = 2 link and the remaining cells: about 2-3 days. Most of that is the encoding work under
  remedies 1-2 above, plus about 1 day per arbiter/merge/mux model.
- What it buys: a changed INIT or pin map in `cells/rtl` regenerates LutCells and re-runs these certificates, so a
  protocol-level hazard regression breaks the build. Each timing rule that `verify/tighten.py` checks post-route
  (H, L) now has a proof that it is needed.

## Fidelity

- **LUT**: the Boolean function from the RTL INIT. The hazard notion is LutAudit's, so its static results transfer
  to the LutTree mux tree through `lut_static_glitch_free` (under `H_sram` and `H_mux_kleene`).
- **H_SETTLE**: an assumption about the ratio of LUT internal settling to the fastest response of any element.
  - Plausible for environment actions and for routed wires.
  - Weakest where a LUT output feeds another LUT through a short wire.
  - Test: GLS with the routed SDF, measuring each LUT's pin-to-O spread against the minimum causal path between two
    transitions that share a pin.
- **Wires**: only the enable branch is a separate delayed element. The other fork branches of c (req_out, ack_in,
  the feedback pin) are isochronic. Shard B's `di_pipe` covers the control branches, and H_FB_FUND covers the
  feedback (B's H_FB_FAST, which is tested the same way).
- **Inertial versus transport**: atomic firing means no runts are propagated. A withdrawn excitation is reported as a
  violation rather than modelled.
- **Assumptions and how to test them**:

  | assumption | meaning | how to test |
  |---|---|---|
  | rule H | enable branch before the sender's next data move | `verify/tighten.py` rule H |
  | rule L | latch output before enable fall | `verify/tighten.py` rule L |
  | isoEn | enable branch before the receiver's acknowledge | routed enable-net max delay against the min round trip through the receiver |
  | rxBundle | latch output before the receiver's acknowledge | `verify/tighten.py` rule I / the measured req_out lead |
