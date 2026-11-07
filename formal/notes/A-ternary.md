# A-ternary: soundness of ternary (Kleene) simulation for the binary delay semantics

Probe: link track 4 (Kleene LUT semantics) to track 3 (delay channels).
Files:
- `formal/lean/Formal/Core/Ternary.lean` (proved, namespace `Formal.Core.Ternary`)
- `formal/lean/Wip/Ternary.lean` (statements with `sorry`)
- this note

## How to check

```
cd formal/lean && ../slot.sh lake env lean Formal/Core/Ternary.lean
```
This checks with no output: no errors, no warnings, no `sorry`/`axiom`/`native_decide`.
`#print axioms` (run on a scratch copy): `soundA`, `noGlitchA`, `settleResultB`,
`resultB_fix`, `bdc2_no_static_hazard`, `bdc2_settles` use only `propext`,
`Classical.choice`, `Quot.sound`. `bdc2_single_input_ok` uses `propext`, `Quot.sound`.
`kext_mono` uses `propext`. The file imports nothing: core Lean only, about 4 s.

## What is proved (exact names)

**Model.**
- `K3`, `⊑` (`K3.Le`), `K3.meet`, `K3.sel` (one 2:1 mux), and `kext` (the Kleene extension of `f : 𝔹^k → 𝔹` as a LUT mux tree). These are local minimal copies. They use the same constructor names and order as `Formal.Core.Kleene`, and `kext` has the same recursion as `Formal.Core.Lut.kevalT`, so unifying is mostly renaming.
- `Net ι ν` is a network. It has inputs `ι` and nodes `ν` (one node per gate output). It holds a Boolean excitation `fb` and a ternary model `F`, plus two named hypotheses: `mono` (F is monotone) and `ext` (F extends fb). The theory uses nothing else about `F`, so any sound Kleene gate model fits.
- `LutNet` / `LutNet.toNet`: a network of LUTs. Each pin is wired to an input or to a node, and the gate is `kext` of its table. `mono` and `ext` are proved, not assumed.
- `Causal N c σ` is the binary delay semantics. Discrete time, inputs `c t`, node values `σ t`. At each step a node either holds its value, or takes its Boolean gate function applied to samples of each of its inputs taken at **arbitrary earlier times, chosen separately for each wire**.
- `GStep` is the GMW step (unbounded gate delay, ideal wires). `gmw_causal`: every GMW run is `Causal`.
- `Stale N c σ D` is bounded staleness. From time `D` on, each node value is its gate function of samples taken within the last `D` steps.

**(1)** `kext_bool` (kext extends f) and `kext_mono` (kext is monotone in ⊑).

**(2) Algorithm A.**
- `stepA` is `t ↦ t ⊓ F u t` and `iterA` iterates it.
- `iterA_antitone`: the iterates decrease.
- `iterA_fix`: the iteration is stationary after `|ν|` steps, given an enumeration `l` of the nodes. The proof is a generic measure argument, `stationary_of_measure`, with `ndef`/`nX`.
- `resultA_postfix`: the result `tA` is a post-fixed point, `tA ⊑ F u tA`.
- `le_iterA` / `resultA_greatest`: `tA` is the **greatest** sound certificate. Any `p ⊑ s0` with `p ⊑ F u p` satisfies `p ⊑ tA`.

**(3) Soundness.**
- `sound_postfix`: any post-fixed point that covers the start state and whose inputs are covered at all times covers every state at every time, in every `Causal` behaviour.
- `soundA`: this holds for `tA`, with `u = a ⊓ b` and any input sequence whose entries each come from `a` or `b`. Inputs may change in any order, and may even bounce back and forth.
- `noGlitchA`: a node that is binary in `tA` never changes.

**(4) Algorithm B / settling.**
- `iterB_mono`: the B-iterates increase.
- `iterB_fix` / `resultB_fix`: B reaches a fixed point within `|ν|` steps.
- `settleB`: if inputs equal `b` from `T0` on and the behaviour is `Causal` and `Stale D`, then the k-th B-iterate covers every state from time `T0 + k·D` on.
- `settleB_value` / `settleResultB`: a node that is binary in `tB` equals that value from `T0 + |ν|·D` on and stays there. This is the full settling half, not only "covers the final state".

**Example: `bd_c2`** (`cells/rtl/bd_ce.v`, `INIT 64'h00E8_…`).
- It is modelled as one LUT4, pins `I0=a, I1=b, I2=q (own output), I3=rst`, table `0x00E8`. Pins `I4` and `I5` are tied to 0, so only `INIT[15:0]` is ever addressed.
- `bdc2_fb`: the cell computes `maj(a,b,q)·¬rst`, by `decide`.
- `bdc2_a_rise_hold`: when `a` rises with `b = 0, q = 0`, `tA = 0`.
- `bdc2_b_rise_fire`: when `b` rises with `a = 1`, `tA = X` and `tB = 1`.
- `bdc2_rst_rise`: when `rst` rises while holding 1, `tA = X` and `tB = 0`.
- **`bdc2_single_input_ok`**, by `decide` over all 8×2 states and all 3 pins. For every stable state and every single-input flip, (i) `tB` is binary, so the cell settles deterministically, and (ii) if `tB` equals the old `q`, then `tA` is already that value, so there is no static hazard.
- `bdc2_no_static_hazard` and `bdc2_settles` carry this over to every `Causal` behaviour, and to every `Stale D` behaviour.
- `bdc2_two_input_hazard` shows the check catches real problems. If `a↑` and `b↓` happen together, `tA = X` **and** `tB = X`: the feedback can latch the glitch, so the final value is not determined.

## What is not proved (Wip/Ternary.lean) and why

- **W1, completeness** (`completeA_wired`, `completeB_wired`), from Brzozowski–Seger. If a node is `X` in A (resp. B), some GMW run glitches (resp. fails to settle).
  - This holds only for the **wire-delay expansion** `wired` (a buffer node on every LUT pin).
  - With ideal wires, ternary simulation is only conservative. Example: a LUT with `I0 = I1 = x` and table `I0∧¬I1`.
  - Proof effort: about 1–2 days. It needs a constructive scheduling argument that follows the A-iteration.
  - It is not needed for any safety claim. Soundness is what certifies hazard-freedom. Completeness only says a reported `X` is real.
- **W2, `settleB_fair`**: settling under unbounded delay with weak fairness, with no bound `D`. This is the same induction as `settleB`, but over rounds. About half a day.
- **W3**: a generic `checkCell : LUT INIT → Bool` covering all stable states and all single-input flips, with its soundness theorem. `allVecs` is defined. `mem_allVecs` and the glue to `noGlitchA`/`settleResultB` remain. About half a day. Until then, each cell gets its own `decide` theorem in the style of `bdc2_single_input_ok`. That takes one line per cell and checks in under a second.
- **W4, inertial delay → `Stale`.** It is only stated in prose (see below).

## How the delay semantics relates to transport, inertial and bounded delay with wire delays

- **Soundness is proved for `Causal`, the weakest causal semantics.** Each node, at each step, holds or takes `f(samples)`, with every input wire sampled at its own past time. This covers all of the following:
  - **Transport (pure) delay on gates and on every wire separately.** Gate output at `t` is `f(x₁(t−d₁), …, xₙ(t−dₙ))`, where `dᵢ` is wire plus gate delay. Each sample is at its own past time.
  - **GMW** (unbounded gate delay, ideal wires): `gmw_causal`.
  - **Inertial channels** after an ideal gate. In `Formal/Core/Delay/Inertial.lean`, the output at `u` is `(f∘x)(τ)` for some `τ ≤ u−Δ`.
  - **Bounded or unbounded variants and mixtures of all of these.**

  So the no-glitch half (`noGlitchA`) needs no delay hypothesis at all beyond causality and discrete time. Mendler–Shiple–Berry's caveat (ternary simulation is *not exact* for the up-bounded inertial model) is about **exactness, not soundness**: inertial filtering only removes behaviours.
- **The settling half needs a bound.** `Stale D` is the hypothesis:
  - It holds for bounded transport delay with every path delay at most `D` time steps.
  - For an inertial gate it does not hold in general. If the excitation keeps toggling faster than the rejection window, the output can hold an arbitrarily old value. That case is already one in which B gives `X`, but the formal link is W4.
- **Discrete time.** One time step is a resolution unit, for example 1 ps. Real-time traces map to discrete ones by sampling, given finite variability. That bridge belongs to the Trace probe (`Formal/Core/Trace/Bridge.lean`) and is not used here.

## Fidelity to 7-series silicon (gate-fidelity)

| Primitive / assumption | Model here | Status | How to test |
|---|---|---|---|
| LUT output for binary pins | `tbl` = `INIT[addr]`, `I0` the LSB | exact (UG474); `bdc2_fb` checks the INIT | GLS with unisim LUT6 |
| LUT under a changing pin | `kext` mux tree: a mux whose select is X outputs `meet` of its data | **hypothesis** (field `Net.mono`/`ext`, discharged for `kext`); the physical claim "equal data ⇒ clean output while the select is mid-rail" is the Kleene-LUT hypothesis of `A-kleene-lut.md` | board: toggle one LUT pin whose cofactors are equal and look for runt pulses on a counter/TDC; GLS cannot test it (GLS is binary) |
| Delays | arbitrary per-wire sample times (`Causal`) | sound for every delay assignment, so no delay numbers are needed for the no-glitch claim | none needed |
| Settling bound | `Stale D` | **hypothesis**. `D` must bound the max LUT+route delay over the loop (prjxray slow-max) | GLS with SDF max corner; on the board, measure `T0 + D` with a TDC |
| Each LUT pin separately buffered | `kext` treats pins independently (wire-delay reading) | faithful; it also explains why ideal-wire reasoning would be unsound on silicon | n/a |
| Single node per LUT, output = feedback wire | `bdc2.pin 2 = inr ()` | faithful to `bd_c2` (the feedback is an internal route, kept by `(* keep *)`) | n/a |
| Metastability | not modelled; `X` is "may be either / in transit" | an arbiter needs the M-value of Friedrichs et al.; out of scope | — |

## Verdict

**Works.** All four requested results are proved, together with the full bd_c2 single-input check. The checked file is 700 lines, uses core Lean only, and checks in about 4 s.

Effort to finish:
- W3 generic checker: about 0.5 day.
- W2: about 0.5 day.
- Unifying with `Formal.Core.Kleene`/`Lut`: about 0.5 day. Replace the local `K3`/`kext` with `K3`/`kevalT`. The `Net` interface (`mono`, `ext`) is exactly what `Lut.keval_mono`/`keval_ofBoolVec` provide.
- W1 completeness: 1–2 days. Optional.

## What it buys the project

A **decidable, delay-independent check of hazard-freedom** for every LUT cell. For each cell INIT, each stable state and each allowed input transition (single-input here, or any input cube the protocol permits):
- `tA` binary on an output means that output **cannot glitch under any delay assignment**: transport, inertial, wire or gate, bounded or not.
- `tB` binary means the output **settles deterministically** within `|ν|·D` of the last input change.

Each such fact is one `decide` per cell, as in `bdc2_single_input_ok`. The theorems `noGlitchA`/`settleResultB` turn it into a statement about all binary behaviours. The same theorems apply unchanged to multi-LUT networks: algorithm A runs `|ν|` iterations over the whole netlist. So the check scales from a cell to a composed controller, without enumerating interleavings.

The check is not vacuous. `bdc2_two_input_hazard` shows it flags the latched-glitch case of opposite-sense double changes. That is exactly the case the four-phase protocol must exclude, and it becomes the protocol hypothesis that track 5 must discharge.
