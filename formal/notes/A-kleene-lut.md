# A-kleene-lut: Kleene semantics of a LUT at the INIT-table level (track 4, shard A)

## Files

- `formal/lean/Formal/Core/Kleene.lean` (proved). This is the shared `K3` API: `K3`, `⊑`, `ofBool`, `merge`,
  strong-Kleene `not/and/or`, tuple helpers `vcons/vtail/setAt/ofList`, `Consistent`,
  and `Decidable (∀ v : Fin k → K3, _)` / `(∀ x : Fin k → Bool, _)` instances. It uses core Lean only, with no Mathlib.
- `formal/lean/Formal/Core/Lut.lean` (proved). It holds `Lut k`, `Lut62`, `addr`, `eval`, `keval`
  (the mux tree), `kevalSpec` (the set specification), the hazard theorems, and the INIT constants of every LUT in
  `bd_ce.v`, `bd_arb.v` and `bd_latch.v`. It imports only `Formal.Core.Kleene`.
- `formal/lean/Wip/Kleene.lean` holds the `decide` timing benchmarks. They all check, but they are not claimed because they are slow.

Check (from `formal/lean`, after Kleene's olean exists, e.g. via the lead's `lake build`):

    ../slot.sh lake env lean Formal/Core/Kleene.lean     # ~3 s
    ../slot.sh lake env lean Formal/Core/Lut.lean        # ~5 s

I checked both without `lake build`. I compiled Kleene to a scratch olean (`lean -o /tmp/kleene/olean/...`) and set
`LEAN_PATH=/tmp/kleene/olean:$LEAN_PATH`. Both files give no output, with no sorry, admit, axiom,
native_decide or bv_decide. `#print axioms` shows only `propext` and `Quot.sound`, plus `Classical.choice`
in `keval_eq_X_iff`.

## API (for shards B and C)

- `Formal.Core.K3` has the values `zero | one | X`. `a ⊑ b` (`K3.Le`, written after `open Formal.Core K3`) means `a = X ∨ a = b`.
  `K3.merge a b` = `if a = b then a else X` is the glb, i.e. a mux with an X select.
- `Lut k := ⟨init : BitVec (2^k)⟩`. `addr x = Σ x_i·2^i`, with I0 as the LSB, as in the Xilinx INIT convention.
  `Lut.eval L x = INIT[addr x]`.
- `Lut.keval L v` is the mux tree. I0 is at the root, which is the order of the GLS `SLICE_LUTX`. `Lut.kevalSpec L v` is the literal
  "1 if every consistent INIT entry is 1, 0 if every one is 0, else X".
- `Lut62 := ⟨init : BitVec 64⟩`. `o6 : Lut 6` covers I0..I5, and `o5 : Lut 5` covers I0..I4 over `INIT[31:0]`.
- Pin vectors are built with `bvec [a, b, …] k` (Bool) and `kvec [..] k` (K3, padded with X).
- `Formal.Core.Init.<cell>` holds the INIT constants listed below.

## What checks (theorem names, all in `Formal.Core`)

| theorem | statement |
|---|---|
| `Lut.keval_ofBoolVec` | on Boolean inputs, `keval = ofBool (eval)` (for all k and all INITs) |
| `Lut.keval_mono` | `VLe u v → keval u ⊑ keval v` (monotone in the information order) |
| `Lut.keval_eq_ofBool_iff` | `keval v = ofBool b ↔ ∀ x, Consistent v x → eval x = b` |
| `Lut.keval_eq_kevalSpec` | the mux tree equals the set specification, so the tree order is irrelevant |
| `Lut.keval_eq_X_iff` | X iff two Boolean resolutions disagree |
| `Lut.keval_hull_eq_ofBool_iff` | a transition `x → x'` with any set of changing inputs is defined as `b` iff the whole subcube gives `b` |
| `Lut.keval_setAt_X_iff` | with one input at X, the output is `b` iff both values of that input give `b` |
| `Lut.no_static_hazard_single` | **a single input flips and the Boolean output is unchanged, so the Kleene output with that input X is that value** |
| `Lut.single_change_visible` | a single flip that changes the output gives X (it is never masked) |
| `Lut.hull_single` | `hull x (flip j) = setAt (ofBoolVec x) j X` |
| `Lut.two_change_hazard`, `Lut.not_no_static_hazard_two` | **this fails for two simultaneous changes**: XOR2 (`4'h6`), 00→11 |
| `Init.bd_c2_two_change_hazard` | the C-element itself: `a b = 01 → 10`, q=0, holds 0 at both ends, and the hull is X |
| `Init.bd_c2_contain` | **X containment**: q = X, rst = 0, a = b ⇒ output = a |
| `Init.bd_c2_hold_X` | q = X, a ≠ b ⇒ output X |
| `Init.bd_c2_reset` | rst = 1 ⇒ output 0 for all a, b, q ∈ K3 |
| `Init.*_eval` (23 theorems) | the Boolean function of every library INIT, by `decide`, which checks the transcription and the RTL comments |

The Boolean functions proved for each INIT (these confirm the RTL headers):
- `bd_c2` = ¬rst·maj(a,b,q). `bd_c2_set` = rst + maj. `bd_c2n` / `bd_c2n_set` use maj(a,¬b,q).
- `bd_c3` / `bd_c4` / `*_norst`: all-high, or q held while any input is high.
- `arb_grant`: O5 = g1 = r1·q, and O6 (I5 = 1) = g2 = r2·¬q.
- `arb_state`: O6 = q = rst + (A0 ? q : maj(r1,¬r2,q)). O5 = R0 = r1·q + r2·¬q. This confirms the
  "q frozen while A0 high" claim at the INIT level.
- `latch_pair`: O5 = en ? d_i : q_i, and O6 = en ? d_j : q_j. `latch_odd` is the same. `latch_rst0/1` are ¬rst·mux / rst + mux.
- `delay_buf` = a. `delay_and` (4'h8) and `delay_or` (4'hE).
- `datamux_pair`: O5 = s ? b_i : a_i, and O6 = s ? b_j : a_j. `datamux_odd` is the same.

INIT constants and their sources:
- bd_ce.v:34 `bd_c2`, :40 `bd_c2_set`, :49 `bd_c2n`, :55 `bd_c2n_set` (also bd_arbcell's state, bd_arb.v:89),
  :62 `bd_c3`, :70 `bd_c4`, :81 `bd_c2_norst`, :86 `bd_c3_norst`.
- bd_arb.v:91/249 `arb_grant`, bd_arb.v:245 `arb_state`.
- bd_latch.v:38 `latch_pair`, :44 `latch_odd`, :64 `latch_rst0`/`latch_rst1`, :126/135/180 `delay_buf`,
  :116/138/183 `delay_and`, :116/138 `delay_or`, :209 `datamux_pair`, :215 `datamux_odd`.
- bd_merge, bd_mux, bd_ctl and the other files were out of scope and are not transcribed.

## The decide question (measured; see Wip/Kleene.lean)

These are wall times for a fixed INIT (bd_c2), quantified over all 3^6 = 729 Kleene vectors:

| statement | `decide +kernel` | `decide` |
|---|---|---|
| X-containment over all 729 | 2.5 s | 3.6 s |
| one-step monotonicity, 729 × 6 | 21 s | 45 s |
| one-step monotonicity at I0, 729 | ~7 s | |
| mux tree = spec, 729 × 64 resolutions | 83 s | |

- **Verdict:** `decide` handles "∀ 729 Kleene inputs of one fixed 6-input INIT" in seconds.
  - `decide +kernel` is kernel reduction only and adds no axiom. It is not `native_decide`, and it is about 2× faster than the elaborator path.
  - The elaborator path needed `maxRecDepth 100000` as a precaution. `+kernel` needed nothing.
  - It works because `BitVec.getLsbD` on a literal reduces through GMP-accelerated `Nat.testBit` in the kernel.
- Statements quadratic in the vectors are out of reach (729² ≈ 5·10⁵, projected over 30 min), as are statements over INITs (2^64).
  Those need structural lemmas. Monotonicity, spec equivalence and hazard freedom are already proved structurally for every k and every INIT.
- Recommendation for shards B/C: use the general theorems, and use `decide` only for per-cell facts. For K3 universals
  over a few named pins, use `cases a <;> cases b <;> … <;> decide`, which is instant.

## Fidelity

- **INIT addressing** is exact and matches the 7-series convention. I0 is the LSB, and O5 reads `INIT[31:0]` over I0..I4.
  23 decide proofs reproduce the functions the RTL headers claim, so the transcription is checked.
  Caveat: these are logical pins. After place-and-route, nextpnr permutes physical pins and rewrites the INIT
  (the GLS pre-applies `X_ORIG_PORT_A<n>`). The function is the same, but a fidelity proof about the physical LUT
  needs that permutation. Track 11 (netlist import) should carry it.
- **Kleene semantics is a HYPOTHESIS about silicon, not a theorem** (call it `H_kleene_lut`). The claim is that a LUT
  whose inputs are each a valid level or "in transit/intermediate" outputs a valid level whenever every
  INIT entry consistent with the valid inputs agrees.
  - Structurally, it needs each 2:1 pass-transistor stage, with an intermediate select and equal
    data, to pass the data level, which the output buffer then restores.
  - Plausible for NMOS pass gates plus level restorers. The data reaches the output through partially-on paths
    that all carry the same level, so the output is slow but correct.
  - Not documented by Xilinx. There is no transistor schematic, and this is folklore-level
    (see A-lut-tree.md for sources).
  - It is a **static** statement only. It says nothing about dynamic hazards
    (0→1→0→1 on a changing output; Kleene just says X), nor about the timing of the restored
    level. A mid-rail select with *unequal* data gives a mid-rail output (X): that is how the arbiter's
    metastable q reaches g1/g2.
- **Agreement with the research GLS:** `SLICE_LUTX` in `origin/claude/research:cells/gls/prims.v` is a
  Verilog `?:` mux tree with A1 at the root. IEEE 1364 `?:` with an X select returns the bitwise merge
  (equal bits pass, others X). That is exactly `kevalT`, including the tree order, so its zero-time X behaviour
  equals `Lut.keval` (Z is treated like X).
  - The GLS evaluates in zero time behind one inertial specify delay per pin. So a single-input change produces
    one output event, which is consistent with `no_static_hazard_single`.
  - Multi-input changes within one inertial window are swallowed. The Kleene `hull` theorems say exactly which of
    these could glitch on silicon (`two_change_hazard`, `bd_c2_two_change_hazard`). The GLS cannot show them.
- **How to test `H_kleene_lut`:**
  1. **Board:** a LUT2 configured as AND(a, b) with b = 0 held, and a toggled at a high
     rate through a long route so that its edges are slow. The output drives the clock of a toggle FF or ripple counter.
     The hypothesis predicts a count of 0.
     - Control: XOR with both inputs toggled from one source through two routes of different length. This should count
       glitches (`two_change_hazard`).
     - Repeat with `bd_c2` held (a = 0, b = 1) and a single input moving. The prediction is no output event.
  2. **GLS:** the current GLS cannot falsify it (see above). A transistor-level SPICE model of a
     generic NMOS mux tree with level restorer could check that the masked case stays at the rail.
- What the theorems buy:
  - They give shards B and C one checked INIT table per library LUT.
  - They give a proved bridge from per-LUT Kleene behaviour to "single-input-change hazard freedom".
    That is the property bundled-data control relies on, because in a correct four-phase run every C-element and latch
    sees one input change at a time.
  - They give a precise statement of when that fails: opposite-sense changes on a C-element, i.e. the arbiter's runt
    condition, now a theorem in Kleene form.

## Verdict

**Works.** Everything asked for is proved for every k and every INIT, with no sorry, in about 8 s of checking. `decide` handles fixed-INIT
6-input statements over all 729 Kleene vectors in seconds, using `decide +kernel` with no extra axioms. Structural lemmas
are needed (and given) for anything over pairs of vectors or over INITs.

Effort to finish:
- Done for the INIT level.
- Next (about 1 day): Kleene fixed points for feedback LUTs (C-element/latch loops: the least fixed point
  of `keval` with q as an input) on top of `Lut.keval_mono`. This overlaps `Formal.Core.Ternary`'s `iterA`.
- Also about 1 day: transcribe bd_merge/bd_mux/bd_ctl INITs.

**Duplication to resolve (lead):** `Formal.Core.Ternary`, `Formal.Core.LutTree` and `Formal.Cells.Prelim` each
define their own `K3`, in separate namespaces, so nothing clashes. They should be ported to `Formal.Core.K3`.
`LutTree` addresses INIT MSB-first with A6 at the root. Its `evalTree_eq_tableEval` and this file's
`keval_eq_kevalSpec` both reduce to the same order-free specification.
