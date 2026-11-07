# B probe G5a: mux and muxn3 contracts in C's interface

Shard B, Phase 3, gap G5 of `B-contracts.md` for `bd_mux` and `bdc_muxn3`. 2026-10-27.
Core Lean, no Mathlib.

File (CLAIMED, checks clean): `formal/lean/Formal/Cells/ContractsMux.lean` (665 lines).
Imports (read-only, through their oleans): `Formal.Cells.ContractsB` (and through it
`Contracts`, `ContractsOps`, `OpsTimed2`, `OpsTimedMux`), `Formal.Cells.OpsHold` (and through it
`MuxN3Timed`). No shared definition added or changed. New definitions are local to this file:
`b2` (a bit as a value) and the witness channels.

## Check

    cd /home/user/asyncfpga3/formal/lean
    # OpsHold had no olean in the build dir; build it first (once):
    PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/OpsHold.lean \
      -o .lake/build/lib/lean/Formal/Cells/OpsHold.olean -i .lake/build/lib/lean/Formal/Cells/OpsHold.ilean
    PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/ContractsMux.lean
    python3 ../scan.py Formal/Cells/ContractsMux.lean

- `ContractsMux.lean`: no output, about 4 s. `scan.py`: clean (no `sorry`, `admit`, `axiom`,
  `native_decide`).
- `#print axioms` (scratch copy) on `mux_contract`, `muxn3_contract`, `idx_cnt`, both witnesses and
  both `witness_values`: `[propext, Classical.choice, Quot.sound]` only.
- The lead must add `Formal.Cells.ContractsMux` to `Formal.lean` (after `ContractsB`, `OpsHold`).

## Theorems (all proved)

| theorem | statement |
|---|---|
| `idx_cnt` | the lemma G5 asked for: on an enumerated token `k` (`g k`), B's `idx κ k` = C's `cnt g k` (from `enum_cnt` and `κ_idx`) |
| `bus_eq` | two values `< 2^W` with the same low `W` bits are equal (assembles B's per-bit theorems into C's `Nat` bus) |
| `order_of_steps` | the four half-step inequalities give strict interleaving `r j < a j < r (j+1)` |
| `mux_x_le_E`, `mux_y_le_E` | input request edge (even AND odd) ≤ the selected join's node edge for the consuming control token |
| `mux_chain` | `γ j ≤ E j < Z j < ζ j < Z (j+1)`, and `γ j < Wzc.fst (ζ j) < γ (j+1)` |
| `mux_x_order`, `mux_y_order` | `ξ j < rx XA κ0 j < ξ (j+1)` (input channel, on x's own tokens), y likewise |
| **`mux_contract`** | see below |
| `mn3_x_le_E`, `mn3_ζ_le_XA`, `mn3_chain`, `mn3_x_order` | the same for the 3-way mux, per input `i < 3` |
| **`muxn3_contract`** | see below |
| `MuxContractWit.witness`, `Mn3ContractWit.witness` | non-vacuity: every hypothesis of each contract discharged on a unit-delay run |
| `…witness_values` | not degenerate: 2-way output tokens carry 1, 0, 0, 1 (x, y, x, y); 3-way 1, 0, 1, 0 (inputs 0, 1, 2, 0) |

**`mux_contract`.** Hypotheses: exactly `mux_ok_static`'s (`MuxGates` with the real INITs, `MuxEnv`,
`MuxCausal`, `MuxStatic`, reset sequencing) and, for every bus bit `n < W`, exactly
`OpsHold.mux_data_hold_fall`'s (`DmRel` with the real `bd_datamux` INITs, `MuxDataEnv`, the
hold-to-fall sender contracts `MuxHoldF`, `MuxDataStatic`), plus the named hypotheses below.
Conclusions:
1. the output channel `cz` is a FULL `Port (ch cz) Z ζ (v cz)`: z_req is `Tok 0` on `Z`, z_ack is
   `Tok 0` on `ζ` (the server's, from `MuxEnv.H_ZA`), `0 < Z 0`, `Z j < ζ j < Z (j+1)`, and the bus
   holds `v cz k` on `[Z(2k), ζ(2k+1))` (C's `Held`, from G3's hold-to-fall theorem);
2. x_ack and y_ack, re-indexed on their own tokens, are `Tok 0` (the input ports' ack halves);
3. strict interleaving on cx, cy, and on the control channel as seen by the control sender
   (`γ j < Wzc.fst (ζ j) < γ (j+1)`);
4. C's `MuxEv ρ v sel cc cx cy cz` verbatim; with ports on all channels `mux_spec` gives
   `OpProto ∧ OpData (muxEq …)`.

**`muxn3_contract`.** Same shape: `muxn3_ok_static`'s hypotheses, per bit
`OpsHold.muxn3_data_hold_fall`'s (`Gate DM5` with the real LUT5 `32'hF0AA_CCF0`, `MN3DataEnv`,
`MN3HoldF`, `MN3DataStatic`), and the named hypotheses. Conclusions: full `Port` on `cz` (z_req is
the line's last stage `ln P.N`), each `in_i_ack` on input `i`'s tokens `Tok 0`, interleaving on every
input and on the control channel, and C's `MuxNEv ρ v sel cc cxs cz` (so `muxn_spec` gives
`muxnEq`). `range` comes from `MN3Env.H_RANGE` (H_S_RANGE) via `H_SEL_VAL`.

## Hypotheses added (beyond B's theorems), each named in the statement

- **`H_ES`, `H_EC`, `H_EX`, `H_EY` ≥ 1** (2-way; for the 3-way `H_ES` is already in `MN3Causal`, the
  rest are `H_EC`, `H_EX`): the partners' handshake latencies are positive. Needed for STRICT
  interleaving (B's causality is `≤`). GLS: no partner answers in zero time (SDF minima > 0).
- **`H_FWD_POS`**: `1 ≤ wo + Lor.lo + Dz.lo` (2-way), `1 ≤ wo + Lo.lo + Dl` (3-way): the join → OR →
  delay line → server path has positive minimum delay. Gives C's causality `ρ in (2i) < ρ cz (2k)`.
- **Reset quiet** `H_QUIET_Z`, `H_QUIET_XA`, `H_QUIET_YA` (`H_QUIET_A i`) with `H_TZ`, `H_TX`, `H_TY`
  (`H_TA i`): every mux-driven wire is 0 before B's clean window starts (`Tz`, `Tx`, `Ty`; 3-way
  `ffT … To N`, `Ta i`) and that window starts before its first edge. Same as the steer's
  `H_QUIET_*`. GLS: the wire is 0 from power-up to its first edge. `ResetGcd` proves the control
  nets settle low under reset but is not yet tied to these traces.
- **G2 identifications** `hρc hρx hρy hρz hαz hreqz hackz` (3-way: `hρx i`). See the convention below.
- **`H_SEL_VAL`**: B's select of control token `k` (`sv k`) is C's `sel (v cc k)` (as for the steer).
- **Bus** (B's data theorems are per bit; C's channel value is a `Nat`):
  - `H_BUS`: the output bus value is `< 2^W` and its bit `n < W` is the bit-`n` LUT output `z n`;
  - `H_X_VAL`, `H_Y_VAL`: the senders' per-bit token values `xv n m` are the bits of C's `v cx m`;
  - `H_X_W`, `H_Y_W`: input token values fit in `W` bits;
  - `H_Z_TOKVAL`: the output token's value is DEFINED as the bus value at its offer instant `Z(2k)`
    (C's `offer_val` reading). This is a definition of `v cz`, not a physical assumption; the
    theorem then proves the bus holds that value over the whole window and that it equals the
    selected input token's value.

## G2: the observation-point convention used

**Every channel is observed at its consumer's pins; each cell owns its output wires.** Applied to
B's mux model:
- the mux's driven traces already sit at consumer pins: `zr` at the server's pin (`Dz` includes the
  wire), `xak`, `yak` at the clients' pins (`Wxa`, `Wya`); 3-way: `ln P.N` (the wire to the server is
  folded into the last stage), `ak i` (`Wak i`). So the output halves need no re-statement.
- B's input traces `x`, `y`, `ctl`, `za` (3-way `x i`, `ctl`, `za`) are read as the channel traces at
  their observation point, and B's input arcs `Wx`, `Wy`, `Wc0`, `Wc1`, `Wzx`, `Wzy` (3-way `Wx i`,
  `Wc i`, `Wza i`) as the residual arc from that point to the physical LUT pin.
  - For a single-pin input (x_req, y_req, in_i_req) the residual is zero, and the sender owns the wire
    (its latency `Ex` is then pin-to-pin, including its output wire).
  - **Refinement needed for multi-pin inputs.** ctl_req (2 join pins; 3 decode pins in the 3-way)
    and z_ack (2 (3) ack C-element pins) fan out INSIDE the cell. A `Ret` arc has non-negative delay,
    so the reference point must lead every pin it feeds. "The consumer's pins" therefore has to mean
    a single reference point on the net from which all of the cell's pins are reached by FIFO arcs:
    the in-cell branch point, not any one pin. This is exactly B's model. A rigid "one LUT pin" reading
    would require re-proving B's theorems with a skew term instead.
- **The control channel's acknowledge is the server's z_ack seen at the CONTROL SENDER's pin**,
  `Wzc.fst ∘ ζ`. The mux does not drive it (the server owns all branches of its net). The contract
  proves the ctl channel's interleaving with that ack. The `Tok` half of that wire is the server's.
- **Not the mux's to give**: the input channels' request `Tok` and data window (senders), and the
  ctl channel's ack `Tok` (server). With those partner halves, every touched channel is a `Port`.

## What did not work / what is not done

- Everything attempted is proved. No unproved goals.
- **Two unlinked select drivers.** `bd_mux` feeds ONE `s` net to the joins (`uj0`, `uj1` I2) and to the
  datamux. In B's hypotheses the joins' select pins (`sx0`, `sx1`, `MuxEnv.H_S_PIN*`) and the datamux's
  select driver (`s`, `MuxDataEnv.H_S_DATA`) are independent traces. The theorem is sound (it is more
  general), but the 2-way witness uses two different drivers: `sx` (Lt's control run, released
  after ctl_ack rose) at the joins and `sF` (held to ctl_ack fall) at the datamux. A one-select joint
  witness needs Lt's control run re-built on `sF`. That is about 1 h. Plausible: `sF` covers the
  joins' ctl_req-high windows.
- **G1 (time-truncated theorems) is untouched.** As for the steer, the contract takes the partners'
  traces for the whole run. In a closed graph this is circular until G1 is done.
- **G4 (finite streams).** The contract needs `Enum` on every input, i.e. infinitely many tokens per
  input, as B's theorems already do.
- `H_*_LEAD` (rule E/I lead of a `bd_link` sender) is still an environment hypothesis inside
  `MuxDataEnv`/`MN3DataEnv` (see `B-ops-hold.md`).
- No `Port` for the input channels is assembled (their data windows belong to the senders). The
  `opSpec` step needs `Port` on ALL channels (`opSpec_of_ports`), so `mux_spec` is applied by the
  composer, not here.

## Verdict

**Works.** G5 is done for `bd_mux` and `bdc_muxn3`. Both are now in the same state as the steer, and
one step further: the output channel is a FULL `Port` including C's `Held`, from B's timed gate
models (control: `mux_ok_static`/`muxn3_ok_static`; data: G3's hold-to-fall theorems).
- The `idx = cnt` lemma is generic (`idx_cnt`).
- Every added hypothesis is named and is a positivity, reset-quiet, identification or bus-encoding
  fact.
- Both contracts are witnessed jointly on unit-delay runs, with non-degenerate values.
- Remaining for C's composition to rest on these: G1 (1-2 days for steer/mux/muxn3), the one-select
  joint witness (~1 h), and linking `H_QUIET_*` to `ResetGcd` (needs per-port net names).
- What it buys: C's `muxEq` and `muxnEq` (the gcd_hw loop-carried muxes) are now consequences of the
  gate-level timed models under per-arc static obligations. Each obligation is checkable on the
  routed design and on GLS.

## Fidelity per primitive (inherited unchanged; this file models nothing new)

- **Joins, ack C-elements** (`uj0/1`: REAL `0x0000AE08…`, `0x0000EA80…`; `uxa/uya`, `ua_i`, `uj_i`:
  `bd_c2` REAL `0x00E800E8…`): LUTs evaluated from the INITs (`lutB`). Each LUT is a FIFO
  bounded-delay arc (`Ret`, H_LUT_FIFO). Feedback is a routed wire with a delay window (`WinDelay`).
  No glitch, no runt, no inertial filtering on control paths.
- **`uor` (`4'hE`), `|j` (`8'hFE`), decodes `sel_i`** (inferred `8'h10/40/40`): FIFO LUT arcs.
- **Delay lines**: `bd_delay` FASTFALL=0 is one FIFO arc (`H_LINE_FIFO`). The 3-way's FASTFALL=1 line
  is Lt2's `FFLine` (AND-stage FIFO model, flush per stage).
- **Data path**: `bd_datamux` (REAL `8'hE4`, `64'hFFAA_5500_E4E4_E4E4` via `DmRel`) and the muxn3
  LUT5 (REAL `32'hF0AA_CCF0` via `Gate`). Both are Kleene LUTs over pin windows (H_KLEENE_LUT):
  unselected inputs may move freely.
- **Wires**: FIFO `Ret` arcs. Under the G2 reading, input arcs are residual fanout arcs (see above).
- **Witnesses**: unit transport delay on every arc. This is a consistency check, not timing evidence.
