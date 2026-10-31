# B-zero-delay-tok (probe Bzd3): one `bd_link` stage and the closed-loop chain with k tokens

Files (core Lean only). Each checks with `/tmp/claude-0/btools/bcheck.py Formal/Cells/<File>.lean`:

| file | content |
|---|---|
| `formal/lean/Formal/Cells/ZeroDelayTok.lean` | k-token stage: model, multi-token latch capture, sufficiency, the new row H_REARM and its necessity, 1-ps counter-run, 2-token witness |
| `formal/lean/Formal/Cells/ZeroDelayTokChain.lean` | closed-loop N-stage chain with k tokens, physical half: every stage meets the k-token spec in the loop |
| `formal/lean/Formal/Cells/ZeroDelayTokWit.lean` | non-vacuity of the chain: 2 stages, 2 tokens (values 1 then 0), nonzero reads, joint simulator |

Builds on LinkExact (Blink), ZeroDelayNet/ZeroDelayNetPhys (Bzd2). C's definitions are not restated.

## Problem statement

**Model.** One `bd_link` stage as LinkExact models it:
- the `bd_c2n` node at its real INIT in Kleene semantics;
- each pin read through its own read map in the box, non-monotone maps allowed;
- the `bd_latch` bit;
- power-up arbitrary, X included.

The environment now sends `k` four-phase tokens:
- `EnvK`: the request is low before `Ra 0`, high on `[Ra1 j, Fa j)`, low on `[Fa1 j, Ra (j+1))`, and low for ever after the last token. The acknowledge is the same. Both are ARBITRARY inside every window.
- `DStabK`: the data pin carries `vs j` on `[Td j, Tn j)`.
- There is one shared box and one reset.
- `P.tok j` is token `j` as a LinkExact `Par`, so `U0, U1, Rel, V0, V1` and the six rows `Conj` are LinkExact's own, per token.

**Scope `WfK`.** LinkExact's `Wf` for every token, `k >= 1`, and H_NEXT: the env pulses are in order (`Fa1 j <= Ra (j+1)`, `Fb1 j <= Rb (j+1)`).

**Spec `SpecK`.** The node is a window token per token:
- 0 on `[Rhi, U0 0)`;
- 1 on the nonempty `[U1 j, V0 j)`;
- 0 on `[V1 j, U0 (j+1))`, and for ever after the last token.

The latch outputs `vs j` from its capture (`V0 j <= pe.σ t`), and from `max(U1 j + pe.hi, Td j + pd.hi)`, up to `U0 (j+1) + Elo`. That is the earliest instant at which the next token's opening can be read through the enable. For `k = 1` this is LinkExact's `Spec`.

## The new cross-token row

`H_REARM (j)`: `Fb1 j + Bhi <= Ra1 (j+1) + Ahi`. In words: the node is surely reading the previous token's acknowledge fall by the time it surely reads the next request rise.

If this fails, at `U1 (j+1)` the node reads:
- request 1;
- acknowledge 1 (still the previous token's);
- its own 0.

The real INIT then holds 0 (`c2nK 1 1 0 0 = 0`), where the spec demands 1.

This is the only new row. The rise of token `j+1` has no new feedback race: with request 1 and acknowledge 0 the INIT gives 1 whatever the feedback is (`c_follow1`). The low phase of token `j` extends up to `U0 (j+1)` from the existing H_RACE_DN.

There is also no new latch row. The latch rows apply per token window (`latch_tok_ok`).

### cell_constraints.json form (proposed, NOT applied to the JSON)

```json
{
 "id": "bd_link.stage_rearm",
 "cell": "bd_link",
 "catalogue_row": "none (Bzd3, formal/notes/B-zero-delay-tok.md)",
 "obligation": "one bd_link stage carrying k >= 2 tokens (bd_c2n + one bd_latch bit, real INITs, open loop): between tokens j and j+1 the controller surely reads the previous ack_out fall no later than it surely reads the next req_in rise",
 "inequality": "H_REARM Fb1_j + Bhi <= Ra1_{j+1} + Ahi (ack_out fall window end of token j plus the ack pin's slow read, against req_in rise window end of token j+1 plus the req pin's slow read); together with bd_link.stage's six rows at every token. Closed-loop form (ZeroDelayTokChain): V1_{i+1,j} + Bhi_i <= U1_{i,j+1}",
 "refers_to": ["bd_link.stage", "bd_c2n.env_latency"],
 "informational": true,
 "lean": [
  {"file": "formal/lean/Formal/Cells/ZeroDelayTok.lean", "name": "exact_rearm", "role": "exact",
   "note": "under WfK, GapK and bd_link.stage's six rows at every token: SafeK P <-> forall j, H_REARM j. The full iff SafeK <-> RowsK is NOT proved (the six rows' necessity inside a k-token env is open)"},
  {"file": "formal/lean/Formal/Cells/ZeroDelayTok.lean", "name": "sufficientK", "role": "sufficient",
   "note": "WfK + six rows per token + H_REARM => SpecK for every behaviour (no GapK)"},
  {"file": "formal/lean/Formal/Cells/ZeroDelayTok.lean", "name": "need_rearm", "role": "necessary",
   "note": "needs GapK j and token j+1's H_RACE_UP"},
  {"file": "formal/lean/Formal/Cells/ZeroDelayTok.lean", "name": "rearm_breaks", "role": "counter_trace",
   "note": "P2 2979: 2 tokens, P0 box, H_REARM violated by exactly 1 ps (rearm_one_tick), all else met"}
 ],
 "status": "proved",
 "combine": "all"
}
```

H_DATA_LOOP_K is a closed-loop row and not a cell row. If it were catalogued, its JSON would follow the same pattern: `Tn_{i+1,j} <= U0_{i,j+1} + Elo_i`, and with bd_link.stage's hold row the cross-stage hold `V1_{i+1,j} + Ehi_{i+1} <= U0_{i,j+1} + Elo_i + Dlo_{i+1}`. It is a sufficient hypothesis only; its necessity is not proved.

## Results

| theorem | assumed | proved |
|---|---|---|
| `latch_tok_ok` | LibGapLatch's three rows for one window; enable 1 on `[A,B)`, 0 on `[C,∞) ∩ Lt` (`Lt` downward closed) | output `v` at every `t >= 0` with `B <= pe.σ t` and `Lt (t - pe.lo)`: multi-token capture, per token window. `Lt = True` gives `latch_pin_ok` |
| `sufficientK` | `WfK`, `RowsK` (six rows per token + H_REARM) | `SpecK` for every behaviour, every data sequence |
| `need_rearm` | `WfK`, `GapK j`, H_RACE_UP of token `j+1`, H_REARM `j` false | not `SafeK` (explicit run: reads at their slowest, request pulses `[Ra1,Fa)`, ack pulses held to `Fb1`) |
| **`exact_rearm`** | `WfK`, `GapK`, six rows at every token | `SafeK ↔ ∀ j, H_REARM j` |
| `rearm_one_tick`, **`rearm_breaks`** | `P2 2979`: 2 tokens, LinkExact's P0 box (reads 280..900 ps) | H_REARM violated by exactly 1 ps, everything else met; the stage breaks |
| `witness2` | `P2 3500` | all rows hold; `SafeK`; a simulated behaviour (data 1 then 0) exists and meets `SpecK` |
| `chain_rstK`, `chain_tokK`, **`chain_specK`** | `ChainCellK` + `ChainBehK` | every stage of the closed N-stage loop meets `SpecK` for k tokens |
| `chain2_witness` | 2 stages × 2 tokens, nonzero reads | all chain hypotheses hold; a coupled behaviour exists; both stages meet the 2-token spec |

**`GapK j`** is the necessity scope only: `Fa1 j + Ahi <= U0 (j+1)` and `V1 j + Qhi <= U0 (j+1)`. The previous request fall, and the node's own fall through its feedback, are surely read before the next request can be read rising. It does not imply H_REARM, which is about `Fb1`.

**The closed loop** (`ChainCellK`) carries these hypotheses:
- `WfK` and `RowsK` per stage;
- H_LOOP_K per token;
- H_WIRE_POS and H_RST_SEEN, as in Bzd2, for token 0;
- H_DATA_LOOP_K.

The proof goes as follows:
- the reset phase is Bzd2's joint time induction;
- then, token by token: first the high phases of all stages, by induction over the stage index. The acknowledge low phase comes from the downstream node's previous-token low phase plus H_REARM.
- then the low phases of all stages.

**In the loop, H_REARM of stage `i`** reads `V1_{i+1,j} + Bhi_i <= U1_{i,j+1}`. Both sides are caused by stage `i`'s own fall:
- through the downstream request pin;
- through the upstream acknowledge pin and back through stage `i`'s request pin.

So it is a genuine race of the loop, not a consequence of the other rows.

Axioms (checked with a temporary companion file, since removed): `latch_tok_ok` and `need_rearm` use `propext` and `Quot.sound`; `sufficientK`, `exact_rearm`, `rearm_one_tick`, `rearm_breaks`, `witness2`, `chain_specK` and `chain2_witness` use `propext`, `Classical.choice` and `Quot.sound`. There is no sorry, admit, native_decide or axiom.

## NOT covered / open

- **Full iff for k tokens.** The necessity of LinkExact's six rows INSIDE a k-token environment (k >= 2) is not proved. `exact_rearm` takes them as hypotheses. The reason: LinkExact's `need_*` are stated as `¬ SafeLink`, which does not expose the counter-behaviour, so they cannot be transported. A token-`j` version needs the six runs re-proved with:
  - the rest state taken from the spec of the counter-behaviour itself, which is the trick used in `need_rearm`;
  - `GapK` as the scope;
  - data values alternating at `j-1, j`.

  The value alternation matters: if `vs (j-1) = vs j`, setup_pulse of token `j` is NOT necessary, because the latch already holds the right value. So the six-row iff must quantify over data sequences, as `SafeK` does.
- **Goal (2), abstract half.** C's `Link` on a k-token zero-delay chain run, and one key retiming for it, are not written. What is needed:
  - a k-token `Sch` with trains and C's gate fields per token via `train_at`;
  - a bus defined by counting openings;
  - cross-token order items `akf (i+1) j < cu i (j+1)` and `cd i j <= cu (i-1) (j+1)`.

  Finding (argued, not mechanised): with the key taken at `lo`, the second item can fail. `U0 (j+1)` may precede the downstream fall, because the node's rise window opens when the request can be read, even while the acknowledge is still high and the node holds 0. Two ways out:
  - key the rise at a representative point `max(U0 (j+1), Fb j + Blo)`. H_REARM keeps this inside the window, and monotonicity survives because sure precedence orders any points of the windows;
  - add a lo-causality hypothesis.

  A related physical point (argued, not mechanised): for `t >= U0 (j+1)` with the acknowledge still read high and the feedback reading the node's own falling window, the INIT can re-latch 1 before the acknowledge fell. This is invisible to `SpecK`, since it happens inside token `j+1`'s rise window, and it is allowed by the neighbours' window environments.
- **Goal (3), rings with initial tokens.** NOT done. What is missing:
  - a `bd_c2n_set` stage contract (reset forces 1, first edge a fall);
  - a ring induction (no stage index to induct on; the induction order is generation/time around the cycle);
  - the abstract half onto C's `Ring.Run` from `resetState K` / `kState k`. This needs distinct firing steps; the key with per-event depth gives them.
- The alternative spec whose rise window starts at `max(Ra (j+1) + Alo, Fb j + Blo)` and ends at `max(U1, Fb1 j + Bhi)`. Under it H_REARM would become part of the window definition (a latency, not a condition). Not mechanised.
- Correlated corners: box form only, as in LinkExact. A W-bit bus beyond one bit per shared node is not covered. Zero-delay inter-stage reads (H_WIRE_POS) are not covered.
