# B probe Bex2: Win request and acknowledge lines, any number of stages

Shard B, 2026-10-27. Lean: `formal/lean/Formal/Cells/WinFifoN.lean`, core Lean only.
Check: `scratchpad/bchk.sh formal/lean/Formal/Cells/WinFifoN.lean` prints `[bchk] OK`
(autoImplicit=false). `#print axioms` for every theorem below gives a subset of
`[propext, Classical.choice, Quot.sound]`. There is no sorry, admit, axiom or native_decide.

This follows Bw (`B-win-fifo.md`) and Bex (`B-win-fifo-causal.md`). Bex put the two LUTs of the
2-stage pipe on `Win` and kept the lines FIFO. This probe puts every channel of the
`N`-stage pipe (`PipeTimedN`) on `Win`:
- the `N` controller LUTs (Bex's `Stage`: `Win` + H_NO_REVERT, real `bd_c2n` INIT);
- the `N - 1` request lines;
- the `m b + 1` acknowledge copies whose OR is the acknowledge pin of boundary `b`.

Every event time is read off a trace with `nt`: node edges off the node, request edges off the
request pin, acknowledge edges off the copies. There are no read maps.

## The wire question: can a routed wire glitch in the digital model?

Yes, under `Win` alone. A wire is a buffer chain: site pin, pips, segments. In the digital model
that is a single-input pure delay line `y t = x (t - d t)` with `d t` in the band.

| theorem | statement | status |
|---|---|---|
| `delay_line_iff_win` | `Win lo hi x y` holds iff `y` is a pure delay line of `x` with a time-varying delay in `[lo, hi]`. `Win` says nothing more than this. | proved |
| `wire_glitch` | For every band at least 2 ticks wide there is a delay function in the band such that one rising edge comes out as 1, 0, 1. No FIFO read reproduces it (from `win_glitch_not_fifo`). **H_NO_REVERT is not provable for a wire from `Win`.** | proved |
| `mono_read_fifo` | Monotone read (`t - d t` nondecreasing) turns the delay line into a FIFO read. Composition along a chain is `PipeTimed.fifo_comp`. | proved |
| `wire_noRevert` | Take a FIFO read of an alternating clean input (edges `c`). Assume **H_CATCH**: the wire delivers edge `j` before input edge `j+1` can arrive, i.e. `fst (c j) ≤ c (j+1) + lo`. Then the wire satisfies the line hypothesis `NoRevertFrom g` for every `g` with `c 0 + hi ≤ g + lo`. **There is no spacing condition between the band and the edges.** | proved |
| `fifo_req_nr`, `fifo_copy_nr` | In every PipeTimedN run, every FIFO request line and every FIFO acknowledge copy (`O ∘ σ`) satisfies this file's line hypotheses: `H_REQ_WIN`/`H_REQ_NR` and `H_AP_WIN`/`H_AP_NR`. H_CATCH comes from causality and from 6e's `H_ACK_FLUSH`. | proved |

**Decision.** For a wire, take monotone read as the primitive. Its physical content: each stage
of the chain has one input and a monotone transfer, so no edge overtakes another, and one input
edge gives one output edge. H_NO_REVERT then follows (`wire_noRevert`), and H_CATCH is the
handshake's causality.

For a LUT the same step is not available. A LUT has several inputs, and Bw showed skew glitches
there. The LUT keeps H_NO_REVERT as an assumption.

The line hypothesis is stated as `NoRevertFrom R`: Bex's intrinsic form, restricted to input
stretches that start at or after reset release. The restriction matters for two reasons:
- Bex's unrestricted `NoRevertI` is false for a constant transport delay strictly inside the
  band when the input is not spaced, and on a junk power-up prefix. This is argued by hand
  (input `v, !v, v` with a 1-tick middle pulse and delay `d > lo`); there is no Lean
  counter-example.
- `NoRevertFrom R` is implied by FIFO lines in the loop (`fifo_req_nr`).

## Results (all-Win `N`-stage pipe)

The hypotheses are:
- `GatesNW`: H_RST; H_ST i; H_REQ_WIN/H_REQ_NR b; H_AP_WIN/H_AP_NR b k; H_ACK_LINE b (the pin
  is the OR of the copies).
- `EnvNW`: as `EnvN`, with departures measured from the node edges read off the traces.
- `TimingNW`: as `TimingN`. The only change is **H_ACK_FLUSH_W**, `ahi b < Won b + alo b`. This
  is 6e's `H_ACK_FLUSH` made one tick strict.

| theorem | proved |
|---|---|
| `pipe_ctl_w` | Every excitation equals `Vph j` over every phase, for every stage and every `N`. The induction is outer on `j`, inner on `i`, as in `PipeTimedN.pipe_ctl`. |
| `nodes_clean_w`, `pins_clean_w` | Every node, request pin and acknowledge pin is a clean four-phase step signal, with edges at the trace-read times. |
| `spread`, `gap`, `live`, `Rin_le_c` | The derived timing. The excitation spacing (H_BAND) follows from H_LAT and H_LOOP_POS, as Bex found. **The request lines need no spacing condition at all.** The causality lemma `Rin_le_c` (a request edge comes before the sender's next phase starts) gives the upper edge bound. |
| `lift` | There is a `PipeTimedN.PN` with the same `N`, reset, environment times and bands, and with FIFO read maps for every LUT, request line and copy, built by `ret_steps` and Bex's `ret_of_clean`. Its derived `c` and `τ` are the run's. There are pin traces `r'`, `a'` equal to the real pins from `R` on; before `R`, reset masks the pins (`ex_congr`). `GatesN`, `EnvN` and `TimingN` all hold. **So every PipeTimedN theorem holds on the all-Win run.** |
| `pipe_forward_w` | Example: PipeTimedN's data theorem. Any `DataN` for the lifted `P` gives token delivery. |
| `Wn.witness`, `Wn.witness_lift` | Non-vacuity for every `N ≥ 1`. Every LUT, request line and copy is a **2-tick delay inside a `[1, 3]` band, strictly inside** (stated as trace equations in the theorem). Feedback is 1 tick and reset releases at 6. Times: `τ i j = 8 + 4i + 8j`. H_NO_REVERT holds at that interior delay (`del_nr`, via `noRevertI_of_ret` on the clean square wave). |
| `Wg.line_nr_needed` | **Counter-run: H_AP_NR cannot be dropped.** Setup: `N = 2`, half period 10, so stage 0's acknowledge comes 2 ticks before its next request. One glitch on the boundary-1 copy, inside stage 1's first node zone `[13, 15)`: the copy shows 1 at 13 (the window reads node@12) and 0 at 14 (reads node@11). Stage 0's excitation cannot see it, because its request and feedback are high (`ex0_g`). Every other field of `GatesNW`, and all of `EnvNW` and `TimingNW`, hold. `H_AP_NR` fails, the acknowledge-pin conclusion of `pins_clean_w` fails at `t = 14`, and no FIFO read with `hi ≤ 3` reproduces the copy. |

## Findings

1. **For lines, no-revert is a theorem of monotone read plus causality, not an extra assumption
   of the same kind as the LUT's.**
   - A Win line with `NoRevertFrom R` needs no band-vs-spacing condition. The request line's
     edge bound comes from causality (`Rin_le_c`), not from a spread hypothesis.
   - FIFO lines in a PipeTimedN run satisfy it (`fifo_req_nr`, `fifo_copy_nr`), so FIFO is a
     special case.
   - What remains a genuine assumption is monotone read of each wire stage. A board test: a wire
     driven by a clean edge never shows a double edge.
2. **H_ACK_FLUSH_W is one tick stricter than 6e's H_ACK_FLUSH.**
   - Under `Win`, a slow copy whose spread exactly equals the node spacing could swallow a phase
     and make the edge found by `nt` fall back to its default value.
   - With FIFO copies the non-strict form suffices (`fifo_copy_nr` uses only `H_ACK_FLUSH`).
   - Strictness is sufficient. It is not claimed necessary: no counter-run was built at equality.
3. **Interior delays work.** H_NO_REVERT holds for a fixed delay strictly inside the band on a
   spaced clean input. It does NOT hold for such a delay on an arbitrary input (argued, not
   formalised): the unrestricted `NoRevertI` fails when an earlier pulse is still in flight. That is why the line form is
   restricted to stretches after `R`, and why the LUT form is only ever applied to excitations
   that are proved clean and spaced.

## Not covered

- **Per-pin LUT arcs.** The LUT reads the lumped excitation at one instant, as in
  PipeTimed/PipeTimedN; FifoFidelity's H_SEL_ORDER is not used.
- The gate-level FASTRISE chain under `Win` is not modelled. The copies are abstract Win+no-revert
  paths. PipeTimedN's `fastrise_or` covers only the FIFO chain.
- No counter-run for H_REQ_NR. It is symmetric to H_AP_NR but needs a run in which the request
  arrives before the acknowledge.
- No counter-run for strict H_ACK_FLUSH_W.
- That FIFO LUTs give Bex's `Stage` (H_NO_REVERT for the LUT) is not packaged here. It is Bex's
  `noRevertI_of_ret` under the derived spread.
- Kleene/X values, the routed reset network, and the involution channel.
