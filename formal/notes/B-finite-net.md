# B-finite-net (probe Bfin2): a time-indexed assume-guarantee rule; FEnv1 derived on runs that stop

2026-10-29. Continues Bfin (`notes/B-finite-runs.md`), which had the link class for runs
that finish (`FEnv1`, `FPhysLink`, `gcd_hw_safe_fin_links`) but ASSUMED each link's
`FEnv1`. Bnet's closure (`AssumeGuarantee.ag_time`) times each (cell, segment) event by the
segment's END, and in a quiet run every cell's last segment has no end.

## Files (all checked with `/tmp/claude-0/btools/bcheck.py`, core Lean only)

| file | result | content |
|---|---|---|
| `formal/lean/Formal/Cells/FiniteNet.lean` | **OK** | `GPhT`, `ag_trunc` + zero-delay counter-example, `tnode`/`twire`/`tlink`, `FChain`, `fchain_env1`, `FInChain`, `gcd_hw_safe_fin_chains` |
| `formal/lean/Formal/Cells/FiniteNetWit.lean` | **OK** | `linkB_chain`, `chW_fin_chains`, `gcd_hw_fin_chains_witness` (the decisive check) |
| `formal/lean/Formal/Cells/FiniteNetCells.lean` | **OK** | truncated C-element (`tcelX`, `tcelG`), gated request / steer / mux join (`tgated`, `tsteer`, `tmuxj`), the ORs (`tor_ex`, `tuack`, `tuor`), `WitOr.tor_witness` |
| `formal/lean/Formal/Cells/FiniteNetMixed.lean` | **OK** | `fnet_closed`, cell specs, `fmixed_closed`, `flink_spec_env1`, `gcd_hw_safe_fin_net` |

Scratch: `/tmp/claude-0/probes/Bfin2/` (`Ax.lean`, `ax.out`: the axiom printout).

## (1) Truncated segment lemmas

`GPhT x c L T`: `x` is a clean step signal on `[0, T)` with edges `c j` for `j` in the edge
set `L` (`L j`: the j-th edge exists). `L = (· < n)` is Bfin's `FPhases` (`gph_fin_iff`),
`L = True` is Bfb's `Phases` (`gph_inf_iff`): one notion for finite and infinite runs.

* `tnode`: a `Win lo hi` LUT with H_NO_REVERT, excitation clean on `[0, T)` ⇒ node clean on
  `[0, T + lo)`, edges read off the node (`nt`). Only `hi ≤ c j + lo` and H_PWR needed; NO
  spacing hypothesis (Bnet's H_SP / H_RT disappear).
* `twire`: the same for a wire (`T ↦ T + wl`).
* `tlink`: B's link (`Stage`, real `bd_c2n`): request and acknowledge clean on `[0, T)` ⇒
  node clean on `[0, T + lo)`; edge `j` exists iff request edge `j` and acknowledge edge
  `j-1` do (`LnL`, finite form `min nr (na+1)`, `lnL_fin`). H_SND / H_RCV only for edges
  that exist.
* `tcelG` (n-pin C-element, `CelG` + `CelLaw`, node edge exists iff every pin's does; via
  `tcelX`, the pointwise form of Bmux2's `celX_segK`), `tsteer` (real `bd_steer` `u`, via
  `tgated`), `tmuxj` (`uj0`/`uj1` as `G2` of the input and the gated control).

## (2) The time-indexed rule

`ag_trunc`: `G i T` (cell correct on `[0,T)`), `A i T` (its pins correct on `[0,T)`);
H_ENV: all guarantees at `T` give every assumption at `T`; H_CELL: `A i T → G i (T + lo i)`,
`lo i ≥ 1`; H_MONO; then `G i T` for all `i`, `T`. Induction on `T`: no event must end.
`ag_trunc_zero_unsound` / `ag_trunc_zero_cex`: with `lo = 0` all premises hold on Bnet's
two-zero-delay-buffer loop (`x = y = true`) and the conclusion (`x` low) is false;
`ag_trunc_unit_ok`: the one-tick loop meets the rule and is low forever.

## (3) Closures, FEnv1 derived

* `FChain D L` (Bnet's `ChainData` verbatim, an edge set per cell, end cells as TRUNCATED
  contracts with waits only for edges that exist): `fchain_nodes`, `fchain_reqPin`,
  `fchain_ackPin`, and `fchain_env1`: with finite counts every link's `FEnv1` + `Timing1`,
  with Bnet's derived slacks `Es = vl + lo + wl`, `Ea = wl + lo + vl`. `fchain_nodes_inf`:
  the same theorem with every edge set `True` gives `Phases`.
* `gcd_hw_safe_fin_chains`: C's `gcd_hw_circuit_safe` with `H_CELLS` of every link replaced
  by `FInChain` (the link in an `FChain` with finite counts; its `FEnv1` is derived).
* `fnet_closed` (any `GD` network whose cells meet the truncated contract `FCellOK`, with
  wires and floors; no H_WAIT, no H_SP), specs `FLinkSpec`/`FCelSpec`/`FSteerSpec`/
  `FOrSpec` each proved to give `FCellOK`, `fmixed_closed`, `flink_spec_env1` (FEnv1
  derived), and `gcd_hw_safe_fin_net`: one gate-level network of gcd_hw (`FGcdNetOK`,
  finite edge counts) with links, forks N ≤ 4, joins N = 2, steer branches AND the 38 steer
  acknowledge ORs gate-modelled; contracts on the rest.

## (4) The decisive check: chW meets the derived-Env1 theorem

`linkB_chain`: Bfin's kernel checker `linkB x y = true` implies `FInChainC x.ch y.ch`, with
a three-cell chain around the link: source = the producer's request node `cL x.rq`, the
link, sink = the consumer's acknowledge node `cL y.ak` (every node its pin one tick
earlier), unit LUT and wire delays, `R = 2`, end waits `lo = 1`, so the derived slacks are
`Es = Ea = 3`, exactly what the checker verified (`sndQ`, `rcvQ`). Edge counts: request's
length, `min nr (na+1)`, acknowledge's length. `chW_fin_chains`: all 175 links of `chW`
(a = 12, b = 18, quiet after 476 ticks; 34 links idle), reusing Bfin's `lk_all` (no new
`decide`). `gcd_hw_fin_chains_witness`: `chW` meets ALL hypotheses of
`gcd_hw_safe_fin_chains` jointly, and out0 latches a token carrying 6;
`gcd_hw_fin_chains_consistent` applies the theorem.

Degenerate parts, stated: the chains are the shortest (one link between two end cells), not
gcd_hw's maximal chains (up to 3 links); the end contracts hold because their conclusions
do (as in Bnet's witnesses); unit-delay run, every window met at width 0; `R = 2` chosen.

## The OR cells (lead's request)

Bmux2's `or_not_causal`: an OR's low segment reads a prefix of the idle branch's
later-ending segment, so no end-ordered rule carries it. In the time-indexed rule the OR at
`t < T` reads both branches only at `t`: `tor_ex` (branches clean on `[0, T)` ⇒ OR
excitation clean on `[0, T)`, merged edges Bmux2's `oe`, edge set `Lor`) needs, beyond the
per-branch token enumerations, ONE edge-time hypothesis H_ORD (merged edges increase: the
branches interleave in token order) and H_DOWN (they exist in order). A branch that never
fires again is constant: Bmux2's H_LATER (needed for the bracket in finite runs) is gone.
`tuack`, `tuor`: the real `bd_steer` `uack` and `bd_mux` `uor` LUTs. `WitOr.tor_witness`:
all hypotheses on a finite run (token 0 on branch 0, token 1 on branch 1, then quiet; the
idle branch rises later in token 0's low phase, branch 0 is idle forever after token 1).

Which of gcd_hw's remaining contracts (`op_classes2`) the rule discharges: the 38 steer
`uack` ORs are gate-modelled in `gcd_hw_safe_fin_net`. The 21 mux `uor` ORs and the mux
joins have truncated lemmas (`tuor`, `tmuxj`), but the mux cells stay contracts there
because the mux acknowledges `uxa`/`uya` (`muxa_segK`) and the sources (`src_segK`) have no
truncated form here; so do muxn (1), amerge (9), forkH5/forkH6 (3). join1/sink have no cell.

## NOT done / open

* No joint witness of `FGcdNetOK` (a gate-level elaboration of all of gcd_hw on a run: C's
  run has channel traces, not fork/join/steer internal nodes). `gcd_hw_safe_fin_net` is
  proved, not witnessed; the chain form is witnessed.
* Truncated `muxa` (`uxa`/`uya`), `src`, C-trees N ≥ 5, muxn, amerge: not done.
* Departure bounds and H_ORD stay EDGE-TIME inequalities in the mixed network (as Bseg);
  in `FChain` they are derived from delay constants.
* The time-indexed rule is not shown to subsume Bnet's segment-contract theorems formally
  (different contract forms); `fchain_nodes_inf` shows the same chain theorem covers
  infinite runs.

## Axioms

`#print axioms` on 29 headline theorems (`/tmp/claude-0/probes/Bfin2/Ax.lean`, output
`ax.out`): `ag_trunc`, `ag_trunc_zero_*`, `ag_trunc_unit_ok`, `gph_inf_iff` use propext, Quot.sound; all
others propext, Classical.choice, Quot.sound. No sorry, admit, native_decide.
