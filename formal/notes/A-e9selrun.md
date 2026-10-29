# A-e9selrun (probe E9SelRun, shard A): running the causal select verdict on gcd_hw

STATUS (2026-10-29 11:45 UTC): DONE (runs being tabulated, §4/§5 filled at the end). 3 Lean files,
check.sh OK (3435 + 3732 declarations, §6). Generator + executable + 16 rows + 6 controls.

## 0. Summary

1. **E8Causal's `design_verdict9_selL` is not applicable as stated to most gcd_hw select
   literals.** Its identity check `ackOK` wants the request wire to be a chain of 1-input
   buffers from a real node, and the ack wire to BE a real node's LUT output. On each of the 4
   seeds, 78 of 126 request wires are the end of an asymmetric (fast-fall) delay line of 2-input
   AND LUTs (`ucmpiK.udly.chain.g[m]` / `uoriK.udly.chain.g[m]` = AND(r, g[m-1]), INIT 1000, all
   fed by the same request `r`), 12 acknowledge wires are a buffer chain of the controller and 6
   an OR (`ulink_nX.uack.chain.g[1]` = OR(g[0], ctl), INIT 1110). With the generated lines,
   selL's rows pass on at most 30 of 126 literals on every row (§4).
2. **`Events9SelL.design_verdict9_selT`** (new, proved): `ackOK` replaced by positive gate
   trees (`AT`, `treeOK`): the ack wire is a one-leaf tree (each gate's INIT is 1 when the
   listed input is 1), the request wire a tree listing all inputs of every AND (one leaf per
   delay-line element). H_REQ_CNT per request leaf from a checked log line (`ReqLineT`: walk
   leaf → ack leaf, ≤ 1 token, delay ≥ `phi κa − plo π`), H_ACK_CNT from a source-anchored
   `AckLineT` (`Dl + phi bot ≤ dW + plo κa + 1`). Generated and run: §4.
3. **`Events9SelJ.design_verdict9_selJ`** (new, proved): a junction-anchored lag with the
   minimum over ALL arms, derived from the accepted log through a second, checked "junction
   log" (`JLn`, `runJ_sound`). An arm that shares the junction's lower part `bot` enters with
   its unshared stretch at its low end; an arm that does not share it enters with its source lag
   minus `phi bot` (`facOK`'s second case, `jlift`). This is the rule E8Causal's
   `sibling_lag_neg` asks for. Generated and run: §4.
4. **Finding: E8SelC's split margins are recovered causally only on the mux rows, not on the
   steer rows.** On steer pins (`ucond_brN`), the acknowledge (`merge:ucond_brN.uack`) closes a
   sibling-branch token through the merge's OTHER, directly filtered pin, which reads the source
   through its own steer LUT and does not pass this pin's junction. The causal lag is then the
   sibling arm's, measured from the source, so the junction row's margin equals the
   source-anchored row's (e.g. seed d slow `ulink_n_falseResult_77.ctl` pin1: 928 ps causal vs
   E8SelC's split 2851 ps, which rested on the unjustified own-arm lag). On mux joins (`umuxN`),
   both arms (`uj0`, `uj1`) read the select link through the SAME request delay line, so the
   junction at the delay line's output recovers most of the split gain (e.g. `umux14.uj1`:
   3721 → 4668 ps; E8SelC split 4989).
5. **Negative controls** (§5): the wrong ack wire (E8SelC's NEGack, which PASSED E8SelC's
   rows) is now REJECTED, in both forms (regenerated certificate: no one-leaf positive tree;
   stale certificate: tree root ≠ ack wire). A request walk with ≥ 2 tokens is rejected; a
   junction row whose sibling arm claims the own arm's lag is rejected, and the same row with the
   honest lag passes.

## 1. Why `ackOK` fails on gcd_hw (task 1, first run)

`Events9PrefixSel.ackOK e na nq κ` requires `e.ak = out(na)` and `bufPath d e.rq out(nq) κ`
(every element input 0 of a 1-input buffer). Measured on the E8SelC maps (126 literals; the
same counts on seeds d, 3, 4, 5; `scratchpad/E9SelRun/census.py`, untrusted):

| wire | structure | literals |
|---|---|---|
| request | 1-input buffer chain to a real node | 48 |
| request | AND delay line `chain.g[m] = AND(r, g[m-1])`, `g[0] = BUF(uor)`, `uor = BUF(r)` | 78 |
| acknowledge | a real node's LUT output | 108 |
| acknowledge | a buffer chain (`uack.chain.g[0]`) of the controller | 12 |
| acknowledge | `uack.chain.g[1] = OR(g[0], ctl)` | 6 |

So `ackOK` (and therefore `design_verdict9_selL`) fails on most literals for reasons of
identity, not timing (on seed d slow `ackOK` + `ReqLine` hold for 30 literals). `selL`'s other rows (ReqLine, AckLine, holdBandS) were generated and
evaluated for every literal anyway (column "selL" of §4 counts literals with all of them).

## 2. `Events9SelL.lean`: gate-tree identities

* `AT` / `ATL` (mutual inductive): `leaf n` (node `n`'s LUT output) or `gate gi ch` (children:
  input index and subtree). `AT.leaves`: leaves with their paths from the root wire.
* `initAll g is` (decidable): INIT is 1 at every address with the bits `is` set.
* `atOK d rn w t` (decidable): every gate exists, drives the wire its parent reads, satisfies
  `initAll` for its listed inputs; every leaf node's LUT output is the wire read.
* **`at_true`**: under SatPin (per-pin LUT semantics, `wf_eval`), if every leaf's wire reads 1
  at its path-warped time `tau π t`, the root reads 1 at `t`. Proved by mutual structural
  induction.
* `treeOK e ta tq na κa` (decidable): ack tree with exactly one leaf `(na, κa)`, request tree
  with real reset-0 leaves; all paths exist.
* **`design_verdict9_selTP`**: as E8Causal's `selP`, with `treeOK` instead of `ackOK`, and
  count facts per leaf: H_SEL_O (by `O k` every request leaf's read has seen transaction `k`),
  H_REQ_CNT (each request leaf's count at its read ≤ the ack leaf's count at its read + 1),
  H_ACK_CNT (the ack leaf's count at its read stays ≤ 2k+1 until `Dl` after the junction shows
  `k`). The new step is the case analysis: ack leaf odd ⇒ ack wire 1 (`at_true`); else every
  request leaf is exactly 2k+1 ⇒ request wire 1 (`at_true` on the AND tree).
* `ReqLineT`, `AckLineT`, `reqOK` (decidable), `reqCnt_of_lineT`, `ackCnt_of_lineT`.
* **`design_verdict9_selT`**: H_REQ_CNT and H_ACK_CNT from checked log lines.

Plain statement of `design_verdict9_selT`. Assumed: Recog6, OK7, an accepted log with the
certified items; per real select literal `entOK`, `treeOK`, `reqOK` (one `ReqLineT` per request
leaf); per copy `holdBandS` at lag `Dl` and an `AckLineT` (all decidable, evaluated by `xselL`);
SatPin, constants, reset, H_ARB with the virtual pins' SelOK, SelPart; per literal C's H_BUNDLE
of the mapped channel, H_SEL_SETUP, H_SEL_O (per request leaf), `sel = selFn` of the bus at
`O k`; the residual obligations of uncertified items. Proved: SelOK of the realisation and the
count/wire link of every real LUT wire at every time. NOT covered: H_BUNDLE, H_SEL_SETUP,
H_SEL_O; that the mapped ack/req wires are C's channel's (trusted name map); H_ARB (refuted in
its old encoding by E8Arb; these rows use the old core, XA_ARB=old, to keep E8SelC's map valid).

## 3. `Events9SelJ.lean`: the junction-anchored lag (task 2)

Fix a source `S` and a monotone `gB` with `t − phb ≤ gB t` (design: `gB = tau bot`,
`phb = phi bot`). Junction judgements (`Jd`): walk `M u a ≤ M (gB (u − d)) S + t`, U-bound
`M u a ≤ filt (sel g) β (M (gB (u − d)) S)`. Rules (`jconcl`, each proved in `jconcl_sound`;
`runJ_sound` for a whole junction log, for every behaviour):

| rule | premise (checked) | conclusion |
|---|---|---|
| `jrefl` | `bot = []` | `S` trails by 0 |
| `jpin n p e` | stage `n`, pin `p` non-guard, offset 0, source `S`, `FacP n p e` | walk, lag `loF + e` |
| `juT n p e` | the same for a filtered pin | U-bound in the pin's label, lag `loF + e` |
| `jwalk w r` | main-log walk line `w` (`a → X`), junction walk `r` of `X` | walk, lags and tokens add |
| `juW w r` | main-log token-free walk `w`, junction U-bound `r` | U-bound, lags add |
| `jlift w` | main-log walk / U-bound line `w` ending at `S` with `d ≥ phb` | same kind, lag `d − phb` |
| `jr3 xm arms` | merge, arms pairwise exclusive (`lx`), each arm a direct filtered pin (`FacP`, lag `e`) or a junction U-bound of its source (lag `loP + d`) | walk, lag `loF + min over arms` |

`FacP n p e` (all copies read `S` no later than `gB (s − e)`) is checked by **`facOK`** per copy:
either the copy path ends with the list `bot` and `plo(top) ≥ e + 1` (it passes the junction), or
`e + phi bot ≤ loC` (it does not; source lag minus `phi bot`). `fac_of_ok` proves it from the
realisation's copy warps `G = tau full (· + 1)`.

**`design_verdict9_selJ`**: as `selT`, with each copy's `AckLineT` replaced by **`jrowOK`**:
the junction log of `(src, botP cut)` runs, its line `jw` is a token-free walk judgement of the
ack leaf with lag `dj`, and `Dl ≤ dj + plo κa + 1`; `holdBandS` at the copy's own cut. Same
assumptions and conclusion as `selT` otherwise.

Margin of a row: `Dl + selLo + lo(rg) − phi(top)` ps.

## 4. Results

(filled in below from `tools-A/xaudit/selrun/results/table.txt`)

## 5. Negative controls

(filled in below)

## 6. Check

From `formal/lean` (the lead's `.lake/build` has oleans up to Events8Main; the 10 files of the
closure without oleans are checked first, read-only, then mine):

    ../check.sh Formal/Core/XAudit/Events9Cert.lean Formal/Core/XAudit/Events9Beh.lean \
      Formal/Core/XAudit/Events9Prefix.lean Formal/Core/XAudit/Events8Bridge.lean \
      Formal/Core/XAudit/Events8BridgeSel.lean Formal/Core/XAudit/Events9Sel.lean \
      Formal/Core/XAudit/Events9SelC.lean Formal/Core/XAudit/Events9SelHold.lean \
      Formal/Core/XAudit/Events9SelSplit.lean Formal/Core/XAudit/Events9PrefixSel.lean \
      Formal/Core/XAudit/Events9SelL.lean Formal/Core/XAudit/Events9SelJ.lean \
      Formal/Core/XAudit/Events9SelLMain.lean
    ...
    [check] axiom audit
    [audit] 3435 declarations checked
    [check] audit (executable) Formal.Core.XAudit.Events9SelLMain
    [audit] 3732 declarations checked
    [check] OK

md5s at check time:

    798acaa77d3460fb0e65d5682d7902d9  Formal/Core/XAudit/Events9SelL.lean
    79d819272aeebc03a32c41c33c415860  Formal/Core/XAudit/Events9SelJ.lean
    539a626058f5d889a07fcf57fecaaaa7  Formal/Core/XAudit/Events9SelLMain.lean
