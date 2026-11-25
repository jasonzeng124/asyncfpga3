# A-e8causal (probe E8Causal, shard A): the verdict prefix by prefix

STATUS (2026-10-29): PARTIAL-DONE. 3 Lean files, check.sh OK (3274 declarations, §6). Task 1
done; task 2 done in Lean, with no row evaluated (needs new certificate log lines) and only at a
source-anchored lag; task 3 partly in Lean (prefix behaviours), with the arbiter side open.

## 0. Summary

1. **Prefix verdict (done, Lean).** `Events9Prefix.safe8_upto`: the core safety induction
   behind `design_verdict9` (`Events8.safe8`) with SelOK, LineOK, PinOK, ExclOK and the guard
   facts assumed only at the samples `s < t0` gives the count/wire link of every node on
   `[0, t0]`. **Lag L = 0** (a node's value at `t` is computed from its sample `F t ≤ t − 1`).
   `verdict9_upto`, `design_verdict9_upto` lift it through the certificate and the netlist;
   `safe8_of_upto` and **`design_verdict9'`** re-derive `safe8` and `design_verdict9` with
   their exact statements (statement-preserving corollaries). **`causal_close`**: if SelOK at
   each sample `s` follows from the link at times `< s`, the link and SelOK hold at all times.
2. **H_ACK_LAG (done in Lean, with two caveats).** `Events9PrefixSel.design_verdict9_selL`:
   E8SelC's split select verdict with NO wire-level lag hypothesis. H_ACK_LAG_w is replaced by
   checked data (an identity check `ackOK` of the channel's ack/req wires against real
   nodes, and two lines of the accepted derivation log, `ReqLine` and `AckLine`), proved
   through the prefix verdict and `causal_close`. Select-side trace hypotheses left: C's
   **H_BUNDLE**, **H_SEL_SETUP**, and **H_SEL_O** (new, part of the setup pair: by `O k` the
   channel's request has reached transaction `k`). Caveats:
   - the lag the log can support is SOURCE-anchored (`Dl + phi bot ≤ dW + 1`), so the hold
     rows of `selL` are essentially E8SelC's source rows, not its split rows; on E8SelC's
     numbers this would cover 10 of the 12 slow/fast/gb rows (the src rows that pass), not
     3 gb / 4 gb, and no indep row (estimate, §2.4; NOT evaluated);
   - no certificate generator emits `ReqLine` / `AckLine` yet, so NO gcd_hw row has been
     evaluated with `selL`.
3. **Finding (Lean negative control `sibling_lag_neg`).** E8SelC's split lag `D = plo π`, with
   π a path from the ack to the pin's OWN junction, is not a consequence of causality for
   tokens routed to the SIBLING branch (mux `uj0`/`uj1`, the two steer branches): such a token
   closes the ack through the sibling's arm, which does not pass through that junction. The
   correct junction lag is the minimum over all arms by which the ack can close, each measured
   to where it meets the copy path (with the spread of the unshared stretch). H_ACK_LAG_w as
   checked by xselhold's split rows is therefore an unjustified hypothesis on rows where the
   sibling arm is faster; since it is a named hypothesis this is not unsound, but those rows
   should not be cited as "H_ACK_LAG_w follows from causality".
4. **E8Arb (§4).** Lean: prefix behaviours (`Beh7P`), their extension to a `Beh7` with the
   same counts (`ext`, `M_congr`) and the link on the prefix (`link_upto_P`). Missing: the
   design-level prefix H_ARB, and a CAUSAL form of E8ArbFix's canonical ctl (its `Settled`
   looks at q's future), which would give the HARB step a lag δ ≥ H + K.

## 1. Task 1: the prefix verdict (`Formal/Core/XAudit/Events9Prefix.lean`)

Definitions: `SelAt x s` (SelOK at one sample, all filtered pins and copies); `Link x t`
(`c j u = ph (v j) (M u j)` for every node `j` and every `u ≤ t`); `GuardCntB`, `GuardPinB`
(Events8's GuardCnt / GuardPin at samples `< t0`).

| theorem | assumed | proved |
|---|---|---|
| `pin_val_at` | SelOK and LineOK at the ONE sample `s` of pin `p` | `Beh7.pin_val` at `s` |
| **`safe8_upto`** | `net.OK7`; at every sample `s < t0`: SelAt, LineOK, PinOK, ExclOK; guarded pins: GStruct + GuardCntB t0 (certified) or GuardPinB t0 | `Link x t0` |
| `safe8_of_upto` | exactly `safe8`'s hypotheses | exactly `safe8`'s conclusion |
| **`verdict9_upto`** | `verdict9`'s checks (accepted log, certified items; these are count facts at all samples); SelOK and the residual obligations at samples `< t0` | `Link x t0` |
| `causal_close` | the prefix verdict as a function of `t0`; SelAt `s` from the link at all times `< s` | SelOK and the link at all times |
| **`design_verdict9_upto`** | `design_verdict9`'s checks and trace hypotheses (SatPin, constants, reset, H_ARB at all times) | ONE realisation `bh` (independent of `t0`) with `design_verdict9`'s properties, and for every `t0`: SelPart + SelAt on samples `< t0` + residuals on samples `< t0` ⇒ `Link bh t0` and every real LUT wire's link on `[0, t0]` |
| **`design_verdict9'`** | (statement identical to `Events9.design_verdict9`) | (same), proved from the prefix form |

Why the lag is 0: in `safe8`'s induction, the value at `t` uses the node's sample `s = F t`
(`F t < t`, `loF ≥ 1`) and copies/feedback at `G s, Q s < s`. So hypotheses at samples
`< t0` decide `[0, t0]`. The all-times theorem is the corollary at `t0 = t`.

NOT covered: H_ARB stays at all times (the realisation is built from it, §4); the residual
obligations of uncertified items are vacuous only on a CLEAN row, as before.

## 2. Task 2: H_ACK_LAG (`Formal/Core/XAudit/Events9PrefixSel.lean`)

### 2.1 Why the circle closes
SelOK at sample `s` (pin `(j,p)`, copy `i`) is a statement about the select wire at its read
time `gS s ≤ s`. Through `route_hold` (rg's band, `lo(rg) ≥ 1` by `d.WF`) and H_BUNDLE
(`held_wire`) it needs the channel mid-transaction on `[O k, gS s − lo(rg)]`, i.e. at times
`≤ s − 1`. Mid-transaction at `σ` is a statement about the req/ack WIRES at `σ` (and the req's
delay-line source at `tau κ σ ≤ σ`); the prefix verdict gives their counts at `σ < s` from SelOK
at samples `< σ`. `causal_close` is the strong induction on `s`.

### 2.2 The checked data and the count facts
- **`ackOK e na nq κ`** (decidable): `na`, `nq` real reset-0 nodes; the entry's ack wire is
  `na`'s LUT output; the request wire is the top of a checked buffer chain `κ` (`bufPath`:
  `chainOK` + every element input 0 of a 1-input buffer) from `nq`'s LUT output
  (`bufPath_val`: `x rq t = x (out nq) (tau κ t)`).
- `inTx_of_cnt`: ack reads `A`, req reads `R` (reset 0), `2k+1 ≤ R ≤ A + 1`, `A ≤ 2k+1` ⇒
  `req ∨ ack`.
- **H_SEL_O**: for every transaction `k` the source reaches (`M u src = 2k+1` for some `u`),
  `2k+1 ≤ M (tau κ (O k)) nq` (restricted to reached tokens so that a run with finitely many
  tokens can satisfy it; an earlier draft quantified over all `k`, which would have been vacuous). **H_REQ_CNT**: `M (tau κ v) nq ≤ M v na + 1`.
  **H_ACK_CNT(Dl)**: `M (tau bot r) src = 2k+1 → σ < r + Dl → M σ na ≤ 2k+1`.
- **`design_verdict9_selP`**: `design_verdict9_selS` with H_ACK_LAG_w replaced by `ackOK`
  (checked), H_SEL_O, H_REQ_CNT, H_ACK_CNT(Dl), and `holdBandS` at lag `Dl` (checked; no
  certificate path needed). Conclusion strengthened to SelOK AND the link at all times.

### 2.3 Discharging the count facts from the log
- `ReqLine J nq na w` (decidable): line `w` is an unlabelled walk `nq → na` with ≤ 1 token.
  `reqCnt_of_line`: H_REQ_CNT for every behaviour (`runLog_sound`).
- `AckLine J na src w D phb` (decidable): line `w` is an unlabelled walk `na → src` with 0
  tokens and `D + phb ≤ dW + 1`, `phb = phi bot`. `ackCnt_of_line`: H_ACK_CNT(D).
- **`design_verdict9_selL`**: `selP` with H_REQ_CNT / H_ACK_CNT from checked lines.

Plain statement of `design_verdict9_selL`. Assumed: Recog6, OK7, an accepted log with the
certified items, the select map with `entOK` and `ackOK` per literal and a `ReqLine` per
literal, a `holdBandS` row and an `AckLine` per copy and literal (all checked by Lean
decision procedures, to be evaluated by an executable); SatPin, constants, reset, H_ARB and the
virtual pins' SelOK; SelPart; per literal C's H_BUNDLE of the mapped channel, H_SEL_SETUP,
H_SEL_O, and `sel = selFn` of the bus values at `O k`; the residual obligations of uncertified
items. Proved: SelOK of the realisation and the count/wire link of every real LUT wire at every
time. NOT covered: H_BUNDLE, H_SEL_SETUP, H_SEL_O themselves; the trusted map (channel name,
which wire is the ack); H_ARB.

### 2.4 What the rows would look like (estimate, not evaluated)
`holdBandS(Dl)` with `Dl = dW + 1 − phi bot` reads `phi top − 1 + 1 ≤ dW + 1 − phi bot + selLo
+ lo(rg)`, i.e. `phi full ≤ dW + 1 + selLo + lo(rg)`: E8SelC's SOURCE row with `D = dW` (the
walk's band delay instead of the shortest gate path). If the walk delay equals the gate path's
low end, the pass/fail pattern is E8SelC's "src" column: pass on all slow/fast rows and on
d gb, 5 gb; fail on 3 gb (−139) and 4 gb (−701) and on every indep row. Whether walks with 0
tokens `ack → src` and ≤ 1 token `req source → ack` exist in the derivation log is expected
(the ack follows the source through the join/steer and a merge of the branches, which the
existing SUB rule handles; the request source's controller reads the ack through an inverted
pin, an `r1` step with offset 1) but NOT checked: cert9.py does not emit these walks.

To recover the split rows' margin one needs a JUNCTION-anchored count rule: a walk from the ack
to each arm's meeting point with the copy path, plus monotonicity of the shared tail warp
(the same `tau bot` for the own arm; for a sibling arm meeting at wire `w'` on `bot`, the
unshared stretch's spread). Not built.

### 2.5 The sibling-branch finding
`sibling_lag_neg` (decide): an ack that merges two branch arms of one source, own arm lag 30
(through the junction), sibling arm lag 5; transaction 0 goes to the sibling. The junction
shows transaction 0 at `r = 19`, the ack's count is 2 at `σ = 26 < r + 30`; at the sibling lag
the bound holds on the whole window. On gcd_hw: for `umuxN.uj1`'s junction (`uj1/I0`, the
select link's request after its route arc), tokens with `s = 0` close `ctl_ack = z_ack`
through `uj0`, `uor`'s other pin and `uj0`'s own route arc; the lag from `r` (time at `uj1/I0`)
is then at least `plo(z_ack → uj0) + lo(arc0) − hi(arc1)`, not `plo π`. Margins on the mux rows
are several ns, so the corrected value probably still passes, but that is argued, not computed.

## 3. Negative controls
- `sibling_lag_neg` (above): H_ACK_CNT fails at the own-arm lag; holds at the min lag.
- The existing E8SelC / HDsub controls are unaffected (no file of theirs changed).

## 4. Task 3: what the prefix form gives E8Arb's "uncontested" discharge

E8Arb (§4 "Circularity") needs: HARB on `[0, t)` ⇒ counts on `[0, t + δ)` ⇒ port protocol and
`Unc W` there ⇒ HARB on `[0, t + δ')`. `design_verdict9_upto` gives the middle arrow for SelOK
only: `design_beh8` builds the realisation from H_ARB at ALL times (the virtual nodes' ND7
come from `harb.1`). What exists now and what is missing:

1. **Prefix behaviours (Lean, `Events9PrefixExt.lean`).** `Beh7P net b sel t0`: `Beh7`'s data
   with the node equations `hc`, `hpin`, `hq` only on `[0, t0]` (warps, reset, skew, guarded
   count at all times). `Beh7P.ext` extends the signals after `t0` by the node equations (well
   founded) into a `Beh7` with the same warps, reset, select reads and guarded count, equal on
   `[0, t0]` (`ext_c`). **`M_congr`**: counts depend only on `F`, `G`, `r`, `gc`, so the
   extensions at different `t0` built on the SAME warps have the SAME counts.
   **`link_upto_P`**: `safe8_upto` for a prefix behaviour: the count facts at samples `< t0`
   give the prefix behaviour's own signals the link on `[0, t0]`. Lag L = 0 again.
   So "H_ARB on `[0, t0]` ⇒ link on `[0, t0]`" holds at the `Beh7` level, provided the virtual
   nodes' warps are fixed in advance (independent of `t0`).
2. **Missing (design level):** a `Beh7P` built from SatPin plus a PREFIX H_ARB over the parsed
   netlist (`ndReal7` reads a virtual source through `hW`, the grant/R0 wire = virtual signal,
   at all times; in prefix form only on `[0, t0]`). Routine but not written.
3. **Missing (arbiter side), and a real obstacle:** E8ArbFix's canonical ctl `ctlc` is not
   causal. `Events9Arb.Settled a q f4 u` quantifies over q's whole FUTURE in the A0-low phase
   (`∀ u' ≥ u, A0 low on [u, u'] → q u' = q u`), so the virtual ctl at time `u + K` depends on
   the real q after `u + K`. A global realisation from the full trace is fine for the all-times
   theorem, but in the induction the conditions B1/B2/C/hstall at times `≤ t0` then refer to q
   after `t0`, which depends on the environment's requests after `t0`, i.e. on counts after
   `t0`. A prefix discharge needs a bounded-horizon settledness (q constant on `[u, u + H]`,
   with `hstall` giving `H`), which makes the HARB step's lag `δ ≥ H + K` instead of 0.
4. **Then Unc W and the protocol are prefix facts of the counts.** With the link on `[0, t0]`,
   the request and grant wires on `[0, t0]` are their counts' parities, so `Unc W` on `[0, t0]`
   is a count statement (no two requests pending within `W`: an exclusion-style certificate row
   over the arbiter's request sources) and the port protocol (A0 rises only with R0 high, falls
   only with R0 low) is a walk inequality. Both, once certified, hold for every behaviour at
   every time. E8ArbFix §4's certificate gap (a LIVENESS rule for the shadow-grant walks) is
   independent of the prefix question and still open.
5. Shape of the final argument: the same as `design_verdict9_selP`, i.e. `causal_close` over
   `t0` with the step "HARB conditions on `[0, t0 + 1]` from the link on `[0, t0 − δ]`". With a
   positive lag δ the closure is a strong induction on `t0` whose step uses the link only up to
   `t0 − δ`, which `causal_close`'s proof pattern handles unchanged (δ ≥ 0).

## 5. Files

- `formal/lean/Formal/Core/XAudit/Events9Prefix.lean` (imports `Events9Beh`).
- `formal/lean/Formal/Core/XAudit/Events9PrefixSel.lean` (imports `Events9Prefix`,
  `Events9SelSplit`, read-only).
- `formal/lean/Formal/Core/XAudit/Events9PrefixExt.lean` (imports `Events9Prefix`).
- No file of E8SelC / E8ArbFix / HDsub was edited.

## 6. Check

The lead's `.lake/build` has no oleans for Events5..Events9Sel*, so check.sh was run on the
whole missing closure (E8SelC's 23 files minus Events9SelMain, plus my three), from formal/lean:

    ../check.sh Formal/Core/XAudit/{Events2PinDesign,Events4,Events5Line,Events5,Events6Gate,Events6Cert,
      Events6Design,Events6Beh,Events7Core,Events7Excl,Events7Cert,Events7Beh,Events8Core,Events8Cert,
      Events8Beh,Events8Bridge,Events8BridgeSel,Events9Cert,Events9Beh,Events9Sel,Events9SelC,
      Events9SelHold,Events9SelSplit,Events9Prefix,Events9PrefixSel,Events9PrefixExt}.lean
    ...
    [check] axiom audit
    [audit] 3274 declarations checked
    [check] OK

Once lake has built Events9SelSplit, the short form is
`../check.sh Formal/Core/XAudit/Events9Prefix.lean Formal/Core/XAudit/Events9PrefixSel.lean Formal/Core/XAudit/Events9PrefixExt.lean`.
md5s at check time (unchanged after):

    58f8b6dcc75405a145b5957358a8a3e5  Formal/Core/XAudit/Events9Prefix.lean
    f993626f23b5cd2c4d33aec7cde732e7  Formal/Core/XAudit/Events9PrefixExt.lean
    9a04f599af082fcb98f83ba5221bc007  Formal/Core/XAudit/Events9PrefixSel.lean

Warnings only: unused simp args (copied from Events7Core's pin_val), deprecated if_pos/if_neg
in Events9PrefixExt. Root imports if wanted: the three modules (none defines `main`).
