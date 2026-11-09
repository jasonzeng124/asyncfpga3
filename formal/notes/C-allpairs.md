# Shard C: from one pair to every pair (design note, 2026-11-09; nothing here is proved unless a Lean name is given)

## Problem, plainly
THE statement (`NetCorrectSeq`) is about every pair a, b < 2^31 and any number of pairs. The S4 route of
2026-11-08 (`Net/AO/*`) proves: if ONE finite certificate (the event order of one run, bounds, separations, data
claims with concrete values) passes local checks, every admissible behaviour follows it. A certificate is a
property of one operand pair: its length is the run's length (8,333 events for (12,18), 12,059 for (17,5)), and its
data claims carry that pair's register values. There are 2^62 pairs. So the per-pair theorem can at best give
`NetCorrectSeq` restricted to one pair (`va 0 = 12, vb 0 = 18, n = some 1`): useful as a milestone and a
non-vacuity check, not as THE theorem.

## What has to change (three independent pieces)
1. **Control: word-indexed certificates.** The control's event order in one loop iteration depends on the data only
   through the branch it takes (the 1-bit conditions the control reads: `cmpi` results, the shift loop's parity
   test, the exit test). Cut every run at the loop-head events into *windows*; a window's certificate depends only
   on its *kind* (the branch taken). A run is then a word `prefix · k1 · k2 ... km · suffix` over finitely many
   kinds, determined by the token-level run (`GcdHw.Seq`), and its certificate is the concatenation (the
   *unrolled* certificate: window j's events of node u are numbered from the offset `o_j(u) = Σ_{i<j} len_i(u)`).
   The timed theorem (`AO.timedA_follows`, `timedA_live`) applies to the unrolled certificate unchanged; what is
   new is proving its hypotheses for EVERY word from finitely many checks:
   * each obligation (local check at a node, TO row, Sep/Up entry, guard) is about events within a bounded number
     of events of each other; if every such neighbourhood lies within two consecutive windows, a check of every
     *two-window* certificate `W_k · W_k'` (for each allowed kind pair, plus prefix/suffix junctions) covers every
     word (`OccWindow.lcheck_of_window` is this for the plain local check);
   * the locality itself is an instance property: per node, the counts its readers can see stay within one window of
     each other (the bounds `L` enforce it when every node of `D v` is causally linked to every other inside one
     window).
2. **Data: symbolic claims.** Today's claims say "node z holds the value 1 on [s, e)" with the value computed from
   the run. For every pair the claim must say "z holds f(register values) on [s, e)", with f the MLIR operation the
   unit implements (a 1-bit `cmpi` result for the nodes the control reads). That needs, per datapath unit of THE
   target, a combinational equivalence (`Net/Compute/*` did this for the old target from yosys cells: `add_sound`,
   EqZero, bitwise) on the DECODED netlist, plus a settle bound (bundling: the unit's inputs stable from s - settle).
   The control only reads 1-bit conditions, so the window kind fixes the guard values the local checks need; the
   symbolic claims are needed to show the guards hold and that the registers carry the token-level values.
3. **Refinement: the word is the token run.** Show that the kind sequence the circuit follows is the branch
   sequence of the token-level run of bdc's graph on the same pair (`GcdHw.Seq.gcd_hw_seq`), by induction over
   windows: at each loop head, the registers hold the token values (piece 2), so the condition bits, hence the next
   kind, are the token run's.

## Order of work
- Piece 1 is generic Lean and does not need THE target's certificate to pass yet: the unrolled certificate and the
  lifting of `TmOK`, `LStep`/`LSound`, `LCheckXA`, `TOA`, Sep/Up soundness from two-window checks.
- Piece 2 starts with identifying THE target's datapath units in the decoded netlist (the cone of each condition
  bit the control reads) and porting `Net/Compute` to `DecodedPS`.
- The one-pair certificate (data layer R1-R4, B's R2/R3) remains the test bed: every two-window check is a check
  of a slice of it.

## Not covered by this plan
Liveness bounds across words (the timed theorem gives a bound per certificate; for every word the bound grows with
m, which is enough for `Correct`'s "eventually"), reset/quiet start (`RIslPS`, separate), pipelining (refuted;
SeqEnv).

## Status at the end of 2026-11-09 (shard C)
- Piece 1 (control windows): `Net/AO/Window.lcheckXA_window` (Lean): the AND-OR, data-guarded local check of a long
  certificate inside a window's box from the window's check; pre-window causes (reset, last events of quiet nodes)
  are admitted. Evidence (untrusted Python, tools/tocc/win): from iteration 2 on, same-kind main-loop windows are
  shift-identical across iterations and pairs (kind = number m of inner shift iterations, m ≥ 2 continuing, m = 1
  exit); two L entries depend on the previous kind; iterations 0 and 1 belong in the prefix. Open: the window form of
  the timing checks (TOA, SepOKA, UpOKA, GuardTime), coverage, nested inner windows, delay variation.
- Piece 2 (datapath): `Net/Compute/PS/Uselect1.uselect1_ps` (Lean, check.sh OK): the decoded gates of unit uselect1
  compute its MLIR op for all inputs, given the zero-delay gate equations (`Settled`). `Timing/SpecSettleSym`
  (Lean): value-free settle certificates give `Settled` at every time inside the windows, for every (g, κ). Python:
  all 20 units match Net/Compute's cells (uori4 needs its own extraction). In progress: the other units, the timed
  instance.
- R1 data-layer failures: not races (env-stall simulations); a proof-rule gap, closed in Lean by `UpOKA`'s relative
  clause (Up a p with Sep a e0).
- Quiet start: `CViewPS.reset_quiet_PS` (Lean): the 3,224-node reset island holds its values during reset.
