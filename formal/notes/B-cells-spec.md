# B: the routed storage cells under THE Spec (S3 cell theorems), 2026-11-06

**Problem.** For shard C's composition (notes/C-route-S4.md (b)): when does a LUT whose output returns through its
routing to one of its own pins behave as a C-element in EVERY behaviour of the Spec (per-pin read times inside the
Adm bands, transport/glitches allowed)?

**Lean (standard axioms, check.sh OK).**
- `Formal.Cells.SpecCElem.celem_forced` / `celem_forced'`. Premises: collapsed relation `CGateOK` (C's `collapse`),
  composite bands `[lo i, hi i]` (`SpecFbChain.cbands_of_sums`), feedback pin j with `src j = out`, `lo j ≥ 1`;
  INIT facts `hall`/`hhold` (C-element over the C inputs `ci`, polarities `pol`, other pins held at `ov`);
  held pins really held (`hoth`); environment `hA`: a C input changes only when q already shows the input's old
  value and has shown it for Δ i; timing `hloop` (∀ C input: hi j ≤ Δ i + lo i), `hM`/`hi0` (separation);
  q quiet on (S0 - H, S0]. Conclusion: every toggle from S0 is forced (every C input shows the new value at its
  read) and toggles are ≥ M apart.
- `SpecCElemFact.cfact` + `hall_of_cfact`/`hhold_of_cfact`: the INIT facts as a decide over 2^k addresses.
- `SpecCElemWit`: joint non-vacuity witness (a switching C-element run meeting every premise).
- `CElemPS` (generated, tools-B/ps/gen_celem_ps.py): 361 C-elements of `DecodedPS.net` pass the INIT and wiring
  check (`row_hall`, `row_hhold` on `net.gates.getD q default`).
- `ViewPS.view_collapse`: in every behaviour of THE circuit, listed gates with checked copy chains satisfy CGateOK
  (via C's `SpecChain.collapse_net`); `const_hold`: constant gates hold their value.
- `CElemView.target_celem_forced`: the C-element theorem stated on `Behaves p (circuit net boundary) x` for every
  row list passing `crowOK` (instance `CElemViewPS`, 361 rows).
- Latches: `SpecLatch.latch_close` (clean close and hold; derived windows: enable open ≥ (hi e - lo e) + hi j, data
  stable from hi d + hi j - lo e before the close to hi e after), `SpecLatchWit`, `SpecLatchFact`,
  `LatchView.target_latch_close` (instance `LatchViewPS`, 4,185 rows; out/target_ps_latch.json lists each latch's
  derived windows).
- Arbiters: `ArbViewPS.target_ps_arb_clean_set` / `ArbViewPSReset` (the nine state LUTs decide a separated arbitration
  cleanly, both directions); under H_ARB(T): `ArbGrantPS.target_ps_grants_excl` (grants exclusive once the state has
  settled) and `ArbAckPS.target_ps_ack_low` (the losing client's ack stays low while settled; 18 acks). Open: the
  settling window and the server-path obligation (static: grant -> A0 ≥ 1,225 ps FAST_MIN).
- Link stage: `SpecLatchSep.latch_close_sep` (a latch's enable width from its controller's toggle separation; every
  latch's enable source is a covered C-element).
- Mux joins (42): `SpecCElemWin.celem_forced_win`, `CElemWinView.target_celemw_forced`, instance `CElemWinViewPS` (C-elements while the select is held at its selecting value).

**How C uses it.** `hA` = persistence of the Huffman/abstract machine (C: WinInv/Keller) + a distance bound: an input
change that responds to q's change arrives no sooner than the shortest causal return path. The static all-paths
distance (out/target_ps_allpaths.json, out/target_ps_celem.json) is a sound but loose Δ (binding 0.295 at g = 1 is a
false path, JOURNAL-B 08:45); protocol-aware distances are needed for a tight margin.

**Not covered.** hA itself; the other 4,236 storage gates (latches: use SpecLoop.cgate_switch with the bundling
window; arbiters: ArbClean / H_ARB(T)); the bridge from C's `collapsed` view entries to these rows.

**Evidence on the environment premises (simulation, untrusted; JOURNAL-B 2026-11-06).**
- C-element races: all-paths static bound κ ≤ 0.295 (binding path is a false path under the protocol); recorded
  episodes 0.415 (RaceTablePS); C's 23 order-level persistence pairs: 0 withdrawals in a timed 13-pair run; ua1 of
  merge10 timing-safe to κ ≈ 0.38 under C's causal order.
- Latches: every close in a 13-pair run meets latch_close's windows with ≥ 2.26 ns slack (hold binding); the tightest
  hold survives an adversary to κ = 0.5 (204 ps left), because the data release is caused by the enable's own fall
  through a 43-arc chain; short structural paths through OR/AND gates are not sensitizable.
- Lesson for a sound static bound: path sums must follow the protocol's causal order (which input is the LAST to
  arrive at each join), not graph distance.
