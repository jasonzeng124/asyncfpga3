# B: the routed C-element under THE Spec (S3 cell theorem), 2026-11-06

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
  check (`row_hall`, `row_hhold` on `net.gates.getD q default`). [status: see JOURNAL-B]

**How C uses it.** `hA` = persistence of the Huffman/abstract machine (C: WinInv/Keller) + a distance bound: an input
change that responds to q's change arrives no sooner than the shortest causal return path. The static all-paths
distance (out/target_ps_allpaths.json, out/target_ps_celem.json) is a sound but loose Δ (binding 0.295 at g = 1 is a
false path, JOURNAL-B 08:45); protocol-aware distances are needed for a tight margin.

**Not covered.** hA itself; the other 4,236 storage gates (latches: use SpecLoop.cgate_switch with the bundling
window; arbiters: ArbClean / H_ARB(T)); the bridge from C's `collapsed` view entries to these rows.
