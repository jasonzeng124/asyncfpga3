# C-11e: port shard C off `Formal/Cells/Prelim.lean`

Status: IN PROGRESS (notes kept current as work proceeds).

## Inventory (step 1)

Shard-C modules whose import closure contains `Formal.Cells.Prelim` (before this probe):

* Prelim only, no other B module (fully portable now):
  `Gen.Netlist` (direct), `Gen.Cells`, `Gen.ProofsPrims`; `Net.Import.Netlist` (direct),
  `Net.Import.Cells`; `Net.HandshakeMuller` (direct), `Net.PerLink`, `Net.PerLinkEvent`,
  `Net.PerLinkPin`, `Net.HandshakeLive`, `Net.HandshakeWitness`, `Net.EndToEnd`,
  `Net.EndToEndToy`, `Net.EndToEnd2`, `Net.EndToEnd2Toy`.
* Through B modules (still Prelim-based):
  `Gen.ProofsCE` (CElemFn, CTree, CElemTiming), `Gen.ProofsLatch` (Latch, LinkHandshake, Bundling),
  `Gen.ProofsLink` (CElemFn, Latch, LinkHandshake, Bundling), `Gen.ProofsCtl` (LibCtlMergeMux),
  `Gen.ProofsArb` (CElemFn, ArbKleene, ArbBinary, ArbHandover, ArbHeldTimed, ArbA0Fork),
  `Gen.ProofsMisc` (Latch), `Gen.All`; `Net.Import.Proofs` (CElemFn, Latch, ArbKleene);
  `Net.Muller` (direct + CElemFn) and `MullerRun`, `MullerSI`, `MullerTimed`, `MullerTimedInst`,
  `MullerTimedCx`; `Net.Ring` (CElemFn), `BridgeRing`, `BridgeWire`;
  `Net.Fasm.Basic` (direct + CElemTiming) and `Fasm.CePair*`, `FasmLink.*`, `Timing.RoutedCePair`.

Not importing Prelim, only mentioning it in comments: `Net.Prelim`, `Timing.Semantics` (left
untouched: tcheck's `sync.sh --check` requires them byte-identical to its copies).
