# A-lit-2: Literature survey (track 13, part 2)

Scope: gate- and timing-level hardware verification in proof assistants, formal timing analysis,
formal models of FPGA LUTs and bitstreams, and dataflow/elastic/Kahn/latency-insensitive circuits.
Each item was found with WebSearch and, where marked [repo checked], its repository was also
fetched with WebFetch on 2026-10-27. Many publisher and university hosts did not resolve from
this sandbox (arxiv.org, *.epfl.ch, cs.utexas.edu, doc.ic.ac.uk), so some summaries rest on search
abstracts and not on the full text. Those entries are marked [abstract only]. I have not invented
any citation. If I could not confirm a detail, I say so.

Relevance key: "us" means this project, i.e. Lean 4 proofs about bundled-data async cells built
from 7-series LUTs, and Dynamatic-generated bundled-data circuits.

---

## 1. Dataflow circuits and Dynamatic (most relevant)

### 1.1 Graphiti (Lean 4, Dynamatic): READ THIS FIRST
- Y. Herklotz, A. Elakhras, M. Camaioni, P. Ienne, L. Josipović, T. Bourgeat. "Graphiti: Formally
  Verified Out-of-Order Execution in Dataflow Circuits." ASPLOS '26, pp. 821-837.
  DOI 10.1145/3779212.3790166.
- Code: https://github.com/VCA-EPFL/graphiti [repo checked]. Apache-2.0. `lean-toolchain` is
  `leanprover/lean4:v4.34.1`, and it depends on Mathlib `v4.34.1`. Libraries are `GraphitiCore`
  and `GraphitiProjects`. `benchmarks/dynamatic/` holds Dynamatic `.dot` files, and
  `Graphiti/Core/Dataflow/` has `DotParser`, `DynamaticPrinter` and `DynamaticTypes`. A Rust
  oracle does the matching, and a `--fast` flag selects an unverified rewrite path.
- What it proves: the framework is embedded in Lean 4 for dataflow circuits as produced by HLS.
  It has a metatheory of graph refinement, a verified general-purpose rewriting algorithm, and a
  verified loop rewrite that adds out-of-order execution through tagging. The abstract reports
  2.1x over in-order HLS and 5.8x over a verified static HLS (Vericert). The core semantic object,
  quoted from `Graphiti/Core/Graph/Module.lean`:
  `structure Module (Ident S) where inputs : PortMap Ident (RelIO S); outputs : PortMap Ident (RelIO S); internals : List (RelInt S); init_state : S → Prop`.
  Ports are state relations. Components in `Dataflow/Component.lean` are unbounded `List`
  queues: inputs append, outputs pop the head, and merge removes any element. Only `join` uses a
  bounded list. **There is no clock, no latency and no valid/ready wire level.** The handshake
  is abstracted into atomic token transfers. The refinement notion lives in another file that I
  did not open. The docstring says inputs may be followed by internal steps but outputs may not.
- Relevance to us: this is the closest existing work. It covers the token level of exactly the
  circuits Dynamatic emits, in Lean 4, under a permissive license. It stops where we start,
  though: it says nothing about whether a handshake implementation (our LUT/bundled-data
  cells) refines its token-level `Module`. The natural bridge theorem is "our gate/timing-level
  cell model refines Graphiti's component `Module` under named timing hypotheses". Toolchain gap:
  we pin our own Lean/Mathlib, it is on v4.34.1, and it needs Mathlib broadly. We should reuse
  definitions by copying or adapting them, not by adding it as a lake dependency.

### 1.2 Wavelet / "Let it Flow" (Lean 4, asynchronous dataflow)
- Z. Lin, Y. Cai, M. Surbatovich. "Let It Flow: A Formally Verified Compilation Framework for
  Asynchronous Dataflow." Proc. ACM Program. Lang. 10 (PLDI 2026), article 185.
  DOI 10.1145/3808263. arXiv 2608.05451.
- Code: https://github.com/plum-umd/wavelet [repo checked]. The Lean part is in
  `wavelet-core/lean` (`leanprover/lean4:v4.24.0`), checked with `lake build Thm`. The page
  showed no license, so treat it as unlicensed until checked.
- What it proves [abstract only]: a compiler from a Rust-based DSL to asynchronous dataflow
  graphs. Two core backend passes are formalised in Lean with forward-simulation and determinacy
  results. The frontend uses capabilities and fences for memory. The paper cites Graphiti and
  ElasticMiter as prior Dynamatic rewrite verification and suggests connecting to Graphiti.
- Relevance to us: it shows a second Lean 4 dataflow semantics with a determinacy (Kahn-style)
  result. If we need "the graph is deterministic, so any interleaving of handshakes gives the
  same streams", this is where to look. It is also token-level only, with no gates or timing.

### 1.3 ElasticMiter (model checking, Dynamatic)
- A. Elakhras, J. Xu, M. Erhart, P. Ienne, L. Josipović. "ElasticMiter: Formally Verified
  Dataflow Circuit Rewrites." ASPLOS '25 (published 2025-03-30).
  PDF: https://www.epfl.ch/labs/lap/wp-content/uploads/2026/03/ElakhrasMar25-ElasticMiter-Formally-Verified-Dataflow-Circuit-Rewrites-ASPLOS25.pdf
- What it does [abstract only]: standard sequential equivalence does not fit latency-insensitive
  circuits, so the paper builds a generic equivalence framework for latency-insensitive circuits,
  a miter-based approach checked automatically. It uses this to verify a rewriting system that
  simplifies Dynamatic dataflow circuits, and claims the first formal verification of dataflow
  circuit transformations. I did not confirm which model checker it uses.
- Relevance to us: it gives an automatic equivalence notion at Dynamatic's elastic level. It is
  useful as a test oracle and as a definition of "same behaviour" for latency-insensitive
  netlists, but it is not a proof-assistant artefact.

### 1.4 Dynamatic itself
- L. Josipović, R. Ghosal, P. Ienne. "Dynamically Scheduled High-level Synthesis." FPGA '18,
  pp. 127-136. DOI 10.1145/3174243.3174264.
- Tool: https://github.com/EPFL-LAP/dynamatic [repo checked]. License: Apache-2.0 with LLVM
  Exceptions (inherits from LLVM/CIRCT/Polygeist). It is an LLVM/MLIR-based HLS producing
  synchronous dynamically scheduled (elastic) circuits for Xilinx FPGAs.
- Relevance to us: this is the source of the circuits we want to run as bundled-data async. Its
  components are clocked elastic (valid/ready). Our step from synchronous elastic to bundled-data
  async is not covered by any of 1.1-1.3.

### 1.5 Synchronous elastic circuits, SELF (Cortadella, Kishinevsky, Grundmann)
- J. Cortadella, M. Kishinevsky, B. Grundmann. "Synthesis of Synchronous Elastic Architectures."
  DAC 2006. PDF: https://upcommons.upc.edu/bitstream/2117/133566/1/dac06_self-1.pdf
- S. Krstić, J. Cortadella, M. Kishinevsky, J. O'Leary. "Synchronous Elastic Networks." FMCAD 2006.
  Extended report: https://www.cs.upc.edu/~jordicf/Research/gavina/BIB/reports/fmcad06_ext.pdf
- What they prove [abstract only]: DAC'06 specifies the SELF valid/stop protocol formally. FMCAD'06
  defines elastic machines as stream transformers that tolerate any latency variation in their
  environment and proves compositionality, i.e. networks of elastic machines are elastic. These
  are pen-and-paper proofs, not mechanised.
- Relevance to us: this is the protocol-level theory under Dynamatic's handshakes. The FMCAD'06
  compositionality theorem is what we would want to restate in Lean for our cells.

### 1.6 xMAS (Intel) and its formalisation
- F. Verbeek, J. Schmaltz et al. "A formalisation of xMAS." ACL2 Workshop 2013, arXiv 1304.7862.
  https://research.tue.nl/en/publications/a-formalisation-of-xmas/
- [abstract only] xMAS is Intel's graphical language for executable micro-architecture models
  (queues, fork, join, merge, switch). The formalisation is in ACL2. Related work on SAT/SMT
  deadlock hunting found that one liveness encoding was unsound. That is a cautionary data point
  for unmechanised deadlock arguments. I did not find and verify the original Chatterjee,
  Kishinevsky, Ogras paper text.
- Relevance to us: its primitives are close to Dynamatic's, and deadlock-freedom is a property we
  also need.

### 1.7 Latency-insensitive design
- L. P. Carloni, K. L. McMillan, A. L. Sangiovanni-Vincentelli. Theory of latency-insensitive
  design (DAC 2000 version found: https://sld.cs.columbia.edu/pubs/carloni_dac00.pdf). These are
  paper proofs.
- S. Dai et al. (NVIDIA). "Verifying High-Level Latency-Insensitive Designs with Formal Model
  Checking." 2021, arXiv 2102.06326. Model checking of deadlock and invalid-input consumption.
- Y. Pan, C. Batten. Stall-invariant / bounded latency equivalence checking, MEMOCODE 2023,
  https://www.csl.cornell.edu/~cbatten/pdfs/pan-stall-invariant-memocode2023.pdf
- I found **no mechanised (Coq, Isabelle or Lean) proof** of Carloni's latency-insensitivity theory.

### 1.8 Kahn process networks in Coq
- C. Paulin-Mohring. "A constructive denotational semantics for Kahn networks in Coq." In Bertot,
  Huet, Lévy, Plotkin (eds.), From Semantics to Computer Science (Kahn Festschrift), CUP 2009.
  Preprint: https://www.lri.fr/~paulin/PUBLIS/paulin07kahn.pdf. HAL: inria-00431806.
- What it proves: a Coq cpo library with computable lubs, a cpo of possibly infinite streams,
  Kahn networks as least fixpoints of stream equations, with Kahn's example and a dynamic
  Sieve of Eratosthenes.
- Relevance to us: it is the standard mechanised Kahn semantics. Our determinacy argument for
  bundled-data pipelines (any handshake interleaving gives the same output streams) could mirror
  it. It is Coq, so the ideas transfer but the code does not.

## 2. Asynchronous circuits in proof assistants (gate/handshake level)

### 2.1 Chau, Hunt, Kaufmann, Roncken, Sutherland: self-timed circuits in ACL2/DE
- C. Chau, W. A. Hunt Jr., M. Kaufmann, M. Roncken, I. Sutherland. "Data-Loop-Free Self-Timed
  Circuit Verification." ASYNC 2018, pp. 51-58.
- Same authors. "A Hierarchical Approach to Self-Timed Circuit Verification." ASYNC 2019.
  DOI 10.1109/ASYNC.2019.00022. https://pdxscholar.library.pdx.edu/compsci_fac/246
- Code: ACL2 community books `books/projects/async`,
  https://github.com/acl2/acl2/tree/master/books/projects/async [repo checked]. BSD-3-Clause,
  (c) 2018 University of Texas, author Cuong Chau. It contains `link-joint.lisp`, `de.lisp`, and
  `fifo/`, `serial-adder/`, `gcd/`, `arbitration/` (arbitrated merge), `branch.lisp`, `merge.lisp`.
- What it proves: it uses the Roncken-Sutherland link-joint model. Links are state-holding channels
  with a full/empty bit plus data, and joints are the actions that fire when their input links
  are full and output links are empty. Self-timed circuits are expressed in Hunt's DE HDL with
  nondeterministic "go" signals standing for arbitrary delays. It proves the functional
  correctness of FIFOs, a 32-bit serial adder (feedback loop), iterative GCD and arbitrated
  merges for all interleavings, using hierarchical (port-level) reasoning to avoid interleaving
  explosion. Each module is verified with a generator, a multi-step state lemma, a single-step
  update and an input/output sequence relation.
- Relevance to us: **this is the closest prior art for our cell-level proofs.** It is bundled-data
  style (link full/empty plus data), handles arbitration, and is hierarchical. It abstracts delays
  as nondeterministic go-signals, i.e. the bundling constraint is assumed and not derived from
  numeric delays, and it has no LUT/FPGA model. Its link-joint abstraction is a good candidate
  for the intermediate layer between our LUT/timing model and Graphiti's token `Module`s.

### 2.2 Paykin, Huffman, Zimmerman, Beerel: flow equivalence of desynchronisation in Coq
- J. Paykin, B. Huffman, D. M. Zimmerman, P. A. Beerel. "Formal Verification of Flow Equivalence
  in Desynchronized Designs." ASYNC 2020, pp. 54-62. arXiv 2004.10655.
- What it proves: a Coq mechanisation of flow equivalence, meaning an async (desynchronised)
  latch-based circuit produces the same per-latch value sequences as its synchronous original.
  It found a **counterexample to the hand proof** of Cortadella et al. for one handshake protocol
  and proved that two less-concurrent protocols preserve flow equivalence. I did not find a
  public code repository.
- Relevance to us: very high. Dynamatic-to-bundled-data is a desynchronisation-like step, and
  this is a mechanised criterion for it. It is also concrete evidence that published async
  handshake proofs can be wrong, which justifies mechanising ours.

### 2.3 Verbeek and Schmaltz: Click building blocks in ACL2
- F. Verbeek, J. Schmaltz. "Verification of Building Blocks for Asynchronous Circuits."
  ACL2 Workshop 2013, EPTCS 114, pp. 70-84. DOI 10.4204/EPTCS.114.6. arXiv 1304.7859.
- What it proves: ACL2 conditions under which Click-style delay-insensitive primitives (storage,
  fork, join, distributor) are deadlock-free, a proved-correct executable checker, and the
  generation of SAT/SMT deadlock queries for composed circuits. A companion paper is
  "Formal Deadlock Verification for Click Circuits," ASYNC 2013.
- Relevance to us: Click controllers are close to what LUT-built bundled-data controllers look
  like. Their deadlock conditions could become named hypotheses or lemmas for us.

## 3. Synchronous gate/RTL-level hardware in proof assistants

### 3.1 Lööw and Myreen: Verilog semantics, Lutsig and Silver (HOL4)
- A. Lööw, M. O. Myreen. "A Proof-Producing Translator for Verilog Development in HOL."
  FormaliSE 2019. https://research.chalmers.se/publication/512446
- A. Lööw. "Lutsig: A Verified Verilog Compiler for Verified Circuit Development." CPP 2021.
  DOI 10.1145/3437992.3439916.
- A. Lööw, R. Kumar, Y. K. Tan, M. O. Myreen, M. Norrish, O. Abrahamsson, A. Fox. "Verified
  Compilation on a Verified Processor." PLDI 2019, pp. 1041-1053 (the Silver/ag32 processor
  running CakeML).
- A. Lööw. PhD thesis "Building Verified Hardware and Verified Stacks in HOL," Chalmers 2021.
  https://research.chalmers.se/publication/525394
- Code: https://github.com/CakeML/hardware [repo checked]. BSD-3-Clause, HOL4.
  `compiler/RTLScript.sml` defines netlist cells including `CellLUT` (output high iff the input
  vector is in a truth-table list) and `Carry4`, documented in the source as a "model of CARRY4
  (carry chain primitive) in 7 Series FPGAs" (MUXCY/XORCY chain). `netlist_step` folds the
  combinational cells **in list order** (there is no timing and no topological-order check in the
  step itself), then updates registers. It uses one global clock with no clock domains or
  delays. The README says the latest commit does not build Silver and recommends an older commit.
- What it proves: a formal Verilog-subset semantics, translation correctness HOL to Verilog, and
  Lutsig's correctness from Verilog to a technology-mapped LUT/CARRY4/FF netlist for a class of
  FPGAs. It also gives an end-to-end processor used under CakeML.
- Relevance to us: **the only verified toolchain I found that models 7-series LUT and CARRY4
  primitives**, so it is a direct template for our LUT cell model (a truth table as a list of
  true minterms, which is a 64-bit INIT in our case). It is purely synchronous and zero-delay,
  so the async/timing layer is entirely our addition.

### 3.2 Hunt: FM9001, DUAL-EVAL and DE (Nqthm/ACL2)
- W. A. Hunt Jr., B. C. Brock. "A Formal HDL and Its Use in the FM9001 Verification." In
  C. A. R. Hoare, M. J. C. Gordon (eds.), Mechanized Reasoning and Hardware Design, Prentice Hall
  1992, pp. 35-47 (also CLI Tech. Report 79). Proof files: https://www.cs.utexas.edu/~boyer/ftp/fm9001
- W. A. Hunt Jr., E. Reeber. "Formalization of the DE2 Language." CHARME 2005.
  https://www.cs.utexas.edu/~hunt/research/de-hdl/charme-2005.pdf
- What it proves: the FM9001 gate-level netlist in DUAL-EVAL (Nqthm) is proved to implement its ISA
  spec. It was fabricated, and Hunt describes it as the only formally verified microprocessor
  design manufactured as far as he knows. DE/DE2 is the ACL2 successor, a deeply embedded,
  occurrence-oriented HDL for hierarchical Mealy machines with a well-formedness predicate and a
  symbolic simulator.
- Relevance to us: the precedent for gate-level, hierarchical, deep-embedded netlists with a
  well-formedness predicate. DE is the substrate that 2.1 extends to self-timed circuits.

### 3.3 Kami (Coq)
- J. Choi, M. Vijayaraghavan, B. Sherman, A. Chlipala, Arvind. "Kami: A Platform for High-Level
  Parametric Hardware Specification and Its Modular Verification." ICFP 2017 (PACMPL 1, ICFP).
  DOI 10.1145/3110268. https://adam.chlipala.net/papers/KamiICFP17/
- Code: https://github.com/mit-plv/kami [repo checked]. MIT license, Coq 8.12.x in the README.
- What it proves: a Bluespec-style rule-based HDL in Coq with labelled-transition-system modular
  refinement. It verifies an infinite family of cache-coherent multicore RV32I systems and
  extracts toward FPGAs. SiFive used it for the Apex core generators. The precursor is
  Vijayaraghavan, Chlipala, Arvind, Dave, CAV 2015.
- Relevance to us: the LTS-refinement-with-labels style is the right shape for "a cell refines a
  token module". It works at rule (cycle) level with no gates and no time.

### 3.4 Kôika (Coq)
- T. Bourgeat, C. Pit-Claudel, A. Chlipala, Arvind. "The Essence of Bluespec: A Core Language for
  Rule-Based Hardware Design." PLDI 2020. https://adam.chlipala.net/papers/KoikaPLDI20/
- Code: https://github.com/mit-plv/koika [repo checked]. LGPL-2.1, Coq 8.18. Theorems:
  `compiler_correct` (coq/CircuitCorrectness.v) and one-rule-at-a-time equivalence
  (coq/OneRuleAtATime.v).
- What it proves: the deterministic semantics of a Bluespec core and a verified compiler from rules
  to a synchronous circuit IR (the circuits compute the same results as the rule semantics).
- Relevance to us: it shows a verified rules-to-circuits step. Bourgeat is also a Graphiti
  author. It is synchronous only.

### 3.5 Coquet and Fe-Si (Coq)
- T. Braibant. "Coquet: a Coq library for verifying hardware." CPP 2011. arXiv 1108.4253.
- T. Braibant, A. Chlipala. "Formal Verification of Hardware Synthesis." CAV 2013. arXiv 1301.4779.
- [abstract only] Coquet uses dependently typed gate-level circuit combinators in Coq with
  structural and functional proofs. Fe-Si is a verified synthesis from a Bluespec-like language
  to RTL.
- Relevance to us: gate-level deep embeddings with typed wiring are a design reference for a
  typed netlist in Lean.

### 3.6 VAMP / Verisoft (PVS, Isabelle/HOL)
- S. Beyer, C. Jacobi, D. Kröning, D. Leinenbach, W. J. Paul. "Putting it all together - Formal
  verification of the VAMP." STTT 2006.
  https://www-wjp.cs.uni-saarland.de/forschung/projekte/VAMP/?lang=en
- [abstract only] Gate-level verification in PVS of a DLX-variant with Tomasulo scheduler, FPU
  and caches, plus a PVS2HDL translator. A separate Verisoft thesis verified a gate-level system
  (VAMP plus devices) in Isabelle/HOL with the IHaVeIt tool. I did not confirm that thesis's author.
- Relevance to us: scale precedent only. It is synchronous and zero-delay.

### 3.7 Vericert (Coq, HLS)
- Y. Herklotz, J. D. Pollard, N. Ramanathan, J. Wickerson. "Formal Verification of High-Level
  Synthesis." OOPSLA 2021. https://www.cl.cam.ac.uk/~jpw48/papers/vericert_oopsla21.pdf
  Code: https://github.com/ymherklotz/vericert (GPL-3.0, per a search summary; repo not opened).
- What it proves: CompCert-based C-to-Verilog HLS with statically scheduled FSMD output,
  proved in Coq to preserve behaviour.
- Relevance to us: it is the static-HLS baseline Graphiti compares against, from the same lead
  author. It confirms the lineage from Wickerson's group to Herklotz's Graphiti.

### 3.8 VHDL in Isabelle/HOL
- W. Khan, Z. Hou, D. Sanan, J. Nebhen, Y. Liu, A. Tiu. "An Executable Formal Model of the VHDL in
  Isabelle/HOL." arXiv 2202.04192 (2022).
- [abstract only] An executable VHDL operational semantics, exported to OCaml as a simulator and
  validated on LEON3 parts. I did not confirm whether delta cycles or inertial delay are modelled.
- Relevance to us: it is a possible reference for delta-cycle/inertial-delay semantics if we model
  GLS-like event semantics. It is low priority.

## 4. Lean 4 hardware and bit-vector work

### 4.1 bv_decide (Lean core)
- H. Böving, S. Bhat, et al. "Interactive Bitvector Reasoning using Verified Bit-Blasting."
  PACMPL 9 (OOPSLA2), Oct 2025, pp. 3259-3285. DOI 10.1145/3763167.
  https://theory.stanford.edu/~barrett/pubs/BBC+25-abstract.html (I did not confirm the full
  author list beyond Bhat and Böving.)
- What it proves: a verified AIG bit-blaster and LRAT checker in Lean core (`Std.Tactic.BVDecide`,
  since Lean 4.12, originally LeanSAT). CaDiCaL produces the proofs and Lean checks them. It trusts
  the Lean compiler through `Lean.ofReduceBool`.
- Relevance to us: it is the obvious way to discharge LUT truth-table and small combinational
  goals, **but our brief forbids `bv_decide` in `Formal/`** because of `ofReduceBool`. Use
  `decide` on small finite goals, and keep `bv_decide` in `Wip/` as an exploration or
  cross-check tool. The verified AIG data structure in `Std.Sat.AIG` is an alternative LUT-network
  representation we could reuse, since it ships with the toolchain.

### 4.2 Sparkle HDL (Lean 4)
- https://github.com/Verilean/sparkle [repo checked], Apache-2.0, around Lean 4.28 (per README),
  v0.1.0 on Reservoir in Jan 2026. It is a Clash-like HDL in Lean 4 with
  `Signal d α ≈ Nat → α` cycle streams, feedback only through `register`/`loop`, SystemVerilog
  emission, and multi-clock domains in simulation. The README claims many theorems (an RV32IMA
  SoC, AXI4-Lite deadlock freedom, CDC) and checks emitted SV against IR with `bv_decide`. I did
  not inspect the theorem statements.
- Follow-up: "CktFormalizer" (arXiv 2605.07782) and "CircuitProver" (arXiv 2607.27259) use Lean 4
  for LLM-driven circuit formalisation [abstract only]. A Reservoir package `matthunz/circuitlib`
  (0.1.0, Apr 2026, Mathlib) also exists, contents unchecked.
- Relevance to us: there is no async, gate-delay or LUT model. It is useful only as a Lean 4
  stream-semantics style reference.

### 4.3 LeanHDL
- I did not find a project with this name. Do not cite it.

### 4.4 CoqPIE
- I did not find a hardware project with this name. Do not cite it.

## 5. Formal timing analysis

- **Verified STA: no proof-assistant-verified static timing analyser for circuits was found.**
  The nearest verified timing work is software real-time analysis (Prosa/RT-proofs in Coq, POET),
  which does not apply here.
- J. Herbert. HOL proofs of memory devices under gate-delay and signal-timing constraints,
  Cambridge TR (1988), https://www.cl.cam.ac.uk/techreports/UCAM-CL-TR-124.html [abstract only].
  This is the closest mechanised timing-level hardware precedent, an old HOL example.
- Relative timing: K. S. Stevens, R. Ginosar, S. Rotem. "Relative Timing." IEEE TVLSI 2003,
  https://my.ece.utah.edu/~kstevens/docs/tvlsi03.pdf. It expresses timing assumptions as event-order
  constraints, including the bundled-data "data stable before request" constraint. Related:
  S. A. Seshia, R. E. Bryant, K. S. Stevens, "Modeling and Verifying Circuits Using Generalized
  Relative Timing," ASYNC 2005 (timed automata, symbolic delays).
- Timed automata for async circuits: "Verification of Asynchronous Circuits using Timed Automata"
  (OpenKronos, STG specs, bounded gate delays), https://hal.archives-ouvertes.fr/hal-00374812
  [abstract only].
- ARCtimer: H. Park, PhD thesis, Portland State 2015. Generates and verifies timing constraints
  for bounded-bundled-data handshake components.
  https://arc.cecs.pdx.edu/wp-content/uploads/2023/04/Park_ARCtimer_PhDThesis_2015.pdf
- Relevance to us: relative-timing constraints are the right **form for our named timing
  hypotheses** (for example `h_bundle : delay(data path) + setup < delay(req matched delay)`).
  ARCtimer is closest in spirit (bundled data), but it is model checking, not a proof assistant.

## 6. Formal models of FPGA LUTs and bitstreams

- Lutsig (3.1) is the only proof-assistant LUT/CARRY4 model found.
- B. McKendrick, ..., J. Goeders. Netlist-to-bitstream equivalence for 7-series via prjxray/FASM,
  ICFPT 2023. Tool: BFASST, https://github.com/byuccl/bfasst (not opened) [abstract only]. This is
  equivalence checking, not proof. It notes that the prjxray database misses some BELs, so
  fasm2bels netlists are incomplete.
- VTR and nextpnr have no formal verification that I found.
- Relevance to us: BFASST/fasm2bels could give an independent check that the bitstream Vivado
  produced still contains our LUT INITs and routing topology. This would support the hypothesis
  "the placed netlist equals the netlist we proved things about" by test, not by proof.

---

## Reusable code and libraries

| Artefact | Prover / version | License | What to reuse |
|---|---|---|---|
| VCA-EPFL/graphiti | Lean 4 v4.34.1, Mathlib v4.34.1 | Apache-2.0 | `Module` (relational I/O ports), Dynamatic component library, DOT parser; the refinement target for our cells. Copy or adapt; do not depend (toolchain/Mathlib mismatch). |
| plum-umd/wavelet | Lean 4 v4.24.0 | none shown, ask before reuse | dataflow semantics with determinacy/forward simulation |
| acl2 books/projects/async | ACL2 | BSD-3 | link-joint model, arbitrated merge, FIFO proofs; port ideas, not code |
| CakeML/hardware (Lutsig) | HOL4 | BSD-3 | `CellLUT`/`Carry4` 7-series cell semantics, netlist well-formedness |
| mit-plv/kami | Coq 8.12 | MIT | LTS modular refinement design |
| mit-plv/koika | Coq 8.18 | LGPL-2.1 | verified rules-to-circuit compiler design |
| Lean core `Std.Tactic.BVDecide`, `Std.Sat.AIG` | ships with Lean | Apache-2.0 | AIG data structure; `bv_decide` only in Wip (it uses ofReduceBool) |
| Verilean/sparkle | Lean 4 (~4.28) | Apache-2.0 | stream-signal style, reference only |
| EPFL-LAP/dynamatic | C++/MLIR | Apache-2.0 w/ LLVM exc. | circuit source, DOT export compatible with Graphiti |
| Paulin-Mohring Kahn library | Coq | not checked | stream cpo design |

## Gaps (what nobody has done, as far as I found)

1. **No mechanised link from a handshake/gate-level implementation up to a token-level dataflow
   semantics.** Graphiti, Wavelet and ElasticMiter all start at tokens. ACL2 async (2.1) has
   handshake-level cells but no connection to Dynamatic/elastic graphs. A Lean theorem "a
   bundled-data LUT cell refines the Graphiti component under named timing hypotheses" would
   be new.
2. **No proof-assistant-verified static timing analysis**, and no mechanised derivation of
   bundling constraints from numeric delays. Prior async proofs (ACL2, Coq flow equivalence)
   abstract delays as arbitrary interleavings plus assumed orderings. Stating timing hypotheses
   as explicit relative-timing inequalities, testable by GLS or on the board, is the open niche.
3. **No formal model of 7-series LUTs used asynchronously.** Lutsig models LUT6 and CARRY4
   functionally under a zero-delay, single-clock semantics. Glitch and hazard behaviour of a LUT
   during input transitions is modelled nowhere. This needs a named hypothesis (for example
   "the LUT output is hazard-free for single-input-change when the function is monotone or has
   a consensus cover"), and it is testable only on silicon or with GLS.
4. **No mechanised arbiter or metastability model** beyond functional arbitrated merge in ACL2,
   which treats arbitration as nondeterministic choice. MUTEX resolution time stays a hypothesis.
5. **No mechanisation of latency-insensitive theory** (Carloni, or Krstić et al. elastic
   compositionality) in any prover. This is a candidate Lean contribution, and Graphiti's
   `Module` could serve as the base.
6. **No verified FPGA place-and-route or bitstream generation.** Placed-design fidelity must
   remain a named hypothesis, at best cross-checked with prjxray/BFASST.
7. Unverified items (not found, do not cite): "LeanHDL", "CoqPIE", the HVC 2017 Chau et al. paper
   title, the Graphiti refinement definition's exact form (not opened), and ElasticMiter's
   backend model checker.
