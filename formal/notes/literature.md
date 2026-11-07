# Literature (track 13)

Merged from notes/A-lit-1.md (async/self-timed/metastability verification) and notes/A-lit-2.md (proof-assistant hardware and dataflow work). The two source files are kept; this file is their concatenation.

# A-lit-1: literature survey, track 13, part 1

Probe: what has been formally proved about self-timed, bundled-data and metastable circuits, and with which tools.
The point is to place this project (C-elements, latches and an arbiter built from LUTs on a 7-series FPGA, with Lean 4 proofs) against that work.
No Lean was written for this probe.

How the citations were checked: every entry below was confirmed to exist by a web search on 2026-10-27, through a publisher page, DBLP, a university repository, arXiv, or the author's own page.
WebFetch could not resolve arxiv.org, ar5iv, cs.ubc.ca or vde-verlag.de from this container.
So the summaries rest on abstracts, publisher listings and secondary citations, not on full texts, unless marked otherwise.
Each entry is tagged with how much of it was checked:
- **[abs]**: summary taken from the abstract or publisher listing.
- **[sec]**: summary taken from secondary sources only.

Relevance lines refer to this project's setup:
- LUT6 cells with combinational feedback.
- Bundled-data control.
- A LUT-built mutex/arbiter (`cells/rtl/bd_arb.v`).
- Proofs in Lean 4 under named hypotheses.

---

## 1. Trace theory, delay-insensitive (DI) and speed-independent (SI) verification

**1.1 Dill, trace theory.** D. L. Dill, *Trace Theory for Automatic Hierarchical Verification of Speed-Independent Circuits*. ACM Distinguished Dissertation, MIT Press, 1989 (ISBN 9780262041010).
URL: https://blackwells.co.uk/bookshop/product/9780262041010 (catalogue entry).
[abs]
- Defines trace structures in two forms. Prefix-closed traces cover safety. Complete traces add liveness and fairness.
- Defines conformance between an implementation and its specification. Conformance is hierarchical, so components can be swapped for their specifications.
- Gives an automatic checker for conformance.

Relevance: conformance with a "choke"/failure set is the right correctness notion for a C-element or latch inside a larger handshake circuit. A Lean model could reproduce it over finite traces.

**1.2 Ebergen, DI design.** J. C. Ebergen, "A formal approach to designing delay-insensitive circuits," *Distributed Computing* 5(3):107-119, 1991. DOI 10.1007/BF02252954.
URL: https://link.springer.com/journal/446/5/3/page/1
[sec] (abstract not retrieved)
- Designs DI circuits as compositions of basic components specified in trace theory. This continues his CWI report CS-R8622 (1986) and his 1987 thesis, *Translating Programs into Delay-Insensitive Circuits*.

Relevance: the specification style for the basic DI components (C-element, toggle, merge) is a ready-made source of Lean specifications for our cells.

**1.3 Brzozowski and Seger, *Asynchronous Circuits*.** J. A. Brzozowski, C.-J. H. Seger, *Asynchronous Circuits*, Springer Monographs in Computer Science, 1995.
URL: https://link.springer.com/978-1-4612-8698-1
[abs]
- A full theory covering modelling, gate and wire delay models, and hazards.
- Covers ternary simulation, which goes back to Eichelberger, IBM J. Res. Dev. 9, 1965.
- Contains the Brzozowski–Seger result that ternary simulation is equivalent to GMW (general multiple-winner) analysis when started from a stable state, published in IEEE Trans. Comp. C-36, 1987.
- The generalized version for arbitrary start states is UBC TR-94-02: https://www.cs.ubc.ca/tr/1994/tr-94-02

Relevance: ternary (0/X/1) simulation with GMW soundness is the standard bridge from a race/delay model to a decidable check. It is directly reusable as a Lean decision procedure for LUT feedback cells.

**1.4 Mendler, Shiple, Berry, constructive circuits.** M. Mendler, T. R. Shiple, G. Berry, "Constructive Boolean circuits and the exactness of timed ternary simulation," *Formal Methods in System Design* 40(3):283-329, 2012. DOI 10.1007/s10703-012-0144-6.
URL: https://www.doi.org/10.1007/S10703-012-0144-6
[abs]
- Defines constructive circuits: circuits that settle to a unique value in bounded time under the up-bounded non-inertial (UN) delay model.
- Proves that ternary simulation decides this class exactly.
- Shows ternary simulation is not exact for the up-bounded inertial (UI) model.
- Introduces UN-Logic, with a symbolic calculus that is sound and complete for the UN model.

Relevance: this is the most relevant theory paper for us. It says exactly which delay model makes Kleene/ternary evaluation exact. Our LUT cells need the same model choice to be stated as an explicit hypothesis.

## 2. Petri nets and STGs: Petrify and Workcraft

**2.1 Petrify.** J. Cortadella, M. Kishinevsky, A. Kondratyev, L. Lavagno, A. Yakovlev, "Petrify: a tool for manipulating concurrent specifications and synthesis of asynchronous controllers," *IEICE Trans. Inf. & Syst.* E80-D(3):315-325, 1997.
URL: https://upcommons.upc.edu/entities/publication/dea27e3b-48c9-4b7c-9f24-39a91de76582
[abs]
- Synthesises speed-independent, hazard-free netlists from signal transition graphs (STGs).
- Solves complete state coding (CSC), minimises the logic, and maps it to a gate library.
- Uses BDD (binary decision diagram) state-space methods.

Relevance: Petrify can produce reference SI implementations of our controllers. However, its "complex gate is atomic" assumption is exactly what a LUT does *not* guarantee for multi-input changes.

**2.2 Workcraft, MPSat and Punf.** I. Poliakov, V. Khomenko, A. Yakovlev, "Workcraft – A Framework for Interpreted Graph Models," *Applications and Theory of Petri Nets* (PETRI NETS 2009), LNCS, Springer 2009. Also I. Poliakov, *Interpreted Graph Models*, PhD thesis, Newcastle 2011.
URLs: https://www.springerprofessional.de/workcraft-a-framework-for-interpreted-graph-models/3119042 and https://dspace.ncl.ac.uk/jspui/handle/10443/1183 and https://workcraft.org/overview/backend_tools
[abs]
- Model-checks STGs and gate netlists by Petri-net unfolding with the Punf and MPSat tools.
- Checks deadlock, consistency, output persistency (hazard freedom), CSC and conformation.
- Checks a netlist for speed-independence by composing it with an STG model of its environment.

Relevance: this is the most practical way to cross-check our controllers' SI and hazard properties against Lean. Kushnerov et al. (5.3) already used it for FPGA-MUX C-elements.

## 3. Timed models: relative timing, timed automata, bundled data

**3.1 Stevens, Ginosar, Rotem, relative timing.** K. S. Stevens, R. Ginosar, S. Rotem, "Relative timing," *IEEE Trans. VLSI Systems* 11(1):129-140, Feb 2003. The earlier version appeared at ASYNC 1999, pp. 208-218.
URL: https://my.ece.utah.edu/~kstevens/docs/tvlsi03.pdf
[abs]
- Makes timing assumptions explicit as orderings between pairs of events ("a before b").
- Uses those orderings to synthesise and verify burst-mode and pulse-mode circuits.
- Reports up to 3x gains in area, power and performance.

Relevance: a bundled-data delay-matching assumption *is* a relative-timing (RT) constraint. Writing each assumption as a named Lean hypothesis "path p settles before path q" is RT in theorem-prover form.

**3.2 Seshia, Bryant, Stevens, generalized relative timing.** S. A. Seshia, R. E. Bryant, K. S. Stevens, "Modeling and verifying circuits using generalized relative timing," ASYNC 2005, pp. 98-108.
URL: https://my.ece.utah.edu/~kstevens/docs/async05.pdf
[abs]
- Generalizes RT to metric constraints on the intervals between events.
- Encodes the circuit as timed automata.
- Verifies with fully symbolic timed-automata algorithms, checking temporal-logic properties and conformance to untimed specifications.

Relevance: our bundled-delay assumptions have metric form (d_data + margin < d_req), which is exactly what generalized relative timing expresses.

**3.3 Maler and Pnueli, timed automata.** O. Maler, A. Pnueli, "Timing analysis of asynchronous circuits using timed automata," CHARME'95, LNCS 987, pp. 189-205, Springer 1995.
URL: https://www-verimag.imag.fr/PEOPLE/Oded.Maler/cabst.html (author abstract list)
[abs]
- Models gates with bounded delays [l,u] as timed automata, so that circuits become verifiable objects.
- The follow-up work by Bozga, Hou, Maler and Yovine uses OpenKronos to verify STG-specified circuits with bounded gate delays: https://hal.archives-ouvertes.fr/hal-00374812

Relevance: bounded-delay gate semantics ([l,u] per LUT and route) is the natural timed semantics for our Lean model. Maler and Pnueli show how to make it finite-state.

**3.4 Park, ARCtimer.** H. Park, *ARCtimer* (formal modelling, generation, verification and enforcement of timing constraints for self-timed handshake components), PhD thesis, Portland State University, 2015.
URLs: https://pdxscholar.library.pdx.edu/open_access_etds/2639 and https://arc.cecs.pdx.edu/wp-content/uploads/2023/04/Park_ARCtimer_PhDThesis_2015.pdf
[abs]
- Generates and verifies relative-timing constraints for individual components that use bounded-bundled-data handshakes.
- Turns those constraints into place-and-route timing constraints.
- I found no joint Park–Stevens publication; the "Park, Stevens" pairing in the brief may conflate two separate lines of work.

Relevance: this is the closest prior art to the flow of deriving bundled-data cell timing assumptions and enforcing them in layout. It was done with model checking, not proof.

**3.5 Paykin et al., Coq proof of flow equivalence.** J. Paykin, B. Huffman, D. M. Zimmerman, P. A. Beerel, "Formal verification of flow equivalence in desynchronized designs," ASYNC 2020.
URL: https://arxiv.org/abs/2004.10655
[abs]
- Mechanizes in **Coq** the flow-equivalence proofs for desynchronized (bundled-data) designs.
- Finds that one handshake protocol from the earlier hand proof by Cortadella et al. breaks flow equivalence.

Relevance: this is the closest precedent for proving bundled-data correctness in a dependently typed prover. Matched-delay inequalities are abstracted away there; we would make them hypotheses.

**3.6 Peng and Greenstreet, timed circuits in ACL2.** Y. Peng, M. R. Greenstreet, "Verifying timed, asynchronous circuits using ACL2," ASYNC 2019, pp. 96-104.
URL: https://www.cs.ubc.ca/~yanpeng/talks/async19.pdf (slides)
[sec] (from the slides and DBLP)
- Verifies timed handshake pipelines (asP* pipelines) in ACL2, with SMT discharge through the Smtlink interface.

Relevance: this is a theorem-prover proof of *timed* self-timed pipelines. It is the nearest analogue to a Lean proof with real-valued delay hypotheses.

## 4. Theorem-prover work on self-timed circuits (ACL2 and Coq; none in Lean)

**4.1 Verbeek and Schmaltz, click deadlock.** F. Verbeek, S. J. C. Joosten, J. Schmaltz, "Formal deadlock verification for click circuits," ASYNC 2013, pp. 183-190.
URL: https://dblp.org/pid/33/2094
[sec] (DBLP listing; abstract not retrieved)
- Deadlock verification of click-element circuits. Click is the bundled-data, flip-flop-based handshake style of Peeters, te Beest, de Wit and Mallon: "Click elements: an implementation style for data-driven compilation," ASYNC 2010, pp. 3-14.

Relevance: click is the bundled-data template closest to ours, and this is the precedent for deadlock analysis of it.

**4.2 Verbeek and Schmaltz, ACL2 building blocks.** F. Verbeek, J. Schmaltz, "Verification of building blocks for asynchronous circuits," ACL2 Workshop 2013, EPTCS 114:70-84. DOI 10.4204/EPTCS.114.6.
URL: https://arxiv.org/abs/1304.7859
[abs]
- In ACL2, proves necessary and sufficient deadlock conditions for a library of DI primitives from the Click library.
- Generates SAT/SMT instances from those conditions, and proves the checker correct.
- The authors call the proofs "large and cumbersome".

Relevance: verified primitive lemmas plus a verified checker is a good architecture for our Lean cell library.

**4.3 Verbeek and Schmaltz, xMAS deadlock.** F. Verbeek, J. Schmaltz, "Hunting deadlocks efficiently in microarchitectural models of communication fabrics," FMCAD 2011.
URL: https://www.cs.utexas.edu/~hunt/FMCAD/fmcad11/papers/34.pdf
[abs]
- Detects deadlock in xMAS fabric models through labelled waiting graphs.
- A later TU/e paper reports that the xMAS+FSM extension was unsound: https://fsa.win.tue.nl/?p=514

Relevance: this matters only at system level; it can be skipped for cell-level work.

**4.4 Chau et al., data-loop-free circuits.** C. Chau, W. A. Hunt Jr., M. Kaufmann, M. Roncken, I. Sutherland, "Data-loop-free self-timed circuit verification," ASYNC 2018.
URL: https://dblp.org/pid/63/5796
[abs]

**4.5 Chau et al., hierarchical verification.** C. Chau, W. A. Hunt Jr., M. Kaufmann, M. Roncken, I. Sutherland, "A hierarchical approach to self-timed circuit verification," ASYNC 2019. DOI 10.1109/ASYNC.2019.00022.
URL: https://pdxscholar.library.pdx.edu/compsci_fac/246
[abs]
- Both papers prove functional correctness in ACL2 over the link-joint model of Roncken and Sutherland. That model is independent of the handshake protocol: https://arc.cecs.pdx.edu/wp-content/uploads/2023/04/RonckenSutherland_ThinkST_Asilomar_2017.pdf
- The 2019 paper extends the method to parameterized circuits with loops and non-deterministic (arbitrated) outputs. Its examples are GCD and arbitrated merge.

Relevance: this is the strongest prior mechanized work on self-timed systems, and it includes arbiters as nondeterministic choice. Their abstraction level sits above gates: no timing, no LUT and no metastability.

**4.6 Manohar and Moses, eventual C-element theorem.** R. Manohar, Y. Moses, "The eventual C-element theorem for delay-insensitive asynchronous circuits," ASYNC 2017.
URL: https://csl.yale.edu/~rajit/abstracts/eventualc.html
[abs] (title and author page; no mechanization was mentioned)
- Strengthens Martin's (1990) limitation result for purely DI circuits: C-elements are unavoidable.

Relevance: this justifies why the project needs a C-element primitive at all. It could be a nice small Lean formalization target.

## 5. FPGA-specific asynchronous work and LUT hazards

**5.1 Pfeifer and Vierhaus, C-elements in FPGAs.** P. Pfeifer, H. T. Vierhaus, "On implementation and usage of Muller C-element in FPGA-based dependable systems," Int. Conf. on Applied Electronics 2017, Pilsen, pp. 163-166.
URL: https://otik.uk.zcu.cz/handle/11025/35432 (open PDF)
[abs]
- Surveys LUT-based C-element implementations and proposes a new scheme.
- Discusses how the choice of LUT input pin affects the circuit.
- Measures the result on Xilinx Artix (7-series).

Relevance: this is direct empirical prior art on our exact device family. LUT pin selection matters, which supports making the pin assignment part of the cell model.

**5.2 Deeg, Eiermann, Sattler, function-stable C-element.** F. Deeg, F. Eiermann, S. M. Sattler, "Verification of function stable Muller C-element in FPGA," AmE 2023 (14th GMM Symposium Automotive meets Electronics), GMM-Fachberichte 106, pp. 62-67, VDE Verlag.
URLs: https://www.cris.fau.de/publications/332537351/ and the PDF at https://www.lzs.eei.fau.de/jdownloads/Publikationen/2019-2020/AME2023.pdf
[abs]
- States the correctness condition for a LUT C-element with output-to-input feedback: the feedback loop must be faster than the forward path.
- Measures the low-level delays by making the LUT oscillate through its feedback loop.
- Then verifies the condition by a test on the board.

Relevance: this is very close to our feedback-LUT hypothesis. It gives a board test we can cite for "feedback delay < forward delay", which is exactly the kind of named Lean hypothesis plus board experiment that the brief asks for.

**5.3 Kushnerov, Medina, Yakovlev, MUX-based C-element.** A. Kushnerov, M. Medina, A. Yakovlev, "Towards hazard-free multiplexer based implementation of self-timed circuits," ASYNC 2021, pp. 17-24. DOI 10.1109/ASYNC48570.2021.00011.
URL: https://eprints.ncl.ac.uk/276950
[abs]
- LUTs are trees of 2:1 MUXes, and MUXes can produce logic hazards.
- *Assuming* the 2:1 MUXes in some commercial FPGAs are hazard-free, the paper builds multi-input C-elements.
- The circuits were verified in Workcraft.

Relevance: this is the published form of the LUT-internal hazard assumption. We should state the same assumption as a named hypothesis, at single-input-change granularity, and not assume it more widely than that.

**5.4 Single-input-change glitch freedom of Xilinx LUTs (community source, not peer-reviewed).** Comp.arch.fpga posts by Xilinx's Peter Alfke state that a LUT output does not glitch when exactly one input changes between two addresses with equal output. They also say this guarantee is not in the data sheets. Example: https://www.fpgarelated.com/showthread/comp.arch.fpga/32950-1.php
Intel's Quartus rule LNT-30025 warns about multi-input LUTs that drive asynchronous pins: https://www.intel.com/content/www/us/en/programmable/quartushelp/22.1/da_rules/lnt_30025.htm
[sec]

Relevance: the "single-input-change (SIC) glitch-free LUT" hypothesis is folklore, not a vendor specification. It must remain a named hypothesis with a gate-level-simulation (GLS) and board test, and multi-input-change cases must be ruled out by the circuit's own timing argument.

**5.5 Older work on hazard-free Muller gates on Xilinx.** A Muller-gate library for Xilinx FPGAs, with place-and-route constraints to avoid hazards, appears at IEEE DELTA 2003 (https://computer.org/csdl/proceedings-article/cw/2003/19220128/12OmNxWcHjq). A Vietnamese JSTD article, "Method for implementing asynchronous circuits on FPGA," covers similar ground (https://vjol.info.vn/index.php/JSTD/article/view/8117).
[sec] Authorship of the 2003 paper could not be confirmed from the snippets. Cite it only after checking.

## 6. Delay models: the involution model and faithful binary circuit models

**6.1 Függer, Nowak, Schmid, unfaithful glitch propagation.** M. Függer, T. Nowak, U. Schmid, "Unfaithful glitch propagation in existing binary circuit models," *IEEE Trans. Computers* 65(3):964-978, 2016.
URL: https://arxiv.org/abs/1311.1423
[abs]
- Proves that no existing continuous-time, binary-valued delay model is faithful. This covers pure delay, inertial delay, and the general class of bounded single-history channels.
- Specifically, in all of them short-pulse filtration (SPF) is solvable in bounded time. That contradicts physics, where SPF is equivalent to the impossibility of a bounded-time synchronizer.
- The method is mathematical proof, with no tool.

Relevance: this is critical. A naive Lean model with inertial or pure delays can "prove" a bounded-time arbiter or pulse filter. Our model must be checked against this trap, or must restrict its claims to properties that are not SPF-like.

**6.2 Függer, Najvirt, Nowak, Schmid, faithful model.** M. Függer, R. Najvirt, T. Nowak, U. Schmid, "A faithful binary circuit model," *IEEE Trans. CAD* 39(10):2784-2797, 2020. DOI 10.1109/TCAD.2019.2937748.
Preprint "Faithful glitch propagation in binary circuit models": https://arxiv.org/abs/1406.2544
Earlier version: "Towards binary circuit models that faithfully capture physical solvability," DATE 2015: https://hal.archives-ouvertes.fr/hal-01107436
[abs]
- Introduces involution channels, where the delay functions satisfy -δ↑(-δ↓(T)) = T.
- Proves that SPF is solvable in this model exactly when it is physically solvable: only in unbounded time.
- Validates the model against SPICE and against measurements on an inverter chain.

Relevance: if we want a continuous-time Lean model that does not prove impossible things, we should model involution channels. They are simple real-valued functions, well within Mathlib.Data.Real.

**6.3 Najvirt et al., experimental validation.** R. Najvirt, M. Függer, T. Nowak, U. Schmid, M. Hofbauer, K. Schweiger, "Experimental validation of a faithful binary circuit model," GLSVLSI 2015. DOI 10.1145/2742060.2742081.
URL: https://hal.archives-ouvertes.fr/hal-01231509
[abs]
- Validates involution channels with SPICE (UMC 90 nm and 65 nm processes) and with a measurement ASIC (UMC 90 nm).

Relevance: this is the template for our own board test, which would measure pulse attenuation through a LUT chain to fit δ↑/δ↓.

**6.4 Öhlinger, Maier, Függer, Schmid, the Involution Tool.** D. Öhlinger, J. Maier, M. Függer, U. Schmid, "The involution tool for accurate digital timing and power analysis," *Integration, the VLSI Journal* 76:87-98, 2021. DOI 10.1016/j.vlsi.2020.09.007. The conference version appeared at PATMOS 2019.
URL: https://repositum.tuwien.at/handle/20.500.12708/15702
[abs]
- A ModelSim-based simulator for involution delays (the Exp, Hill and SumExp channels).
- Beats standard digital timing simulation on inverter and clock trees.
- Is *not* clearly better for multi-input NAND gates: the existing channels model multi-input gates poorly.
- A 2025 extension adds 2-input NOR and NAND gates based on a hybrid model: https://arxiv.org/html/2512.01309v1

Relevance: multi-input gates are the weak point of the involution model, and LUT6 cells are multi-input gates. So a faithful model of a C-element LUT is still open research.

**6.5 Függer et al., adversarial noise.** M. Függer, J. Maier, R. Najvirt, T. Nowak, U. Schmid, "A faithful binary circuit model with adversarial noise," DATE 2018.
URL: https://past.date-conference.com/proceedings-archive/2018/html/0968.html
[abs]
- Adds bounded non-deterministic delay variation to the involution model, and keeps faithfulness.

Relevance: PVT (process, voltage, temperature) variation in our LUTs and routes corresponds to "η-bounded adversarial noise". This is the right way to make delay uncertainty a hypothesis.

## 7. Metastability containment and Kleene logic

**7.1 Friedrichs, Függer, Lenzen, MC circuits.** S. Friedrichs, M. Függer, C. Lenzen, "Metastability-containing circuits," *IEEE Trans. Computers* 67(8):1167-1183, 2018. DOI 10.1109/TC.2018.2808185.
URL: https://arxiv.org/abs/1606.06570
[abs]
- Gives a time- and value-discrete worst-case model of metastability. The value M propagates as Kleene's third value.
- Characterizes the functions that metastability-containing (MC) circuits can compute: the "metastable closure" f_M.
- Shows that clocked circuits can contain metastability by logical masking, instead of resolving it.

Relevance: Kleene 3-valued logic, where M plays the role of X, is directly formalizable in Lean. The order 0,1 < M and the monotonicity proofs are small. The paper gives the semantics for "what our arbiter outputs before resolution".

**7.2 Lenzen and Medina, MC Gray-code 2-sort.** C. Lenzen, M. Medina, "Efficient metastability-containing Gray code 2-sort," ASYNC 2016, pp. 49-56.
URL: https://cris.iucc.ac.il/en/publications/efficient-metastability-containing-gray-code-2-sort/
[abs]
- An MC max/min circuit for B-bit Gray-code inputs that each carry at most one M bit. Size O(B²), depth O(B).

**7.3 Bund, Lenzen, Medina, MC sorting networks.** J. Bund, C. Lenzen, M. Medina, "Near-optimal metastability-containing sorting networks," DATE 2017.
URL: https://past.date-conference.com/proceedings-archive/2017/html/0200.html
Same authors, "Optimal metastability-containing sorting networks," DATE 2018: https://past.date-conference.com/proceedings-archive/2018/html/0454.html (arXiv 1801.07549)
[abs]
- MC 2-sort circuits with asymptotically optimal depth and size, using parallel prefix computation.

Relevance for 7.2 and 7.3: these are hand proofs over the Kleene model. They are good examples of MC correctness proofs that could be mechanized in Lean. They do not concern arbiters.

**7.4 Ikenmeyer et al., hazard-free complexity.** C. Ikenmeyer, B. Komarath, C. Lenzen, V. Lysikov, A. Mokhov, K. Sreenivasaiah, "On the complexity of hazard-free circuits," *J. ACM* 66(4), 2019. Also STOC 2018 and arXiv 1711.01904.
URL: https://livrepository.liverpool.ac.uk/3063591/
[abs]
- Hazard-freeness is defined via Kleene/ternary evaluation.
- Proves exponential lower bounds for some functions, and shows that hazard detection is NP-complete.
- Gives a polynomial construction for circuits that are hazard-free when at most k inputs are unstable.

Relevance: this gives the precise definition of "hazard-free LUT function" that we should use. A LUT truth table is hazard-free iff its ternary extension equals the metastable closure. This is a decidable check per LUT INIT value, possibly by `decide`.

**7.5 MC Turing machines (2026 preprint).** "Metastability-containing Turing machines," arXiv 2604.17285, April 2026 (Bar-Ilan University).
URL: https://arxiv.org/abs/2604.17285
[sec] (authors not confirmed by the sources I saw)
- Shows the metastable closure is non-computable in general, and coNP-complete for polynomial-time functions with arbitrarily many uncertain bits.

Relevance: none beyond background; listed for completeness. Note: arXiv 2606.00942, "Characterizing metastable faults and failures", is about distributed-systems "metastable failures". It is **unrelated**, so do not cite it.

## 8. Arbiter and synchronizer metastability theory

**8.1 Chaney and Molnar.** T. J. Chaney, C. E. Molnar, "Anomalous behavior of synchronizer and arbiter circuits," *IEEE Trans. Computers* C-22(4):421-422, 1973. DOI 10.1109/T-C.1973.223730.
URL: https://ibm1401.computerhistory.org/AnomalousSynchronizer_ChaneyMolnar_IEEE1973.pdf
[abs]
- Oscilloscope observations of metastable and oscillatory flip-flop behaviour under logically undefined inputs.

Relevance: this is the empirical origin of the "no bounded-time arbiter" fact.

**8.2 Marino, general theory.** L. R. Marino, "General theory of metastable operation," *IEEE Trans. Computers* C-30(2):107-115, 1981.
URL: https://link.springer.com/doi/10.1007/BF01660032 (a citing paper; no IEEE page was retrieved)
[sec]
- Shows from a continuous-time, continuous-voltage dynamical model that no digital circuit can reliably avoid, resolve in bounded time, or detect metastability.
- Gives a three-region model with exponential resolution.

Relevance: our Lean arbiter theorem must *not* claim bounded-time mutual exclusion *and* bounded-time decision. Any such theorem must carry an explicit "resolves by time T" hypothesis, or use a probabilistic MTBF statement.

**8.3 Lamport, Buridan's Principle.** L. Lamport, "Buridan's Principle," *Foundations of Physics* 42(8):1056-1066, 2012. Written in 1984.
URL: https://www.microsoft.com/en-us/research/publication/buridans-principle/
[abs]
- A discrete decision based on a continuous input cannot be made in bounded time. This is proved from continuity alone.

Relevance: this is the cleanest *formalizable* impossibility. A continuity argument over ℝ could be done in Lean with Mathlib topology, though not with the currently built modules.

**8.4 Kinniment, the standard book.** D. J. Kinniment, *Synchronization and Arbitration in Digital Systems*, Wiley 2007/2008 (ISBN 9780470510827). Some listings co-credit A. Yakovlev; check the title page.
URL: https://www.ellibs.com/fi/book/9780470517130/synchronization-and-arbitration-in-digital-systems
[abs]
- The standard reference on MTBF models, the resolution time constant τ, and the design of mutual-exclusion (MUTEX) and priority arbiters, including STG-based design.

**8.5 Ginosar, tutorial.** R. Ginosar, "Metastability and synchronizers: a tutorial," *IEEE Design & Test of Computers* 28(5):23-35, 2011.
URL: https://webee.technion.ac.il/~ran/papers/Metastability%20and%20Synchronizers.posted.pdf
[abs and sec]
- Gives the standard formula MTBF = e^{S/τ} / (T_W · F_C · F_D), as quoted in Beer–Ginosar, IEEE TVLSI 23(11), 2015.
- Related measurement papers: Beer and Ginosar, "...devolution of synchronizers," ASYNC 2010, which reports FPGA τ values of about 51-73 ps at 130, 90 and 65 nm (vendor unclear): https://www.ee.technion.ac.il/~ran/papers/BeerDevolutionSynchronizersASYNC2010.pdf
- Xilinx XAPP094 (2005) measured Virtex-II Pro, not 7-series.
- **No published 7-series τ was found.**

Relevance: an MTBF claim for our LUT arbiter needs τ and T_W, which must be measured on our board. That is a named hypothesis, not a theorem.

**8.6 Greenstreet group, reachability for arbiters and C-elements.** C. Yan, M. R. Greenstreet, "Verifying an arbiter circuit," FMCAD 2008.
URLs: https://www.cs.utexas.edu/~hunt/FMCAD/FMCAD08/accepted.html and https://www.cs.ubc.ca/~mrg/research.html
[sec]
- Uses projection-based reachability (the Coho tool) on non-linear ordinary-differential-equation (ODE) transistor models of arbiters.
- Related work applies the same methods to flip-flops, C-elements (2011) and ring oscillators.
- Mitchell and Greenstreet (1996) gave the "cone argument" for start-up. Yan, Greenstreet and Yang published "Verifying global start-up for a Möbius ring-oscillator" in FMSD (2014).

Relevance: this is the only work I found that formally verifies an arbiter *including* its metastable behaviour, at the analog level. Our gate-level Lean model sits above it and must assume what they prove.

## 9. Performance analysis (Burns)

**9.1 Burns, performance analysis.** S. M. Burns, *Performance Analysis and Optimization of Asynchronous Circuits*, PhD thesis, Caltech 1991 (advisor A. J. Martin). DOI 10.7907/kez1-7q52.
URL: https://thesis.library.caltech.edu/2835/
[abs]
- Analytical cycle-time analysis of self-timed circuits via timed event graphs, and transistor sizing.

Relevance: if we ever prove throughput or cycle-time bounds for our pipelines, the max-plus cycle-period formulation is the thing to formalize.

---

## What to borrow

1. **Kleene/ternary semantics as the logical core** (1.3, 1.4, 7.1, 7.4).
   - Model every LUT as its ternary extension (Kleene closure of its INIT table).
   - Prove hazard-freeness of each cell function, under the transitions it is allowed to see, as "ternary extension equals metastable closure on the reachable input cubes". This is decidable per cell.
   - Mendler, Shiple and Berry tell us which delay model makes ternary simulation *exact* (UN, not UI). That model choice must be an explicit hypothesis.
2. **Relative-timing constraints as named Lean hypotheses** (3.1, 3.2, 3.4).
   - Each bundled-data matching assumption becomes a hypothesis "d(path₁) + margin ≤ d(path₂)". Use metric generalized relative timing where needed.
   - ARCtimer shows how the same constraint list can drive place-and-route constraints and timing checks: one source, two consumers.
3. **The feedback-faster-than-forward condition for LUT C-elements** (5.2), plus the single-input-change glitch-free LUT assumption (5.3, 5.4).
   - Both become named hypotheses.
   - Both come with existing board-test recipes: oscillate the feedback loop and measure (Deeg et al.); measure on Artix (Pfeifer and Vierhaus).
4. **The SPF/faithfulness sanity check** (6.1, 6.2).
   - Any Lean delay model must be checked for the unfaithfulness bug.
   - If the model lets one prove that a bounded-time pulse filter or bounded-time arbiter exists, the model is wrong.
   - Either adopt involution channels with η-noise, or restrict theorems to statements that hold under *every* delay inside the bounds (bounded-delay nondeterminism) and never claim bounded-time resolution.
5. **Arbiter theorems in the shape physics allows** (8.2, 8.3, 8.5).
   - Mutual exclusion and no spurious grant can be proved *unconditionally* at gate level, given a mutual-exclusion primitive hypothesis.
   - Liveness and latency can only be proved *conditional on* a resolution-time hypothesis or an MTBF bound with measured τ.
   - Model metastable outputs as Kleene M, which the downstream filter must mask (7.1).
6. **Architecture from the ACL2 work** (4.2, 4.5):
   - verified primitive lemmas,
   - a hierarchical link-joint composition that is independent of the handshake protocol,
   - nondeterministic arbitrated merge as an oracle,
   - optionally a verified checker that emits SAT/SMT instances.
7. **Cross-check with Workcraft/MPSat** (2.2) on the same STGs: an independent tool confirms output persistency and deadlock freedom of our controllers.

## What nobody has done (as far as these searches found)

- **No Lean (or Isabelle) formalization of any asynchronous or self-timed circuit.** Mechanized work exists only in ACL2 (Verbeek/Schmaltz; Chau/Hunt/Kaufmann; Peng/Greenstreet) and Coq (Paykin et al., flow equivalence).
- **No machine-checked proof about LUT-implemented asynchronous primitives on FPGAs.** FPGA C-element work is empirical (Pfeifer and Vierhaus; Deeg et al.) or tool-checked under an *assumed* hazard-free MUX (Kushnerov et al., in Workcraft).
- **No gate-level formal model of a 7-series LUT6 with its MUX-tree hazard behaviour stated as an explicit, testable hypothesis.** No vendor specification exists; the single-input-change guarantee is forum folklore.
- **No mechanized proof that combines bundled-data timing (metric relative timing on real-valued delays) with functional correctness of a self-timed pipeline at gate level.**
  - Paykin et al. abstract timing away.
  - Peng and Greenstreet do timed pipelines in ACL2, but not on FPGA cells.
- **No formal, gate-level proof of a LUT-built arbiter/MUTEX.**
  - Arbiter verification exists only at the analog ODE level (Yan and Greenstreet) or as an abstract nondeterministic choice (Chau et al.).
  - No one connects a Kleene-M metastability model (Friedrichs et al.) to a concrete FPGA arbiter with a stated resolution hypothesis.
- **No mechanization of the involution model or of the SPF impossibility results**, in any prover.
- **No published metastability τ / T_W for 7-series (28 nm) LUT-built latches.** Measuring these on the board would be new data.

---

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
