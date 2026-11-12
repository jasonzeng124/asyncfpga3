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
