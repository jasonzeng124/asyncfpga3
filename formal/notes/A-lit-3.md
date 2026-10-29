# A-lit-3: literature survey, track 13, part 3 (targeted follow-ups)

Probe: answer five specific questions the lead raised after A-lit-1 and A-lit-2. Those notes
are not repeated here: if a source is already there, it appears here only when this probe found a new
fact about it. No Lean was written for this probe.

How the citations were checked (2026-10-27):
- Every entry was confirmed to exist by web search, through a publisher page, DBLP, a university
  repository or arXiv listing.
- WebFetch and curl could reach **no** paper host from this container. arxiv.org, ar5iv,
  repositum.tuwien.at, bitsavers.org, berkeley.edu and uni-bamberg.de all failed with DNS errors or a
  proxy 403. So nothing here was read in full text.
- Each entry is tagged with how much was checked:
  - **[abs]**: abstract or publisher listing, seen in search results.
  - **[snip]**: a search-engine snippet from the full text. Treat it as a quotation fragment, not a
    checked statement.
  - **[mem]**: my recollection of the paper, consistent with [abs] and [snip] but not checked
    against the text. **The lead should not cite a [mem] statement as the paper's wording.**

---

## 1. Involution channels: exact faithfulness results and conditions on δ↑/δ↓

**1.1 Függer, Najvirt, Nowak, Schmid, "A faithful binary circuit model."** IEEE TCAD 39(10):2784-2797,
2020. DOI 10.1109/TCAD.2019.2937748. Preprint arXiv 1406.2544.
[abs, mem for the conditions]
- **Model** [mem]:
  - A circuit is zero-time Boolean gates joined by single-input, single-output channels.
  - A channel is described by δ↑ and δ↓, each a function of T. T is the time from the previous
    *output* transition to the current *input* transition, which makes the channel single-history.
  - A transition is cancelled when it would overtake the previous output transition.
- **Conditions on δ↑ and δ↓** [mem]:
  - strictly increasing;
  - concave;
  - finite limits δ↑∞ and δ↓∞;
  - strictly causal: δ(0) > 0;
  - the involution property −δ↑(−δ↓(T)) = T, on the domains (−δ↓∞,∞) and (−δ↑∞,∞).
- **Theorems** [abs]:
  1. No circuit with involution channels solves bounded-time short-pulse filtration (SPF).
  2. A specific circuit solves unbounded SPF. [snip] That circuit is an OR gate fed back through a
     channel, followed by a high-threshold buffer channel.
  - [mem] The impossibility proof is a **continuity argument**: the output trace depends
    continuously on the input pulse length, and the intermediate value theorem then forces a
    short-pulse output. This is the "full trace semantics" gap named in A-delay-involution.
- **What this means for our model:**
  - `InvolutionPair` in `Core/Delay/Involution.lean` already carries every condition the
    faithfulness theorem needs except concavity and continuity.
  - Continuity follows from what we have. A strictly monotone function that maps an interval *onto*
    an interval is continuous, and `down_surj`/`up_surj` give the onto part. So `exists_dmin` (the
    remaining `sorry` in Wip) can come from IVT once continuity is derived. Check Mathlib for
    `StrictMonoOn` plus image-is-interval lemmas in `Mathlib/Topology/Order/MonotoneContinuity.lean`,
    for example `StrictMonoOn.continuousWithinAt_right_of_surjOn`; I have not checked these names
    in our Mathlib.
  - Concavity is only needed for the physical validity of the channels, not for SPF.

**1.2 Függer, Maier, Najvirt, Nowak, Schmid, "A faithful binary circuit model with adversarial noise"
(the η-involution channel).** DATE 2018, pp. 1327-1332. DOI 10.23919/DATE.2018.8342219. Preprint
arXiv 2006.08485. [abs, snip, mem]
- **Model** [mem]: each output transition gets the delay δ(T) + η_n. The adversary chooses
  η_n ∈ [−η⁻, η⁺] independently per transition.
- **Theorems:**
  - [snip] "η-involution channels are faithful with respect to SPF."
  - [snip] Bounded SPF stays impossible, because "the adversary is free to always choose η_n = 0".
    This reduces the noisy case to the plain involution result.
  - [abs] "The amount of allowed non-determinism must be considerably restricted" for the unbounded
    SPF circuit to still work.
  - [mem] The restriction is roughly that η⁺ + η⁻ is small compared with δmin. I could not see the
    exact inequality.
- **What this means for our model:**
  - The original η-IDM allows only a *small additive* band. Our `Corner.LocalScatter κ` band is
    multiplicative, (1±κ)·D, and is about 10-20% of a LUT or route delay. That is outside what DATE'18
    covers.
  - Our impossibility-style claims (there is no bounded-time arbiter) are safe in any case, by the
    same "η = 0" reduction.
  - Our positive claims (a circuit works under κ) need 1.3, not 1.2.

**1.3 Öhlinger and Schmid, "A digital delay model supporting large adversarial delay variations"
(extended η-IDM, η-CIDM).** DDECS 2023, pp. 111-117. DOI 10.1109/DDECS57882.2023.10139680.
arXiv 2301.09588. [abs, snip]
- The allowed variation range depends on T: η ∈ [−η⁻(T), η⁺(T)]. Except at very small T, the range
  can be large enough to cover PVT variation and aging.
- [snip] The faithfulness theorem lists conditions of the form η⁺∞ + η⁻∞ < δ↑∞ − δmin. The snippet is
  truncated, so this is not the complete list.
- The model is combined with the CIDM (1.4) and checked against SPICE under PVT corners and aging.
- **What this means for our model:**
  - This is the published model closest to "shared corner plus local scatter".
  - A large variation is allowed for long gaps between transitions (the normal handshake regime). Only
    a narrow band is allowed for near-cancelling glitches.
  - If we ever connect `Corner` to `Involution`, the honest hypothesis has this shape: κ applies when T
    is far from −δ∞, and a much smaller η applies near cancellation. A flat κ everywhere is not that.

**1.4 Maier, Öhlinger, Schmid, Függer, Nowak, "A composable glitch-aware delay model" (CIDM).**
GLSVLSI '21, pp. 147-154. DOI 10.1145/3453688.3461519. arXiv 2104.10966.
Thesis version with η: D. Öhlinger, "β-CIDM ...", TU Wien 2022,
https://repositum.tuwien.at/handle/20.500.12708/20225 [abs]
- The CIDM drops the requirement that the input and output thresholds of a channel match. Each
  channel is split into a pure-delay part and an involution part, so chained gates with different
  thresholds compose.
- Cancelled pulse trains on interconnect stay visible.
- The authors argue on paper that faithfulness is kept.
- **What this means for our model:** our cells are LUT + route pairs with different, unknown
  internal thresholds. The CIDM split, (pure delay) ∘ (involution), is the right shape:
  `Pure.Chan` followed by an `InvolutionPair`. This is also the missing "transfer lemma" the audit
  asked about: a CIDM channel *is* a pure channel composed with an involution channel, so the relation
  is composition, not refinement.

**1.5 Multi-input gates.** [abs]
- A. Ferdowsi, U. Schmid, J. Salzmann, "An accurate hybrid delay model for multi-input gates,"
  arXiv 2211.10628 (2022).
- A. Ferdowsi et al., "A hybrid delay model for interconnected multi-input gates," arXiv 2403.10540
  (2024).
- A. Ferdowsi, M. Függer, T. Nowak, U. Schmid, M. Drmota, "Faithful dynamic timing analysis of
  digital circuits using continuous thresholded mode-switched ODEs," *Nonlinear Analysis: Hybrid
  Systems* 56:101572, 2025. DOI 10.1016/j.nahs.2024.101572. arXiv 2403.03235.
- The HSCC'23 precursor: "Continuity of thresholded mode-switched ODEs and digital circuit delay
  models," arXiv 2303.14048.
- What they show: for NOR/NAND gates, delay depends on *which* input switched and on the gap between
  input transitions (the Charlie/MIS effect). Single-history channels cannot capture this. The 2025
  paper proves continuity, and hence faithfulness, for a class of hybrid ODE models.
- **What this means for our model:** a LUT6 is a multi-input gate. A per-pin involution channel in
  front of a zero-time LUT is the IDM approximation that these papers show is inaccurate for
  near-simultaneous inputs. That is acceptable for SPF-type *impossibility* statements and for
  well-separated handshake events. It is not acceptable for claims about two LUT inputs switching
  within ~δ of each other, for example in the arbiter.

**1.6 Mechanised formalisations.** None found.
- Searches combining involution, faithful, SPF or glitch with Coq, Isabelle or Lean returned only
  paper proofs. Every faithfulness proof in 1.1-1.5 is "analytic".
- **What this means for our model:** `Core/Delay/Involution.lean` appears to be the first mechanised
  involution-channel theory. Say "as far as we found", since this rests on searches only.

**1.7 Pulse shrinking in FPGA fabric specifically.** No involution or IDM fit to FPGA LUT or routing
measurements was found. The nearest evidence:
- Intel Quartus Prime Standard Edition, *Power Analysis and Optimization* user guide, section "Glitch
  filtering". https://www.intel.com/content/www/us/en/docs/programmable/683506/18-1/glitch-filtering.html
  [abs] "The logic and routing structures of the device form a low-pass filter that filters out
  glitches that are tens to hundreds of picoseconds long, depending on the device family." It also
  says the ModelSim inertial default filters more than transport delay does. This is a vendor
  statement, Intel and not Xilinx, with no model.
- J. Lamoureux, G. Lemieux, S. Wilton, "GlitchLess: dynamic power minimization in FPGAs through edge
  alignment and glitch filtering," IEEE TVLSI 16(11), 2008.
  https://people.ece.ubc.ca/lemieux/publications/lamoureux-tvlsi2008.pdf [abs] Programmable delay
  elements at LUT inputs also act as glitch filters.
- J. Shum, J. Anderson, "Towards PVT-tolerant glitch-free operation in FPGAs," FPGA 2016.
  https://janders.eecg.utoronto.ca/pdfs/fpga_2016.pdf [abs] Pulse filters on logic-element outputs
  with a configurable window.
- "Non-blocking programmable delay line with minimal dead time and tens of picoseconds jitter,"
  arXiv 2105.09183 (2021) [abs]. LUT-chain delay lines show non-negligible pulse-width dispersion, so
  the authors insert pulse-shrinking stages that reset the width to 1 ns. Each LUT differs because of
  manufacturing variation.
- FPGA TDC literature (pulse-shrinking TDCs). For example, a GSI overview quotes about 500 ps minimum
  pulse width for full efficiency on a Lattice ECP3 [abs].
- **What this means for our model:**
  - Fabric pulse shrinking is real and large. Widths up to hundreds of ps, comparable to one LUT plus
    route delay, are attenuated, and LUT chains disperse widths.
  - Nobody has published δ↑/δ↓ for a 7-series LUT or route. Any numeric involution instance we use is
    our own fit (the board test proposed in A-lit-1 §6.3) or a hypothesis, never a cited value.
  - The safe statements are the ones that need no numbers: SPF impossibility, and "a pulse longer
    than W_pass propagates" as a named hypothesis.

---

## 2. Ternary (X) simulation soundness under inertial delays

**2.1 Eichelberger, "Hazard detection in combinational and sequential switching circuits."** *IBM J.
Res. Dev.* 9(2):90-99, 1965. DOI 10.1147/rd.92.0090. [abs, mem]
- Defines procedures A and B, which `Core/Ternary.lean` implements as `iterA` and `iterB`.
- [mem] Claim: if a node is binary in A's result, it has no hazard during the change. If it is
  binary in B's result, the circuit settles to that value. The claim holds for gate delays of
  arbitrary size.
- The argument is informal, with no precise delay model.

**2.2 Brzozowski and Yoeli conjecture; Brzozowski and Seger theorems.**
- J. A. Brzozowski, M. Yoeli, "On a ternary model of gate networks," IEEE Trans. Computers
  C-28(3):178-184, 1979 [mem for the venue]. The conjecture: ternary simulation of N equals binary
  race analysis of Ñ, where Ñ is N with a delay in every wire, in the multiple-winner model.
- J. A. Brzozowski, C.-J. Seger, "A characterization of ternary simulation of gate networks," IEEE
  Trans. Computers C-36(11):1318-1327, 1987. https://ieeexplore.ieee.org/document/5009471/ [abs]
  "proves a somewhat modified version" of that conjecture.
- J. A. Brzozowski, C.-J. Seger, "Correspondence between ternary simulation and binary race analysis
  in gate networks," ICALP 1986, LNCS 226. [abs]
- C.-J. Seger, J. A. Brzozowski, "Generalized ternary simulation of sequential circuits," RAIRO ITA
  28(3-4):159-186, 1994. https://numdam.org/item/ITA_1994__28_3-4_159_0 [abs] Extends the result to
  start states that are not stable. The new algorithm is "equivalent to GMW analysis".
- J. A. Brzozowski, C.-J. Seger, *Asynchronous Circuits*, Springer 1995, chapter 7: the textbook
  statement.

Theorem statements, in the book's form [mem]. Take a network N, a stable state s0 under input a, and
the input changing to b. Let Ñ be N with a delay variable on every wire, and let GMW be the
general-multiple-winner relation, in which any nonempty set of unstable variables may change in one
step.
- **(A-exactness)** For every node j: A(j) = lub{ s(j) : s is reachable from s0 in GMW(Ñ, b) }.
- **(B-exactness)** For every node j: B(j) = lub{ s(j) : s ∈ out(s0) }. Here out(s0) is the set of
  states in the terminal strongly connected components of the GMW(Ñ, b) graph reachable from s0.
- With gate delays only (N rather than Ñ), only the ⊒ direction holds: ternary results over-approximate
  the race analysis, and GMW(N) may be more precise.
- GMW with unbounded gate and wire delays is the unbounded *inertial* delay model of Brzozowski and
  Seger, "Advances in asynchronous circuit theory, Part I: gate and unbounded inertial delay models,"
  *Bull. EATCS* 42, 1990. https://research.tue.nl/en/publications/advances-in-asynchronous-circuit-theory-part-i-gate-and-unbounded/ [abs]

**2.3 Mendler, Shiple, Berry, "Constructive Boolean circuits and the exactness of timed ternary
simulation."** *Formal Methods in System Design* 40(3):283-329, 2012. DOI 10.1007/s10703-012-0144-6.
[abs]
- "The match [between ternary simulation and the up-bounded inertial (UI) model] is not exact"
  [abs]. Stabilisation under UI "cannot in general be decided by ternary simulation".
- Under the up-bounded *non-inertial* (UN) model, timed ternary simulation is exact. It decides the
  constructive circuits, which settle to a unique value in bounded time for every delay assignment.
  The paper also gives UN-Logic, a sound and complete calculus.
- The authors argue that UN is preferable for complexity, compositionality and electrical adequacy,
  and because physics cannot implement non-deterministic choice in bounded time. The last point is
  the same principle as the Függer et al. faithfulness work.

**What this means for our model** (comparison with `Core/Ternary.lean`):
- `soundA`/`noGlitchA` prove the ⊒ (soundness) half of A-exactness. The model is `Causal`, with
  per-input sample times, which contains per-wire delays and so contains GMW(Ñ) (`gmw_causal`).
  That is the *right* model class for the Brzozowski-Seger theorem, and the sound direction is the
  one we need.
- The converse, "every X in tA is witnessed by some delay assignment", is the exactness direction.
  It is **not** proved, and nothing in the project needs it. The one place it would matter is a claim
  that a hazard is *real*: `bdc2_two_input_hazard` shows an X, not a reachable glitch.
- `settleB` plus `Stale D` is Mendler-Shiple-Berry's *timed* ternary simulation under UN. The bound
  T0 + k·D corresponds to their up-bounded delay. So our settling result is in the class where
  ternary simulation is known to be exact, which supports the design choice.
- Inertial delay: Mendler-Shiple-Berry's negative result is about exactness, not soundness, as
  A-ternary.md already says. One addition: B-exactness in Brzozowski-Seger is about *outcomes*
  (terminal SCCs), not about settling *time*. So there is no published "B settles within k·D under
  bounded inertial delay" theorem for us to cite. Our W4 (inertial ⇒ `Stale`) is open in the
  literature as well, and Mendler-Shiple-Berry argue it is false in general.
- Recommendation: state W4 as a hypothesis, not as an expected lemma.

---

## 3. Corner and on-chip variation: shared corner plus local scatter

**3.1 What Vivado itself assumes (AMD UG906, *Vivado Design Analysis and Closure Techniques*,
section "Max and Min Delay Analysis" and the setup and hold check pages).**
https://docs.amd.com/r/2022.1-English/ug906-vivado-design-analysis/Max-and-Min-Delay-Analysis [abs]
- Four analyses: {Slow, Fast} corner × {max, min} delay.
- For setup, the source clock and data paths use the *slowest* delays of a corner and the
  destination clock uses the *fastest* delays of the **same** corner. Hold is the reverse. "Delays
  from different corners are never mixed on one path."
- **What this means for our model:**
  - This is exactly our SharedCorner + LocalScatter structure, and it is the vendor's own sign-off
    model.
  - The within-corner (MIN::MAX) pair is the vendor's on-chip variation band at that corner. So the
    vendor-implied local scatter for an arc is κ_v = (MAX−MIN)/(MAX+MIN) inside one corner, for
    example `(FAST_MIN::FAST_MAX)`.
  - The lead can compute κ_v per arc from the prjxray SDF and compare it with the κ limits in
    `Corner.lean`: rule A ≤ 1/11, rule E ≤ 0.1988.
  - Caveat: prjxray's triples come from Vivado's timing database, and whether its MIN/MAX inside a
    corner is OCV or something else (rise/fall merge) was not confirmed by any source found.

**3.2 Maragos, Lentaris, Soudris, et al., "Application performance improvement by exploiting process
variability on FPGA devices."** DATE 2017. https://past.date-conference.com/proceedings-archive/2017/html/0294.html [abs]
- **Device: 8 × Zynq XC7Z020, which has the same 7-series fabric and process as our xc7z010.**
- More than 400 ring-oscillator sites per chip.
- **Intra-chip variability 5.2-7.7%; inter-chip up to 17%; device speed difference up to 12.4%.**
- **What this means for our model:**
  - This is the best published within-die number for our fabric.
  - Inter-die and corner variation (≈17%) is 2-3× the intra-die variation (≈5-8%, peak to peak over
    a die). So sharing the corner removes most of the spread.
  - These are averages over RO loops of several LUTs. Single-arc scatter is larger because the
    averaging is lost (see 3.4). A per-arc κ of about 0.1 is plausible. A κ of 0.2 is conservative for
    random scatter but may be needed for systematic gradients across a large ring.

**3.3 Artix-7 ring-oscillator datasets (28 nm, same 7-series fabric).** [abs]
- R. Hesselbarth, F. Wilde, C. Gu, N. Hanley, "Large scale RO PUF analysis over slice type,
  evaluation time and temperature on 28nm Xilinx FPGAs," HOST 2018, pp. 126-133.
  DOI 10.1109/HST.2018.8383900. Dataset: https://aisec.fraunhofer.de/en/FPGA_ro_Freq.html
  - 217 × XC7A35T, 6592 ROs each, 100 measurements.
  - Systematic effects: slice location and type shift frequency by ≈5 MHz; nearby fast-switching
    logic by ≈10 MHz; ROs next to clock routing are ≈20 MHz slower.
  - The absolute RO frequency is not in the snippets I saw.
- C. Gu, W. Liu, Y. Cui, N. Hanley, M. O'Neill, F. Lombardi, "A large-scale comprehensive evaluation
  of single-slice ring oscillator and PicoPUF bit cells on 28-nm Xilinx FPGAs," *J. Cryptographic
  Engineering*, 2020. DOI 10.1007/s13389-020-00244-5. The author list is [mem]; the 217 Artix-7
  devices are [abs].
- **What this means for our model:**
  - The data is public, so the lead can derive an empirical within-die σ/μ for a 7-series LUT loop
    without a board.
  - The systematic placement effects (≈ a few % of frequency) are *spatially correlated*. Our
    LocalScatter treats every arc independently in (1±κ), which over-covers them. That is sound but
    pessimistic.

**3.4 Sedcole and Cheung, "Within-die delay variability in 90nm FPGAs and beyond."** IEEE FPT 2006.
[sec: numbers from P. Cheung's slides,
https://www.panda.ac.uk/workshop/slides/tuesday/Peter%20Cheung.pdf]
- 18 Cyclone II (90 nm) devices.
- **Random 3σ per LUT ≈ ±3.54%; correlated (spatial) per LUT < 3.66%.**
- Older node and another vendor, but it is the classic random-versus-systematic split for FPGA LUTs.
  Random and systematic are about equal in size.
- Related: Tuan et al. (Xilinx), "Analysis of within-die process variation in 65nm FPGAs," ISQED 2011
  [abs]. Same decomposition on Xilinx parts.

**3.5 Statistical STA background.** [abs]
- D. Blaauw, K. Chopra, A. Srivastava, L. Scheffer, "Statistical timing analysis: from basic
  principles to state of the art," IEEE TCAD 27(4):589-607, 2008.
- [mem] The canonical first-order form is d = d0 + Σ a_i·ΔG_i + a_r·ΔR: shared global sources plus
  an independent local random term.
- C. Visweswariah et al., "First-order incremental block-based statistical timing analysis," DAC
  2004 [mem].
- Industrial OCV, AOCV and POCV/LVF are refinements of this form. AOCV derates by path depth because
  random terms average out along a path (√n). POCV/LVF gives each arc its own σ.
- Typical flat OCV derate in methodology guides is 5-8% (for example https://ecrionix.org/sta/day-07-ocv-aocv-pocv/,
  a blog: [abs], not authoritative). No published 28HPL per-arc σ was found. That data is in foundry
  or vendor libraries under NDA.
- **What this means for our model:**
  - `Corner.lean` (affine in c, plus Scat κ) is the first-order SSTA form with a single global source
    and a bounded rather than Gaussian local term, worst case rather than statistical. That is the
    right choice for proofs.
  - An AOCV-style refinement is available if κ = 0.2 is too pessimistic for long matched delays:
    independent per-arc scatter on an n-arc path gives an n-dependent band instead of a flat κ.
    That needs either a probabilistic statement or a "not all arcs at their extreme" hypothesis,
    which is not provable from worst-case bounds. Keep the flat κ.

---

## 4. Verified STA and formal verification of bundled-data, MOUSETRAP and Click pipelines

**4.1 Verified STA in a proof assistant: none found** (searches over Coq, Isabelle, HOL4 and Lean,
with "certified" and "proof-carrying" variants). The nearest items:
- "Formal timing analysis of gate-level digital circuits using model checking," *Microprocessors and
  Microsystems* 2024 (ScienceDirect S0141933124000784) [abs]. Uppaal timed automata for critical path
  and clock period. Model checking, not a proof assistant.
- Proof-carrying hardware (Paderborn SFB 901, B4) [abs] certifies *functional* equivalence of
  bitstreams. Timing is listed as future work.
- Prosa/RT-proofs (Coq) cover software real-time analysis only, as already noted in A-lit-2.
- **What this means for our model:** a Lean-checked longest-path or bundling check over SDF delays
  (C's checker plus `Corner.lean`) would be, as far as found, the first proof-assistant-verified STA
  of any kind. State the claim with that hedge.

**4.2 Formal work on bundled-data, Click and MOUSETRAP since 2020.** Little found. The relevant items:
- R. Manohar, Y. Moses, "Timed signalling processes," 2023 (IEEE; probably ASYNC 2023, not
  confirmed). https://csl.yale.edu/~rajit/abstracts/tsp.html [abs]
  - Gives a knowledge-based theory of when a transition ordering is guaranteed from known delay
    bounds, with no clocks.
  - "Zigzag patterns" are shown to be the basic construct for ordering transitions. The bundling
    constraint is the motivating example.
  - **This is the closest theory paper to our bundling theorems.** A bundling proof is a zigzag:
    data launch, then the req fork, then the arrival comparison.
- Yak: "An asynchronous bundled data pipeline description language," arXiv 2308.04189 (2023) [abs].
  Generates Verilog and timing constraints for bundled-data pipelines, with no proofs.
- Survey of 2-phase and 4-phase bundled-data pipelines (micropipeline, MOUSETRAP, Click) and their
  timing constraints, *Tsinghua Sci. Technol.*, 2021, DOI 10.26599/TST.2021.9010089 [abs]. No
  mechanised proofs.
- Portland State (ARC group), NuSMV timing verification of Click components,
  https://pdxscholar.library.pdx.edu/cgi/viewcontent.cgi?article=1305&context=ece_fac [abs; year not
  confirmed]. Protocol as cooperating finite-state machines, plus timing constraints.
- Already in A-lit-1/2, not repeated: ARCtimer (Park 2015), Chau et al. ACL2 link-joint (2018-2019),
  Paykin et al. Coq desynchronisation (2020), Verbeek-Schmaltz Click in ACL2.
- **What this means for our model:**
  - In 2020-2026 no one has published a mechanised proof that a bundled-data or Click or MOUSETRAP
    stage meets its bundling constraint under explicit delay bounds.
  - The ACL2 work proves functional correctness and leaves timing to ARCtimer-style tools.
  - Our `Corner`-based bundling theorems and B's timed pipeline proofs fill that gap. Cite Manohar
    and Moses for the event-ordering principle and Stevens et al. (relative timing) for the form of
    the constraint.

---

## 5. Lean 4 hardware verification since 2024, and formal work on Dynamatic

Graphiti, Wavelet ("Let it Flow"), ElasticMiter, Sparkle and bv_decide are in A-lit-2 §1 and §4. New
items:

**5.1 Rtl2lean.** "Rtl2lean: automated RTL-to-Lean translation with hierarchical theorem generation
and lemma reuse," arXiv 2607.16855 (2026). [abs]
- Translates SystemVerilog into executable Lean 4 models.
- 403 machine-checked theorems on 6 designs, with LLM-assisted lemmas.
- Synchronous RTL only.

**5.2 CircuitProver.** Yang, Fang, Chen, Xie, Zhang, "CircuitProver: agentic Lean 4 theorem proving
with reusable circuit proof library for hardware verification," arXiv 2607.27259 (2026). [abs]
- Chisel to Lean.
- Models are validated by exhaustive small-width co-simulation.
- Clocked designs only.
- It cites CktFormalizer (Xiong et al. 2026), which is in A-lit-2.

**5.3 Veil.** G. Pîrlea, V. Gladshtein, E. Kinsbruner, Q. Zhao, I. Sergey, "Veil: a framework for
automated and interactive verification of transition systems," CAV 2025, Springer LNCS,
DOI 10.1007/978-3-031-98682-6_2. Reservoir: `verse-lab/veil`. [abs]
- Lean 4.
- Transition systems written imperatively. The VC generator to SMT is proved sound; Lean proofs are
  the fallback.
- Veil 2.0 adds a TLC-style explicit-state model checker.
- Distributed protocols, not hardware.
- **What this means for our model:**
  - Our handshake and Muller-ring models are transition systems with invariants (C's `Kahn`/`Muller`
    files).
  - Veil could discharge inductive invariants by SMT, but its trust base includes the SMT solver,
    unless it reconstructs proofs; I did not check which. That conflicts with our no-`ofReduceBool`
    rule.
  - Use: an exploration tool in `Wip/`, not in `Formal/`.

**5.4 Lean-MLIR / SSA.** S. Bhat et al., "Verifying peephole rewriting in SSA compiler IRs," ITP 2024,
LIPIcs 309, paper 9, arXiv 2407.03685. Code: https://github.com/opencompl/lean-mlir [abs]
- Verified rewrites over a Lean SSA semantics: LLVM bit-vectors, structured control flow, FHE.
- **No CIRCT `comb` or `handshake` dialect semantics in Lean was found.**
- K-CIRCT (arXiv 2404.18756, K framework, not Lean) formalises hw, comb, seq and sv.
- **What this means for our model:** there is no Lean semantics of CIRCT's `handshake` dialect, which
  is Dynamatic's IR. A Graphiti `Module` remains the only Lean target for "our cells refine the
  Dynamatic component".

**5.5 Dynamatic formal work, 2025-2026.** [abs]
- Graphiti (ASPLOS'26) and ElasticMiter (ASPLOS'25), as in A-lit-2.
- Graphiti uses a *modified* Dynamatic buffer placement to avoid deadlock. Buffer placement itself is
  not verified.
- Wavelet ("Let it Flow", PLDI'26) leaves its last operator-selection pass unverified and points to
  Graphiti for it.
- "Is it a good idea to build an HLS tool on top of MLIR? Experience from building the Dynamatic HLS
  compiler," arXiv 2603.19856 (2026): an experience report, with no proofs.
- **No proof was found that any Dynamatic *handshake implementation* (valid/ready RTL, elastic buffer,
  or an asynchronous version) refines the token-level component.**
- **What this means for our model:** our gap statement in A-lit-2 still holds as of 2026-10. The
  bridge "LUT/bundled-data cell ⊑ Graphiti `Module`" is unclaimed. Deadlock freedom under buffer
  placement is also unproved upstream, so any whole-circuit liveness claim we make on a Dynamatic
  netlist must carry that as a hypothesis.

**5.6 Lean 4 asynchronous circuit work: none found (2026-10-27; superseded 2026-10-29 by A-lit-4 §2: async-lean (KelvinChung2000, SI/QDI, untimed) and MCL (snisimu, relative timing over integer pure delays) exist).** Searches for Lean 4 with C-element,
delay-insensitive, handshake or asynchronous found only Graphiti and Wavelet (token level) and the
synchronous items above.

---

## Summary for the lead (one line per question)

1. **Involution channels.** The conditions are monotone, concave, finite limits, strictly causal and
   involutive. Faithfulness is SPF impossibility in bounded time and possibility in unbounded time,
   proved by continuity. Our `InvolutionPair` has everything but concavity, and continuity follows
   from monotone + onto.
   - The noisy versions allow only a small band near cancellation (DATE'18), or a T-dependent large
     band (η-CIDM 2023).
   - CIDM = pure ∘ involution, which is the honest link to `Pure.Chan`.
   - No mechanisation exists, and no FPGA δ↑/δ↓ has been published.
2. **Ternary simulation.** Brzozowski-Seger: A and B are *exact* for GMW with wire delays. Our Lean
   proves the sound half, for a model that contains GMW(Ñ). Mendler-Shiple-Berry: exact for timed UN,
   not exact for UI. Keep W4 (inertial ⇒ Stale) as a hypothesis.
3. **Variation.** Vivado itself uses "same corner, fastest vs slowest within it". Zynq-7020: 5.2-7.7%
   intra-die, 17% inter-die (DATE'17). Random and systematic per LUT are each ≈3.5% at 3σ (90 nm).
   A per-arc κ of about 0.1 is plausible and 0.2 is conservative. The 217-device Artix-7 RO dataset is
   public.
4. **Verified STA and bundled-data proofs.** No proof-assistant STA found. No mechanised bundled-data,
   Click or MOUSETRAP timing proof found from 2020-2026. Manohar-Moses 2023 "zigzag" is the theory to
   cite.
5. **Lean 4 hardware.** New since A-lit-2: Rtl2lean, CircuitProver (2026, synchronous, LLM) and Veil
   (CAV'25, transition systems). Still nothing asynchronous in Lean, and no Lean CIRCT-handshake
   semantics. The cell ⊑ Graphiti `Module` bridge is unclaimed.
