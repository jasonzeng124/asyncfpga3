# A-lit-4: literature survey, part 4 (IDM follow-ups, elastic and async proofs, X-sim and MC, LUT pulse rejection, 7-series τ)

STATUS: done (probe Lit4, shard A, 2026-10-29). No Lean was written. Five topics, one section each,
then a summary. Sources already in literature.md or A-lit-1..3 appear only when this probe found a
new fact about them.

How the sources were checked:
- WebFetch could reach **no** paper host. arxiv.org, repositum.tuwien.at, past.date-conference.com,
  schmiste.github.io, eecg.utoronto.ca and aitech.ac.jp all failed DNS in this sandbox. So nothing
  was read in full text. To read the full papers the lead must allow those hosts in the session
  network settings.
- GitHub clones over git did work. Three public repositories were cloned to the scratch directory
  and read: async-lean, mcl-lean-artifact and TC-TERO. They are tagged **[repo checked]**.
- The other tags are the same as in A-lit-3:
  - **[abs]**: abstract or publisher listing.
  - **[snip]**: a search-engine fragment of the full text. Treat it as a quotation fragment.
  - **[mem]**: my recollection. It is consistent with [abs]/[snip] but was not checked. Do not
    cite it as the paper's wording.

---

## 1. The involution delay model (IDM) line: equality rule, storage-loop metastability

### 1.1 Cancellation at equality: equality cancels (resolves the open point of A-inv-trace)

- M. Függer, R. Najvirt, T. Nowak, U. Schmid, "Towards binary circuit models that faithfully capture
  physical solvability," DATE 2015, pp. 1455-1460, IEEE Xplore 7092619. PDF:
  past.date-conference.com/proceedings-archive/2015/pdf/0799.pdf. [snip] "the nth and mth pending
  output transitions cancel if n < m but t_n+δ_n ≥ t_m+δ_m. In this case, we mark both as canceled."
- Függer, Najvirt, Nowak, Schmid, "A faithful binary circuit model," IEEE TCAD 39(10):2784-2797,
  2020, DOI 10.1109/TCAD.2019.2937748 (already cited). [snip] It has a lemma with the equivalent
  conditions "1) the nth and (n+1)th pending output transitions cancel. 2) t_{n+1} ≤ t_n + δ_n −
  δmin. 3) δ_{n+1} ≤ δmin". It also says that "pending transitions can still be canceled by other
  transitions", whereas fixed transitions are guaranteed to occur.
- D. Öhlinger, J. Maier, M. Függer, U. Schmid, Involution Tool, *Integration* 76, 2021 (already
  cited). [snip] "An output transition is only fixed, i.e., moved from Pending to Output, when it
  cannot be canceled later on."

What this means for us:
- `InvolutionTrace.lean` cancels on `o' ≤ o`, so equality cancels. That is the paper's rule (≥ in
  the DATE'15 notation).
- Our boundary results agree with condition 2/3 of the TCAD lemma:
  - `rat_threshold_cancelled`: a pulse of width exactly δ∞↑ − δmin is cancelled.
  - `channel_pulse`: a single pulse is cancelled iff Δ ≤ δ∞↑ − δmin.
- The "What is NOT covered" item in A-inv-trace about strict versus non-strict comparison can be
  closed at [snip] level. Cite the DATE'15 inequality and the TCAD lemma.
- [mem] δ_n is computed from the previous *tentative* output, whether or not it was cancelled.
  Our `tent` follows that reading. The snippets do not settle it. `rat_memory_channel` is the test
  that would tell the two readings apart once the full text is readable.

### 1.2 CIDM: involution then pure delay is an involution channel (known; we re-proved it)

J. Maier, D. Öhlinger, U. Schmid, M. Függer, T. Nowak, "A composable glitch-aware delay model,"
GLSVLSI '21, pp. 147-154, DOI 10.1145/3453688.3461519. arXiv 2104.10966; HAL hal-03451070. (Already
cited.)
- [snip] "every IP channel satisfies the properties of an involution channel". An IP channel is an
  IDM channel followed by a pure-delay shifter.
- [snip] The faithfulness argument: "for every modeling of a circuit with our CIDM channels, there
  is an equivalent modeling with IDM channels".
- [snip] The faithfulness proof "rests on the continuity of IDM channels, which has been proved only
  for involution delay functions".
- No journal version was found.

What this means for us: our `outList_shiftPair` (δ'(T) = D + δ(T+D), δ'min = δmin + D) is the
mechanised form of the CIDM lemma. It is known, so cite CIDM for it. It is not new.

### 1.3 The storage (OR) loop: what is known about metastability under IDM

- **J. Maier, "Gain and pain of a reliable delay model,"** Euromicro DSD 2021, pp. 246-250.
  arXiv 2107.06814; TechRxiv 14872116; repositum 20.500.12708/18634, DOI 10.34726/1681. [abs, snip]
  - It runs IDM (Involution Tool) against SPICE on an OR loop, an SR latch and a ripple-carry adder.
  - [snip] On the OR loop: "Based on the input pulse width Δ^I the signal may oscillate for a
    possibly infinite amount of time before vanishing or setting the loop to HI."
  - [snip] On the SR latch: the IDM "describes the behavior in, and also the resolution out of,
    metastability faithfully". The paper has figures of the latch being "steered back into
    metastability".
- **η-IDM**, Függer, Maier, Najvirt, Nowak, Schmid, DATE 2018, arXiv 2006.08485 (already cited).
  [snip] The SPF proof considers "a pulse of length Δ0 at time 0" at the storage loop, with three
  cases:
  - "If Δ0 is small, then the pulse is filtered by the channel in the feedback loop."
  - "If it is big, the pulse is captured by the storage loop."
  - The third case (in between, where the loop oscillates) was cut off in the snippet.
- **D. Öhlinger, U. Schmid, η-CIDM,** DDECS 2023, arXiv 2301.09588 (already cited). [snip]
  - It classifies the OR-loop output into decreasing and increasing pulse trains.
  - Pulses are "monotonically increasing until the pulse length reaches Δ̄ and the feedback loop
    locks at 1".
  - A decreasing train must map to the zero signal at the high-threshold buffer.
- arXiv 1406.2544 (the TCAD preprint) [snip] has lemmas with a Δ̃ and a count of generated pulses.
  The statements could not be read.

**Comparison with A-inv-loop.md** (our `InvolutionLoop.lean`, 197 decls):

| Our result | Known? |
|---|---|
| Trichotomy: the loop is lost below s*, latches above s*, and oscillates for ever at s* | **Known qualitatively.** DSD'21 description; the DATE'18 three-case SPF proof; η-CIDM monotone trains. The TCAD faithfulness proof needs it in some form. |
| Unbounded resolution: `laps_unbounded_*`, `resolution_unbounded` | **Known.** It is the content of "SPF is not solvable in bounded time" (TCAD, by continuity). It is also stated for the OR loop in DSD'21. |
| Highs grow while latching (`latch_grow`) and shrink while lost (`lost_shrink`) | **Known in substance.** η-CIDM states the monotone increasing and decreasing pulse trains. |
| Closed form s* = δ∞↑ − l, with (h, l) the unique stationary train δ↑(−h) = h+l = δ↓(−l) (`stat_exists`, `stat_unique`, `crit_unique`) | **Not found** in any snippet. It may be the Δ̃ of the TCAD/arXiv lemmas, which could not be read. |
| Expansion of the half-lap maps, |Δout| > |Δin|, from monotonicity alone (`fu_exp`, `F_exp`) | **Not found.** |
| Symmetric channel: 50% duty, 2w* = δ(−w*), s* in (δ∞/2, δ∞ − δmin/2) (`Sym.*`, `exp_crit`) | **Not found.** |
| Asymmetry direction (`asym_iff`) | **Not found.** |
| Rate law (TAU_eff) | **Not found** in any paper. It is also not proved by us. |

How to word the claims:
- "Mechanised, as far as we found, for the first time" is safe for all of `InvolutionLoop.lean`
  and `InvolutionTrace.lean`. Again no mechanisation of any IDM result was found in Lean, Coq or
  Isabelle (same result as A-lit-3 §1.6).
- "New result" is safe only for the closed-form, symmetric and asymmetric rows, and only with
  "not found in the abstracts and fragments we could read". The full TCAD Δ̃ lemma must be read
  before claiming novelty.
- Physical support: DSD'21 (SPICE) shows the oscillating OR loop and the metastable SR latch.
  That is evidence that a pulse train near s* is physical, not an artefact of the model. This
  matters for FID_RESOLVE: its "clean hold" resolver hides that pulse train (A-fid3).

### 1.4 New IDM-line papers since A-lit-3 (multi-input; not about loops)

- A. Ferdowsi, U. Schmid, J. Salzmann (authors inferred from the e-mail header; check them),
  "Drafting and multi-input switching in digital dynamic timing," DATE 2026; extended version
  arXiv 2512.01309. [abs] A closed-form analytic delay model for interconnected NOR gates that
  covers drafting and MIS effects. It is implemented in the Involution Tool.
- The ICCAD 2023 version of the hybrid multi-input model: "Accurate hybrid delay models for
  dynamic timing analysis" (Ferdowsi, Schmid, Salzmann; repositum 20.500.12708/192521). [abs]
- For us, these are the same caveat as A-lit-3 §1.5. LUT6 multi-input behaviour is outside
  single-input IDM. Nothing in this line treats an FPGA LUT.

---

## 2. Formal verification of bundled-data, self-timed and elastic circuits, 2023-2026

### 2.1 async-lean: Lean 4 deadlock and livelock checking of asynchronous designs (new)

github.com/KelvinChung2000/async-lean [repo checked]. Kelvin Chung. Apache-2.0. `lean4:v4.34.1`
with Mathlib. Commits from 2026-10-05 to 2026-10-09; about 27.9k lines.
- **Models.** Petri nets, STGs (CSC, consistency, output persistence, conformance of gates),
  gate-level circuits (`SpeedIndependent`, `QDI` with isochronic forks), and NoC routing
  (wormhole, starvation freedom).
- **Tactics.** Goals close by kernel-checked decision procedures (`async_decide`), with no
  `native_decide`. An `#assert_standard_axioms` guard fails the build on `sorry` or extra axioms.
- **Theorem.** `Circuit.correct_of_qdi`: correctness under wire delays implies correctness without
  them.
- **Limits.** Interleaving semantics. Delays are unbounded, so there is no metric time, no
  bundling constraint and no metastability model.
- **What it means for us:**
  - This is the first Lean 4 *gate-level asynchronous* library found. It refutes A-lit-3 §5.6
    ("Lean 4 asynchronous circuit work: none found").
  - It is untimed (SI/QDI) and token-free. Our timed, bundled-data, LUT-level and involution work
    does not overlap with it.
  - Possible reuse: their SI/QDI checker for the speed-independent parts of our controllers, with
    the same trust base as ours (no `ofReduceBool`).
  - Their toolchain is newer than ours. Check compatibility before importing.

### 2.2 MCL: Modal Circuit Logic in Lean 4 (new)

github.com/snisimu/mcl-lean-artifact [repo checked]. Anonymised artifact. Paper: "Machine-checked
verification of gate-level asynchronous circuits under metric-free relative-timing assumptions:
Modal Circuit Logic in Lean 4", submitted to SASIMI 2027. About 1500 lines, `lean4:v4.33.0`, no
Mathlib. Commits from 2026-09-26 to 2026-10-14.
- It ports a 2016 Agda development (authors not identified).
- **Semantics** (`MCL/Sem.lean`): a pure-delay model over integer time, with a positive integer
  delay per gate-input arc. Relative-timing hypotheses are path inequalities.
- **Results.**
  - Soundness of the inference rules.
  - `hold` for a sum-of-products C-element with feedback.
  - `existsValue_inconsistent`: the old 2016 totality axiom derives False, and the old constraint
    has no solution.
- It includes an LLM coding-agent experiment.
- **What it means for us:**
  - It is the closest published Lean work to ours: gates, delays and relative timing.
  - Its delays are metric-free, pure and integer. There are no bounds, no inertial or involution
    channels and no FPGA cells.
  - Its C-element `hold` theorem is a point of comparison for B's C-element proofs.
  - Its negative result is a warning for every project that assumes totality or existence of a
    value: check hypotheses for satisfiability. Our own rule ("Negative controls must be able to
    fail") is the same discipline.

### 2.3 A mechanized semantics for dataflow circuits (Coq, Dynamatic-validated; missed earlier)

T. Law, D. Demange, S. Blazy, "A mechanized semantics for dataflow circuits," PACMPL 9 (OOPSLA1),
2025, presented at SPLASH 2025. DOI 10.1145/3720432. [abs]
- Components communicate over unbounded FIFOs.
- It gives a graph view and a term calculus, proved semantically equivalent.
- It gives sufficient conditions for determinacy.
- It is validated on Dynamatic circuits.
- **What it means for us:** a third token-level Dynamatic semantics, alongside Graphiti and
  Wavelet. It is in Coq, so it cannot be imported, but its determinacy conditions are a reference
  for B/C's Kahn-style results. Like the others, it has no handshake implementation and no timing.

### 2.4 Nothing new on timed bundled-data proofs

Searches for 2023-2026 mechanised bundled-data, Click or MOUSETRAP timing proofs in Lean, Coq,
Isabelle or ACL2 found only the older items already listed (Paykin et al. 2020; Chau et al.;
ARCtimer). The gap statement of A-lit-3 §4.2 stands. With 2.1 and 2.2 it can now be worded as:
"Lean 4 work on asynchronous gates exists (async-lean: SI/QDI, untimed; MCL: metric-free relative
timing), but none with metric delay bounds, bundling or FPGA cells."

---

## 3. Ternary / X simulation and metastability containment, 2022-2026

- **J. Bund, C. Lenzen, M. Medina, "Small hazard-free transducers,"** IEEE Trans. Computers
  74(5):1549-1564, 2025. Conference version ITCS 2022, LIPIcs, DOI 10.4230/LIPIcs.ITCS.2022.32.
  arXiv 1811.12369. [abs]
  - Finite-state transducers with small state space have hazard-free (Kleene-exact) circuits of
    asymptotically optimal size, via parallel prefix.
  - For us: a positive result on *sequential* hazard freedom. It is the closest theory to
    "a LUT state machine whose ternary extension is exact".
- **Bund, Lenzen, Medina, "Codes for metastability-containing addition,"** arXiv 2602.06467,
  February 2026, accepted to IEEE TC. [abs] Background only.
- **J. Bund, A. Leshem, "Metastability-containing Turing machines,"** arXiv 2604.17285. This
  confirms the authors that A-lit-1 §7.5 could not confirm.
- **L. London Arazi, A. Shpilka, "On the complexity of hazard-free formulas,"** ICALP 2025,
  LIPIcs 334, paper 115. arXiv 2411.09026. [abs]
  - The hazard-free formula size equals the monotone formula size of the "hazard derivative".
  - The multiplexer is exponentially expensive as a hazard-free formula.
  - For us: it confirms that the LUT's internal MUX-tree hazard behaviour cannot be fixed cheaply
    in logic. Hazard freedom of a LUT stays a hardware hypothesis (`H_LUT` SIC), not a property
    of the INIT.
- Hazard-free decision trees, arXiv 2501.00831 (2025) [abs; authors not seen]: size_u(f) ≥
  2·size(f) − 1. Background only.
- J. Bund, M. Függer, C. Lenzen, M. Medina, "Synchronizer-free digital link controller,"
  arXiv 2010.02017 (2020; venue not confirmed) [abs]. An MC design for clock-domain links.
  Relevant if we ever replace a synchroniser by containment.
- S. Thompson, A. Mycroft, "Abstract interpretation of combinational asynchronous circuits,"
  SAS 2004, LNCS 3148 (cl.cam.ac.uk/~am21/papers/sas04.pdf) [abs/mem]. This is older but was
  missed: multi-valued abstract interpretation that finds static and dynamic hazards, with
  inertial-delay elements. It is an alternative abstraction to Eichelberger A/B for glitch
  detection.
- **Mechanised ternary-simulation soundness: none found.** Searches for Eichelberger or
  Brzozowski-Seger soundness in Coq, Isabelle, HOL or Lean found nothing. So `Core/Ternary.lean`
  (`soundA`, `noGlitchA`) remains, as far as found, the only mechanised proof of the sound half.
- No 2022-2026 paper revisits ternary exactness under inertial delay. Mendler-Shiple-Berry (2012)
  is still the last word, so W4 stays a hypothesis (A-lit-3 §2).

---

## 4. LUT pulse rejection and LUT internal skew on 7-series silicon (the transport-vs-inertial question)

**Bottom line: no publication measures the pulse-rejection width, or the internal input-to-input
skew, of a 7-series LUT.** The literature does not decide the hypothesis. What was found is
indirect evidence about LUT *loops* on 7-series silicon. It bears on the loop and echo questions,
not on rejection of sub-delay pulses.

**4.1 N. Fujieda, "On the feasibility of TERO-based true random number generator on Xilinx
FPGAs,"** FPL 2020, pp. 103-108, DOI 10.1109/FPL50879.2020.00027. Code: github.com/nfproc/TC-TERO
[repo checked; BSD; last commit 2024-08-20]. Board: Arty A7-35, **XC7A35T (Artix-7, 28 nm)**.
- **Circuit** (`tero.v`): two LUT2 NANDs cross-coupled through LUT1 buffer chains of 5 and 3
  (RLOC-placed, DONT_TOUCH). On CTR↑ a transition pair circulates. The pulse width drifts each lap
  by the branch asymmetry Δr (design 4:6, Δr = 0.2) plus noise, until the pulse vanishes.
- **Counts.** An 8-bit counter counts the laps. The parameter search targets a mean of about 112
  and σ ≈ 7 (README).
- **Infinite oscillation.** [snip] "too small Δr might result in an infinite oscillation". The
  controller therefore forces a timeout after 2 µs.
- **What it means for us:**
  - On Artix-7, a loop of LUTs and routes circulates a pulse train for hundreds of laps when the
    rise/fall asymmetry is small. Per-lap distortion is small and is set by asymmetry and noise.
  - This supports A-fid3's statement that the GLS echo (E4, transport loop) is physical, not a
    simulation artefact.
  - It also supports the involution-loop picture: near s* a LUT loop circulates a pulse train
    rather than holding a clean value.
  - It does **not** test pulses narrower than one LUT delay. The circulating widths are of the
    order of branch delays (several LUT+route hops). So it neither refutes nor supports an
    inertial LUT with rejection width ≤ δ_LUT.

**4.2 B. Habib, J.-P. Kaps, K. Gaj, "Implementation of efficient SR-latch PUF on FPGA and SoC
devices,"** *Microprocessors and Microsystems*, 2017. ResearchGate 318604144; GMU ARC 2015
precursor. [abs, snip]
- An SR latch of **two LUTs as NANDs**, tested on 25 Spartan-6 and **10 Zynq XC7Z010** (7-series
  fabric).
- "During the metastable state, the SR-latch oscillates." An 8-bit counter counts the
  oscillations, and the count is the entropy source.
- **What it means for us:** this is direct 7-series silicon evidence that a two-LUT state loop
  driven into metastability resolves *through a digital oscillation*. It does not hold a clean
  value. This is the behaviour the involution loop model predicts and that FID_RESOLVE's default
  clean hold hides (A-fid3 row "LUT state loop"). Cite it as support for running `+META_X=1`, or a
  pulse-train resolver, in pessimistic GLS.

**4.3 Pulse-shrinking TDCs (not 7-series).** R. Szplet, K. Klepacki, "An FPGA-integrated
time-to-digital converter based on two-stage pulse shrinking," IEEE Trans. Instrum. Meas., 2010,
IEEE Xplore 5280372. [abs]
- Cyclic pulse shrinking in a loop with "two complementary delay lines", on Spartan-3: 42 ps
  resolution, 11.5 ns range.
- For us: FPGA LUT and route loops propagate pulses whose width changes by a small, repeatable
  amount per lap. That fits the involution and asymmetric-transport picture.
- It is not 28 nm, and the minimum surviving width was not seen.

**4.4 Vendor simulation convention (not silicon).** AMD UG900 (Vivado logic simulation),
xelab options, versions 2021.1-2025.2:
- `-pulse_r` and `-pulse_e` default to 100 (% of path delay). So by default a pulse shorter than
  the path delay is rejected (inertial).
- For timing simulation AMD recommends `-transport_int_delays -pulse_r 0 -pulse_int_r 0`
  ("Running Timing Simulation", 2025.2) [abs/snip]. That is transport with no rejection.
- For us: AMD's own sign-off simulation convention is transport. Iverilog's inertial specify paths
  are therefore *less* faithful to AMD practice than our transport GLS. This is a statement about
  practice, not about silicon.

**4.5 LUT internal skew.**
- Peter Alfke (Xilinx), comp.arch.fpga 2005-2006 (A-lit-1 §5.4 has the SIC claim). [snip] It adds
  that the mux is "done by pass transistors, and the internal capacitance holds the value during
  non-overlapped switching". It also says per-input LUT delay differences "are not in the data
  sheet, but they are ... in the speeds files". That was the Virtex-4 era.
- For us: per-pin delays are the prjxray/SDF numbers we already use. No silicon measurement of 7-series
  internal skew or MIC glitches was found. `H_LUT` SIC stays folklore plus our own GLS and board tests.

**4.6 Other negatives.**
- No 7-series single-event-transient (SET) pulse-propagation study was found. The SET pulse
  broadening and attenuation literature is for ASICs and 130 nm flash FPGAs.
- Chen et al. (Altera, FPGA 2010) and the 2009 PGR paper treat routing glitch filtering only in
  simulation.

**Recommendation.** The deciding experiment is still the board test of A-delay-inertial §4(ii):
a two-path pulse whose width is swept through δ_LUT, read out by a toggle counter. A step means
inertial; a ramp means involution. A TERO-style loop (4.1) is a cheap second test of rise/fall
asymmetry (Δr) per LUT pin. The reference HDL for it is public.

---

## 5. Arbiter and synchroniser τ on 28 nm (7-series)

**No published τ or T_W for any 7-series flip-flop, LUT latch or MUTEX was found.** New facts:

- **AMD UG835**, `report_synchronizer_mtbf` (2023.2) [snip]: "supported for AMD UltraScale devices
  only, and does not support AMD 7 series devices". So AMD does not ship 7-series metastability
  parameters even in the tool. A τ for our part must come from our own measurement.
- **N. V. Toan, D. M. Tung, J.-G. Lee, "Measurements of metastability in MUTEX on an FPGA,"**
  IEICE Electronics Express 15(1):20171165, 2018, DOI 10.1587/elex.14.20171165. [abs]
  - A LUT-built MUTEX on Spartan-6 (XC6SLX9, 45 nm). Near-simultaneous requests come from DCM
    fine phase shift, and the resolution time is measured.
  - This is the closest published template for hw/arb_mtbf. Our design uses MMCM fine phase
    shift, its 7-series equivalent. The numbers were not visible and the part is not 28 nm.
- **D. Chen, D. Singh, J. Chromczak, D. Lewis, R. Fung, D. Neto, V. Betz, "A comprehensive
  approach to modeling, characterizing and optimizing for metastability in FPGAs,"** FPGA 2010,
  pp. 167-176 [abs]. Altera: a model, SPICE and board characterisation, and CAD optimisation.
  The numbers were not visible. A method reference.
- **S. Beer, R. Ginosar et al., "An on-chip metastability measurement circuit to characterize
  synchronization behavior in 65nm,"** ISCAS 2011 [abs]. Fully digital on-chip τ measurement,
  65 nm ASIC. A method reference.
- **Bernard, Haddad, Fischer, Nicolai, "From physical to stochastic modeling of a TERO-based
  TRNG,"** J. Cryptology, 2018/2019, DOI 10.1007/s00145-018-9291-2. CHES 2015 version, ePrint
  2015/593 [abs].
  - A physical, then stochastic, model of how the TERO oscillation count decays, validated on an
    ST 28 nm bulk ASIC (not an FPGA).
  - For us: the only 28 nm source found on how a cross-coupled loop decays. It is a possible model
    to compare with our involution-loop rate (TAU_eff), which is unproved.
- A blog figure of "2-10 ns τ at 28 nm" (ecrionix.org) has no source. **Do not cite it.**
- Status unchanged from literature.md §8.5: the known FPGA values are 57/51/73 ps at
  130/90/65 nm (Beer and Ginosar, ASYNC 2010). TAU_FF = 75 ps in our GLS is an assumption, and
  hw/arb_mtbf would produce the first public 7-series figure. The SR-latch-PUF counts (4.2) show
  that a LUT-latch metastability event on Zynq is observable with an 8-bit oscillation counter.
  That is a cheap add-on to hw/arb_mtbf: count q toggles per race (already proposed in A-fid3).

---

## Summary for the lead

1. **IDM.**
   - Equality cancels. DATE'15 [snip]: cancel if t_n+δ_n ≥ t_m+δ_m. The TCAD lemma: cancel iff
     t_{n+1} ≤ t_n+δ_n−δmin iff δ_{n+1} ≤ δmin. Our `o' ≤ o` and the threshold Δ ≤ δ∞↑−δmin
     match, so the open item in A-inv-trace can be closed.
   - CIDM's "IDM followed by pure delay is an involution channel" is our `outList_shiftPair`.
     It is known; cite it.
   - The OR-loop facts are known in the papers: the lost/latch/oscillate trichotomy, unbounded
     resolution and monotone trains (DSD'21, DATE'18, DDECS'23). Our mechanisation is new.
   - The closed-form s* = δ∞↑ − l with its stationary train, the symmetric bound (δ∞/2,
     δ∞−δmin/2) and the asymmetry direction were not found. Read the TCAD Δ̃ lemma before calling
     them new.
   - SPICE (DSD'21) confirms OR-loop oscillation and SR-latch metastability under IDM.
2. **Proofs of elastic and async circuits.**
   - New Lean 4 asynchronous work exists: async-lean (SI/QDI, Petri, STG, untimed, Oct 2026) and
     MCL (metric-free relative timing, integer pure delay, C-element `hold`, SASIMI'27
     submission). Update A-lit-3 §5.6.
   - Missed Coq item: Law, Demange, Blazy, OOPSLA 2025 (Dynamatic semantics).
   - Still nothing with metric delay bounds, bundling or FPGA cells.
3. **X-sim and MC.** Bund-Lenzen-Medina hazard-free transducers (IEEE TC 2025), MC addition
   codes (2026), and Arazi-Shpilka hazard-free formulas (ICALP'25). No mechanised ternary
   soundness was found, so ours appears to be first. W4 stays a hypothesis.
4. **LUT pulse rejection.**
   - Not measured for 7-series anywhere. The literature does not decide transport versus
     inertial.
   - 7-series silicon does show long-lived pulse trains in LUT loops: TERO on Artix-7 runs for
     hundreds of laps, "infinite" at small asymmetry. It also shows metastable oscillation of a
     2-LUT SR latch on Zynq-7010.
   - That supports "the echo is physical" and the pulse-train resolution picture, but not
     anything about sub-δ_LUT pulses.
   - AMD's recommended timing simulation is transport (`-pulse_r 0`).
   - The board test is still needed.
5. **τ at 28 nm.** None published. Vivado's MTBF report excludes 7-series. The method templates
   are Toan et al. 2018 (LUT MUTEX, DCM phase), Chen et al. FPGA 2010 and Beer et al. 2011.

Files: this note only. Scratch clones (untrusted, not committed):
/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad/Lit4/dl1/async-lean,
/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad/Lit4/dl2/mcl,
/tmp/claude-0/-home-user-asyncfpga3/e4887bac-6d7b-51e8-a617-7dbd05e5b307/scratchpad/Lit4/dl3/tc.
