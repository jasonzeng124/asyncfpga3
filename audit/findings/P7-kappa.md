# P7-kappa: audit of formal 861de85 (B kappa), 6763571 CornerCode, 66d94fa/2f0994e Involution*, 065a361 TernaryChannels, 807448a/21b1b7c RigContract

Checkout ~/wt-f7 at 6863284. Auditor files: audit/lean/P7k/ (P7kAudit.lean: #print axioms for 45 headline
theorems + own witnesses; Mut*.lean: 7 mutants), audit/P7k/ (lutarcs.py/.out, xfix.py, gcdk.py).

**STATUS OF LEAN CHECKS: NOT RUN.** The clean `lake build` of 6863284 was still compiling Mathlib
(log at [~2800/...] Mathlib modules, no EXIT line) when this report had to be handed back. So for every
row: compilation in the clean build, my #print axioms, my witnesses and my mutation results are
UNVERIFIED. Re-run once the log ends with EXIT:
`cd ~/wt-f7/formal/lean && lake env lean /home/user/asyncfpga3/audit/lean/P7k/P7kAudit.lean`
then each `Mut*.lean` (each must FAIL; expected failing theorem in the table in "Mutants").
Shard B's own notes (B-constraints-kappa.md, B-arb-kappa.md, B-gcd-arb-kappa.md) say the three kappa
files were never checked against real Mathlib either, only against hand-made core mirrors.

grep for sorry/admit/native_decide/implemented_by/extern/unsafe/axiom/opaque on the 18 files of the
proof paths (ConstraintsKappa, OnNetlistArbKappa, OnGcdArbKappa, CornerNat, CornerCode,
InvolutionTransfer, InvolutionDMin, Involution, Pure, TernaryChannels, Ternary, RigContract, ArbA0Fork,
OnNetlistArb, ArbCornersPin, OnGcdArbA0, OnGcdArbFix, ArbPin2): only comment hits. Row checks use
`decide +kernel` (kernel, not native).

| commit | claim (quoted) | verdict | evidence | note |
|---|---|---|---|---|
| 861de85 ConstraintsKappa | "exact corner-model check GenOK for every constraint shape, sound, tight under H_DISJ/H_DIV, sandwich otherwise; box and SLOW-only checks unsound for kappa > 0" | CONFIRMED by statement reading; compile UNVERIFIED | allOK_of_gen (no extra hyps), allOK_iff_gen (Disj+DivOK), sandwich, box_unsound_with_kappa, slow_only_unsound read in full; model = CornerNat (one shared rational corner, per-arc scatter ±κ around lerp(F,S)) | slow-only is unsound even at κ=0 (stronger than claimed). box counterexample uses a degenerate arc F=S. Meaning depends entirely on the H_SHARED_CORNER + scatter model; κ itself unmeasured (A withdrew 0.311) |
| 861de85 OnNetlistArbKappa | "link_arb A0 fork safe 8/8 at kappa 1/11; exact per-pair kappa thresholds" | safe 8/8 at 1/11: CONFIRMED (reading); "exact thresholds": OVERSTATED | verdict_*_κA are all ∀-safe; safe_* at κ ≤ κ*, unsafe_* only at κ ≥ κ*+6/(E+L) (file docstring: "Between the two ... not decided"). My hand computation: s1c2 cons at κ=200/1103 (inside the gap) already has a violating fast-corner assignment (535 > 534), so κ* is the real-relaxation bound, not the whole-ps threshold (`P7kAudit.s1c2_gap_unsafe_at_200`, unchecked) | pins: aG uses the ugrant q pin read from the bits (A5 on s1/s3/s4 client 1, A3 on s2), matching P3's FasmLink evidence. `cons` early SLOW_MIN / late FAST_MAX come from Bt3 prose and are not tied to any file |
| 861de85 OnGcdArbKappa | "all 36 gcd_hw arbiters x 18 conditions safe for kappa <= 16587/374773 ~ 0.0443 (lit), 0.0802 with the server credited; 5 rows on 3 arbiters fail at kappa = 0 (cons)" | Arithmetic CONFIRMED (own recomputation); arc data vs route UNVERIFIED; "tight" OVERSTATED (mildly) | audit/P7k/gcdk.py, my own parser over the Lean data: lit min 16587/374773 (g3 merge12.uarb1 rt1b), server-credited min 138217/1724217 (g2 merge3 h21), 0 lit negatives, cons negatives exactly the 5 rows claimed; 5 lit rows fail at 1/11, 28 at κE (as in the note). LUT arcs: 360/360 match prjxray per-(site type, O5/O6, pin) envelopes (lutarcs.out); 3168/3168 values agree with OnGcdArbFix's independent Q records (xfix.py) | design_gate_lit gives gate-level safety at κ ≤ 0.0443. Unsafe direction only at the arc-form level, from κu = 33181/749546 (gap 1.3e-5), not at κ* itself and not gate-level (note admits). gcd_hw routes (seeds 2,3,4,d) are not on disk (only sha_*.txt), so wire numbers (rg2, rs2, ...) cannot be checked. Q-pin: per-arbiter (ag1q: A1 8, A2 8, A3 3, A4 7, A5 10 arbiters; binding rows are A5) so the P3 A3-vs-A5 issue is addressed in the data; whether each pin is the routed one is UNVERIFIED. LUT arcs are envelopes over the 4 LUT letters (A-D), up to 3 ps off the actual BEL |
| 6763571 CornerCode | "tighten.py rule A as coded is sound iff kappa <= 25/276 (SLACK>=1 gives 1/11)" | CONFIRMED (reading + code); compile UNVERIFIED | tighten.py:1129-1132 `max(int(0.2*t),200)+SLACK`, check() l.793 margin = t_e - t_l - g, SDF parsed with int(): matches `guard`/`pass` with t/5 floor. int(0.2*t)==t//5: 0 mismatches for t<1e7 and 1e6 random t<2^50 (49795 mismatches at 2^53: out of range, ok). ruleA_code_iff/model_iff: both directions over all t (∀ te tl : ℕ). Slack: ruleA_slack_sound (S≥1, κ≤1/11) + ruleA_slack_tight (∀S, κ>1/11 has a counterexample) | Model is the proportional one-SDF-number corner (scale s, ±κ), not CornerNat; float→floor fact proved only by scan (stated) |
| 66d94fa / 2f0994e Involution* | "S > D - dmin => no cancellation, bounded pure delay in [delta(S-D), D], Pure.Chan relation, sharp threshold, concrete instance"; "dmin exists for every involution pair" | CONFIRMED (reading); compile UNVERIFIED | transfer_sep concludes tent strictly increasing, band, and `Chan lo hi (sigOf N t) (sigOf N tent)` with DelayPure.Chan (real Retime relation); ratPair δ(T)=2-1/(T+2) is a full InvolutionPair with rat_dmin; exists_dmin proved by sSup + down_surj, no new field; sep_threshold_exact is an iff incl. asymmetric pairs; both modules imported in Formal.lean | "no cancellation" = tent(n)<tent(n+1); the filtered output with chained cancellations still not formalised (stated). sep_threshold_sharp in 66d94fa alone was exact only for symmetric pairs; 2f0994e closes it |
| 065a361 TernaryChannels | "ternary simulation sound for gates + transport/inertial channels with positive lower delay (RCausal), settling within |nu|*D; counterexamples for zero delay and grid sampling" | CONFIRMED (reading); compile UNVERIFIED | transport/inertial membership is PROVED, not assumed: chan_readsPast, inertialRD_readsPast, boundedInertial_* → nodeChan_readsPast → rcausal_of_nodeChan; settle via SettlesWithin; ternary_settle_channels bound T0 + l.length*D; zero_delay_chan_unsound, zero_delay_inertial_unsound, sample_not_causal | uses the real DelayPure.Chan and DelayInertial.InertialRD (Filt) definitions. No positive in-tree instance of the settle theorem; mine is P7kAudit.tern_settle_witness (unchecked). Involution channels not covered (stated) |
| 807448a / 21b1b7c RigContract | "compiles (audit row 48)"; withdrawn claims | Compile UNVERIFIED (clean build not finished); wording CONFIRMED | stale_window now binds `{e : Nat → Nat}` explicitly (l.605); stale_nonvacuous passes `(e := e)`. Docstring now says verdict_attrib needs H_RESULT_FRESH; notes correction block: "refuted"/"explained exactly" downgraded to "excluded given H_RESULT_FRESH", C_STALE unproved, necessity of stale_window withdrawn, "bit-exact" qualified (arm_sr/hold_* constants), idx_setup's H_TOKEN_STATIC false in the running ring (exact version in RigIdx) | must check the build log for RigContract once EXIT appears |

## Mutants (prepared, NOT yet run; each must fail to compile)
- MutCK.lean: GenOK request side `k.lo` → `k.den` (no scatter on requests); expect allOK_of_gen to fail.
- MutNAK.lean: safe_s1c2_cons bound 197 → 198; expect failure.
- P7kAudit.gcd_mut_breaks: +1 ps on rg2 FAST_MIN of g3 merge12.uarb1 makes certFor at 16587/374773 false (in-file test; gcd_orig_ok is the control).
- MutCC.lean: ruleA_code_iff threshold 25/276 → 1/11; expect failure.
- MutIT.lean: rat_transfer_example band 4/3 → 3/2; expect failure.
- MutID.lean: sep_threshold_exact `infDown - dmin ≤ S` → `<`; expect failure.
- MutTC.lean: ternary_noGlitch_channels `0 < δ` → `0 ≤ δ`; expect failure.
- MutRC.lean: stale_nonvacuous t = e n0 + 1500 → +500 (before the 600 ps arm path); expect failure.

## Model remarks (kappa)
κ = per-arc relative scatter around a die-wide corner c ∈ [0,1] interpolating each arc between its
FAST and SLOW endpoint (CornerNat: H_ENDPOINTS, H_AFFINE, H_SHARED_CORNER, H_SCATTER). It is a coherent
model, but (a) no κ is measured on the current toolchain, so every "safe" verdict is conditional; (b) in the
`lit` reading the prjxray within-corner min..max spread (about 0.1-0.2) must itself fit inside κ, while
the safe thresholds are 0.044/0.080, so `lit` safety at those κ implicitly assumes the within-corner
spread is fully correlated die-wide; in the `cons` reading (spread charged to each side) 3 gcd arbiters
fail at κ = 0. One delay per arc per run (rise = fall).
