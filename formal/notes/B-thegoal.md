# Shard B under THE goal: results of 2026-11-01 (for STATUS / FEASIBILITY)

Every Lean item: check.sh OK (per file), standard axioms only. Simulation items: untrusted Python.

## H_PRIM (STATUS item 3)
- `Cells/PrimTables`: LUT6_2 O6/O5, MUXF7/F8 (0xCA), CARRY4 (8 tables; Core pin order AND shard A's
  build_net.py layout) as Spec table gates, each proved equal to Core's model. With audit T4 (no FF in the
  kernel cone), every primitive in the cone has its Spec form.
- `Cells/HPrimWin`: the window (bounded-delay Kleene) form; implied by time-varying transport and by inertial
  behaviours; widening-monotone; settling and single-input-change lemmas.
- `Cells/HPrimInv`: read-time models (Spec GateOK, WinH) do NOT cover involution channels in general
  (ratPair trace); they do for separated inputs. Fidelity-table entry for A.

## H_ARB (STATUS item 4)
- `Cells/SpecArbVacuous`: Spec v1's ArbOK made NetCorrect vacuous on every held-arbiter handover (A repaired
  it at 08:11). `Cells/ArbOKRepair`: the repaired ArbOK admits the handover, and is vacuous for T below the
  state gate's slowest arc (the theorem must take T at least that).
- `Cells/ArbT`, `Cells/ArbTSpec`: H_ARB(T) alone does not give exclusion: `spec_double_ack` (a frozen-Spec
  behaviour, repaired ArbOK for T >= 7) acknowledges both clients; `one_ack`/`spec_one_ack`: q settled W before
  A0 rises gives one acknowledge per transaction.
- `Cells/ArbClean`: a separated arbitration is decided by the gate relation alone (`q_clean_set(_gen)`), and
  the target's nine ustates (pin-permuted) meet its table facts (`targetQ_facts`, generated data).
- Simulation: on all 16 rig vectors every arbitration is separated by >= ~50 ns, robust to adversarial
  in-band skew; H_ARB is never exercised.

## S3 (feedback cells' loop timing)
- `Cells/SpecFb`: stay / forced / clean switch (forcing >= feedback arc) for any feedback LUT; a C-element
  left oscillating for ever by a short forcing episode (`fb_runt_oscillates`).
- `formal/out/target_fb_nodes.json`: the 4401 storage nodes of the kernel cone, feedback routes, loop bands,
  tightest simulated episodes.
- **Candidate counterexample (simulation):** arbiter 0's acknowledge C-element ua1 (SLICE_X2Y18.DLUT.O6)
  latches a runt that circulates for ever, at g = 1, κ >= 0.155 (corners 0.2-0.3; g >= 1.2: κ >= 0.148 at the
  fast corner), sequential env, 4 of 6 rig vectors tried; reproduced flip-for-flip by an independent
  simulator. Rests on transport (GateOK admits it); involution/inertial gates would let ua1 latch. If every
  reader of ua1 skips the runt (a read-map choice inside the bands) the run is correct, so the failure needs a
  reader to see it. [CORRECTED 2026-11-02, audit T6: "with runt resolution the same delays give the correct
  result" holds only for B's simb --gfilter model; research's fid GLS with its resolver still shows out0_req
  pulse trains and a stall at these delays, so the "it is only transport pessimism" reading is withdrawn; and
  no finite run shows the liveness failure, so "counterexample" is UNVERIFIED. Period is 901 ps, not 894.]
  tools-B/target/out/cex_ua1_README.md.
- `Cells/Ua1Static` (Lean, decided on generated arc data): ua1's fb_switch premise holds for its tightest
  episode at κ = 0.15 (path >= 865 ps, loop <= 852 ps) and can fail at κ = 0.16 (852 < 860).
- Static estimate over all storage nodes (tools-B/target/kstar.py, calibrated on ua1): only ua1 binds below
  κ = 0.36 (next: SLICE_X0Y18.CLUT.O6 0.365, SLICE_X42Y82.ALUT.O6 0.500).

## Tools (tools-B/target/)
lean2json (decoded Lean net -> JSON), simb (A's simulator + per-gate/per-pin positions, κ, g, watch, runt
filters), sim2 (independent re-implementation), adv/tie/a0race (arbitration timing), fbscan/fbtable/fbadv
(storage-node margins), kmap (κ thresholds), gen_targetq.

# 2026-11-02: THE target gcd_ps_e6bb4aec (owner decision 1)

- **Storage-node races (simulation, untrusted; tools-B/ps/kscan.sh, kcorner.sh, kadv.py, current Spec.Adm):**
  the tightest node is SLICE_X32Y45.ALUT.O6 = `ulink_n_falseResult_85.many.stage[0].u.ctl.u.u` (a link
  controller C-element; gate 120808 of DecodedPS.net), exercised by 24 of 32 vectors. Race threshold (g = 1,
  vector (12,18)): corner 0.0: 0.419/0.425; 0.5: 0.4375/0.444; 0.8: 0.4375/0.444; 1.0: 0.444/0.450 (clean/runt).
  Next nodes (static κ*): SLICE_X18Y96.A ~0.50-0.52, SLICE_X16Y22.C ~0.515-0.54. On gcd_hw the binding node
  (`ucontrol_merge10.uarb1.ua2`, nicknamed "ua1") gave 0.155; in gcd_ps that cell does not bind.
- `Cells/RaceStaticPS` (Lean, generated arc data): the node's fb_switch premise holds for its tightest episode
  at κ = 0.435 (path >= 1099 ps, loop <= 1091 ps), fails at 0.44 (1093 < 1094); corner 1/2.
- `Cells/ArbCleanPS` (Lean): gcd_ps's nine ustates meet ArbClean's table facts. Arc SLOW_MAX up to 664 ps,
  so the T non-vacuity bound is (1+κ)·664·g ps, as on gcd_hw.
- `Cells/SpecFbChain` (Lean, generic): fb_switch through a routed feedback (C's CGateOK), and Spec.Adm's
  integer window ends bound every summed delay (`sumAdm_bounds`).
- `Cells/TargetLinkPS` (Lean, generated; building): ties targetQPS and the race arcs to DecodedPS.net, the
  node's feedback chain (`pinsOK`), and `race_loop_delay_le` (feedback delay <= 1091 ps at κ = 0.435).
- Arbiter separation on gcd_ps (adv.py, 32 vectors, corner 0.5): see JOURNAL-B.
