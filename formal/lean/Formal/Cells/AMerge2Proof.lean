import Formal.Cells.AMerge2

/-!
# Probe Cm, part 2b: `bdc_amerge2_0`, the certificate and the theorems

Model, spec and named hypotheses: `Formal.Cells.AMerge2`.
-/

namespace Formal.Cells.AMerge2
open Formal.Cells.AMergeSys Formal.Cells.AMergeGates

/-- Reachable-set certificate for `sys hOK` (183 states with their
excitation masks), produced by the scratch explorer; checked below. -/
def T2 : KTree := (.node (.node (.node (.node (.node (.node (.node (.node .leaf 0 3 .leaf) 1 26 .leaf) 2 5 (.node (.node .leaf 3 24 .leaf) 4 3 .leaf)) 5 6 (.node (.node (.node .leaf 6 41 .leaf) 7 40 .leaf) 9 530 (.node (.node .leaf 11 528 .leaf) 14 545 .leaf))) 15 544 (.node (.node (.node (.node .leaf 17 10 .leaf) 19 8 .leaf) 25 514 (.node (.node .leaf 27 512 .leaf) 38 4105 .leaf)) 39 4104 (.node (.node (.node .leaf 46 4609 .leaf) 47 4608 .leaf) 257 282 (.node .leaf 259 280 .leaf)))) 260 259 (.node (.node (.node (.node (.node .leaf 261 262 .leaf) 262 297 .leaf) 263 296 (.node (.node .leaf 265 786 .leaf) 267 784 .leaf)) 270 801 (.node (.node (.node .leaf 271 800 .leaf) 273 266 .leaf) 275 264 (.node (.node .leaf 281 770 .leaf) 283 768 .leaf))) 294 4361 (.node (.node (.node (.node .leaf 295 4360 .leaf) 302 4865 .leaf) 303 4864 (.node (.node .leaf 521 1042 .leaf) 523 1040 .leaf)) 526 1057 (.node (.node (.node .leaf 527 1056 .leaf) 537 1026 .leaf) 539 1024 (.node .leaf 558 5121 .leaf))))) 559 5120 (.node (.node (.node (.node (.node (.node .leaf 777 1298 .leaf) 779 1296 .leaf) 782 1313 (.node (.node .leaf 783 1312 .leaf) 793 1282 .leaf)) 795 1280 (.node (.node (.node .leaf 814 5377 .leaf) 815 5376 .leaf) 4134 265 (.node (.node .leaf 4135 264 .leaf) 4142 769 .leaf))) 4143 768 (.node (.node (.node (.node .leaf 4353 4122 .leaf) 4355 4120 .leaf) 4356 4099 (.node (.node .leaf 4357 4102 .leaf) 4358 4137 .leaf)) 4359 4136 (.node (.node (.node .leaf 4361 4626 .leaf) 4363 4624 .leaf) 4366 4641 (.node .leaf 4367 4640 .leaf)))) 4369 4106 (.node (.node (.node (.node (.node .leaf 4371 4104 .leaf) 4377 4610 .leaf) 4379 4608 (.node (.node .leaf 4390 9 .leaf) 4391 8 .leaf)) 4398 513 (.node (.node (.node .leaf 4399 512 .leaf) 4654 1281 .leaf) 4655 1280 (.node (.node .leaf 4873 5138 .leaf) 4875 5136 .leaf))) 4878 5153 (.node (.node (.node (.node .leaf 4879 5152 .leaf) 4889 5122 .leaf) 4891 5120 (.node (.node .leaf 4910 1025 .leaf) 4911 1024 .leaf)) 17929 2066 (.node (.node (.node .leaf 17931 2064 .leaf) 17945 2050 .leaf) 17947 2048 (.node .leaf 38702 2049 .leaf)))))) 38703 2048 (.node (.node (.node (.node (.node (.node (.node .leaf 65600 66 .leaf) 65602 68 .leaf) 65606 104 (.node (.node .leaf 65614 608 .leaf) 65616 18 .leaf)) 65618 20 (.node (.node (.node .leaf 65622 56 .leaf) 65630 560 .leaf) 65638 4168 (.node (.node .leaf 65646 4672 .leaf) 66126 1120 .leaf))) 66142 1072 (.node (.node (.node (.node .leaf 66158 5184 .leaf) 69734 328 .leaf) 69742 832 (.node (.node .leaf 69990 72 .leaf) 69998 576 .leaf)) 70254 1344 (.node (.node (.node .leaf 70510 1088 .leaf) 84032 2050 .leaf) 84034 2048 (.node .leaf 84048 2066 .leaf)))) 84050 2064 (.node (.node (.node (.node (.node .leaf 85056 1026 .leaf) 85058 1024 .leaf) 85072 1042 (.node (.node .leaf 85074 1040 .leaf) 85513 18 .leaf)) 85515 16 (.node (.node (.node .leaf 85529 66 .leaf) 85531 64 .leaf) 85568 514 (.node (.node .leaf 85570 512 .leaf) 85576 10 .leaf))) 85578 8 (.node (.node (.node (.node .leaf 85584 530 .leaf) 85586 528 .leaf) 85592 26 (.node (.node .leaf 85593 3 .leaf) 85594 24 .leaf)) 85595 1 (.node (.node (.node .leaf 104302 2112 .leaf) 131457 152 .leaf) 131460 129 (.node .leaf 131461 132 .leaf))))) 131465 656 (.node (.node (.node (.node (.node (.node .leaf 131473 136 .leaf) 131481 640 .leaf) 131977 1168 (.node (.node .leaf 131993 1152 .leaf) 135553 4248 .leaf)) 135556 4225 (.node (.node (.node .leaf 135557 4228 .leaf) 135561 4752 .leaf) 135569 4232 (.node (.node .leaf 135577 4736 .leaf) 135585 56 .leaf))) 135588 33 (.node (.node (.node (.node .leaf 135589 36 .leaf) 135593 560 .leaf) 136073 5264 (.node (.node .leaf 136089 5248 .leaf) 136105 1072 .leaf)) 166276 2049 (.node (.node (.node .leaf 166277 2048 .leaf) 167300 1025 .leaf) 167301 1024 (.node .leaf 167812 513 .leaf)))) 167813 512 (.node (.node (.node (.node (.node .leaf 167820 9 .leaf) 167821 8 .leaf) 170372 6145 (.node (.node .leaf 170373 6144 .leaf) 170404 2081 .leaf)) 170405 2080 (.node (.node (.node .leaf 171396 5121 .leaf) 171397 5120 .leaf) 171428 1057 (.node (.node .leaf 171429 1056 .leaf) 171822 129 .leaf))) 171823 128 (.node (.node (.node (.node .leaf 171908 4609 .leaf) 171909 4608 .leaf) 171916 4105 (.node (.node .leaf 171917 4104 .leaf) 171940 545 .leaf)) 171941 544 (.node (.node (.node .leaf 171948 41 .leaf) 171949 40 .leaf) 171950 3 (.node .leaf 171951 2 .leaf)))))))

theorem amerge2_check : (sys gE hOK).check T2 = true := by decide +kernel

/-- **`bdc_amerge2_0` is a correct control_merge (speed independent, under
named hypotheses).** In every state reachable from reset, with unbounded gate
and wire delays on every gate of the wrapper and on the `g2 -> index` fork,
under H_RT1, H_RT2, H_BUNDLED_IDX, H_IDX_ACK_FORK, the arbiter-internal
isochrony listed in the module doc, and `q` Boolean (H_ARB_RESOLVED):
* `spec`: every step is a step of the control_merge automaton: each output
  transaction (`z_req`/`z_ack` cycle) carries exactly one input token, the one
  of the client the arbiter chose, and only that client is acknowledged, once,
  after the server acknowledged its token;
* `persist`: no gate or control wire of the wrapper or the arbiter (other
  than `q`, the decision node, and the index data cone) ever has its
  excitation withdrawn: no hazard;
* `live`: while a client waits and the others are at rest, some circuit or
  server step is allowed (no stranded token, no deadlock);
* `good`: the grants are never both high, and while `z_req` or `z_ack` is
  high `index` is 1 exactly when the owner is client 1 (input 1 won). -/
theorem amerge2_ok {s} (h : (sys gI hOK).Reach s) : Sys.Props (sys gI hOK) s := by
  rw [gI_eq_gE] at h ⊢; exact (Sys.sound amerge2_check h).2

/-- The check is not vacuous: a run in which client 1 wins and is served,
reaching a state with `z_ack` high, `index = 1` and `in1_ack` high. -/
theorem amerge2_serves_1 :
    ∃ s, (sys gI hOK).Reach s ∧ tb s 11 = true ∧ tb s 8 = true ∧ tb s 7 = true :=
  ⟨171950, Sys.run_reach [1, 2, 3, 5, 12, 8, 9, 10, 11, 7] Sys.Reach.init (by decide +kernel), by decide⟩

/-! ## Each hypothesis is needed (kernel-checked runs) -/

/-- **Without H_RT1** the two grants are both high: client 0 is served and
drops its request; `R0` falls, the server drops `A0`, `q` flips for the
waiting client 1 and `g2` rises while `g1`'s fall (excited) has not happened. -/
theorem amerge2_needs_rt1 :
    ∃ s, (sys gI ⟨false, true, true, false, true⟩).Reach s ∧ good s = false :=
  ⟨65654, Sys.run_reach [0, 1, 3, 4, 9, 10, 11, 6, 0, 3, 9, 10, 11, 2, 5] Sys.Reach.init
    (by decide +kernel), by decide⟩

/-- **Without H_RT2** the server's next `A0` rise withdraws the excitation of
the previous owner's falling acknowledge `A1` (a runt on `in0_ack`). -/
theorem amerge2_needs_rt2 :
    ∃ s, (sys gI ⟨true, false, true, false, true⟩).Reach s ∧
      (sys gI ⟨true, false, true, false, true⟩).can s 11 = true ∧
      exv gI ⟨true, false, true, false, true⟩ s 6 = true ∧
      exv gI ⟨true, false, true, false, true⟩ (fire s 11) 6 = false :=
  ⟨104302, Sys.run_reach [0, 1, 3, 4, 9, 10, 11, 6, 0, 3, 4, 9, 10, 11, 2, 3, 5, 9, 12, 8, 10]
    Sys.Reach.init (by decide +kernel), by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **Without H_BUNDLED_IDX** `z_req` rises before the index LUT has seen
`g2`: client 1 wins, and the consumer samples `index = 0`. -/
theorem amerge2_needs_bundled_idx :
    ∃ s, (sys gI ⟨true, true, false, false, true⟩).Reach s ∧ good s = false :=
  ⟨34318, Sys.run_reach [1, 2, 3, 9, 10] Sys.Reach.init (by decide +kernel), by decide⟩

/-- **H_IDX_ACK_FORK is needed** (every other fork isochronic, all other
hypotheses on): `in1_ack`'s rise reaches the client before the index LUT;
client 1 drops its request, `g2` falls and reaches the index LUT, which still
reads `in1_ack` low, so `index` falls while `z_ack` is high (the consumer's
data changes inside its hold window). The race: `A2 -> index` against
`A2 -> client -> r2 -> ugrant -> g2 -> index`. -/
theorem amerge2_needs_idx_ack_fork :
    ∃ s, (sys gI ⟨true, true, true, true, false⟩).Reach s ∧ good s = false :=
  ⟨167564, Sys.run_reach [1, 2, 3, 5, 8, 9, 10, 11, 7, 1, 5, 8] Sys.Reach.init
    (by decide +kernel), by decide⟩

/-- **H_ARB_RESOLVED** is why `q` is exempt from the hazard check. From
reset (`q = 1`), client 1 raises its request: `q` is excited to flip to 0.
Client 0 then raises its request: the tie holds `q`, and the flip is
withdrawn. In this binary interleaving model that is a nondeterministic
winner; on silicon it is the runt on the set/reset condition that can leave
`q` intermediate (ArbBinary `runt_*`, `exclusion_needs_sep`, H_REQ_SEP), whose
rate this file does not bound. Every theorem here assumes `q` Boolean. -/
theorem amerge2_q_race :
    ∃ s, (sys gI hOK).Reach s ∧ (sys gI hOK).can s 0 = true ∧
      exv gI hOK s 2 = true ∧ exv gI hOK (fire s 0) 2 = false :=
  ⟨2, Sys.run_reach [1] Sys.Reach.init (by decide +kernel), by decide +kernel,
    by decide +kernel, by decide +kernel⟩

end Formal.Cells.AMerge2
