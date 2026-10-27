# C-8h: per-link end-to-end theorem (tracks 8 + 10)

Status: IN PROGRESS (notes written first so a dead session leaves something).

Plan: (1) per-link `muller_pipeline2`; (2) rise/fall-asymmetric pins;
(3) per-event delays under a pulse-width condition; (4) latch open-width
numbers for a W=32 link.

## Progress (checkpoint 1)
Checks: PerLink.lean (muller_pipeline2), PerLinkPin.lean (EPin/ELink/DPin/latch_bit2),
EndToEnd2.lean (end_to_end2, end_to_end_fixed), EndToEnd2Toy.lean (split_global_rejects,
split_check2, dack_check2, dack_band_rejects). Next: PerLinkEvent.lean (per-event
construction under pulse width; BoundedDelay echo counterexample; FASTRISE OR line).
