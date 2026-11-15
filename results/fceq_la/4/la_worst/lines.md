## eventgraph, corner worst

- c0 critical: 38514 ps, 88 arcs, stages ulink_n13 1579/1579, ulink_n14__1 15530/15530, umux1 2956/1340; polarity changes ulink_n13R->ulink_n14__1F, ulink_n13F->ulink_n14__1R

| line | n | ps (ps/el) | on cycle R/F | set by | margin | launch -> capture | data: logic / latch / enable / wire / ctl | en spread | req: total / not line / wire | guard | n_need | n_logic | corner_audit proposal | widest data wire | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| ulink_n14__1.many.stage[1].u.rdly | 36 | 14591 (415) | 15012/15012 | E depends | 14443 | ulink_n14__1.many.stage[1].u.ctl.u.u -> umux1.uj1/A5 | 0 / 68 / 171 / 306 / 0 |  | 15469 / 457 / 457 | 0.97/1.03 | 1 | 0 | 36 | ulink_n14__1.many.stage[1].u.lat.odd.u/O6 -> umux1.uj1/A5 306 | select link (withdrawn select rule; corner_audit never shortens it); corner_audit: select path: never shortened (see docstring) |
| umux1.udly | 5 | 1561 (375) | 1911/295 | A own | 1975 | umux1.uj0 -> umux1.uxa.u/O6 | 0 / 0 / 0 / 442 / 68 |  | 2535 / 624 / 556 | 50 | 0 | 0 | 5 | umux1.uj0/O6 -> umux1.uxa.u/A1 442 | F (own flush) margin 2840; mux delay (withdrawn select rule; corner_audit never shortens it); rule A pairs by common source umux1.uj0; 32 peer output(s) no common source pairs with the request, on NO rule-A constraint: umux1.udat; corner_audit: select path: never shortened (see docstring) |
| ulink_n13.uack | 1 | 62 (376) | 799/799 | H own | 1540 |  ->  |  /  /  /  /  | 180-1031 (32 bits) | 2696 /  /  |  | 0 |  | 1 |  | corner_audit: floor 1; totals only (H) |
