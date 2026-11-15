## eventgraph, corner nom

- c0 critical: 35297 ps, 88 arcs, stages ulink_n13 1131/1131, ulink_n14__1 14190/14190, umux1 3146/1509; polarity changes ulink_n13R->ulink_n14__1F, ulink_n13F->ulink_n14__1R

| line | n | ps (ps/el) | on cycle R/F | set by | margin | launch -> capture | data: logic / latch / enable / wire / ctl | en spread | req: total / not line / wire | guard | n_need | n_logic | corner_audit proposal | widest data wire | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| ulink_n14__1.many.stage[1].u.rdly | 36 | 14700 (418) | 13766/13766 | E depends | 14518 | ulink_n14__1.many.stage[1].u.ctl.u.u -> umux1.uj0/A5 | 0 / 68 / 182 / 334 / 0 |  | 15588 / 344 / 344 | 0.97/1.03 | 1 | 0 | 36 | ulink_n14__1.many.stage[1].u.lat.odd.u/O6 -> umux1.uj0/A5 334 | select link (withdrawn select rule; corner_audit never shortens it); corner_audit: select path: never shortened (see docstring) |
| umux1.udly | 5 | 1877 (452) | 2301/664 | A own | 2457 | umux1.uj0 -> umux1.uxa.u/O6 | 0 / 0 / 0 / 378 / 68 |  | 2953 / 414 / 346 | 50 | 1 | 0 | 5 | umux1.uj0/O6 -> umux1.uxa.u/A3 378 | F (own flush) margin 2535; mux delay (withdrawn select rule; corner_audit never shortens it); rule A pairs by common source umux1.uj0; 32 peer output(s) no common source pairs with the request, on NO rule-A constraint: umux1.udat; corner_audit: select path: never shortened (see docstring) |
| ulink_n13.uack | 1 | 68 (416) | 497/497 | H own | 725 |  ->  |  /  /  /  /  | 481-1522 (32 bits) | 2372 /  /  |  | 0 |  | 1 |  | corner_audit: floor 1; totals only (H) |
