## eventgraph, corner nom

- c0 critical: 33378 ps, 88 arcs, stages ulink_n13 854/854, ulink_n14__1 13958/13958, umux1 2607/1147; polarity changes ulink_n13R->ulink_n14__1F, ulink_n13F->ulink_n14__1R

| line | n | ps (ps/el) | on cycle R/F | set by | margin | launch -> capture | data: logic / latch / enable / wire / ctl | en spread | req: total / not line / wire | guard | n_need | n_logic | corner_audit proposal | widest data wire | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| ulink_n14__1.many.stage[1].u.rdly | 36 | 14512 (413) | 13515/13515 | E depends | 13865 | ulink_n14__1.many.stage[1].u.ctl.u.u -> umux1.uj0/A3 | 0 / 68 / 171 / 620 / 0 |  | 15206 / 236 / 236 | 0.97/1.03 | 2 | 0 | 36 | ulink_n14__1.many.stage[1].u.lat.odd.u/O6 -> umux1.uj0/A3 620 | select link (withdrawn select rule; corner_audit never shortens it); corner_audit: select path: never shortened (see docstring) |
| umux1.udly | 5 | 1562 (374) | 1674/214 | A own | 1713 | umux1.uj0 -> umux1.uxa.u/O6 | 0 / 0 / 0 / 335 / 68 |  | 2166 / 313 / 245 | 50 | 1 | 0 | 5 | umux1.uj0/O6 -> umux1.uxa.u/A4 335 | F (own flush) margin 2061; mux delay (withdrawn select rule; corner_audit never shortens it); rule A pairs by common source umux1.uj0; 32 peer output(s) no common source pairs with the request, on NO rule-A constraint: umux1.udat; corner_audit: select path: never shortened (see docstring) |
| ulink_n13.uack | 1 | 68 (414) | 462/462 | H own | 1120 |  ->  |  /  /  /  /  | 218-894 (32 bits) | 2138 /  /  |  | 0 |  | 1 |  | corner_audit: floor 1; totals only (H) |
