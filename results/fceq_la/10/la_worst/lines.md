## eventgraph, corner worst

- c0 critical: 36746 ps, 88 arcs, stages ulink_n13 1015/1015, ulink_n14__1 15074/15074, umux1 2850/1718; polarity changes ulink_n13R->ulink_n14__1F, ulink_n13F->ulink_n14__1R

| line | n | ps (ps/el) | on cycle R/F | set by | margin | launch -> capture | data: logic / latch / enable / wire / ctl | en spread | req: total / not line / wire | guard | n_need | n_logic | corner_audit proposal | widest data wire | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| ulink_n14__1.many.stage[1].u.rdly | 36 | 14210 (404) | 14646/14646 | E depends | 14056 | ulink_n14__1.many.stage[1].u.ctl.u.u -> umux1.uj1/A5 | 0 / 68 / 184 / 324 / 0 |  | 15103 / 457 / 457 | 0.97/1.03 | 1 | 0 | 36 | ulink_n14__1.many.stage[1].u.lat.odd.u/O6 -> umux1.uj1/A5 324 | select link (withdrawn select rule; corner_audit never shortens it); corner_audit: select path: never shortened (see docstring) |
| umux1.udly | 5 | 1480 (354) | 1805/673 | A own | 1639 | umux1.uj1 -> umux1.uya.u/O6 | 0 / 0 / 0 / 568 / 68 |  | 2325 / 520 / 452 | 50 | 1 | 0 | 5 | umux1.uj1/O6 -> umux1.uya.u/A2 568 | F (own flush) margin 2555; mux delay (withdrawn select rule; corner_audit never shortens it); rule A pairs by common source umux1.uj1; 32 peer output(s) no common source pairs with the request, on NO rule-A constraint: umux1.udat; corner_audit: select path: never shortened (see docstring) |
| ulink_n13.uack | 1 | 62 (374) | 628/628 | H own | 1326 |  ->  |  /  /  /  /  | 244-727 (32 bits) | 2178 /  /  |  | 0 |  | 1 |  | corner_audit: floor 1; totals only (H) |
