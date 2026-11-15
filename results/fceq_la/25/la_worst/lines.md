## eventgraph, corner worst

- c0 critical: 34394 ps, 88 arcs, stages ulink_n13 851/851, ulink_n14__1 14366/14366, umux1 2433/1527; polarity changes ulink_n13R->ulink_n14__1F, ulink_n13F->ulink_n14__1R

| line | n | ps (ps/el) | on cycle R/F | set by | margin | launch -> capture | data: logic / latch / enable / wire / ctl | en spread | req: total / not line / wire | guard | n_need | n_logic | corner_audit proposal | widest data wire | flags |
|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|---|
| ulink_n14__1.many.stage[1].u.rdly | 36 | 13424 (382) | 13935/13935 | E depends | 13155 | ulink_n14__1.many.stage[1].u.ctl.u.u -> umux1.uj1/A4 | 0 / 68 / 183 / 618 / 0 |  | 14485 / 550 / 550 | 0.97/1.03 | 1 | 0 | 36 | ulink_n14__1.many.stage[1].u.lat.odd.u/O6 -> umux1.uj1/A4 618 | select link (withdrawn select rule; corner_audit never shortens it); corner_audit: select path: never shortened (see docstring) |
| umux1.udly | 5 | 1111 (262) | 1479/573 | A own | 1233 | umux1.uj1 -> umux1.uya.u/O6 | 0 / 0 / 0 / 464 / 68 |  | 1815 / 336 / 268 | 50 | 1 | 0 | 5 | umux1.uj1/O6 -> umux1.uya.u/A2 464 | F (own flush) margin 2253; mux delay (withdrawn select rule; corner_audit never shortens it); rule A pairs by common source umux1.uj1; 32 peer output(s) no common source pairs with the request, on NO rule-A constraint: umux1.udat; corner_audit: select path: never shortened (see docstring) |
| ulink_n13.uack | 1 | 62 (373) | 355/355 | H own | 933 |  ->  |  /  /  /  /  | 406-958 (32 bits) | 2016 /  /  |  | 0 |  | 1 |  | corner_audit: floor 1; totals only (H) |
