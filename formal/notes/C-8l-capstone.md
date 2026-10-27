# C-8l: Phase 3 capstone, shard C's part (IN PROGRESS, notes kept current)

## Status so far
- (1a) `Formal/Net/OpsLink.lean`: bd_link (Muller) as an Ops operator: `link_op`
  (OpProto + OpData, equation `σ o k = σ i k`), `link_capacity` (one place),
  `link_held`, `link_out_le`. Checks in ~2 s.
- (1b) `Formal/Net/OpsMuxN.lean` + `OpsMuxNOp.lean`: bdc_muxn N = 3, 648 states
  (594 with s < 3), closure split into 4+4 kernel decides by select value;
  `muxn_op`. ~2.3 min, peak 2.9 GB.
- (2), (3), (4): in progress.
