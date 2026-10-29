# A-inv-loop: the involution OR loop, pulse-width orbit, critical runt (probe InvLoop, shard A)

STATUS: in progress (plan written; Lean being written in formal/lean/Formal/Core/Delay/InvolutionLoop.lean).

Plan.
- Same recurrence as B's `CElemInvolution.orb` (copied, so a bridge is `rfl`), on A's `InvolutionPair`.
- Widths `wd s n = o(n+1) - o(n)` satisfy `wd (n+1) = δ_n(-wd n) - wd n`; each half-lap map
  `w ↦ δ(-w) - w` is strictly decreasing and EXPANDING (|Δout| > |Δin|), from strict monotonicity alone.
- Stationary train (h*, l*): δ↑(-h*) = h* + l* = δ↓(-l*). Critical input runt s* = δ∞↑ - l*.
- Symmetric: h* = l* = w*, 2 w* = δ(-w*); s* = δ∞ - w* > δ∞/2 (NOT = δ∞/2).
- Growth/decay with a linear rate on each side; unbounded laps near s* (elementary continuity from surjectivity).
