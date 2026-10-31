import Formal.Net.CapstoneLiveNd5
/-! Negative controls for C-8z5 (silent = every control holds).

1. The local cell tables alone admit the full return-to-zero loop state of C-8z4's buggy
   explorer: a link with both sides acknowledged is a reachable link state, and an arbiter
   with `y` and `z` both acknowledged is a reachable arbiter state. So `no_rtz_loop` really
   needs the walk (the control token's order), not just the local invariants.
2. Without the count relation `d = [input mid-transaction]` (which comes from 8r's walk
   invariant), quiescent link states other than "input holds the token, output returning"
   exist: `link_quiet_tbl`'s count premise is necessary.
3. Without the counts (`dx = 2`), a quiescent arbiter need not be blocked in the `BlkX` sense
   (the idle state is quiescent).
-/
open Formal.Net Formal.Net.Ops Formal.Net.CapNet.Live.Nd5
open Formal.Cells.LinkHandshake (ctlB)
open Formal.Net.Ops.Link (ltbl LS)

-- 1
example : (⟨true, true, true, true, true, 2, 2⟩ : LS) ∈ ltbl := by decide
example : ∃ e ∈ CM.atbl, e.yr = true ∧ e.ya = true ∧ e.zr = true ∧ e.za = true := by decide

-- 2
example : ¬ ∀ e ∈ ltbl, e.c = ctlB e.ir e.oa e.c false → e.ia = e.c → e.orq = e.c →
    e.ir = true ∧ e.ia = false ∧ e.c = false ∧ e.orq = false ∧ e.oa = true := by decide

-- 3
example : ¬ ∀ e ∈ CM.atbl, QA e → BlkX e.xr e.xa e.yr e.ya e.g1 e.g2 e.zr e.za := by decide
