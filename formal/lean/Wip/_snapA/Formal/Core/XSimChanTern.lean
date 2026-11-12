import Formal.Core.XSimChanReal
import Formal.Core.TernaryChannels

/-!
# Formal.Core.XSimChanTern — the timed (XSim) and untimed (ternary) channel classes agree

Probe XSound2 (shard A). See `formal/notes/A-xsound2.md`.

`XSimChanReal.PhysChan q lo hi` (the gate channels for which `xaudit`'s timed
verdicts are proved sound in continuous time) are inside
`TernaryChannels.NodeChan (lo q) (hi q)` (the channels for which the untimed
Eichelberger analysis is sound, `TernaryChannels.rcausal_of_nodeChan`), and
read the past by at least `lo q ≥ q > 0`: the positive lower delay that
`TernaryChannels.zero_delay_chan_unsound`/`zero_delay_inertial_unsound` show
to be necessary. The converse inclusion fails: `NodeChan` puts no bound on an
inertial rejection window, `PhysChan` must (`XSimChanReal.inertial_wide_not_chanCells`).
-/

namespace Formal.Core.XSimChanTern

open Formal.Core.XSimChanReal

/-- `PhysChan` channels are `TernaryChannels.NodeChan` channels. -/
theorem physChan_nodeChan {q : ℝ} {lo hi : ℕ} {e o : ℝ → Bool} (h : PhysChan q lo hi e o) :
    TernaryChannels.NodeChan ((lo : ℝ) * q) ((hi : ℝ) * q) e o := by
  rcases h with ⟨L, H, h1, h2, h⟩ | ⟨ρ, L, H, h1, h2, _, h⟩
  · exact Or.inl ⟨L, H, h1, h2, h⟩
  · exact Or.inr ⟨ρ, L, H, h1, h2, h⟩

/-- They read the past by at least `lo q` (positive when `1 ≤ lo`, `0 < q`). -/
theorem physChan_readsPast {q : ℝ} {lo hi : ℕ} {e o : ℝ → Bool} (h : PhysChan q lo hi e o) :
    TernaryChannels.ReadsPast ((lo : ℝ) * q) e o :=
  TernaryChannels.nodeChan_readsPast (physChan_nodeChan h)

end Formal.Core.XSimChanTern
