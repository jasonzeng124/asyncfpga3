import Formal.Net.HandshakeMuller

/-!
# Probe C-8h, part 1: the Muller pipeline with per-link margins

8a's `muller_pipeline` takes ONE `(m, h)` for every link. That is sound, but
it couples unrelated links: with a single `m`, the source-setup race has to be
as slow as the slowest internal data wire (8e's finding). Here every link `j`
has its own setup margin `m j` and hold margin `h j`:

* `H_SRC_SETUP_HOLD : SetupHold (m 0) (h 0) (ch 0)`;
* for every internal link `j+1`: `Sep (m (j+1)) (ch j) (ch (j+1))` and
  `Hold (h (j+1)) (ch j) (ch (j+1))`;
* stage `j` is a `MullerStage (m j) (h j)`: its latch contract is used with
  the margins of ITS input link.

`muller_pipeline2` has the same conclusion as `muller_pipeline` (protocol on
every link, FIFO, counts). `muller_pipeline` is the special case of constant
`m`, `h` (`muller_pipeline_of_2`).

8a's `Pipeline`/`StageSpec` fix `(m, h)` for all stages, so the protocol part
is re-proved here (`pipeline_protocol2`, the same strong induction on time);
8a's files are not edited.
-/

namespace Formal.Net.Handshake
open Formal.Net

/-- The protocol half of a stage spec: no margins involved. -/
structure StageCtl (i o : Chan) : Prop where
  ag : ∀ t, (∀ s, s < t → Rules i s ∧ Rules o s) → RecvStep i t ∧ SendStep o t
  initIn : i.ack 0 = false
  initOut : o.req 0 = false

theorem StageSpec.ctl {m h : Nat} {i o : Chan} (S : StageSpec m h i o) : StageCtl i o :=
  ⟨S.ag, S.initIn, S.initOut⟩

/-- Every link obeys the protocol when every stage obeys its control spec
(stages may have different data margins; they play no role here). -/
theorem pipeline_protocol2 {n : Nat} {ch : Nat → Chan}
    (stage : ∀ j, j < n → StageCtl (ch j) (ch (j + 1)))
    (srcInit : (ch 0).req 0 = false) (snkInit : (ch n).ack 0 = false)
    (src : ∀ t, (∀ s, s < t → Rules (ch 0) s) → SendStep (ch 0) t)
    (snk : ∀ t, (∀ s, s < t → Rules (ch n) s) → RecvStep (ch n) t) :
    ∀ j, j ≤ n → Protocol (ch j) := by
  have step : ∀ t, ∀ j, j ≤ n → SendStep (ch j) t ∧ RecvStep (ch j) t := by
    intro t
    induction t using Nat.strongRecOn with
    | _ t ih =>
      intro j hj
      constructor
      · cases j with
        | zero => exact src t (fun s hs => ih s hs 0 (Nat.zero_le _))
        | succ j =>
          exact ((stage j (by omega)).ag t (fun s hs =>
            ⟨ih s hs j (by omega), ih s hs (j+1) hj⟩)).2
      · by_cases hjn : j = n
        · subst hjn; exact snk t (fun s hs => ih s hs j (Nat.le_refl _))
        · exact ((stage j (by omega)).ag t (fun s hs =>
            ⟨ih s hs j hj, ih s hs (j+1) (by omega)⟩)).1
  intro j hj
  refine ⟨⟨?_, ?_⟩, fun t => step t j hj⟩
  · cases j with
    | zero => exact srcInit
    | succ j => exact (stage j (by omega)).initOut
  · by_cases hjn : j = n
    · subst hjn; exact snkInit
    · exact (stage j (by omega)).initIn

/-- Chaining per-stage transfers. -/
theorem chain_transfers {n : Nat} {ch : Nat → Chan}
    (hst : ∀ j, j < n → Transfers (ch j) (ch (j + 1))) (hn : 0 < n) :
    Transfers (ch 0) (ch n) := by
  have : ∀ j, j < n → Transfers (ch 0) (ch (j + 1)) := by
    intro j
    induction j with
    | zero => intro h0; exact hst 0 h0
    | succ j ih => intro hj; exact transfers_trans (ih (by omega)) (hst (j+1) hj)
  have h := this (n - 1) (by omega)
  rwa [show n - 1 + 1 = n by omega] at h

/-- **Muller pipeline, per-link margins.** As `muller_pipeline`, but link `j`
has its own setup margin `m j` and hold margin `h j`; stage `j` uses the
margins of its input link `j`. -/
theorem muller_pipeline2 {m h : Nat → Nat} {n : Nat} {ch : Nat → Chan}
    (H_STAGE : ∀ j, j < n → MullerStage (m j) (h j) (ch j) (ch (j + 1)))
    (srcInit : (ch 0).req 0 = false) (snkInit : (ch n).ack 0 = false)
    (src : ∀ t, (∀ s, s < t → Rules (ch 0) s) → SendStep (ch 0) t)
    (snk : ∀ t, (∀ s, s < t → Rules (ch n) s) → RecvStep (ch n) t)
    (H_SRC_SETUP_HOLD : SetupHold (m 0) (h 0) (ch 0))
    (H_SEP : ∀ j, j + 1 < n → Sep (m (j + 1)) (ch j) (ch (j + 1)))
    (H_HOLD : ∀ j, j + 1 < n → Hold (h (j + 1)) (ch j) (ch (j + 1)))
    (hn : 0 < n) :
    (∀ j, j ≤ n → Protocol (ch j)) ∧
    (∀ t, cnt (fallB (ch n).ack) t ≤ cnt (fallB (ch 0).ack) t) ∧
    (∀ k e', TokAt (ch n) k e' → ∃ e, e < e' ∧ TokAt (ch 0) k e ∧ (ch n).dat e' = (ch 0).dat e) := by
  have hp := pipeline_protocol2 (fun j hj => (muller_stageSpec (H_STAGE j hj)).ctl)
    srcInit snkInit src snk
  have hsh : ∀ j, j < n → SetupHold (m j) (h j) (ch j) := by
    intro j
    induction j with
    | zero => intro _; exact H_SRC_SETUP_HOLD
    | succ j ih =>
      intro hj
      exact muller_out_setupHold (H_STAGE j (by omega)) (hp (j+1) (by omega))
        (ih (by omega)) (H_SEP j hj) (H_HOLD j hj)
  have T : Transfers (ch 0) (ch n) := chain_transfers (fun j hj =>
    (muller_stageSpec (H_STAGE j hj)).xfer (hp j (by omega)) (hp (j+1) hj) (hsh j hj)) hn
  exact ⟨hp, transfers_count T, T⟩

/-- 8a's global-margin theorem is the constant case. -/
theorem muller_pipeline_of_2 {m h n : Nat} {ch : Nat → Chan}
    (H_STAGE : ∀ j, j < n → MullerStage m h (ch j) (ch (j + 1)))
    (srcInit : (ch 0).req 0 = false) (snkInit : (ch n).ack 0 = false)
    (src : ∀ t, (∀ s, s < t → Rules (ch 0) s) → SendStep (ch 0) t)
    (snk : ∀ t, (∀ s, s < t → Rules (ch n) s) → RecvStep (ch n) t)
    (H_SRC_SETUP_HOLD : SetupHold m h (ch 0))
    (H_SEP : ∀ j, j + 1 < n → Sep m (ch j) (ch (j + 1)))
    (H_HOLD : ∀ j, j + 1 < n → Hold h (ch j) (ch (j + 1)))
    (hn : 0 < n) :
    (∀ j, j ≤ n → Protocol (ch j)) ∧
    (∀ t, cnt (fallB (ch n).ack) t ≤ cnt (fallB (ch 0).ack) t) ∧
    (∀ k e', TokAt (ch n) k e' → ∃ e, e < e' ∧ TokAt (ch 0) k e ∧ (ch n).dat e' = (ch 0).dat e) :=
  muller_pipeline2 (m := fun _ => m) (h := fun _ => h) H_STAGE srcInit snkInit src snk
    H_SRC_SETUP_HOLD H_SEP H_HOLD hn

end Formal.Net.Handshake
