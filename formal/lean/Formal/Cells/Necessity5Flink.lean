import Formal.Cells.ConstraintsMore
open Formal.Core.LutList

/-!
# Necessity5Flink: `bd_flink.qfb_first` (H_QFB_FIRST_T) is tight to 1 tick

Probe Bnx5 (shard B). Row `bd_flink.qfb_first` was "sufficient", backed by
`ConstraintsMore.flink_qfb_first_timed` (request bit `uq = 8'hE2`,
transparent while `ck = 0`, clock `uck = 8'h06`, `ck = done xor ack`; Kleene
`Gate` windows on every pin; H_ACK_STABLE, H_QFB_FIRST_T, H_GAP, H_HOLD).
Its twin `bd_mlink.qfb_first` was labelled s+n_at_boundary from P3's
`qfb_counter`; flink had no counter-run.

`QClaim s` is `flink_qfb_first_timed` with H_QFB_FIRST_T weakened by `s`,
every other hypothesis verbatim. `q0 : QClaim 0` is the shipped theorem.
`q1_false : ¬ QClaim 1`.

* **Assumed (the run):** real INITs as fixed transport gates (one corner):
  `uq` reads `req` 1, `ck` 1, its own `done` 3 (slow feedback); `uck` reads
  `done` 1, `ack = 0`. `req` rises at 5 (token 0 -> 1). Gate equations for
  ALL `t` (`fDone_tr`, `fCk_tr`).
* **Proved:** every other hypothesis holds (`A = B = 0`, `Tq = 6`,
  `C = Tnew = 100`, `Td = 5`, `Toff2 = 7`, `Tnext = 9`; H_GAP `7 ≤ 7`,
  H_HOLD `8 ≤ 101`), H_QFB_FIRST_T reads `9 ≤ 8 + 1` (off by exactly 1),
  and `done` rises at 6 and falls back at 8 (a runt), then oscillates with
  period 3 (`f_runt`). Clean twin at `fhi = 2` (H_QFB_FIRST_T with
  equality): `done` makes one edge at 6 for all `t` (`f_clean`, non-vacuity).
* **Result:** necessary at the boundary (one parameter point), Lean `≤`
  form. The JSON form carries the strict +1 (Bs, Kleene X window); this
  binary run does not address that +1. Not an iff. NOPEN > 1 (uz path) not
  modelled.

Core Lean only.
-/

namespace Formal.Cells.Necessity5Flink
open Formal.Cells Formal.Cells.Bundling Formal.Cells.ConstraintsMore

/-- `flink_qfb_first_timed` with H_QFB_FIRST_T weakened by `s`. -/
def QClaim (s : Nat) : Prop :=
  ∀ (req ck done ack : Sig) (dlo dhi elo ehi flo fhi wlo whi alo ahi : Nat),
    Gate LibEndMemMlink.INIT_FQ [(req, dlo, dhi), (ck, elo, ehi), (done, flo, fhi)] done →
    Gate LibEndMemMlink.INIT_UCK [(done, wlo, whi), (ack, alo, ahi), (zero, 0, 0)] ck →
    dlo ≤ dhi → elo ≤ ehi → flo ≤ fhi → wlo ≤ whi → alo ≤ ahi → 1 ≤ flo →
    ∀ (v : Bool) (A Tq B C Td Tnew Toff2 Tnext : Nat),
    (∀ t, A ≤ t → t < Tq → done t = !v) →
    ((∀ t, B ≤ t → t < C → ack t = !v) ∧ Tq + wlo ≤ C + alo) →
    (∀ t, Td ≤ t → t < Tnew → req t = v) →
    (∀ t, Toff2 ≤ t → t < Tnext → ck t = true) →
    max (max (A + whi) (B + ahi) + ehi) (Td + dhi) + fhi ≤ Tq + wlo + elo + s →
    Tq + wlo ≤ Toff2 →
    Toff2 + ehi ≤ Tnew + dlo →
    ∀ t, max (max (A + whi) (B + ahi) + ehi) (Td + dhi) ≤ t → t < Tnext + elo → done t = v

theorem q0 : QClaim 0 := by
  intro req ck done ack dlo dhi elo ehi flo fhi wlo whi alo ahi hq hx hdw hew hfw hww haw hl
    v A Tq B C Td Tnew Toff2 Tnext h1 h2 h3 h4 h5 h6 h7
  exact flink_qfb_first_timed hq hx hdw hew hfw hww haw hl v A Tq B C Td Tnew Toff2 Tnext
    h1 h2 h3 h4 (by simpa using h5) h6 h7

theorem fq_bin (d c q : Bool) : lutB LibEndMemMlink.INIT_FQ [d, c, q] = (if c then q else d) := by
  cases d <;> cases c <;> cases q <;> decide
theorem uck_bin (d a : Bool) : lutB LibEndMemMlink.INIT_UCK [d, a, false] = (d != a) := by
  cases d <;> cases a <;> decide

/-! ## The run -/

def fReq : Sig := fun t => decide (5 ≤ t)
def fDone : Sig := fun t => if t < 6 then false else decide ((t - 6) % 3 ≠ 2)
def fCk : Sig := fun t => if t < 7 then false else fDone (t - 1)

theorem fDone_tr : Transport LibEndMemMlink.INIT_FQ [(fReq, 1), (fCk, 1), (fDone, 3)] fDone := by
  intro t
  show fDone t = lutB _ [fReq (t - 1), fCk (t - 1), fDone (t - 3)]
  rw [fq_bin]
  by_cases ht : t < 20
  · revert t; decide
  · have r1 : fReq (t - 1) = true := by simp [fReq]; omega
    have hk : (t - 6) % 3 = 0 ∨ (t - 6) % 3 = 1 ∨ (t - 6) % 3 = 2 := by omega
    have a1 : ¬ t < 6 := by omega
    have a2 : ¬ t - 1 < 7 := by omega
    have a3 : ¬ t - 1 - 1 < 6 := by omega
    have a4 : ¬ t - 3 < 6 := by omega
    simp only [fDone, fCk, a1, a2, a3, a4, ↓reduceIte, r1]
    rcases hk with h | h | h
    · have e1 : (t - 1 - 1 - 6) % 3 = 1 := by omega
      have e2 : (t - 3 - 6) % 3 = 0 := by omega
      simp [h, e1, e2]
    · have e1 : (t - 1 - 1 - 6) % 3 = 2 := by omega
      simp [h, e1]
    · have e1 : (t - 1 - 1 - 6) % 3 = 0 := by omega
      have e2 : (t - 3 - 6) % 3 = 2 := by omega
      simp [h, e1, e2]

theorem fCk_tr : Transport LibEndMemMlink.INIT_UCK [(fDone, 1), (zero, 0), (zero, 0)] fCk := by
  intro t
  show fCk t = lutB _ [fDone (t - 1), false, false]
  rw [uck_bin]
  by_cases ht : t < 7
  · have : fDone (t - 1) = false := by simp [fDone]; omega
    simp [fCk, ht, this]
  · simp [fCk, ht]

theorem gq : Gate LibEndMemMlink.INIT_FQ [(fReq, 1, 1), (fCk, 1, 1), (fDone, 3, 3)] fDone :=
  transport_gate _ [(fReq, 1, 1, 1), (fCk, 1, 1, 1), (fDone, 3, 3, 3)] fDone (by simp) fDone_tr

theorem gx : Gate LibEndMemMlink.INIT_UCK [(fDone, 1, 1), (zero, 0, 0), (zero, 0, 0)] fCk :=
  transport_gate _ [(fDone, 1, 1, 1), (zero, 0, 0, 0), (zero, 0, 0, 0)] fCk (by simp) fCk_tr

/-- H_QFB_FIRST_T on the run: `max (max (0+1) (0+0) + 1) (5+1) + 3 = 9 = 6 + 1 + 1 + 1`. -/
theorem q_viol : max (max (0 + 1) (0 + 0) + 1) (5 + 1) + 3 = 6 + 1 + 1 + 1 := by decide

/-- The runt: 1 at 6, 0 at 8, period 3 for ever. -/
theorem f_runt : fDone 5 = false ∧ fDone 6 = true ∧ fDone 8 = false ∧
    ∀ k, fDone (6 + 3 * k) = true ∧ fDone (8 + 3 * k) = false := by
  refine ⟨by decide, by decide, by decide, fun k => ⟨?_, ?_⟩⟩
  · have a : ¬ 6 + 3 * k < 6 := by omega
    simp [fDone, a]
  · have a : ¬ 8 + 3 * k < 6 := by omega
    have b : (8 + 3 * k - 6) % 3 = 2 := by omega
    simp [fDone, a, b]

theorem q1_false : ¬ QClaim 1 := by
  intro h
  have := h fReq fCk fDone zero 1 1 1 1 3 3 1 1 0 0 gq gx (by decide) (by decide) (by decide)
    (by decide) (by decide) (by decide) true 0 6 0 100 5 100 7 9
    (fun t _ h2 => by simp [fDone]; omega) ⟨fun _ _ _ => rfl, by decide⟩
    (fun t h1 _ => by simp [fReq]; omega)
    (fun t h1 h2 => by
      have : t = 7 ∨ t = 8 := by omega
      rcases this with rfl | rfl <;> decide)
    (by decide) (by decide) (by decide) 8 (by decide) (by decide)
  rw [f_runt.2.2.1] at this; exact absurd this (by decide)

/-! ## Clean twin: `fhi = 2` (H_QFB_FIRST_T with equality) -/

def gDone : Sig := fun t => decide (6 ≤ t)
def gCk : Sig := fun t => decide (7 ≤ t)

theorem f_clean :
    Gate LibEndMemMlink.INIT_FQ [(fReq, 1, 1), (gCk, 1, 1), (gDone, 2, 2)] gDone ∧
    Gate LibEndMemMlink.INIT_UCK [(gDone, 1, 1), (zero, 0, 0), (zero, 0, 0)] gCk ∧
    max (max (0 + 1) (0 + 0) + 1) (5 + 1) + 2 ≤ 6 + 1 + 1 ∧ ∀ t, gDone t = decide (6 ≤ t) := by
  refine ⟨transport_gate _ [(fReq, 1, 1, 1), (gCk, 1, 1, 1), (gDone, 2, 2, 2)] gDone (by simp) ?_,
    transport_gate _ [(gDone, 1, 1, 1), (zero, 0, 0, 0), (zero, 0, 0, 0)] gCk (by simp) ?_,
    by decide, fun _ => rfl⟩
  · intro t
    show gDone t = lutB _ [fReq (t - 1), gCk (t - 1), gDone (t - 2)]
    rw [fq_bin]
    by_cases ht : t < 20
    · revert t; decide
    · have e1 : gCk (t - 1) = true := by simp [gCk]; omega
      have e2 : gDone (t - 2) = true := by simp [gDone]; omega
      have e3 : gDone t = true := by simp [gDone]; omega
      rw [e1, e2, e3]; rfl
  · intro t
    show gCk t = lutB _ [gDone (t - 1), false, false]
    rw [uck_bin]
    simp only [gCk, gDone]
    by_cases h : 7 ≤ t
    · have : 6 ≤ t - 1 := by omega
      simp [h, this]
    · have : ¬ 6 ≤ t - 1 := by omega
      simp [h, this]

end Formal.Cells.Necessity5Flink
