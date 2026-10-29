import Formal.Core.XAudit.Events7Excl
import Formal.Cells.LibGapSteer

namespace Formal.Core.XAudit.Events8Bridge

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp Mono)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events7

theorem warp_lo_le_hi' {lo hi : Nat} {f : Nat → Nat} (w : Warp lo hi f) : lo ≤ hi := by
  have a := w.le_late (lo + hi); have b := w.early_le (lo + hi); omega

/-- A (ℕ-time, truncated-at-0) warp as one of B's ℤ-time read maps `LibGapSteer.Rd`:
before `lo` the pin reads the driver at a negative time (where the driver is extended
by its time-0 value), from `lo` on it reads at the warp. -/
def rdOf {lo hi : Nat} {f : Nat → Nat} (w : Warp lo hi f) : Formal.Cells.LibGapSteer.Rd where
  σ := fun t => if t < (lo : Int) then t - lo else (f t.toNat : Int)
  lo := lo
  hi := hi
  ge := fun t => by
    have hlh := warp_lo_le_hi' w
    by_cases h : t < (lo : Int)
    · rw [if_pos h]; omega
    · rw [if_neg h]
      have := w.early_le t.toNat; omega
  le := fun t => by
    by_cases h : t < (lo : Int)
    · rw [if_pos h]; omega
    · rw [if_neg h]
      have := w.le_late t.toNat; omega

/-- The ℤ-time extension of a trace: its time-0 value before 0. -/
def extZ (x : Sig) : Int → Bool := fun t => x t.toNat

theorem rdOf_read {lo hi : Nat} {f : Nat → Nat} (w : Warp lo hi f) (x : Sig) (s : Nat) :
    extZ x ((rdOf w).σ s) = x (f s) := by
  unfold extZ rdOf
  by_cases h : (s : Int) < (lo : Int)
  · rw [if_pos h]
    have h1 : f s = 0 := by have := w.le_late s; omega
    rw [h1]; congr 1; omega
  · rw [if_neg h]; congr 1

/-- **One select read, from B's steer theorem.** The request source's count `M`
(0 at time 0) is `2k+1` only inside `[R k, F k)`; the select driver `xs` shows `v k`
on `[S0 k, S1 k)` (B's H_S_STABLE); the request is read through a warp in
`[Rlo, Rhi]` and the select through one in `[Slo, Shi]`, both at the same sample
time; and B's per-pin H_SETUP_PIN / H_HOLD_PIN hold for every transaction. Then
whenever the request read shows transaction `k`, the select read shows `v k`.
The proof is `LibGapSteer.steer_pin_ok` (branch `true`) on the ℤ embedding. -/
theorem sel_read_of_steer {Rlo Rhi Slo Shi : Nat} {gR gS : Nat → Nat}
    (wR : Warp Rlo Rhi gR) (wS : Warp Slo Shi gS) (M : Nat → Nat) (hM0 : M 0 = 0)
    (xs : Sig) (v : Nat → Bool) (R F S0 S1 : Nat → Nat)
    (hwin : ∀ u k, M u = 2 * k + 1 → R k ≤ u ∧ u < F k)
    (hstab : ∀ k t, S0 k ≤ t → t < S1 k → xs t = v k)
    (hsetup : ∀ k, S0 k + Shi ≤ R k + Rlo) (hhold : ∀ k, F k + Rhi ≤ S1 k + Slo) :
    ∀ s k, M (gR s) = 2 * k + 1 → xs (gS s) = v k := by
  intro s k hm
  have hspec := Formal.Cells.LibGapSteer.steer_pin_ok true (v k) (rdOf wR) (rdOf wS)
    (R k) (F k) (S0 k) (S1 k) (extZ xs)
    (fun t h1 h2 => by unfold extZ; exact hstab k t.toNat (by omega) (by omega))
    (by show ((S0 k : Nat) : Int) + Shi ≤ (R k : Int) + Rlo; have := hsetup k; omega)
    (by show ((F k : Nat) : Int) + Rhi ≤ (S1 k : Int) + Slo; have := hhold k; omega) (s : Int)
  have hlo : Rlo ≤ s := by
    rcases Nat.lt_or_ge s Rlo with hc | hc
    · have : gR s = 0 := by have := wR.le_late s; omega
      rw [this, hM0] at hm; omega
    · exact hc
  have hσ : (rdOf wR).σ s = (gR s : Int) := by
    unfold rdOf; simp only; rw [if_neg (by omega)]; rfl
  have hw := hwin (gR s) k hm
  have hp : Formal.Cells.LibGapSteer.pulse (R k) (F k) ((rdOf wR).σ s) = true := by
    rw [hσ]; unfold Formal.Cells.LibGapSteer.pulse; simp only [decide_eq_true_eq]; omega
  rw [hp, Formal.Cells.LibGapSteer.outB_eq, rdOf_read] at hspec
  cases h1 : xs (gS s) <;> cases h2 : v k <;> simp_all

/-- **SelOK from B's steer conditions** (multi-bit select). For every filtered pin
`(j, p)`, the select it sees is a function `φ j p` of `nb j p` select bits, bit `q`
being the driver `xs j p q` read through its own warp `gS j p q` in
`[Slo j p q, Shi j p q]`; transaction `k` of the pin's source lies in `[R j p k, F j p k)`;
bit `q` is stable at `vb j p q k` on `[S0 j p q k, S1 j p q k)`, with B's setup / hold
against every copy's band; and `sel` is `φ` of the stable bits. Then `SelOK`. -/
theorem selOK_of_steer {N : Nat} {net : Net4 N} {b : Bands4 net} {sel : Nat → Nat → Bool}
    (bh : Beh7 net b sel)
    (nb : (j : Fin N) → Fin (net.ar j) → Nat)
    (φ : (j : Fin N) → (p : Fin (net.ar j)) → (Fin (nb j p) → Bool) → Bool)
    (xs : (j : Fin N) → (p : Fin (net.ar j)) → Fin (nb j p) → Sig)
    (gS : (j : Fin N) → (p : Fin (net.ar j)) → Fin (nb j p) → Nat → Nat)
    (Slo Shi : (j : Fin N) → (p : Fin (net.ar j)) → Fin (nb j p) → Nat)
    (wS : ∀ j p q, Warp (Slo j p q) (Shi j p q) (gS j p q))
    (hsv : ∀ j p s, net.pk j p = PK.filt → bh.sv j p s = φ j p (fun q => xs j p q (gS j p q s)))
    (R F : (j : Fin N) → Fin (net.ar j) → Nat → Nat)
    (S0 S1 : (j : Fin N) → (p : Fin (net.ar j)) → Fin (nb j p) → Nat → Nat)
    (vb : (j : Fin N) → (p : Fin (net.ar j)) → Fin (nb j p) → Nat → Bool)
    (hwin : ∀ j p u k, net.pk j p = PK.filt → bh.M u (net.src j p) = 2 * k + 1 →
      R j p k ≤ u ∧ u < F j p k)
    (hstab : ∀ j p q k t, net.pk j p = PK.filt → S0 j p q k ≤ t → t < S1 j p q k →
      xs j p q t = vb j p q k)
    (hsetup : ∀ j p q (i : Fin (net.nc j p)) k, net.pk j p = PK.filt →
      S0 j p q k + Shi j p q ≤ R j p k + b.loC j p i)
    (hhold : ∀ j p q (i : Fin (net.nc j p)) k, net.pk j p = PK.filt →
      F j p k + b.hiC j p i ≤ S1 j p q k + Slo j p q)
    (hsel : ∀ j p k, net.pk j p = PK.filt → sel (net.grp j p) k = φ j p (fun q => vb j p q k)) :
    bh.SelOK := by
  intro j p s i hk hodd
  have hk2 : bh.M (bh.G j p i s) (net.src j p) = 2 * (bh.M (bh.G j p i s) (net.src j p) / 2) + 1 := by
    omega
  rw [hsv j p s hk, hsel j p _ hk]
  congr 1
  funext q
  exact sel_read_of_steer (bh.wG j p i) (wS j p q) (fun u => bh.M u (net.src j p))
    (bh.M_zero _) (xs j p q) (vb j p q) (R j p) (F j p) (S0 j p q) (S1 j p q)
    (fun u k h => hwin j p u k hk h) (fun k t h1 h2 => hstab j p q k t hk h1 h2)
    (fun k => hsetup j p q i k hk) (fun k => hhold j p q i k hk) s _ hk2

/-! ## SelPart by construction -/

/-- **SelPart from one select value per partition.** If every group of a partition is
the indicator of its own pattern of ONE value sequence `val P` (distinct patterns within
a partition), then `SelPart` holds. -/
theorem selPart_of_value (sel : Nat → Nat → Bool) (parts : List (List Nat))
    (pat : Nat → Nat) (val : List Nat → Nat → Nat)
    (hinj : ∀ P ∈ parts, ∀ g1 ∈ P, ∀ g2 ∈ P, g1 ≠ g2 → pat g1 ≠ pat g2)
    (hsel : ∀ P ∈ parts, ∀ g ∈ P, ∀ k, sel g k = decide (pat g = val P k)) :
    Formal.Core.XAudit.Events7.SelPart sel parts := by
  intro P hP g1 h1 g2 h2 hne k ⟨a, c⟩
  rw [hsel P hP g1 h1, decide_eq_true_eq] at a
  rw [hsel P hP g2 h2, decide_eq_true_eq] at c
  exact hinj P hP g1 h1 g2 h2 hne (by rw [a, c])

end Formal.Core.XAudit.Events8Bridge
