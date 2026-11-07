import Formal.Core.XAudit.Events2

/-!
# Formal.Core.XAudit.Events2Time — period bounds for any net, from kernel-checked certificates (E3)

Probe A-events2. Everything here holds for EVERY behaviour of ANY `CNet`
(closed, or open with the environment as channels), with no hypothesis on
the net's shape; the shape enters only through small decidable
certificates that an untrusted tool computes and `decide` checks.

* `cycle_le` (per-window upper bound): a closed walk `w` from `j` to `j`
  carrying `K` tokens with fastest traversal `L` gives
  `M (t + L) j ≤ M t j + K` for all `t`: at most `K` firings of `j` in any
  window of `L` steps. With the critical cycle this is the minimum period.
* `rate_upper` (potential certificate, upper): integers `T', K'` and
  potentials `ρ` with a chosen pin `σ j` per stage such that
  `ρ (src j σ) + T'·off ≤ ρ j + K'·(loF j + loG j σ)` on every chosen arc
  give `T'·M t j ≤ K'·t + ρ j + T'`: long-run rate at most `K'/T'`. Such a
  certificate exists iff `T'/K' ≤` the minimum over cycles of the chosen
  arcs of `lo(C)/tok(C)`.
* `rate_lower` (potential certificate, lower; liveness): `T, K, π` with
  `π (src j p) + K·(hiF j + hiG j p) ≤ π j + T·off j p` on EVERY arc, and
  reset released at `R`, give `K·t ≤ T·M t j + π j + K·(R + D)`: long-run
  rate at least `K/T`. Such a certificate exists iff `T/K ≥` the maximum
  cycle ratio `hi(C)/tok(C)` of the counter graph (Bellman–Ford), so the
  bound is the max-cycle-ratio period, as a checked certificate.
* `ge_pins`: the one-step lower bound behind `rate_lower`.
-/

namespace Formal.Core.XAudit.Events2

open Formal.Core.TraceDiscrete (Sig Warp)

theorem warp_lo_le_hi {lo hi : Nat} {f : Nat → Nat} (w : Warp lo hi f) : lo ≤ hi := by
  have := w.le_late (lo + hi); have := w.early_le (lo + hi); omega

namespace Beh
variable {N : Nat} {net : CNet N} {b : Bands net} (x : Beh net b)

/-- **Cycle bound.** -/
theorem cycle_le (w : List (Arc net)) (j : Fin N) (hw : walkOK net j j w = true) (t : Nat) :
    x.M (t + wLo b w) j ≤ x.M t j + wTok net w := by
  have := x.walk_le w j j hw (t + wLo b w)
  rwa [Nat.add_sub_cancel] at this

theorem cycle_le_iter (w : List (Arc net)) (j : Fin N) (hw : walkOK net j j w = true) (t : Nat) :
    ∀ k, x.M (t + k * wLo b w) j ≤ x.M t j + k * wTok net w
  | 0 => by simp
  | k + 1 => by
      have h1 := x.cycle_le w j hw (t + k * wLo b w)
      have h2 := cycle_le_iter w j hw t k
      rw [show t + (k + 1) * wLo b w = t + k * wLo b w + wLo b w by rw [Nat.succ_mul]; omega,
        Nat.succ_mul]
      omega

/-- Potential certificate for the upper rate. -/
def UpCert (b : Bands net) (σ : (j : Fin N) → Fin (net.ar j)) (T' K' : Nat) (ρ : Fin N → Nat) :
    Prop :=
  ∀ j, ρ (net.src j (σ j)) + T' * net.off j (σ j) ≤ ρ j + K' * (b.loF j + b.loG j (σ j))

/-- **Upper rate bound** from a potential certificate. -/
theorem rate_upper {σ : (j : Fin N) → Fin (net.ar j)} {T' K' : Nat} {ρ : Fin N → Nat}
    (hc : UpCert b σ T' K' ρ) : ∀ t j, T' * x.M t j ≤ K' * t + ρ j + T' := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro j
    have h1 := x.M_le_pin j (σ j) t
    have a1 := (x.wF j).le_late t
    have a2 := (x.wG j (σ j)).le_late (x.F j t)
    have hoff := net.off_le j (σ j)
    by_cases ht : b.loF j + b.loG j (σ j) ≤ t
    · have hlt : t - (b.loF j + b.loG j (σ j)) < t := by
        have := x.loF1 j; omega
      have hi := ih _ hlt (net.src j (σ j))
      have hm := x.M_mono (t - (b.loF j + b.loG j (σ j))) (net.src j (σ j))
        (x.G j (σ j) (x.F j t)) (by omega)
      have hcj := hc j
      have e1 : T' * x.M t j ≤ T' * x.M (t - (b.loF j + b.loG j (σ j))) (net.src j (σ j))
          + T' * net.off j (σ j) := by
        rw [← Nat.mul_add]; exact Nat.mul_le_mul_left _ (by omega)
      have e2 : K' * (t - (b.loF j + b.loG j (σ j))) + K' * (b.loF j + b.loG j (σ j)) = K' * t := by
        rw [← Nat.mul_add]; congr 1; omega
      omega
    · have h0 : x.G j (σ j) (x.F j t) = 0 := by omega
      rw [h0, x.M_zero] at h1
      have : T' * x.M t j ≤ T' * 1 := Nat.mul_le_mul_left _ (by omega)
      omega

/-- Potential certificate for the lower rate (liveness). -/
def LoCert (b : Bands net) (T K : Nat) (π : Fin N → Nat) : Prop :=
  ∀ j p, π (net.src j p) + K * (b.hiF j + b.hiG j p) ≤ π j + T * net.off j p

instance (b : Bands net) (T K : Nat) (π : Fin N → Nat) : Decidable (LoCert b T K π) := by
  unfold LoCert; exact inferInstance

/-- One step of the min-plus lower bound: once the reset pin of `j` is low at
its LUT sample, `j` has caught up with every pin read `hiF + hiG` earlier. -/
theorem ge_pins (j : Fin N) (t : Nat) (hr : x.r j (x.F j t) = false) :
    ∃ p, x.M (t - (b.hiF j + b.hiG j p)) (net.src j p) + net.off j p ≤ x.M t j := by
  rw [x.M_eq]
  unfold E
  simp only [hr, Bool.false_eq_true, ite_false]
  obtain ⟨p, hp⟩ := fmin_mem _ (fun p => x.P j p (x.F j t)) (net.ar_pos j)
  refine ⟨p, ?_⟩
  rw [hp]; unfold P
  have a1 := (x.wF j).early_le t
  have a2 := (x.wG j p).early_le (x.F j t)
  have := x.M_mono (x.G j p (x.F j t)) (net.src j p) (t - (b.hiF j + b.hiG j p)) (by omega)
  omega

/-- **Lower rate bound (liveness)** from a potential certificate: once every
reset pin is low from `R`, with `D` bounding every `hiF + hiG`. -/
theorem rate_lower {T K R D : Nat} {π : Fin N → Nat} (hc : LoCert b T K π)
    (hD : ∀ j p, b.hiF j + b.hiG j p ≤ D) (hR : ∀ j s, R ≤ s → x.r j s = false) :
    ∀ t j, K * t ≤ T * x.M t j + π j + K * (R + D) := by
  intro t
  induction t using Nat.strongRecOn with
  | ind t ih =>
    intro j
    by_cases ht : R + D ≤ t
    · have hr : x.r j (x.F j t) = false := by
        apply hR
        have := (x.wF j).early_le t
        have := (x.wG j ⟨0, net.ar_pos j⟩).le_late 0
        have := hD j ⟨0, net.ar_pos j⟩
        omega
      obtain ⟨p, hp⟩ := x.ge_pins j t hr
      have hDp := hD j p
      have hlo := (x.loG1 j p)
      have hlt : t - (b.hiF j + b.hiG j p) < t := by
        have := warp_lo_le_hi (x.wF j); have := x.loF1 j; omega
      have hi := ih _ hlt (net.src j p)
      have hcj := hc j p
      have e1 : T * (x.M (t - (b.hiF j + b.hiG j p)) (net.src j p) + net.off j p) ≤ T * x.M t j :=
        Nat.mul_le_mul_left _ hp
      rw [Nat.mul_add] at e1
      have e2 : K * (t - (b.hiF j + b.hiG j p)) + K * (b.hiF j + b.hiG j p) = K * t := by
        rw [← Nat.mul_add]; congr 1; omega
      omega
    · have : K * t ≤ K * (R + D) := Nat.mul_le_mul_left _ (by omega)
      omega

/-- **The lower certificate is the max cycle ratio** (it cannot be beaten):
along any walk the potentials telescope, so a closed walk with `tok` tokens
and slowest traversal `hi` forces `K·hi ≤ T·tok`. -/
theorem LoCert.walk {T K : Nat} {π : Fin N → Nat} (hc : LoCert b T K π) :
    ∀ (w : List (Arc net)) (a c : Fin N), walkOK net a c w = true →
      π c + K * wHi b w ≤ π a + T * wTok net w
  | [], a, c, h => by
      simp only [walkOK, beq_iff_eq] at h; subst h; simp [wHi, wTok]
  | ⟨k, p⟩ :: w, a, c, h => by
      simp only [walkOK, Bool.and_eq_true, beq_iff_eq] at h
      obtain ⟨hk, hw⟩ := h
      subst hk
      have h1 := LoCert.walk hc w _ c hw
      have h2 := hc k p
      simp only [wHi, wTok, Nat.mul_add] at h1 h2 ⊢
      omega

theorem LoCert.cycle {T K : Nat} {π : Fin N → Nat} (hc : LoCert b T K π) (w : List (Arc net))
    (j : Fin N) (hw : walkOK net j j w = true) : K * wHi b w ≤ T * wTok net w := by
  have := LoCert.walk hc w j j hw; omega

end Beh

end Formal.Core.XAudit.Events2
