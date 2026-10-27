import Formal.Core.XAudit.Events

/-!
# Formal.Core.XAudit.EventsRing — ring3 in the counter domain: no hazard, ever, and cycle-time bounds

Probe A-events. The tb_ring control ring, N = 3, K = 1 (`cells/tb/tb_ring.v`,
`formal/tools-A/xaudit/mkdesign.py ring3`): `c_i = C(c_{i-1}, ¬c_{i+1})`,
stage 0 is `bd_c2n_set` (reset value 1), stages 1 and 2 are `bd_c2n`.

For ANY delay bands (parameters `d ≤ loF + loG`, `hiF + hiG ≤ D` per pin) and
every behaviour:

* `ring_inv`: at every time `M 2 ≤ M 0 ≤ M 1 ≤ M 2 + 1` — the firings are
  strictly sequential, c1, c0, c2, c1, ... (`state_of_hops`: the whole state
  is a function of the hop count `H = M 0 + M 1 + M 2`).
* `hops_upper`: `H (t + k·d) ≤ H t + k` — at most one hop per `d` steps.
* `hops_lower`: once every reset pin has fallen (time `R`),
  `H t + k ≤ H (t + k·D)` — at least one hop per `D` steps.
* `node_period`: each node toggles at least once in every window of `3·D`
  steps after `R`, and at most once in every window of `3·d` steps; so the
  node period (two toggles) lies in `[6·d, 6·D]`.
* `ring3_safe`: with `Race` (feedback no slower than a neighbour round trip)
  every node equals its reset value flipped by that count, so the waveform
  of every node is fixed by `H` at every time: no X, no glitch, forever.

None of these windows grows with the number of laps: the per-hop bound is
`[d, D]` for every hop. The absolute time of hop `n` is uncertain by
`n·(D - d)` (the delays of different laps are independent), and this is
real, not a loss of the abstraction.
-/

namespace Formal.Core.XAudit.Events.Ring3

open Formal.Core.XAudit.Events

/-- ring3: pin `a` (false) reads `c_{i-1}`, pin `b` (true) reads `c_{i+1}`;
stage 0 resets to 1. -/
def net : MNet 3 where
  v := fun j => decide (j.val = 0)
  src := fun j p => if p then j + 1 else j - 1

theorem pairing : net.Pairing := by decide

section
variable {b : Bands 3} (x : Beh net b)

/-- Hop count: total number of firings. -/
def H (t : Nat) : Nat := x.M t 0 + x.M t 1 + x.M t 2

/-- One step of the min-plus upper bound through a pin, with a uniform lower
delay `d` per (LUT + route). -/
theorem le_through {d : Nat} (hd : ∀ j p, d ≤ b.loF j + b.loG j p) (j : Fin 3) (p : Bool)
    (t : Nat) : x.M t j ≤ x.M (t - d) (net.src j p) + net.off j p := by
  have h1 := x.M_le_pin j p t
  have a1 := (x.wF j).le_late t
  have a2 := (x.wG j p).le_late (x.F j t)
  have := x.M_mono (t - d) (net.src j p) (x.G j p (x.F j t)) (by have := hd j p; omega)
  omega

/-- Strict sequencing: `M 2 ≤ M 0 ≤ M 1 ≤ M 2 + 1` at every time. -/
theorem ring_inv (t : Nat) : x.M t 2 ≤ x.M t 0 ∧ x.M t 0 ≤ x.M t 1 ∧ x.M t 1 ≤ x.M t 2 + 1 := by
  have e1 := le_through x (d := 0) (fun _ _ => Nat.zero_le _) 2 true t
  have e2 := le_through x (d := 0) (fun _ _ => Nat.zero_le _) 0 true t
  have e3 := le_through x (d := 0) (fun _ _ => Nat.zero_le _) 1 true t
  simp only [Nat.sub_zero] at e1 e2 e3
  have s1 : net.src 2 true = 0 := by decide
  have s2 : net.src 0 true = 1 := by decide
  have s3 : net.src 1 true = 2 := by decide
  have o1 : net.off 2 true = 0 := by decide
  have o2 : net.off 0 true = 0 := by decide
  have o3 : net.off 1 true = 1 := by decide
  rw [s1, o1] at e1; rw [s2, o2] at e2; rw [s3, o3] at e3
  exact ⟨by omega, by omega, by omega⟩

/-- The whole ring state is a function of the hop count. -/
theorem state_of_hops (t : Nat) :
    x.M t 1 = (H x t + 2) / 3 ∧ x.M t 0 = (H x t + 1) / 3 ∧ x.M t 2 = H x t / 3 := by
  have := ring_inv x t; unfold H; omega

theorem H_zero : H x 0 = 0 := by
  unfold H; simp only [x.M_eq, x.F_zero, x.E_zero]

theorem H_mono (a t : Nat) (h : a ≤ t) : H x a ≤ H x t := by
  unfold H
  have := x.M_mono t 0 a h; have := x.M_mono t 1 a h; have := x.M_mono t 2 a h
  omega

/-- **At most one hop per `d` steps.** -/
theorem hop_upper {d : Nat} (hd : ∀ j p, d ≤ b.loF j + b.loG j p) (t : Nat) :
    H x (t + d) ≤ H x t + 1 := by
  have i := ring_inv x t
  have f1 := le_through x hd 1 false (t + d)
  have f2 := le_through x hd 1 true (t + d)
  have f3 := le_through x hd 0 false (t + d)
  have f4 := le_through x hd 0 true (t + d)
  have f5 := le_through x hd 2 false (t + d)
  have f6 := le_through x hd 2 true (t + d)
  simp only [Nat.add_sub_cancel] at f1 f2 f3 f4 f5 f6
  have : net.src 1 false = 0 := by decide
  rw [this] at f1
  have : net.src 1 true = 2 := by decide
  rw [this] at f2
  have : net.src 0 false = 2 := by decide
  rw [this] at f3
  have : net.src 0 true = 1 := by decide
  rw [this] at f4
  have : net.src 2 false = 1 := by decide
  rw [this] at f5
  have : net.src 2 true = 0 := by decide
  rw [this] at f6
  have : net.off 1 false = 1 := by decide
  rw [this] at f1
  have : net.off 1 true = 1 := by decide
  rw [this] at f2
  have : net.off 0 false = 1 := by decide
  rw [this] at f3
  have : net.off 0 true = 0 := by decide
  rw [this] at f4
  have : net.off 2 false = 0 := by decide
  rw [this] at f5
  have : net.off 2 true = 0 := by decide
  rw [this] at f6
  unfold H; omega

theorem hops_upper {d : Nat} (hd : ∀ j p, d ≤ b.loF j + b.loG j p) (t : Nat) :
    ∀ k, H x (t + k * d) ≤ H x t + k
  | 0 => by simp
  | k + 1 => by
      have := hop_upper x hd (t + k * d)
      have := hops_upper hd t k
      rw [show t + (k + 1) * d = t + k * d + d by rw [Nat.succ_mul]; omega]
      omega

/-- The min-plus lower bound: after reset release, a stage has caught up
with both its pins (read `D` steps earlier). -/
theorem ge_through {D R : Nat} (hD : ∀ j p, b.hiF j + b.hiG j p ≤ D)
    (hR : ∀ j s, R ≤ s → x.r j s = false) (j : Fin 3) (t : Nat) (ht : R ≤ t) :
    min (x.M t (net.src j false) + net.off j false) (x.M t (net.src j true) + net.off j true)
      ≤ x.M (t + D) j := by
  rw [x.M_eq (t + D) j]
  have a1 := (x.wF j).early_le (t + D)
  have hr := hR j (x.F j (t + D)) (by have := hD j false; omega)
  unfold Beh.E Beh.P
  simp only [hr, Bool.false_eq_true, ite_false]
  have k : ∀ p, x.M t (net.src j p) ≤ x.M (x.G j p (x.F j (t + D))) (net.src j p) := by
    intro p
    apply x.M_mono
    have := (x.wG j p).early_le (x.F j (t + D)); have := hD j p; omega
  have := k false; have := k true
  omega

/-- **At least one hop per `D` steps** once reset is released everywhere. -/
theorem hop_lower {D R : Nat} (hD : ∀ j p, b.hiF j + b.hiG j p ≤ D)
    (hR : ∀ j s, R ≤ s → x.r j s = false) (t : Nat) (ht : R ≤ t) :
    H x t + 1 ≤ H x (t + D) := by
  have i := ring_inv x t
  have g0 := ge_through x hD hR 0 t ht
  have g1 := ge_through x hD hR 1 t ht
  have g2 := ge_through x hD hR 2 t ht
  have : net.src 0 false = 2 := by decide
  rw [this] at g0
  have : net.src 0 true = 1 := by decide
  rw [this] at g0
  have : net.src 1 false = 0 := by decide
  rw [this] at g1
  have : net.src 1 true = 2 := by decide
  rw [this] at g1
  have : net.src 2 false = 1 := by decide
  rw [this] at g2
  have : net.src 2 true = 0 := by decide
  rw [this] at g2
  have : net.off 0 false = 1 := by decide
  rw [this] at g0
  have : net.off 0 true = 0 := by decide
  rw [this] at g0
  have : net.off 1 false = 1 := by decide
  rw [this] at g1
  have : net.off 1 true = 1 := by decide
  rw [this] at g1
  have : net.off 2 false = 0 := by decide
  rw [this] at g2
  have : net.off 2 true = 0 := by decide
  rw [this] at g2
  have m0 := x.M_mono (t + D) 0 t (Nat.le_add_right _ _)
  have m1 := x.M_mono (t + D) 1 t (Nat.le_add_right _ _)
  have m2 := x.M_mono (t + D) 2 t (Nat.le_add_right _ _)
  unfold H; omega

theorem hops_lower {D R : Nat} (hD : ∀ j p, b.hiF j + b.hiG j p ≤ D)
    (hR : ∀ j s, R ≤ s → x.r j s = false) (t : Nat) (ht : R ≤ t) :
    ∀ k, H x t + k ≤ H x (t + k * D)
  | 0 => by simp
  | k + 1 => by
      have := hop_lower x hD hR (t + k * D) (by omega)
      have := hops_lower hD hR t ht k
      rw [show t + (k + 1) * D = t + k * D + D by rw [Nat.succ_mul]; omega]
      omega

/-- Phase shift of node `j` in the hop count. -/
def cj (j : Fin 3) : Nat := if j = 0 then 1 else if j = 1 then 2 else 0

theorem cj_le (j : Fin 3) : cj j ≤ 2 := by unfold cj; split <;> (try split) <;> omega

theorem M_of_H (j : Fin 3) (t : Nat) : x.M t j = (H x t + cj j) / 3 := by
  have s := state_of_hops x t
  have : ∀ j : Fin 3, j = 0 ∨ j = 1 ∨ j = 2 := by decide
  rcases this j with rfl | rfl | rfl
  · rw [s.2.1]; rfl
  · rw [s.1]; rfl
  · rw [s.2.2]; rfl

/-- **Cycle-time bounds per node.** After reset release every node fires at
least once in each window of `3·D` steps, and in every window of `3·d` steps
at most once. -/
theorem node_period {d D R : Nat} (hd : ∀ j p, d ≤ b.loF j + b.loG j p)
    (hD : ∀ j p, b.hiF j + b.hiG j p ≤ D) (hR : ∀ j s, R ≤ s → x.r j s = false)
    (j : Fin 3) (t : Nat) :
    x.M (t + 3 * d) j ≤ x.M t j + 1 ∧ (R ≤ t → x.M t j + 1 ≤ x.M (t + 3 * D) j) := by
  have u := hops_upper x hd t 3
  rw [M_of_H x j (t + 3 * d), M_of_H x j t, M_of_H x j (t + 3 * D)]
  have c := cj_le j
  refine ⟨by omega, fun ht => ?_⟩
  have l := hops_lower x hD hR t ht 3
  omega

/-- **ring3 is hazard-free forever.** Under `Race`, every node of every
behaviour is its reset value flipped `M t j` times, with `M` the hop-count
state above: the waveforms of all three nodes are determined by `H` at all
times. -/
theorem ring3_safe (hR : Race net b) (t : Nat) :
    x.c 1 t = ph false ((H x t + 2) / 3) ∧ x.c 0 t = ph true ((H x t + 1) / 3) ∧
      x.c 2 t = ph false (H x t / 3) := by
  have s := state_of_hops x t
  rw [x.safe pairing hR t 1, x.safe pairing hR t 0, x.safe pairing hR t 2, s.1, s.2.1, s.2.2]
  exact ⟨rfl, rfl, rfl⟩

end

end Formal.Core.XAudit.Events.Ring3
