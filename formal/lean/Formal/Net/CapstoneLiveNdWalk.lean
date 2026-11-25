import Formal.Net.CapstoneLiveNdOff
import Formal.Net.CapstoneWalk

/-!
# Probe C-8z (5): H_WALK_ENDS proved; gcd_hw liveness with only H_NO_DEADLOCK' open

8u bounded the spine by H_WALK_ENDS `L` (the token-level spine walk stops after `L` steps),
checked on 32 vectors but not proved. Here it is proved for the token run `y` that 8s's
`good_run` provides, with an explicit `L`:

    Lrun y = 1 + Σ_{spine c} (A y c + 1)

where `A y c` (8s) is the number of tokens the complete token run consumes on the GcdHw
channels that circuit spine channel `c` stands for. So `Lrun y` is at most (number of spine
channels) + (number of spine tokens the token run consumes) + 1: a token-run length.

Proof (`walk_ends`): along the walk, every step that has a current channel increments that
channel's visit count `W`, so `Σ_spine W ≥ p` while the walk is alive (`sumW_ge`). 8s's
simulation (`walk_sim`) relates each walk position to a state `x` on the path of the run,
with `W c ≤ A x c + 1 ≤ A y c + 1` (consumed histories only grow, `texec_pre`). Both
together bound the number of live steps by `Σ (A y c + 1)`.

`gcd_hw_live_final`: for `a, b < 2^31`, under H_CELLS, H_BUNDLE, H_START_ONCE,
H_BOUNDED_DELAY' `H`, H_START_ENV `H`, H_ARB_UNCONTESTED_BOUNDED `H` and **H_NO_DEADLOCK'**
(the one open obligation), the first `out0` token closes before
`(1168 * (8 * Lrun y + 23) + 1) * (H + 1)` ticks and carries `Nat.gcd a b`, for the complete
token run `y` of `(a, b)`.
-/

namespace Formal.Net.CapNet.Live.Nd
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Live
open Formal.Net.CapSafe (Good TS texec)

/-- The walk-length bound from the token run. -/
def Lrun (y : TS) : Nat :=
  1 + ((List.finRange NC).map (fun c => if sp c then A y c + 1 else 0)).sum

theorem sum_le_sum {α : Type} (L : List α) (f g : α → Nat) (h : ∀ x ∈ L, f x ≤ g x) :
    (L.map f).sum ≤ (L.map g).sum := by
  induction L with
  | nil => simp
  | cons a L ih =>
    simp only [List.map_cons, List.sum_cons]
    have := h a (List.mem_cons_self ..)
    have := ih (fun x hx => h x (List.mem_cons_of_mem _ hx))
    omega

theorem A_mono {x y : TS} {ls : List Nat} (hex : texec x ls = some y) (c : Fin NC) : A x c ≤ A y c := by
  unfold A
  apply sum_le_sum
  intro h _
  obtain ⟨t, ht⟩ := (texec_pre ls x y hex h).2
  rw [ht, List.length_append]; omega

theorem Bo_le (cur : Option (Nat × Nat)) (g r : Nat) (a : Bool) : Bo cur g r a ≤ 1 := by
  unfold Bo; cases cur with
  | none => simp
  | some p => simp only [Gcd.bn]; split <;> omega

section
variable (σ : Fin NC → Nat → Nat)

/-- While the walk is alive, the spine visit counts sum to at least the number of steps. -/
theorem sumW_ge : ∀ p, (∀ q, q < p → (walk σ q).cur ≠ none) →
    p ≤ ((List.finRange NC).map (fun c => if sp c then (walk σ p).W c else 0)).sum := by
  intro p
  induction p with
  | zero => intro _; exact Nat.zero_le _
  | succ p ih =>
    intro hal
    have h1 := ih (fun q hq => hal q (by omega))
    have hsplit : ((List.finRange NC).map (fun c => if sp c then (walk σ (p + 1)).W c else 0)).sum =
        ((List.finRange NC).map (fun c => if sp c then (walk σ p).W c else 0)).sum +
        ((List.finRange NC).map (fun c => if sp c then Gcd.bn (visB σ c p) else 0)).sum := by
      rw [← sum_map_add]
      congr 1
      apply List.map_congr_left
      intro c _
      rw [W_succ]
      split <;> simp
    obtain ⟨d, hd⟩ : ∃ d, (walk σ p).cur = some d := by
      cases h : (walk σ p).cur with
      | none => exact absurd h (hal p (by omega))
      | some d => exact ⟨d, rfl⟩
    have h2 := one_le_sum (L := List.finRange NC)
      (f := fun c => if sp c then Gcd.bn (visB σ c p) else 0) (List.mem_finRange d) (by
        simp [cur_sp σ p d hd, visB, hd, Gcd.bn])
    omega

end

/-- **H_WALK_ENDS, proved.** For the token run `y` of 8s's `good_run`, the spine walk has
ended by step `Lrun y`. -/
theorem walk_ends {a b : Nat} {y : TS} (hy : Good a b y) {ls : List Nat}
    (hex : texec (Gcd.x0 a b) ls = some y) : (walk (σY a b y) (Lrun y)).cur = none := by
  apply Classical.byContradiction
  intro hne
  have hal : ∀ q, q < Lrun y → (walk (σY a b y) q).cur ≠ none := by
    intro q hq hq'
    have := walk_stuck (σY a b y) hq' (Lrun y) (by omega)
    rw [this] at hne; exact hne hq'
  have h1 := sumW_ge (σY a b y) (Lrun y) hal
  obtain ⟨x, ⟨_, ls', hx⟩, hR⟩ := walk_sim hy hex (Lrun y)
  have h2 := sum_le_sum (List.finRange NC)
    (fun c => if sp c then (walk (σY a b y) (Lrun y)).W c else 0)
    (fun c => if sp c then A y c + 1 else 0) (by
      intro c _
      by_cases hs : sp c = true
      · simp only [hs, ite_true]
        have e := hR.cnt c hs
        have := Bo_le ((walk (σY a b y) (Lrun y)).cur.map gr) (grp c) (rho c) (adj c)
        have := A_mono hx c
        omega
      · simp [hs])
  unfold Lrun at h1 h2
  omega

/-- **gcd_hw circuit liveness, with H_NO_DEADLOCK' the only open network obligation.** -/
theorem gcd_hw_live_final (a b H : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (ch : Fin NC → Chan) (itr : Itr)
    (H_CELLS : ∀ p : Fin NO, CellI ch (srcV a b) itr p (opAt p))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1)
    (H_BOUNDED_DELAY' : ∀ p, p ≠ prodOf start → ∀ g ∈ gatesK p (opAt p), BndG H (gsAt ch itr) g)
    (H_START_ENV : StartEnv H (ch start))
    (H_ARB_UNCONTESTED_BOUNDED : ∀ p x u z w, opAt p = .amerge x u z w →
      ArbUnc H (ch x) (ch u) (ch z) (itr p 0) (itr p 1))
    (H_NO_DEADLOCK' : ∀ t, cnt (fallB (ch out0).ack) t = 0 →
      ¬ (Quiet2 (gsAt ch itr t) ∧
         (cnt (riseB (ch start).req) t = 0 → (ch start).ack t = false → (ch start).req t = true))) :
    ∃ y, Good a b y ∧ ∃ e, e < (1168 * (8 * Lrun y + 23) + 1) * (H + 1) ∧ TokAt (ch out0) 0 e ∧
      (ch out0).dat e = Nat.gcd a b := by
  obtain ⟨y, ls, hy, hex⟩ := good_run ha hb
  exact ⟨y, hy, gcd_hw_live_bounded a b H (Lrun y) ch itr H_CELLS H_BUNDLE H_START_ONCE y hy
    (walk_ok hy hex) (walk_ends hy hex) H_BOUNDED_DELAY' H_START_ENV H_ARB_UNCONTESTED_BOUNDED
    H_NO_DEADLOCK'⟩

end Formal.Net.CapNet.Live.Nd
