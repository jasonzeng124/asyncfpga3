import Formal.Net.CapstoneRefine

/-!
# Probe C-8x: non-vacuity witness for the per-channel refinement

A concrete physical channel `wP` and concrete single-launch runs `wrun k` meeting every
hypothesis of `held_dag` / `sampled_eq_zd_dag` (H_TXWIN, tcheck's DAG verdict, reset, receiver
rule), whose bus carries DIFFERENT values in different transactions (token `k` = `k mod 2`).

* netlist `wnet`: launch 0; data node 1 (arc 0→1, delay [1,2]); request node 2 (arc 0→2,
  delay [5,6]). `checkArr wnet 2 [1] 0 = true` by `decide` (data window (1,2) ends before the
  request window (5,6) starts).
* run `k` (fixed delays 2 and 5): launch rises at 0→1, data = launch ∧ `bk k` (so it settles
  to the token bit at 3), request rises at 5→6.
* channel `wP`, period 20 ps: transaction `k` launched at `20k`; req↑ at `20k+5→6`, ack↑ at
  `+7→8`, req↓ `+9→10`, ack↓ `+11→12`; bus at time `u` = run `u/20` at `u mod 20`.
-/

namespace Formal.Net.CapstoneRefine.Wit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Timing Formal.Net.CapstoneRefine

def wnet : Netlist := ⟨[⟨0, 1, 1, 2⟩, ⟨0, 2, 5, 6⟩]⟩

theorem wnet_wf : wnet.WF := by decide

theorem wcheck : checkArr wnet 2 [1] 0 = true := by decide

def bk (k : Nat) : Bool := k % 2 == 1

def wsig (k : Nat) : Nat → Trace := fun v t =>
  if v = 0 then decide (1 ≤ t) else if v = 1 then (decide (3 ≤ t) && bk k)
  else if v = 2 then decide (6 ≤ t) else false

def wd (i : Nat) : Nat := if i = 0 then 2 else 5

def wg (k : Nat) : Nat → (Nat → Bool) → Bool := fun v p =>
  if v = 1 then (p 0 && bk k) else if v = 2 then p 1 else false

theorem shift_launch {k : Nat} (d t : Nat) :
    shift d (wsig k 0) t = decide (d + 1 ≤ t) := by
  simp only [shift, wsig, ite_true]
  by_cases h : t < d
  · rw [if_pos h]; simp; omega
  · rw [if_neg h]; simp; omega

def wfrun (k : Nat) : FixedRun wnet (wsig k) where
  d := wd
  g := wg k
  launch := by
    intro t h
    simp only [changes, wsig, ite_true] at h
    apply Classical.byContradiction; intro h0
    apply h; simp; omega
  range := by
    intro i a h
    match i with
    | 0 => simp [wnet] at h; subst h; decide
    | 1 => simp [wnet] at h; subst h; decide
    | n + 2 => simp [wnet] at h
  local_ := by
    intro v x y h
    simp only [wg]
    by_cases h1 : v = 1
    · subst h1; simp only [ite_true]; rw [h 0 ⟨0, 1, 1, 2⟩ rfl rfl]
    · by_cases h2 : v = 2
      · subst h2; simp only [ite_true]; exact h 1 ⟨0, 2, 5, 6⟩ rfl rfl
      · simp only [h1, h2, ite_false]
  node := by
    intro v hv t
    have e0 : fixedPin wnet wd (wsig k) 0 t = shift 2 (wsig k 0) t := rfl
    have e1 : fixedPin wnet wd (wsig k) 1 t = shift 5 (wsig k 0) t := rfl
    by_cases h1 : v = 1
    · subst h1; simp only [wg, ite_true, e0, shift_launch]; simp [wsig]
    · by_cases h2 : v = 2
      · subst h2; simp only [wg, e1, shift_launch]; simp [wsig]
      · simp [wsig, wg, hv, h1, h2]

def wrun (k : Nat) : Run wnet (wsig k) := (wfrun k).toRun

/-- The physical channel: period 20 ps. -/
def wP : Chan where
  req := fun u => decide (6 ≤ u % 20 ∧ u % 20 ≤ 9)
  ack := fun u => decide (8 ≤ u % 20 ∧ u % 20 ≤ 11)
  dat := fun u => bv 1 (fun j => wsig (u / 20) ([1].getD j 0) (u % 20))

theorem riseB_wP (u : Nat) : riseB wP.req u = (u % 20 == 5) := by
  have e : (u + 1) % 20 = (u % 20 + 1) % 20 := by omega
  have key : ∀ m, m < 20 →
      (!(decide (6 ≤ m ∧ m ≤ 9)) && decide (6 ≤ (m + 1) % 20 ∧ (m + 1) % 20 ≤ 9)) = (m == 5) := by
    decide
  simp only [riseB, wP, e]
  exact key _ (Nat.mod_lt _ (by decide))

theorem cnt_wP (u : Nat) : cnt (riseB wP.req) u = u / 20 + (if 5 < u % 20 then 1 else 0) := by
  induction u with
  | zero => rfl
  | succ u ih =>
    simp only [cnt, ih, riseB_wP, beq_iff_eq]
    have hm := Nat.mod_lt u (show 20 > 0 by decide)
    have e : (u + 1) % 20 = (u % 20 + 1) % 20 := by omega
    have hd : (u + 1) / 20 = u / 20 + (if u % 20 = 19 then 1 else 0) := by
      by_cases h : u % 20 = 19
      · rw [if_pos h]; omega
      · rw [if_neg h]; omega
    have key : ∀ m, m < 20 → (if 5 < m then 1 else 0) + (if m = 5 then 1 else 0) =
        (if m = 19 then 1 else 0) + (if 5 < (m + 1) % 20 then 1 else 0) := by decide
    rw [hd, e]
    have := key _ hm
    omega

def wX : TxWin wP wsig [1] (fun k v => changes (wsig k 2) v) where
  τ k := 20 * k
  idle k := by simp [wP, Nat.mul_mod_right]
  count k := by rw [cnt_wP]; simp [Nat.mul_mod_right]
  reqIn k r ho := by
    have h1 := ho.1
    rw [riseB_wP] at h1
    have h5 : r % 20 = 5 := by simpa using h1
    have h2 := ho.2
    rw [cnt_wP, if_neg (by omega)] at h2
    rw [show r - 20 * k = 5 by omega]
    simp [changes, wsig]
  win k u h1 h2 := by
    show bv 1 (fun j => wsig (u / 20) ([1].getD j 0) (u % 20)) = _
    rw [show u / 20 = k by omega, show u % 20 = u - 20 * k by omega]; rfl

theorem wInit : Init wP := ⟨rfl, rfl⟩

theorem wRecv (u : Nat) : RecvStep wP u := by
  have e : (u + 1) % 20 = (u % 20 + 1) % 20 := by omega
  have key : ∀ m, m < 20 →
      (decide (8 ≤ (m + 1) % 20 ∧ (m + 1) % 20 ≤ 11) ≠ decide (8 ≤ m ∧ m ≤ 11) →
        decide (8 ≤ m ∧ m ≤ 11) ≠ decide (6 ≤ m ∧ m ≤ 9)) := by decide
  simp only [RecvStep, wP, e]
  exact key _ (Nat.mod_lt _ (by decide))

theorem w_zdBus (k : Nat) : zdBus wrun [1] k = if bk k then 1 else 0 := by
  have hz : zdEval wnet (wrun k).g (wsig k 0 1) 1 = bk k := by
    rw [zdEval_ne _ _ _ (by decide)]
    show wg k 1 _ = _
    simp only [wg, ite_true]
    rw [zdEval_zero]; rfl
  simp only [zdBus]
  show 0 + (if zdEval wnet (wrun k).g (wsig k 0 1) 1 = true then 2 ^ 0 else 0) = _
  rw [hz]; cases bk k <;> rfl

/-- **Non-vacuity of the per-channel refinement**: all hypotheses of `held_dag` and
`sampled_eq_zd_dag` hold for `wP`, the bus changes between transactions, and the conclusions
(Ops H_BUNDLE; every in-transaction sample = the zero-delay value) follow. -/
theorem refine_witness :
    Held wP ∧
    (∀ k r t, OffAt wP k r → r < t → (∀ s, r < s → s ≤ t → inTx wP s = true) →
      wP.dat t = if bk k then 1 else 0) ∧
    wP.dat 6 = 0 ∧ wP.dat 26 = 1 := by
  refine ⟨held_dag wnet_wf wcheck wrun wX wInit wRecv, ?_, by decide, by decide⟩
  intro k r t ho hrt hb
  rw [sampled_eq_zd_dag wnet_wf wcheck wrun wX ho hrt hb, w_zdBus]

/-! ## The separation is needed: a stale sample without tcheck's verdict

`bnet`: data arc delay 3, request arc delay 1. tcheck rejects it, and at the instant right after
the request changes the data node still holds the OLD value, not the zero-delay one. -/

def bnet : Netlist := ⟨[⟨0, 1, 3, 3⟩, ⟨0, 2, 1, 1⟩]⟩

theorem bnet_reject : checkArr bnet 2 [1] 0 = false := by decide

def bsig : Nat → Trace := fun v t =>
  if v = 0 then decide (1 ≤ t) else if v = 1 then decide (4 ≤ t)
  else if v = 2 then decide (2 ≤ t) else false

def bg : Nat → (Nat → Bool) → Bool := fun v p => if v = 1 then p 0 else if v = 2 then p 1 else false

theorem bshift (d t : Nat) : shift d (bsig 0) t = decide (d + 1 ≤ t) := by
  simp only [shift, bsig, ite_true]
  by_cases h : t < d
  · rw [if_pos h]; simp; omega
  · rw [if_neg h]; simp; omega

def bfrun : FixedRun bnet bsig where
  d := fun i => if i = 0 then 3 else 1
  g := bg
  launch := by
    intro t h
    simp only [changes, bsig, ite_true] at h
    apply Classical.byContradiction; intro h0
    apply h; simp; omega
  range := by
    intro i a h
    match i with
    | 0 => simp [bnet] at h; subst h; decide
    | 1 => simp [bnet] at h; subst h; decide
    | n + 2 => simp [bnet] at h
  local_ := by
    intro v x y h
    simp only [bg]
    by_cases h1 : v = 1
    · subst h1; simp only [ite_true]; exact h 0 ⟨0, 1, 3, 3⟩ rfl rfl
    · by_cases h2 : v = 2
      · subst h2; simp only [ite_true]; exact h 1 ⟨0, 2, 1, 1⟩ rfl rfl
      · simp only [h1, h2, ite_false]
  node := by
    intro v hv t
    have e0 : fixedPin bnet (fun i => if i = 0 then 3 else 1) bsig 0 t = shift 3 (bsig 0) t := rfl
    have e1 : fixedPin bnet (fun i => if i = 0 then 3 else 1) bsig 1 t = shift 1 (bsig 0) t := rfl
    by_cases h1 : v = 1
    · subst h1; simp only [bg, ite_true, e0, bshift]; simp [bsig]
    · by_cases h2 : v = 2
      · subst h2; simp only [bg, e1, bshift]; simp [bsig]
      · simp [bsig, bg, hv, h1, h2]

theorem stale_without_check :
    checkArr bnet 2 [1] 0 = false ∧ changes (bsig 2) 1 ∧
      bsig 1 2 = false ∧ zdEval bnet bfrun.toRun.g (bsig 0 1) 1 = true := by
  refine ⟨bnet_reject, by simp [changes, bsig], by decide, ?_⟩
  rw [zdEval_ne _ _ _ (by decide)]
  show bg 1 _ = _
  simp only [bg, ite_true]
  rw [zdEval_zero]; rfl

end Formal.Net.CapstoneRefine.Wit
