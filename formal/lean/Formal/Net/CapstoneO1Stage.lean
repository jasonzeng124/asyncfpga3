import Formal.Net.CapstoneCM

/-!
# Probe C-8q: one arbiter stage, forced by a count bound (the arbiter half of O1)

`CM.amerge_forced` (8j) forces the winner from H_EXCL_REQ ("the two requests are never high
together"). That hypothesis is too strong for a real network: after input `x` wins, `x.req`
stays high through its return-to-zero, and nothing in a loop with storage waits for that
return-to-zero, so under unbounded (SI) delays the back-edge request `y.req` can rise while
`x.req` is still high. The arbiter is then not contended: grant 1 is held (`g1` follows
`x.req`, and `g2` cannot rise while `g1` or `A0` is high).

This file replaces H_EXCL_REQ by a COUNT-ONLY bound, the shape a simulation of the token run
produces ("the circuit is never ahead of the token run at this stage's inputs"):

`CutBound x y z ω`: at every time `t`, with `n` = #offers on `z` so far, if the first `n`
winners were `ω`, then input `x` has offered at most `#(¬ω before n) + [¬ω n]` tokens and
input `y` at most `#(ω before n) + [ω n]`. In the token run with labels `ω`, those are exactly
the input tokens that firings `0..n` of the control_merge consume; any later input token is
produced causally after firing `n` (one token on the control spine).

Proved, for the gate model `CM.AMerge` (grants free, H_ARB, H_ARB_EXCL, H_AMERGE_RTZ, ...):
* `zc_eq`: the merge's internal "passed" counters are the winner counts at `#z offers`;
* `offer_pending`: at each `z` offer, the winning input has exactly one offered, not yet
  passed token (`dx = 2` / `dy = 2` of 8j's table);
* `stage_forced`: `CutBound ⇒` the winner of EVERY offered token is `ω` (H_CM_FORCED for the
  stage), by induction on the token index;
* `stage_uncontended`: `CutBound ⇒` whenever both requests are high, a grant is already
  held: the arbiter never has to decide between two live requests (no free contention);
  `free_contended_pending` is the table fact behind it.
NOT proved here: that requests are never high together (H_EXCL_REQ). It does not follow, and
is not expected to hold under SI delays (see C-8q-o1.md).
-/

namespace Formal.Net.Capstone.O1
open Formal.Net Formal.Net.Handshake Formal.Net.Ops
open Formal.Net.Ops.CM
open Formal.Net.Ops.Mux (b2n)

/-- The count bound of one stage (see the module doc). -/
def CutBound (x y z : Chan) (ω : Nat → Bool) : Prop :=
  ∀ t, (∀ i, i < cnt (riseB z.req) t → winner z i = ω i) →
    cnt (riseB x.req) t ≤ cnt (fun i => !ω i) (cnt (riseB z.req) t) + b2n (!ω (cnt (riseB z.req) t)) ∧
    cnt (riseB y.req) t ≤ cnt ω (cnt (riseB z.req) t) + b2n (ω (cnt (riseB z.req) t))

variable {x y z : Chan} {g1 g2 : Trace}

theorem won_dat (M : AMerge x y z g1 g2) (u : Nat) :
    (z.dat (u + 1) % 2 == 1) = won y g2 (u + 1) := by
  rw [M.dat, b2n_mod]; unfold won; cases g2 (u + 1) || y.ack (u + 1) <;> rfl

theorem cnt_succ (f : Nat → Bool) (t : Nat) : cnt f (t + 1) = cnt f t + b2n (f t) := by
  simp only [cnt, b2n]

/-- The merge's "passed" counters are the winner counts at the number of `z` offers. -/
theorem zc_eq (M : AMerge x y z g1 g2) : ∀ t,
    zc0 y z g2 t = cnt (fun i => !winner z i) (cnt (riseB z.req) t) ∧
    zc1 y z g2 t = cnt (winner z) (cnt (riseB z.req) t) := by
  intro t
  induction t with
  | zero => exact ⟨rfl, rfl⟩
  | succ t ih =>
    obtain ⟨h0, h1⟩ := ih
    unfold zc0 zc1 at *
    simp only [cnt_succ]
    cases hr : riseB z.req t
    · simp only [Bool.false_and, b2n, Bool.false_eq_true, ite_false, Nat.add_zero]; exact ⟨h0, h1⟩
    · have hw : winner z (cnt (riseB z.req) t) = won y g2 (t + 1) := by
        rw [winner_at ⟨hr, rfl⟩, won_dat M]
      simp only [Bool.true_and, b2n, ite_true, cnt_succ, ← hw, h0, h1]
      cases winner z (cnt (riseB z.req) t) <;> simp

/-- At each `z` offer, the winning input has exactly one offered, not yet passed token. -/
theorem offer_pending (M : AMerge x y z g1 g2) (hpx : Protocol x) (hpy : Protocol y)
    (hpz : Protocol z) {k r : Nat} (hoff : OffAt z k r) :
    (winner z k = true → cnt (riseB y.req) r = cnt (winner z) k + 1) ∧
    (winner z k = false → cnt (riseB x.req) r = cnt (fun i => !winner z i) k + 1) := by
  obtain ⟨dx, dy, hm, h1, h2⟩ := amerge_inv M hpx.1.1 hpy.1.1 hpz.1.2 r
    (fun s _ => ⟨(hpx.2 s).1, (hpy.2 s).1, (hpz.2 s).2⟩)
  have hr0 : z.req r = false := by have := hoff.1; simp [riseB] at this; exact this.1
  have hr1 : z.req (r + 1) = true := by have := hoff.1; simp [riseB] at this; exact this.2
  have K := amerge_closed _ (amem hm) _ (hpx.2 r).1 _ (hpy.2 r).1 _ (hpz.2 r).2
    _ (M.H_ARB1 r) _ (M.H_ARB2 r) (M.H_ARB_EXCL (r + 1)) _ (M.zr r) (M.H_AMERGE_RTZ r)
    _ (M.xa r) _ (M.ya r)
  have Ko := K.2.2.2.2.2.2
  simp only [ast, hr0, hr1] at Ko
  obtain ⟨_, hsel⟩ := Ko rfl
  have hw : winner z k = won y g2 (r + 1) := by rw [winner_at hoff, won_dat M]
  obtain ⟨e0, e1⟩ := zc_eq M r
  rw [hoff.2] at e0 e1
  unfold won at hw
  refine ⟨fun ht => ?_, fun hf => ?_⟩
  · rw [hw] at ht; rw [ht] at hsel; simp only [ite_true] at hsel
    omega
  · rw [hw] at hf; rw [hf] at hsel; simp only [Bool.false_eq_true, ite_false] at hsel
    omega

theorem offered_lt {c : Chan} {t i : Nat} (h : i < cnt (riseB c.req) t) : ∃ r, OffAt c i r := by
  obtain ⟨e, _, hf, hc⟩ := cnt_ge_aux (riseB c.req) t i (by omega)
  exact ⟨e, hf, hc⟩

/-- **H_CM_FORCED for one stage, from the count bound.** -/
theorem stage_forced (M : AMerge x y z g1 g2) (hpx : Protocol x) (hpy : Protocol y)
    (hpz : Protocol z) (ω : Nat → Bool) (H_CUT : CutBound x y z ω) :
    ∀ k r, OffAt z k r → winner z k = ω k := by
  intro k
  induction k using Nat.strongRecOn with
  | _ k ih =>
    intro r hoff
    have hb : ∀ i, i < k → winner z i = ω i := by
      intro i hi
      obtain ⟨r', hr'⟩ := Capstone.offered_below hoff hi
      exact ih i hi r' hr'
    have hk : cnt (riseB z.req) r = k := hoff.2
    obtain ⟨cx, cy⟩ := H_CUT r (by rw [hk]; exact hb)
    rw [hk] at cx cy
    have c1 : cnt (winner z) k = cnt ω k := cnt_congr_lt k hb
    have c0 : cnt (fun i => !winner z i) k = cnt (fun i => !ω i) k :=
      cnt_congr_lt k (fun i hi => by rw [hb i hi])
    obtain ⟨py, px⟩ := offer_pending M hpx hpy hpz hoff
    cases hwk : winner z k
    · have := px hwk; rw [c0] at this
      cases hω : ω k
      · rfl
      · rw [hω] at cx; simp [b2n] at cx; omega
    · have := py hwk; rw [c1] at this
      cases hω : ω k
      · rw [hω] at cy; simp [b2n] at cy; omega
      · rfl

set_option maxRecDepth 100000 in
/-- Table fact: in a reachable state where both requests are high and no grant is held, both
inputs have an offered, not yet passed token. -/
theorem free_contended_pending : ∀ e ∈ atbl,
    e.xr = true → e.yr = true → e.g1 = false → e.g2 = false → e.dx = 2 ∧ e.dy = 2 := by
  decide +kernel

/-- **No free contention.** Under the count bound, whenever both requests are high a grant is
already held: the arbiter's mutex never has to resolve two live requests. -/
theorem stage_uncontended (M : AMerge x y z g1 g2) (hpx : Protocol x) (hpy : Protocol y)
    (hpz : Protocol z) (ω : Nat → Bool) (H_CUT : CutBound x y z ω) :
    ∀ t, x.req t = true → y.req t = true → g1 t = true ∨ g2 t = true := by
  intro t hx hy
  cases hg1 : g1 t
  · cases hg2 : g2 t
    · exfalso
      obtain ⟨dx, dy, hm, h1, h2⟩ := amerge_inv M hpx.1.1 hpy.1.1 hpz.1.2 t
        (fun s _ => ⟨(hpx.2 s).1, (hpy.2 s).1, (hpz.2 s).2⟩)
      have hp := free_contended_pending _ (amem hm) hx hy hg1 hg2
      simp only [ast] at hp
      obtain ⟨e0, e1⟩ := zc_eq M t
      have hf := stage_forced M hpx hpy hpz ω H_CUT
      have hb : ∀ i, i < cnt (riseB z.req) t → winner z i = ω i := by
        intro i hi
        obtain ⟨r, hr⟩ := offered_lt hi
        exact hf i r hr
      obtain ⟨cx, cy⟩ := H_CUT t hb
      have c1 := cnt_congr_lt (cnt (riseB z.req) t) hb
      have c0 : cnt (fun i => !winner z i) (cnt (riseB z.req) t) =
          cnt (fun i => !ω i) (cnt (riseB z.req) t) :=
        cnt_congr_lt _ (fun i hi => by rw [hb i hi])
      cases hω : ω (cnt (riseB z.req) t)
      · rw [hω] at cy; simp [b2n] at cy; omega
      · rw [hω] at cx; simp [b2n] at cx; omega
    · exact Or.inr rfl
  · exact Or.inl rfl

/-! ## H_CUT is not trivially true, and is satisfiable -/

/-- Negative control: a `y` request with no `z` offer and run labels `ω = false` (the run's
next firing takes `x`) violates the bound. -/
theorem cut_can_fail : ¬ CutBound ⟨fun _ => false, fun _ => false, fun _ => 0⟩
    ⟨fun t => decide (1 ≤ t), fun _ => false, fun _ => 0⟩ ⟨fun _ => false, fun _ => false, fun _ => 0⟩
    (fun _ => false) := by
  intro h
  have := (h 2 (by intro i hi; simp [cnt, riseB] at hi)).2
  simp [cnt, riseB, b2n] at this

/-- Satisfiable: a quiet stage meets the bound for every label stream. -/
theorem cut_quiet (ω : Nat → Bool) : CutBound ⟨fun _ => false, fun _ => false, fun _ => 0⟩
    ⟨fun _ => false, fun _ => false, fun _ => 0⟩ ⟨fun _ => false, fun _ => false, fun _ => 0⟩ ω := by
  intro t _
  have h : ∀ t, cnt (riseB (fun _ => false)) t = 0 := by
    intro t; induction t with
    | zero => rfl
    | succ t ih => simp [cnt, riseB, ih]
  simp only [h]; exact ⟨Nat.zero_le _, Nat.zero_le _⟩

end Formal.Net.Capstone.O1
