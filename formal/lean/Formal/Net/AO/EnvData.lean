import Formal.Target.Spec
import Formal.Net.AO.EnvHS
import Formal.Net.TimedOccX

/-!
# Input data claims from `Spec.EnvIn` (shard C, S4: the data half of the environment bridge)

**Problem, plainly.** `AO.timedA_follows` needs every data claim on an environment node to hold (`hEnvC`), given
that the counts so far are an ideal. The natural claim on bit `i` of an input bus for pair `j` is: from `su` before
the request's `j`-th rise (event `(req, 2j)`) until the acknowledge's `j`-th fall (event `(ack, 2j+1)`), the bit is
bit `i` of `vals j`. `Spec.EnvIn` says the bus holds `vals j` from `su` before the rise, and while request or
acknowledge is high. Does that give the claim, in the count terms of the timed model?

**Proved:**
* `testBit_busVal`: bit `i` of `busVal x d t` is `x d[i] t`;
* `rises_cnt`: from a time `t0 ≥ R` with the request low and no rise yet, `rises = (cnt + 1) / 2`;
* `env_claim`: the claim holds at every `t` at which the request and acknowledge counts are within one
  (`cnt ack ≤ cnt req ≤ cnt ack + 1`), which `EnvHS.hs_counts` gives from the ideal.

**Not shown here:** the instance (which claims THE target's certificate uses), the start channel's `vals = 0`.
-/

namespace Formal.Net.AO.EnvData
open Formal.Target Formal.Net.AO Formal.Net.OccNet.Timed Formal.Net.OccNet.TimedX

/-! ## Bits of a bus -/

def bv (b : Nat → Bool) (d : List Nat) (o : Nat) : Nat := ((d.zipIdx o).map fun p => if b p.1 then 2 ^ p.2 else 0).sum

theorem bv_cons (b : Nat → Bool) (n : Nat) (d : List Nat) (o : Nat) :
    bv b (n :: d) o = (if b n then 2 ^ o else 0) + bv b d (o + 1) := by
  simp [bv, List.zipIdx_cons]

theorem bv_succ (b : Nat → Bool) : ∀ (d : List Nat) (o : Nat), bv b d (o + 1) = 2 * bv b d o
  | [], o => by simp [bv]
  | n :: d, o => by
    rw [bv_cons, bv_cons, bv_succ b d (o + 1)]
    cases b n <;> simp [Nat.pow_succ] <;> omega

theorem bv_cons0 (b : Nat → Bool) (n : Nat) (d : List Nat) :
    bv b (n :: d) 0 = (if b n then 1 else 0) + 2 * bv b d 0 := by
  rw [bv_cons, bv_succ]; simp

theorem testBit_bv (b : Nat → Bool) : ∀ (d : List Nat) (i : Nat) (hi : i < d.length),
    (bv b d 0).testBit i = b (d[i]'hi)
  | [], i, hi => by simp at hi
  | n :: d, 0, _ => by
    rw [bv_cons0, Nat.testBit_zero]
    cases h : b n <;> simp [h] <;> omega
  | n :: d, i + 1, hi => by
    rw [bv_cons0, Nat.testBit_succ]
    have : ((if b n then 1 else 0) + 2 * bv b d 0) / 2 = bv b d 0 := by
      cases b n <;> simp <;> omega
    rw [this, testBit_bv b d i (by simp at hi; omega)]
    simp

theorem busVal_eq (x : Beh) (d : List Nat) (t : Nat) : busVal x d t = bv (fun n => x n t) d 0 := by
  simp only [busVal, bv]

theorem testBit_busVal (x : Beh) (d : List Nat) (t i : Nat) (hi : i < d.length) :
    (busVal x d t).testBit i = x (d[i]'hi) t := by
  rw [busVal_eq, testBit_bv]

/-! ## Rises and counts -/

theorem x_par (x : Beh) (t0 u : Nat) (h0 : x u t0 = false) (t : Nat) (ht : t0 ≤ t) :
    x u t = (cnt x t0 u t % 2 == 1) := by
  have := x_eq_st (x := x) (t0 := t0) u 0 (fun s h1 h2 => by rw [show s = t0 by omega]) t (by omega)
  rw [this]; simp [Formal.Net.OccNet.st, h0]

theorem rises_cnt (x : Beh) (R t0 rq : Nat) (hR : R ≤ t0) (h0 : x rq t0 = false) (hr0 : rises (x rq) R t0 = 0) :
    ∀ t, t0 ≤ t → rises (x rq) R t = (cnt x t0 rq t + 1) / 2 := by
  intro t ht
  induction t, ht using Nat.le_induction with
  | base => rw [hr0, cnt_le_t0 rq t0 (Nat.le_refl _)]
  | succ t ht ih =>
    have p1 := x_par x t0 rq h0 t ht
    have hRt : R ≤ t := by omega
    rw [cnt_succ rq t ht]
    simp only [rises, ih]
    rcases Nat.mod_two_eq_zero_or_one (cnt x t0 rq t) with hp | hp
    · have hx : x rq t = false := by rw [p1, hp]; rfl
      cases h1 : x rq (t + 1) <;> simp [hx, hRt] <;> omega
    · have hx : x rq t = true := by rw [p1, hp]; rfl
      cases h1 : x rq (t + 1) <;> simp [hx] <;> omega

/-- The first time a count reaches `k + 1`. -/
theorem first_reach (x : Beh) (t0 u k a : Nat) (ha : cnt x t0 u a ≤ k) :
    ∀ b, k + 1 ≤ cnt x t0 u b → ∃ T, a < T ∧ T ≤ b ∧ cnt x t0 u (T - 1) = k ∧ cnt x t0 u T = k + 1
  | 0, hb => by have := cnt_mono (x := x) (t0 := t0) u 0 a (Nat.zero_le _); omega
  | b + 1, hb => by
    by_cases hc : k + 1 ≤ cnt x t0 u b
    · obtain ⟨T, h1, h2, h3, h4⟩ := first_reach x t0 u k a ha b hc
      exact ⟨T, h1, by omega, h3, h4⟩
    · have hs := cnt_step_le (x := x) (t0 := t0) u b
      have hab : a ≤ b := by
        rcases Nat.lt_or_ge b a with h | h
        · have := cnt_mono (x := x) (t0 := t0) u (b + 1) a (by omega); omega
        · exact h
      have := cnt_mono (x := x) (t0 := t0) u a b hab
      exact ⟨b + 1, by omega, Nat.le_refl _, by simp only [Nat.add_sub_cancel]; omega, by omega⟩

/-! ## The claim -/

/-- **An input bus bit holds its offered value**, from `su` before the request's `j`-th rise until the
acknowledge's `j`-th fall, at every time where the two counts are within one. -/
theorem env_claim (x : Beh) (ch : InCh) (R su t0 : Nat) (n : Option Nat) (vals : Nat → Nat)
    (hE : EnvIn x ch R su n vals) (hR : R ≤ t0) (h0r : x ch.req t0 = false) (h0a : x ch.ack t0 = false)
    (hr0 : rises (x ch.req) R t0 = 0)
    (j i : Nat) (hi : i < ch.data.length) (t : Nat)
    (hbal : cnt x t0 ch.ack t ≤ cnt x t0 ch.req t ∧ cnt x t0 ch.req t ≤ cnt x t0 ch.ack t + 1)
    (hA : 2 * j < cnt x t0 ch.req (t + su)) (hB : cnt x t0 ch.ack t ≤ 2 * j + 1) :
    x (ch.data[i]'hi) t = (vals j).testBit i := by
  obtain ⟨_, _, _, _, hsu, hhi⟩ := hE
  rw [← testBit_busVal x ch.data t i hi]
  congr 1
  by_cases hc : 2 * j + 1 ≤ cnt x t0 ch.req t
  · -- the rise has happened: request or acknowledge is high
    have ht0 : t0 < t := by
      rcases Nat.lt_or_ge t0 t with h | h
      · exact h
      · rw [cnt_le_t0 _ t h] at hc; omega
    have hrs := rises_cnt x R t0 ch.req hR h0r hr0 t (by omega)
    have pr := x_par x t0 ch.req h0r t (by omega)
    have pa := x_par x t0 ch.ack h0a t (by omega)
    have hhigh : x ch.req t = true ∨ x ch.ack t = true := by
      rcases Nat.mod_two_eq_zero_or_one (cnt x t0 ch.req t) with hp | hp
      · right; rw [pa]
        have : cnt x t0 ch.ack t = 2 * j + 1 := by omega
        rw [this]; simp <;> omega
      · left; rw [pr, hp]; rfl
    have := hhi t (by omega) hhigh (by rw [hrs]; omega)
    rw [this, hrs]; congr 1; omega
  · -- the rise is within `su` after `t`: the setup clause
    obtain ⟨T, h1, h2, h3, h4⟩ := first_reach x t0 ch.req (2 * j) t (by omega) (t + su) (by omega)
    have hT0 : t0 < T := by
      rcases Nat.lt_or_ge t0 T with h | h
      · exact h
      · rw [cnt_le_t0 _ T h] at h4; omega
    have hT : T - 1 + 1 = T := by omega
    have pr1 := x_par x t0 ch.req h0r (T - 1) (by omega)
    have pr2 := x_par x t0 ch.req h0r T (by omega)
    rw [h3] at pr1; rw [h4] at pr2
    have hf : x ch.req (T - 1) = false := by rw [pr1]; simp
    have htr : x ch.req (T - 1 + 1) = true := by rw [hT, pr2]; simp <;> omega
    have := hsu (T - 1) (by omega) hf htr t (by omega) (by omega)
    rw [this, hT, rises_cnt x R t0 ch.req hR h0r hr0 T (by omega), h4]; congr 1; omega

/-- **The claim in the timed model's terms**: given that the counts at `t` are an ideal of an order in which
acknowledge `k` needs request `k` and request `k+1` needs acknowledge `k`, the input bit's claim for pair `j` holds at
`t` (window `[τ(req, 2j) - su, τ(ack, 2j+1))`). This is the shape `hEnvC` of `AO.timedA_follows` asks for. -/
theorem env_holds (C : Cert Nat) (dat : Nat → Bool) (x : Beh) (ch : InCh) (R su t0 H : Nat) (n : Option Nat)
    (vals : Nat → Nat) (hE : EnvIn x ch R su n vals) (hR : R ≤ t0) (h0r : x ch.req t0 = false)
    (h0a : x ch.ack t0 = false) (hr0 : rises (x ch.req) R t0 = 0)
    (hdr : dat ch.req = false) (hda : dat ch.ack = false)
    (hAk : ∀ k, k < C.len ch.ack → ∀ alt ∈ C.causes ch.ack k, (ch.req, k) ∈ alt)
    (hRq : ∀ k, k + 1 < C.len ch.req → ∀ alt ∈ C.causes ch.req (k + 1), (ch.ack, k) ∈ alt)
    (j i : Nat) (hi : i < ch.data.length) (t : Nat) (hI : Ideal C (fun u => cntE dat x t0 u t)) :
    Holds x t0 H ⟨ch.data[i]'hi, (vals j).testBit i, some (ch.req, 2 * j), -(su : Int), some (ch.ack, 2 * j + 1), 0⟩ t := by
  intro _ hA hB
  simp only [hbI] at hA hB
  obtain ⟨b1, b2⟩ := EnvHS.hs_counts C _ hI ch.req ch.ack hAk hRq
  simp only [cntE, hdr, hda, Bool.false_eq_true, if_false] at b1 b2
  have hA' : 2 * j < cnt x t0 ch.req (t + su) := by
    have e : ((t : Int) - -(su : Int)).toNat = t + su := by omega
    rw [e] at hA; exact hA.2
  have hB' : cnt x t0 ch.ack t ≤ 2 * j + 1 := by
    have e : ((t : Int) - ((0 : Nat) : Int)).toNat = t := by omega
    rcases Nat.lt_or_ge (2 * j + 1) (cnt x t0 ch.ack t) with h | h
    · exact absurd ⟨by omega, by rw [e]; exact h⟩ hB
    · exact h
  exact env_claim x ch R su t0 n vals hE hR h0r h0a hr0 j i hi t ⟨b1, b2⟩ hA' hB'

end Formal.Net.AO.EnvData
