import Formal.Net.CapstoneLive
import Formal.Net.CapstoneO1

/-!
# Probe C-8z (1): `gcd_hw_live`'s hypotheses force the `start` handshake to hang

`CapstoneLive.gcd_hw_live` (8u) assumes H_BOUNDED_DELAY for EVERY gate of `gatesK`, which
includes the `bd_src` LUT1 of the `start` source (`gw (rq start) (!ak start)`), AND
H_START_ONCE (`start` is offered at most once). The two together say: once `start`'s first
token closes (its acknowledge falls), the source is excited to offer again and must do so
within `H`, which H_START_ONCE forbids.

`start_never_closes`: under H_CELLS, H_BUNDLE, H_START_ONCE and H_BOUNDED_DELAY as stated in
`gcd_hw_live`, the acknowledge of `start` never falls: the first invocation's start token is
never released.

Consequence (argued, not mechanised here): in the rig the start token is released as soon as
the first link stage behind `start` hands its token on, long before `out0` can close, and
after the first `out0` close the hypotheses still constrain the run forever. So the
hypothesis set of `gcd_hw_live` describes only runs in which the first stage behind `start`
never completes its input handshake. In such a run `out0` never closes, while
H_NO_DEADLOCK + H_FIRING_BOUND force it to close. The set is therefore (at least) not
satisfiable by any physically meaningful run, and H_NO_DEADLOCK, as 8u stated it, should
not be proved in that context. `CapstoneLiveNd.gcd_hw_live_nd` repairs the statement: the
`start` LUT gets a bound only before its first offer (H_START_ENV), and quiescence ignores
it afterwards.
-/

namespace Formal.Net.CapNet.Live
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd

/-- Generic form: a protocol channel whose request is driven by a `bd_src` LUT with a settle
bound `H`, and which is offered at most once, never closes its token. -/
theorem src_once_never_closes (c : Chan) (H : Nat) (hp : Protocol c)
    (hbnd : ∀ t, Win H t (fun u => c.ack u = false) → Ev H t (fun u => c.req u = true))
    (hone : ∀ t, cnt (riseB c.req) t ≤ 1) : ∀ t, fallB c.ack t = false := by
  intro t
  cases hf : fallB c.ack t with
  | false => rfl
  | true =>
    exfalso
    have ha : c.ack t = true ∧ c.ack (t + 1) = false := by
      simp [fallB] at hf; exact hf
    have hrt : c.req t = false := by
      have := (hp.2 t).2 (by rw [ha.1, ha.2]; decide)
      rw [ha.1] at this; cases h : c.req t <;> simp_all
    have hr1 : c.req (t + 1) = false := by
      cases h : c.req (t + 1)
      · rfl
      · have := (hp.2 t).1 (by rw [h, hrt]; decide)
        rw [hrt, ha.1] at this; cases this
    -- one rise already happened before `t + 1`
    have hc1 : 1 ≤ cnt (riseB c.req) (t + 1) := by
      have h := rise_inv hp (t + 1)
      have h2 : cnt (fallB c.ack) (t + 1) = cnt (fallB c.ack) t + 1 := cnt_succ_of hf
      omega
    -- from `t + 1` on, both wires stay low
    have low : ∀ u, t + 1 ≤ u → c.req u = false ∧ c.ack u = false := by
      intro u hu
      induction u with
      | zero => omega
      | succ u ih =>
        rcases Nat.eq_or_lt_of_le hu with e | hlt
        · rw [← e]; exact ⟨hr1, ha.2⟩
        · obtain ⟨hq, hk⟩ := ih (by omega)
          constructor
          · cases h : c.req (u + 1)
            · rfl
            · have hr : riseB c.req u = true := by simp [riseB, hq, h]
              have := cnt_succ_of hr
              have hm := cnt_mono (riseB c.req) (show t + 1 ≤ u by omega)
              have := hone (u + 1)
              omega
          · cases h : c.ack (u + 1)
            · rfl
            · have := (hp.2 u).2 (by rw [h, hk]; decide)
              rw [hq, hk] at this; exact absurd rfl this
    obtain ⟨u, h1, _, hu⟩ := hbnd (t + 1) (fun u h1 _ => (low u h1).2)
    rw [(low u h1).1] at hu; cases hu

/-- **`gcd_hw_live`'s hypotheses force `start` to hang.** Under H_CELLS, H_BUNDLE,
H_START_ONCE and H_BOUNDED_DELAY exactly as `gcd_hw_live` states them, `start`'s acknowledge
never falls. -/
theorem start_never_closes (a b H : Nat) (ch : Fin NC → Chan) (itr : Itr)
    (H_CELLS : ∀ p : Fin NO, CellI ch (srcV a b) itr p (opAt p))
    (H_BUNDLE : ∀ c, Held (ch c))
    (H_START_ONCE : ∀ t, cnt (riseB (ch start).req) t ≤ 1)
    (H_BOUNDED_DELAY : ∀ p, ∀ g ∈ gatesK p (opAt p), BndG H (gsAt ch itr) g) :
    ∀ t, fallB (ch start).ack t = false := by
  have hC : ∀ p : Fin NO, Cell ch (srcV a b) (opAt p) := fun p => cellI_cell _ (H_CELLS p)
  have hP := gcd_hw_protocol a b ch hC H_BUNDLE start
  have hg := H_BOUNDED_DELAY (prodOf start)
  rw [prod_start] at hg
  have hb := hg (gw (fun s => s.rq start) (fun s => !s.ak start)) (by simp [gatesK])
  refine src_once_never_closes (ch start) H hP ?_ H_START_ONCE
  intro t hw
  exact hb true t (fun u h1 h2 => by
    show (!(ch start).ack u) = true
    rw [hw u h1 h2]; rfl)

end Formal.Net.CapNet.Live
