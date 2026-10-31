import Formal.Net.OpsWitness

/-!
# Probe C-8j (1, 4): the 8b gcd graph built from bdc's cells is live only at `a = 0`

`gcd_stuck`: under EVERY hypothesis of 8f's `gcd_circuit` (bundled as
`Witness.GcdHyps`) and the loop's entry condition, if `a ≠ 0` then `out.req`
never rises, so no result is ever latched (`gcd_no_token`). With
`Witness.gcd_witness` (a delivering run at `a = 0`), `gcd_circuit` is non-vacuous
exactly at `a = 0`: for every other input it holds because the circuit
deadlocks.

The reason is the acknowledge cycle of the data loop: the graph has no storage
between the loop header and the back edge, so

    hA.ack↑  needs hA2.ack↑ (fork C-tree)      needs jA.ack↑ (join ack wire)
             needs aT.ack↑ ∨ aF.ack↑ (steer OR) needs a1.ack↑ (fork C-tree)
             needs backA.ack↑ (sub's ack wire) needs hA.ack↑ (bd_mux: y_ack = C(j1, z_ack))

and `aF` is never requested because the loop's first token (`a ≠ 0`) is
steered to `aT`. So `hA`'s first transaction never closes (`gcd_loop_stuck`),
`hA` has one offer, hence (`join_data`/`fork_data`) `jB` has one offer, whose
condition is `a ≠ 0`, so `brB` never requests `out`.

This is 9's storage rule seen from the safety side: a cycle needs storage (9:
at least 3 stages and one token) to make progress. The theorem is the formal
form of 8f's remark that a cycle with no storage deadlocks.
-/

namespace Formal.Net.Ops.Live
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.Ops.Gcd
open Formal.Net.Ops.Fork Formal.Net.Ops.Join Formal.Net.Ops.Steer Formal.Net.Ops.Mux
open Formal.Net.Ops.Witness
open GC

theorem cnt_fall_zero {s : Trace} : ∀ t, (∀ u, u ≤ t → s u = false) → cnt (fallB s) t = 0 := by
  intro t
  induction t with
  | zero => intro _; rfl
  | succ t ih =>
    intro h
    simp only [cnt, ih (fun u hu => h u (by omega)), fallB, h t (by omega)]
    rfl

/-- A signal that only moves to the previous value of a signal that is low stays low. -/
theorem stay {x : Trace} {y : Bool} {t : Nat} (hx : x t = false) (hy : y = false)
    (h : x (t + 1) ≠ x t → x (t + 1) = y) : x (t + 1) = false := by
  cases hx1 : x (t + 1)
  · rfl
  · have := h (by rw [hx1, hx]; decide); rw [hx1, hy] at this; exact this

theorem stay' {x : Trace} {y : Bool} {t : Nat} (hx : x t = false) (hy : y = false)
    (h : x (t + 1) ≠ x t → y = x (t + 1)) : x (t + 1) = false :=
  stay hx hy (fun hne => (h hne).symm)

section
variable (a b : Nat) (ch : GC → Chan) (j0A j1A j0B j1B : Trace)

theorem hyps_ops (H : GcdHyps a b ch j0A j1A j0B j1B) : ∀ o, OpProto ch (net.ins o) (net.outs o) ∧
    OpData ch (net.ins o) (net.outs o) (E a b o) := by
  intro o
  cases o
  · exact H.H_SRCA
  · exact H.H_SRCB
  · exact mux_op ch sA inA backA hA j0A j1A H.H_MUXA
  · exact mux_op ch sB inB backB hB j0B j1B H.H_MUXB
  · exact fork_op ch hA [hA1, hA2] H.H_FORKA
  · exact join_op ch [hA1] cnd H.H_ISNZ
  · exact fork_op ch cnd [cA, cB, sA', sB'] H.H_FORKC
  · exact H.H_INITBUFA
  · exact H.H_INITBUFB
  · exact join_op ch [cA, hA2] jA H.H_JOINA
  · exact steer_op ch jA coutA H.H_BRA
  · exact join_op ch [cB, hB] jB H.H_JOINB
  · exact steer_op ch jB coutB H.H_BRB
  · exact sink_op ch aF H.H_SNKA
  · exact fork_op ch aT [a1, a2] H.H_FORKAT
  · exact fork_op ch bT [b1, b2] H.H_FORKBT
  · exact join_op ch [a1, b1] backA H.H_SUB
  · exact join_op ch [a2, b2] backB H.H_MIN
  · exact ⟨H.H_ENV_OUT, fun _ _ c hc => by cases hc⟩

end

/-- The loop's data acknowledge cycle never fires: `hA`'s first token is never
acknowledged (and neither is anything on the cycle), for `a ≠ 0`. -/
theorem gcd_loop_stuck (a b : Nat) (hb : b % 2 = 1) (ha : a % 2 = 1)
    (ch : GC → Chan) (j0A j1A j0B j1B : Trace) (H : GcdHyps a b ch j0A j1A j0B j1B) :
    ∀ t, (ch hA).ack t = false ∧ (ch hA2).ack t = false ∧ (ch jA).ack t = false ∧
      (ch aT).ack t = false ∧ (ch a1).ack t = false ∧ (ch backA).ack t = false ∧
      (ch aF).req t = false ∧ (ch aF).ack t = false := by
  have hops := hyps_ops a b ch j0A j1A j0B j1B H
  have hp := net_protocol net ch (fun o => (hops o).1) H.H_BUNDLE
  obtain ⟨N, h1, h2, _⟩ := loop_N _ _ _ _ (Kahn.Gcd.cLoop_gcd (a + b + 1) a b (by omega) hb (Or.inr ha))
  have hv := net_refines net ch (E a b) (fun o => (hops o).1) H.H_BUNDLE (fun o => (hops o).2)
    (refS a b N) (refS_solves a b N h1 h2)
  have ha0 : a ≠ 0 := by omega
  have all : ∀ t, ∀ u, u ≤ t → (ch hA).ack u = false ∧ (ch hA2).ack u = false ∧
      (ch jA).ack u = false ∧ (ch aT).ack u = false ∧ (ch a1).ack u = false ∧
      (ch backA).ack u = false ∧ (ch aF).req u = false ∧ (ch aF).ack u = false := by
    intro t
    induction t with
    | zero =>
      intro u hu
      have : u = 0 := by omega
      subst this
      exact ⟨(hp hA).1.2, (hp hA2).1.2, (hp jA).1.2, (hp aT).1.2, (hp a1).1.2, (hp backA).1.2,
        (hp aF).1.1, (hp aF).1.2⟩
    | succ t ih =>
      intro u hu
      rcases Nat.lt_or_ge u (t + 1) with hlt | hge
      · exact ih u (by omega)
      have hu' : u = t + 1 := by omega
      subst hu'
      obtain ⟨i1, i2, i3, i4, i5, i6, i7, i8⟩ := ih t (Nat.le_refl _)
      -- jA's open transaction (if any) is its first token, steered to aT
      have hsel : (ch jA).req t = true → selE ((ch jA).dat t) = true := by
        intro hq
        obtain ⟨r, k, hr, ho, _, hcf, _⟩ := open_offer (hp jA) hq
        have hk : k = 0 := by
          rw [cnt_fall_zero t (fun u hu => (ih u hu).2.2.1)] at hcf; omega
        subst hk
        rw [held_at (hp jA) (H.H_BUNDLE jA) ho hr hcf, ← hv jA 0 r ho]
        simp [refS, gEnc, cndS, A, it, ph, selE, ha0]
      refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
      · exact stay' i1 i2 (fun hne => H.H_FORKA.cel t hne (ch hA2) m1)
      · exact stay i2 i3 (H.H_JOINA.wire (ch hA2) m1 t)
      · exact stay i3 (show ((ch aT).ack t || (ch aF).ack t) = false by rw [i4, i8]; rfl)
          (H.H_BRA.orr t)
      · exact stay' i4 i5 (fun hne => H.H_FORKAT.cel t hne (ch a1) m0)
      · exact stay i5 i6 (H.H_SUB.wire (ch a1) m0 t)
      · exact stay' i6 i1 (fun hne => (H.H_MUXA.ya t hne).2)
      · have hl := H.H_BRA.lut false t
        refine stay (x := (ch aF).req) i7 ?_ hl
        cases hq : (ch jA).req t
        · rfl
        · rw [hsel hq]; rfl
      · exact stay i8 i7 (H.H_SNKA.wire t)
  exact fun t => all t t (Nat.le_refl _)

/-- For `a ≠ 0` (with the entry condition: `a`, `b` odd) the 8b gcd graph built
from bdc's cells never requests `out`: no run satisfying the hypotheses of
`gcd_circuit` delivers a result. -/
theorem gcd_stuck (a b : Nat) (hb : b % 2 = 1) (ha : a % 2 = 1)
    (ch : GC → Chan) (j0A j1A j0B j1B : Trace) (H : GcdHyps a b ch j0A j1A j0B j1B) :
    ∀ t, (ch out).req t = false := by
  have hops := hyps_ops a b ch j0A j1A j0B j1B H
  have hp := net_protocol net ch (fun o => (hops o).1) H.H_BUNDLE
  obtain ⟨N, h1, h2, _⟩ := loop_N _ _ _ _ (Kahn.Gcd.cLoop_gcd (a + b + 1) a b (by omega) hb (Or.inr ha))
  have hv := net_refines net ch (E a b) (fun o => (hops o).1) H.H_BUNDLE (fun o => (hops o).2)
    (refS a b N) (refS_solves a b N h1 h2)
  have ha0 : a ≠ 0 := by omega
  have stuck := gcd_loop_stuck a b hb ha ch j0A j1A j0B j1B H
  -- hA is offered once
  have hAone : ∀ k r, OffAt (ch hA) k r → k = 0 := by
    intro k r ho
    have := off_falls (hp hA) ho
    rw [cnt_fall_zero r (fun u _ => (stuck u).1)] at this; omega
  -- so is jB: its k-th offer needs the k-th offer of cB, cnd, hA1, hA
  have hjB : ∀ k r, OffAt (ch jB) k r → k = 0 := by
    intro k r ho
    obtain ⟨r1, _, o1, _⟩ := join_data H.H_JOINB (hp jB)
      (fun i hi => by rcases mem2 hi with rfl | rfl <;> exact hp _)
      (fun i hi => by rcases mem2 hi with rfl | rfl <;> exact H.H_BUNDLE _) k r ho (ch cB) m0
    obtain ⟨r2, _, o2, _⟩ := fork_data H.H_FORKC (hp cnd)
      (fun i hi => by rcases mem4 hi with rfl | rfl | rfl | rfl <;> exact hp _)
      (H.H_BUNDLE cnd) (ch cB) m1 k r1 o1
    obtain ⟨r3, _, o3, _⟩ := join_data H.H_ISNZ (hp cnd)
      (fun i hi => by rw [mem1 hi]; exact hp _)
      (fun i hi => by rw [mem1 hi]; exact H.H_BUNDLE _) k r2 o2 (ch hA1) m0
    obtain ⟨r4, _, o4, _⟩ := fork_data H.H_FORKA (hp hA)
      (fun i hi => by rcases mem2 hi with rfl | rfl <;> exact hp _)
      (H.H_BUNDLE hA) (ch hA1) m0 k r3 o3
    exact hAone k r4 o4
  intro t
  induction t with
  | zero => exact (hp out).1.1
  | succ t ih =>
    have hl := H.H_BRB.lut false t
    refine stay (x := (ch out).req) ih ?_ hl
    cases hq : (ch jB).req t
    · rfl
    · obtain ⟨r, k, hr, ho, _, hcf, _⟩ := open_offer (hp jB) hq
      have hk := hjB k r ho
      subst hk
      have hs : selE ((ch jB).dat t) = true := by
        rw [held_at (hp jB) (H.H_BUNDLE jB) ho hr hcf, ← hv jB 0 r ho]
        simp [refS, gEnc, cndS, A, B, it, ph, selE, ha0]
      rw [hs]; rfl

/-- Hence no token is ever latched on `out` for `a ≠ 0`. -/
theorem gcd_no_token (a b : Nat) (hb : b % 2 = 1) (ha : a % 2 = 1)
    (ch : GC → Chan) (j0A j1A j0B j1B : Trace) (H : GcdHyps a b ch j0A j1A j0B j1B) :
    ∀ k e, ¬ TokAt (ch out) k e := by
  intro k e h
  have hops := hyps_ops a b ch j0A j1A j0B j1B H
  have hp := net_protocol net ch (fun o => (hops o).1) H.H_BUNDLE
  obtain ⟨r, _, ho⟩ := tok_off (hp out) h
  have := ho.1
  simp [riseB, gcd_stuck a b hb ha ch j0A j1A j0B j1B H (r + 1)] at this

end Formal.Net.Ops.Live
