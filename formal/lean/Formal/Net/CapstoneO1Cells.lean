import Formal.Net.OpsSteer
import Formal.Net.OpsJoin

/-!
# Probe C-8q: per-cell offer counters (step 1 of the O1 simulation)

The causality counters that 8m's O1 plan needs, exported for the fork, join and steer gate
models (8f). Each is an exact count identity at every time `t` (both channels obeying the
four-phase protocol), from the cell's existing Boolean phase invariant:

* `fork_cnt`: `#offers(in) = #offers(out_i) + [in.req ∧ ¬out_i.req]` for every branch, so
  each branch is at most one token behind its input and never ahead;
* `join_cnt`: `#offers(in_i) = #offers(out) + [¬out.req ∧ ¬out.ack ∧ in_i.req]` for every
  input, so the output never runs ahead of any input;
* `steer_cnt`: `#(input offers routed to b) = #offers(out b) + [j.req ∧ sel = b ∧ ¬out_b.req]`.

The arbiter stage's counters are `CapstoneO1Stage.zc_eq` / `offer_pending` (and 8j's
`amerge_inv`); the link's are 8f's `link_out_le` / `link_capacity`. Not yet exported: mux,
3-way mux (only off the control spine, so the spine argument needs them only for values).
-/

namespace Formal.Net.Capstone.O1
open Formal.Net Formal.Net.Handshake Formal.Net.Ops

theorem fork_cnt {a : Chan} {os : List Chan} (F : Fork.Fork a os) (hpa : Protocol a)
    (hpo : ∀ o ∈ os, Protocol o) : ∀ o ∈ os, ∀ t,
    cnt (riseB a.req) t = cnt (riseB o.req) t + (if (a.req t && !o.req t) = true then 1 else 0) := by
  intro o ho t
  induction t with
  | zero => simp [cnt, hpa.1.1, (hpo o ho).1.1]
  | succ t ih =>
    have hi := Fork.fork_inv F hpa.1.1 (fun o ho => (hpo o ho).1.2) t
      (fun s _ => ⟨hpa.2 s, fun o ho => (hpo o ho).2 s⟩) o ho
    have := Fork.fcnt_step _ _ _ _ _ _ _ _ hi ih (hpa.2 t).1 (F.wire o ho t)
    simp only [cnt, riseB]
    exact this

theorem join_cnt {g : List Nat → Nat} {is : List Chan} {o : Chan} (J : Join.Join g is o)
    (hpo : Protocol o) (hpi : ∀ i ∈ is, Protocol i) : ∀ i ∈ is, ∀ t,
    cnt (riseB i.req) t =
      cnt (riseB o.req) t + (if (!o.req t && !o.ack t && i.req t) = true then 1 else 0) := by
  intro i hi t
  induction t with
  | zero => simp [cnt, (hpi i hi).1.1]
  | succ t ih =>
    have hv := Join.join_inv J hpo.1.2 (fun i hi => (hpi i hi).1.1) t
      (fun s _ => ⟨hpo.2 s, fun i hi => (hpi i hi).2 s⟩) i hi
    have := Join.jcnt_step _ _ _ _ _ _ _ _ _ hv ih (fun h => J.cel t h i hi) (hpo.2 t).2
      ((hpi i hi).2 t).1
    simp only [cnt, riseB]
    exact this

/-- Input offers of a steer whose select (at the offer) is `b`. -/
def selOff (sel : Nat → Bool) (j : Chan) (b : Bool) : Nat → Nat :=
  cnt (fun u => riseB j.req u && (sel (j.dat (u + 1)) == b))

theorem steer_cnt {sel : Nat → Bool} {f : Nat → Nat} {j : Chan} {out : Bool → Chan}
    (S : Steer.Steer sel f j out) (hpj : Protocol j) (hpo : ∀ b, Protocol (out b)) (hh : Held j) :
    ∀ b t, selOff sel j b t = cnt (riseB (out b).req) t +
      (if (j.req t && (sel (j.dat t) == b) && !(out b).req t) = true then 1 else 0) := by
  intro b t
  induction t with
  | zero => simp [selOff, cnt, hpj.1.1]
  | succ t ih =>
    have hv := Steer.steer_inv S hpj.1.1 (fun b => (hpo b).1.2) hh t
      (fun s _ => ⟨hpj.2 s, fun b => (hpo b).2 s⟩)
    have hsel : (j.req t || j.ack t) = true → (j.req (t + 1) || j.ack (t + 1)) = true →
        sel (j.dat (t + 1)) = sel (j.dat t) := fun h1 h2 => by rw [hh t h1 h2]
    have key := Steer.scnt_incr b _ _ _ _ _ _ _ _ _ _ ((out b).req (t + 1)) hv (hpj.2 t).1
      (by cases b <;> exact S.lut _ t) hsel
    have e : (if b then (out true).req t else (out false).req t) = (out b).req t := by cases b <;> rfl
    rw [e] at key
    simp only [selOff, cnt, riseB] at ih ⊢
    rw [ih]
    rw [Nat.add_assoc, Nat.add_assoc, Nat.add_comm (if (j.req t && _ && _) = true then 1 else 0)]
    exact congrArg (fun q => cnt (riseB (out b).req) t + q) key

end Formal.Net.Capstone.O1
