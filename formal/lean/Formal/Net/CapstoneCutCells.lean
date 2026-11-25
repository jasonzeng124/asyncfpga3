import Formal.Net.CapstoneO1Cells
import Formal.Net.CapstoneO1Stage
import Formal.Net.OpsLink

/-!
# Probe C-8r: strict causality of each spine cell, and the arbiter's data spec up to a time

Step 2 of 8q's plan needs, for every cell on the control spine, "an output offer at `t`
needs the input offer strictly before `t`", as a count inequality at one time:

* `fork_strict`: a branch rising at `t` has `#off(out)(t+1) ≤ #off(in)(t)`;
* `join_strict`: the same for every input of a join (`bjoin` included);
* `link_strict`: the same for a link (8l's 18-state table: a `req_out` rise needs `d = 1`
  and the input mid-transaction);
* `steer_strict`: output `b` rising at `t` has `#off(out b)(t+1) ≤` #input offers before `t`
  whose select was `b`.

Each is the 8q counter identity (`fork_cnt`, `join_cnt`, `steer_cnt`) at `t` plus the gate's
own guard at the rising step. The arbiter's version is 8q's `offer_pending`.

`amerge_data_upto` is 8l's `amerge_op_forced` with H_CM_FORCED needed only for the offers
made up to the offer being valued, so the forcing and the data refinement can be proved
together by induction on time.
-/

namespace Formal.Net.Capstone.Cut
open Formal.Net Formal.Net.Handshake Formal.Net.Ops
open Formal.Net.Capstone.O1

theorem rise_parts {s : Trace} {t : Nat} (h : riseB s t = true) : s t = false ∧ s (t + 1) = true := by
  simp [riseB] at h; exact h

theorem fork_strict {a : Chan} {os : List Chan} (F : Fork.Fork a os) (hpa : Protocol a)
    (hpo : ∀ o ∈ os, Protocol o) {o : Chan} (ho : o ∈ os) {t : Nat} (hr : riseB o.req t = true) :
    cnt (riseB o.req) (t + 1) ≤ cnt (riseB a.req) t := by
  have h := fork_cnt F hpa hpo o ho t
  obtain ⟨h0, h1⟩ := rise_parts hr
  have hw := F.wire o ho t (by rw [h0, h1]; decide)
  rw [h1] at hw
  rw [cnt_succ_of hr, h, h0, ← hw]; simp

theorem join_strict {g : List Nat → Nat} {is : List Chan} {o : Chan} (J : Join.Join g is o)
    (hpo : Protocol o) (hpi : ∀ i ∈ is, Protocol i) {i : Chan} (hi : i ∈ is) {t : Nat}
    (hr : riseB o.req t = true) :
    cnt (riseB o.req) (t + 1) ≤ cnt (riseB i.req) t := by
  have h := join_cnt J hpo hpi i hi t
  obtain ⟨h0, h1⟩ := rise_parts hr
  have ha := (off_idle hpo hr).2
  have hc := J.cel t (by rw [h0, h1]; decide) i hi
  rw [h1] at hc
  rw [cnt_succ_of hr, h, h0, ha, hc]; simp

theorem link_strict {i o : Chan} {c : Trace} (L : Link.Link i o c) (hpi : Protocol i)
    (hpo : Protocol o) {t : Nat} (hr : riseB o.req t = true) :
    cnt (riseB o.req) (t + 1) ≤ cnt (riseB i.req) t := by
  obtain ⟨d, q, _, h1, _, K⟩ := Link.link_step L hpi hpo t
  obtain ⟨h0, h1'⟩ := rise_parts hr
  have K4 := K.2.2.2.1
  simp only [Link.lst, h0, h1', Bool.not_false, Bool.true_and] at K4
  obtain ⟨_, _, hirt, _, hd, _⟩ := K4 trivial
  have hi := rise_inv hpi t
  simp only [inTx] at hi
  simp only [hirt, ite_true] at hi
  rw [cnt_succ_of hr]
  omega

theorem steer_strict {sel : Nat → Bool} {f : Nat → Nat} {j : Chan} {out : Bool → Chan}
    (S : Steer.Steer sel f j out) (hpj : Protocol j) (hpo : ∀ b, Protocol (out b)) (hh : Held j)
    (b : Bool) {t : Nat} (hr : riseB (out b).req t = true) :
    cnt (riseB (out b).req) (t + 1) ≤ selOff sel j b t := by
  have h := steer_cnt S hpj hpo hh b t
  obtain ⟨h0, h1⟩ := rise_parts hr
  have hl := S.lut b t (by rw [h0, h1]; decide)
  rw [h1] at hl
  rw [cnt_succ_of hr, h, h0, ← hl]; simp

/-- 8l's `amerge_op_forced`, data half, with the forcing needed only up to the offer time. -/
theorem amerge_data_upto {C : Type} [DecidableEq C] (ch : C → Chan) (cx cy cz : C) (g1 g2 : Trace)
    (M : CM.AMerge (ch cx) (ch cy) (ch cz) g1 g2) (hx : cx ≠ cz) (hy : cy ≠ cz) (ω : Nat → Bool)
    (hin : ∀ c ∈ [cx, cy], Protocol (ch c) ∧ Held (ch c))
    (hout : ∀ c ∈ [cz], Protocol (ch c) ∧ Held (ch c))
    {k r : Nat} (hoff : OffAt (ch cz) k r)
    (hF : ∀ j r', r' ≤ r → OffAt (ch cz) j r' → CM.winner (ch cz) j = ω j)
    (σ : C → Nat → Nat) (hag : Agree ch σ r) (hE : amergeOff (ch cz) ω cx cy cz σ) :
    σ cz k = (ch cz).dat (r + 1) := by
  classical
  obtain ⟨_, hd⟩ := CM.amerge_op ch cx cy cz g1 g2 M
  let W := CM.winner (ch cz)
  let Off : Nat → Prop := fun i => ∃ r', r' ≤ r ∧ OffAt (ch cz) i r'
  let σ' : C → Nat → Nat := fun c' i =>
    if c' = cz ∧ ¬ Off i then
      2 * (if W i then σ cy (cnt W i) else σ cx (cnt (fun j => !W j) i)) +
        Formal.Net.Ops.Mux.b2n (W i)
    else σ c' i
  have hsx : ∀ i, σ' cx i = σ cx i := by intro i; simp [σ', hx]
  have hsy : ∀ i, σ' cy i = σ cy i := by intro i; simp [σ', hy]
  have hsz : ∀ i, Off i → σ' cz i = σ cz i := by intro i hi; simp [σ', hi]
  have hforce : ∀ i, Off i → ∀ j, j ≤ i → W j = ω j := by
    intro i hi j hj
    obtain ⟨ri, hri, hoi⟩ := hi
    rcases Nat.lt_or_ge j i with hlt | hge
    · obtain ⟨e, he, hf, hc⟩ := CM.cnt_ge_aux (riseB (ch cz).req) ri j (by rw [hoi.2]; omega)
      exact hF j e (by omega) ⟨hf, hc⟩
    · have hji : j = i := by omega
      rw [hji]; exact hF i ri hri hoi
  have hE' : CM.amergeEq W cx cy cz σ' := by
    intro i
    by_cases ho : Off i
    · obtain ⟨ri, _, hoi⟩ := ho
      have h1 := (amergeAt_congr (cx := cx) (cy := cy) (cz := cz) (σ := σ)
        (hforce i ⟨ri, by assumption, hoi⟩)).2 (hE i ⟨ri, hoi⟩)
      unfold amergeAt at h1
      rw [hsz i ⟨ri, by assumption, hoi⟩, hsx, hsy, h1]
    · show σ' cz i = _
      simp only [σ', ho, not_false_eq_true, and_self, ite_true, hsx, hsy]
  have hag' : Agree ch σ' r := by
    intro c' i r' hr' ho'
    by_cases hc' : c' = cz
    · subst hc'; rw [hsz i ⟨r', by omega, ho'⟩]; exact hag _ i r' hr' ho'
    · have : σ' c' i = σ c' i := by simp [σ', hc']
      rw [this]; exact hag c' i r' hr' ho'
  have := hd hin hout cz (List.mem_singleton_self _) k r hoff σ' hag' hE'
  rw [← hsz k ⟨r, Nat.le_refl _, hoff⟩]; exact this

end Formal.Net.Capstone.Cut
