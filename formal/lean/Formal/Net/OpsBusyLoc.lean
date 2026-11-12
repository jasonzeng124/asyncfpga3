import Formal.Net.OpsBusy
import Formal.Net.CapstoneBundle

/-!
# Probe C-8x2: relaxed cells are Ops operators; structural bundling on the relaxed model

* `loc_*`, `cellB_loc`: each relaxed cell, with its output buses re-labelled at idle instants
  (`modC`), meets the OLD gate model; the re-labelling equals the real bus whenever the output
  is busy (the link needs the protocol on its two channels for this).
* `cell_proto_B`, `cell_op_B`: `OpProto` / `OpData` (same token equations `Eqn`) for every
  relaxed cell kind.
* `forkB_held`, `joinB_held`, `steerB_held`, `linkB_held`, `srcB_held`: on the relaxed model,
  bundled inputs give a bundled output (no all-time data field needed).
-/

namespace Formal.Net.OpsBusy
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet

variable {n : Nat}

/-! ## Per kind: relaxed cell ⇒ old cell on the re-labelled trace -/

theorem loc_fork (ch : Fin n → Chan) (i : Fin n) (os : List (Fin n)) (B : ForkB (ch i) (os.map ch))
    (hi : i ∉ os) :
    Fork.Fork (modC ch os (fun _ => (ch i).dat) i) (os.map (modC ch os (fun _ => (ch i).dat))) ∧
    AgrOut ch os (fun _ => (ch i).dat) := by
  have ha : modC ch os (fun _ => (ch i).dat) i = ch i := modC_out hi
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro h; apply B.ne; cases os with
    | nil => rfl
    | cons _ _ => simp at h
  · intro o ho t h
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho
    exact B.wire (ch c) (List.mem_map_of_mem hc) t h
  · intro t h o ho
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho
    exact B.cel t h (ch c) (List.mem_map_of_mem hc)
  · intro o ho t
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho
    rw [modC_in hc, ha]
  · exact B.initA
  · intro o ho; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 ho
    exact B.initO (ch c) (List.mem_map_of_mem hc)
  · intro c hc t h; exact (B.dat (ch c) (List.mem_map_of_mem hc) t h).symm

theorem loc_join (ch : Fin n → Chan) (g : List Nat → Nat) (ins : List (Fin n)) (o : Fin n)
    (B : JoinB g (ins.map ch) (ch o)) (hd : ∀ c ∈ ins, c ∉ [o]) :
    Join.Join g (ins.map (modC ch [o] (fun _ t => g (ins.map (fun i => (ch i).dat t)))))
      (modC ch [o] (fun _ t => g (ins.map (fun i => (ch i).dat t))) o) ∧
    AgrOut ch [o] (fun _ t => g (ins.map (fun i => (ch i).dat t))) := by
  refine ⟨⟨?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro h; apply B.ne; cases ins with
    | nil => rfl
    | cons _ _ => simp at h
  · intro t h i hi
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hi
    exact B.cel t h (ch c) (List.mem_map_of_mem hc)
  · intro i hi t h
    obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hi
    exact B.wire (ch c) (List.mem_map_of_mem hc) t h
  · intro t
    rw [modC_in (List.mem_singleton_self o), List.map_map]
    show g (ins.map (fun i => (ch i).dat t)) = _
    congr 1
    apply List.map_congr_left
    intro c hc
    simp only [Function.comp, modC_out (hd c hc)]
  · exact B.initO
  · intro i hi; obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hi
    exact B.initI (ch c) (List.mem_map_of_mem hc)
  · intro c hc t h
    rw [List.mem_singleton.1 hc] at h ⊢
    rw [B.dat t h, List.map_map]; rfl

theorem bif_mem (b : Bool) (t f : Fin n) : (bif b then t else f) ∈ [t, f] := by
  cases b <;> simp

theorem loc_steer (ch : Fin n → Chan) (sel : Nat → Bool) (fv : Nat → Nat) (j t f : Fin n)
    (B : SteerB sel fv (ch j) (fun b => ch (bif b then t else f))) (hd : j ∉ [t, f]) :
    Steer.Steer sel fv (modC ch [t, f] (fun _ u => fv ((ch j).dat u)) j)
      (fun b => modC ch [t, f] (fun _ u => fv ((ch j).dat u)) (bif b then t else f)) ∧
    AgrOut ch [t, f] (fun _ u => fv ((ch j).dat u)) := by
  have ha : modC ch [t, f] (fun _ u => fv ((ch j).dat u)) j = ch j := modC_out hd
  refine ⟨⟨?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · intro b u h; rw [ha]; exact B.lut b u h
  · intro u h; exact B.orr u h
  · intro b u; rw [modC_in (bif_mem b t f), ha]
  · exact B.initJ
  · intro b; exact B.initO b
  · intro c hc u h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with e | e <;> subst e
    · exact (B.dat true u h).symm
    · exact (B.dat false u h).symm

theorem loc_mux (ch : Fin n → Chan) (sel : Nat → Bool) (c x y z : Fin n) (j0 j1 : Trace)
    (B : MuxB sel (ch x) (ch y) (ch c) (ch z) j0 j1) (hc : c ∉ [z]) (hx : x ∉ [z])
    (hy : y ∉ [z]) :
    Mux.Mux sel (modC ch [z] (fun _ u => if sel ((ch c).dat u) then (ch y).dat u else (ch x).dat u) x)
      (modC ch [z] (fun _ u => if sel ((ch c).dat u) then (ch y).dat u else (ch x).dat u) y)
      (modC ch [z] (fun _ u => if sel ((ch c).dat u) then (ch y).dat u else (ch x).dat u) c)
      (modC ch [z] (fun _ u => if sel ((ch c).dat u) then (ch y).dat u else (ch x).dat u) z) j0 j1 ∧
    AgrOut ch [z] (fun _ u => if sel ((ch c).dat u) then (ch y).dat u else (ch x).dat u) := by
  rw [modC_out hc, modC_out hx, modC_out hy]
  refine ⟨⟨B.cj0, B.cj1, B.zr, B.xa, B.ya, B.ca, ?_, B.i0, B.i1, B.iz, B.ix, B.iy, B.ic⟩, ?_⟩
  · intro u; rw [modC_in (List.mem_singleton_self z)]
  · intro c' hc' u h
    rw [List.mem_singleton.1 hc'] at h ⊢
    exact (B.dat u h).symm

theorem cx3_mem (x0 x1 x2 : Fin n) (k : Nat) : cx3 x0 x1 x2 k ∈ [x0, x1, x2] := by
  match k with
  | 0 => simp [cx3]
  | 1 => simp [cx3]
  | _ + 2 => simp [cx3]

theorem loc_muxn (ch : Fin n → Chan) (sel : Nat → Nat) (c x0 x1 x2 z : Fin n) (j : Nat → Trace)
    (B : MuxNB sel (fun k => ch (cx3 x0 x1 x2 k)) (ch c) (ch z) j) (hc : c ∉ [z])
    (hx : ∀ k, cx3 x0 x1 x2 k ∉ [z]) :
    MuxN.MuxN sel
      (fun k => modC ch [z] (fun _ u => if sel ((ch c).dat u) < 3 then
        (ch (cx3 x0 x1 x2 (sel ((ch c).dat u)))).dat u else (ch z).dat u) (cx3 x0 x1 x2 k))
      (modC ch [z] (fun _ u => if sel ((ch c).dat u) < 3 then
        (ch (cx3 x0 x1 x2 (sel ((ch c).dat u)))).dat u else (ch z).dat u) c)
      (modC ch [z] (fun _ u => if sel ((ch c).dat u) < 3 then
        (ch (cx3 x0 x1 x2 (sel ((ch c).dat u)))).dat u else (ch z).dat u) z) j ∧
    AgrOut ch [z] (fun _ u => if sel ((ch c).dat u) < 3 then
        (ch (cx3 x0 x1 x2 (sel ((ch c).dat u)))).dat u else (ch z).dat u) := by
  have hxs : ∀ k, modC ch [z] (fun _ u => if sel ((ch c).dat u) < 3 then
        (ch (cx3 x0 x1 x2 (sel ((ch c).dat u)))).dat u else (ch z).dat u) (cx3 x0 x1 x2 k) =
      ch (cx3 x0 x1 x2 k) := fun k => modC_out (hx k)
  refine ⟨⟨?_, B.zr, ?_, ?_, ?_, B.ij, B.iz, ?_, ?_⟩, ?_⟩
  · intro k hk u h; simp only [hxs, modC_out hc]; exact B.cj k hk u h
  · intro k hk u h; simp only [hxs]; exact B.xa k hk u h
  · intro u h; rw [modC_out hc]; exact B.ca u h
  · intro u; simp only [hxs, modC_out hc]; intro h3
    rw [modC_in (List.mem_singleton_self z)]; simp [h3]
  · intro k hk; simp only [hxs]; exact B.ix k hk
  · rw [modC_out hc]; exact B.ic
  · intro c' hc' u h
    rw [List.mem_singleton.1 hc'] at h ⊢
    by_cases h3 : sel ((ch c).dat u) < 3
    · simp only [h3, ite_true]; exact (B.dat u h h3).symm
    · simp only [h3, ite_false]

theorem loc_amerge (ch : Fin n → Chan) (x y z : Fin n) (g1 g2 : Trace)
    (B : AMergeB (ch x) (ch y) (ch z) g1 g2) (hx : x ∉ [z]) (hy : y ∉ [z]) :
    CM.AMerge (modC ch [z] (fun _ u => 2 * (if (g2 u || (ch y).ack u) then (ch y).dat u else (ch x).dat u)
        + Mux.b2n (g2 u || (ch y).ack u)) x)
      (modC ch [z] (fun _ u => 2 * (if (g2 u || (ch y).ack u) then (ch y).dat u else (ch x).dat u)
        + Mux.b2n (g2 u || (ch y).ack u)) y)
      (modC ch [z] (fun _ u => 2 * (if (g2 u || (ch y).ack u) then (ch y).dat u else (ch x).dat u)
        + Mux.b2n (g2 u || (ch y).ack u)) z) g1 g2 ∧
    AgrOut ch [z] (fun _ u => 2 * (if (g2 u || (ch y).ack u) then (ch y).dat u else (ch x).dat u)
        + Mux.b2n (g2 u || (ch y).ack u)) := by
  rw [modC_out hx, modC_out hy]
  refine ⟨⟨B.H_ARB1, B.H_ARB2, B.H_ARB_EXCL, B.zr, B.H_AMERGE_RTZ, B.xa, B.ya, ?_, B.i1, B.i2,
    B.iz, B.ix, B.iy⟩, ?_⟩
  · intro u; rw [modC_in (List.mem_singleton_self z)]
  · intro c' hc' u h
    rw [List.mem_singleton.1 hc'] at h ⊢
    exact (B.dat u h).symm

/-- The zero-delay latch content: transparent while `c` is high, holding otherwise. -/
def latchD (c : Trace) (di dO : Nat → Nat) : Nat → Nat
  | 0 => if c 0 = true then di 0 else dO 0
  | t + 1 => if c (t + 1) = true then di (t + 1) else latchD c di dO t

theorem loc_link (ch : Fin n → Chan) (i o : Fin n) (c : Trace) (B : LinkB (ch i) (ch o) c)
    (hd : i ∉ [o]) :
    Link.Link (modC ch [o] (fun _ => latchD c (ch i).dat (ch o).dat) i)
      (modC ch [o] (fun _ => latchD c (ch i).dat (ch o).dat) o) c ∧
    (Protocol (ch i) → Protocol (ch o) → AgrOut ch [o] (fun _ => latchD c (ch i).dat (ch o).dat)) := by
  have ha : modC ch [o] (fun _ => latchD c (ch i).dat (ch o).dat) i = ch i := modC_out hd
  have L : Link.Link (modC ch [o] (fun _ => latchD c (ch i).dat (ch o).dat) i)
      (modC ch [o] (fun _ => latchD c (ch i).dat (ch o).dat) o) c := by
    rw [ha]
    refine ⟨B.H_CEL_SI, B.H_ACK_DI, B.H_REQ_DI, ?_, ?_, B.ic, B.ii, B.io⟩
    · intro t h
      rw [modC_in (List.mem_singleton_self o)]
      cases t with
      | zero => simp [latchD, h]
      | succ t => simp [latchD, h]
    · intro t h
      rw [modC_in (List.mem_singleton_self o), modC_in (List.mem_singleton_self o)]
      simp [latchD, h]
  refine ⟨L, fun hpi hpo => ?_⟩
  have hpi' : Protocol (modC ch [o] (fun _ => latchD c (ch i).dat (ch o).dat) i) := by
    rw [ha]; exact hpi
  have key : ∀ t, inTx (ch o) t = true → latchD c (ch i).dat (ch o).dat t = (ch o).dat t := by
    intro t
    induction t with
    | zero => intro h; simp [inTx, hpo.1.1, hpo.1.2] at h
    | succ t ih =>
      intro h1
      cases hc : c (t + 1)
      · have h0 : inTx (ch o) t = true := by
          cases h0 : inTx (ch o) t
          · exfalso
            simp only [inTx, Bool.or_eq_false_iff] at h0
            have hack : (ch o).ack (t + 1) = false := by
              cases hA : (ch o).ack (t + 1)
              · rfl
              · exfalso
                have := (hpo.2 t).2 (by rw [hA, h0.2]; decide)
                exact this (by rw [h0.1, h0.2])
            have hreq : (ch o).req (t + 1) = true := by
              simp only [inTx, hack, Bool.or_false] at h1; exact h1
            obtain ⟨d, q, _, _, _, K⟩ := Link.link_step L hpi' hpo t
            have K4 := K.2.2.2.1
            simp only [Link.lst, modC_req, h0.1, hreq, Bool.not_false, Bool.true_and] at K4
            have := (K4 trivial).2.1
            rw [hc] at this; exact absurd this (by decide)
          · rfl
        simp only [latchD, hc, Bool.false_eq_true, ite_false]
        rw [ih h0, B.H_LATCH_HOLD_B t hc h0 h1]
      · simp only [latchD, hc, ite_true]
        exact (B.H_LATCH_OPEN_B (t + 1) hc h1).symm
  intro c' hc' t h
  rw [List.mem_singleton.1 hc'] at h ⊢
  exact key t h

theorem loc_src (ch : Fin n → Chan) (z : Fin n) (v : Nat) (B : SrcB (ch z) v) :
    Capstone.Src (modC ch [z] (fun _ _ => v) z) v ∧ AgrOut ch [z] (fun _ _ => v) := by
  refine ⟨⟨B.H_LUT_SI, ?_, B.iz⟩, ?_⟩
  · intro t; rw [modC_in (List.mem_singleton_self z)]
  · intro c hc t h
    rw [List.mem_singleton.1 hc] at h ⊢
    exact (B.dat t h).symm

theorem busy_of_rise {c : Chan} {r : Nat} (h : riseB c.req r = true) : inTx c (r + 1) = true := by
  simp [riseB] at h; simp [inTx, h.2]

theorem forced_mod_amerge {ch : Fin n → Chan} {om : Nat → Nat → Bool} {x y z : Fin n} {w : Nat}
    (D : Fin n → Nat → Nat) (hA : AgrOut ch [z] D) (hf : Forced ch om (.amerge x y z w)) :
    Forced (modC ch [z] D) om (.amerge x y z w) := by
  intro k r hoff
  have e : CM.winner (modC ch [z] D z) k = CM.winner (ch z) k :=
    winner_congr (c := ch z) (c' := modC ch [z] D z) rfl (fun r hr => by
      rw [modC_in (List.mem_singleton_self z)]
      exact hA z (List.mem_singleton_self z) (r + 1) (busy_of_rise hr)) k
  rw [e]; exact hf k r hoff

/-! ## Dispatch -/

theorem cellB_loc (ch : Fin n → Chan) (sv : Nat → Nat) (om : Nat → Nat → Bool) (k : K n)
    (hc : CellB ch sv k) (hj : Disj k) :
    ∃ D, Cell (modC ch k.outsC D) sv k ∧ (Forced ch om k → Forced (modC ch k.outsC D) om k) ∧
      ((∀ c ∈ k.insC, Protocol (ch c)) → (∀ c ∈ k.outsC, Protocol (ch c)) → AgrOut ch k.outsC D) := by
  cases k with
  | forkG i os =>
    have := loc_fork ch i os hc (hj i (by simp [K.insC]))
    exact ⟨_, this.1, fun _ => trivial, fun _ _ => this.2⟩
  | forkH i os l h d hs =>
    have := loc_fork ch i (os.map Prod.fst) hc (hj i (by simp [K.insC]))
    exact ⟨_, this.1, fun _ => trivial, fun _ _ => this.2⟩
  | join ins o e js jw =>
    have := loc_join ch (jg e js) ins o hc (fun c hc' => hj c hc')
    exact ⟨_, this.1, fun _ => trivial, fun _ _ => this.2⟩
  | bjoin ins o ec ed =>
    have := loc_join ch (bg ec ed) ins o hc (fun c hc' => hj c hc')
    exact ⟨_, this.1, fun _ => trivial, fun _ _ => this.2⟩
  | steerC j t f =>
    have := loc_steer ch sel2 (fun _ => 0) j t f hc (hj j (by simp [K.insC]))
    exact ⟨_, this.1, fun _ => trivial, fun _ _ => this.2⟩
  | steerD j t f fd sw =>
    have := loc_steer ch sel2 (fun v => fd.eval [v / 2]) j t f hc (hj j (by simp [K.insC]))
    exact ⟨_, this.1, fun _ => trivial, fun _ _ => this.2⟩
  | mux c x y z mw =>
    obtain ⟨j0, j1, B⟩ := hc
    have := loc_mux ch sel2 c x y z j0 j1 B (hj c (by simp [K.insC])) (hj x (by simp [K.insC]))
      (hj y (by simp [K.insC]))
    exact ⟨_, ⟨j0, j1, this.1⟩, fun _ => trivial, fun _ _ => this.2⟩
  | muxn c x0 x1 x2 z nw =>
    obtain ⟨j, B⟩ := hc
    have hx : ∀ k, cx3 x0 x1 x2 k ∉ [z] := by
      intro k
      have hm := cx3_mem x0 x1 x2 k
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      rcases hm with e | e | e <;> rw [e] <;> exact hj _ (by simp [K.insC])
    have := loc_muxn ch selD c x0 x1 x2 z j B (hj c (by simp [K.insC])) hx
    exact ⟨_, ⟨j, this.1⟩, fun _ => trivial, fun _ _ => this.2⟩
  | amerge x y z w =>
    obtain ⟨g1, g2, B⟩ := hc
    have := loc_amerge ch x y z g1 g2 B (hj x (by simp [K.insC])) (hj y (by simp [K.insC]))
    exact ⟨_, ⟨g1, g2, this.1⟩, forced_mod_amerge _ this.2, fun _ _ => this.2⟩
  | link i o =>
    obtain ⟨c, B⟩ := hc
    have := loc_link ch i o c B (hj i (by simp [K.insC]))
    exact ⟨_, ⟨c, this.1⟩, fun _ => trivial, fun hp hq =>
      this.2 (hp i (by simp [K.insC])) (hq o (by simp [K.outsC]))⟩
  | src z which d =>
    have := loc_src ch z (sv which) hc
    exact ⟨_, this.1, fun _ => trivial, fun _ _ => this.2⟩
  | sink i =>
    refine ⟨fun _ => (ch i).dat, ?_, fun _ => trivial, fun _ _ c hc => by simp [K.outsC] at hc⟩
    show Ops.Gcd.Sink (modC ch [] _ i)
    rw [modC_out (List.not_mem_nil)]; exact hc

end Formal.Net.OpsBusy
