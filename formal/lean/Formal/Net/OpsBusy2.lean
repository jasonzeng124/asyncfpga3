import Formal.Net.OpsBusyHeld

/-!
# Probe C-8x3: the time-bounded operator protocol (`OpProtoT`)

8f's `OpProto` asks the inputs to be bundled (`Held`) at ALL times before it guarantees the
protocol at step `t`. The steer, mux and muxn really read their select input, but only at steps
before `t`: their state invariants (`steer_inv`, `mux_inv`, `muxn_inv`) are inductions from 0 to
`t` that use `Held` of the select only on the steps `s < t`. Here:

* `HeldStep c t`: `Held` at one step; `HeldTo c T`: at every step `s < T`.
* `steer_invT`, `mux_invT`, `muxn_invT`: the three invariants with `HeldTo` (same proofs).
* `OpProtoT`: `OpProto` with `HeldTo (ch c) t` in place of `Held (ch c)` (weaker premise, so a
  stronger operator spec); `OpProtoT.toOpProto`.
* `cell_protoT`: every OLD cell kind of the capstone network meets `OpProtoT`;
  `protoT_of_mod` / **`cell_protoT_B`**: so does every RELAXED cell (via C-8x2's `cellB_loc`).
-/

namespace Formal.Net.OpsBusy2
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.OpsBusy

/-- `Held` at one step. -/
def HeldStep (c : Chan) (t : Nat) : Prop :=
  inTx c t = true → inTx c (t + 1) = true → c.dat (t + 1) = c.dat t

/-- `Held` on every step before `T`. -/
def HeldTo (c : Chan) (T : Nat) : Prop := ∀ s, s < T → HeldStep c s

theorem heldTo_of_held {c : Chan} (h : Held c) (T : Nat) : HeldTo c T := fun s _ => h s

theorem held_of_steps {c : Chan} (h : ∀ t, HeldStep c t) : Held c := fun t => h t

theorem heldTo_mono {c : Chan} {T T' : Nat} (h : HeldTo c T') (hle : T ≤ T') : HeldTo c T :=
  fun s hs => h s (by omega)

/-! ## Bounded invariants of the three select-reading cells -/

section steer
open Formal.Net.Ops.Steer Formal.Net.Ops.Fork
variable {sel : Nat → Bool} {f : Nat → Nat} {j : Chan} {out : Bool → Chan}

theorem steer_invT (S : Steer sel f j out) (hjr : j.req 0 = false)
    (hk : ∀ b, (out b).ack 0 = false) : ∀ t, HeldTo j t →
    (∀ s, s < t → Rules j s ∧ ∀ b, Rules (out b) s) →
    SInv (j.req t) (j.ack t) (sel (j.dat t)) ((out true).req t) ((out true).ack t)
      ((out false).req t) ((out false).ack t) = true := by
  intro t
  induction t with
  | zero =>
    intro _ _
    have h1 := S.initO true; have h2 := S.initO false
    have h3 := hk true; have h4 := hk false
    simp only [SInv, hjr, S.initJ, h1, h2, h3, h4]
    cases sel (j.dat 0) <;> decide
  | succ t ih =>
    intro hh hp
    have h0 := ih (heldTo_mono hh (by omega)) (fun s hs => hp s (by omega))
    obtain ⟨⟨hj1, _⟩, hb⟩ := hp t (by omega)
    exact sinv_step _ _ _ _ _ _ _ _ _ _ _ _ _ _ h0 hj1 (S.lut true t) (S.lut false t) (S.orr t)
      (hb true).2 (hb false).2 (fun a b => by rw [hh t (by omega) a b])

theorem steer_protoT (S : Steer sel f j out) (hjr : j.req 0 = false)
    (hk : ∀ b, (out b).ack 0 = false) : ∀ t, HeldTo j t →
    (∀ s, s < t → Rules j s ∧ ∀ b, Rules (out b) s) →
    RecvStep j t ∧ ∀ b, SendStep (out b) t := by
  intro t hh hp
  have hi := steer_invT S hjr hk t hh hp
  refine ⟨fun h => sinv_recv _ _ _ _ _ _ _ _ hi (S.orr t) h, fun b h => ?_⟩
  cases b
  · exact sinv_sendF _ _ _ _ _ _ _ _ hi (S.lut false t) h
  · exact sinv_sendT _ _ _ _ _ _ _ _ hi (S.lut true t) h

end steer

section mux
open Formal.Net.Ops.Mux
variable {sel : Nat → Bool} {x y c z : Chan} {j0 j1 : Trace}

theorem mux_invT (M : Mux sel x y c z j0 j1) (hx : x.req 0 = false) (hy : y.req 0 = false)
    (hc : c.req 0 = false) (hz : z.ack 0 = false) : ∀ t, HeldTo c t →
    (∀ s, s < t → SendStep x s ∧ SendStep y s ∧ SendStep c s ∧ RecvStep z s) →
    ∃ dc dxo dyo, tbl.contains (st sel x y c z j0 j1 t dc dxo dyo) = true ∧
      cnt (riseB c.req) t = cnt (riseB z.req) t + dc ∧
      cnt (riseB x.req) t + 1 = cnt0 sel c t + dxo ∧
      cnt (riseB y.req) t + 1 = cnt1 sel c t + dyo := by
  intro t
  induction t with
  | zero =>
    intro _ _
    refine ⟨0, 1, 1, ?_, rfl, rfl, rfl⟩
    simp only [st, hx, hy, hc, hz, M.i0, M.i1, M.iz, M.ix, M.iy, M.ic]
    exact mux_init _
  | succ t ih =>
    intro hh hp
    obtain ⟨dc, dxo, dyo, hm, h1, h2, h3⟩ := ih (heldTo_mono hh (by omega)) (fun s hs => hp s (by omega))
    obtain ⟨sx, sy, sc, rz⟩ := hp t (by omega)
    have K := mux_closed _ (mem_of_contains hm) (x.req (t + 1)) sx (y.req (t + 1)) sy
      (c.req (t + 1)) sc (z.ack (t + 1)) rz (j0 (t + 1)) (M.cj0 t) (j1 (t + 1)) (M.cj1 t)
      (z.req (t + 1)) (M.zr t) (x.ack (t + 1)) (M.xa t) (y.ack (t + 1)) (M.ya t)
      (c.ack (t + 1)) (M.ca t) (sel (c.dat (t + 1)))
      (fun hne ⟨a1, a2⟩ => hne (by rw [hh t (by omega) a1 a2] <;> rfl))
    obtain ⟨Km, Kc, Kx, Ky, _⟩ := K
    refine ⟨_, _, _, Km, ?_, ?_, ?_⟩
    · have e1 : cnt (riseB c.req) (t + 1) = cnt (riseB c.req) t +
          b2n (!c.req t && c.req (t + 1)) := rfl
      have e2 : cnt (riseB z.req) (t + 1) = cnt (riseB z.req) t +
          b2n (!z.req t && z.req (t + 1)) := rfl
      simp only [st, nxt] at Kc ⊢
      omega
    · have e1 : cnt (riseB x.req) (t + 1) = cnt (riseB x.req) t +
          b2n (!x.req t && x.req (t + 1)) := rfl
      have e2 : cnt0 sel c (t + 1) = cnt0 sel c t +
          b2n (!c.req t && c.req (t + 1) && !sel (c.dat (t + 1))) := rfl
      simp only [st, nxt] at Kx ⊢
      omega
    · have e1 : cnt (riseB y.req) (t + 1) = cnt (riseB y.req) t +
          b2n (!y.req t && y.req (t + 1)) := rfl
      have e2 : cnt1 sel c (t + 1) = cnt1 sel c t +
          b2n (!c.req t && c.req (t + 1) && sel (c.dat (t + 1))) := rfl
      simp only [st, nxt] at Ky ⊢
      omega

theorem mux_protoT (M : Mux sel x y c z j0 j1) (hx : x.req 0 = false) (hy : y.req 0 = false)
    (hc : c.req 0 = false) (hz : z.ack 0 = false) : ∀ t, HeldTo c t →
    (∀ s, s < t → SendStep x s ∧ SendStep y s ∧ SendStep c s ∧ RecvStep z s) →
    RecvStep x t ∧ RecvStep y t ∧ RecvStep c t ∧ SendStep z t := by
  intro t hh hp
  obtain ⟨dc, dxo, dyo, hm, _⟩ := mux_invT M hx hy hc hz t hh hp
  exact mux_guar _ (mem_of_contains hm) (x.ack (t + 1)) (M.xa t) (y.ack (t + 1)) (M.ya t)
    (c.ack (t + 1)) (M.ca t) (z.req (t + 1)) (M.zr t)

end mux

section muxn
open Formal.Net.Ops.MuxN
variable {sel : Nat → Nat} {xs : Nat → Chan} {c z : Chan} {j : Nat → Trace}

theorem muxn_invT (M : MuxN sel xs c z j) (hx : ∀ k, k < 3 → (xs k).req 0 = false)
    (hc : c.req 0 = false) (hz : z.ack 0 = false) : ∀ t, HeldTo c t →
    (∀ s, s < t → (∀ k, k < 3 → SendStep (xs k) s) ∧ SendStep c s ∧ RecvStep z s) →
    mem (st sel xs c z j t) = true ∧
      cnt (riseB c.req) t = cnt (riseB z.req) t + dcOf (st sel xs c z j t) ∧
      ∀ k, k < 3 → cnt (riseB (xs k).req) t + 1 = cntk sel c k t + dkOf (st sel xs c z j t) k := by
  intro t
  induction t with
  | zero =>
    intro _ _
    have I := init_mem (clip (sel (c.dat 0))) (clip_lt _)
    simp only [st, hx 0 (by omega), hx 1 (by omega), hx 2 (by omega), hc, hz, M.iz,
      M.ix 0 (by omega), M.ix 1 (by omega), M.ix 2 (by omega), M.ic,
      M.ij 0 (by omega), M.ij 1 (by omega), M.ij 2 (by omega)]
    refine ⟨I.1, ?_, ?_⟩
    · rw [I.2.1]; rfl
    · intro k hk; rw [I.2.2 k hk]; rfl
  | succ t ih =>
    intro hh hp
    obtain ⟨hm, h1, h2⟩ := ih (heldTo_mono hh (by omega)) (fun s hs => hp s (by omega))
    obtain ⟨sx, sc, rz⟩ := hp t (by omega)
    have cjk : ∀ k, k < 3 → j k (t + 1) ≠ j k t →
        (xs k).req t = j k (t + 1) ∧ (c.req t && (clip (sel (c.dat t)) == k)) = j k (t + 1) := by
      intro k hk hne
      rw [clip_beq _ _ hk]; exact M.cj k hk t hne
    have K := closed_all _ (clip_lt (sel (c.dat t))) _ _ _ _ _ _ _ _ _ _ _ _ _ hm
      ((xs 0).req (t + 1)) (sx 0 (by omega)) ((xs 1).req (t + 1)) (sx 1 (by omega))
      ((xs 2).req (t + 1)) (sx 2 (by omega)) (c.req (t + 1)) sc (z.ack (t + 1)) rz
      (j 0 (t + 1)) (cjk 0 (by omega)) (j 1 (t + 1)) (cjk 1 (by omega))
      (j 2 (t + 1)) (cjk 2 (by omega)) (z.req (t + 1)) (M.zr t)
      ((xs 0).ack (t + 1)) (M.xa 0 (by omega) t) ((xs 1).ack (t + 1)) (M.xa 1 (by omega) t)
      ((xs 2).ack (t + 1)) (M.xa 2 (by omega) t) (c.ack (t + 1)) (M.ca t)
      (clip (sel (c.dat (t + 1)))) (clip_lt _)
      (fun hne ⟨a1, a2⟩ => hne (by rw [hh t (by omega) a1 a2]))
    obtain ⟨Km, Kc, K0, K1, K2, _⟩ := K
    refine ⟨Km, ?_, ?_⟩
    · have e1 : cnt (riseB c.req) (t + 1) = cnt (riseB c.req) t +
          b2n (!c.req t && c.req (t + 1)) := rfl
      have e2 : cnt (riseB z.req) (t + 1) = cnt (riseB z.req) t +
          b2n (!z.req t && z.req (t + 1)) := rfl
      simp only [st] at Kc h1 ⊢
      omega
    · have step : ∀ k, k < 3 →
          dkOf (st sel xs c z j (t + 1)) k + b2n (!c.req t && c.req (t + 1) &&
            (clip (sel (c.dat (t + 1))) == k)) =
          dkOf (st sel xs c z j t) k + b2n (!(xs k).req t && (xs k).req (t + 1)) :=
        cases3 K0 K1 K2
      intro k hk
      have sk := step k hk
      rw [clip_beq _ _ hk] at sk
      have e1 : cnt (riseB (xs k).req) (t + 1) = cnt (riseB (xs k).req) t +
          b2n (!(xs k).req t && (xs k).req (t + 1)) := rfl
      have e2 : cntk sel c k (t + 1) = cntk sel c k t +
          b2n (!c.req t && c.req (t + 1) && (sel (c.dat (t + 1)) == k)) := rfl
      have := h2 k hk
      omega

theorem muxn_protoT (M : MuxN sel xs c z j) (hx : ∀ k, k < 3 → (xs k).req 0 = false)
    (hc : c.req 0 = false) (hz : z.ack 0 = false) : ∀ t, HeldTo c t →
    (∀ s, s < t → (∀ k, k < 3 → SendStep (xs k) s) ∧ SendStep c s ∧ RecvStep z s) →
    (∀ k, k < 3 → RecvStep (xs k) t) ∧ RecvStep c t ∧ SendStep z t := by
  intro t hh hp
  obtain ⟨hm, _⟩ := muxn_invT M hx hc hz t hh hp
  have G := guar_all _ (clip_lt (sel (c.dat t))) _ _ _ _ _ _ _ _ _ _ _ _ _ hm
    (z.req (t + 1)) (M.zr t)
    ((xs 0).ack (t + 1)) (M.xa 0 (by omega) t) ((xs 1).ack (t + 1)) (M.xa 1 (by omega) t)
    ((xs 2).ack (t + 1)) (M.xa 2 (by omega) t) (c.ack (t + 1)) (M.ca t)
  obtain ⟨g0, g1, g2, gc, gz⟩ := G
  exact ⟨cases3 g0 g1 g2, gc, gz⟩

end muxn

/-! ## The bounded operator protocol -/

section ops
variable {C : Type}

/-- `OpProto` with the inputs bundled only on the steps before `t`. -/
structure OpProtoT (ch : C → Chan) (ins outs : List C) : Prop where
  ag : ∀ t, (∀ c ∈ ins, Init (ch c)) → (∀ c ∈ outs, Init (ch c)) → (∀ c ∈ ins, HeldTo (ch c) t) →
       (∀ s, s < t → (∀ c ∈ ins, Rules (ch c) s) ∧ (∀ c ∈ outs, Rules (ch c) s)) →
       (∀ c ∈ ins, RecvStep (ch c) t) ∧ (∀ c ∈ outs, SendStep (ch c) t)
  initIn : ∀ c ∈ ins, (ch c).ack 0 = false
  initOut : ∀ c ∈ outs, (ch c).req 0 = false

theorem OpProtoT.toOpProto {ch : C → Chan} {ins outs : List C} (h : OpProtoT ch ins outs) :
    OpProto ch ins outs :=
  ⟨fun t hi ho hh hp => h.ag t hi ho (fun c hc => heldTo_of_held (hh c hc) t) hp, h.initIn,
    h.initOut⟩

theorem fork_opT (ch : C → Chan) (ca : C) (cos : List C) (F : Fork.Fork (ch ca) (cos.map ch)) :
    OpProtoT ch [ca] cos := by
  have mem : ∀ c ∈ cos, ch c ∈ cos.map ch := fun c hc => List.mem_map_of_mem hc
  refine ⟨fun t hi ho _ hp => ?_, ?_, ?_⟩
  · have h := Fork.fork_proto F (hi ca (List.mem_singleton_self _)).1
      (fun o hom => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hom; exact (ho c hc).2) t
      (fun s hs => ⟨(hp s hs).1 ca (List.mem_singleton_self _), fun o hom => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 hom; exact (hp s hs).2 c hc⟩)
    refine ⟨fun c hc => ?_, fun c hc => h.2 _ (mem c hc)⟩
    rw [List.mem_singleton.1 hc]; exact h.1
  · intro c hc; rw [List.mem_singleton.1 hc]; exact F.initA
  · intro c hc; exact F.initO _ (mem c hc)

theorem join_opT {g : List Nat → Nat} (ch : C → Chan) (cis : List C) (co : C)
    (J : Join.Join g (cis.map ch) (ch co)) : OpProtoT ch cis [co] := by
  have mem : ∀ c ∈ cis, ch c ∈ cis.map ch := fun c hc => List.mem_map_of_mem hc
  refine ⟨fun t hi ho _ hp => ?_, ?_, ?_⟩
  · have h := Join.join_proto J (ho co (List.mem_singleton_self _)).2
      (fun i him => by obtain ⟨c, hc, rfl⟩ := List.mem_map.1 him; exact (hi c hc).1) t
      (fun s hs => ⟨(hp s hs).2 co (List.mem_singleton_self _), fun i him => by
        obtain ⟨c, hc, rfl⟩ := List.mem_map.1 him; exact (hp s hs).1 c hc⟩)
    refine ⟨fun c hc => h.2 _ (mem c hc), fun c hc => ?_⟩
    rw [List.mem_singleton.1 hc]; exact h.1
  · intro c hc; exact J.initI _ (mem c hc)
  · intro c hc; rw [List.mem_singleton.1 hc]; exact J.initO

theorem link_opT (ch : C → Chan) (ci co : C) (c : Trace) (L : Link.Link (ch ci) (ch co) c) :
    OpProtoT ch [ci] [co] := by
  have mi : ci ∈ [ci] := List.mem_singleton_self _
  have mo : co ∈ [co] := List.mem_singleton_self _
  refine ⟨fun t hi ho _ hp => ?_, ?_, ?_⟩
  · have h := Link.link_proto L (hi ci mi).1 (ho co mo).2 t
      (fun s hs => ⟨((hp s hs).1 ci mi).1, ((hp s hs).2 co mo).2⟩)
    exact ⟨fun c' hc' => by rw [List.mem_singleton.1 hc']; exact h.1,
           fun c' hc' => by rw [List.mem_singleton.1 hc']; exact h.2⟩
  · intro c' hc'; rw [List.mem_singleton.1 hc']; exact L.ii
  · intro c' hc'; rw [List.mem_singleton.1 hc']; exact L.io

theorem amerge_opT (ch : C → Chan) (cx cy cz : C) (g1 g2 : Trace)
    (M : CM.AMerge (ch cx) (ch cy) (ch cz) g1 g2) : OpProtoT ch [cx, cy] [cz] := by
  have mx : cx ∈ [cx, cy] := by simp
  have my : cy ∈ [cx, cy] := by simp
  have mz : cz ∈ [cz] := List.mem_singleton_self _
  refine ⟨fun t hi ho _ hp => ?_, ?_, ?_⟩
  · have h := CM.amerge_proto M (hi cx mx).1 (hi cy my).1 (ho cz mz).2 t
      (fun s hs => ⟨((hp s hs).1 cx mx).1, ((hp s hs).1 cy my).1, ((hp s hs).2 cz mz).2⟩)
    refine ⟨fun c' hc' => ?_, fun c' hc' => ?_⟩
    · simp at hc'
      rcases hc' with rfl | rfl
      · exact h.1
      · exact h.2.1
    · rw [List.mem_singleton.1 hc']; exact h.2.2
  · intro c' hc'; simp at hc'
    rcases hc' with rfl | rfl
    · exact M.ix
    · exact M.iy
  · intro c' hc'; rw [List.mem_singleton.1 hc']; exact M.iz

theorem src_opT (ch : C → Chan) (cz : C) (v : Nat) (S : Capstone.Src (ch cz) v) :
    OpProtoT ch [] [cz] := by
  refine ⟨fun t _ _ _ _ => ⟨fun c hc => absurd hc (List.not_mem_nil), fun c hc => ?_⟩,
    fun c hc => absurd hc (List.not_mem_nil), fun c hc => ?_⟩
  · rw [List.mem_singleton.1 hc]
    intro hne
    have h := S.H_LUT_SI t hne
    revert hne h
    cases (ch cz).req t <;> cases (ch cz).req (t + 1) <;> cases (ch cz).ack t <;> simp
  · rw [List.mem_singleton.1 hc]; exact S.iz

theorem sink_opT (ch : C → Chan) (ca : C) (S : Ops.Gcd.Sink (ch ca)) : OpProtoT ch [ca] [] := by
  refine ⟨fun t _ _ _ _ => ⟨fun c hc h => ?_, fun c hc => by cases hc⟩, ?_, ?_⟩
  · rw [List.mem_singleton.1 hc] at h ⊢
    have := S.wire t h
    intro e; exact h (this.trans e.symm)
  · intro c hc; rw [List.mem_singleton.1 hc]; exact S.init
  · intro c hc; cases hc

theorem steer_opT {sel : Nat → Bool} {f : Nat → Nat} (ch : C → Chan) (cj : C) (cout : Bool → C)
    (S : Steer.Steer sel f (ch cj) (fun b => ch (cout b))) :
    OpProtoT ch [cj] [cout true, cout false] := by
  have memo : ∀ c, c ∈ [cout true, cout false] → ∃ b, c = cout b := by
    intro c hc; simp at hc; rcases hc with h | h
    · exact ⟨true, h⟩
    · exact ⟨false, h⟩
  have memb : ∀ b, cout b ∈ [cout true, cout false] := by intro b; cases b <;> simp
  have hcj : cj ∈ [cj] := List.mem_singleton_self _
  refine ⟨fun t hi ho hhd hp => ?_, ?_, ?_⟩
  · have h := steer_protoT S (hi cj hcj).1 (fun b => (ho _ (memb b)).2) t (hhd cj hcj)
      (fun s hs => ⟨(hp s hs).1 cj hcj, fun b => (hp s hs).2 _ (memb b)⟩)
    refine ⟨fun c hc => ?_, fun c hc => ?_⟩
    · rw [List.mem_singleton.1 hc]; exact h.1
    · obtain ⟨b, rfl⟩ := memo c hc; exact h.2 b
  · intro c hc; rw [List.mem_singleton.1 hc]; exact S.initJ
  · intro c hc; obtain ⟨b, rfl⟩ := memo c hc; exact S.initO b

theorem mux_opT {sel : Nat → Bool} (ch : C → Chan) (cc cx cy cz : C) (j0 j1 : Trace)
    (M : Mux.Mux sel (ch cx) (ch cy) (ch cc) (ch cz) j0 j1) :
    OpProtoT ch [cc, cx, cy] [cz] := by
  have mc : cc ∈ [cc, cx, cy] := by simp
  have mx : cx ∈ [cc, cx, cy] := by simp
  have my : cy ∈ [cc, cx, cy] := by simp
  have mz : cz ∈ [cz] := List.mem_singleton_self _
  refine ⟨fun t hi ho hhd hp => ?_, ?_, ?_⟩
  · have h := mux_protoT M (hi cx mx).1 (hi cy my).1 (hi cc mc).1 (ho cz mz).2 t (hhd cc mc)
      (fun s hs => ⟨((hp s hs).1 cx mx).1, ((hp s hs).1 cy my).1, ((hp s hs).1 cc mc).1,
        ((hp s hs).2 cz mz).2⟩)
    refine ⟨fun c' hc' => ?_, fun c' hc' => ?_⟩
    · simp at hc'
      rcases hc' with rfl | rfl | rfl
      · exact h.2.2.1
      · exact h.1
      · exact h.2.1
    · rw [List.mem_singleton.1 hc']; exact h.2.2.2
  · intro c' hc'; simp at hc'
    rcases hc' with rfl | rfl | rfl
    · exact M.ic
    · exact M.ix
    · exact M.iy
  · intro c' hc'; rw [List.mem_singleton.1 hc']; exact M.iz

theorem muxn_opT {sel : Nat → Nat} (ch : C → Chan) (cc : C) (cxs : Nat → C) (cz : C)
    (j : Nat → Trace) (M : MuxN.MuxN sel (fun k => ch (cxs k)) (ch cc) (ch cz) j) :
    OpProtoT ch [cc, cxs 0, cxs 1, cxs 2] [cz] := by
  have mc : cc ∈ [cc, cxs 0, cxs 1, cxs 2] := by simp
  have mx : ∀ k, k < 3 → cxs k ∈ [cc, cxs 0, cxs 1, cxs 2] :=
    MuxN.cases3 (by simp) (by simp) (by simp)
  have mz : cz ∈ [cz] := List.mem_singleton_self _
  refine ⟨fun t hi ho hhd hp => ?_, ?_, ?_⟩
  · have h := muxn_protoT M (fun k hk => (hi _ (mx k hk)).1) (hi cc mc).1 (ho cz mz).2 t
      (hhd cc mc)
      (fun s hs => ⟨fun k hk => ((hp s hs).1 _ (mx k hk)).1, ((hp s hs).1 cc mc).1,
        ((hp s hs).2 cz mz).2⟩)
    refine ⟨fun c' hc' => ?_, fun c' hc' => ?_⟩
    · simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
      rcases hc' with rfl | rfl | rfl | rfl
      · exact h.2.1
      · exact h.1 0 (by omega)
      · exact h.1 1 (by omega)
      · exact h.1 2 (by omega)
    · rw [List.mem_singleton.1 hc']; exact h.2.2
  · intro c' hc'
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hc'
    rcases hc' with rfl | rfl | rfl | rfl
    · exact M.ic
    · exact M.ix 0 (by omega)
    · exact M.ix 1 (by omega)
    · exact M.ix 2 (by omega)
  · intro c' hc'; rw [List.mem_singleton.1 hc']; exact M.iz

end ops

/-! ## Every capstone cell kind -/

variable {n : Nat}

/-- Every OLD cell kind of the capstone network meets the bounded protocol spec. -/
theorem cell_protoT (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (hc : Cell ch sv k) :
    OpProtoT ch k.insC k.outsC := by
  cases k with
  | forkG i os => exact fork_opT ch i os hc
  | forkH i os l h d hs => exact fork_opT ch i (os.map Prod.fst) hc
  | join ins o e js _ => exact join_opT ch ins o hc
  | bjoin ins o ec ed => exact join_opT ch ins o hc
  | steerC j t f => exact steer_opT ch j (fun b => bif b then t else f) hc
  | steerD j t f fd _ => exact steer_opT ch j (fun b => bif b then t else f) hc
  | mux c x y z _ =>
    obtain ⟨j0, j1, M⟩ := hc; exact mux_opT ch c x y z j0 j1 M
  | muxn c x0 x1 x2 z _ =>
    obtain ⟨j, M⟩ := hc; exact muxn_opT ch c (cx3 x0 x1 x2) z j M
  | amerge x y z w =>
    obtain ⟨g1, g2, M⟩ := hc; exact amerge_opT ch x y z g1 g2 M
  | link i o => obtain ⟨c, L⟩ := hc; exact link_opT ch i o c L
  | src z which _ => exact src_opT ch z (sv which) hc
  | sink i => exact sink_opT ch i hc

theorem protoT_of_mod {ch : Fin n → Chan} {S : List (Fin n)} {D : Fin n → Nat → Nat}
    {ins outs : List (Fin n)} (hS : ∀ c ∈ ins, c ∉ S)
    (h : OpProtoT (modC ch S D) ins outs) : OpProtoT ch ins outs := by
  refine ⟨fun t hi ho hh hp => ?_, fun c hc => h.initIn c hc, fun c hc => h.initOut c hc⟩
  exact h.ag t (fun c hc => hi c hc) (fun c hc => ho c hc)
    (fun c hc => by rw [modC_out (hS c hc)]; exact hh c hc) (fun s hs => hp s hs)

/-- **Every relaxed cell meets the bounded protocol spec.** -/
theorem cell_protoT_B (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (hc : CellB ch sv k)
    (hj : Disj k) : OpProtoT ch k.insC k.outsC := by
  obtain ⟨D, hC, -, -⟩ := cellB_loc ch sv (fun _ _ => false) k hc hj
  exact protoT_of_mod hj (cell_protoT _ sv k hC)

end Formal.Net.OpsBusy2
