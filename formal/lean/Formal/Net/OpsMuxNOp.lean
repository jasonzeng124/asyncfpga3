import Formal.Net.OpsMuxN

/-!
# Probe C-8l (1b, part 2): the N = 3 mux cell at network level

Gate model `MuxN`, invariant `muxn_inv` (via the generated table of
`Formal.Net.OpsMuxN`), `muxn_proto` (causal assume-guarantee), and
`muxn_op`: `OpProto` + `OpData` with the token equation `muxnEq`
(the k-th output token is token #{i < k : sel (σ c i) = m} of input `m`,
`m = sel (σ c k) < 3`; the unselected inputs' tokens stay).
-/

namespace Formal.Net.Ops.MuxN
open Formal.Net Formal.Net.Handshake Formal.Net.Ops

/-- The select value as the state sees it: 3 stands for "none". -/
def clip (v : Nat) : Nat := if v < 3 then v else 3

theorem clip_lt (v : Nat) : clip v < 4 := by unfold clip; split <;> omega

theorem clip_beq (v k : Nat) (hk : k < 3) : (clip v == k) = (v == k) := by
  unfold clip
  by_cases h : v < 3
  · simp [h]
  · simp only [h, ite_false]
    have h1 : (3 == k) = false := by simp; omega
    have h2 : (v == k) = false := by simp; omega
    rw [h1, h2]

theorem clip_of_lt {v : Nat} (h : clip v < 3) : clip v = v := by
  unfold clip at *; split at h <;> simp_all

/-- Gate model of `bdc_muxn3` (see `Formal.Net.OpsMuxN`). `xs k` are the data
inputs, `c` the index channel, `j k` the join C-elements. -/
structure MuxN (sel : Nat → Nat) (xs : Nat → Chan) (c z : Chan) (j : Nat → Trace) : Prop where
  cj : ∀ k, k < 3 → ∀ t, j k (t + 1) ≠ j k t →
    (xs k).req t = j k (t + 1) ∧ (c.req t && (sel (c.dat t) == k)) = j k (t + 1)
  zr : ∀ t, z.req (t + 1) ≠ z.req t → z.req (t + 1) = (j 0 t || j 1 t || j 2 t)
  xa : ∀ k, k < 3 → ∀ t, (xs k).ack (t + 1) ≠ (xs k).ack t →
    j k t = (xs k).ack (t + 1) ∧ z.ack t = (xs k).ack (t + 1)
  ca : ∀ t, c.ack (t + 1) ≠ c.ack t → c.ack (t + 1) = z.ack t
  dat : ∀ t, sel (c.dat t) < 3 → z.dat t = (xs (sel (c.dat t))).dat t
  ij : ∀ k, k < 3 → j k 0 = false
  iz : z.req 0 = false
  ix : ∀ k, k < 3 → (xs k).ack 0 = false
  ic : c.ack 0 = false

variable {sel : Nat → Nat} {xs : Nat → Chan} {c z : Chan} {j : Nat → Trace}

def st (sel : Nat → Nat) (xs : Nat → Chan) (c z : Chan) (j : Nat → Trace) (t : Nat) : MS :=
  ⟨(xs 0).req t, (xs 1).req t, (xs 2).req t, (xs 0).ack t, (xs 1).ack t, (xs 2).ack t,
   c.req t, c.ack t, z.req t, z.ack t, j 0 t, j 1 t, j 2 t, clip (sel (c.dat t))⟩

/-- #offers on `c` (before `t`) whose select is `m`. -/
def cntk (sel : Nat → Nat) (c : Chan) (m : Nat) : Nat → Nat :=
  cnt (fun u => riseB c.req u && (sel (c.dat (u + 1)) == m))

set_option maxRecDepth 10000 in
theorem init_mem : ∀ s, s < 4 →
    mem ⟨false, false, false, false, false, false, false, false, false, false, false, false,
      false, s⟩ = true ∧
    dcOf ⟨false, false, false, false, false, false, false, false, false, false, false, false,
      false, s⟩ = 0 ∧
    ∀ k, k < 3 → dkOf ⟨false, false, false, false, false, false, false, false, false, false,
      false, false, false, s⟩ k = 1 := by decide +kernel

theorem cases3 {P : Nat → Prop} (h0 : P 0) (h1 : P 1) (h2 : P 2) : ∀ k, k < 3 → P k := by
  intro k hk
  rcases (show k = 0 ∨ k = 1 ∨ k = 2 by omega) with rfl | rfl | rfl <;> assumption

theorem muxn_inv (M : MuxN sel xs c z j) (hx : ∀ k, k < 3 → (xs k).req 0 = false)
    (hc : c.req 0 = false) (hz : z.ack 0 = false) (hh : Held c) : ∀ t,
    (∀ s, s < t → (∀ k, k < 3 → SendStep (xs k) s) ∧ SendStep c s ∧ RecvStep z s) →
    mem (st sel xs c z j t) = true ∧
      cnt (riseB c.req) t = cnt (riseB z.req) t + dcOf (st sel xs c z j t) ∧
      ∀ k, k < 3 → cnt (riseB (xs k).req) t + 1 = cntk sel c k t + dkOf (st sel xs c z j t) k := by
  intro t
  induction t with
  | zero =>
    intro _
    have I := init_mem (clip (sel (c.dat 0))) (clip_lt _)
    simp only [st, hx 0 (by omega), hx 1 (by omega), hx 2 (by omega), hc, hz, M.iz,
      M.ix 0 (by omega), M.ix 1 (by omega), M.ix 2 (by omega), M.ic,
      M.ij 0 (by omega), M.ij 1 (by omega), M.ij 2 (by omega)]
    refine ⟨I.1, ?_, ?_⟩
    · rw [I.2.1]; rfl
    · intro k hk; rw [I.2.2 k hk]; rfl
  | succ t ih =>
    intro hp
    obtain ⟨hm, h1, h2⟩ := ih (fun s hs => hp s (by omega))
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
      (fun hne ⟨a1, a2⟩ => hne (by rw [hh t a1 a2]))
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

theorem muxn_proto (M : MuxN sel xs c z j) (hx : ∀ k, k < 3 → (xs k).req 0 = false)
    (hc : c.req 0 = false) (hz : z.ack 0 = false) (hh : Held c) : ∀ t,
    (∀ s, s < t → (∀ k, k < 3 → SendStep (xs k) s) ∧ SendStep c s ∧ RecvStep z s) →
    (∀ k, k < 3 → RecvStep (xs k) t) ∧ RecvStep c t ∧ SendStep z t := by
  intro t hp
  obtain ⟨hm, _⟩ := muxn_inv M hx hc hz hh t hp
  have G := guar_all _ (clip_lt (sel (c.dat t))) _ _ _ _ _ _ _ _ _ _ _ _ _ hm
    (z.req (t + 1)) (M.zr t)
    ((xs 0).ack (t + 1)) (M.xa 0 (by omega) t) ((xs 1).ack (t + 1)) (M.xa 1 (by omega) t)
    ((xs 2).ack (t + 1)) (M.xa 2 (by omega) t) (c.ack (t + 1)) (M.ca t)
  obtain ⟨g0, g1, g2, gc, gz⟩ := G
  exact ⟨cases3 g0 g1 g2, gc, gz⟩

theorem rq_st (t : Nat) : ∀ m, m < 3 → rq (st sel xs c z j t) m = (xs m).req t :=
  cases3 rfl rfl rfl
theorem ak_st (t : Nat) : ∀ m, m < 3 → ak (st sel xs c z j t) m = (xs m).ack t :=
  cases3 rfl rfl rfl

/-! ## Network level -/

variable {C : Type}

/-- The N = 3 mux's token equation. -/
def muxnEq (sel : Nat → Nat) (cc : C) (cxs : Nat → C) (cz : C) (σ : C → Nat → Nat) : Prop :=
  ∀ k, sel (σ cc k) < 3 →
    σ cz k = σ (cxs (sel (σ cc k))) (cnt (fun i => sel (σ cc i) == sel (σ cc k)) k)

theorem muxn_op (ch : C → Chan) (cc : C) (cxs : Nat → C) (cz : C) (j : Nat → Trace)
    (M : MuxN sel (fun k => ch (cxs k)) (ch cc) (ch cz) j) :
    OpProto ch [cc, cxs 0, cxs 1, cxs 2] [cz] ∧
    OpData ch [cc, cxs 0, cxs 1, cxs 2] [cz] (muxnEq sel cc cxs cz) := by
  have mc : cc ∈ [cc, cxs 0, cxs 1, cxs 2] := by simp
  have mx : ∀ k, k < 3 → cxs k ∈ [cc, cxs 0, cxs 1, cxs 2] := cases3 (by simp) (by simp) (by simp)
  have mz : cz ∈ [cz] := List.mem_singleton_self _
  refine ⟨⟨fun t hi ho hhd hp => ?_, ?_, ?_⟩, ?_⟩
  · have h := muxn_proto M (fun k hk => (hi _ (mx k hk)).1) (hi cc mc).1 (ho cz mz).2 (hhd cc mc) t
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
  · intro hin hout c' hc' k r hoff σ hag hE
    rw [List.mem_singleton.1 hc'] at hoff ⊢
    obtain ⟨hpc, hhc⟩ := hin cc mc
    have hpx : ∀ m, m < 3 → Protocol (ch (cxs m)) ∧ Held (ch (cxs m)) :=
      fun m hm => hin _ (mx m hm)
    have hpz := (hout cz mz).1
    obtain ⟨hm, h1, h2⟩ := muxn_inv M (fun k hk => (hpx k hk).1.1.1) hpc.1.1 hpz.1.2 hhc r
      (fun s _ => ⟨fun k hk => ((hpx k hk).1.2 s).1, (hpc.2 s).1, (hpz.2 s).2⟩)
    have hr0 : (ch cz).req r = false := by have := hoff.1; simp [riseB] at this; exact this.1
    have hr1 : (ch cz).req (r + 1) = true := by have := hoff.1; simp [riseB] at this; exact this.2
    have cjk : ∀ k, k < 3 → j k (r + 1) ≠ j k r →
        (ch (cxs k)).req r = j k (r + 1) ∧
          ((ch cc).req r && (clip (sel ((ch cc).dat r)) == k)) = j k (r + 1) := by
      intro k hk hne
      rw [clip_beq _ _ hk]; exact M.cj k hk r hne
    have K := closed_all _ (clip_lt (sel ((ch cc).dat r))) _ _ _ _ _ _ _ _ _ _ _ _ _ hm
      _ ((hpx 0 (by omega)).1.2 r).1 _ ((hpx 1 (by omega)).1.2 r).1
      _ ((hpx 2 (by omega)).1.2 r).1 _ (hpc.2 r).1 _ (hpz.2 r).2
      _ (cjk 0 (by omega)) _ (cjk 1 (by omega)) _ (cjk 2 (by omega)) _ (M.zr r)
      _ (M.xa 0 (by omega) r) _ (M.xa 1 (by omega) r) _ (M.xa 2 (by omega) r) _ (M.ca r)
      (clip (sel ((ch cc).dat (r + 1)))) (clip_lt _)
      (fun hne ⟨a1, a2⟩ => hne (by rw [hhc r a1 a2]))
    have Ko := K.2.2.2.2.2
    simp only [hr0, hr1, Bool.not_false, Bool.true_and] at Ko
    obtain ⟨hcr, hca, _, hdc, hs3, hrq, hak, hdk⟩ := Ko trivial
    -- the control token
    obtain ⟨rc, ic, hrc, hoffc, hcrc, hcfc, _⟩ := open_offer hpc hcr
    have hic : ic = k := by
      simp only [st, hr0] at h1; rw [hoff.2, hdc] at h1; omega
    subst hic
    have hcfc' : cnt (fallB (ch cc).ack) (r + 1) = ic := by simp [cnt, fallB, hca, hcfc]
    have hdc0 := held_at hpc hhc hoffc hrc hcfc
    have hdc1 := held_at hpc hhc hoffc (by omega) hcfc'
    have hσc : σ cc ic = (ch cc).dat (rc + 1) := hag cc ic rc hrc hoffc
    -- the selected input
    generalize hmdef : clip (sel ((ch cc).dat r)) = m at hs3 hrq hak hdk
    have hsel : sel ((ch cc).dat r) = m := by rw [← hmdef]; exact (clip_of_lt (hmdef ▸ hs3)).symm
    have hselσ : sel (σ cc ic) = m := by rw [hσc, ← hdc0, hsel]
    have hEk := hE ic (by rw [hselσ]; exact hs3)
    rw [hselσ] at hEk
    rw [hEk, M.dat (r + 1) (by rw [hdc1, ← hdc0, hsel]; exact hs3), hdc1, ← hdc0, hsel]
    have hxr : (ch (cxs m)).req r = true := by
      rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with rfl | rfl | rfl <;> exact hrq
    have hxa : (ch (cxs m)).ack r = false := by
      rcases (show m = 0 ∨ m = 1 ∨ m = 2 by omega) with rfl | rfl | rfl <;> exact hak
    obtain ⟨hpxm, hhxm⟩ := hpx m hs3
    obtain ⟨rx, ix, hrx, hoffx, hcrx, hcfx, _⟩ := open_offer hpxm hxr
    have hcfx' : cnt (fallB (ch (cxs m)).ack) (r + 1) = ix := by simp [cnt, fallB, hxa, hcfx]
    have hag' : ∀ i u, u < r → OffAt (ch cc) i u → σ cc i = (ch cc).dat (u + 1) :=
      fun i u hu ho => hag cc i u hu ho
    have hco : cntk sel (ch cc) m r =
        cnt (fun i => sel (σ cc i) == m) (cnt (riseB (ch cc).req) r) :=
      cnt_offers (fun v => sel v == m) hag' r (Nat.le_refl _)
    rw [hcrc] at hco
    have hsucc : cnt (fun i => sel (σ cc i) == m) (ic + 1) =
        cnt (fun i => sel (σ cc i) == m) ic + 1 := by
      show cnt (fun i => sel (σ cc i) == m) ic + (if (sel (σ cc ic) == m) = true then 1 else 0) = _
      rw [hselσ]; simp
    have hk2 := h2 m hs3
    simp only [st, hr0] at hk2
    rw [hmdef] at hk2
    rw [hdk] at hk2
    have hix : cnt (fun i => sel (σ cc i) == m) ic = ix := by omega
    rw [hix, hag (cxs m) ix rx hrx hoffx, held_at hpxm hhxm hoffx (by omega) hcfx']

end Formal.Net.Ops.MuxN
