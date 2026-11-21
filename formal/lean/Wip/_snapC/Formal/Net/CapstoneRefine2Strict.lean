import Formal.Net.CapstoneRefine2

/-!
# Probe C-8x2: the relaxation is strict on a whole-network run

`chS` is C-8t's witness run `chW` with ONE change: while channel 3 (`ufork0`'s first branch,
consumed by a sink) is idle, its bus shows `start`'s bus plus one (a stand-in for whatever a
physical bus carries between transactions). Then:

* `strict_old_fails`: the OLD gate model fails on `chS` (fork 0's all-time data field breaks at
  `t = 0`), so `gcd_hw_circuit_safe3` / C-8x's `gcd_hw_circuit_safe_phys` cannot take `chS`
  as its Ops trace without a separate zero-delay trace and H_ZD_AGREE;
* `strict_phys2_hyps`: every hypothesis of `gcd_hw_circuit_safe_phys2` holds on `chS`
  (certificates `exempt`), so the relaxed capstone applies to it directly.

`cellB_congr`: a relaxed gate model depends on the trace only through its own channels.
-/

namespace Formal.Net.CapNet.Wit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapstoneRefine Formal.Net.OpsBusy

set_option maxRecDepth 100000

theorem cellB_congr {n : Nat} {ch ch' : Fin n → Chan} {sv : Nat → Nat} (k : K n)
    (h : ∀ c, c ∈ k.insC ∨ c ∈ k.outsC → ch' c = ch c) (hc : CellB ch sv k) : CellB ch' sv k := by
  cases k with
  | forkG i os =>
    show ForkB (ch' i) (os.map ch')
    rw [h i (Or.inl (by simp [K.insC])),
      List.map_congr_left (fun o ho => h o (Or.inr (by simpa [K.outsC] using ho)))]
    exact hc
  | forkH i os l hh d hs =>
    show ForkB (ch' i) ((os.map Prod.fst).map ch')
    rw [h i (Or.inl (by simp [K.insC])),
      List.map_congr_left (fun o ho => h o (Or.inr (by simpa [K.outsC] using ho)))]
    exact hc
  | join ins o e js jw =>
    show JoinB (jg e js) (ins.map ch') (ch' o)
    rw [h o (Or.inr (by simp [K.outsC])),
      List.map_congr_left (fun i hi => h i (Or.inl (by simpa [K.insC] using hi)))]
    exact hc
  | bjoin ins o ec ed =>
    show JoinB (bg ec ed) (ins.map ch') (ch' o)
    rw [h o (Or.inr (by simp [K.outsC])),
      List.map_congr_left (fun i hi => h i (Or.inl (by simpa [K.insC] using hi)))]
    exact hc
  | steerC j t f =>
    have e : (fun b => ch' (bif b then t else f)) = (fun b => ch (bif b then t else f)) := by
      funext b; cases b
      · exact h f (Or.inr (by simp [K.outsC]))
      · exact h t (Or.inr (by simp [K.outsC]))
    show SteerB sel2 (fun _ => 0) (ch' j) (fun b => ch' (bif b then t else f))
    rw [h j (Or.inl (by simp [K.insC])), e]; exact hc
  | steerD j t f fd sw =>
    have e : (fun b => ch' (bif b then t else f)) = (fun b => ch (bif b then t else f)) := by
      funext b; cases b
      · exact h f (Or.inr (by simp [K.outsC]))
      · exact h t (Or.inr (by simp [K.outsC]))
    show SteerB sel2 (fun v => fd.eval [v / 2]) (ch' j) (fun b => ch' (bif b then t else f))
    rw [h j (Or.inl (by simp [K.insC])), e]; exact hc
  | mux c x y z mw =>
    show ∃ j0 j1, MuxB sel2 (ch' x) (ch' y) (ch' c) (ch' z) j0 j1
    rw [h x (Or.inl (by simp [K.insC])), h y (Or.inl (by simp [K.insC])),
      h c (Or.inl (by simp [K.insC])), h z (Or.inr (by simp [K.outsC]))]
    exact hc
  | muxn c x0 x1 x2 z nw =>
    have e : (fun k => ch' (cx3 x0 x1 x2 k)) = (fun k => ch (cx3 x0 x1 x2 k)) := by
      funext k
      apply h; left
      have hm := cx3_mem x0 x1 x2 k
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hm
      simp only [K.insC, List.mem_cons, List.not_mem_nil, or_false]
      rcases hm with e | e | e <;> simp [e]
    show ∃ j, MuxNB selD (fun k => ch' (cx3 x0 x1 x2 k)) (ch' c) (ch' z) j
    rw [e, h c (Or.inl (by simp [K.insC])), h z (Or.inr (by simp [K.outsC]))]
    exact hc
  | amerge x y z w =>
    show ∃ g1 g2, AMergeB (ch' x) (ch' y) (ch' z) g1 g2
    rw [h x (Or.inl (by simp [K.insC])), h y (Or.inl (by simp [K.insC])),
      h z (Or.inr (by simp [K.outsC]))]
    exact hc
  | link i o =>
    show ∃ c, LinkB (ch' i) (ch' o) c
    rw [h i (Or.inl (by simp [K.insC])), h o (Or.inr (by simp [K.outsC]))]
    exact hc
  | src z which d =>
    show SrcB (ch' z) (sv which)
    rw [h z (Or.inr (by simp [K.outsC]))]; exact hc
  | sink i =>
    show Ops.Gcd.Sink (ch' i)
    rw [h i (Or.inl (by simp [K.insC]))]; exact hc

/-- The changed channel. -/
def c3 : Fin NC := 3

/-- Channel 3's bus, garbage (start's bus + 1) at its idle instants. -/
def ch3 : Chan :=
  ⟨(chW c3).req, (chW c3).ack, fun t => if inTx (chW c3) t = true then (chW c3).dat t
    else (chW start).dat t + 1⟩

def chS (c : Fin NC) : Chan := if c = c3 then ch3 else chW c

theorem chS_ne {c : Fin NC} (h : c ≠ c3) : chS c = chW c := by simp [chS, h]
theorem chS_3 : chS c3 = ch3 := by simp [chS]

theorem op0 : opAt 0 = .forkG start [c3, 4] := rfl
theorem op190 : opAt 190 = .sink c3 := rfl

theorem w_proto : ∀ c, Protocol (chW c) := gcd_hw_protocol 12 18 chW w_cells w_held

theorem idle3 : inTx (chW c3) 0 = false := by
  simp [inTx, (w_proto c3).1.1, (w_proto c3).1.2]

/-- The old gate model fails on `chS`. -/
theorem strict_old_fails : ¬ ∀ o : Fin NO, Cell chS (srcV 12 18) (opAt o) := by
  intro h
  have F := h 0
  rw [op0] at F
  have hd := F.dat (chS c3) (by simp) 0
  rw [chS_3, chS_ne (show start ≠ c3 by decide)] at hd
  simp only [ch3, idle3, Bool.false_eq_true, ite_false] at hd
  omega

theorem cells_S : ∀ o : Fin NO, CellB chS (srcV 12 18) (opAt o) := by
  intro o
  by_cases h0 : o = 0
  · subst h0
    have F := w_cells 0
    rw [op0] at F
    show ForkB (chS start) ([c3, 4].map chS)
    rw [chS_ne (show start ≠ c3 by decide)]
    simp only [List.map, chS_3, chS_ne (show (4 : Fin NC) ≠ c3 by decide)]
    have m3 : chW c3 ∈ [c3, (4 : Fin NC)].map chW := by simp
    have m4 : chW 4 ∈ [c3, (4 : Fin NC)].map chW := by simp
    refine ⟨by simp, ?_, ?_, ?_, F.initA, ?_⟩
    · intro o ho t hne
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with e | e <;> subst e
      · exact F.wire (chW c3) m3 t hne
      · exact F.wire _ m4 t hne
    · intro t hne o ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with e | e <;> subst e
      · exact F.cel t hne (chW c3) m3
      · exact F.cel t hne _ m4
    · intro o ho t hb
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with e | e <;> subst e
      · have hb' : inTx (chW c3) t = true := hb
        simp only [ch3, hb', ite_true]
        exact F.dat _ m3 t
      · exact F.dat _ m4 t
    · intro o ho
      simp only [List.mem_cons, List.not_mem_nil, or_false] at ho
      rcases ho with e | e <;> subst e
      · exact F.initO (chW c3) m3
      · exact F.initO _ m4
  by_cases h1 : o = 190
  · subst h1
    have S := w_cells 190
    rw [op190] at S
    show Ops.Gcd.Sink (chS c3)
    rw [chS_3]
    exact ⟨S.wire, S.init⟩
  · apply cellB_congr (opAt o) _ (cell_relax chW _ _ (w_cells o))
    intro c hc
    apply chS_ne
    intro e; subst e
    rcases hc with hc | hc
    · exact h1 (cons_in o c3 hc).symm
    · exact h0 (prod_out o c3 hc).symm

theorem held_S : ∀ c, Held (chS c) := by
  intro c
  by_cases h : c = c3
  · subst h
    rw [chS_3]
    intro t h0 h1
    have h0' : inTx (chW c3) t = true := h0
    have h1' : inTx (chW c3) (t + 1) = true := h1
    simp only [ch3, h0', h1', ite_true]
    exact w_held c3 t h0' h1'
  · rw [chS_ne h]; exact w_held c

/-- Every hypothesis of `gcd_hw_circuit_safe_phys2` holds on `chS` (certificates `exempt`). -/
theorem strict_phys2_hyps :
    (∀ o : Fin NO, CellB chS (srcV 12 18) (opAt o)) ∧
    (∀ t, Handshake.cnt (riseB (chS start).req) t ≤ 1) ∧
    (∀ c t, RecvStep (chS c) t) ∧
    (∀ c, BCert (chS c)) := by
  refine ⟨cells_S, ?_, ?_, fun c => BCert.exempt (held_S c)⟩
  · rw [chS_ne (show start ≠ c3 by decide)]; exact w_start_once
  · intro c t
    by_cases h : c = c3
    · subst h; rw [chS_3]; exact ((w_proto c3).2 t).2
    · rw [chS_ne h]; exact ((w_proto c).2 t).2

/-- So the relaxed capstone applies to `chS`: out0 latches only `gcd 12 18`. -/
theorem strict_out0 : ∀ k e, TokAt (chS out0) k e → (chS out0).dat e = Nat.gcd 12 18 :=
  (gcd_hw_circuit_safe_phys2 12 18 (by decide) (by decide) chS strict_phys2_hyps.1
    strict_phys2_hyps.2.1 strict_phys2_hyps.2.2.1 strict_phys2_hyps.2.2.2).1

end Formal.Net.CapNet.Wit
