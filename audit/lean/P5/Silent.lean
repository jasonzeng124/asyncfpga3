import Formal.Net.CapstoneCut
open Formal.Net Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.CapSafe Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.Handshake Formal.Net.Ops

set_option maxRecDepth 100000
namespace AuditP5S

/-- output values of an operator from input values (silent run: links hold 0). -/
def outs (a b : Nat) (D : Nat → Nat) : K NC → List (Nat × Nat)
  | .forkG i os => os.map fun o => (o.val, D i.val)
  | .forkH i os _ _ _ _ => os.map fun o => (o.1.val, D i.val)
  | .join ins o e js _ => [(o.val, jg e js (ins.map fun i => D i.val))]
  | .bjoin ins o ec ed => [(o.val, bg ec ed (ins.map fun i => D i.val))]
  | .steerC _ t f => [(t.val, 0), (f.val, 0)]
  | .steerD j t f fd _ => [(t.val, fd.eval [D j.val / 2]), (f.val, fd.eval [D j.val / 2])]
  | .mux c x y z _ => [(z.val, if sel2 (D c.val) then D y.val else D x.val)]
  | .muxn c x0 x1 x2 z _ => [(z.val, if selD (D c.val) < 3 then D (cx3 x0 x1 x2 (selD (D c.val))).val else 0)]
  | .amerge x _ z _ => [(z.val, 2 * D x.val)]
  | .link _ _ => []
  | .src z which _ => [(z.val, srcV a b which)]
  | .sink _ => []

def iter (a b : Nat) (D : List Nat) : List Nat :=
  let f := fun c => D.getD c 0
  let upd := ops.flatMap (outs a b f)
  (List.range NC).map fun c => match upd.find? (·.1 == c) with
    | some p => p.2
    | none => 0

def fix (a b : Nat) : Nat → List Nat → List Nat
  | 0, D => D
  | n+1, D => fix a b n (iter a b D)

def DL : List Nat := [1, 1, 0, 0, 0, 1, 1, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 1, 1, 1, 0, 0, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 1, 0, 0, 1, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 3, 1, 3, 3, 1, 3, 3, 3, 1, 1, 1, 1, 3, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0]
def D (c : Nat) : Nat := DL.getD c 0

def sil (c : Fin NC) : Chan := ⟨fun _ => false, fun _ => false, fun _ => D c.val⟩

def dOK (a b : Nat) (k : K NC) : Bool :=
  (outs a b D k).all (fun p => D p.1 == p.2) &&
  (match k with
   | .forkG _ os => !os.isEmpty
   | .forkH _ os _ _ _ _ => !os.isEmpty
   | .join ins _ _ _ _ => !ins.isEmpty
   | .bjoin ins _ _ _ => !ins.isEmpty
   | _ => true)

theorem all_ok : ops.all (dOK 1 1) = true := by decide +kernel

theorem mem_sil {o : Chan} {os : List (Fin NC)} (h : o ∈ os.map sil) : ∃ c ∈ os, o = sil c := by
  simp only [List.mem_map] at h; obtain ⟨c, hc, e⟩ := h; exact ⟨c, hc, e.symm⟩

theorem cell_sil (a b : Nat) (k : K NC) (h : dOK a b k = true) : Cell sil (srcV a b) k := by
  simp only [dOK, Bool.and_eq_true] at h
  obtain ⟨h1, h2⟩ := h
  have hall := List.all_eq_true.mp h1
  cases k with
  | forkG i os =>
    refine ⟨by simpa using h2, ?_, ?_, ?_, rfl, ?_⟩
    · intro o ho t hne; obtain ⟨c, -, rfl⟩ := mem_sil ho; exact absurd rfl hne
    · intro t hne; exact absurd rfl hne
    · intro o ho t; obtain ⟨c, hc, rfl⟩ := mem_sil ho
      have := hall (c.val, D i.val) (List.mem_map.mpr ⟨c, hc, rfl⟩); simpa [sil] using this
    · intro o ho; obtain ⟨c, -, rfl⟩ := mem_sil ho; rfl
  | forkH i os l hh d hs =>
    refine ⟨by simpa using h2, ?_, ?_, ?_, rfl, ?_⟩
    · intro o ho t hne; rw [List.map_map] at ho; simp only [List.mem_map] at ho
      obtain ⟨c, -, rfl⟩ := ho; exact absurd rfl hne
    · intro t hne; exact absurd rfl hne
    · intro o ho t; rw [List.map_map] at ho; simp only [List.mem_map] at ho
      obtain ⟨c, hc, rfl⟩ := ho
      have := hall (c.1.val, D i.val) (List.mem_map.mpr ⟨c, hc, rfl⟩); simpa [sil] using this
    · intro o ho; rw [List.map_map] at ho; simp only [List.mem_map] at ho
      obtain ⟨c, -, rfl⟩ := ho; rfl
  | join ins o e js jw =>
    refine ⟨by simpa using h2, ?_, ?_, ?_, rfl, ?_⟩
    · intro t hne; exact absurd rfl hne
    · intro i hi t hne; obtain ⟨c, -, rfl⟩ := mem_sil hi; exact absurd rfl hne
    · intro t; have := hall _ (List.mem_singleton_self _); simp [sil, List.map_map] at this ⊢
      rw [this]; rfl
    · intro i hi; obtain ⟨c, -, rfl⟩ := mem_sil hi; rfl
  | bjoin ins o ec ed =>
    refine ⟨by simpa using h2, ?_, ?_, ?_, rfl, ?_⟩
    · intro t hne; exact absurd rfl hne
    · intro i hi t hne; obtain ⟨c, -, rfl⟩ := mem_sil hi; exact absurd rfl hne
    · intro t; have := hall _ (List.mem_singleton_self _); simp [sil, List.map_map] at this ⊢
      rw [this]; rfl
    · intro i hi; obtain ⟨c, -, rfl⟩ := mem_sil hi; rfl
  | steerC j t f =>
    refine ⟨?_, ?_, ?_, rfl, ?_⟩
    · intro bb tt hne; exact absurd rfl hne
    · intro tt hne; exact absurd rfl hne
    · intro bb tt
      have ht := hall (t.val, 0) (by simp [outs]); have hf := hall (f.val, 0) (by simp [outs])
      cases bb <;> simp_all [sil]
    · intro bb; cases bb <;> rfl
  | steerD j t f fd sw =>
    refine ⟨?_, ?_, ?_, rfl, ?_⟩
    · intro bb tt hne; exact absurd rfl hne
    · intro tt hne; exact absurd rfl hne
    · intro bb tt
      have ht := hall (t.val, _) (by simp [outs]; exact Or.inl rfl)
      have hf := hall (f.val, _) (by simp [outs]; exact Or.inr rfl)
      cases bb <;> simp_all [sil]
    · intro bb; cases bb <;> rfl
  | mux c x y z mw =>
    refine ⟨fun _ => false, fun _ => false, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl, rfl⟩
    · intro tt hne; exact absurd rfl hne
    · intro tt hne; exact absurd rfl hne
    · intro tt hne; exact absurd rfl hne
    · intro tt hne; exact absurd rfl hne
    · intro tt hne; exact absurd rfl hne
    · intro tt hne; exact absurd rfl hne
    · intro tt; have := hall _ (List.mem_singleton_self _)
      by_cases hs : sel2 (D c.val) = true <;> simp_all [sil, outs]
  | muxn c x0 x1 x2 z nw =>
    refine ⟨fun _ _ => false, ?_, ?_, ?_, ?_, ?_, ?_, rfl, ?_, rfl⟩
    · intro k _ tt hne; exact absurd rfl hne
    · intro tt hne; exact absurd rfl hne
    · intro k _ tt hne; exact absurd rfl hne
    · intro tt hne; exact absurd rfl hne
    · intro tt hlt; have := hall _ (List.mem_singleton_self _); simp only [sil] at this hlt ⊢
      simp only [hlt, ite_true] at this; simpa using this
    · intro k _; rfl
    · intro k _; rfl
  | amerge x y z w =>
    refine ⟨fun _ => false, fun _ => false, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl, rfl, rfl⟩
    · intro tt hne; exact absurd rfl hne
    · intro tt hne; exact absurd rfl hne
    · intro tt; rfl
    · intro tt hne; exact absurd rfl hne
    · intro tt _ h; cases h
    · intro tt hne; exact absurd rfl hne
    · intro tt hne; exact absurd rfl hne
    · intro tt; have := hall _ (List.mem_singleton_self _); simp [sil, Mux.b2n] at this ⊢; exact this
  | link i o =>
    refine ⟨fun _ => false, ?_, ?_, ?_, ?_, ?_, rfl, rfl, rfl⟩
    · intro tt hne; exact absurd rfl hne
    · intro tt hne; exact absurd rfl hne
    · intro tt hne; exact absurd rfl hne
    · intro tt h; cases h
    · intro tt _; rfl
  | src z which d =>
    refine ⟨?_, ?_, rfl⟩
    · intro tt hne; exact absurd rfl hne
    · intro tt; have := hall _ (List.mem_singleton_self _); simpa [sil] using this
  | sink i =>
    exact ⟨fun tt hne => absurd rfl hne, rfl⟩

theorem H_CELLS_sil (o : Fin NO) : Cell sil (srcV 1 1) (opAt o) :=
  cell_sil 1 1 _ (List.all_eq_true.mp all_ok _ getD_mem)

theorem H_BUNDLE_sil (c : Fin NC) : Held (sil c) := fun t h _ => by simp [inTx, sil] at h

theorem cnt_false (t : Nat) : Handshake.cnt (fun _ => false) t = 0 := by
  induction t with
  | zero => rfl
  | succ t ih => simp [Handshake.cnt, ih]

theorem H_START_ONCE_sil (t : Nat) : cnt (riseB (sil start).req) t ≤ 1 := by
  have : riseB (sil start).req = fun _ => false := by funext u; simp [riseB, sil]
  rw [this, cnt_false]; omega

/-- out0 never latches in the silent run. -/
theorem sil_no_latch (k e : Nat) : ¬ TokAt (sil out0) k e := by
  intro h; simp [TokAt, fallB, sil] at h

end AuditP5S
