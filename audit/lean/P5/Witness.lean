import Formal.Net.CapstoneCut
/-! Audit P5: joint satisfiability of gcd_hw_circuit_safe'' hypotheses.
(1) H_WALK proved in the kernel for one concrete input (a, b) = (1, 1).
(2) The all-silent run satisfies H_CELLS, H_BUNDLE, H_START_ONCE (so the conclusion holds
    vacuously for it: out0 never latches). -/
open Formal.Net Formal.Net.Kahn Formal.Net.GcdHw Formal.Net.CapSafe Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.Handshake Formal.Net.Ops

set_option maxRecDepth 100000

namespace AuditP5

def x0 (a b : Nat) : TS := ⟨GcdHw.Gcd.init a b, fun _ => [], fun _ => []⟩

def walkChk (σ : Fin NC → Nat → Nat) (om : Nat → Nat → Bool) (P : Nat) : Bool :=
  (List.range P).all fun p => match (walk σ p).cur with
    | none => true
    | some d => match opAt (consOf d) with
      | .amerge _ y z w => om w ((walk σ p).W z) == decide (d = y)
      | _ => true

theorem walk_none (σ : Fin NC → Nat → Nat) (P : Nat) (h : (walk σ P).cur = none) :
    ∀ p, P ≤ p → (walk σ p).cur = none := by
  intro p hp
  induction p with
  | zero => have : P = 0 := by omega
            subst this; exact h
  | succ p ih =>
    rcases Nat.lt_or_ge P (p+1) with h1 | h1
    · have := ih (by omega)
      show (wstep σ (walk σ p)).cur = none
      unfold wstep; rw [this]; exact this
    · have : P = p + 1 := by omega
      subst this; exact h

theorem walkOK_of (σ : Fin NC → Nat → Nat) (om : Nat → Nat → Bool) (P : Nat)
    (hc : walkChk σ om P = true) (hn : (walk σ P).cur = none) : WalkOK σ om := by
  intro p d x y z w hcur hop
  rcases Nat.lt_or_ge p P with hp | hp
  · have := List.all_eq_true.mp hc p (List.mem_range.mpr hp)
    simp only [hcur, hop] at this
    simpa using this
  · rw [walk_none σ P hn p hp] at hcur; cases hcur

def ls11 : List Nat := [0, 1, 2, 3, 4, 5, 6, 8, 9, 10, 11, 12, 13, 14, 15, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 56, 58, 53, 54, 55, 64, 66, 59, 60, 61, 62, 63, 67, 68, 69, 70, 72, 73, 74, 75, 76, 77, 78, 84, 86, 79, 80, 81, 82, 83, 87, 88, 89, 90, 92, 93, 94, 95, 96, 97, 98, 99, 100, 101, 102, 103, 104, 105, 123, 125, 118, 119, 120, 121, 122, 126, 133, 135, 127, 128, 129, 130, 131, 132, 136, 137, 138, 139, 107, 111, 112, 116, 117, 141, 114, 142, 143, 110, 113, 144, 108, 109, 115, 145, 146, 150, 151, 147, 148, 152, 156, 153, 157]

theorem ex11 : (exec GcdHw.Gcd.G (GcdHw.Gcd.init 1 1) ls11).isSome = true := by decide +kernel
theorem tx11 : (texec (x0 1 1) ls11).isSome = true := by decide +kernel

def y11 : TS := (texec (x0 1 1) ls11).get tx11

theorem term_chk : (List.range GcdHw.Gcd.rules.length).all
    (fun l => (step GcdHw.Gcd.G y11.s l).isNone) = true := by decide +kernel

theorem exec_texec_s : ∀ (ls : List Nat) (x y : TS), texec x ls = some y →
    exec GcdHw.Gcd.G x.s ls = some y.s := by
  intro ls
  induction ls with
  | nil => intro x y h; simp [texec] at h; subst h; rfl
  | cons l ls ih =>
    intro x y h
    simp only [texec] at h
    cases ht : tstep x l with
    | none => rw [ht] at h; simp at h
    | some z =>
      rw [ht] at h
      obtain ⟨r, hf, hs, -, -⟩ := tstep_some ht
      have := ih z y h
      simp only [exec, step, hf, Option.map_some, Option.bind_some]
      rw [← hs]; exact this

theorem tx11_eq : texec (x0 1 1) ls11 = some y11 := by
  unfold y11; exact (Option.some_get tx11).symm

theorem term11 : Terminal (step GcdHw.Gcd.G) y11.s := by
  intro l
  rcases Nat.lt_or_ge l GcdHw.Gcd.rules.length with hl | hl
  · have := List.all_eq_true.mp term_chk l (List.mem_range.mpr hl)
    simpa using this
  · simp only [step, GcdHw.Gcd.G, graph, graphV, List.getElem?_eq_none hl]
    rfl

theorem fin11 : y11.s = GcdHw.Gcd.final (Nat.gcd 1 1) := by
  have he := exec_texec_s ls11 (x0 1 1) y11 tx11_eq
  have hr := exec_run (t' := y11.s) he (fun _ => rfl)
  exact ((GcdHw.Gcd.gcd_hw_graph_computes_gcd (a := 1) (b := 1) (by decide) (by decide)).2.1 _ _ hr term11).1

theorem good11 : Good 1 1 y11 := by
  have hy := tx11_eq
  let x0' := x0 1 1
  have P : ∀ {P : TS → Prop}, Pres P → P x0' → P y11 := fun hP h0 => texec_pres hP ls11 x0' y11 hy h0
  refine ⟨fin11, P (fifo_pres _) (fun c => by simp [x0', x0]), ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro l i os hr; exact P (fk_pres hr) (fun o _ => rfl)
  · intro l ins o e hr; exact P (cp_pres hr) ⟨0, fun _ _ => rfl, rfl⟩
  · intro l c d t f hr
    have := side_of hr; simp [sideOK] at this
    exact P (br_pres hr this) ⟨rfl, rfl, rfl⟩
  · intro l s ds o iw hr
    have := side_of hr; simp [sideOK] at this
    exact P (mx_pres hr this.1 this.2) ⟨rfl, fun j hj => by simp [x0', x0] at hj, fun m _ => by simp [x0', x0, cntm]⟩
  · intro c hc; exact P (np_pres c hc) rfl
  · intro c hc; exact P (nc_pres c hc) rfl

theorem walk11_chk : walkChk (σY 1 1 y11) (omOf 1 1 y11) 41 = true := by decide +kernel
theorem walk11_end : (walk (σY 1 1 y11) 41).cur = none := by decide +kernel

/-- **H_WALK holds at (a, b) = (1, 1)** (kernel-checked). -/
theorem H_WALK_11 : ∃ y, Good 1 1 y ∧ WalkOK (σY 1 1 y) (omOf 1 1 y) :=
  ⟨y11, good11, walkOK_of _ _ 41 walk11_chk walk11_end⟩

end AuditP5

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

namespace AuditP5
open AuditP5S

/-- **Joint satisfiability** of all four hypotheses of `gcd_hw_circuit_safe''` at (a,b) = (1,1),
by the all-silent run; and in that run out0 never latches (conclusion vacuous). -/
theorem joint11 :
    (∀ o : Fin NO, Cell sil (srcV 1 1) (opAt o)) ∧ (∀ c, Held (sil c)) ∧
    (∀ t, Handshake.cnt (riseB (sil start).req) t ≤ 1) ∧
    (∃ y, Good 1 1 y ∧ WalkOK (σY 1 1 y) (omOf 1 1 y)) ∧
    (∀ k e, ¬ TokAt (sil out0) k e) :=
  ⟨H_CELLS_sil, H_BUNDLE_sil, H_START_ONCE_sil, H_WALK_11, sil_no_latch⟩

example := gcd_hw_circuit_safe'' 1 1 sil H_CELLS_sil H_BUNDLE_sil H_START_ONCE_sil H_WALK_11

/-- Negative control: H_WALK with the oracle flipped fails (it is not trivially true). -/
theorem walk11_flip : walkChk (σY 1 1 y11) (fun w k => !omOf 1 1 y11 w k) 41 = false := by decide +kernel

end AuditP5

#print axioms AuditP5.joint11
#print axioms Formal.Net.CapNet.Gcd.gcd_hw_circuit_safe''
#print axioms Formal.Net.CapNet.Gcd.gcd_hw_circuit_safe'
#print axioms Formal.Net.CapNet.Gcd.gcd_hw_circuit_safe
#print axioms Formal.Net.CapNet.Gcd.gcd_hw_forced
