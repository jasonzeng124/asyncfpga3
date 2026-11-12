import Formal.Core.EnvFast.Kernel

/-!
# Formal.Core.EnvFast.Data — `Env` soundness with a bundled-data window

Shard A. Notes: `formal/notes/A-envfast-2.md`.

`Env.Sound` asks every LUT to see a hazard-free MIC on every reachable
transition, and every excited element to stay excited. That is the right
obligation for control: a glitch on a request, an acknowledge or a C-element
is an event. It is the WRONG obligation for a data path: a bundled-data mux
(`bd_datamux`) glitches legitimately whenever its select and its data inputs
move together while nobody is sampling its output, and every honest
environment lets them move together then (the senders load their next data,
the control sender loads its next select, all while the output channel is idle).

So this file adds one relaxation, and nothing else:

* `DSpec.dout u`: signal `u` is the output of a DATA-path element;
* `DSpec.win s`: the output channel's hold window is open in state `s`
  (for a four-phase output `z`: `z_req ∨ z_ack`, the window `z_req↑ … z_ack↓`
  of `cells/docs/LIBRARY.md`).

`stepOKD` is `Env.stepOK` except that a data element is exempt from the MIC
hazard check and from persistence on a transition `s → s'` with the window
closed in BOTH `s` and `s'`. Control elements are never exempt
(`SoundD.lutOK_ctl`, `SoundD.persist_ctl`), so a `SoundD` model has exactly the
`Env.Sound` guarantee on its control path; with `dout = fun _ => false` the two
notions coincide (`soundD_none_iff`). Data validity inside the window (output
equals the selected input, and is not excited) is part of the per-state `Q`
of each model.

The kernel checker `kcheckD_sound` is `Kernel.kcheck_sound` with `kstepOK`
replaced by `kstepOKD`; it reuses every evaluation piece of `Kernel.lean`
(`kexc`, `kenOf`, `kpost`, `klutOK`, …) and their equality proofs.
-/

namespace Formal.Core.EnvFast

set_option linter.unusedSimpArgs false

open Formal.Core.LutTree Formal.Core.LutCells Formal.Core.LutAudit Formal.Core.Env

/-! ## 1. Specification -/

/-- Which signals are data-path outputs, and when the output hold window is open. -/
structure DSpec where
  dout : Nat → Bool
  win : Nat → Bool

/-- Transition `t` from `s` may glitch data element `u`: `u` is data and the
window is closed before and after `t`. -/
def exempt (D : DSpec) (s t u : Nat) : Bool := D.dout u && !D.win s && !D.win (s ^^^ 2 ^ t)

def persistOKD (M : Model) (D : DSpec) (s t : Nat) : Bool :=
  (List.range M.n).all fun u =>
    u == t || !bit (excMask M s) u || bit (excMask M (s ^^^ 2 ^ t)) u ||
      (isEnv M t && isEnv M u) || exempt D s t u

def stepOKD (M : Model) (D : DSpec) (s t : Nat) : Bool :=
  persistOKD M D s t && (idxd M.gates 0).all fun ggi => lutOK M s t ggi.1 ggi.2 || exempt D s t ggi.1.out

/-- `Env.Sound` with the data-window relaxation. -/
def SoundD (M : Model) (D : DSpec) (Q : Nat → Bool) : Prop :=
  ∀ s, Reach M s → Q s = true ∧ ∀ p ∈ succs M s, stepOKD M D s p.1 = true

/-- No data elements: `SoundD` is `Env.Sound`. -/
theorem soundD_none_iff (M : Model) (w : Nat → Bool) (Q : Nat → Bool) :
    SoundD M ⟨fun _ => false, w⟩ Q ↔ Sound M Q := by
  have h : ∀ s t, stepOKD M ⟨fun _ => false, w⟩ s t = stepOK M s t := by
    intro s t
    simp [stepOKD, stepOK, persistOKD, persistOK, exempt]
  simp only [SoundD, Sound, h]

/-- In a `SoundD` model every CONTROL element sees a hazard-free MIC on every
reachable transition (the `Env.reach_mic_hazard_free` guarantee). -/
theorem SoundD.lutOK_ctl {M : Model} {D : DSpec} {Q : Nat → Bool} (hS : SoundD M D Q) {s : Nat}
    (hs : Reach M s) {p : Nat × Nat} (hp : p ∈ succs M s) {g : Gate} {gi : Nat}
    (hg : (g, gi) ∈ idxd M.gates 0) (hd : D.dout g.out = false) : lutOK M s p.1 g gi = true := by
  have h := (hS s hs).2 p hp
  simp only [stepOKD, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 _ hg
  simpa [exempt, hd] using this

/-- … and every excited CONTROL element stays excited (persistence). -/
theorem SoundD.persist_ctl {M : Model} {D : DSpec} {Q : Nat → Bool} (hS : SoundD M D Q) {s : Nat}
    (hs : Reach M s) {p : Nat × Nat} (hp : p ∈ succs M s) {u : Nat} (hu : u < M.n)
    (hd : D.dout u = false) :
    (u == p.1 || !bit (excMask M s) u || bit (excMask M (s ^^^ 2 ^ p.1)) u ||
      (isEnv M p.1 && isEnv M u)) = true := by
  have h := (hS s hs).2 p hp
  simp only [stepOKD, persistOKD, Bool.and_eq_true, List.all_eq_true, List.mem_range] at h
  have := h.1 u hu
  simpa [exempt, hd] using this

/-- … and every data element is checked like a control element whenever the
window is open before or after the transition. -/
theorem SoundD.lutOK_data_win {M : Model} {D : DSpec} {Q : Nat → Bool} (hS : SoundD M D Q)
    {s : Nat} (hs : Reach M s) {p : Nat × Nat} (hp : p ∈ succs M s) {g : Gate} {gi : Nat}
    (hg : (g, gi) ∈ idxd M.gates 0) (hw : D.win s = true ∨ D.win (s ^^^ 2 ^ p.1) = true) :
    lutOK M s p.1 g gi = true := by
  have h := (hS s hs).2 p hp
  simp only [stepOKD, Bool.and_eq_true, List.all_eq_true] at h
  have := h.2 _ hg
  rcases hw with hw | hw <;> simpa [exempt, hw] using this

/-! ## 2. Kernel form -/

/-- `exempt` with raw operations; `D'` is the kernel form of the `DSpec`. -/
def kexempt (D' : DSpec) (s t u : Nat) : Bool :=
  D'.dout u && !D'.win s && !D'.win (Nat.xor s (Nat.pow 2 t))

/-- `D'` agrees with `D`. -/
structure DAgree (D' D : DSpec) : Prop where
  dout : ∀ u, D'.dout u = D.dout u
  win : ∀ s, D'.win s = D.win s

theorem kexempt_eq {D' D : DSpec} (hD : DAgree D' D) (s t u : Nat) :
    kexempt D' s t u = exempt D s t u := by
  simp only [kexempt, exempt, hD.dout, hD.win]; rfl

noncomputable def kpersistD (C : CModel) (D' : DSpec) (x0 x1 s t : Nat) : Bool :=
  let et := kisEnv C t
  kall (fun u => Nat.beq u t || !kb x0 u || kb x1 u || (!et && !kisEnv C u) || kexempt D' s t u)
    (List.range C.n)

theorem kpersistD_eq {M : Model} {C : CModel} (hc : KCompiled M C) {D' D : DSpec} (hD : DAgree D' D)
    (s t : Nat) :
    kpersistD C D' (kexc C s) (kexc C (Nat.xor s (Nat.pow 2 t))) s t = persistOKD M D s t := by
  have hx : Nat.xor s (Nat.pow 2 t) = s ^^^ 2 ^ t := rfl
  unfold kpersistD persistOKD
  rw [kall_eq, hc.n, hx]
  apply all_congr_mem
  intro u _
  simp only [kisEnv_eq hc, kb_eq, beq_eq_nat, Bool.not_not, kexc_eq hc, kexempt_eq hD]

noncomputable def kstepOKD (C : CModel) (D' : DSpec) (x0 x1 s t : Nat) : Bool :=
  kpersistD C D' x0 x1 s t &&
    kall (fun ci => klutOK C s t ci.1 ci.2 || kexempt D' s t ci.1.out) (idxd C.gates 0)

theorem kstepOKD_eq {M : Model} {C : CModel} (hc : KCompiled M C) {D' D : DSpec} (hD : DAgree D' D)
    (s t : Nat) :
    kstepOKD C D' (kexc C s) (kexc C (Nat.xor s (Nat.pow 2 t))) s t = stepOKD M D s t := by
  unfold kstepOKD stepOKD
  rw [kpersistD_eq hc hD, kall_eq, ← hc.comp.gates, idxd_map, List.all_map]
  congr 1
  apply all_congr_mem
  intro ci hci
  simp only [Function.comp_apply]
  rw [klutOK_eq hc, lutOKF_eq (hc.comp.valid_of_mem (mem_idxd hci)), kexempt_eq hD, CGate.out_g]

/-- Per-state check (kernel form). -/
noncomputable def kstateOKD (C : CModel) (D' : DSpec) (T : Tree) (s : Nat) : Bool :=
  let x0 := kexc C s
  let e0 := kenOf C x0
  kall (fun t => !kb e0 t ||
    (let x1 := kexc C (Nat.xor s (Nat.pow 2 t))
     kcontains T (kpost C e0 (kenOf C x1) s t) && kstepOKD C D' x0 x1 s t)) (List.range C.n)

theorem kstateOKD_sound {M : Model} {C : CModel} (hc : KCompiled M C) {D' D : DSpec}
    (hD : DAgree D' D) {T : Tree} {s : Nat} (h : kstateOKD C D' T s = true) :
    ∀ p ∈ succs M s, T.contains p.2 = true ∧ stepOKD M D s p.1 = true := by
  intro p hp
  simp only [succs, List.mem_map, List.mem_filter, List.mem_range] at hp
  obtain ⟨t, ⟨ht, he⟩, rfl⟩ := hp
  unfold kstateOKD at h
  rw [kall_eq, List.all_eq_true] at h
  have h1 := h t (List.mem_range.2 (hc.n ▸ ht))
  have hx : Nat.xor s (Nat.pow 2 t) = s ^^^ 2 ^ t := rfl
  simp only [Bool.or_eq_true, Bool.not_eq_true', Bool.and_eq_true] at h1
  rcases h1 with h1 | h1
  · rw [kb_eq, kenOf_eq hc, kexc_eq hc, ← enMask_eq_enOf] at h1
    rw [h1] at he; cases he
  · refine ⟨?_, ?_⟩
    · have := h1.1
      rw [kcontains_eq, kpost_eq hc, kenOf_eq hc, kenOf_eq hc, kexc_eq hc, hx, kexc_eq hc,
        ← enMask_eq_enOf, ← enMask_eq_enOf, postF_eq] at this
      exact this
    · rw [← kstepOKD_eq hc hD]; exact h1.2

noncomputable def kchunkD (C : CModel) (D' : DSpec) (Q' : Nat → Bool) (T : Tree) (chunk : List Nat) :
    Bool :=
  kall (fun s => Q' s && kstateOKD C D' T s) chunk

/-- **Soundness of the chunked kernel checker with a data window** (proved
once, for every model). -/
theorem kcheckD_sound {M : Model} {C : CModel} {D' D : DSpec} {Q Q' : Nat → Bool}
    {cert : List (List Nat)} (hc : KCompiled M C) (hD : DAgree D' D) (hQ : ∀ s, Q' s = Q s)
    (hinit : kinit M (kmkTree cert.flatten) = true)
    (hch : ∀ c ∈ cert, kchunkD C D' Q' (kmkTree cert.flatten) c = true) :
    ∀ s, Reach M s → s ∈ cert.flatten ∧ Q s = true ∧ ∀ p ∈ succs M s, stepOKD M D s p.1 = true := by
  rw [kmkTree_eq] at hinit hch
  have key : ∀ s, (mkTree cert.flatten).contains s = true → s ∈ cert.flatten ∧ Q s = true ∧
      ∀ p ∈ succs M s, (mkTree cert.flatten).contains p.2 = true ∧ stepOKD M D s p.1 = true := by
    intro s hs
    have hm := mem_of_mkTree hs
    obtain ⟨c, hc', hsc⟩ := List.mem_flatten.1 hm
    have := hch c hc'
    simp only [kchunkD, kall_eq, List.all_eq_true, Bool.and_eq_true] at this
    obtain ⟨h1, h2⟩ := this s hsc
    exact ⟨hm, hQ s ▸ h1, kstateOKD_sound hc hD h2⟩
  have inv : ∀ s, Reach M s → (mkTree cert.flatten).contains s = true := by
    intro s hs
    induction hs with
    | init h =>
        simp only [kinit, kall_eq, List.all_eq_true] at hinit
        rw [← kcontains_eq]; exact hinit _ h
    | step _ hp ih => exact ((key _ ih).2.2 _ hp).1
  intro s hs
  obtain ⟨hm, hq, hp⟩ := key s (inv s hs)
  exact ⟨hm, hq, fun p hpm => (hp p hpm).2⟩

theorem kcheckD_SoundD {M : Model} {C : CModel} {D' D : DSpec} {Q Q' : Nat → Bool}
    {cert : List (List Nat)} (hc : KCompiled M C) (hD : DAgree D' D) (hQ : ∀ s, Q' s = Q s)
    (hinit : kinit M (kmkTree cert.flatten) = true)
    (hch : ∀ c ∈ cert, kchunkD C D' Q' (kmkTree cert.flatten) c = true) : SoundD M D Q :=
  fun s hs => let r := kcheckD_sound hc hD hQ hinit hch s hs; ⟨r.2.1, r.2.2⟩

/-! ## 3. Negative controls for the relaxed notion -/

/-- A witnessed transition failing `stepOKD` refutes `SoundD`. -/
theorem not_soundD_of_witness {M : Model} {D : DSpec} {Q : Nat → Bool} {s0 : Nat} {ts : List Nat}
    {t : Nat} (h0 : s0 ∈ M.inits) (h : witness M s0 ts t (fun s t => !stepOKD M D s t) = true) :
    ¬ SoundD M D Q := by
  intro hS
  obtain ⟨s, hs, hm, hb⟩ := witness_sound h0 h
  have := (hS s hs).2 _ hm
  simp only at this
  simp [this] at hb

/-- A witnessed state failing `Q` refutes `SoundD`. -/
theorem not_soundD_of_witnessQ {M : Model} {D : DSpec} {Q : Nat → Bool} {s0 : Nat} {ts : List Nat}
    {t : Nat} (h0 : s0 ∈ M.inits) (h : witness M s0 ts t (fun s _ => !Q s) = true) :
    ¬ SoundD M D Q := by
  intro hS
  obtain ⟨s, hs, _, hb⟩ := witness_sound h0 h
  have := (hS s hs).1
  simp [this] at hb

end Formal.Core.EnvFast
