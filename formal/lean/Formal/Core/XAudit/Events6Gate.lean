import Formal.Core.XAudit.Events2PinDesign
import Formal.Core.XAudit.Events5

/-!
# Formal.Core.XAudit.Events6Gate — gates, paths and trees under the per-pin semantics

Probe A-events6 (W-E4n, the netlist half, part 1). See `formal/notes/A-events6.md`.

The netlist semantics is `Events2Pin.SatPin d plG x`: every gate reads EACH input
pin through its own monotone warp in the gate's band (`plG g i = (g.lo, g.hi)`),
so a LUT does NOT sample its pins at one instant (no H_ATOMIC_LUT). Here:

* `wf hsat gi i`: the warp with which gate number `gi` reads its input `i`
  (chosen from `SatPin`); `wf_warp`, `wf_eval`.
* `InitSpec g spec` (decidable over the `2^k` addresses): the INIT is `spec` of
  the pin values, constant pins (wires 0/1) fixed. **`gate_spec`**: then the
  gate's output is `spec` of its inputs, each read at its own warp.
* Paths `List (gate, input)` from a wire down to a source wire; `tau` composes
  the per-pin warps along a path (`tau_warp`: band `[plo, phi]`).
* `chkT` (a checker over a list of paths) and **`chkT_sound`**: a tree of
  buffers / inverters / AND / OR gates between wire `w` and the source wire
  `sw` evaluates, at every time, to `par ^^ (all|any)` of the source read at the
  composed warp of each path. This is how a FASTFALL / FASTRISE line, a chain
  of routes and a merge arm become the copies of an `Events5.Net4` pin.
* `pairW` and **`pairW_sound`**: two paths with a common head part (cancels: one
  warp) and a common tail part (adds its band width, `Events5Line.prefix_skew`)
  are sampled within `pairW` of each other (`hop_skew` on the middle parts).
-/

namespace Formal.Core.XAudit.Events6

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events2 (testBit_addr)
open Formal.Core.XAudit.Events2Pin (PinRel SatPin PinTab)
open Formal.Core.XAudit.Events5 (warp_comp hop_skew prefix_skew)

/-- The per-pin band table used here: every input of a gate in the gate's own
band (prjxray's LUT IOPATH rows are flat over A1..A6; the site-pin delay is in
the routed arc, A-events2pin §2). -/
def plG : PinTab := fun g _ => (g.lo, g.hi)

/-- Gate number `gi`. -/
def gt (d : Design) (gi : Nat) : GSpec := d.gates.getD gi default

theorem gt_mem (d : Design) {gi : Nat} (h : gi < d.gates.length) : gt d gi ∈ d.gates := by
  unfold gt; rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; exact List.getElem_mem h

section
variable {d : Design} {x : Fin d.n → Sig} (hsat : SatPin d plG x)

/-- The warp with which gate `gi` reads its input `i`. -/
noncomputable def wf (gi i : Nat) : Nat → Nat :=
  if h : gi < d.gates.length then Classical.choose (hsat _ (gt_mem d h)) i else id

theorem wf_warp {gi i : Nat} (h : gi < d.gates.length) (hi : i < (gt d gi).k) :
    Warp (gt d gi).lo (gt d gi).hi (wf hsat gi i) := by
  unfold wf; rw [dif_pos h]
  exact (Classical.choose_spec (hsat _ (gt_mem d h))).1 i hi

theorem wf_eval {gi : Nat} (h : gi < d.gates.length) (t : Nat) :
    x (d.wire (gt d gi).out) t = (gt d gi).init.testBit
      (addr (fun p : Fin (gt d gi).k => x (d.wire ((gt d gi).ins.getD p.val 0)) (wf hsat gi p.val t))) := by
  have := (Classical.choose_spec (hsat _ (gt_mem d h))).2 t
  unfold wf; simp only [dif_pos h]; exact this

/-- A warp with `1 ≤ lo` reads time `0` at `0` and `1`. -/
theorem warp_pred {lo hi : Nat} {f : Nat → Nat} (w : Warp lo hi f) (h1 : 1 ≤ lo) (t : Nat) : f t = f (t - 1 + 1) := by
  rcases Nat.eq_zero_or_pos t with h | h
  · subst h; have := w.le_late 0; have := w.le_late 1; simp only [Nat.zero_sub, Nat.zero_add]; omega
  · congr 1; omega

theorem warp_zero {lo hi : Nat} {f : Nat → Nat} (w : Warp lo hi f) : f 0 = 0 := by
  have := w.le_late 0; omega

end

/-! ## Gate functions -/

/-- **InitSpec** (decidable): on every address whose constant pins hold their
constant, the INIT bit is `spec` of the address bits. -/
def InitSpec (g : GSpec) (spec : (Nat → Bool) → Bool) : Prop :=
  ∀ a, a < 2 ^ g.k → (∀ i, i < g.k → g.ins.getD i 0 = 0 → a.testBit i = false) →
    (∀ i, i < g.k → g.ins.getD i 0 = 1 → a.testBit i = true) → g.init.testBit a = spec (fun i => a.testBit i)

instance (g : GSpec) (spec : (Nat → Bool) → Bool) : Decidable (InitSpec g spec) := by
  unfold InitSpec; exact inferInstance

section
variable {d : Design} {x : Fin d.n → Sig} (hsat : SatPin d plG x)
  (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
include h0 h1

/-- **A recognised gate under the per-pin semantics.** -/
theorem gate_spec {gi : Nat} (h : gi < d.gates.length) {spec : (Nat → Bool) → Bool}
    (hs : InitSpec (gt d gi) spec) (t : Nat) :
    x (d.wire (gt d gi).out) t =
      spec (fun i => if i < (gt d gi).k then x (d.wire ((gt d gi).ins.getD i 0)) (wf hsat gi i t) else false) := by
  rw [wf_eval hsat h t]
  generalize hv : (fun p : Fin (gt d gi).k => x (d.wire ((gt d gi).ins.getD p.val 0)) (wf hsat gi p.val t)) = v
  have hb : ∀ i, (addr v).testBit i =
      if i < (gt d gi).k then x (d.wire ((gt d gi).ins.getD i 0)) (wf hsat gi i t) else false := by
    intro i; rw [testBit_addr, ← hv]
    by_cases hi : i < (gt d gi).k
    · rw [dif_pos hi, if_pos hi]
    · rw [dif_neg hi, if_neg hi]
  rw [hs (addr v) (addr_lt v)]
  · congr 1; funext i; exact hb i
  · intro i hi hc; rw [hb, if_pos hi, hc, h0]
  · intro i hi hc; rw [hb, if_pos hi, hc, h1]

end

/-! ## Paths -/

/-- A path: `(gate, input)` pairs, from the reading end down to the source. -/
abbrev Path := List (Nat × Nat)

section
variable {d : Design} {x : Fin d.n → Sig} (hsat : SatPin d plG x)

/-- The composed warp of a path (the head pair is applied first). -/
noncomputable def tau : Path → Nat → Nat
  | [], t => t
  | (gi, i) :: r, t => tau r (wf hsat gi i t)

theorem tau_append : ∀ (p q : Path) (t : Nat), tau hsat (p ++ q) t = tau hsat q (tau hsat p t)
  | [], _, _ => rfl
  | (gi, i) :: r, q, t => by simp only [List.cons_append, tau]; exact tau_append r q _

end

def plo (d : Design) : Path → Nat
  | [] => 0
  | (gi, _) :: r => (gt d gi).lo + plo d r

def phi (d : Design) : Path → Nat
  | [] => 0
  | (gi, _) :: r => (gt d gi).hi + phi d r

/-- Every element is a gate input that exists. -/
def pathOK (d : Design) (p : Path) : Bool :=
  p.all fun e => decide (e.1 < d.gates.length) && decide (e.2 < (gt d e.1).k)

theorem plo_append (d : Design) : ∀ p q : Path, plo d (p ++ q) = plo d p + plo d q
  | [], _ => by simp [plo]
  | (gi, i) :: r, q => by simp only [List.cons_append, plo, plo_append d r q]; omega

theorem phi_append (d : Design) : ∀ p q : Path, phi d (p ++ q) = phi d p + phi d q
  | [], _ => by simp [phi]
  | (gi, i) :: r, q => by simp only [List.cons_append, phi, phi_append d r q]; omega

section
variable {d : Design} {x : Fin d.n → Sig} (hsat : SatPin d plG x)

theorem tau_warp : ∀ (p : Path), pathOK d p = true → Warp (plo d p) (phi d p) (tau hsat p)
  | [], _ => ⟨fun _ _ h => h, fun t => by simp [plo, tau], fun t => by simp [phi, tau]⟩
  | (gi, i) :: r, h => by
      simp only [pathOK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
      obtain ⟨⟨hg, hi⟩, hr⟩ := h
      have w1 := wf_warp hsat hg hi
      have w2 := tau_warp r hr
      have := warp_comp w2 w1
      refine ⟨this.mono, fun t => ?_, fun t => ?_⟩
      · have := this.le_late t; simp only [tau, plo]; omega
      · have := this.early_le t; simp only [tau, phi]; omega

theorem tau_zero (p : Path) (h : pathOK d p = true) : tau hsat p 0 = 0 := by
  have := (tau_warp hsat p h).le_late 0; omega

end

/-! ## Trees of buffers, inverters, AND and OR gates -/

/-- The live (non-constant) inputs of a gate. -/
def liveIdx (g : GSpec) : List Nat := (List.range g.k).filter (fun i => 2 ≤ g.ins.getD i 0)

def specL {α : Type} (op : Bool) (l : List α) (f : α → Bool) : Bool := if op then l.all f else l.any f

/-- The paths of `ps` whose head is input `i` (of the head gate), with the head dropped. -/
def subOf (ps : List Path) (i : Nat) : List Path :=
  ps.filterMap fun p => match p with
    | (_, i') :: r => if i' == i then some r else none
    | [] => none

def headOK (ps : List Path) (gi : Nat) (L : List Nat) : Bool :=
  ps.all fun p => match p with
    | (gi', i) :: _ => gi' == gi && L.contains i
    | [] => false

/-- **The tree checker.** `chkT d sw fuel op w ps = some par`: the paths `ps`
from wire `w` down to the source wire `sw` are exactly the paths of a tree of
1-input buffers/inverters and multi-input AND (`op`) / OR (`!op`) gates; `par`
is the inversion parity above the first multi-input gate. -/
def chkT (d : Design) (sw : Nat) : Nat → Bool → Nat → List Path → Option Bool
  | fuel, op, w, ps =>
    if ps = [[]] then (if w = sw then some false else none) else
    match fuel with
    | 0 => none
    | fuel + 1 =>
      match ps with
      | [] => none
      | [] :: _ => none
      | ((gi, _) :: _) :: _ =>
        if gi < d.gates.length ∧ (gt d gi).out = w ∧ headOK ps gi (liveIdx (gt d gi)) = true then
          if (liveIdx (gt d gi)).length = 1 then
            if InitSpec (gt d gi) (fun v => v ((liveIdx (gt d gi)).headD 0)) then
              chkT d sw fuel op ((gt d gi).ins.getD ((liveIdx (gt d gi)).headD 0) 0) (ps.map List.tail)
            else if InitSpec (gt d gi) (fun v => !v ((liveIdx (gt d gi)).headD 0)) then
              (chkT d sw fuel op ((gt d gi).ins.getD ((liveIdx (gt d gi)).headD 0) 0) (ps.map List.tail)).map (! ·)
            else none
          else if InitSpec (gt d gi) (fun v => specL op (liveIdx (gt d gi)) v) ∧ 2 ≤ (liveIdx (gt d gi)).length ∧
              (liveIdx (gt d gi)).all (fun i => chkT d sw fuel op ((gt d gi).ins.getD i 0) (subOf ps i) == some false) = true
          then some false else none
        else none

theorem mem_liveIdx {g : GSpec} {i : Nat} (h : i ∈ liveIdx g) : i < g.k := by
  unfold liveIdx at h; simp only [List.mem_filter, List.mem_range] at h; exact h.1

theorem headOK_mem {ps : List Path} {gi : Nat} {L : List Nat} (h : headOK ps gi L = true) {p : Path} (hp : p ∈ ps) :
    ∃ i r, p = (gi, i) :: r ∧ i ∈ L := by
  unfold headOK at h; rw [List.all_eq_true] at h
  have := h p hp
  match p, this with
  | (gi', i) :: r, hh =>
    simp only [Bool.and_eq_true, beq_iff_eq, List.contains_iff_mem] at hh
    exact ⟨i, r, by rw [hh.1], hh.2⟩

theorem specL_congr {α : Type} (op : Bool) (l : List α) (f g : α → Bool) (h : ∀ a ∈ l, f a = g a) :
    specL op l f = specL op l g := by
  unfold specL
  cases op
  · simp only [Bool.false_eq_true, ite_false]
    apply Bool.eq_iff_iff.mpr; rw [List.any_eq_true, List.any_eq_true]
    constructor
    · rintro ⟨a, ha, hf⟩; exact ⟨a, ha, by rw [← h a ha]; exact hf⟩
    · rintro ⟨a, ha, hf⟩; exact ⟨a, ha, by rw [h a ha]; exact hf⟩
  · simp only [ite_true]
    apply Bool.eq_iff_iff.mpr; rw [List.all_eq_true, List.all_eq_true]
    constructor
    · intro H a ha; rw [← h a ha]; exact H a ha
    · intro H a ha; rw [h a ha]; exact H a ha

theorem specL_tail (op : Bool) (e : Nat × Nat) (G : Path → Bool) :
    ∀ (ps : List Path), (∀ p ∈ ps, ∃ r, p = e :: r) →
      specL op ps G = specL op (ps.map List.tail) (fun r => G (e :: r))
  | [], _ => rfl
  | p :: ps, h => by
      obtain ⟨r, hr⟩ := h p (List.mem_cons_self ..)
      subst hr
      have ih := specL_tail op e G ps (fun q hq => h q (List.mem_cons_of_mem _ hq))
      unfold specL at ih ⊢
      cases op <;> simp only [List.all_cons, List.any_cons, List.map_cons, List.tail_cons] <;>
        simp only [Bool.false_eq_true, ite_false, ite_true] at ih ⊢ <;> rw [ih]

theorem mem_subOf {ps : List Path} {i : Nat} {r : Path} (h : r ∈ subOf ps i) : ∃ gi', ((gi', i) :: r) ∈ ps := by
  unfold subOf at h; rw [List.mem_filterMap] at h
  obtain ⟨p, hp, he⟩ := h
  rcases p with _ | ⟨⟨gi', i'⟩, r'⟩
  · simp at he
  · simp only at he
    by_cases hi : i' = i
    · subst hi; simp at he; subst he; exact ⟨gi', hp⟩
    · simp [hi] at he

theorem mem_subOf' {ps : List Path} {gi i : Nat} {r : Path} (h : ((gi, i) :: r) ∈ ps) : r ∈ subOf ps i := by
  unfold subOf; rw [List.mem_filterMap]; exact ⟨_, h, by simp⟩

theorem regroup (op : Bool) (ps : List Path) (gi : Nat) (L : List Nat) (hh : headOK ps gi L = true) (G : Path → Bool) :
    specL op L (fun i => specL op (subOf ps i) (fun r => G ((gi, i) :: r))) = specL op ps G := by
  unfold specL
  cases op
  · simp only [Bool.false_eq_true, ite_false]
    apply Bool.eq_iff_iff.mpr; simp only [List.any_eq_true]
    constructor
    · rintro ⟨i, _, r, hr, hg⟩
      obtain ⟨gi', hm⟩ := mem_subOf hr
      obtain ⟨i2, r2, he, _⟩ := headOK_mem hh hm
      simp only [List.cons.injEq, Prod.mk.injEq] at he
      obtain ⟨⟨e1, _⟩, _⟩ := he
      subst e1
      exact ⟨_, hm, hg⟩
    · rintro ⟨p, hp, hg⟩
      obtain ⟨i, r, he, hi⟩ := headOK_mem hh hp
      subst he
      exact ⟨i, hi, r, mem_subOf' hp, hg⟩
  · simp only [ite_true]
    apply Bool.eq_iff_iff.mpr; simp only [List.all_eq_true]
    constructor
    · intro H p hp
      obtain ⟨i, r, he, hi⟩ := headOK_mem hh hp
      subst he
      exact H i hi r (mem_subOf' hp)
    · intro H i _ r hr
      obtain ⟨gi', hm⟩ := mem_subOf hr
      obtain ⟨i2, r2, he, _⟩ := headOK_mem hh hm
      simp only [List.cons.injEq, Prod.mk.injEq] at he
      obtain ⟨⟨e1, _⟩, _⟩ := he
      subst e1
      exact H _ hm

theorem length_one {L : List Nat} (h : L.length = 1) : L = [L.headD 0] := by
  match L, h with
  | [a], _ => rfl

section
variable {d : Design} {x : Fin d.n → Sig} (hsat : SatPin d plG x)
  (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
include h0 h1

/-- **Soundness of the tree checker.** -/
theorem chkT_sound (sw : Nat) : ∀ (fuel : Nat) (op : Bool) (w : Nat) (ps : List Path) (par : Bool),
    chkT d sw fuel op w ps = some par →
    ∀ t, x (d.wire w) t = (par ^^ specL op ps (fun p => x (d.wire sw) (tau hsat p t))) := by
  intro fuel
  induction fuel with
  | zero =>
    intro op w ps par h t
    unfold chkT at h
    split at h
    · rename_i hp
      subst hp
      split at h
      · rename_i hw; cases h; subst hw; cases op <;> simp [specL, tau]
      · cases h
    · simp at h
  | succ n ih =>
    intro op w ps par h t
    unfold chkT at h
    split at h
    · rename_i hp
      subst hp
      split at h
      · rename_i hw; cases h; subst hw; cases op <;> simp [specL, tau]
      · cases h
    · simp only at h
      match ps, h with
      | ((gi, i0) :: r0) :: ps', h =>
        simp only at h
        split at h
        · rename_i hc
          obtain ⟨hg, hout, hh⟩ := hc
          rw [← hout]
          have hall : ∀ p ∈ ((gi, i0) :: r0) :: ps', ∃ i r, p = (gi, i) :: r ∧ i ∈ liveIdx (gt d gi) :=
            fun p hp => headOK_mem hh hp
          split at h
          · rename_i hl
            have hL := length_one hl
            generalize hi : (liveIdx (gt d gi)).headD 0 = i at h hL
            have hik : i < (gt d gi).k := mem_liveIdx (by rw [hL]; exact List.mem_singleton_self i)
            have hall1 : ∀ p ∈ ((gi, i0) :: r0) :: ps', ∃ r, p = (gi, i) :: r := by
              intro p hp
              obtain ⟨i', r, he, hm⟩ := hall p hp
              rw [hL] at hm; simp only [List.mem_singleton] at hm; subst hm; exact ⟨r, he⟩
            rw [specL_tail op (gi, i) _ _ hall1]
            simp only [tau]
            split at h
            · rename_i hs
              rw [gate_spec hsat h0 h1 hg hs t]; simp only [if_pos hik]
              exact ih op _ _ par h (wf hsat gi i t)
            · split at h
              · rename_i _ hs
                rw [gate_spec hsat h0 h1 hg hs t]; simp only [if_pos hik]
                cases hq : chkT d sw n op ((gt d gi).ins.getD i 0) (List.map List.tail (((gi, i0) :: r0) :: ps')) with
                | none => rw [hq] at h; cases h
                | some p' =>
                  rw [hq] at h; simp only [Option.map_some] at h; cases h
                  rw [ih op _ _ p' hq (wf hsat gi i t)]
                  cases p' <;> simp
              · cases h
          · split at h
            · rename_i _ hc2
              obtain ⟨hs, _, hch⟩ := hc2
              cases h
              rw [gate_spec hsat h0 h1 hg hs t, ← regroup op _ gi _ hh]
              simp only [Bool.false_xor]
              apply specL_congr
              intro i hi
              rw [if_pos (mem_liveIdx hi)]
              rw [List.all_eq_true] at hch
              have := hch i hi
              simp only [beq_iff_eq] at this
              rw [ih op _ _ false this (wf hsat gi i t), Bool.false_xor]
              rfl
            · cases h
        · cases h
      | [] :: ps', h => simp at h
      | [], h => simp at h

end


/-! ## The window between two copies -/

/-- Common prefix length. -/
def cpl : Path → Path → Nat
  | a :: p, b :: q => if a = b then cpl p q + 1 else 0
  | _, _ => 0

/-- **The window of two paths**: the common head part (one warp, read at one
time) cancels; the middle parts give `hop_skew`'s window; the common tail part
(next to the source) adds its band width (`prefix_skew`). Falls back to the
whole-path window when the claimed decomposition does not hold. -/
def pairW (d : Design) (p q : Path) : Nat :=
  let c := cpl p q
  let a := p.drop c
  let a' := q.drop c
  let z := cpl a.reverse a'.reverse
  if p.take c = q.take c ∧ a.drop (a.length - z) = a'.drop (a'.length - z) then
    max (phi d (a.take (a.length - z)) - plo d (a'.take (a'.length - z)))
        (phi d (a'.take (a'.length - z)) - plo d (a.take (a.length - z))) +
      (phi d (a.drop (a.length - z)) - plo d (a.drop (a.length - z)))
  else max (phi d p - plo d q) (phi d q - plo d p)

theorem pathOK_sub {d : Design} {p q : Path} (hp : pathOK d p = true) (h : ∀ e ∈ q, e ∈ p) : pathOK d q = true := by
  unfold pathOK at *; rw [List.all_eq_true] at *; exact fun e he => hp e (h e he)

theorem plo_le_phi {d : Design} (hwf : d.WF) : ∀ (p : Path), pathOK d p = true → plo d p ≤ phi d p
  | [], _ => Nat.le_refl _
  | (gi, i) :: r, h => by
      simp only [pathOK, List.all_cons, Bool.and_eq_true, decide_eq_true_eq] at h
      have := (hwf _ (gt_mem d h.1.1)).2.2.2.2.1
      have := plo_le_phi hwf r h.2
      simp only [plo, phi]; omega

section
variable {d : Design} {x : Fin d.n → Sig} (hsat : SatPin d plG x)

theorem pairW_sound (hwf : d.WF) (p q : Path) (hp : pathOK d p = true) (hq : pathOK d q = true) (t : Nat) :
    tau hsat p t ≤ tau hsat q t + pairW d p q ∧ tau hsat q t ≤ tau hsat p t + pairW d p q := by
  unfold pairW
  simp only
  split
  · rename_i hc
    obtain ⟨hpre, hsuf⟩ := hc
    generalize cpl p q = c at hpre hsuf ⊢
    generalize ha : p.drop c = a at hsuf ⊢
    generalize ha' : q.drop c = a' at hsuf ⊢
    generalize cpl a.reverse a'.reverse = z at hsuf ⊢
    have ep : p = p.take c ++ a := by rw [← ha, List.take_append_drop]
    have eq' : q = p.take c ++ a' := by rw [← ha', hpre, List.take_append_drop]
    have eA : a = a.take (a.length - z) ++ a.drop (a.length - z) := (List.take_append_drop _ _).symm
    have eA' : a' = a'.take (a'.length - z) ++ a.drop (a.length - z) := by
      rw [hsuf]; exact (List.take_append_drop _ _).symm
    have okA : pathOK d a = true := pathOK_sub hp (fun e he => by rw [← ha] at he; exact List.mem_of_mem_drop he)
    have okA' : pathOK d a' = true := pathOK_sub hq (fun e he => by rw [← ha'] at he; exact List.mem_of_mem_drop he)
    have okM : pathOK d (a.take (a.length - z)) = true := pathOK_sub okA (fun e he => List.mem_of_mem_take he)
    have okM' : pathOK d (a'.take (a'.length - z)) = true := pathOK_sub okA' (fun e he => List.mem_of_mem_take he)
    have okZ : pathOK d (a.drop (a.length - z)) = true := pathOK_sub okA (fun e he => List.mem_of_mem_drop he)
    generalize a.take (a.length - z) = m at eA okM ⊢
    generalize a'.take (a'.length - z) = m' at eA' okM' ⊢
    generalize a.drop (a.length - z) = zz at eA eA' okZ ⊢
    have tp : tau hsat p t = tau hsat zz (tau hsat m (tau hsat (p.take c) t)) := by
      conv => lhs; rw [ep, tau_append, eA, tau_append]
    have tq : tau hsat q t = tau hsat zz (tau hsat m' (tau hsat (p.take c) t)) := by
      conv => lhs; rw [eq', tau_append, eA', tau_append]
    rw [tp, tq]
    generalize tau hsat (p.take c) t = u
    have wm := tau_warp hsat m okM
    have wm' := tau_warp hsat m' okM'
    have wz := tau_warp hsat zz okZ
    have hlz := plo_le_phi hwf zz okZ
    have hs := hop_skew wm wm' (W := max (phi d m - plo d m') (phi d m' - plo d m))
      (by have := Nat.le_max_right (phi d m - plo d m') (phi d m' - plo d m); omega)
      (by have := Nat.le_max_left (phi d m - plo d m') (phi d m' - plo d m); omega) u
    exact ⟨prefix_skew wz hlz _ _ _ hs.1, prefix_skew wz hlz _ _ _ hs.2⟩
  · have wp := tau_warp hsat p hp
    have wq := tau_warp hsat q hq
    exact hop_skew wp wq
      (by have := Nat.le_max_right (phi d p - plo d q) (phi d q - plo d p); omega)
      (by have := Nat.le_max_left (phi d p - plo d q) (phi d q - plo d p); omega) t

end

end Formal.Core.XAudit.Events6
