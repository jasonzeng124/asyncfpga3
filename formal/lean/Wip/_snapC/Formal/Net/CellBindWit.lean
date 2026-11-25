import Formal.Net.CellBindGcd
import Formal.Net.CapstoneWitness3

/-!
# Probe C-O4: non-vacuity of H_GEN (jointly with H_BUNDLE and H_START_ONCE), quiet run only

`gen_frozen`: freezing any run that satisfies an operator's `Cell` at tick 0 (every request,
acknowledge and internal node held at 0, every bus held at its tick-0 value) satisfies that
operator's `GenCell`, provided the operator has a width the generated netlists cover
(`shapeB`: forks of 2..6 branches, compute joins of 1..2 inputs, branch joins of 2).
`gcd_ops_shape`: every gcd_hw operator has such a width.

`gcd_gen_witness`: freezing 8t's run (`Formal.Net.CapNet.Wit.gcd_hw_joint_witness3`, a = 12, b = 18) gives a run of
the gcd_hw network that satisfies H_GEN, H_BUNDLE and H_START_ONCE together. So the
hypotheses of `gcd_hw_circuit_safe_gen` are jointly satisfiable, but only by a run in which
nothing moves: this witness exercises no gate transition. The per-cell active runs of this
probe (`Chain.fastfall_hazard`, `Gcd.tree_needs_persist`, `Gcd.mut_breaks`) show transitions
of single cells under the per-gate relations; no active whole-network run satisfying H_GEN is
built (open).
-/

namespace Formal.Net.CellBind.Wit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CellBind Formal.Net.CellBind.Ops Formal.Net.Ops.Gen

def q : Trace := fun _ => false
def frz (c : Chan) : Chan := ⟨q, q, fun _ => c.dat 0⟩

theorem cnodeQ {α : Type} {F : α → Bool → Bool} {p : Nat → α} : CNode F p q :=
  ⟨q, fun _ h => absurd rfl h, fun _ _ => rfl⟩

theorem lutQ {α : Type} {F : α → Bool} {p : Nat → α} : LutSI F p q := fun _ h => absurd rfl h

theorem leafQ {ls : List Trace} {r : Trace} (h : ∀ l ∈ ls, l = q) : LeafPersist ls r := by
  intro l hl t hm; rw [h l hl] at hm; exact absurd rfl hm

theorem chainQ : GenChain q q :=
  ⟨1, fun _ => .buf 0, fun _ => q, Nat.le_refl 1, rfl, rfl, fun _ _ _ => Nat.zero_le 1,
    fun _ _ _ _ h => absurd rfl h, fun _ h => absurd rfl h, fun _ _ => rfl⟩

theorem bufQ : GenBufChain q q :=
  ⟨1, fun _ => q, Nat.le_refl 1, rfl, rfl, fun _ _ _ _ h => absurd rfl h, fun _ h => absurd rfl h,
    fun _ _ => rfl⟩

theorem treeQ : ∀ ls : List Trace, (∀ l ∈ ls, l = q) → 2 ≤ ls.length → ls.length ≤ 6 → ForkTree q ls
  | [a0, a1], h, _, _ => by
    obtain rfl := h a0 (by simp); obtain rfl := h a1 (by simp); exact cnodeQ
  | [a0, a1, a2], h, _, _ => by
    obtain rfl := h a0 (by simp); obtain rfl := h a1 (by simp); obtain rfl := h a2 (by simp)
    exact cnodeQ
  | [a0, a1, a2, a3], h, _, _ => by
    obtain rfl := h a0 (by simp); obtain rfl := h a1 (by simp); obtain rfl := h a2 (by simp)
    obtain rfl := h a3 (by simp); exact cnodeQ
  | [a0, a1, a2, a3, a4], h, _, _ => ⟨q, cnodeQ, cnodeQ, rfl, leafQ (fun l hl => h l (by
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hl ⊢
      rcases hl with h' | h' | h' | h' <;> simp [h']))⟩
  | [a0, a1, a2, a3, a4, a5], h, _, _ =>
    ⟨q, q, cnodeQ, cnodeQ, cnodeQ, rfl, rfl, leafQ h⟩
  | [], _, h2, _ => by simp at h2
  | [_], _, h2, _ => by simp at h2
  | _ :: _ :: _ :: _ :: _ :: _ :: _ :: _, _, _, h6 => by simp at h6

variable {n : Nat}

/-- The widths the generated netlists cover. -/
def shapeB : K n → Bool
  | .forkG _ os => decide (2 ≤ os.length ∧ os.length ≤ 6)
  | .forkH _ os _ _ _ _ => decide (2 ≤ os.length ∧ os.length ≤ 6)
  | .join ins _ _ _ _ => decide (ins.length = 1 ∨ ins.length = 2)
  | .bjoin ins _ _ _ => decide (ins.length = 2)
  | _ => true

theorem mapq {ch : Fin n → Chan} (l : List (Fin n)) : ∀ x ∈ (l.map (fun c => frz (ch c))).map Chan.ack, x = q := by
  intro x hx; simp only [List.map_map, List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; rfl

theorem mapq' {ch : Fin n → Chan} (l : List (Fin n)) : ∀ x ∈ (l.map (fun c => frz (ch c))).map Chan.req, x = q := by
  intro x hx; simp only [List.map_map, List.mem_map] at hx; obtain ⟨_, _, rfl⟩ := hx; rfl

theorem gen_frozen (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (hc : Cell ch sv k) (hs : shapeB k = true) :
    GenCell (fun c => frz (ch c)) sv k := by
  cases k with
  | forkG i os =>
    have F : Fork.Fork (ch i) (os.map ch) := hc
    simp only [shapeB, decide_eq_true_eq] at hs
    exact ⟨treeQ _ (mapq os) (by simp; omega) (by simp; omega),
      fun o ho t h => by simp only [List.mem_map] at ho; obtain ⟨_, _, rfl⟩ := ho; exact absurd rfl h,
      fun o ho t => by
        obtain ⟨c, hc', rfl⟩ := List.mem_map.mp ho
        exact F.dat (ch c) (List.mem_map_of_mem hc') 0,
      rfl, fun o ho => by simp only [List.mem_map] at ho; obtain ⟨_, _, rfl⟩ := ho; rfl⟩
  | forkH i os l h d hs' =>
    have F : Fork.Fork (ch i) ((os.map Prod.fst).map ch) := hc
    simp only [shapeB, decide_eq_true_eq] at hs
    exact ⟨treeQ _ (mapq _) (by simp; omega) (by simp; omega),
      fun o ho t h => by simp only [List.mem_map] at ho; obtain ⟨_, _, rfl⟩ := ho; exact absurd rfl h,
      fun o ho t => by
        obtain ⟨c, hc', rfl⟩ := List.mem_map.mp ho
        exact F.dat (ch c) (List.mem_map_of_mem hc') 0,
      rfl, fun o ho => by simp only [List.mem_map] at ho; obtain ⟨_, _, rfl⟩ := ho; rfl⟩
  | join ins o e js jw =>
    have J : Join.Join (jg e js) (ins.map ch) (ch o) := hc
    simp only [shapeB, decide_eq_true_eq] at hs
    have hn : JoinNode q (ins.map (fun c => frz (ch c))) := by
      match ins, hs with
      | [_], _ => rfl
      | [_, _], _ => exact cnodeQ
      | [], hs => simp at hs
      | _ :: _ :: _ :: _, hs => simp at hs
    exact ⟨⟨q, hn, chainQ, rfl⟩, leafQ (mapq' ins),
      fun i hi t h => by simp only [List.mem_map] at hi; obtain ⟨_, _, rfl⟩ := hi; exact absurd rfl h,
      fun t => by have := J.dat 0; simpa [List.map_map, Function.comp_def, frz] using this,
      rfl, fun i hi => by simp only [List.mem_map] at hi; obtain ⟨_, _, rfl⟩ := hi; rfl⟩
  | bjoin ins o ec ed =>
    have J : Join.Join (bg ec ed) (ins.map ch) (ch o) := hc
    simp only [shapeB, decide_eq_true_eq] at hs
    have h2 : ∃ i0 i1, ins.map (fun c => frz (ch c)) = [i0, i1] ∧
        CNode j2F (fun t => (i0.req t, i1.req t)) (frz (ch o)).req := by
      match ins, hs with
      | [_, _], _ => exact ⟨_, _, rfl, cnodeQ⟩
      | [], hs => simp at hs
      | [_], hs => simp at hs
      | _ :: _ :: _ :: _, hs => simp at hs
    exact ⟨h2, fun i hi t h => by simp only [List.mem_map] at hi; obtain ⟨_, _, rfl⟩ := hi; exact absurd rfl h,
      fun t => by have := J.dat 0; simpa [List.map_map, Function.comp_def, frz] using this,
      rfl, fun i hi => by simp only [List.mem_map] at hi; obtain ⟨_, _, rfl⟩ := hi; rfl⟩
  | steerC j t f =>
    have S := hc
    exact ⟨fun _ => lutQ, lutQ, fun b _ => S.dat b 0, rfl, fun _ => rfl⟩
  | steerD j t f fd sw =>
    have S := hc
    exact ⟨fun _ => lutQ, lutQ, fun b _ => S.dat b 0, rfl, fun _ => rfl⟩
  | mux c x y z mw =>
    obtain ⟨j0, j1, M⟩ := hc
    exact ⟨q, q, cnodeQ, cnodeQ, cnodeQ, cnodeQ, ⟨q, lutQ, bufQ, rfl, leafQ (by simp)⟩,
      fun _ h => absurd rfl h, fun _ => M.dat 0, rfl, rfl, rfl, rfl, rfl, rfl⟩
  | muxn c x0 x1 x2 z nw =>
    obtain ⟨j, M⟩ := hc
    exact ⟨fun _ => q, fun _ _ => cnodeQ, fun _ _ => cnodeQ,
      ⟨q, fun _ h => absurd rfl h, chainQ, rfl, leafQ (by simp)⟩,
      fun _ h => absurd rfl h, fun _ h => M.dat 0 h, fun _ _ => rfl, rfl, fun _ _ => rfl, rfl⟩
  | amerge x y z w =>
    obtain ⟨g1, g2, A⟩ := hc
    have hd := A.dat 0
    rw [A.i2, A.iy] at hd
    exact ⟨q, q, cnodeQ, cnodeQ, ⟨q, chainQ, fun _ h => absurd rfl h⟩, fun _ h => absurd rfl h,
      fun _ h => absurd rfl h, fun _ => rfl, fun _ _ h => absurd h (by simp [frz, q]),
      fun _ => hd, rfl, rfl, rfl, rfl, rfl⟩
  | link i o =>
    exact ⟨q, cnodeQ, bufQ, chainQ, fun _ h => absurd h (by simp [q]), fun _ _ => rfl, rfl, rfl, rfl⟩
  | src z which d =>
    have S : Capstone.Src (ch z) (sv which) := hc
    exact ⟨lutQ, fun _ => S.dat 0, rfl⟩
  | sink i => exact ⟨fun _ h => absurd rfl h, rfl⟩

theorem gcd_ops_shape : ops.all shapeB = true := by decide +kernel

theorem gcd_shape (o : Fin NO) : shapeB (opAt o) = true := List.all_eq_true.mp gcd_ops_shape _ getD_mem

/-- **Joint non-vacuity (quiet run).** -/
theorem gcd_gen_witness :
    ∃ ch : Fin NC → Chan,
      (∀ o : Fin NO, GenCell ch (srcV 12 18) (opAt o)) ∧
      (∀ c, Held (ch c)) ∧
      (∀ t, cnt (riseB (ch start).req) t ≤ 1) := by
  obtain ⟨ch, hC, _, _, _⟩ := Formal.Net.CapNet.Wit.gcd_hw_joint_witness3
  refine ⟨fun c => frz (ch c), fun o => gen_frozen ch _ (opAt o) (hC o) (gcd_shape o),
    fun c t _ _ => rfl, fun t => ?_⟩
  have : ∀ t, cnt (riseB (frz (ch start)).req) t = 0 := by
    intro t; induction t with
    | zero => rfl
    | succ t ih => simp only [cnt]; rw [ih]; rfl
  rw [this]; exact Nat.zero_le 1

end Formal.Net.CellBind.Wit
