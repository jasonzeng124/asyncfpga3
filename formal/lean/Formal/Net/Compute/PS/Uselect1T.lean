import Formal.Net.Compute.PS.Uselect1
import Formal.Gen.Compute.PSMap.Uselect1T.All
import Mathlib.Data.List.Nodup

/-!
# THE target's `uselect1` unit, timed: from held inputs to the op at the output (shard C, 2026-11-09)

**Problem.** `PS.Uselect1.uselect1_ps` says what the decoded `uselect1` gates compute once they are
settled (zero-delay equations). When are they? In every behaviour of THE decoded netlist, for every
`(g, κ)`: if the unit's 64 input nodes hold on `[T0, T1]`, does the output word carry the op of the
input words from some fixed time on?

**Proved** (`uselect1_timed`): for every sane `p` (`g > 0`, `0 ≤ κ ≤ 1`) and every `x` with
`Behaves p DecodedPS.net x`, if `e0Node k`, `e1Node k` (`k < 32`) are constant on `[T0, T1]`, then for
every `t` with `T0 + ⌈(1+κ)g⌉ · 8815 ≤ t ≤ T1` the 32 `zNode` bits at `t` are
`select (sgt d (-1)) d (0 - d)` with `d = e0 - e1` of the input words (at `t`, = at `T0`).
`8815` = `Uselect1T.D`, the unit's longest prjxray slow-max path (ps).

Route: the generated `Gen/Compute/PSMap/Uselect1T` (untrusted `formal/tools/compute/ps/psmapT.py`)
lists the 2,645 gates driving `S` in topological order, each PICKED from a decoded chunk `g0xx` by
skip counts (so every listed gate is a gate of `DecodedPS.net` by construction: `gs_sub`), with a
slow-max depth `SN` (a search tree); 31 pieces each decide `certOKN` (against the outputs of earlier
pieces), their output lists, and `SN ≤ D`; `cover_ok` decides that every node of `S` is an output of
a listed gate. `SpecSettleSym.certN_sound_net` then gives every listed gate constant on
`[T0 + C·SN out, T1]` with its gate equation inside its inputs' windows; output-uniqueness
(`net_wf`) makes the listed gate THE driver of its node, so `Settled DecodedPS.net S (x · t)`, and
`uselect1_ps` finishes.

**Not shown.** That the inputs hold (the token protocol); that `T1 - T0` is large enough in a run;
the other 19 units.
-/

namespace Formal.Net.Compute.PS.Uselect1T
open Formal.Target Formal.Timing.SpecSettle Formal.Net.Compute Formal.Net.Compute.OnDecoded
open Formal.Net.Compute.PS.Uselect1 Formal.Net.GcdHw

namespace G
export Formal.Gen.Compute.PSMap.Uselect1T (pickR stepP chunk seg A gs pcs nP oAll Kof SN known bnd pieceOK
  pieces_ok cover_ok known_ok ptT)
end G
open G

/-- The unit's slow-max depth (ps). -/
abbrev D : Nat := Formal.Gen.Compute.PSMap.Uselect1T.D

theorem D_eq : D = 8815 := rfl

/-! ## Membership by construction -/

theorem pickR_sub : ∀ (l : List Gate) (ds : List Nat) (g : Gate), g ∈ pickR l ds → g ∈ l
  | [], ds, g, h => by
    have e : pickR [] ds = [] := rfl
    rw [e] at h; exact absurd h List.not_mem_nil
  | a :: l, ds, g, h => by
    have e : pickR (a :: l) ds = stepP a (pickR l) ds := rfl
    rw [e] at h
    match ds, h with
    | [], h => simp [stepP] at h
    | 0 :: ds, h =>
      simp only [stepP, List.mem_cons] at h
      rcases h with rfl | h
      · exact List.mem_cons_self
      · exact List.mem_cons_of_mem _ (pickR_sub l ds g h)
    | (d + 1) :: ds, h =>
      simp only [stepP] at h
      exact List.mem_cons_of_mem _ (pickR_sub l (d :: ds) g h)

open Formal.Gen.Compute.PSMap.Uselect1 in
theorem chunk_sub (c : Nat) (g : Gate) (h : g ∈ chunk c) : g ∈ DecodedPS.net.gates := by
  unfold chunk at h
  split at h
  · exact gin007 g h
  · exact gin032 g h
  · exact gin033 g h
  · exact gin034 g h
  · exact gin035 g h
  · exact gin037 g h
  · exact gin039 g h
  · exact gin045 g h
  · exact gin046 g h
  · exact gin047 g h
  · exact gin048 g h
  · exact gin049 g h
  · exact gin050 g h
  · exact absurd h List.not_mem_nil

theorem seg_sub (s : Nat × List Nat) (g : Gate) (h : g ∈ seg s) : g ∈ DecodedPS.net.gates :=
  chunk_sub s.1 g (pickR_sub _ _ g h)

theorem A_sub (i : Nat) (g : Gate) (h : g ∈ A i) : g ∈ DecodedPS.net.gates := by
  unfold A at h
  obtain ⟨s, -, hs⟩ := List.mem_flatMap.mp h
  exact seg_sub s g hs

theorem gs_mem (g : Gate) (h : g ∈ gs) : ∃ i, i < nP ∧ g ∈ A i := by
  unfold gs at h
  obtain ⟨l, hl, hg⟩ := List.mem_flatten.mp h
  obtain ⟨i, hi, rfl⟩ := List.mem_map.mp hl
  exact ⟨i, List.mem_range.mp hi, hg⟩

theorem gs_sub : ∀ g ∈ gs, g ∈ DecodedPS.net.gates := fun g h => by
  obtain ⟨i, -, hg⟩ := gs_mem g h
  exact A_sub i g hg

theorem A_mem_gs {i : Nat} (hi : i < nP) {g : Gate} (h : g ∈ A i) : g ∈ gs := by
  unfold gs
  exact List.mem_flatten.mpr ⟨A i, List.mem_map.mpr ⟨i, List.mem_range.mpr hi, rfl⟩, h⟩

/-! ## The pieces' certificates compose -/

theorem certOKN_app (SN' : Nat → Nat) : ∀ (K : List Nat) (a b : List Gate), certOKN SN' K a = true →
    certOKN SN' ((a.map Gate.out).reverse ++ K) b = true → certOKN SN' K (a ++ b) = true
  | K, [], b, _, h2 => by simpa using h2
  | K, g :: a, b, h1, h2 => by
    simp only [certOKN, Bool.and_eq_true] at h1
    simp only [List.cons_append, certOKN, Bool.and_eq_true]
    refine ⟨h1.1, certOKN_app SN' (g.out :: K) a b h1.2 ?_⟩
    simpa [List.map_cons, List.reverse_cons, List.append_assoc] using h2

theorem Kof_zero (os : List (List Nat)) (K : List Nat) : Kof os K 0 = K := by
  cases os <;> rfl

theorem chain (SN' : Nat → Nat) : ∀ (As : List (List Gate)) (os : List (List Nat)) (K : List Nat),
    As.length = os.length →
    (∀ i, i < As.length → certOKN SN' (Kof os K i) (As.getD i []) = true ∧
      (As.getD i []).map Gate.out = os.getD i []) →
    certOKN SN' K As.flatten = true
  | [], _, _, _, _ => rfl
  | a :: As, [], _, hl, _ => by simp at hl
  | a :: As, o :: os, K, hl, h => by
    obtain ⟨h1, h2⟩ := h 0 (by simp)
    rw [Kof_zero] at h1
    simp only [List.getD_cons_zero] at h1 h2
    simp only [List.flatten_cons]
    refine certOKN_app SN' K a _ h1 ?_
    rw [h2]
    apply chain SN' As os (o.reverse ++ K) (by simpa using hl)
    intro i hi
    have := h (i + 1) (by simp; omega)
    simp only [List.getD_cons_succ] at this
    exact this

theorem oAll_len : oAll.length = nP := rfl

theorem getD_As {i : Nat} (hi : i < nP) : ((List.range nP).map A).getD i [] = A i := by
  simp [List.getD_eq_getElem?_getD, hi]

theorem piece (i : Nat) (hi : i < nP) :
    certOKN SN (Kof oAll known i) (A i) = true ∧ (A i).map Gate.out = oAll.getD i [] ∧
      ∀ g ∈ A i, bnd g = true := by
  have h := pieces_ok i hi
  unfold pieceOK at h
  simp only [Bool.and_eq_true, beq_iff_eq, List.all_eq_true] at h
  exact ⟨h.1.1, h.1.2, h.2⟩

theorem cert_ok : certOKN SN known gs = true := by
  unfold gs
  apply chain SN _ oAll known (by simp [oAll_len])
  intro i hi
  simp only [List.length_map, List.length_range] at hi
  rw [getD_As hi]
  exact ⟨(piece i hi).1, (piece i hi).2.1⟩

theorem bnd_gs : ∀ g ∈ gs, bnd g = true := fun g h => by
  obtain ⟨i, hi, hg⟩ := gs_mem g h
  exact (piece i hi).2.2 g hg

theorem cover : ∀ n ∈ S, ∃ g ∈ gs, g.out = n := by
  intro n hn
  have h := (mem_iff _ _).mp (cover_ok n hn)
  by_cases hj : ptT.find n < nP
  · rw [← (piece _ hj).2.1] at h
    obtain ⟨g, hg, rfl⟩ := List.mem_map.mp h
    exact ⟨g, A_mem_gs hj hg, rfl⟩
  · have e : oAll.getD (ptT.find n) [] = [] := by
      rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by rw [oAll_len]; omega)]; rfl
    rw [e] at h
    exact absurd h List.not_mem_nil

theorem known_mem (n : Nat) (h : n ∈ known) : ∃ k, k < 32 ∧ (n = e0Node k ∨ n = e1Node k) := by
  unfold known at h
  rcases List.mem_append.mp h with h | h
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
    exact ⟨k, List.mem_range.mp hk, Or.inl rfl⟩
  · obtain ⟨k, hk, rfl⟩ := List.mem_map.mp h
    exact ⟨k, List.mem_range.mp hk, Or.inr rfl⟩

/-! ## The timed unit theorem -/

set_option maxRecDepth 100000 in
/-- **THE target's decoded `uselect1` unit, timed.** For every sane `(g, κ)` and every behaviour of the
decoded netlist: if the unit's 64 input nodes hold on `[T0, T1]`, then at every `t` with
`T0 + ⌈(1+κ)g⌉·8815 ≤ t ≤ T1` the output word is `d = e0 - e1; (d > -1) ? d : 0 - d` of the input
words at `t`. -/
theorem uselect1_timed (p : DelayPar) (hp : Sane p) (x : Beh) (hb : Behaves p DecodedPS.net x)
    (T0 T1 : Nat)
    (hin : ∀ k, k < 32 → ∀ t, T0 ≤ t → t ≤ T1 →
      x (e0Node k) t = x (e0Node k) T0 ∧ x (e1Node k) t = x (e1Node k) T0)
    (t : Nat) (ht0 : T0 + cScale p * D ≤ t) (ht1 : t ≤ T1) :
    word ((fun w => x w t) ∘ zNode) 32 =
      Ops.select (Ops.cmpi .sgt 32 (Ops.subi 32 (word ((fun w => x w t) ∘ e0Node) 32)
          (word ((fun w => x w t) ∘ e1Node) 32)) 4294967295)
        (Ops.subi 32 (word ((fun w => x w t) ∘ e0Node) 32) (word ((fun w => x w t) ∘ e1Node) 32))
        (Ops.subi 32 0 (Ops.subi 32 (word ((fun w => x w t) ∘ e0Node) 32)
          (word ((fun w => x w t) ∘ e1Node) 32))) := by
  apply uselect1_ps
  -- the input nodes hold on their windows `[T0 + C·0, T1]`
  have hk : ∀ n ∈ known, ConstW (fun n => T0 + cScale p * SN n) (fun _ => T1) x n := by
    intro n hn t' h1 h2
    have h0 : SN n = 0 := by
      have := List.all_eq_true.mp known_ok n hn
      simpa using this
    simp only [h0, Nat.mul_zero, Nat.add_zero] at h1 ⊢
    obtain ⟨k, hk, e | e⟩ := known_mem n hn <;> subst e
    · exact (hin k hk t' h1 h2).1
    · exact (hin k hk t' h1 h2).2
  have hset := certN_sound_net hp DecodedPS.net_wf hb SN T0 T1 known gs gs_sub hk cert_ok
  have win : ∀ n, SN n ≤ D → T0 + cScale p * SN n ≤ t := fun n h =>
    le_trans (Nat.add_le_add_left (Nat.mul_le_mul_left _ h) _) ht0
  intro g hg hgS
  obtain ⟨g', hg', hout⟩ := cover g.out hgS
  have e : g' = g := List.inj_on_of_nodup_map DecodedPS.net_wf.2 (gs_sub g' hg') hg hout
  subst e
  have hb' := bnd_gs g' hg'
  simp only [bnd, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hb'
  exact (hset g' hg').2 t (win _ hb'.1) ht1 (fun i hi => ⟨win _ (hb'.2 i hi), ht1⟩)

end Formal.Net.Compute.PS.Uselect1T
