import Formal.Timing.SpecChainM
import Formal.Target.NetBase

/-!
# A copy map stored as chunked binary trees, checked against a chunked gate list (shard C)

Kernel-checkable data layout for `SpecChainM` on a big netlist whose gates are given in chunks
`cs` of `C` gates (gate `i` drives node `i`, `outsOK`): per chunk a perfect binary tree of depth
`d` (`2^d ≥ C`) whose leaves are `cpIn` of the chunk's gates (the input of a copy gate, else
`none`), padded with `none`. A lookup is `O(log C)` reduction steps, so a checker can follow
hundreds of thousands of chain links. `cmSound_of_chunks` turns per-chunk facts (each a small
`decide`) into `CmSound`; `collapse_chunks` gives the collapsed relation for every logic gate.
Nothing here is about a particular netlist.
-/

namespace Formal.Timing.ChunkCM
open Formal.Target Formal.Timing.SpecSettle Formal.Timing.SpecChain Formal.Timing.SpecChainM

/-- The input of a copy gate (`k = 1`, INIT `0b10`), `none` for any other gate. -/
def cpIn (g : Gate) : Option Nat := if g.k == 1 && g.init == 2 then some (g.ins.getD 0 0) else none

/-- `cpIn` restricted to the gates that `keep` keeps (the circuit drops the environment's drivers). -/
def cpK (keep : Gate → Bool) (g : Gate) : Option Nat := if keep g then cpIn g else none

theorem cpIn_some {g : Gate} {y : Nat} (h : cpIn g = some y) :
    g.k = 1 ∧ g.init = 2 ∧ g.ins.getD 0 0 = y := by
  unfold cpIn at h
  split at h
  · rename_i hc
    simp only [Bool.and_eq_true, beq_iff_eq] at hc
    simp only [Option.some.injEq] at h
    exact ⟨hc.1, hc.2, h⟩
  · cases h

/-- Binary trees with `Option Nat` leaves. -/
inductive BT
  | lf (v : Option Nat)
  | nd (l r : BT)

/-- Lookup in a tree of depth `d`. -/
def BT.get : BT → Nat → Nat → Option Nat
  | .lf v, _, _ => v
  | .nd _ _, 0, _ => none
  | .nd l r, d + 1, i => if i < 2 ^ d then l.get d i else r.get d (i - 2 ^ d)

def BT.toList : BT → List (Option Nat)
  | .lf v => [v]
  | .nd l r => l.toList ++ r.toList

/-- Perfect of depth `d`. -/
def BT.perf : BT → Nat → Bool
  | .lf _, 0 => true
  | .nd l r, d + 1 => l.perf d && r.perf d
  | _, _ => false

theorem BT.length_toList : ∀ (t : BT) (d : Nat), t.perf d = true → t.toList.length = 2 ^ d
  | .lf _, 0, _ => rfl
  | .nd l r, d + 1, h => by
    simp only [BT.perf, Bool.and_eq_true] at h
    simp only [BT.toList, List.length_append, l.length_toList d h.1, r.length_toList d h.2]
    rw [Nat.pow_succ]; omega
  | .lf _, _ + 1, h => by simp [BT.perf] at h
  | .nd _ _, 0, h => by simp [BT.perf] at h

theorem BT.get_eq : ∀ (t : BT) (d i : Nat), t.perf d = true → i < 2 ^ d → t.get d i = t.toList.getD i none
  | .lf v, 0, i, _, hi => by
    have : i = 0 := by simp at hi; omega
    subst this; rfl
  | .nd l r, d + 1, i, h, hi => by
    simp only [BT.perf, Bool.and_eq_true] at h
    have hl := l.length_toList d h.1
    simp only [BT.get, BT.toList, List.getD_eq_getElem?_getD]
    split
    · rename_i hi'
      rw [List.getElem?_append_left (by omega), l.get_eq d i h.1 hi', List.getD_eq_getElem?_getD]
    · rename_i hi'
      rw [Nat.pow_succ] at hi
      rw [List.getElem?_append_right (by omega), hl, r.get_eq d _ h.2 (by omega), List.getD_eq_getElem?_getD]
  | .lf _, _ + 1, _, h, _ => by simp [BT.perf] at h
  | .nd _ _, 0, _, h, _ => by simp [BT.perf] at h

theorem getD_map_rep (f : Gate → Option Nat) : ∀ (l : List Gate) (n o : Nat),
    (l.map f ++ List.replicate n none).getD o none = if o < l.length then f (l.getD o default) else none
  | [], n, o => by
    simp only [List.map_nil, List.nil_append, List.length_nil, Nat.not_lt_zero, ↓reduceIte,
      List.getD_eq_getElem?_getD, List.getElem?_replicate]
    split <;> rfl
  | g :: l, n, 0 => by simp
  | g :: l, n, o + 1 => by
    simp only [List.map_cons, List.cons_append, List.getD_cons_succ, List.length_cons]
    rw [getD_map_rep f l n o]
    by_cases h : o < l.length
    · simp [h]
    · simp [h, show ¬ (o + 1 < l.length + 1) by omega]

theorem getD_mem_of_lt {α : Type} {l : List α} {o : Nat} {d : α} (h : o < l.length) : l.getD o d ∈ l := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]; exact List.getElem_mem h

/-- The copy map read from chunk trees `tl` (chunk size `C`, tree depth `d`). -/
def cmOf (tl : List BT) (C d : Nat) (w : Nat) : Option Nat := (tl.getD (w / C) (.lf none)).get d (w % C)

/-- The gate driving node `w`, from the chunks. -/
def gaOf (cs : List (List Gate)) (C : Nat) (w : Nat) : Gate := (cs.getD (w / C) []).getD (w % C) default

/-- What is checked per chunk `c` (one `decide` each). -/
def ChunkFact (tl : List BT) (cs : List (List Gate)) (keep : Gate → Bool) (C d c : Nat) : Prop :=
  (tl.getD c (.lf none)).perf d = true ∧
  (tl.getD c (.lf none)).toList =
    (cs.getD c []).map (cpK keep) ++ List.replicate (2 ^ d - (cs.getD c []).length) none ∧
  outsOK (cs.getD c []) (C * c) = true ∧ (cs.getD c []).length ≤ C

theorem out_of_outsOK : ∀ (l : List Gate) (s o : Nat), outsOK l s = true → o < l.length →
    (l.getD o default).out = s + o
  | [], _, _, _, h => by simp at h
  | g :: l, s, o, h, ho => by
    simp only [outsOK, Bool.and_eq_true, beq_iff_eq] at h
    cases o with
    | zero => simpa using h.1
    | succ o =>
      have := out_of_outsOK l (s + 1) o h.2 (by simp at ho; omega)
      simp only [List.getD_cons_succ]; rw [this]; omega

theorem cmSound_of_chunks {N : Net} {tl : List BT} {cs : List (List Gate)} {keep : Gate → Bool} {C d : Nat}
    (hC : 0 < C) (hCd : C ≤ 2 ^ d) (hN : N.gates = cs.flatten.filter keep) (hlen : tl.length = cs.length)
    (hf : ∀ c, c < cs.length → ChunkFact tl cs keep C d c) :
    CmSound N (cmOf tl C d) (gaOf cs C) := by
  intro w y h
  unfold cmOf at h
  have hc : w / C < cs.length := by
    by_contra hc
    rw [List.getD_eq_getElem?_getD, List.getElem?_eq_none (by omega)] at h
    simp [BT.get] at h
  obtain ⟨hp, ht, ho, hl⟩ := hf _ hc
  have hmod : w % C < C := Nat.mod_lt _ hC
  rw [BT.get_eq _ _ _ hp (by omega), ht, getD_map_rep] at h
  have hgD : gaOf cs C w = (cs.getD (w / C) []).getD (w % C) default := rfl
  have hmem : cs.getD (w / C) [] ∈ cs := getD_mem_of_lt hc
  generalize cs.getD (w / C) [] = gc at h ho hl hgD hmem
  split at h
  · rename_i hlt
    unfold cpK at h
    split at h
    case isFalse => cases h
    rename_i hkeep
    obtain ⟨k1, k2, k3⟩ := cpIn_some h
    refine ⟨?_, ?_, by rw [hgD]; exact k1, by rw [hgD]; exact k2, by rw [hgD]; exact k3⟩
    · rw [hgD, hN, List.mem_filter, List.mem_flatten]
      exact ⟨⟨gc, hmem, getD_mem_of_lt hlt⟩, hkeep⟩
    · rw [hgD, out_of_outsOK _ _ _ ho hlt]; exact Nat.div_add_mod w C
  · cases h

/-- Per chunk: the view lists one `PinData` per gate, and every logic gate's pins check. -/
def chunkViewOK (cm : Nat → Option Nat) (keep : Gate → Bool) (gs : List Gate) (vs : List PinData) : Bool :=
  gs.length == vs.length && (gs.zip vs).all fun e => !(keep e.1) || (cpIn e.1).isSome || pinsOKm cm e.1 e.2

/-- The collapsed view: every logic gate with its pin data. -/
def logicView (cs : List (List Gate)) (keep : Gate → Bool) (vss : List (List PinData)) : List (Gate × PinData) :=
  (cs.zip vss).flatMap fun p => (p.1.zip p.2).filter fun e => keep e.1 && (cpIn e.1).isNone

theorem mem_logicView {cs : List (List Gate)} {keep : Gate → Bool} {vss : List (List PinData)}
    {e : Gate × PinData} (h : e ∈ logicView cs keep vss) :
    ∃ p ∈ cs.zip vss, e ∈ p.1.zip p.2 ∧ keep e.1 = true ∧ (cpIn e.1).isNone = true := by
  simp only [logicView, List.mem_flatMap, List.mem_filter, Bool.and_eq_true] at h
  obtain ⟨p, hp, he, hk, hn⟩ := h
  exact ⟨p, hp, he, hk, hn⟩

/-- Every logic gate of the chunks is in the view (completeness of the collapse). -/
theorem logicView_complete {cs : List (List Gate)} {keep : Gate → Bool} {vss : List (List PinData)}
    (hl : cs.length = vss.length)
    (hv : ∀ p ∈ cs.zip vss, p.1.length = p.2.length) {g : Gate} (hg : g ∈ cs.flatten) (hk : keep g = true)
    (hn : cpIn g = none) : ∃ pv, (g, pv) ∈ logicView cs keep vss := by
  obtain ⟨gc, hgc, hgg⟩ := List.mem_flatten.mp hg
  obtain ⟨j, hj, rfl⟩ := List.getElem_of_mem hgc
  have hj' : j < vss.length := by omega
  have hp : (cs[j], vss[j]) ∈ cs.zip vss := by
    rw [List.mem_iff_getElem]; exact ⟨j, by simp; omega, by simp⟩
  have hlen := hv _ hp
  obtain ⟨o, ho, rfl⟩ := List.getElem_of_mem hgg
  refine ⟨vss[j][o]'(by simp at hlen; omega), ?_⟩
  simp only [logicView, List.mem_flatMap, List.mem_filter]
  refine ⟨_, hp, ?_, by simp [hn, hk]⟩
  rw [List.mem_iff_getElem]
  exact ⟨o, by simp; simp at hlen; omega, by simp⟩

/-- **Collapse over chunked data.** -/
theorem collapse_chunks {p : DelayPar} {N : Net} {x : Beh} (hp : Sane p) (hNw : N.WF) (hb : Behaves p N x)
    {tl : List BT} {cs : List (List Gate)} {keep : Gate → Bool} {vss : List (List PinData)} {C d : Nat}
    (hC : 0 < C) (hCd : C ≤ 2 ^ d) (hN : N.gates = cs.flatten.filter keep) (hlen : tl.length = cs.length)
    (hf : ∀ c, c < cs.length → ChunkFact tl cs keep C d c)
    (hv : ∀ p ∈ cs.zip vss, chunkViewOK (cmOf tl C d) keep p.1 p.2 = true) :
    ∃ c : ℚ, 0 ≤ c ∧ c ≤ 1 ∧ ∀ e ∈ logicView cs keep vss,
      CGateOK p c e.1 (fun i => ((toPCs (cmOf tl C d) (gaOf cs C) e.1 e.2).getD i ⟨0, []⟩).src)
        (pinArcs e.1 (toPCs (cmOf tl C d) (gaOf cs C) e.1 e.2))
        (cStart p e.1 (toPCs (cmOf tl C d) (gaOf cs C) e.1 e.2)) x := by
  apply collapse_net_m hp hNw hb (cmSound_of_chunks hC hCd hN hlen hf)
  intro e he
  obtain ⟨q, hq, he', hk, hn⟩ := mem_logicView he
  have hok := hv q hq
  simp only [chunkViewOK, Bool.and_eq_true, beq_iff_eq, List.all_eq_true, Bool.or_eq_true] at hok
  refine ⟨?_, ?_⟩
  · rw [hN, List.mem_filter, List.mem_flatten]
    exact ⟨⟨q.1, (List.of_mem_zip hq).1, (List.of_mem_zip he').1⟩, hk⟩
  · rcases hok.2 e he' with (h | h) | h
    · simp [hk] at h
    · simp [Option.isNone_iff_eq_none] at hn; simp [hn] at h
    · exact h

end Formal.Timing.ChunkCM
