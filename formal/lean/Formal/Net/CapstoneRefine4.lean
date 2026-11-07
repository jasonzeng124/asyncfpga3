import Formal.Net.OpsBusy3Fn
import Formal.Net.CapstoneRefine3

/-!
# Probe C-8x4 (2): the physical gcd_hw capstone with the data fields derived

C-8x3's `gcd_hw_circuit_safe_phys4` assumed H_CELLS_B, the relaxed gate models, INCLUDING every
data field ("while this output is busy, its bus is the cell function of the input buses"). For a
SAMPLED channel that field is a timing claim. Here it is derived:

* the per-operator hypothesis is `CellP`: the handshake half (`HS`) and, for each output,
  EITHER its data field (`FieldOf`: a GHOST channel, whose bus no gate samples, so the observed
  bus is by definition the zero-delay value) OR a `Row` (a SAMPLED channel: tcheck row + H_TXWIN,
  H_FN, H_LAUNCH);
* **`gcd_hw_joint5`**: protocol and bundling of all 465 channels, by C-8x3's joint induction
  over time, where the bundling step at `t` uses: the row (sampled channels, any rank), the
  ghost field and the inputs (`hs_heldT_one`, ghost non-root channels), the certificate (the 26
  roots). No data field of a sampled channel is used;
* **`gcd_hw_cells_of_phys`**: then every sampled field follows from its row
  (`fieldOf_row`), so H_CELLS_B holds;
* **`gcd_hw_circuit_safe_phys5`**: every out0 latch is `Nat.gcd a b` from `CellP`,
  H_START_ONCE and the 26 root certificates;
* `sampIds` (221 channels: latch D, steer/mux/3-input-mux select, and out0, from
  `Wip/C8x2/classes.tsv`), `CellPcls` (rows exactly on the sampled channels, fields exactly on
  the others), **`gcd_hw_circuit_safe_phys5_cls`**;
* `gcd_hw_phys5_witness`: C-8t's run meets every hypothesis of `phys5` (all outputs as
  ghosts); `strict_phys5_hyps`: so does C-8x2's `chS`, where the OLD models fail.
-/

namespace Formal.Net.OpsBusy3
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.OpsBusy
open Formal.Net.OpsBusy2

variable {n : Nat}

/-- **The physical per-operator hypothesis**: handshake half, and per output a ghost field or a
row. -/
def CellP (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) : Prop :=
  ∃ w, HS ch sv k w ∧ ∀ c ∈ k.outsC, FieldOf ch sv k w c ∨ Row ch sv k w c

/-- The data field of each output, read off a relaxed cell. -/
theorem fieldOf_of_cellW {ch : Fin n → Chan} {sv : Nat → Nat} {k : K n} {w : Nat → Trace}
    (h : CellW ch sv k w) {c : Fin n} (hc : c ∈ k.outsC) : FieldOf ch sv k w c := by
  cases k with
  | forkG i os => exact fun t ht _ => (h : ForkB _ _).dat (ch c) (List.mem_map_of_mem hc) t ht
  | forkH i os l hh d hs =>
    exact fun t ht _ => (h : ForkB _ _).dat (ch c) (List.mem_map_of_mem hc) t ht
  | join ins o e js jw =>
    rw [List.mem_singleton.1 hc]
    intro t ht _
    rw [(h : JoinB _ _ _).dat t ht, List.map_map]; rfl
  | bjoin ins o ec ed =>
    rw [List.mem_singleton.1 hc]
    intro t ht _
    rw [(h : JoinB _ _ _).dat t ht, List.map_map]; rfl
  | steerC j tt f =>
    simp only [K.outsC, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with e | e <;> subst e
    · exact fun t ht _ => (h : SteerB _ _ _ _).dat true t ht
    · exact fun t ht _ => (h : SteerB _ _ _ _).dat false t ht
  | steerD j tt f fd sw =>
    simp only [K.outsC, List.mem_cons, List.not_mem_nil, or_false] at hc
    rcases hc with e | e <;> subst e
    · exact fun t ht _ => (h : SteerB _ _ _ _).dat true t ht
    · exact fun t ht _ => (h : SteerB _ _ _ _).dat false t ht
  | mux cc x y z mw =>
    rw [List.mem_singleton.1 hc]; exact fun t ht _ => (h : MuxB _ _ _ _ _ _ _).dat t ht
  | muxn cc x0 x1 x2 z nw =>
    rw [List.mem_singleton.1 hc]; exact fun t ht h3 => (h : MuxNB _ _ _ _ _).dat t ht h3
  | amerge x y z ww =>
    rw [List.mem_singleton.1 hc]; exact fun t ht _ => (h : AMergeB _ _ _ _ _).dat t ht
  | link i o =>
    rw [List.mem_singleton.1 hc]
    exact ⟨(h : LinkB _ _ _).H_LATCH_OPEN_B, (h : LinkB _ _ _).H_LATCH_HOLD_B⟩
  | src z which d =>
    rw [List.mem_singleton.1 hc]; exact fun t ht _ => (h : SrcB _ _).dat t ht
  | sink i => simp [K.outsC] at hc

/-- A relaxed cell meets `CellP` with every output a ghost. -/
theorem cellP_of_cellB {ch : Fin n → Chan} {sv : Nat → Nat} {k : K n} (hj : Disj k)
    (h : CellB ch sv k) : CellP ch sv k := by
  obtain ⟨w, hw⟩ := W_of_cellB h
  exact ⟨w, hs_of_cellW hj hw, fun c hc => Or.inl (fieldOf_of_cellW hw hc)⟩

/-- `CellP` + protocol and bundling everywhere ⇒ the relaxed cell (sampled fields derived). -/
theorem cellB_of_cellP {ch : Fin n → Chan} {sv : Nat → Nat} {k : K n} (hj : Disj k)
    (h : CellP ch sv k) (hP : ∀ c, Protocol (ch c)) (hH : ∀ c, Held (ch c)) : CellB ch sv k := by
  obtain ⟨w, hs, hd⟩ := h
  exact cellB_of_W (cellW_of_hs hj hs (fun c hc =>
    (hd c hc).elim id (fun row => fieldOf_row hj hs hP hH hc row)))

end Formal.Net.OpsBusy3

namespace Formal.Net.CapNet.Gcd
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.OpsBusy
open Formal.Net.CapstoneRefine Formal.Net.OpsBusy2 Formal.Net.OpsBusy3

set_option maxRecDepth 100000

/-- **Protocol and bundling from the physical hypotheses** (no sampled data field used). -/
theorem gcd_hw_joint5 (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS_P : ∀ o : Fin NO, CellP ch (srcV a b) (opAt o))
    (H_TCHECK_ROOT : ∀ c, isRoot3 c = true → BCert (ch c)) :
    (∀ c, Protocol (ch c)) ∧ (∀ c, Held (ch c)) := by
  obtain ⟨w, hw⟩ := Classical.axiomOfChoice H_CELLS_P
  refine net_joint net ch (fun o => hs_protoT (disj_ok o) (hw o).1) ?_
  intro t hinit hp hprev
  have key : ∀ m, ∀ c : Fin NC, hrk3 c = m → HeldStep (ch c) t := by
    intro m
    induction m using Nat.strongRecOn with
    | _ m ih =>
      intro c hm
      cases hr : isRoot3 c
      · rcases (hw (prodOf c)).2 c (prod_mem c) with hF | row
        · obtain ⟨hs, hlt⟩ := struct3_chk c hr
          exact hs_heldT_one (disj_ok _) (hw (prodOf c)).1 hs (prod_mem c) hF t hinit hp
            (fun i hi s hs => by
              rcases Nat.lt_or_eq_of_le hs with h | h
              · exact hprev i s h
              · rw [h]; exact ih (hrk3 i) (by rw [← hm]; exact hlt i hi) i rfl)
        · exact row.heldStep (hinit c) (fun s hs => (hp c s hs).2)
      · exact heldStep_of_bcert (H_TCHECK_ROOT c hr) (hinit c) (fun s hs => (hp c s hs).2)
  exact fun c => key _ c rfl

/-- **H_CELLS_B derived**: every relaxed cell, data fields of the sampled channels included. -/
theorem gcd_hw_cells_of_phys (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS_P : ∀ o : Fin NO, CellP ch (srcV a b) (opAt o))
    (H_TCHECK_ROOT : ∀ c, isRoot3 c = true → BCert (ch c)) :
    ∀ o : Fin NO, CellB ch (srcV a b) (opAt o) := by
  obtain ⟨hP, hH⟩ := gcd_hw_joint5 a b ch H_CELLS_P H_TCHECK_ROOT
  exact fun o => cellB_of_cellP (disj_ok o) (H_CELLS_P o) hP hH

/-- **Physical gcd_hw safety, data fields derived.** The observed run `ch` meets, per operator,
the handshake half of its gate model and, per output channel, either the relaxed data field
(ghost: no gate samples the bus) or a tcheck row with H_FN and H_LAUNCH (sampled); `start` is
offered at most once; each of the 26 root channels has a tcheck certificate (or `exempt`).
Then every value out0 latches is `Nat.gcd a b`. -/
theorem gcd_hw_circuit_safe_phys5 (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (ch : Fin NC → Chan)
    (H_CELLS_P : ∀ o : Fin NO, CellP ch (srcV a b) (opAt o))
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch start).req) t ≤ 1)
    (H_TCHECK_ROOT : ∀ c, isRoot3 c = true → BCert (ch c)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t =
      List.replicate (Handshake.cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) :=
  gcd_hw_circuit_safe_phys4 a b ha hb ch (gcd_hw_cells_of_phys a b ch H_CELLS_P H_TCHECK_ROOT)
    H_START_ONCE H_TCHECK_ROOT

/-! ## The classification of `classes.tsv`: rows exactly on the sampled channels -/

/-- The 221 SAMPLED channels (`Wip/C8x2/classes.tsv`: consumer = a latch D with data pins, a
steer / mux / 3-input-mux select LUT, or the environment reading out0). Every other channel is a
ghost: its consumer is combinational (join, fork, mux data, arbiter), a sink, or a W = 0 control
stage. Produced by `Wip/C8x4/sampled.py`. -/
def sampIds : List Nat := [6, 12, 13, 21, 22, 30, 31, 39, 40, 43, 44, 51, 52, 59, 60, 62, 63, 65, 66, 68, 69, 71, 72, 74, 75, 79, 80, 81, 82, 84, 86, 87, 88, 89, 91, 93, 94, 95, 96, 97, 99, 109, 113, 116, 123, 124, 126, 127, 129, 130, 133, 134, 135, 136, 137, 139, 140, 141, 142, 143, 145, 146, 147, 148, 149, 153, 154, 155, 156, 159, 162, 164, 166, 167, 168, 169, 170, 171, 174, 175, 176, 177, 178, 179, 195, 196, 199, 200, 202, 203, 209, 210, 211, 212, 215, 218, 220, 222, 223, 224, 225, 226, 227, 230, 231, 232, 233, 234, 235, 258, 259, 268, 269, 271, 272, 274, 275, 277, 278, 283, 284, 288, 293, 295, 303, 304, 306, 309, 310, 312, 317, 319, 320, 322, 324, 326, 327, 329, 331, 333, 334, 335, 336, 337, 344, 346, 347, 348, 349, 352, 355, 357, 359, 360, 361, 362, 363, 366, 367, 368, 369, 370, 373, 374, 375, 376, 377, 396, 397, 398, 399, 400, 402, 403, 404, 405, 406, 410, 411, 413, 414, 415, 416, 418, 419, 420, 421, 422, 423, 424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442, 443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455]

def isSampled (c : Fin NC) : Bool := sampIds.contains c.val

/-- Per operator: handshake half, a row on every sampled output, the field on every ghost one. -/
def CellPcls (ch : Fin NC → Chan) (sv : Nat → Nat) (o : Fin NO) : Prop :=
  ∃ w, HS ch sv (opAt o) w ∧ ∀ c ∈ (opAt o).outsC,
    (isSampled c = true → Row ch sv (opAt o) w c) ∧
    (isSampled c = false → FieldOf ch sv (opAt o) w c)

theorem cellP_of_cls {ch : Fin NC → Chan} {sv : Nat → Nat} {o : Fin NO} (h : CellPcls ch sv o) :
    CellP ch sv (opAt o) := by
  obtain ⟨w, hs, hd⟩ := h
  refine ⟨w, hs, fun c hc => ?_⟩
  cases e : isSampled c
  · exact Or.inl ((hd c hc).2 e)
  · exact Or.inr ((hd c hc).1 e)

/-- **phys5 with the classification of `classes.tsv`**: rows (tcheck + H_FN + H_LAUNCH) on the
221 sampled channels, the (by-construction) field on the 244 ghosts. -/
theorem gcd_hw_circuit_safe_phys5_cls (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (ch : Fin NC → Chan)
    (H_CELLS_P : ∀ o : Fin NO, CellPcls ch (srcV a b) o)
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch start).req) t ≤ 1)
    (H_TCHECK_ROOT : ∀ c, isRoot3 c = true → BCert (ch c)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t =
      List.replicate (Handshake.cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) :=
  gcd_hw_circuit_safe_phys5 a b ha hb ch (fun o => cellP_of_cls (H_CELLS_P o)) H_START_ONCE
    H_TCHECK_ROOT

theorem samp_count : sampIds.length = 221 := by decide

/-- phys5 is at least as strong as phys4: phys4's hypotheses give phys5's (all outputs ghosts). -/
theorem phys5_hyps_of_phys4 (a b : Nat) (ch : Fin NC → Chan)
    (H_CELLS_B : ∀ o : Fin NO, CellB ch (srcV a b) (opAt o)) :
    ∀ o : Fin NO, CellP ch (srcV a b) (opAt o) := fun o => cellP_of_cellB (disj_ok o) (H_CELLS_B o)

end Formal.Net.CapNet.Gcd

namespace Formal.Net.CapNet.Wit
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapstoneRefine Formal.Net.OpsBusy Formal.Net.OpsBusy3

/-- Joint consistency of the three hypotheses of `gcd_hw_circuit_safe_phys5` (C-8t's run, every
output a ghost, root certificates `exempt`). -/
theorem gcd_hw_phys5_witness :
    (∀ o : Fin NO, CellP chW (srcV 12 18) (opAt o)) ∧
    (∀ t, Handshake.cnt (riseB (chW start).req) t ≤ 1) ∧
    (∀ c, isRoot3 c = true → BCert (chW c)) :=
  ⟨phys5_hyps_of_phys4 12 18 chW gcd_hw_phys4_witness.1, gcd_hw_phys4_witness.2.1,
    gcd_hw_phys4_witness.2.2⟩

/-- C-8x2's `chS` (old gate models fail on it) also meets every hypothesis of phys5. -/
theorem strict_phys5_hyps :
    (∀ o : Fin NO, CellP chS (srcV 12 18) (opAt o)) ∧
    (∀ t, Handshake.cnt (riseB (chS start).req) t ≤ 1) ∧
    (∀ c, isRoot3 c = true → BCert (chS c)) :=
  ⟨phys5_hyps_of_phys4 12 18 chS strict_phys4_hyps.1, strict_phys4_hyps.2.1,
    strict_phys4_hyps.2.2⟩

end Formal.Net.CapNet.Wit
