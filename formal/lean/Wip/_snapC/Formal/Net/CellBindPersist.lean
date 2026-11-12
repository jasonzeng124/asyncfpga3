import Formal.Net.CellBindKOps
import Formal.Net.KernelCapSafe

/-!
# Probe C-O4b (persistence 1/3): freezing a run, causal lumping, causal operator protocols

O4 kept H_LEAF_PERSIST and H_REQ_PERSIST as hypotheses because the capstone derives the
four-phase protocol FROM the lumped cell fields, while those fields need the persistence that
the protocol gives: a circle. This file breaks it by induction on time, with one tool:

* **freezing** a run at `T` (`fz`, `fzC`, `fzK`: every trace holds its tick-`T` value from `T`
  on). A frozen run satisfies every one-step ("moves only to ...") field at steps `≥ T`
  vacuously, and agrees with the run up to `T`. So "the field holds at steps `< T`" is enough
  to build an Ops structure for the run frozen at `T`, and then every existing invariant
  (`fork_inv`, `join_inv`, `mux_inv`, `muxn_inv`, `link_inv`) and every existing
  `OpProto` (via `cell_proto`) applies to it, and its conclusions at `≤ T` transfer back.
* `cel_inv_upto`, `cel_lumped_upto`, `or_inv_upto`, `or_lumped_upto`, `bufchain_lumped_upto`:
  O4's lumping lemmas with every hypothesis needed only at EARLIER steps (by freezing).
* `opproto_of`: an operator whose frozen-at-`T+1` run satisfies its `Cell` whenever its
  channels obeyed the protocol before `T` is a causal `OpProto` operator. This is the shape
  in which the joint induction enters `net_protocol` unchanged.
-/

namespace Formal.Net.CellBind.Persist
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CellBind Formal.Net.CellBind.Ops
open Formal.Net.CapNet

/-! ## 1. Freezing -/

def fz (T : Nat) (x : Trace) : Trace := fun t => x (min t T)
def fzD (T : Nat) (d : Nat → Nat) : Nat → Nat := fun t => d (min t T)
def fzC (T : Nat) (c : Chan) : Chan := ⟨fz T c.req, fz T c.ack, fzD T c.dat⟩
def fzK {n : Nat} (T : Nat) (ch : Fin n → Chan) : Fin n → Chan := fun c => fzC T (ch c)

theorem fz_le {T t : Nat} (x : Trace) (h : t ≤ T) : fz T x t = x t := by
  simp [fz, Nat.min_eq_left h]

theorem fzD_le {T t : Nat} (d : Nat → Nat) (h : t ≤ T) : fzD T d t = d t := by
  simp [fzD, Nat.min_eq_left h]

theorem fz_ge {T t : Nat} (x : Trace) (h : T ≤ t) : fz T x t = x T := by
  simp [fz, Nat.min_eq_right h]

/-- A frozen trace moves only before `T`. -/
theorem fz_move {T t : Nat} {x : Trace} (h : fz T x (t + 1) ≠ fz T x t) : t < T := by
  apply Classical.byContradiction; intro hc
  exact h (by rw [fz_ge x (by omega), fz_ge x (by omega)])

theorem fz0 (T : Nat) (x : Trace) : fz T x 0 = x 0 := fz_le x (Nat.zero_le T)

theorem fz_lt {T t : Nat} (x : Trace) (h : t < T) : fz T x t = x t ∧ fz T x (t + 1) = x (t + 1) :=
  ⟨fz_le x (by omega), fz_le x (by omega)⟩

theorem fzD_succ (T t : Nat) (d : Nat → Nat) (h : ¬ t < T) : fzD T d (t + 1) = fzD T d t := by
  simp [fzD, Nat.min_eq_right (show T ≤ t + 1 by omega), Nat.min_eq_right (show T ≤ t by omega)]

/-- The generic step transfer: a one-step property of `x` at the steps before `T` gives the
same property of the frozen trace at every step. -/
theorem fz_step {T : Nat} {x : Trace} {P : Nat → Bool → Prop}
    (h : ∀ t, t < T → x (t + 1) ≠ x t → P t (x (t + 1))) :
    ∀ t, fz T x (t + 1) ≠ fz T x t → t < T ∧ P t (fz T x (t + 1)) := by
  intro t hm
  have ht := fz_move hm
  rw [(fz_lt x ht).1, (fz_lt x ht).2] at hm
  exact ⟨ht, by rw [(fz_lt x ht).2]; exact h t ht hm⟩

theorem init_fz {T : Nat} {c : Chan} (h : Init c) : Init (fzC T c) := by
  simp only [Init, fzC, fz0]; exact h

theorem held_fz {T : Nat} {c : Chan} (h : Held c) : Held (fzC T c) := by
  intro t h1 h2
  by_cases ht : t < T
  · simp only [inTx, fzC, (fz_lt _ ht).1, (fz_lt _ ht).2] at h1 h2
    simp only [fzC, fzD_le _ (show t ≤ T by omega), fzD_le _ (show t + 1 ≤ T by omega)]
    exact h t h1 h2
  · exact fzD_succ T t c.dat ht

theorem rules_fz {T s : Nat} {c : Chan} (hs : s < T) (h : Rules c s) : Rules (fzC T c) s := by
  simp only [Rules, SendStep, RecvStep, fzC, (fz_lt _ hs).1, (fz_lt _ hs).2]; exact h

theorem recv_unfz {T s : Nat} {c : Chan} (hs : s < T) (h : RecvStep (fzC T c) s) : RecvStep c s := by
  simp only [RecvStep, fzC, (fz_lt _ hs).1, (fz_lt _ hs).2] at h; exact h

theorem send_unfz {T s : Nat} {c : Chan} (hs : s < T) (h : SendStep (fzC T c) s) : SendStep c s := by
  simp only [SendStep, fzC, (fz_lt _ hs).1, (fz_lt _ hs).2] at h; exact h

/-! ## 2. Causal lumping -/

theorem fz_hyp {T : Nat} {x y : Trace} {Q : Nat → Prop}
    (h : ∀ t, t < T → x (t + 1) ≠ x t → Q t) : ∀ t, fz T x (t + 1) ≠ fz T x t → Q t := by
  intro t hm
  have ht := fz_move hm
  rw [(fz_lt x ht).1, (fz_lt x ht).2] at hm
  exact h t ht hm

/-- `cel_inv` with every hypothesis needed only before `T`, conclusion at `T`. -/
theorem cel_inv_upto {m r : Trace} {leaves : List Trace} (T : Nat)
    (hC : ∀ t, t < T → m (t + 1) ≠ m t → ∀ l ∈ leaves, l t = m (t + 1))
    (hR : ∀ t, t < T → r (t + 1) ≠ r t → r (t + 1) = m t)
    (hL : ∀ l ∈ leaves, ∀ t, t < T → l (t + 1) ≠ l t → l t = r t)
    (h0 : m 0 = r 0) : m T ≠ r T → ∀ l ∈ leaves, l T = m T := by
  intro hne l hl
  have key := cel_inv (m := fz T m) (r := fz T r) (leaves := leaves.map (fz T))
    (fz_hyp (fun t ht hm l' hl' => by
      obtain ⟨l0, hl0, rfl⟩ := List.mem_map.mp hl'
      rw [(fz_lt l0 ht).1, (fz_lt m ht).2]; exact hC t ht hm l0 hl0))
    (fz_hyp (fun t ht hm => by rw [(fz_lt r ht).2, (fz_lt m ht).1]; exact hR t ht hm))
    (fun l' hl' => by
      obtain ⟨l0, hl0, rfl⟩ := List.mem_map.mp hl'
      exact fz_hyp (fun t ht hm => by rw [(fz_lt l0 ht).1, (fz_lt r ht).1]; exact hL l0 hl0 t ht hm))
    (by rw [fz0, fz0]; exact h0) T
    (by rw [fz_le m (Nat.le_refl T), fz_le r (Nat.le_refl T)]; exact hne) (fz T l)
    (List.mem_map_of_mem hl)
  rwa [fz_le l (Nat.le_refl T), fz_le m (Nat.le_refl T)] at key

/-- `cel_lumped` at step `T` from the hypotheses before `T` (and `hR` at `T`). -/
theorem cel_lumped_upto {m r : Trace} {leaves : List Trace} (T : Nat)
    (hC : ∀ t, t < T → m (t + 1) ≠ m t → ∀ l ∈ leaves, l t = m (t + 1))
    (hR : ∀ t, t ≤ T → r (t + 1) ≠ r t → r (t + 1) = m t)
    (hL : ∀ l ∈ leaves, ∀ t, t < T → l (t + 1) ≠ l t → l t = r t)
    (h0 : m 0 = r 0) : r (T + 1) ≠ r T → ∀ l ∈ leaves, l T = r (T + 1) := by
  intro hr l hl
  have e := hR T (Nat.le_refl T) hr
  have hmr : m T ≠ r T := fun h => hr (by rw [e, h])
  rw [cel_inv_upto T hC (fun t ht => hR t (by omega)) hL h0 hmr l hl, e]

theorem any_fz {T t : Nat} (leaves : List Trace) (h : t ≤ T) :
    (leaves.map (fz T)).any (fun l => l t) = leaves.any (fun l => l t) := by
  simp only [List.any_map, Function.comp_def, fz_le _ h]

/-- `or_inv` with every hypothesis needed only before `T`, conclusion at `T`. -/
theorem or_inv_upto {e r : Trace} {leaves : List Trace} (T : Nat)
    (hE : ∀ t, t < T → e (t + 1) ≠ e t → e (t + 1) = leaves.any (fun l => l t))
    (hR : ∀ t, t < T → r (t + 1) ≠ r t → r (t + 1) = e t)
    (hL : ∀ l ∈ leaves, ∀ t, t < T → l (t + 1) ≠ l t → l t = r t)
    (h0 : e 0 = r 0) : e T ≠ r T → leaves.any (fun l => l T) = e T := by
  intro hne
  have key := or_inv (e := fz T e) (r := fz T r) (leaves := leaves.map (fz T))
    (fz_hyp (fun t ht hm => by
      rw [(fz_lt e ht).2, any_fz leaves (by omega)]; exact hE t ht hm))
    (fz_hyp (fun t ht hm => by rw [(fz_lt r ht).2, (fz_lt e ht).1]; exact hR t ht hm))
    (fun l' hl' => by
      obtain ⟨l0, hl0, rfl⟩ := List.mem_map.mp hl'
      exact fz_hyp (fun t ht hm => by rw [(fz_lt l0 ht).1, (fz_lt r ht).1]; exact hL l0 hl0 t ht hm))
    (by rw [fz0, fz0]; exact h0) T
    (by rw [fz_le e (Nat.le_refl T), fz_le r (Nat.le_refl T)]; exact hne)
  rwa [any_fz leaves (Nat.le_refl T), fz_le e (Nat.le_refl T)] at key

theorem or_lumped_upto {e r : Trace} {leaves : List Trace} (T : Nat)
    (hE : ∀ t, t < T → e (t + 1) ≠ e t → e (t + 1) = leaves.any (fun l => l t))
    (hR : ∀ t, t ≤ T → r (t + 1) ≠ r t → r (t + 1) = e t)
    (hL : ∀ l ∈ leaves, ∀ t, t < T → l (t + 1) ≠ l t → l t = r t)
    (h0 : e 0 = r 0) : r (T + 1) ≠ r T → r (T + 1) = leaves.any (fun l => l T) := by
  intro hr
  have e1 := hR T (Nat.le_refl T) hr
  have her : e T ≠ r T := fun h => hr (by rw [e1, h])
  rw [e1, or_inv_upto T hE (fun t ht => hR t (by omega)) hL h0 her]

/-- A plain buffer chain without H_REQ_PERSIST (O4's `GenBufChain` minus `PersistEnd`). -/
def GenBufChainP (i o : Trace) : Prop :=
  ∃ (n : Nat) (x : Nat → Trace), 1 ≤ n ∧ x 0 = i ∧ x n = o ∧
    NetSI n (fun k f => Formal.Gen.genF Formal.Gen.Cells.bd_delay_N3 "chain.g[0].u" .O ["a"] [f (k - 1)]) x ∧
    (∀ j, j ≤ n → x j 0 = x 0 0)

theorem bufchainP_of {i o : Trace} (h : GenBufChain i o) : GenBufChainP i o := by
  obtain ⟨n, x, h1, h0, hn, hsi, _, hI⟩ := h
  exact ⟨n, x, h1, h0, hn, hsi, hI⟩

/-- The buffer chain is lumped at step `T` if its input persisted (end-only) at the steps
`≤ T`. -/
theorem bufchain_lumped_upto {i o : Trace} (h : GenBufChainP i o) (T : Nat)
    (hP : ∀ t, t ≤ T → i (t + 1) ≠ i t → o t = i t) :
    o (T + 1) ≠ o T → o (T + 1) = i T := by
  obtain ⟨n, x, h1, h0, hn, hsi, hI⟩ := h
  have hB : GenBufChain (fz (T + 1) i) (fz (T + 1) o) := by
    refine ⟨n, fun k => fz (T + 1) (x k), h1, by rw [h0], by rw [hn], ?_, ?_, ?_⟩
    · intro k hk1 hkn t hm
      have ht := fz_move hm
      rw [(fz_lt _ ht).1, (fz_lt _ ht).2] at hm
      rw [(fz_lt _ ht).2, hsi k hk1 hkn t hm]
      simp only [fz_le _ (show t ≤ T + 1 by omega)]
    · intro t hm
      have ht := fz_move hm
      rw [(fz_lt _ ht).1, (fz_lt _ ht).2] at hm
      rw [(fz_lt _ ht).1, (fz_lt _ ht).1, hn, ← h0]
      rw [h0] at hm; rw [h0]; exact hP t (by omega) hm
    · intro j hj; simp only [fz0]; exact hI j hj
  intro hm
  have := bufchain_lumped hB T (by rw [fz_le o (by omega), fz_le o (by omega)]; exact hm)
  rwa [fz_le o (by omega), fz_le i (by omega)] at this

/-! ## 3. Causal operators -/

variable {n : Nat}

/-- The premise of `OpProto.ag` before `T`. -/
def RulesBefore (ch : Fin n → Chan) (k : K n) (T : Nat) : Prop :=
  ∀ s, s < T → (∀ c ∈ k.insC, Rules (ch c) s) ∧ (∀ c ∈ k.outsC, Rules (ch c) s)

/-- **Causal operators.** If the run frozen at `T + 1` satisfies the operator's `Cell`
whenever its channels obeyed the protocol before `T`, the operator is an `OpProto`
operator of the run itself. -/
theorem opproto_of (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (hd : Dist k)
    (h : ∀ T, RulesBefore ch k T → Cell (fzK (T + 1) ch) sv k) : OpProto ch k.insC k.outsC := by
  have P0 := Formal.Net.KCap.cell_proto (fzK 1 ch) sv k (h 0 (fun s hs => absurd hs (Nat.not_lt_zero _))) hd
  refine ⟨fun t hi ho hh hp => ?_, fun c hc => ?_, fun c hc => ?_⟩
  · have P := Formal.Net.KCap.cell_proto (fzK (t + 1) ch) sv k (h t hp) hd
    obtain ⟨R, S⟩ := P.ag t (fun c hc => init_fz (hi c hc)) (fun c hc => init_fz (ho c hc))
      (fun c hc => held_fz (hh c hc))
      (fun s hs => ⟨fun c hc => rules_fz (by omega) ((hp s hs).1 c hc),
                    fun c hc => rules_fz (by omega) ((hp s hs).2 c hc)⟩)
    exact ⟨fun c hc => recv_unfz (Nat.lt_succ_self t) (R c hc),
           fun c hc => send_unfz (Nat.lt_succ_self t) (S c hc)⟩
  · have := P0.initIn c hc; simp only [fzK, fzC, fz0] at this; exact this
  · have := P0.initOut c hc; simp only [fzK, fzC, fz0] at this; exact this

end Formal.Net.CellBind.Persist
