import Formal.Core.XAudit.Events4

/-!
# Formal.Core.XAudit.Events5Line — delay lines (FASTFALL / FASTRISE) in the warp model

Probe A-events5. See `formal/notes/A-events5.md` §3.

bdc's request delays are trees of AND (FASTFALL, `bd_delay #(.FASTFALL(1))`,
`bd_delay_gated`) or OR (FASTRISE) LUTs whose inputs are all copies of ONE
source `c` (the chain wire and the side taps). Under transport delay (monotone
warps) and H_ATOMIC_LUT (a LUT samples all its pins at one instant), the tree's
output at time `t` is the AND (OR) of `c` read at one sample time `τ i` per tap
`i`. `Events4.and_val` gives its count, provided the tap counts are CONTIGUOUS.

This file proves the per-gate contiguity certificate that `events5/ana5.py`
(`contig5`) checks, in the warp model:

* `tree_contig`: if at every gate of the tree SOME tap of the left subtree and
  SOME tap of the right subtree are sampled within `W` of each other, and the
  source fires at most once per `W` window (`OneEvent`, from a closed walk with
  one token, `Events3.Beh3.cycle_le`), the tap counts are contiguous;
  `line_and` / `line_or` then give the line's value as a count.
* `hop_skew`: two taps that MEET at a gate are sampled within
  `max (hiQ - loP) (hiP - loQ)` of each other, where `[loP, hiP]`, `[loQ, hiQ]`
  are the bands of the two tap paths from the source to the gate's input pins
  only. The chain suffix after the gate is the same warp for both taps and does
  not enter (the gate LUT itself is one warp: H_ATOMIC_LUT). This is the term
  that `events4/model.py` counted in full (each tap's band ran to the stage pin):
  that, not the circuit, produced the −11.4 ns contiguity "failures".
* `prefix_skew`: a SHARED prefix (source → buffer → fanout point) does NOT
  cancel in the warp model: a time-varying delay can differ by its band width
  at the two sample times. `contig5` adds the width of the shared prefix.
* `line_gap_neg` (negative control, `decide`): a source low phase shorter than
  the window between two taps yields tap counts 1 and 3 (old high on the slow
  chain path, new high on the fast tap): the AND reads 1 while the count model
  says 0 — the request skips its matched delay. This is the mechanism of rule F's
  missing in-flight term (B-bundling `ff_counter_ruleF`) and of the concrete
  trace `events5/linetrace.py` on gcd_hw seed d (ushli0, `trace_ushli0_*.txt`).
-/

namespace Formal.Core.XAudit.Events5

open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events (ph)
open Formal.Core.XAudit.Events3 (ph_false_eq)
open Formal.Core.XAudit.Events4 (Contig andCnt orCnt and_val or_val' contig_union andCnt_mem orCnt_mem)

/-! ## 1. One event per window -/

/-- A monotone count fires at most once in any window of `W` steps. -/
def OneEvent (M : Nat → Nat) (W : Nat) : Prop := ∀ t, M (t + W) ≤ M t + 1

def MonoC (M : Nat → Nat) : Prop := ∀ a b, a ≤ b → M a ≤ M b

/-- Two samples within `W` see counts at most one apart. -/
theorem close_of_window (M : Nat → Nat) (W : Nat) (hm : MonoC M) (hW : OneEvent M W)
    (a b : Nat) (h1 : a ≤ b + W) (h2 : b ≤ a + W) : M a ≤ M b + 1 ∧ M b ≤ M a + 1 := by
  rcases Nat.le_total a b with h | h
  · have := hm a b h; have := hm b (a + W) h2; have := hW a; omega
  · have := hm b a h; have := hm a (b + W) h1; have := hW b; omega

/-! ## 2. Trees of taps -/

/-- The gate tree of a delay line: leaves are taps (indices into the sample
times `τ`), inner nodes are 2-input gates (a wider LUT is a nest of these, the
certificate per inner node being one edge of a spanning tree). -/
inductive LTree where
  | tap (i : Nat)
  | gate (l r : LTree)

namespace LTree

def taps : LTree → List Nat
  | tap i => [i]
  | gate l r => l.taps ++ r.taps

def evalAnd (x : Nat → Bool) : LTree → Bool
  | tap i => x i
  | gate l r => l.evalAnd x && r.evalAnd x

def evalOr (x : Nat → Bool) : LTree → Bool
  | tap i => x i
  | gate l r => l.evalOr x || r.evalOr x

theorem evalAnd_eq (x : Nat → Bool) : ∀ T : LTree, T.evalAnd x = T.taps.all x
  | tap i => by simp [evalAnd, taps]
  | gate l r => by simp [evalAnd, taps, List.all_append, evalAnd_eq x l, evalAnd_eq x r]

theorem evalOr_eq (x : Nat → Bool) : ∀ T : LTree, T.evalOr x = T.taps.any x
  | tap i => by simp [evalOr, taps]
  | gate l r => by simp [evalOr, taps, List.any_append, evalOr_eq x l, evalOr_eq x r]

/-- **The per-gate contiguity certificate** (what `contig5` checks, with
`W` = the source's per-window bound): at every gate, one tap on each side
sampled within `W` of each other. -/
def Cert (τ : Nat → Nat) (W : Nat) : LTree → Prop
  | tap _ => True
  | gate l r => l.Cert τ W ∧ r.Cert τ W ∧
      ∃ a ∈ l.taps, ∃ b ∈ r.taps, τ a ≤ τ b + W ∧ τ b ≤ τ a + W

end LTree

theorem contig_single (m : Nat) : Contig [m] m m := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro x hx; simp at hx; omega
  · simp
  · simp
  · intro k h1 h2; simp; omega

/-- **Contiguity of a delay line's tap counts from the per-gate certificate.** -/
theorem tree_contig (M : Nat → Nat) (W : Nat) (hm : MonoC M) (hW : OneEvent M W) (τ : Nat → Nat) :
    ∀ T : LTree, T.Cert τ W → ∃ lo hi, Contig (T.taps.map (fun i => M (τ i))) lo hi
  | .tap i, _ => ⟨M (τ i), M (τ i), by simpa [LTree.taps] using contig_single (M (τ i))⟩
  | .gate l r, ⟨hl, hr, a, ha, b, hb, h1, h2⟩ => by
      obtain ⟨la, ha', cA⟩ := tree_contig M W hm hW τ l hl
      obtain ⟨lb, hb', cB⟩ := tree_contig M W hm hW τ r hr
      have hc := close_of_window M W hm hW (τ a) (τ b) h1 h2
      refine ⟨min la lb, max ha' hb', ?_⟩
      simp only [LTree.taps, List.map_append]
      exact contig_union _ _ la ha' lb hb' cA cB (M (τ a)) (M (τ b))
        (List.mem_map.mpr ⟨a, ha, rfl⟩) (List.mem_map.mpr ⟨b, hb, rfl⟩) ⟨hc.1, hc.2⟩

/-- **FASTFALL line value**: under the certificate the AND tree of the copies
reads `ph false (andCnt lo hi)`, `lo`/`hi` the extreme tap counts. -/
theorem line_and (M : Nat → Nat) (W : Nat) (hm : MonoC M) (hW : OneEvent M W) (τ : Nat → Nat)
    (T : LTree) (hc : T.Cert τ W) :
    ∃ lo hi, Contig (T.taps.map (fun i => M (τ i))) lo hi ∧
      T.evalAnd (fun i => ph false (M (τ i))) = ph false (andCnt lo hi) ∧
      lo ≤ andCnt lo hi ∧ andCnt lo hi ≤ hi := by
  obtain ⟨lo, hi, h⟩ := tree_contig M W hm hW τ T hc
  refine ⟨lo, hi, h, ?_, andCnt_mem lo hi (h.1 lo h.2.1).2⟩
  rw [LTree.evalAnd_eq, ← and_val _ lo hi h, List.all_map]; rfl

/-- **FASTRISE line value** (OR tree). -/
theorem line_or (M : Nat → Nat) (W : Nat) (hm : MonoC M) (hW : OneEvent M W) (τ : Nat → Nat)
    (T : LTree) (hc : T.Cert τ W) :
    ∃ lo hi, Contig (T.taps.map (fun i => M (τ i))) lo hi ∧
      T.evalOr (fun i => ph false (M (τ i))) = ph false (orCnt lo hi) ∧
      lo ≤ orCnt lo hi ∧ orCnt lo hi ≤ hi := by
  obtain ⟨lo, hi, h⟩ := tree_contig M W hm hW τ T hc
  refine ⟨lo, hi, h, ?_, orCnt_mem lo hi (h.1 lo h.2.1).2⟩
  rw [LTree.evalOr_eq, ← or_val' _ lo hi h, List.any_map]; rfl

/-! ## 3. Where the window comes from: warps of the two tap paths -/

/-- Composition of warps (a tap path is a chain of routed arcs and LUTs). -/
theorem warp_comp {lo1 hi1 lo2 hi2 : Nat} {f g : Nat → Nat} (wf : Warp lo1 hi1 f) (wg : Warp lo2 hi2 g) :
    Warp (lo1 + lo2) (hi1 + hi2) (fun t => f (g t)) := by
  refine ⟨fun a b h => wf.mono _ _ (wg.mono _ _ h), fun t => ?_, fun t => ?_⟩
  · have := wf.le_late (g t); have := wg.le_late t; omega
  · have := wf.early_le (g t); have := wg.early_le t; omega

/-- **The hop window** (the corrected per-gate check): two tap paths `P`, `Q`
that meet at one gate are read by that gate at ONE time `u` (H_ATOMIC_LUT); the
chain after the gate is shared and does not enter. Their sample times of the
source differ by at most `W` when `hiQ ≤ loP + W` and `hiP ≤ loQ + W`. -/
theorem hop_skew {loP hiP loQ hiQ W : Nat} {fP fQ : Nat → Nat}
    (wP : Warp loP hiP fP) (wQ : Warp loQ hiQ fQ) (h1 : hiQ ≤ loP + W) (h2 : hiP ≤ loQ + W) (u : Nat) :
    fP u ≤ fQ u + W ∧ fQ u ≤ fP u + W := by
  have := wP.le_late u; have := wP.early_le u; have := wQ.le_late u; have := wQ.early_le u
  omega

/-- **A shared prefix does not cancel** in the warp model: after a common
`[lo, hi]` element the two sample times may move apart by its band width. -/
theorem prefix_skew {lo hi : Nat} {g : Nat → Nat} (wg : Warp lo hi g) (hlh : lo ≤ hi) (a b w : Nat)
    (h : a ≤ b + w) : g a ≤ g b + (w + (hi - lo)) := by
  have := wg.le_late a; have := wg.early_le b; omega

/-- ... and the bound is attained: a `[1, 3]` warp, slow (3) at `b = 7` and fast
(1) at `a = 8 = b + 1`, puts the two samples `1 + (3 - 1)` apart. -/
theorem prefix_skew_tight : ∃ g : Nat → Nat, Warp 1 3 g ∧ g 8 = g 7 + (1 + (3 - 1)) := by
  refine ⟨fun t => if t ≤ 7 then t - 3 else t - 1, ⟨?_, ?_, ?_⟩, ?_⟩
  · intro a b h; by_cases ha : a ≤ 7 <;> by_cases hb : b ≤ 7 <;> simp [ha, hb] <;> omega
  · intro t; by_cases ht : t ≤ 7 <;> simp [ht] <;> omega
  · intro t; by_cases ht : t ≤ 7 <;> simp [ht] <;> omega
  · decide

/-- The certificate of one gate from the hop window: the two subtrees'
chosen taps `a`, `b` are sampled through warps `fa`, `fb` of the gate's sample
time `u`. -/
theorem gate_cert_of_hop {loP hiP loQ hiQ W : Nat} {fP fQ : Nat → Nat} (τ : Nat → Nat)
    (wP : Warp loP hiP fP) (wQ : Warp loQ hiQ fQ) (h1 : hiQ ≤ loP + W) (h2 : hiP ≤ loQ + W)
    (u a b : Nat) (ha : τ a = fP u) (hb : τ b = fQ u) :
    τ a ≤ τ b + W ∧ τ b ≤ τ a + W := by
  rw [ha, hb]; exact hop_skew wP wQ h1 h2 u

/-! ## 4. Negative control: a low phase shorter than the hop window -/

/-- The source of the concrete trace, scaled: rises at 10, falls at 40, rises
again at 42 (low phase 2). -/
def srcCount (t : Nat) : Nat :=
  (if 10 ≤ t then 1 else 0) + (if 40 ≤ t then 1 else 0) + (if 42 ≤ t then 1 else 0)

/-- NEGATIVE CONTROL (delay line): the slow chain path reads the source 5
steps ago, the fast tap 1 step ago (window 4 > low phase 2). At `u = 44` the
chain still shows the OLD high (count 1) and the tap the NEW high (count 3):
the AND gate is 1, but the line's count is `andCnt 1 3 = 2` (low) — the
request rises one tap hop after the source instead of after the matched delay.
The certificate cannot hold here: `OneEvent srcCount 4` is false. -/
theorem line_gap_neg :
    srcCount (44 - 5) = 1 ∧ srcCount (44 - 1) = 3 ∧
    (ph false (srcCount (44 - 5)) && ph false (srcCount (44 - 1))) = true ∧
    ph false (andCnt 1 3) = false ∧ ¬ (srcCount (38 + 4) ≤ srcCount 38 + 1) := by
  decide

end Formal.Core.XAudit.Events5
