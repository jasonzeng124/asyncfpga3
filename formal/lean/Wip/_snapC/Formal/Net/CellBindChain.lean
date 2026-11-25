import Formal.Net.CellBind
import Formal.Net.OpsGen

/-!
# Probe C-O4 (2/4): the generated delay-chain stages, and the fast-chain hazard

The request and acknowledge delay lines of the library are chains of LUTs:
* `bd_delay` (plain): LUT1 buffers (INIT 2), e.g. bd_link's `rdly`, bd_mux's `udly`;
* `bd_delay` FASTFALL / `bd_delay_gated`: a LUT1 head, then LUT2 `s ∧ tap` (INIT 8);
  this is the compute units' request delay (`bdc/compute.py` `request_delay`, default
  `BDC_FASTFALL=1`, behind the `uor` LUT1 anchor);
* `bd_delay` FASTRISE: a LUT1 head, then LUT2 `s ∨ tap` (INIT E); this is bd_link's `uack`
  acknowledge line (`DACK` stages).

`*_gate`: each stage function, read off the generated netlist (`genF`, kernel `decide`),
is a buffer / AND / OR, hence monotone and constant-preserving (`stage_mono`), so
`CellBind.mono_net` applies under H_CHAIN_SETTLED.

**`fastfall_hazard`** (counterexample, the generated `bd_delay_N3_FF`): with only END-ONLY
persistence (the input moves only when the chain's end shows it, which is what the four-
phase protocol around the chain guarantees), the chain's end can move to a value its input
did NOT have one tick earlier. The run: the input pulses low and high again while the head
buffer still lags; the end falls fast (side taps), re-rises from the stale middle node, and
falls again while the input is high: a runt on the request. So for FASTFALL / FASTRISE
chains H_CHAIN_SETTLED (every stage has followed the input before the input moves again)
is a genuine timing hypothesis, not implied by the protocol. A brute-force search over the
per-gate SI semantics (`Wip/CO4/chain_bfs.py`) finds the same hazard for every side-tapped
chain of length ≥ 3 (FASTFALL, FASTRISE, gated + anchor), and none for plain buffer chains
of any length ≤ 5 or for length ≤ 2 (plain chains: proved for all lengths,
`CellBind.buf_settled`).
-/

namespace Formal.Net.CellBind.Chain
open Formal.Net Formal.Net.CellBind Formal.Gen Formal.Gen.Cells Formal.Net.Ops.Gen

/-! ## Stage functions from the generated netlists -/

theorem rdly_gate : ∀ a : Bool,
    genF bd_link_W2_D2_K2 "rdly.chain.g[0].u" .O ["c"] [a] = a ∧
    genF bd_link_W2_D2_K2 "rdly.chain.g[1].u" .O ["rdly.chain.s[1]"] [a] = a := by decide +kernel

/-- bd_link's `uack` line (FASTRISE): head buffer, then `s ∨ c`. -/
theorem uack_gate : ∀ s a : Bool,
    genF bd_link_W2_D2_K2 "uack.chain.g[0].u" .O ["c"] [a] = a ∧
    genF bd_link_W2_D2_K2 "uack.chain.g[1].u" .O ["uack.chain.s[1]", "c"] [s, a] = (s || a) := by
  decide +kernel

theorem ff_gate : ∀ s a : Bool,
    genF bd_delay_N3_FF "chain.g[0].u" .O ["a"] [a] = a ∧
    genF bd_delay_N3_FF "chain.g[1].u" .O ["chain.s[1]", "a"] [s, a] = (s && a) ∧
    genF bd_delay_N3_FF "chain.g[2].u" .O ["chain.s[2]", "a"] [s, a] = (s && a) := by decide +kernel

theorem fr_gate : ∀ s a : Bool,
    genF bd_delay_N3_FR "chain.g[1].u" .O ["chain.s[1]", "a"] [s, a] = (s || a) ∧
    genF bd_delay_N3_FR "chain.g[2].u" .O ["chain.s[2]", "a"] [s, a] = (s || a) := by decide +kernel

theorem gated_gate : ∀ s g : Bool,
    genF bd_delay_gated_N3 "chain.g[0].u" .O ["a"] [s] = s ∧
    genF bd_delay_gated_N3 "chain.g[1].u" .O ["chain.s[1]", "gate"] [s, g] = (s && g) ∧
    genF bd_delay_gated_N3 "chain.g[2].u" .O ["chain.s[2]", "gate"] [s, g] = (s && g) := by decide +kernel

theorem sym_gate : ∀ a : Bool,
    genF bd_delay_N3 "chain.g[0].u" .O ["a"] [a] = a ∧
    genF bd_delay_N3 "chain.g[1].u" .O ["chain.s[1]"] [a] = a ∧
    genF bd_delay_N3 "chain.g[2].u" .O ["chain.s[2]"] [a] = a := by decide +kernel

/-! ## Every stage kind is monotone and constant-preserving -/

/-- A two-input stage reading node `p` (its predecessor) and node `q` (its tap). -/
def stage2 (op : Bool → Bool → Bool) (p q : Nat) (f : Nat → Bool) : Bool := op (f p) (f q)

theorem stage_mono {n p q : Nat} (hp : p ≤ n) (hq : q ≤ n) (op : Bool → Bool → Bool)
    (hmono : ∀ a b c d : Bool, (a = true → c = true) → (b = true → d = true) → op a b = true → op c d = true)
    (hidem : ∀ v, op v v = v) : MonoOn n (stage2 op p q) ∧ IdemOn n (stage2 op p q) :=
  ⟨fun f g h hf => hmono _ _ _ _ (h p hp) (h q hq) hf,
   fun f v h => by simp only [stage2]; rw [h p hp, h q hq, hidem]⟩

theorem and_mono : ∀ a b c d : Bool, (a = true → c = true) → (b = true → d = true) →
    (a && b) = true → (c && d) = true := by decide
theorem or_mono : ∀ a b c d : Bool, (a = true → c = true) → (b = true → d = true) →
    (a || b) = true → (c || d) = true := by decide
theorem fst_mono : ∀ a b c d : Bool, (a = true → c = true) → (b = true → d = true) →
    (fun x _ => x) a b = true → (fun x _ => x) c d = true := by decide

/-! ## The FASTFALL hazard run on the generated `bd_delay_N3_FF` -/

/-- The generated FASTFALL chain as a node network: node 0 = `a`, node `k` = `chain.s[k]`,
node 3 = `z`, each moving to its generated LUT of the previous tick. -/
def ffG : Nat → (Nat → Bool) → Bool
  | 1, f => genF bd_delay_N3_FF "chain.g[0].u" .O ["a"] [f 0]
  | 2, f => genF bd_delay_N3_FF "chain.g[1].u" .O ["chain.s[1]", "a"] [f 1, f 0]
  | _, f => genF bd_delay_N3_FF "chain.g[2].u" .O ["chain.s[2]", "a"] [f 2, f 0]

def tr (l : List Bool) (d : Bool) : Trace := fun t => l.getD t d

/-- The run (found by `Wip/CO4/chain_path.py`): rows are `a, s1, s2, z` at t = 0..9, then
constant. -/
def ffRun : Nat → Trace
  | 0 => tr [false, true, true, true, true, false, false, true, true, true] true
  | 1 => tr [false, false, true, true, true, true, true, false, false, false] false
  | 2 => tr [false, false, false, true, true, true, true, true, false, false] false
  | _ => tr [false, false, false, false, true, true, false, false, true, false] false

theorem tr_tail (l : List Bool) (d : Bool) (t : Nat) (h : l.length ≤ t) : tr l d t = d := by
  simp [tr, List.getD_eq_getElem?_getD, List.getElem?_eq_none h]

theorem ff_si : NetSI 3 ffG ffRun := by
  intro k h1 hk t hm
  have hk' : k = 1 ∨ k = 2 ∨ k = 3 := by omega
  by_cases ht : t < 10
  · have key : ∀ t, t < 10 → ∀ k ∈ [1, 2, 3],
        ffRun k (t + 1) ≠ ffRun k t → ffRun k (t + 1) = ffG k (fun j => ffRun j t) := by
      decide +kernel
    rcases hk' with rfl | rfl | rfl <;> exact key t ht _ (by simp) hm
  · exfalso; apply hm
    rcases hk' with rfl | rfl | rfl <;>
      simp only [ffRun] <;> rw [tr_tail _ _ _ (by simp; omega), tr_tail _ _ _ (by simp; omega)]

theorem ff_persist : PersistEnd 3 ffRun := by
  intro t hm
  by_cases ht : t < 10
  · have key : ∀ t, t < 10 → ffRun 0 (t + 1) ≠ ffRun 0 t → ffRun 3 t = ffRun 0 t := by decide +kernel
    exact key t ht hm
  · exfalso; apply hm
    simp only [ffRun]; rw [tr_tail _ _ _ (by simp; omega), tr_tail _ _ _ (by simp; omega)]

theorem ff_init : ∀ j, j ≤ 3 → ffRun j 0 = ffRun 0 0 := by
  intro j hj
  have : j = 0 ∨ j = 1 ∨ j = 2 ∨ j = 3 := by omega
  rcases this with rfl | rfl | rfl | rfl <;> rfl

/-- **The FASTFALL hazard.** The generated `bd_delay_N3_FF` chain, run under the per-gate
SI model with end-only persistence and a quiet reset, has its output `z` fall at `t = 8`
while the input `a` was high: the lumped field "`z` moves only to `a`'s previous value"
fails. So `Settled` (H_CHAIN_SETTLED) cannot be weakened to `PersistEnd` for side-tapped
chains. -/
theorem fastfall_hazard :
    NetSI 3 ffG ffRun ∧ PersistEnd 3 ffRun ∧ (∀ j, j ≤ 3 → ffRun j 0 = ffRun 0 0) ∧
    ¬ (∀ t, ffRun 3 (t + 1) ≠ ffRun 3 t → ffRun 3 (t + 1) = ffRun 0 t) := by
  refine ⟨ff_si, ff_persist, ff_init, fun H => ?_⟩
  have := H 8 (by decide)
  exact absurd this (by decide)

/-- The same run violates H_CHAIN_SETTLED (as it must, by `mono_net`): at `t = 6` the input
rises while `s1` still shows 1. -/
theorem ff_not_settled : ¬ Settled 3 ffRun := by
  intro h
  have := h 6 (by decide) 1 (by decide)
  exact absurd this (by decide)

end Formal.Net.CellBind.Chain
