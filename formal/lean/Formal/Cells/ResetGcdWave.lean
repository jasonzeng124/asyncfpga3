import Formal.Cells.ResetGcd
import Formal.Cells.TernaryPhases
open Formal.Core.LutList

/-!
# Probe Rst3 (shard B, gcd_hw capstone): from release through the first wave

Notes: `formal/notes/B-reset-gcd-wave.md`. Builds on `ResetGcd.lean` (Rst2:
gcd_hw's 3322-node control network `gNet`, reset and release).

`ResetGcd.gcd_release_quiet` stops at the first move of one of the 10 frontier
link controllers. This file carries the run on: from the window in which rst
is released (any per-pin skew, glitches, even re-assertion) through the whole
first wave, up to the first time a request reaches the loop: the moment one of
the three entry steers `ucond_br9/10/11` (their 6 LUT outputs, `zL`) leaves 0.
Data nets stay `x` throughout.

Method: multi-phase ternary soundness (`TernaryPhases.phase_cov`) applied to
the CUT network `gCut`: `gNet` with the 6 steer outputs turned into inputs.
A run of `gNet` is a run of `gCut` (`cutRun`, `cutBounded`), and while the
steers have not moved their values are the cut inputs' value 0. On `gCut` the
whole first wave is acyclic, so:

* phase A (rst window, inputs `uW`: rst `x`, data `x`, steers 0): the ternary
  state `sA` (control nodes at reset, except the 108 wave nodes and rst, which
  are `x`) is closed under the window step (`sA_closed`, decided);
* phase B (rst final 0, inputs `aF`): the Jacobi iterates from `sA` are covered
  by a ranked certificate `sB m` (`iter_le_bst`): node `n` of the wave is
  definite from iterate `wR n` on, with value `wF n`. The B phases are:
  - B1: `rst`
  - B2: `ulink_n1__1.ctl.u`, `ulink_n155__0.ctl.u`, `ulink_n155__1.ctl.u`, `ulink_n36__0.ctl.u`, `ulink_n36__1.ctl.u`, `ulink_n36__2.ctl.u`, `ulink_n68__0.ctl.u`, `ulink_n68__1.ctl.u`, `ulink_n94__0.ctl.u`, `ulink_n94__1.ctl.u`
  - B3: `ucmpi0.uor` and the six ack delay elements `uack.g[0..5]` of each of the 10 frontier links (61 nodes)
  - B4: `ucmpi0.udly.g[0].u`, `ufork11.u.u`, `ufork19.u.u`, `ufork24.u.u`, `ufork39.u.u`
  - B5 .. B33: one element each, `ucmpi0.udly.g[1]` .. `ucmpi0.udly.g[29]` (`g[k]` at B(k+4))
  - B34: `ucond_br9_j.u.u`, `ucond_br10_j.u.u`, `ucond_br11_j.u.u`
  After `maxB = 34` iterates every control node is definite (`sB_max`).

Results (namespace `Formal.Cells.ResetGcdWave`):
* `gcd_first_wave`: every bounded run, from the reset state, with rst doing
  anything on `(S, F]` and 0 on `(F, E]`, and the steers still 0 on `(S, E]`:
  `sA` covers the run on `[S, E]` and `sB m` covers it on
  `[F + m(D+W+1), E]`, for every `m`;
* `gcd_wave_only`: before the loop is requested only the 108 wave nodes (and
  rst) can move;
* `gcd_wave_settled`: from `F + 34(D+W+1)` to `E` every control node is at
  `sigB`, whatever rst did in its window: no event of the wave is lost to a
  cell still held in reset (H_NO_RETURN for the reset-release window);
* `gcd_wave_moves`: `sigB` differs from the reset state exactly on the 108
  wave nodes (and rst); `gcd_wave_quiet`: at `sigB` every control node of
  `gNet` other than the 6 steers is excited to its own value, and each steer
  is excited to `x` only through its data select (`gcd_steer_req`: with a
  definite select bit `b`, O6 = `b` and O5 = `!b`: one branch is requested);
* `gcd_boot`: the composition with `ResetGcd.gcd_reset_binary`, from ANY
  power-up state;
* `gcd_loop_late`: no steer leaves 0 until 34 steps after rst was last 1
  (a causal chain of 34 real LUTs, `steerPaths_ok`), and `gcd_clean_release`:
  with a clean rst edge at `F` the whole segment from power-up, with the
  steer-hold hypothesis only needed after `F + 34`; with `W < 34` every rst
  pin reads 0 when the loop is first requested (`rst_reads_low`);
* negative controls `neg_nocut`, `neg_rank`, `neg_chain`.

Core Lean only. Every certificate check is `decide +kernel`.
-/

namespace Formal.Cells.ResetGcdWave
open Formal.Cells Formal.Cells.TernarySound Formal.Cells.ResetContract Formal.Cells.ResetGcd

/-! ## Generic: cutting a network, and ranked B certificates -/

/-- `N` with the nodes in `z` turned into inputs. -/
def cut (N : Circ) (z : Nat → Bool) : Circ :=
  ⟨N.size, fun n => if z n then .input else N.node n⟩

theorem cut_gate {N : Circ} {z : Nat → Bool} {j init : Nat} {pins : List Src}
    (h : (cut N z).node j = .gate init pins) : N.node j = .gate init pins := by
  unfold cut at h
  dsimp only at h
  split at h
  · cases h
  · exact h

/-- A run of `N` is a run of any cut of `N` (same wires). -/
def cutRun {N : Circ} {v : Nat → Nat → Bool} (R : Run N v) (z : Nat → Bool) :
    Run (cut N z) v where
  rd := R.rd
  rd_le := R.rd_le
  gate k j init pins h := R.gate k j init pins (cut_gate h)

theorem cutBounded {N : Circ} {v : Nat → Nat → Bool} {R : Run N v} {D W : Nat}
    (hB : Bounded N v R D W) (z : Nat → Bool) : Bounded (cut N z) v (cutRun R z) D W where
  wire := hB.wire
  gate k j init pins b h hx := hB.gate k j init pins b (cut_gate h) hx

theorem le_x (a : K3) : le a .x := Or.inr rfl

/-- Ranked B certificate: node `n` keeps its A value if `r n = 0`, else it is
`x` before iterate `r n` and `fin n` from it on. -/
def bst (s : Nat → K3) (r : Nat → Nat) (fin : Nat → Bool) (i n : Nat) : K3 :=
  if r n = 0 then s n else if r n ≤ i then K3.ofBool (fin n) else .x

section Ranked
variable (s : Nat → K3) (r : Nat → Nat) (fin : Nat → Bool)

theorem bst_zero (hC2 : ∀ n, r n ≠ 0 → s n = .x) : bst s r fin 0 = s := by
  funext n
  unfold bst
  by_cases h : r n = 0
  · rw [ite_eq_left h]
  · rw [ite_eq_right h, ite_eq_right (by omega), hC2 n h]

theorem bst_mono {i j : Nat} (hji : j ≤ i) : sle (bst s r fin i) (bst s r fin j) := by
  intro n
  unfold bst
  by_cases h0 : r n = 0
  · rw [ite_eq_left h0, ite_eq_left h0]; exact le_refl _
  · rw [ite_eq_right h0, ite_eq_right h0]
    by_cases hj : r n ≤ j
    · rw [ite_eq_left hj, ite_eq_left (by omega)]; exact le_refl _
    · rw [ite_eq_right hj]; exact le_x _

theorem bst_le_s (hC2 : ∀ n, r n ≠ 0 → s n = .x) (i : Nat) : sle (bst s r fin i) s := by
  intro n
  unfold bst
  by_cases h0 : r n = 0
  · rw [ite_eq_left h0]; exact le_refl _
  · rw [hC2 n h0]; exact le_x _

theorem bst_step (N : Circ) (u a : Nat → K3) (hpost : sle (stepK N u s) s) (hau : sle a u)
    (hC2 : ∀ n, r n ≠ 0 → s n = .x)
    (hC1 : ∀ n, r n ≠ 0 → stepK N a (bst s r fin (r n - 1)) n = K3.ofBool (fin n)) (i : Nat) :
    sle (stepK N a (bst s r fin i)) (bst s r fin (i + 1)) := by
  intro n
  by_cases h0 : r n = 0
  · have e : bst s r fin (i + 1) n = s n := by unfold bst; rw [ite_eq_left h0]
    rw [e]
    exact le_trans (stepK_mono N hau (bst_le_s s r fin hC2 i) n) (hpost n)
  · by_cases hi : r n ≤ i + 1
    · have e : bst s r fin (i + 1) n = K3.ofBool (fin n) := by
        unfold bst; rw [ite_eq_right h0, ite_eq_left hi]
      rw [e, ← hC1 n h0]
      exact stepK_mono N (fun m => le_refl (a m)) (bst_mono s r fin (by omega)) n
    · have e : bst s r fin (i + 1) n = .x := by unfold bst; rw [ite_eq_right h0, ite_eq_right hi]
      rw [e]; exact le_x _

/-- **Ranked B certificate.** If `s` is closed under the window step for `u`,
`a ⊑ u`, the ranked nodes are `x` in `s`, and each ranked node's excitation
from the certificate one iterate earlier is its `fin` value, then the `i`-th
Jacobi iterate from `s` with inputs `a` is below the certificate. -/
theorem iter_le_bst (N : Circ) (u a : Nat → K3) (hpost : sle (stepK N u s) s) (hau : sle a u)
    (hC2 : ∀ n, r n ≠ 0 → s n = .x)
    (hC1 : ∀ n, r n ≠ 0 → stepK N a (bst s r fin (r n - 1)) n = K3.ofBool (fin n)) :
    ∀ i, sle (iter N a i s) (bst s r fin i) := by
  intro i
  induction i with
  | zero =>
    rw [bst_zero s r fin hC2]
    exact fun n => le_refl _
  | succ i ih =>
    rw [iter_succ']
    exact fun n => le_trans (stepK_mono N (fun m => le_refl (a m)) ih n)
      (bst_step s r fin N u a hpost hau hC2 hC1 i n)

end Ranked

/-! ## gcd_hw: the cut, the inputs, the certificates -/

/-- The 6 LUT outputs of the loop-entry steers (O5 = false branch, O6 = true
branch):
  - 100 `ucond_br9.u.O5`, 101 `ucond_br9.u.O6` (select `n5__2_data[0]`)
  - 104 `ucond_br10.u.O5`, 105 `ucond_br10.u.O6` (select `n5__1_data[0]`)
  - 108 `ucond_br11.u.O5`, 109 `ucond_br11.u.O6` (select `n5__0_data[0]`) -/
def zL : List Nat := [100, 101, 104, 105, 108, 109]
def zB (n : Nat) : Bool := zL.contains n
/-- gcd_hw's control network with the steer outputs cut into inputs. -/
def gCut : Circ := cut gNet zB

/-- The wave certificate (UNTRUSTED, made by the scratchpad script
`wave/ranks.py`; checked below): `(node, B rank, final value)`. Node 0 is rst. -/
def wL : List (Nat × Nat × Bool) :=
  [(0, 1, false), (67, 3, true), (68, 4, true), (69, 5, true), (70, 6, true), (71, 7, true),
  (72, 8, true), (73, 9, true), (74, 10, true), (75, 11, true), (76, 12, true), (77, 13, true),
  (78, 14, true), (79, 15, true), (80, 16, true), (81, 17, true), (82, 18, true), (83, 19, true),
  (84, 20, true), (85, 21, true), (86, 22, true), (87, 23, true), (88, 24, true), (89, 25, true),
  (90, 26, true), (91, 27, true), (92, 28, true), (93, 29, true), (94, 30, true), (95, 31, true),
  (96, 32, true), (97, 33, true), (99, 34, true), (103, 34, true), (107, 34, true), (310, 4, true),
  (629, 4, true), (848, 4, true), (1401, 4, true), (1696, 2, true), (1697, 3, true), (1698, 3, true),
  (1699, 3, true), (1700, 3, true), (1701, 3, true), (1702, 3, true), (1931, 2, true), (1932, 3, true),
  (1933, 3, true), (1934, 3, true), (1935, 3, true), (1936, 3, true), (1937, 3, true), (1938, 2, true),
  (1939, 3, true), (1940, 3, true), (1941, 3, true), (1942, 3, true), (1943, 3, true), (1944, 3, true),
  (2182, 2, true), (2183, 3, true), (2184, 3, true), (2185, 3, true), (2186, 3, true), (2187, 3, true),
  (2188, 3, true), (2189, 2, true), (2190, 3, true), (2191, 3, true), (2192, 3, true), (2193, 3, true),
  (2194, 3, true), (2195, 3, true), (2196, 2, true), (2197, 3, true), (2198, 3, true), (2199, 3, true),
  (2200, 3, true), (2201, 3, true), (2202, 3, true), (2432, 2, true), (2433, 3, true), (2434, 3, true),
  (2435, 3, true), (2436, 3, true), (2437, 3, true), (2438, 3, true), (2439, 2, true), (2440, 3, true),
  (2441, 3, true), (2442, 3, true), (2443, 3, true), (2444, 3, true), (2445, 3, true), (2596, 2, true),
  (2597, 3, true), (2598, 3, true), (2599, 3, true), (2600, 3, true), (2601, 3, true), (2602, 3, true),
  (2603, 2, true), (2604, 3, true), (2605, 3, true), (2606, 3, true), (2607, 3, true), (2608, 3, true),
  (2609, 3, true)]

/-- A binary search tree over `wL` (keys = node numbers), for fast kernel
lookup; `wT_spec` checks it against `wL`. -/
inductive WT where
  | leaf
  | br (l : WT) (q : Nat × Nat × Bool) (r : WT)

def WT.find : WT → Nat → Option (Nat × Nat × Bool)
  | .leaf, _ => none
  | .br l q r, n => if n < q.1 then l.find n else if q.1 < n then r.find n else some q

/-- The tree (GENERATED from `wL`). -/
def wT : WT := (.br (.br (.br (.br (.br (.br (.br .leaf (0, 1, false) .leaf) (67, 3, true) (.br .leaf (68, 4, true) .leaf)) (69, 5, true) (.br (.br .leaf (70, 6, true) .leaf) (71, 7, true) .leaf)) (72, 8, true) (.br (.br (.br .leaf (73, 9, true) .leaf) (74, 10, true) (.br .leaf (75, 11, true) .leaf)) (76, 12, true) (.br (.br .leaf (77, 13, true) .leaf) (78, 14, true) .leaf))) (79, 15, true) (.br (.br (.br (.br .leaf (80, 16, true) .leaf) (81, 17, true) (.br .leaf (82, 18, true) .leaf)) (83, 19, true) (.br (.br .leaf (84, 20, true) .leaf) (85, 21, true) .leaf)) (86, 22, true) (.br (.br (.br .leaf (87, 23, true) .leaf) (88, 24, true) (.br .leaf (89, 25, true) .leaf)) (90, 26, true) (.br (.br .leaf (91, 27, true) .leaf) (92, 28, true) .leaf)))) (93, 29, true) (.br (.br (.br (.br (.br .leaf (94, 30, true) .leaf) (95, 31, true) (.br .leaf (96, 32, true) .leaf)) (97, 33, true) (.br (.br .leaf (99, 34, true) .leaf) (103, 34, true) .leaf)) (107, 34, true) (.br (.br (.br .leaf (310, 4, true) .leaf) (629, 4, true) (.br .leaf (848, 4, true) .leaf)) (1401, 4, true) (.br (.br .leaf (1696, 2, true) .leaf) (1697, 3, true) .leaf))) (1698, 3, true) (.br (.br (.br (.br .leaf (1699, 3, true) .leaf) (1700, 3, true) (.br .leaf (1701, 3, true) .leaf)) (1702, 3, true) (.br (.br .leaf (1931, 2, true) .leaf) (1932, 3, true) .leaf)) (1933, 3, true) (.br (.br (.br .leaf (1934, 3, true) .leaf) (1935, 3, true) .leaf) (1936, 3, true) (.br (.br .leaf (1937, 3, true) .leaf) (1938, 2, true) .leaf))))) (1939, 3, true) (.br (.br (.br (.br (.br (.br .leaf (1940, 3, true) .leaf) (1941, 3, true) (.br .leaf (1942, 3, true) .leaf)) (1943, 3, true) (.br (.br .leaf (1944, 3, true) .leaf) (2182, 2, true) .leaf)) (2183, 3, true) (.br (.br (.br .leaf (2184, 3, true) .leaf) (2185, 3, true) (.br .leaf (2186, 3, true) .leaf)) (2187, 3, true) (.br (.br .leaf (2188, 3, true) .leaf) (2189, 2, true) .leaf))) (2190, 3, true) (.br (.br (.br (.br .leaf (2191, 3, true) .leaf) (2192, 3, true) (.br .leaf (2193, 3, true) .leaf)) (2194, 3, true) (.br (.br .leaf (2195, 3, true) .leaf) (2196, 2, true) .leaf)) (2197, 3, true) (.br (.br (.br .leaf (2198, 3, true) .leaf) (2199, 3, true) (.br .leaf (2200, 3, true) .leaf)) (2201, 3, true) (.br (.br .leaf (2202, 3, true) .leaf) (2432, 2, true) .leaf)))) (2433, 3, true) (.br (.br (.br (.br (.br .leaf (2434, 3, true) .leaf) (2435, 3, true) (.br .leaf (2436, 3, true) .leaf)) (2437, 3, true) (.br (.br .leaf (2438, 3, true) .leaf) (2439, 2, true) .leaf)) (2440, 3, true) (.br (.br (.br .leaf (2441, 3, true) .leaf) (2442, 3, true) (.br .leaf (2443, 3, true) .leaf)) (2444, 3, true) (.br (.br .leaf (2445, 3, true) .leaf) (2596, 2, true) .leaf))) (2597, 3, true) (.br (.br (.br (.br .leaf (2598, 3, true) .leaf) (2599, 3, true) (.br .leaf (2600, 3, true) .leaf)) (2601, 3, true) (.br (.br .leaf (2602, 3, true) .leaf) (2603, 2, true) .leaf)) (2604, 3, true) (.br (.br (.br .leaf (2605, 3, true) .leaf) (2606, 3, true) .leaf) (2607, 3, true) (.br (.br .leaf (2608, 3, true) .leaf) (2609, 3, true) .leaf))))))

def wLook (n : Nat) : Option (Nat × Nat × Bool) := wT.find n
/-- B rank (0: not in the wave). -/
def wR (n : Nat) : Nat := match wLook n with | some q => q.2.1 | none => 0
/-- Final value. -/
def wF (n : Nat) : Bool := match wLook n with | some q => q.2.2 | none => false

/-- Phase A state: control nodes at reset, wave nodes and rst `x`, data `x`. -/
def sA (n : Nat) : K3 := if wR n ≠ 0 then .x else if gCtl n then K3.ofBool (gR n) else .x
/-- Window inputs of `gCut`: rst anything, data anything, steers 0. -/
def uW (n : Nat) : K3 := if n = 0 then .x else if zB n then .f else .x
/-- Final inputs of `gCut`: rst 0, data anything, steers 0. -/
def aF (n : Nat) : K3 := if n = 0 then .f else if zB n then .f else .x
def maxB : Nat := 34
/-- Phase B state after `m` iterates (certificate). -/
def sB (m : Nat) : Nat → K3 := bst sA wR wF m

/-- The state at the end of the first wave, as Booleans on control nodes. -/
def sigB (n : Nat) : Bool := if wR n ≠ 0 then wF n else gR n

def leB (a b : K3) : Bool := decide (a = b) || decide (b = .x)

/-- Excitation in the UNCUT network at the end-of-wave state (rst 0, data `x`). -/
def endExc (n : Nat) : K3 :=
  match gNode n with
  | .input => .x
  | .gate init pins => lutK init (pins.map (srcK (sB maxB)))

/-- Everything checked per node: A closure, the B certificate, and
quiescence at the end of the wave (steers: `x`, everyone else: own value). -/
def nodeW (n : Nat) : Bool :=
  leB (stepK gCut uW sA n) (sA n) &&
  (wR n == 0 || decide (stepK gCut aF (sB (wR n - 1)) n = K3.ofBool (wF n))) &&
  (!gCtl n || n == 0 ||
    (if zB n then decide (endExc n = .x) else decide (endExc n = sB maxB n)))

def chunkW (lo k : Nat) : Bool := (List.range' lo k).all nodeW

theorem chunkW_mem {lo k : Nat} (h : chunkW lo k = true) {n : Nat} (h1 : lo ≤ n)
    (h2 : n < lo + k) : nodeW n = true :=
  List.all_eq_true.1 h n (List.mem_range'_1.2 ⟨h1, h2⟩)

theorem cw0 : chunkW 0 200 = true := by decide +kernel
theorem cw1 : chunkW 200 200 = true := by decide +kernel
theorem cw2 : chunkW 400 200 = true := by decide +kernel
theorem cw3 : chunkW 600 200 = true := by decide +kernel
theorem cw4 : chunkW 800 200 = true := by decide +kernel
theorem cw5 : chunkW 1000 200 = true := by decide +kernel
theorem cw6 : chunkW 1200 200 = true := by decide +kernel
theorem cw7 : chunkW 1400 200 = true := by decide +kernel
theorem cw8 : chunkW 1600 200 = true := by decide +kernel
theorem cw9 : chunkW 1800 200 = true := by decide +kernel
theorem cw10 : chunkW 2000 200 = true := by decide +kernel
theorem cw11 : chunkW 2200 200 = true := by decide +kernel
theorem cw12 : chunkW 2400 200 = true := by decide +kernel
theorem cw13 : chunkW 2600 200 = true := by decide +kernel
theorem cw14 : chunkW 2800 200 = true := by decide +kernel
theorem cw15 : chunkW 3000 200 = true := by decide +kernel
theorem cw16 : chunkW 3200 122 = true := by decide +kernel

theorem allW (n : Nat) (h : n < gM) : nodeW n = true := by
  have hM : gM = 3322 := rfl
  by_cases h0 : n < 200
  · exact chunkW_mem cw0 (by omega) (by omega)
  by_cases h1 : n < 400
  · exact chunkW_mem cw1 (by omega) (by omega)
  by_cases h2 : n < 600
  · exact chunkW_mem cw2 (by omega) (by omega)
  by_cases h3 : n < 800
  · exact chunkW_mem cw3 (by omega) (by omega)
  by_cases h4 : n < 1000
  · exact chunkW_mem cw4 (by omega) (by omega)
  by_cases h5 : n < 1200
  · exact chunkW_mem cw5 (by omega) (by omega)
  by_cases h6 : n < 1400
  · exact chunkW_mem cw6 (by omega) (by omega)
  by_cases h7 : n < 1600
  · exact chunkW_mem cw7 (by omega) (by omega)
  by_cases h8 : n < 1800
  · exact chunkW_mem cw8 (by omega) (by omega)
  by_cases h9 : n < 2000
  · exact chunkW_mem cw9 (by omega) (by omega)
  by_cases h10 : n < 2200
  · exact chunkW_mem cw10 (by omega) (by omega)
  by_cases h11 : n < 2400
  · exact chunkW_mem cw11 (by omega) (by omega)
  by_cases h12 : n < 2600
  · exact chunkW_mem cw12 (by omega) (by omega)
  by_cases h13 : n < 2800
  · exact chunkW_mem cw13 (by omega) (by omega)
  by_cases h14 : n < 3000
  · exact chunkW_mem cw14 (by omega) (by omega)
  by_cases h15 : n < 3200
  · exact chunkW_mem cw15 (by omega) (by omega)
  exact chunkW_mem cw16 (by omega) (by omega)
/-- Shape of the certificate: every entry is a real node, ranked `1..34`,
and its final value is the opposite of its reset value (every wave node,
and rst, moves); 109 entries. -/
theorem wL_shape : wL.all (fun q => decide (q.1 < gM) && decide (0 < q.2.1) &&
    decide (q.2.1 ≤ maxB) && gCtl q.1 && (q.2.2 == !gR q.1)) = true ∧ wL.length = 109 := by
  decide +kernel

def WT.toList : WT → List (Nat × Nat × Bool)
  | .leaf => []
  | .br l q r => l.toList ++ q :: r.toList

/-- The tree holds exactly the list `wL` (which is sorted by node). -/
theorem wT_list : wT.toList = wL := by decide +kernel

theorem WT.find_mem {t : WT} {n : Nat} {q : Nat × Nat × Bool} (h : t.find n = some q) :
    q ∈ t.toList := by
  induction t with
  | leaf => simp [WT.find] at h
  | br l q' r ihl ihr =>
    simp only [WT.find] at h
    simp only [WT.toList, List.mem_append, List.mem_cons]
    by_cases h1 : n < q'.1
    · rw [ite_eq_left h1] at h; exact Or.inl (ihl h)
    · rw [ite_eq_right h1] at h
      by_cases h2 : q'.1 < n
      · rw [ite_eq_left h2] at h; exact Or.inr (Or.inr (ihr h))
      · rw [ite_eq_right h2] at h
        cases h
        exact Or.inr (Or.inl rfl)

/-- Every key of the tree is below `gM`. -/
def WT.keysLt (b : Nat) : WT → Bool
  | .leaf => true
  | .br l q r => decide (q.1 < b) && l.keysLt b && r.keysLt b

theorem wT_keys : wT.keysLt gM = true := by decide +kernel

theorem WT.find_lt {t : WT} {b n : Nat} {q : Nat × Nat × Bool} (hk : t.keysLt b = true)
    (h : t.find n = some q) : q.1 = n ∧ n < b := by
  induction t with
  | leaf => simp [WT.find] at h
  | br l q' r ihl ihr =>
    simp only [WT.keysLt, Bool.and_eq_true, decide_eq_true_eq] at hk
    simp only [WT.find] at h
    by_cases h1 : n < q'.1
    · rw [ite_eq_left h1] at h; exact ihl hk.1.2 h
    · rw [ite_eq_right h1] at h
      by_cases h2 : q'.1 < n
      · rw [ite_eq_left h2] at h; exact ihr hk.2 h
      · rw [ite_eq_right h2] at h
        cases h
        exact ⟨by omega, by omega⟩

theorem wLook_mem {n : Nat} {q : Nat × Nat × Bool} (h : wLook n = some q) : q ∈ wL ∧ q.1 = n :=
  ⟨wT_list ▸ WT.find_mem h, (WT.find_lt wT_keys h).1⟩

theorem wq {n : Nat} (h : wR n ≠ 0) : ∃ q, q ∈ wL ∧ q.1 = n ∧ wR n = q.2.1 ∧ wF n = q.2.2 := by
  cases hl : wLook n with
  | none => simp [wR, hl] at h
  | some q =>
    obtain ⟨hm, he⟩ := wLook_mem hl
    exact ⟨q, hm, he, by simp [wR, hl], by simp [wF, hl]⟩

theorem wq_shape {n : Nat} (h : wR n ≠ 0) :
    n < gM ∧ wR n ≤ maxB ∧ gCtl n = true ∧ wF n = !gR n := by
  obtain ⟨q, hm, he, hr, hf⟩ := wq h
  have := List.all_eq_true.1 wL_shape.1 q hm
  simp only [Bool.and_eq_true, decide_eq_true_eq, beq_iff_eq] at this
  subst he
  exact ⟨this.1.1.1.1, hr ▸ this.1.1.2, this.1.2, hf ▸ this.2⟩

theorem nodeW_of {n : Nat} (h : n < gM) :
    le (stepK gCut uW sA n) (sA n) ∧
    (wR n ≠ 0 → stepK gCut aF (sB (wR n - 1)) n = K3.ofBool (wF n)) ∧
    (gCtl n = true → n ≠ 0 → zB n = false → endExc n = sB maxB n) ∧
    (gCtl n = true → zB n = true → endExc n = .x) := by
  have hw := allW n h
  simp only [nodeW, leB, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq, beq_iff_eq] at hw
  obtain ⟨⟨h1, h2⟩, h3⟩ := hw
  refine ⟨h1, fun hr => ?_, fun hc h0 hz => ?_, fun hc hz => ?_⟩
  · rcases h2 with h2 | h2
    · exact absurd h2 hr
    · exact h2
  · rcases h3 with (h3 | h3) | h3
    · simp [hc] at h3
    · exact absurd h3 h0
    · rw [hz] at h3; simpa using h3
  · rcases h3 with (h3 | h3) | h3
    · simp [hc] at h3
    · subst h3; simp [zB, zL] at hz
    · rw [hz] at h3; simpa using h3

theorem gCtl_ge {n : Nat} (h : ¬ n < gM) : gCtl n = false := by
  simp [gCtl, h]

theorem wR_ge {n : Nat} (h : ¬ n < gM) : wR n = 0 :=
  Classical.byContradiction fun hr => h (wq_shape hr).1

/-- **Phase A closure**: `sA` is closed under the window step of `gCut`. -/
theorem sA_closed : sle (stepK gCut uW sA) sA := by
  intro n
  by_cases hn : n < gM
  · exact (nodeW_of hn).1
  · have : sA n = .x := by simp [sA, gCtl_ge hn]
    rw [this]; exact le_x _

theorem aF_le_uW : sle aF uW := by
  intro n
  unfold aF uW
  by_cases h0 : n = 0
  · rw [ite_eq_left h0, ite_eq_left h0]; exact le_x _
  · rw [ite_eq_right h0, ite_eq_right h0]; exact le_refl _

theorem sA_C2 (n : Nat) (h : wR n ≠ 0) : sA n = .x := by
  unfold sA; rw [ite_eq_left h]

theorem sB_C1 (n : Nat) (h : wR n ≠ 0) :
    stepK gCut aF (bst sA wR wF (wR n - 1)) n = K3.ofBool (wF n) :=
  (nodeW_of (wq_shape h).1).2.1 h

/-- **Phase B**: the Jacobi iterates from `sA` are below the certificate. -/
theorem iter_sB (m : Nat) : sle (iter gCut aF m sA) (sB m) :=
  iter_le_bst sA wR wF gCut uW aF sA_closed aF_le_uW sA_C2 sB_C1 m

theorem sB_max (n : Nat) (hc : gCtl n = true) : sB maxB n = K3.ofBool (sigB n) := by
  unfold sB bst sigB
  by_cases h : wR n = 0
  · simp [h, sA, hc]
  · rw [ite_eq_right h, ite_eq_left (wq_shape h).2.1, ite_eq_left h]

/-! ## The first wave, on every bounded run -/

/-- **The first wave (whole network, GMW, any rst skew).** Take a bounded run
of gcd_hw's control network. Suppose every control node other than rst is at
its reset value on `[S - W, S]` (`H_SETTLED`, from `gcd_reset_binary`); rst
does anything on `(S, F]` (falls with any per-pin skew, glitches, or is
re-asserted) and is 0 on `(F, E]` (`H_RST_LOW`); data nets do anything; and
`E` is no later than the step before a loop-entry steer leaves 0
(`H_STEER_HOLD`, the definition of the segment's end, not a timing
assumption). Then `sA` covers the run on `[S, E]`, and after each B phase `m`
the certificate `sB m` covers it on `[F + m(D+W+1), E]`. -/
theorem gcd_first_wave {v : Nat → Nat → Bool} (Rn : Run gNet v) {D W : Nat}
    (hB : Bounded gNet v Rn D W) (S F E : Nat) (hSF : S ≤ F)
    (H_SETTLED : ∀ k n, k ≤ S → S ≤ k + W → gCtl n = true → n ≠ 0 → v k n = gR n)
    (H_RST_LOW : ∀ k, F < k → k ≤ E → v k 0 = false)
    (H_STEER_HOLD : ∀ k z, z ∈ zL → S < k → k ≤ E → v k z = false) :
    (∀ k, S ≤ k + W → k ≤ E → covers sA (v k)) ∧
    (∀ m k, F + m * (D + W + 1) ≤ k → k ≤ E → covers (sB m) (v k)) := by
  have hent : ∀ k, k ≤ S → S ≤ k + W → covers sA (v k) := by
    intro k h1 h2 n
    unfold sA
    by_cases hr : wR n ≠ 0
    · rw [ite_eq_left hr]; rfl
    · rw [ite_eq_right hr]
      cases hc : gCtl n
      · rfl
      · have h0 : n ≠ 0 := by
          intro h0; subst h0; exact hr (by decide +kernel)
        rw [ite_eq_left rfl, H_SETTLED k n h1 h2 hc h0]; exact admits_ofBool _
  have hz : ∀ n, zB n = true → n ∈ zL := fun n h => List.contains_iff_mem.1 h
  have hu : ∀ k, S < k → k ≤ E → TernaryPhases.InputsIn gCut v uW k := by
    intro k h1 h2 n _
    unfold uW
    by_cases h0 : n = 0
    · rw [ite_eq_left h0]; rfl
    · rw [ite_eq_right h0]
      cases hzn : zB n
      · rfl
      · rw [ite_eq_left rfl, H_STEER_HOLD k n (hz n hzn) h1 h2]; rfl
  have ha : ∀ k, F < k → k ≤ E → TernaryPhases.InputsIn gCut v aF k := by
    intro k h1 h2 n _
    unfold aF
    by_cases h0 : n = 0
    · rw [ite_eq_left h0, h0, H_RST_LOW k h1 h2]; rfl
    · rw [ite_eq_right h0]
      cases hzn : zB n
      · rfl
      · rw [ite_eq_left rfl, H_STEER_HOLD k n (hz n hzn) (by omega) h2]; rfl
  have hc := TernaryPhases.phase_cov gCut uW aF sA sA_closed (cutRun Rn zB) (cutBounded hB zB)
    S F E hSF hent hu ha
  exact ⟨hc.1, fun m k h1 h2 => covers_of_sle (iter_sB m) (hc.2 m k h1 h2)⟩

/-- **Only the wave moves** before the loop is requested: on `[S, E]` every
control node outside the 109-entry certificate (rst and the 108 wave nodes)
is at its reset value. -/
theorem gcd_wave_only {v : Nat → Nat → Bool} (Rn : Run gNet v) {D W : Nat}
    (hB : Bounded gNet v Rn D W) (S F E : Nat) (hSF : S ≤ F)
    (H_SETTLED : ∀ k n, k ≤ S → S ≤ k + W → gCtl n = true → n ≠ 0 → v k n = gR n)
    (H_RST_LOW : ∀ k, F < k → k ≤ E → v k 0 = false)
    (H_STEER_HOLD : ∀ k z, z ∈ zL → S < k → k ≤ E → v k z = false) :
    ∀ k n, S ≤ k → k ≤ E → gCtl n = true → wR n = 0 → v k n = gR n := by
  intro k n h1 h2 hc hr
  have h := (gcd_first_wave Rn hB S F E hSF H_SETTLED H_RST_LOW H_STEER_HOLD).1 k (by omega) h2 n
  simp only [sA, hr, hc, ne_eq, not_true_eq_false, ite_false, ite_true] at h
  exact (admits_ofBool_iff _ _).1 h

/-- **End of the first wave; H_NO_RETURN for the reset-release window.**
From `F + 34(D+W+1)` until the first loop request, every control node is at
`sigB`, the same state for EVERY rst waveform in `(S, F]` (any skew, glitches,
re-assertion): no event of the wave is lost to a cell still held in reset. -/
theorem gcd_wave_settled {v : Nat → Nat → Bool} (Rn : Run gNet v) {D W : Nat}
    (hB : Bounded gNet v Rn D W) (S F E : Nat) (hSF : S ≤ F)
    (H_SETTLED : ∀ k n, k ≤ S → S ≤ k + W → gCtl n = true → n ≠ 0 → v k n = gR n)
    (H_RST_LOW : ∀ k, F < k → k ≤ E → v k 0 = false)
    (H_STEER_HOLD : ∀ k z, z ∈ zL → S < k → k ≤ E → v k z = false) :
    ∀ k n, F + maxB * (D + W + 1) ≤ k → k ≤ E → gCtl n = true → v k n = sigB n := by
  intro k n h1 h2 hc
  have h := (gcd_first_wave Rn hB S F E hSF H_SETTLED H_RST_LOW H_STEER_HOLD).2 maxB k h1 h2 n
  rw [sB_max n hc] at h
  exact (admits_ofBool_iff _ _).1 h

/-- **What moved**: a control node's end-of-wave value differs from its reset
value iff it is in the certificate (rst and the 108 wave nodes). -/
theorem gcd_wave_moves (n : Nat) (_hc : gCtl n = true) : sigB n ≠ gR n ↔ wR n ≠ 0 := by
  constructor
  · intro h hr; apply h; simp [sigB, hr]
  · intro hr
    rw [show sigB n = wF n by simp [sigB, hr], (wq_shape hr).2.2.2]
    cases gR n <;> decide

/-- **Quiescence at the end of the wave** (uncut network, rst 0, data `x`):
every control node other than rst and the 6 steers is excited to its own
end-of-wave value; each steer is excited to `x`. -/
theorem gcd_wave_quiet (n : Nat) (hc : gCtl n = true) (h0 : n ≠ 0) :
    (n ∉ zL → endExc n = K3.ofBool (sigB n)) ∧ (n ∈ zL → endExc n = .x) := by
  have hn := gCtl_lt hc
  refine ⟨fun hz => ?_, fun hz => ?_⟩
  · have hz' : zB n = false := by
      cases h : zB n
      · rfl
      · exact absurd (List.contains_iff_mem.1 h) hz
    rw [(nodeW_of hn).2.2.1 hc h0 hz', sB_max n hc]
  · exact (nodeW_of hn).2.2.2 hc (List.contains_iff_mem.2 hz)

/-- The end-of-wave state with the three steer selects (data nets 1, 2, 3)
set to the bit `b`. -/
def selSt (b : Bool) (m : Nat) : K3 :=
  if m = 1 ∨ m = 2 ∨ m = 3 then K3.ofBool b else sB maxB m

def steerExc (b : Bool) (n : Nat) : K3 :=
  match gNode n with
  | .input => .x
  | .gate init pins => lutK init (pins.map (srcK (selSt b)))

/-- **The loop is requested**: at the end of the wave the three steer joins
(99 `ucond_br9_j`, 103 `ucond_br10_j`, 107 `ucond_br11_j`) are 1 and, with a
definite select bit `b`, each steer's O6 (true branch) is excited to `b` and
its O5 (false branch) to `!b`. -/
theorem gcd_steer_req :
    sigB 99 = true ∧ sigB 103 = true ∧ sigB 107 = true ∧
    ∀ b : Bool, steerExc b 101 = K3.ofBool b ∧ steerExc b 105 = K3.ofBool b ∧
      steerExc b 109 = K3.ofBool b ∧ steerExc b 100 = K3.ofBool (!b) ∧
      steerExc b 104 = K3.ofBool (!b) ∧ steerExc b 108 = K3.ofBool (!b) := by
  refine ⟨by decide +kernel, by decide +kernel, by decide +kernel, ?_⟩
  intro b
  cases b
  · decide +kernel
  · decide +kernel

/-! ## From power-up -/

/-- **Reset, release and first wave, composed (GMW).** Every bounded run,
from ANY power-up state, with rst held 1 on `(0, S]`
(`S ≥ 23(D+W+1) + W`), anything on `(S, F]`, 0 on `(F, E]`, data arbitrary,
and no loop-entry steer moved before `E`: `sA` covers the run on `[S, E]`,
and `sB m` on `[F + m(D+W+1), E]`. -/
theorem gcd_boot {v : Nat → Nat → Bool} (Rn : Run gNet v) {D W : Nat}
    (hB : Bounded gNet v Rn D W) (S F E : Nat) (hSF : S ≤ F)
    (H_RST_HELD : ∀ k, 0 < k → k ≤ S → TernaryPhases.InputsIn gNet v gA k)
    (H_HOLD_LONG : (maxRank + 2) * (D + W + 1) + W ≤ S)
    (H_RST_LOW : ∀ k, F < k → k ≤ E → v k 0 = false)
    (H_STEER_HOLD : ∀ k z, z ∈ zL → S < k → k ≤ E → v k z = false) :
    (∀ k, S ≤ k + W → k ≤ E → covers sA (v k)) ∧
    (∀ m k, F + m * (D + W + 1) ≤ k → k ≤ E → covers (sB m) (v k)) :=
  gcd_first_wave Rn hB S F E hSF
    (fun k n h1 h2 hc _ => gcd_reset_binary Rn hB S H_RST_HELD n hc k (by omega) h1)
    H_RST_LOW H_STEER_HOLD

/-- At the first loop request, if rst was final `W` steps before it
(`H_RST_BEFORE_LOOP`), every rst pin of every cell reads 0. -/
theorem rst_reads_low {v : Nat → Nat → Bool} (Rn : Run gNet v) {D W : Nat}
    (hB : Bounded gNet v Rn D W) (F E : Nat)
    (H_RST_LOW : ∀ k, F < k → k ≤ E → v k 0 = false) :
    ∀ k j p, F + W < k → k ≤ E → v (Rn.rd k j p) 0 = false := by
  intro k j p h1 h2
  have := hB.wire k j p
  have := Rn.rd_le k j p
  exact H_RST_LOW _ (by omega) (by omega)

/-! ## The loop cannot be requested early: a causal chain of 34 LUTs -/

/-- **Hold through one gate.** If gate `n`'s LUT is `b` whenever its pins
reading `n` see `b` and its pins reading `m` see `c` (everything else `x`),
`n` is `b` on `[k0 - W, k0]` and `m` is `c` on `[k0 - W, T]`, then `n` is
still `b` at `T + 1`: it cannot move before one step after `m` does. -/
theorem hold_one {N : Circ} {v : Nat → Nat → Bool} (R : Run N v) {W : Nat}
    (hw : ∀ k j p, k ≤ R.rd k j p + W) {n m init : Nat} {pins : List Src}
    (hn : N.node n = .gate init pins) (c b : Bool)
    (hchk : lutK init (pins.map (srcK (fun i => if i = n then K3.ofBool b
      else if i = m then K3.ofBool c else .x))) = K3.ofBool b)
    (k0 T : Nat) (hm : ∀ j, k0 ≤ j + W → j ≤ T → v j m = c)
    (hn0 : ∀ j, k0 ≤ j + W → j ≤ k0 → v j n = b) :
    ∀ j, k0 ≤ j + W → j ≤ T + 1 → v j n = b := by
  intro j
  induction j using Nat.strongRecOn with
  | _ j ih =>
    intro h1 h2
    by_cases hj : j ≤ k0
    · exact hn0 j h1 hj
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rcases R.gate j' n init pins hn with h | h
    · rw [h]; exact ih j' (by omega) (by omega) (by omega)
    · rw [h]
      have hs := lutK_sound init (pins_forall2 (fun i => if i = n then K3.ofBool b
        else if i = m then K3.ofBool c else .x) (fun p i => v (R.rd j' n p) i) ?_ pins 0)
      · rw [hchk] at hs; exact (admits_ofBool_iff _ _).1 hs
      intro q i
      have r1 := R.rd_le j' n q
      have r2 := hw j' n q
      by_cases hi : i = n
      · subst hi; rw [ite_eq_left rfl, ih _ (by omega) (by omega) (by omega)]
        exact admits_ofBool _
      · rw [ite_eq_right hi]
        by_cases hm' : i = m
        · subst hm'; rw [ite_eq_left rfl, hm _ (by omega) (by omega)]; exact admits_ofBool _
        · rw [ite_eq_right hm']; rfl

/-- A chain `ns` of gates, each held at 0 by the previous one (the first by
`m` at level `c`); checked on `gNet`'s real LUTs. -/
def chainOK : Nat → Bool → List Nat → Bool
  | _, _, [] => true
  | m, c, n :: ns =>
    (match gNode n with
     | .gate init pins => decide (lutK init (pins.map (srcK (fun i => if i = n then K3.f
         else if i = m then K3.ofBool c else .x))) = K3.f)
     | .input => false) && chainOK n false ns

theorem chain_hold {v : Nat → Nat → Bool} (R : Run gNet v) {W : Nat}
    (hw : ∀ k j p, k ≤ R.rd k j p + W) (k0 : Nat) :
    ∀ (ns : List Nat) (m : Nat) (c : Bool) (T : Nat), chainOK m c ns = true →
      (∀ j, k0 ≤ j + W → j ≤ T → v j m = c) →
      (∀ n ∈ ns, ∀ j, k0 ≤ j + W → j ≤ k0 → v j n = false) →
      ∀ i n, ns[i]? = some n → ∀ j, k0 ≤ j + W → j ≤ T + i + 1 → v j n = false := by
  intro ns
  induction ns with
  | nil => intro _ _ _ _ _ _ i n h; simp at h
  | cons a ns ih =>
    intro m c T hok hm hinit
    simp only [chainOK, Bool.and_eq_true] at hok
    have ha : ∀ j, k0 ≤ j + W → j ≤ T + 1 → v j a = false := by
      cases hna : gNode a with
      | input => rw [hna] at hok; exact absurd hok.1 (by simp)
      | gate init pins =>
        rw [hna] at hok
        have hchk := of_decide_eq_true hok.1
        exact hold_one R hw (n := a) (m := m) hna c false hchk k0 T hm
          (hinit a (List.mem_cons_self ..))
    intro i n hi
    cases i with
    | zero =>
      simp only [List.getElem?_cons_zero, Option.some.injEq] at hi
      subst hi; intro j h1 h2; exact ha j h1 (by omega)
    | succ i =>
      simp only [List.getElem?_cons_succ] at hi
      intro j h1 h2
      exact ih a false (T + 1) hok.2 ha (fun n hn => hinit n (List.mem_cons_of_mem _ hn)) i n hi
        j h1 (by omega)

/-- The release path into the loop: `ulink_n1__1`, `ucmpi0.uor`, the 30
elements of `ucmpi0`'s matched delay (`g[1..29]` gated by the link), the
three steer joins, and the steer outputs. -/
def basePath : List Nat := [1696, 67] ++ List.range' 68 30
def steerPaths : List (List Nat) :=
  [basePath ++ [99, 100], basePath ++ [99, 101], basePath ++ [103, 104],
   basePath ++ [103, 105], basePath ++ [107, 108], basePath ++ [107, 109]]

theorem steerPaths_ok : steerPaths.all (fun ns => chainOK 0 true ns &&
    ns.all (fun n => gCtl n && !gR n && n != 0) && ns.length == 34 &&
    ns.getLast? != none && zL.contains (ns.getD 33 0)) = true ∧
    steerPaths.map (fun ns => ns.getD 33 0) = zL := by
  decide +kernel

/-- **The loop is not requested before 34 steps after rst is last 1.** In a
run with wires at most `W` old, if the control nodes are at reset on
`[S - W, S]` and the rst source is 1 on `[S - W, T]`, then no loop-entry
steer leaves 0 before `T + 35`: the request has to cross 34 LUTs
(`ulink_n1__1`, `ucmpi0.uor`, the 30-element matched delay, a join, the
steer), each at least one step. -/
theorem gcd_loop_late {v : Nat → Nat → Bool} (Rn : Run gNet v) {W : Nat}
    (H_WIRE_BOUND : ∀ k j p, k ≤ Rn.rd k j p + W) (S T : Nat)
    (H_SETTLED : ∀ k n, k ≤ S → S ≤ k + W → gCtl n = true → n ≠ 0 → v k n = gR n)
    (H_RST_HIGH : ∀ j, S ≤ j + W → j ≤ T → v j 0 = true) :
    ∀ z ∈ zL, ∀ j, S ≤ j + W → j ≤ T + 34 → v j z = false := by
  intro z hz j h1 h2
  have hok := steerPaths_ok
  have hmem : ∃ ns ∈ steerPaths, ns.getD 33 0 = z := by
    rw [← hok.2] at hz
    simpa using hz
  obtain ⟨ns, hns, hzs⟩ := hmem
  have hc := List.all_eq_true.1 hok.1 ns hns
  simp only [Bool.and_eq_true, beq_iff_eq] at hc
  obtain ⟨⟨⟨⟨hch, hall⟩, hlen⟩, _⟩, _⟩ := hc
  have hinit : ∀ n ∈ ns, ∀ j, S ≤ j + W → j ≤ S → v j n = false := by
    intro n hn j h1 h2
    have := List.all_eq_true.1 hall n hn
    simp only [Bool.and_eq_true, Bool.not_eq_true', bne_iff_ne, ne_eq] at this
    rw [H_SETTLED j n h2 h1 this.1.1 this.2, this.1.2]
  have h33 : ns[33]? = some z := by
    rw [← hzs, List.getD_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
    rfl
  exact chain_hold Rn H_WIRE_BOUND S ns 0 true T hch H_RST_HIGH hinit 33 z h33 j h1 (by omega)

/-- **Clean release, end to end.** Every bounded run from ANY power-up state
with a clean rst (1 on `(0, F]`, 0 on `(F, E]`, `F ≥ 23(D+W+1) + W`), data
arbitrary, and `E` before the first loop request: the wave covers hold
(`sA` on `[F, E]`, `sB m` on `[F + m(D+W+1), E]`), and that first request
comes after `F + 34`, so `H_STEER_HOLD` needs no assumption up to there.
If moreover `W < 34` (every rst pin's wire is shorter than 34 minimum
gate steps), every rst pin reads 0 at the first loop request
(`rst_reads_low` at any `k ∈ (F + W, E]`). -/
theorem gcd_clean_release {v : Nat → Nat → Bool} (Rn : Run gNet v) {D W : Nat}
    (hB : Bounded gNet v Rn D W) (F E : Nat)
    (H_RST_CLEAN : ∀ k, 0 < k → k ≤ F → TernaryPhases.InputsIn gNet v gA k)
    (H_HOLD_LONG : (maxRank + 2) * (D + W + 1) + W ≤ F)
    (H_RST_LOW : ∀ k, F < k → k ≤ E → v k 0 = false)
    (H_STEER_HOLD : ∀ k z, z ∈ zL → F + 34 < k → k ≤ E → v k z = false) :
    (∀ k, F ≤ k + W → k ≤ E → covers sA (v k)) ∧
    (∀ m k, F + m * (D + W + 1) ≤ k → k ≤ E → covers (sB m) (v k)) := by
  have hset : ∀ k n, k ≤ F → F ≤ k + W → gCtl n = true → n ≠ 0 → v k n = gR n :=
    fun k n h1 h2 hc _ => gcd_reset_binary Rn hB F H_RST_CLEAN n hc k (by omega) h1
  have hhigh : ∀ j, F ≤ j + W → j ≤ F → v j 0 = true := by
    intro j h1 h2
    have hpos : 0 < (maxRank + 2) * (D + W + 1) := Nat.mul_pos (by decide) (by omega)
    have := H_RST_CLEAN j (by omega) h2 0 (by show gNode 0 = .input; rfl)
    exact (admits_ofBool_iff true _).1 this
  have hlate := gcd_loop_late Rn hB.wire F F hset hhigh
  apply gcd_boot Rn hB F F E (Nat.le_refl F) H_RST_CLEAN H_HOLD_LONG H_RST_LOW
  intro k z hz h1 h2
  by_cases hk : k ≤ F + 34
  · exact hlate z hz k (by omega) hk
  · exact H_STEER_HOLD k z hz (by omega) h2

/-! ## Negative controls -/

/-- Without the cut, phase A is not closed: in `gNet`, steer `ucond_br9`'s
O6 is excited to `x` in `sA` (its request is `x` during the window), while
`sA` holds it at 0. -/
theorem neg_nocut : stepK gNet uW sA 101 = .x ∧ sA 101 = .f := by decide +kernel

/-- One B phase too early, `ucond_br9_j` is not yet definite: rank 33
instead of 34 would fail the certificate check. -/
theorem neg_rank : stepK gCut aF (sB 32) 99 = .x := by decide +kernel

/-- The chain check can fail: rst at 0 does not hold `ulink_n1__1`, and
`g[0]` is not held by the link directly (it reads only `ucmpi0.uor`). -/
theorem neg_chain : chainOK 0 false (basePath ++ [99, 101]) = false ∧
    chainOK 0 true ([1696] ++ List.range' 68 30 ++ [99, 101]) = false := by
  decide +kernel

end Formal.Cells.ResetGcdWave
