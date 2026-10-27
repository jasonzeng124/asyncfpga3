import Formal.Cells.ResetContract

/-!
# Probe Rig (shard B, gcd_hw capstone): the rig's own obligations

Notes: `formal/notes/B-rig-contract.md`.

The clocked harness of `cells/hw/gcd_hw.v` around `cells/hw/gcd_rig.v`:
the housekeeping (hk) window sequencer (`win_cnt`, `win_edge_d`, `rst_sr`,
`idx`, `settle_sr`, `por_sr`, `settled`, `armed`) and the boundary it shares
with the asynchronous kernel (the operand vector `vector(idx)`, the rig reset
`rig_rst`, the frontier link controller, the per-vector sticky LUT latches).

## Model

* **Clocked part, cycle level** (`St`, `step`, `run`): every hk register of the
  sequencer, bit for bit as written in `gcd_hw.v` (16-bit `win_cnt`, the shift
  registers as bit functions with the RTL's shift-in values and load values).
  `run n` is the register state after `n` hk edges from configuration.
  `hold_pin`/`hold_vec` are constants (`pin`, `vec`); `arm_sr[31]` is the
  constant `armG` (it is 1 from the 32nd window edge on and never falls).
  Flops are ideal edge-triggered elements: the hk domain is one BUFG clock, so
  setup/hold between hk flops is a static-timing fact, `H_HK_STA` (named, not
  used as a Lean hypothesis: the cycle model IS that assumption).
* **Timed boundary** (`PathOK`): a combinational path from hk flops to a pin
  in the asynchronous part carries the cycle value `v n` on the stable band
  `[e n + hi, e (n+1) + lo)` and, when `v (n+1) = v n`, also through the
  transition band (`H_NOGLITCH_STEADY`). `e n` is the time of hk edge `n`
  (`H_HK_PERIOD`: `e n + Tlo ≤ e (n+1)`).
* **Frontier link controller**: `ResetContract.c2n_frontier` (window-channel
  loop of the real `bd_c2n` INIT), used as is.
* **Sticky latch**: the real INIT `16'hEC00` of `uerr_s`/`uok_s`/... with
  pins `[raw, q, armed, sticky_keep]`, binary (`lutB`) and Kleene (`lutK`).

## Results

1. `armed_phase`, `armed_iff`, `armedOld_iff`, `idx_const`, `idx_moves`,
   `rr_window`: the closed forms of the sequencer. With `p = n mod 65536`:
   `idx` moves only at `p = 1`; `rig_rst` is high exactly for `p ∈ [1,16]`;
   `armed` (current RTL) is high exactly for `p ≥ 2048`; WITHOUT the
   `settled` term (`armedOld`) it is high for `p ∈ {0,1} ∪ [33, 65535]`,
   i.e. it is still OPEN in the hk cycle in which idx has just moved.
2. `idx_setup` (constraint `gcd_rig.idx_setup`): composes the sequencer with
   `c2n_frontier`: if `vhi + su ≤ 16·Tlo + rlo + dlmin + enlo`, the operands
   are stable `su` before any latch-enable edge derived from the frontier
   controller, and stay stable until `e(n0+65536) + vlo`.
3. `verdict_current`: in the current RTL, at every instant at which the arm
   pin of a sticky is not a definite 0, the window's operands are stable at
   the readers and the instant is at least 2047 hk periods after idx moved,
   given `H_ARM_BEFORE_IDX : ahi ≤ Tlo + vlo`. `verdict_attrib` adds the
   kernel-side fact as the named hypothesis `H_RESULT_FRESH`.
4. `stale_counter`: the counter-run for the RTL without `settled`: in the hk
   cycle after the edge that sets `win_cnt := 1`, the arm pin is 1 and the
   operands/expected/`sel` are the NEW vector's; with the real LUT INITs a
   result for the OLD vector still on `res_req` sets `err` on the new vector
   for every sweep transition whose expected gcds differ (13 of 16;
   `stale_err_vectors`). The same instant in the current RTL has arm = 0 and
   the sticky holds (`sticky_holds_K`).

Core Lean only.
-/

namespace Formal.Cells.RigContract
open Formal.Cells

/-! ## 0. The vector table and the reference -/

/-- `gcd_rig.v` `vector(i)`, as `(a, b, expected)`. In the RTL the word is
`{expected, b, a}` (`a_v = vec[31:0]`, `b_v = vec[63:32]`, `g_v = vec[95:64]`). -/
def table : List (Nat × Nat × Nat) :=
  [ (0x00000000, 0x00000005, 0x00000005),
    (0x00000007, 0x00000000, 0x00000007),
    (0x0000000C, 0x00000012, 0x00000006),
    (0x00000030, 0x00000012, 0x00000006),
    (0x00000001, 0x00000001, 0x00000001),
    (0x00000011, 0x00000005, 0x00000001),
    (0x00798F20, 0x12B87CA0, 0x00000020),
    (0x0000042F, 0x000001CE, 0x00000015),
    (0x0000010E, 0x000000C0, 0x00000006),
    (0x00010000, 0x00001000, 0x00001000),
    (0x00018697, 0x00018697, 0x00018697),
    (0x0001E240, 0x000C0A14, 0x0000000C),
    (0x7FFFFFFF, 0x00000002, 0x00000001),
    (0x000F4240, 0x000F423F, 0x00000001),
    (0x00000024, 0x0000003C, 0x0000000C),
    (0x00000400, 0x00000300, 0x00000100) ]

def vA (i : Nat) : Nat := ((table.getD i (0, 0, 0)).1)
def vB (i : Nat) : Nat := ((table.getD i (0, 0, 0)).2.1)
def vG (i : Nat) : Nat := ((table.getD i (0, 0, 0)).2.2)

/-- Strip trailing zeros (`ctz_shift` of `bdc/simcheck.py`'s `ref_gcd`,
a transcription of Dynamatic's `gcd.c`, Stein's algorithm). `fuel` bounds the
loop. -/
def ctzShift : Nat → Nat → Nat
  | 0, x => x
  | f + 1, x => if x ≠ 0 ∧ x % 2 = 0 then ctzShift f (x / 2) else x

/-- `while ((a|b)&1)==0 { a>>=1; b>>=1; k++ }`. -/
def pow2Out : Nat → Nat → Nat → Nat → Nat × Nat × Nat
  | 0, a, b, k => (a, b, k)
  | f + 1, a, b, k => if a % 2 = 0 ∧ b % 2 = 0 then pow2Out f (a / 2) (b / 2) (k + 1) else (a, b, k)

/-- `while (a != 0) { diff = a - b; if (a < b) b = a; a = |diff|; a = ctz_shift(a) }`. -/
def subLoop : Nat → Nat → Nat → Nat
  | 0, _, b => b
  | f + 1, a, b =>
    if a = 0 then b
    else
      let b' := if a < b then a else b
      let d := if a < b then b - a else a - b
      subLoop f (ctzShift 64 d) b'

/-- The C reference, for operands in `[0, 2^31)` (all sixteen are). -/
def stein (a b : Nat) : Nat :=
  if a = 0 then b else if b = 0 then a else
  let (a1, b1, k) := pow2Out 64 a b 0
  subLoop 200 (ctzShift 64 a1) (ctzShift 64 b1) * 2 ^ k

/-- **The table's expected values are the C reference's answers** (and Lean's
`Nat.gcd`'s). Independent of the RTL comment that says so. -/
theorem table_ok : (List.range 16).all (fun i => stein (vA i) (vB i) == vG i &&
    Nat.gcd (vA i) (vB i) == vG i && decide (vA i < 2 ^ 31) && decide (vB i < 2 ^ 31)) = true := by
  decide +kernel

/-! ## 1. The clocked sequencer, bit for bit -/

/-- The hk registers of `gcd_hw.v`'s window sequencer. Shift registers are bit
functions (`bit i` = `reg[i]`, only `i < width` is ever read). -/
structure St where
  /-- `win_cnt[15:0]`. -/
  wc : Nat
  /-- `win_edge_d`. -/
  wed : Bool
  /-- `rst_sr[15:0]`. -/
  rst : Nat → Bool
  /-- `idx[3:0]`. -/
  idx : Nat
  /-- `settle_sr[15:0]`. -/
  settle : Nat → Bool
  /-- `por_sr[23:0]`. -/
  por : Nat → Bool

/-- Configuration values (`= ...` initialisers, global set/reset). -/
def init : St where
  wc := 0
  wed := false
  rst := fun i => decide (i < 16)
  idx := 0
  settle := fun _ => false
  por := fun _ => false

/-- `wire rig_rst = ~por_done | rst_sr[15]` with `por_done = por_sr[23]`. -/
def rigRst (s : St) : Bool := !(s.por 23) || s.rst 15

/-- One hk edge. Every line is the RTL's `always @(posedge hk_ck)`:
* `win_cnt <= win_cnt + 1`, `win_edge_d <= &win_cnt`;
* `rst_sr <= win_edge_d ? 16'hFFFF : {rst_sr[14:0], 1'b0}`;
* `if (win_edge_d) idx <= hold_pin ? hold_vec : idx + 1`;
* `settle_sr <= rig_rst ? 0 : {settle_sr[14:0], 1'b1}`;
* `por_sr <= {por_sr[22:0], 1'b1}`. -/
def step (pin : Bool) (vec : Nat) (s : St) : St where
  wc := (s.wc + 1) % 65536
  wed := decide (s.wc = 65535)
  rst := fun i => if s.wed then decide (i < 16) else (decide (i ≠ 0) && s.rst (i - 1))
  idx := if s.wed then (if pin then vec % 16 else (s.idx + 1) % 16) else s.idx
  settle := fun i => if rigRst s then false else (decide (i = 0) || s.settle (i - 1))
  por := fun i => decide (i = 0) || s.por (i - 1)

/-- Register state after `n` hk edges. -/
def run (pin : Bool) (vec : Nat) : Nat → St
  | 0 => init
  | n + 1 => step pin vec (run pin vec n)

/-- `wire settled = |win_cnt[15:11]`. -/
def settledB (s : St) : Bool := decide (s.wc / 2048 % 32 ≠ 0)

/-- `wire armed = arm_sr[31] & settle_sr[15] & settled` (current RTL). -/
def armed (armG : Bool) (s : St) : Bool := armG && s.settle 15 && settledB s

/-- `armed` WITHOUT the `settled` term: the RTL the `gcd_hw.v` comment says
was measured to give the ok+err pairs (`arm_sr[31] & settle_sr[15]`). -/
def armedOld (armG : Bool) (s : St) : Bool := armG && s.settle 15

section clocked
variable {pin : Bool} {vec : Nat}

theorem wc_run (n : Nat) : (run pin vec n).wc = n % 65536 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [run, step, ih]; omega

theorem wed_run (n : Nat) : (run pin vec n).wed = true ↔ 65536 ≤ n ∧ n % 65536 = 0 := by
  cases n with
  | zero => simp [run, init]
  | succ n => simp only [run, step, wc_run, decide_eq_true_eq]; omega

theorem por_run (n i : Nat) : (run pin vec n).por i = true ↔ i < n := by
  induction n generalizing i with
  | zero => simp [run, init]
  | succ n ih =>
    cases i with
    | zero => simp [run, step]
    | succ i => simp only [run, step, Bool.or_eq_true, decide_eq_true_eq, Nat.add_sub_cancel]
                rw [ih i]; omega

/-- Shifts of `rst_sr` since its last load (configuration counts as a load of
`16'hFFFF` at edge 0). -/
def jR (n : Nat) : Nat := if n ≤ 65536 then n else (n - 1) % 65536

theorem rst_run (n i : Nat) (hi : i < 16) : (run pin vec n).rst i = true ↔ jR n ≤ i := by
  induction n generalizing i with
  | zero => simp [run, init, jR, hi]
  | succ n ih =>
    have hw := @wed_run pin vec n
    by_cases h : (run pin vec n).wed = true
    · have h' := hw.1 h
      simp only [run, step, h, ite_true, decide_eq_true_eq, hi, true_iff]
      unfold jR; split <;> omega
    · have h' : ¬(65536 ≤ n ∧ n % 65536 = 0) := fun c => h (hw.2 c)
      simp only [run, step, h, Bool.false_eq_true, ite_false, Bool.and_eq_true, decide_eq_true_eq]
      cases i with
      | zero => simp only [Nat.zero_sub, ne_eq, not_true_eq_false, false_and, false_iff]
                unfold jR; split <;> omega
      | succ i =>
        simp only [ne_eq, Nat.add_one_ne_zero, not_false_eq_true, Nat.add_sub_cancel, true_and]
        rw [ih i (by omega)]
        unfold jR; split <;> split <;> omega

theorem settle_run (n i : Nat) : (run pin vec n).settle i = true ↔
    i + 1 ≤ n ∧ ∀ m, n ≤ m + i + 1 → m < n → rigRst (run pin vec m) = false := by
  induction n generalizing i with
  | zero => simp [run, init]
  | succ n ih =>
    by_cases hr : rigRst (run pin vec n) = true
    · simp only [run, step, hr, ite_true, Bool.false_eq_true, false_iff, not_and]
      intro _ hall
      have := hall n (by omega) (by omega)
      rw [hr] at this; exact Bool.noConfusion this
    · have hr' : rigRst (run pin vec n) = false := by simpa using hr
      simp only [run, step, hr', Bool.false_eq_true, ite_false, Bool.or_eq_true, decide_eq_true_eq]
      cases i with
      | zero =>
        simp only [true_or, true_iff]
        refine ⟨by omega, fun m h1 h2 => ?_⟩
        have : m = n := by omega
        subst this; exact hr'
      | succ i =>
        simp only [Nat.add_one_ne_zero, false_or, Nat.add_sub_cancel]
        rw [ih i]
        constructor
        · rintro ⟨h1, h2⟩
          refine ⟨by omega, fun m hm1 hm2 => ?_⟩
          by_cases hmn : m = n
          · subst hmn; exact hr'
          · exact h2 m (by omega) (by omega)
        · rintro ⟨h1, h2⟩
          exact ⟨by omega, fun m hm1 hm2 => h2 m (by omega) (by omega)⟩

/-- `rig_rst` in steady state (after the first window edge): high exactly
for `(n-1) mod 65536 ≤ 15`, i.e. phase `p = n mod 65536 ∈ [1, 16]`. -/
theorem rr_steady (n : Nat) (h : 65537 ≤ n) :
    rigRst (run pin vec n) = true ↔ (n - 1) % 65536 ≤ 15 := by
  have hp : (run pin vec n).por 23 = true := (por_run n 23).2 (by omega)
  have hj : jR n = (n - 1) % 65536 := by unfold jR; split <;> omega
  simp only [rigRst, hp, Bool.not_true, Bool.false_or]
  rw [rst_run n 15 (by omega), hj]

theorem idx_run (n : Nat) : (run pin vec n).idx =
    if pin then (if 65537 ≤ n then vec % 16 else 0) else ((n - 1) / 65536) % 16 := by
  induction n with
  | zero => cases pin <;> rfl
  | succ n ih =>
    have hw := @wed_run pin vec n
    by_cases h : (run pin vec n).wed = true
    · have h' := hw.1 h
      simp only [run, step, h, ite_true]
      rw [ih]; cases pin <;> simp <;> omega
    · have h' : ¬(65536 ≤ n ∧ n % 65536 = 0) := fun c => h (hw.2 c)
      simp only [run, step, h, Bool.false_eq_true, ite_false]
      rw [ih]; cases pin
      · simp only [Bool.false_eq_true, ite_false]; omega
      · simp only [ite_true]
        by_cases h1 : 65537 ≤ n
        · rw [if_pos h1, if_pos (by omega)]
        · rw [if_neg h1, if_neg (by omega)]

/-- A load edge: the edge at which `win_edge_d = 1` is sampled, i.e. the edge
that sets `win_cnt := 1` (phase 1), after the first window. -/
def Load (n0 : Nat) : Prop := 65537 ≤ n0 ∧ n0 % 65536 = 1

/-- **idx is constant for a whole window**: from the load edge `n0` through
`n0 + 65535`. -/
theorem idx_const {n0 : Nat} (hL : Load n0) (m : Nat) (h1 : n0 ≤ m) (h2 : m < n0 + 65536) :
    (run pin vec m).idx = (run pin vec n0).idx := by
  rw [idx_run, idx_run]; unfold Load at hL
  cases pin
  · simp only [Bool.false_eq_true, ite_false]
    have : (m - 1) / 65536 = (n0 - 1) / 65536 := by omega
    rw [this]
  · simp only [ite_true]; rw [if_pos (by omega), if_pos (by omega)]

/-- **idx moves at every load edge** when not pinned. -/
theorem idx_moves {n0 : Nat} (hL : Load n0) :
    (run false vec n0).idx ≠ (run false vec (n0 - 1)).idx := by
  rw [idx_run, idx_run]; unfold Load at hL
  simp only [Bool.false_eq_true, ite_false]; omega

/-- **rig_rst over one window**: high on edges `[n0, n0+15]`, low on
`[n0+16, n0+65535]` (16 hk cycles of reset). -/
theorem rr_window {n0 : Nat} (hL : Load n0) (m : Nat) (h1 : n0 ≤ m) (h2 : m < n0 + 65536) :
    rigRst (run pin vec m) = true ↔ m ≤ n0 + 15 := by
  unfold Load at hL
  rw [rr_steady m (by omega)]; omega

/-- **`armed` (current RTL) is closed outside phase `≥ 2048`** — for every
`n`, from configuration, whatever `arm_sr` and `settle_sr` hold. -/
theorem armed_phase {armG : Bool} (n : Nat) (h : armed armG (run pin vec n) = true) :
    2048 ≤ n % 65536 := by
  simp only [armed, settledB, Bool.and_eq_true, decide_eq_true_eq] at h
  have := h.2; rw [wc_run] at this; omega

/-- `settle_sr[15]` in steady state, as a phase condition. -/
theorem settle15_steady (n : Nat) (h : 131072 ≤ n) :
    (run pin vec n).settle 15 = true ↔ (n % 65536 ≤ 1 ∨ 33 ≤ n % 65536) := by
  rw [settle_run]
  constructor
  · rintro ⟨_, hall⟩
    by_cases hc : n % 65536 ≤ 1 ∨ 33 ≤ n % 65536
    · exact hc
    · exfalso
      by_cases h17 : n % 65536 ≤ 17
      · have := hall (n - 1) (by omega) (by omega)
        rw [← Bool.not_eq_true, rr_steady _ (by omega)] at this; omega
      · have := hall (n - 16) (by omega) (by omega)
        rw [← Bool.not_eq_true, rr_steady _ (by omega)] at this; omega
  · intro hc
    refine ⟨by omega, fun m h1 h2 => ?_⟩
    rw [← Bool.not_eq_true, rr_steady _ (by omega)]; omega

/-- **Non-vacuity: `armed` is open for `p ≥ 2048`** (63488 of 65536 cycles). -/
theorem armed_iff {n : Nat} (h : 131072 ≤ n) :
    armed true (run pin vec n) = true ↔ 2048 ≤ n % 65536 := by
  simp only [armed, settledB, Bool.true_and, Bool.and_eq_true, decide_eq_true_eq, wc_run]
  rw [settle15_steady n h]; omega

/-- **Without `settled`, the arm is open for `p ∈ {0,1} ∪ [33, 65535]`**: it is
open at `p = 1`, the hk cycle right after the edge that moves idx. -/
theorem armedOld_iff {n : Nat} (h : 131072 ≤ n) :
    armedOld true (run pin vec n) = true ↔ (n % 65536 ≤ 1 ∨ 33 ≤ n % 65536) := by
  simp only [armedOld, Bool.true_and]; exact settle15_steady n h

end clocked

/-! ## 2. The timed boundary between the hk domain and the asynchronous part -/

/-- **H_PATH(lo, hi) and H_NOGLITCH_STEADY.** A combinational path from hk
flops (clock-to-out + LUTs + route) to a pin of the asynchronous part shows the
cycle value `v n` on the stable band `[e n + hi, e (n+1) + lo)`; if the cycle
value does not change at edge `n+1`, it also shows it through the transition
band `[e (n+1) + lo, e (n+1) + hi)` (no hazard on a path whose logical value
holds). `lo`/`hi` are the path's min/max delay from the clock edge (prjxray
FAST_MIN / SLOW_MAX of tCO + LUT arcs + route). Test: GLS of the routed
gcd_hw at both corners with the hk BUFG clock; for the hazard clause, an X/edge
scan of the path's LUTs under the RTL's actual input changes (for `armed`:
`settled` is constant 0 across `p ∈ [0, 2047]` and the `win_cnt[15:11]` OR
is monotone at its two real transitions). -/
def PathOK {α : Type} (e : Nat → Nat) (lo hi : Nat) (v : Nat → α) (s : Nat → α) : Prop :=
  (∀ n t, e n + hi ≤ t → t < e (n + 1) + lo → s t = v n) ∧
  (∀ n t, v (n + 1) = v n → e (n + 1) + lo ≤ t → t < e (n + 1) + hi → s t = v n)

/-- A path whose cycle value is constant on edges `[n1, n1 + k]` shows it on
`[e n1 + hi, e N + lo)` with `N = n1 + k + 1`. -/
theorem path_const {α : Type} {e : Nat → Nat} {lo hi : Nat} {v s : Nat → α}
    (P : PathOK e lo hi v s) (c : α) (n1 k N : Nat) (hN : n1 + k + 1 = N)
    (hv' : ∀ m, n1 ≤ m → m < N → v m = c) :
    ∀ t, e n1 + hi ≤ t → t < e N + lo → s t = c := by
  subst hN
  have hv : ∀ m, n1 ≤ m → m ≤ n1 + k → v m = c := fun m a b => hv' m a (by omega)
  clear hv'
  induction k with
  | zero =>
    intro t h1 h2
    rw [P.1 n1 t h1 (by simpa using h2)]; exact hv n1 (by omega) (by omega)
  | succ k ih =>
    intro t h1 h2
    have e1 : n1 + (k + 1) + 1 = (n1 + k + 1) + 1 := by omega
    rw [e1] at h2
    by_cases ha : t < e (n1 + k + 1) + lo
    · exact ih (fun m a b => hv m a (by omega)) t h1 ha
    · by_cases hb : t < e (n1 + k + 1) + hi
      · have hv1 := hv (n1 + k + 1) (by omega) (by omega)
        have hv0 := hv (n1 + k) (by omega) (by omega)
        rw [P.2 (n1 + k) t (by rw [hv1, hv0]) (by omega) hb]; exact hv0
      · rw [P.1 (n1 + k + 1) t (by omega) h2]; exact hv _ (by omega) (by omega)

/-- **H_HK_PERIOD** iterated: `k` hk periods last at least `k · Tlo`. -/
theorem e_mono {e : Nat → Nat} {Tlo : Nat} (H_HK : ∀ n, e n + Tlo ≤ e (n + 1)) :
    ∀ n k, e n + k * Tlo ≤ e (n + k) := by
  intro n k
  induction k with
  | zero => simp
  | succ k ih =>
    have := H_HK (n + k)
    rw [Nat.succ_mul, ← Nat.add_assoc n k 1]; omega

/-- `e_mono` with the end index named (so that no arithmetic on indices is
left to definitional unfolding). -/
theorem e_le {e : Nat → Nat} {Tlo : Nat} (H_HK : ∀ n, e n + Tlo ≤ e (n + 1))
    (n k m : Nat) (h : n + k = m) : e n + k * Tlo ≤ e m := by
  subst h; exact e_mono H_HK n k

section timed
variable {pin : Bool} {vec : Nat} {armG : Bool} {e : Nat → Nat} {Tlo : Nat}

/-- **The arm closes before idx moves (current RTL).** At every instant `t` of
window `n0`'s tile `[e(n0-1) + ahi, e(n0+65535) + ahi)` at which a sticky's
arm pin is NOT a definite 0 (so it is 1 or intermediate and the sticky may
set), the instant is at least 2047 hk periods after the edge that moved idx,
and the readers of idx (operands, expected value, `sel`) show the window's
idx. Hypotheses: `H_HK_PERIOD`; the arm path and the idx paths as `PathOK`;
`H_ARM_BEFORE_IDX : ahi ≤ Tlo + vlo` (the arm path's max delay is less than
one hk period plus the idx paths' min delay; margin about one hk period) and
`H_VEC_EARLY : vhi ≤ 2047·Tlo + alo` (trivial). -/
theorem verdict_current {alo ahi vlo vhi : Nat} {armP : Nat → K3} {idxP : Nat → Nat}
    (H_HK : ∀ n, e n + Tlo ≤ e (n + 1))
    (P_arm : PathOK e alo ahi (fun n => K3.ofBool (armed armG (run pin vec n))) armP)
    (P_idx : PathOK e vlo vhi (fun n => (run pin vec n).idx) idxP)
    (H_ARM_BEFORE_IDX : ahi ≤ Tlo + vlo)
    (H_VEC_EARLY : vhi ≤ 2047 * Tlo + alo)
    {n0 : Nat} (hL : Load n0) (t : Nat)
    (h1 : e (n0 - 1) + ahi ≤ t) (h2 : t < e (n0 + 65535) + ahi)
    (hA : armP t ≠ K3.f) :
    e (n0 + 2047) + alo ≤ t ∧ idxP t = (run pin vec n0).idx := by
  have hL' := hL; unfold Load at hL'
  have hlo : e (n0 + 2047) + alo ≤ t := by
    refine Nat.le_of_not_lt (fun hlt => hA ?_)
    have hv : ∀ m, n0 - 1 ≤ m → m < n0 + 2047 →
        K3.ofBool (armed armG (run pin vec m)) = K3.ofBool false := by
      intro m a b
      cases hm : armed armG (run pin vec m)
      · rfl
      · have := armed_phase m hm; omega
    exact path_const P_arm _ (n0 - 1) 2047 (n0 + 2047) (by omega) hv t h1 hlt
  refine ⟨hlo, ?_⟩
  have m1 := e_le H_HK n0 2047 (n0 + 2047) rfl
  have m2 := e_le H_HK (n0 + 65535) 1 (n0 + 65536) (by omega)
  exact path_const P_idx _ n0 65535 (n0 + 65536) (by omega) (fun m a b => idx_const hL m a b) t
    (by omega) (by omega)

/-- **The verdict is about the current operands.** Adds the kernel-side fact
as a named hypothesis:

`H_RESULT_FRESH`: every result present at the compare (`resP t`, the padded
`res_req`) at an instant `t` of window `n0` at which the arm is open was
computed from operands the kernel read at some `s` with
`e(n0+16) + rlo ≤ s ≤ t`, i.e. after the window's reset released at the
kernel (`rlo`: min delay hk edge → rst at the kernel). This is the reset
contract (`ResetGcd.gcd_reset_binary`, `gcd_release_quiet`: 16 hk cycles of
rst leave no request in flight) plus the one-token ring; it is not derived
here. `out t = K (idxP s)`: what the compare sees is the kernel's answer to
the vector it read (whatever the kernel computes, right or wrong).

Conclusion: the value compared at `t` is the kernel's answer to the SAME
vector whose expected value and `sel` the compare uses at `t`. Needs
`H_IDX_BEFORE_RELEASE : vhi ≤ 16·Tlo + rlo`. -/
theorem verdict_attrib {alo ahi vlo vhi rlo : Nat} {armP : Nat → K3} {idxP : Nat → Nat}
    {resP : Nat → Bool} {out : Nat → Nat} (K : Nat → Nat)
    (H_HK : ∀ n, e n + Tlo ≤ e (n + 1))
    (P_arm : PathOK e alo ahi (fun n => K3.ofBool (armed armG (run pin vec n))) armP)
    (P_idx : PathOK e vlo vhi (fun n => (run pin vec n).idx) idxP)
    (H_ARM_BEFORE_IDX : ahi ≤ Tlo + vlo)
    (H_VEC_EARLY : vhi ≤ 2047 * Tlo + alo)
    (H_IDX_BEFORE_RELEASE : vhi ≤ 16 * Tlo + rlo)
    {n0 : Nat} (hL : Load n0)
    (H_RESULT_FRESH : ∀ t, e (n0 - 1) + ahi ≤ t → t < e (n0 + 65535) + ahi →
      armP t ≠ K3.f → resP t = true →
      ∃ s, e (n0 + 16) + rlo ≤ s ∧ s ≤ t ∧ out t = K (idxP s))
    (t : Nat) (h1 : e (n0 - 1) + ahi ≤ t) (h2 : t < e (n0 + 65535) + ahi)
    (hA : armP t ≠ K3.f) (hR : resP t = true) :
    out t = K (idxP t) ∧ idxP t = (run pin vec n0).idx := by
  have ⟨hlo, hidx⟩ := verdict_current H_HK P_arm P_idx H_ARM_BEFORE_IDX H_VEC_EARLY hL t h1 h2 hA
  obtain ⟨s, hs1, hs2, hout⟩ := H_RESULT_FRESH t h1 h2 hA hR
  have m1 := e_le H_HK n0 16 (n0 + 16) rfl
  have m2 := e_le H_HK (n0 + 65535) 1 (n0 + 65536) (by omega)
  have hsI : idxP s = (run pin vec n0).idx :=
    path_const P_idx _ n0 65535 (n0 + 65536) (by omega) (fun m a b => idx_const hL m a b) s
      (by omega) (by omega)
  exact ⟨by rw [hout, hsI, hidx], hidx⟩

/-- **`gcd_rig.idx_setup`, composed with the frontier controller.**

`F` is a frontier link controller (`bd_c2n`, real INIT, window-channel loop
`L`), e.g. `ulink_n1__1.ctl.u`, whose request carries the rig token through
reset (`H_TOKEN_STATIC` = constraint `gcd_rig.token_static`). `rstP` is rst at
F's pin, `PathOK` from `rig_rst` with `[rlo, rhi]`, falling ONCE inside its
band at `r` (`H_RST_ONE_FALL`: a single flop transition through a route).
`idxP` is the idx-derived operand word at F's latch `d` pins and at the
direct `a_data`/`b_data` readers, `PathOK` with `[vlo, vhi]`. `enlo` is the
min delay from F's output to the latch enable (`>= 0`), `su` the latch/reader
setup.

If `H_IDX_SETUP : vhi + su ≤ 16·Tlo + rlo + dlmin + enlo` then
(a) the operands are the window's vector on `[e n0 + vhi, e(n0+65536) + vlo)`;
(b) every instant `t` (after F's reset hold set in) at which F is high
satisfies `e n0 + vhi + su ≤ t + enlo`: no latch-enable edge derived from F
precedes the operands' settling by less than `su`;
(c) F does fire: it is high from `r + dlmax` to the window's end.
The hold side of `idx_setup` is (a) together with `verdict_current`: the
operands stay until `e(n0+65536) + vlo`, and no result read after that can
be judged (the arm is closed from `e(n0+65535) + ahi`). -/
theorem idx_setup {rlo rhi vlo vhi su enlo dlmin dlmax dwmin dwmax r : Nat}
    {aF bF rstP O qp : CElemTiming.Trace} {idxP : Nat → Nat}
    (L : CTreeTimed.LoopG (fun t q => CElemTiming.exc CElemTiming.INIT_c2n (aF t) (bF t) q (rstP t))
      O qp dlmin dlmax dwmin dwmax)
    (H_HK : ∀ n, e n + Tlo ≤ e (n + 1)) (H_HK_POS : 0 < Tlo)
    (P_rst : PathOK e rlo rhi (fun n => rigRst (run pin vec n)) rstP)
    (P_idx : PathOK e vlo vhi (fun n => (run pin vec n).idx) idxP)
    (H_BAND : rlo ≤ rhi)
    {n0 : Nat} (hL : Load n0)
    (H_RST_ONE_FALL : e (n0 + 16) + rlo ≤ r ∧ r ≤ e (n0 + 16) + rhi ∧
      (∀ t, e (n0 + 16) + rlo ≤ t → t < r → rstP t = true) ∧
      (∀ t, r ≤ t → t < e (n0 + 16) + rhi → rstP t = false))
    (H_TOKEN_STATIC : ∀ s, e n0 + rhi ≤ s → s < e (n0 + 65536) + rlo → aF s = true ∧ bF s = false)
    (H_RST_LONG : rhi + (dlmax + dwmax) ≤ 16 * Tlo + rlo)
    (H_IDX_SETUP : vhi + su ≤ 16 * Tlo + rlo + dlmin + enlo) :
    (∀ t, e n0 + vhi ≤ t → t < e (n0 + 65536) + vlo → idxP t = (run pin vec n0).idx) ∧
    (∀ t, e n0 + rhi + dlmax ≤ t → t + 1 ≤ e (n0 + 65536) + rlo + dlmin → O t = true →
      e n0 + vhi + su ≤ t + enlo) ∧
    (∀ t, r + dlmax ≤ t → t + 1 ≤ e (n0 + 65536) + rlo + dlmin → O t = true) := by
  have hL' := hL; unfold Load at hL'
  obtain ⟨hr1, hr2, hrHi, hrLo⟩ := H_RST_ONE_FALL
  have m16 := e_le H_HK n0 16 (n0 + 16) rfl
  have mW := e_le H_HK (n0 + 16) 65520 (n0 + 65536) (by omega)
  have m1 := e_le H_HK (n0 + 65535) 1 (n0 + 65536) (by omega)
  have hT : 16 * Tlo ≤ 65520 * Tlo := Nat.mul_le_mul_right _ (by omega)
  have hT1 : 1 ≤ 1 * Tlo := by omega
  -- rst high on [e n0 + rhi, r)
  have rstHi : ∀ s, e n0 + rhi ≤ s → s < r → rstP s = true := by
    intro s a b
    by_cases hs : s < e (n0 + 16) + rlo
    · exact path_const P_rst true n0 15 (n0 + 16) (by omega)
        (fun m x y => (rr_window hL m x (Nat.lt_of_lt_of_le y (by omega))).2 (by omega)) s a hs
    · exact hrHi s (by omega) b
  -- rst low on [r, e(n0+65536) + rlo)
  have rstLo : ∀ s, r ≤ s → s < e (n0 + 65536) + rlo → rstP s = false := by
    intro s a b
    by_cases hs : s < e (n0 + 16) + rhi
    · exact hrLo s a hs
    · exact path_const P_rst false (n0 + 16) 65519 (n0 + 65536) (by omega)
        (fun m x y => Bool.eq_false_iff.2 (fun hm => by
          have := (rr_window hL m (Nat.le_trans (by omega) x) y).1 hm; omega)) s (by omega) b
  have F := ResetContract.c2n_frontier L (e n0 + rhi) r (e (n0 + 65536) + rlo - 1)
    (fun s a b => rstHi s a b) (by omega)
    (fun s a b => rstLo s a (by omega))
    (fun s a b => H_TOKEN_STATIC s a (by omega)) (by omega)
  refine ⟨?_, ?_, ?_⟩
  · intro t a b
    exact path_const P_idx _ n0 65535 (n0 + 65536) (by omega) (fun m x y => idx_const hL m x y) t a b
  · intro t a b hO
    by_cases hlt : t < r + dlmin
    · rw [F.1 t (by omega) hlt] at hO; exact absurd hO (by decide)
    · omega
  · intro t a b
    exact F.2 t a (by omega)

end timed

/-! ## 3. The counter-run: the RTL without `settled` -/

/-- **Which cycle.** Unpinned, in steady state, at a load edge `n0` (the hk
edge at which `win_cnt` goes `0000 -> 0001` and the registered `win_edge_d`
is sampled): idx moves and `rig_rst` rises on this SAME edge; the old arm
(`arm_sr[31] & settle_sr[15]`) is 1 before and after it and closes only at
the NEXT edge (`settle_sr` sees `rig_rst` one edge late). The current arm is
already 0 on both sides of the edge (`settled` fell at the edge `FFFF -> 0000`,
one hk cycle earlier). -/
theorem stale_cycle {vec : Nat} {n0 : Nat} (hL : Load n0) (h : 131072 ≤ n0) :
    armedOld true (run false vec (n0 - 1)) = true ∧
    armedOld true (run false vec n0) = true ∧
    armedOld true (run false vec (n0 + 1)) = false ∧
    rigRst (run false vec n0) = true ∧
    (run false vec n0).idx ≠ (run false vec (n0 - 1)).idx ∧
    armed true (run false vec (n0 - 1)) = false ∧
    armed true (run false vec n0) = false := by
  have hL' := hL; unfold Load at hL'
  refine ⟨(armedOld_iff (by omega)).2 (by omega), (armedOld_iff h).2 (by omega), ?_,
    (rr_window hL n0 (by omega) (by omega)).2 (by omega), idx_moves hL, ?_, ?_⟩
  · cases hc : armedOld true (run false vec (n0 + 1))
    · rfl
    · have := (armedOld_iff (by omega)).1 hc; omega
  · cases hc : armed true (run false vec (n0 - 1))
    · rfl
    · have := armed_phase _ hc; omega
  · cases hc : armed true (run false vec n0)
    · rfl
    · have := armed_phase _ hc; omega

/-- **The timed window of the counter-run.** With the old arm on its path
`[alo, ahi]` and idx on `[vlo, vhi]`: on `[e n0 + max ahi vhi, e(n0+1) +
min alo vlo)` the old arm pin is 1 while the readers already show the NEW
idx (which differs from the previous window's), and the current arm pin, on
the same path, is 0. Nonempty whenever `max ahi vhi < Tlo + min alo vlo`
(true for every routed number in the notes: one hk period is about 7.6 ns). -/
theorem stale_window {vec : Nat} {n0 : Nat} (hL : Load n0) (h : 131072 ≤ n0)
    {alo ahi vlo vhi : Nat} {armOldP armP : Nat → K3} {idxP : Nat → Nat}
    (P_old : PathOK e alo ahi (fun n => K3.ofBool (armedOld true (run false vec n))) armOldP)
    (P_cur : PathOK e alo ahi (fun n => K3.ofBool (armed true (run false vec n))) armP)
    (P_idx : PathOK e vlo vhi (fun n => (run false vec n).idx) idxP)
    (t : Nat) (h1 : e n0 + ahi ≤ t) (h1' : e n0 + vhi ≤ t)
    (h2 : t < e (n0 + 1) + alo) (h2' : t < e (n0 + 1) + vlo) :
    armOldP t = K3.t ∧ armP t = K3.f ∧ idxP t = (run false vec n0).idx ∧
    idxP t ≠ (run false vec (n0 - 1)).idx := by
  obtain ⟨_, o0, _, _, mv, _, c0⟩ := stale_cycle (vec := vec) hL h
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [P_old.1 n0 t h1 h2]; simp only [o0]; rfl
  · rw [P_cur.1 n0 t h1 h2]; simp only [c0]; rfl
  · exact P_idx.1 n0 t h1' h2'
  · rw [P_idx.1 n0 t h1' h2']; exact mv

/-! ### The detector, real INITs -/

/-- `uerr_s`/`uok_s`/... `LUT4 #(.INIT(16'hEC00))`, pins `[raw, q, armed, sticky_keep]`. -/
def I_sticky : Nat := 0xEC00
/-- `uerr_d`, `uerr_a`, `uerr_g`: `LUT2 #(.INIT(4'h8))`. -/
def I_and2 : Nat := 8
/-- `uok_d`: `LUT2 #(.INIT(4'h4))`, pins `[mism, res_req]`. -/
def I_ok : Nat := 4

theorem sticky_eq : ∀ r q a k : Bool, lutB I_sticky [r, q, a, k] = (k && (q || (a && r))) := by
  decide

/-- **The arm holds the sticky** (Kleene): with `armed = 0` and `sticky_keep = 1`,
the sticky's excitation is its own state, whatever `raw` is (`1`, `0`, or
intermediate). -/
theorem sticky_holds_K (raw : K3) :
    lutK I_sticky [raw, .f, .f, .t] = .f ∧ lutK I_sticky [raw, .t, .f, .t] = .t := by
  cases raw <;> exact ⟨rfl, rfl⟩

/-- **A sticky leaves 0 only through an open arm and a non-0 raw** (Kleene, all
27 pin combinations). -/
theorem sticky_sets_only (raw arm keep : K3) (h : lutK I_sticky [raw, .f, arm, keep] ≠ .f) :
    raw ≠ .f ∧ arm ≠ .f ∧ keep ≠ .f := by
  cases raw <;> cases arm <;> cases keep <;> first | exact absurd rfl h | decide

/-- **The verdict gate needs the completion** (Kleene): `err_raw`/`ok_raw` are
0 while the padded `res_req` is 0, whatever `mism` is; `sel = 0` blocks the
per-vector gate. -/
theorem gate_needs_req (m : K3) :
    lutK I_and2 [m, .f] = .f ∧ lutK I_ok [m, .f] = .f := by
  cases m <;> exact ⟨rfl, rfl⟩

/-- The sweep's previous vector. -/
def prevIdx (v : Nat) : Nat := (v + 15) % 16

/-- The detector chain for vector `v` when the result on `res_req` is the
PREVIOUS vector's correct answer (`vG (prevIdx v)` = `stein` of its operands,
`table_ok`), steady values after the width filter: `mism`, `uerr_d`,
`uerr_a` (`a & delay(a)` with both legs settled), `uerr_g` (`sel = 1`), and
the sticky with `q = 0`, `sticky_keep = 1` and the given arm. -/
def staleErr (arm : Bool) (v : Nat) : Bool :=
  let mism := decide (vG (prevIdx v) ≠ vG v)
  let errRaw := lutB I_and2 [mism, true]
  let errFlt := lutB I_and2 [errRaw, errRaw]
  let raw := lutB I_and2 [errFlt, true]
  lutB I_sticky [raw, false, arm, true]

def staleOk (arm : Bool) (v : Nat) : Bool :=
  let mism := decide (vG (prevIdx v) ≠ vG v)
  let okRaw := lutB I_ok [mism, true]
  let okFlt := lutB I_and2 [okRaw, okRaw]
  let raw := lutB I_and2 [okFlt, true]
  lutB I_sticky [raw, false, arm, true]

/-- **The counter-run's verdicts.** With the arm open (old RTL, `stale_window`),
a stale result sets `err` on every vector of the sweep except 3, 5 and 13,
whose predecessors (2, 4, 12) have the same expected gcd; on those three it
sets `ok` instead. With the arm closed (current RTL) it sets nothing. -/
theorem stale_err_vectors :
    (List.range 16).filter (staleErr true) = [0, 1, 2, 4, 6, 7, 8, 9, 10, 11, 12, 14, 15] ∧
    (List.range 16).filter (staleOk true) = [3, 5, 13] ∧
    (List.range 16).all (fun v => !staleErr false v && !staleOk false v) = true :=
  ⟨by decide +kernel, by decide +kernel, by decide +kernel⟩

/-! ## 4. Non-vacuity: concrete paths at a 7.6 ns hk period -/

/-- A fixed transport delay `d` from hk edges at `e n = T·n` is a `PathOK`
with `lo = hi = d`. -/
theorem pathOK_transport {α : Type} (T d : Nat) (hT : 0 < T) (v : Nat → α) :
    PathOK (fun n => T * n) d d v (fun t => v ((t - d) / T)) := by
  refine ⟨fun n t h1 h2 => ?_, fun n t _ h1 h2 => absurd h2 (by omega)⟩
  show v ((t - d) / T) = v n
  congr 1
  simp only at h1 h2
  rw [Nat.mul_succ] at h2
  have h1' : T * n ≤ t - d := by omega
  have h2' : t - d < T * (n + 1) := by rw [Nat.mul_succ]; omega
  exact Nat.le_antisymm (Nat.lt_succ_iff.1 ((Nat.div_lt_iff_lt_mul hT).2 (by rw [Nat.mul_comm]; exact h2')))
    ((Nat.le_div_iff_mul_le hT).2 (by rw [Nat.mul_comm]; exact h1'))

/-- **`verdict_current` is reached.** hk period 7600 ps (27.5 hops at about
275 ps, `gcd_hw.v`'s own figure), arm path 600 ps, idx paths 1500 ps: all
hypotheses hold, and at an instant of window `n0 = 2·65536 + 1` (phase 3000)
the arm pin is 1 and the conclusion is non-trivial. -/
theorem verdict_nonvacuous :
    let e := fun n => 7600 * n
    let armP := fun t => K3.ofBool (armed true (run false 0 ((t - 600) / 7600)))
    let idxP := fun t => (run false 0 ((t - 1500) / 7600)).idx
    let n0 := 2 * 65536 + 1
    let t := e (n0 + 2999) + 600
    armP t = K3.t ∧ e (n0 - 1) + 600 ≤ t ∧ t < e (n0 + 65535) + 600 ∧
    idxP t = (run false 0 n0).idx := by
  intro e armP idxP n0 t
  have hL : Load n0 := by unfold Load; decide
  have hA : armed true (run false 0 (n0 + 2999)) = true := (armed_iff (by decide)).2 (by decide)
  have hdiv : (t - 600) / 7600 = n0 + 2999 := by
    show (7600 * (2 * 65536 + 1 + 2999) + 600 - 600) / 7600 = 2 * 65536 + 1 + 2999; omega
  have hA' : armP t = K3.t := by
    show K3.ofBool (armed true (run false 0 ((t - 600) / 7600))) = K3.t
    rw [hdiv, hA]; rfl
  have b1 : e (n0 - 1) + 600 ≤ t := by
    show 7600 * (2 * 65536 + 1 - 1) + 600 ≤ 7600 * (2 * 65536 + 1 + 2999) + 600; omega
  have b2 : t < e (n0 + 65535) + 600 := by
    show 7600 * (2 * 65536 + 1 + 2999) + 600 < 7600 * (2 * 65536 + 1 + 65535) + 600; omega
  refine ⟨hA', b1, b2, ?_⟩
  exact (verdict_current (pin := false) (vec := 0) (armG := true) (e := e) (Tlo := 7600)
    (fun n => by show 7600 * n + 7600 ≤ 7600 * (n + 1); omega)
    (pathOK_transport 7600 600 (by decide) _) (pathOK_transport 7600 1500 (by decide) _)
    (by decide) (by decide) hL t b1 b2 (by rw [hdiv, hA]; decide)).2

/-- **`stale_window` is reached** with the same numbers: 1500 ps after the
load edge, the old arm is 1, the current arm is 0, and the readers show the
new vector (not the previous window's). -/
theorem stale_nonvacuous :
    let e := fun n => 7600 * n
    let n0 := 2 * 65536 + 1
    let t := e n0 + 1500
    K3.ofBool (armedOld true (run false 0 ((t - 600) / 7600))) = K3.t ∧
    K3.ofBool (armed true (run false 0 ((t - 600) / 7600))) = K3.f ∧
    (run false 0 ((t - 1500) / 7600)).idx ≠ (run false 0 (n0 - 1)).idx := by
  intro e n0 t
  have hL : Load n0 := by unfold Load; decide
  have W := stale_window (e := e) (vec := 0) hL (by decide)
    (pathOK_transport 7600 600 (by decide) _) (pathOK_transport 7600 600 (by decide) _)
    (pathOK_transport 7600 1500 (by decide) _) t
    (by show 7600 * (2 * 65536 + 1) + 600 ≤ 7600 * (2 * 65536 + 1) + 1500; omega)
    (by show 7600 * (2 * 65536 + 1) + 1500 ≤ 7600 * (2 * 65536 + 1) + 1500; omega)
    (by show 7600 * (2 * 65536 + 1) + 1500 < 7600 * (2 * 65536 + 1 + 1) + 600; omega)
    (by show 7600 * (2 * 65536 + 1) + 1500 < 7600 * (2 * 65536 + 1 + 1) + 1500; omega)
  exact ⟨W.1, W.2.1, W.2.2.2⟩

end Formal.Cells.RigContract
