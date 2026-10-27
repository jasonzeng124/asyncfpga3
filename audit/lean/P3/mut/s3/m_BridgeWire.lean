import Formal.Net.Bridge
import Formal.Net.Ring

/-!
# Probe 8d: dropping H_ISO — wires as their own buffer gates

`Bridge` assumes isochronic forks: every reader of a node sees it at the same
instant. On the fabric a fork is several routed wires with different delays.
Model each such wire as a BUFFER gate of its own (its own inertial channel,
its own bounds). That is a different network; the bridge applies to it iff it
is persistent, i.e. iff the circuit is speed-independent with those wires
explicit (= delay-insensitive on those forks). Two ways to do it for the
`bd_link_ctl` ring (`c_i = C(c_{i-1}, ~c_{i+1})`, the real `bd_c2n` /
`bd_c2n_set` LUT in run mode):

* **`forkNet`**: the two inter-stage wires of every node are buffers
  (`u_i`: c_i as seen by stage i+1's `a` pin, `v_i`: as seen by stage i-1's
  `b` pin); the feedback pin still reads the node itself (H_FB_SETTLED).
  For N = 3 (9 gates, all 512 states) we prove by a kernel-checked
  certificate (and N = 4, 4096 states): persistent, one loop token (D = 2) in every reachable state,
  never stuck. With `Bridge`: for EVERY assignment of independent inertial
  bounds to the 3 LUTs and the 6 wires, the timed ring is safe and live
  (`timed_fork3`, `timed_fork4`). So the ring needs no isochronic
  fork between stages (each branch is acknowledged before the node moves
  again). Python exploration (formal/notes/C-8d-bridge.md) finds the same for
  N = 5; all N is an open goal.
* **`fbNet`**: the feedback wire `O -> I2` of every stage is a buffer `w_i`
  (stage reads `c_{i-1}, c_{i+1}, w_i`). NOT persistent
  (`fb3_not_persistent`), and the token is LOST: the run
  `[c1, c0, c1, w0]` ends in a dead all-zero ring (`fb3_token_lost`), and by
  `Bridge.realize` it is a timed trace with every LUT and wire an inertial
  channel with bounds `[1, 4]` (`fb3_timed_token_lost`). Mechanism: c1 sets,
  c0 answers (falls), c1's LUT now sees a = b = 0 ("hold") but its I2 pin still
  carries the OLD q = 0, so it reverts. This is exactly the timing condition
  shard B derives for the feedback LUT (probe 5b): the feedback route must be
  faster than the neighbour's response. The isochronic-feedback assumption
  cannot be dropped; it must be discharged by timing (H_FB_SETTLED).
-/

namespace Formal.Net.Bridge.Wire
open Formal.Net Formal.Net.Bridge Formal.Cells.CElemFn

/-! ## A certificate checker for persistence on small networks -/

def exB (N : Net) (s : State) (i : Nat) : Bool := decide (i < N.n) && (N.f i s != s i)

theorem exB_iff {N : Net} {s : State} {i : Nat} : exB N s i = true ↔ excited N s i := by
  unfold exB excited; simp

/-- The state with bits `0 … M-1` read from `m`. -/
def ofMask (M m : Nat) : State := fun j => decide (j < M) && m.testBit j

def enc (s : State) : Nat → Nat
  | 0 => 0
  | k + 1 => enc s k + (if s k then 2 ^ k else 0)

theorem frame_mask : ∀ (M : Nat) (s : State), (∀ j, M ≤ j → s j = false) →
    ∃ m, m < 2 ^ M ∧ s = ofMask M m := by
  intro M
  induction M with
  | zero => intro s h; exact ⟨0, by decide, funext fun j => by simp [ofMask, h j (Nat.zero_le _)]⟩
  | succ M ih =>
    intro s h
    let s' : State := fun j => if j = M then false else s j
    obtain ⟨m', hm', he⟩ := ih s' (fun j hj => by
      simp only [s']; split
      · rfl
      · exact h j (by omega))
    have hpow : 2 ^ (M + 1) = 2 ^ M + 2 ^ M := by rw [Nat.pow_succ]; omega
    refine ⟨if s M then 2 ^ M + m' else m', by split <;> omega, funext fun j => ?_⟩
    have hj' := congrFun he j
    simp only [s'] at hj'
    simp only [ofMask]
    by_cases hjm : j < M
    · have : j ≠ M := by omega
      rw [ite_eq_right_iff.2 (fun h => absurd h this)] at hj'
      rw [hj']; simp only [ofMask, hjm, decide_true, Bool.true_and]
      have : j < M + 1 := by omega
      simp only [this, decide_true, Bool.true_and]
      split
      · rw [Nat.testBit_two_pow_add_gt hjm]
      · rfl
    · by_cases hje : j = M
      · subst hje
        simp only [Nat.lt_succ_self, decide_true, Bool.true_and]
        cases hs : s j
        · simp [Nat.testBit_lt_two_pow hm']
        · simp [Nat.testBit_two_pow_add_eq, Nat.testBit_lt_two_pow hm']
      · have : ¬ j < M + 1 := by omega
        simp only [this, decide_false, Bool.false_and]
        exact h j (by omega)

def allLt (M : Nat) (p : Nat → Bool) : Bool := (List.range M).all p

theorem allLt_true {M : Nat} {p : Nat → Bool} (h : allLt M p = true) {i : Nat} (hi : i < M) :
    p i = true := by
  unfold allLt at h; rw [List.all_eq_true] at h; exact h i (List.mem_range.2 hi)

/-- One state's clause: `P`, closure of the certificate `R` under firing, and
persistence. -/
def clause (N : Net) (R : Nat) (P : State → Bool) (s : State) : Bool :=
  !R.testBit (enc s N.n) ||
    (P s && allLt N.n (fun g => !exB N s g || R.testBit (enc (fire s g) N.n)) &&
      allLt N.n (fun i => allLt N.n (fun j =>
        !(exB N s i && exB N s j && i != j) || exB N (fire s j) i)))

def check (N : Net) (R : Nat) (P : State → Bool) : Bool :=
  allLt (2 ^ N.n) (fun m => clause N R P (ofMask N.n m))

def Frame (N : Net) (s : State) : Prop := ∀ j, N.n ≤ j → s j = false

theorem clause_of_check {N : Net} {R : Nat} {P : State → Bool} (hc : check N R P = true)
    {s : State} (hs : Frame N s) : clause N R P s = true := by
  obtain ⟨m, hm, rfl⟩ := frame_mask N.n s hs
  exact allLt_true hc hm

/-- **Soundness of the certificate check.** -/
theorem check_sound {N : Net} {R : Nat} {P : State → Bool} (hc : check N R P = true)
    {s0 : State} (hf : Frame N s0) (hR : R.testBit (enc s0 N.n) = true) :
    Persistent N s0 ∧ ∀ s, Reach N s0 s → P s = true := by
  have inv : ∀ s, Reach N s0 s → Frame N s ∧ R.testBit (enc s N.n) = true := by
    intro s h
    induction h with
    | refl => exact ⟨hf, hR⟩
    | step g _ he ih =>
      obtain ⟨hfs, hRs⟩ := ih
      have cl := clause_of_check hc hfs
      simp only [clause, hRs, Bool.not_true, Bool.false_or, Bool.and_eq_true] at cl
      refine ⟨fun j hj => ?_, ?_⟩
      · have : j ≠ g := by have := he.1; omega
        simp [fire, this, hfs j hj]
      · have := allLt_true cl.1.2 he.1
        simp only [exB_iff.2 he, Bool.not_true, Bool.false_or] at this
        exact this
  refine ⟨fun s hr i j hi hj hij => ?_, fun s hr => ?_⟩
  · obtain ⟨hfs, hRs⟩ := inv s hr
    have cl := clause_of_check hc hfs
    simp only [clause, hRs, Bool.not_true, Bool.false_or, Bool.and_eq_true] at cl
    have := allLt_true (allLt_true cl.2 hi.1) hj.1
    have hij' : (i != j) = true := bne_iff_ne.2 hij
    simp only [exB_iff.2 hi, exB_iff.2 hj, hij', Bool.and_self, Bool.not_true,
      Bool.false_or] at this
    exact exB_iff.1 this
  · obtain ⟨hfs, hRs⟩ := inv s hr
    have cl := clause_of_check hc hfs
    simp only [clause, hRs, Bool.not_true, Bool.false_or, Bool.and_eq_true] at cl
    exact cl.1.1

/-! ## The ring with every inter-stage wire a separate delay element -/

/-- Stage function: the real LUT in run mode (`_set` for `i < K`). -/
def stage (K i : Nat) (a b q : Bool) : Bool :=
  if i < K then c2nsetB a b q false else c2nB a b q false

/-- Nodes: `c_i = i`, `u_i = n+i` (c_i at stage i+1's `a` pin),
`v_i = 2n+i` (c_i at stage i-1's `b` pin). -/
def forkNet (n K : Nat) : Net where
  n := 3 * n
  f i s :=
    if i < n then stage K i (s (n + Ring.prv n i)) (s (2 * n + Ring.nxt n i)) (s i)
    else if i < 2 * n then s (i - n) else s (i - 2 * n)

def forkReset (n K : Nat) : State := fun j => decide (j < 3 * n) && decide (j % n < K)

def anyLt (M : Nat) (p : Nat → Bool) : Bool := (List.range M).any p

/-- Safety and progress predicate on `forkNet n 1` states: one loop token
(on the stage nodes) and some gate (stage or wire) excited. -/
def forkP (n : Nat) (s : State) : Bool := Ring.D n s == 2 && anyLt (3 * n) (exB (forkNet n 1) s)

theorem forkReset_frame (n K : Nat) : Frame (forkNet n K) (forkReset n K) := by
  intro j hj; simp [forkNet] at hj; simp [forkReset]; omega

theorem fork_sound_of {n R : Nat} (hc : check (forkNet n 1) R (forkP n) = true)
    (hR : R.testBit (enc (forkReset n 1) (forkNet n 1).n) = true) :
    Persistent (forkNet n 1) (forkReset n 1) ∧
    ∀ s, Reach (forkNet n 1) (forkReset n 1) s → forkP n s = true :=
  check_sound hc (forkReset_frame n 1) hR

variable {hi : Nat → Nat} {x : Nat → State}

/-- Timed safety and liveness for any `n` whose certificate checks. -/
theorem timed_fork_of {n R : Nat} (hc : check (forkNet n 1) R (forkP n) = true)
    (hR : R.testBit (enc (forkReset n 1) (forkNet n 1).n) = true)
    (hx : TimedF (forkNet n 1) hi x) (h0 : x 0 = forkReset n 1) (t : Nat) :
    Ring.D n (x t) = 2 ∧ ∃ i u, i < 3 * n ∧ t ≤ u ∧ u < t + hi i ∧ x (u + 1) i ≠ x u i := by
  have hs := fork_sound_of hc hR
  have := hs.2 _ (timed_reachF hs.1 hx h0 t)
  simp only [forkP, Bool.and_eq_true, beq_iff_eq, anyLt, List.any_eq_true,
    List.mem_range] at this
  obtain ⟨hD, i, hi3, he⟩ := this
  obtain ⟨u, h1, h2, h3⟩ := fires_withinF hs.1 hx h0 (exB_iff.1 he)
  exact ⟨hD, i, u, hi3, h1, h2, h3⟩

/-- Reachable-set certificates (bit `m` set iff state `ofMask (3n) m` is
reachable; computed by BFS in Python, CHECKED by the kernel below: the check
needs only that the set is closed and contains reset, so a wrong certificate
fails rather than proving something false). -/
def R3 : Nat := 0x405000104050001020202222000002022030203000100010080008000c040c04404000004444040408000a0208000a020000000000000000
def R4 : Nat := 0x400050000000110000000000000001004000500000001100000000000000010020002000220022000000000002020202000000000000000000000000000200022000300022003300000000000200030000001000000011000000000000000100080000000800000008080000080800000000000000000000000c0004000c00044800400008000100080000000800010040004000000001000004000400040104080000000a000200080800000a0a0202000000000000000000080000000a0002080000000a000300080000000a000300000000000000010000000000000001000080000000000000008000000000000000c000500000001000c00050000000104000500000001000000000000000000040405050000010100040005000000010208020002000200000800000000200020080001000000010008000100002001220003000200030000000000000000000000010100000101000000010000000100080000000000000008800000008000000c000400000000000cc0044000c00044000400000000000000000000000000040404040000000000044004400040004008000000000000000880000000a0002008000000000000000880000000a00020000000000000000000000000000000000000000000000000000000000000000

theorem fork3_check : check (forkNet 3 1) R3 (forkP 4) = true := by decide +kernel
theorem fork4_check : check (forkNet 4 1) R4 (forkP 4) = true := by decide +kernel

theorem fork3_persistent : Persistent (forkNet 3 1) (forkReset 3 1) :=
  (fork_sound_of fork3_check (by decide)).1
theorem fork4_persistent : Persistent (forkNet 4 1) (forkReset 4 1) :=
  (fork_sound_of fork4_check (by decide)).1

/-- **Timed safety and liveness without isochronic inter-stage forks**, N = 3:
one loop token at every ps, and some LUT or wire toggles within its upper
bound, for EVERY inertial bound assignment to the 3 LUTs and 6 wires. -/
theorem timed_fork3 (hx : TimedF (forkNet 3 1) hi x) (h0 : x 0 = forkReset 3 1) (t : Nat) :
    Ring.D 3 (x t) = 2 ∧ ∃ i u, i < 9 ∧ t ≤ u ∧ u < t + hi i ∧ x (u + 1) i ≠ x u i :=
  timed_fork_of fork3_check (by decide) hx h0 t

/-- The same for N = 4 (4 LUTs, 8 wires). -/
theorem timed_fork4 (hx : TimedF (forkNet 4 1) hi x) (h0 : x 0 = forkReset 4 1) (t : Nat) :
    Ring.D 4 (x t) = 2 ∧ ∃ i u, i < 12 ∧ t ≤ u ∧ u < t + hi i ∧ x (u + 1) i ≠ x u i :=
  timed_fork_of fork4_check (by decide) hx h0 t

/-! ## The ring with the FEEDBACK wire a separate delay element -/

/-- Nodes: `c_i = i`, `w_i = n+i` (c_i at its own I2 pin). -/
def fbNet (n K : Nat) : Net where
  n := 2 * n
  f i s :=
    if i < n then stage K i (s (Ring.prv n i)) (s (Ring.nxt n i)) (s (n + i))
    else s (i - n)

def fbReset (n K : Nat) : State := fun j => decide (j < 2 * n) && decide (j % n < K)

def runB (N : Net) : State → List Nat → Bool
  | _, [] => true
  | s, i :: is => exB N s i && runB N (fire s i) is

theorem runB_sound {N : Net} : ∀ {L : List Nat} {s : State}, runB N s L = true → Run N s L := by
  intro L
  induction L with
  | nil => intro _ _; trivial
  | cons i L ih =>
    intro s h
    simp only [runB, Bool.and_eq_true] at h
    exact ⟨exB_iff.1 h.1, ih h.2⟩

theorem not_excited_of {N : Net} {s : State} (h : allLt N.n (fun i => !exB N s i) = true) :
    ∀ i, ¬ excited N s i := by
  intro i he
  have := allLt_true h he.1
  rw [exB_iff.2 he] at this; exact Bool.noConfusion this

/-- **Not persistent**: after `c1` sets and `c0` answers, both `c2` and `c1`
(about to revert, its I2 pin still reads the old value) are excited, and
firing `c1` disables `c2`. -/
theorem fb3_not_persistent : ¬ Persistent (fbNet 3 1) (fbReset 3 1) := by
  intro hp
  have hr : Reach (fbNet 3 1) (fbReset 3 1) (final (fbReset 3 1) [1, 0]) :=
    run_reach .refl (runB_sound (by decide))
  have := hp _ hr 2 1 (exB_iff.1 (by decide)) (exB_iff.1 (by decide)) (by decide)
  have := exB_iff.2 this
  revert this; decide

/-- **The token is lost** (SI semantics of `fbNet`): the run
`[c1, c0, c1, w0]` from reset ends in a dead ring with no wavefront. -/
theorem fb3_token_lost :
    Run (fbNet 3 1) (fbReset 3 1) [1, 0, 1, 3] ∧
    Ring.D 3 (fbReset 3 1) = 2 ∧
    Ring.D 3 (final (fbReset 3 1) [1, 0, 1, 3]) = 0 ∧
    ∀ i, ¬ excited (fbNet 3 1) (final (fbReset 3 1) [1, 0, 1, 3]) i :=
  ⟨runB_sound (by decide), by decide, by decide, not_excited_of (by decide)⟩

/-- **…and in time.** With every LUT and every wire (including the feedback
wires) an inertial channel with bounds `[1, 4]`, the ring starts with one
token and is dead with none from `t = 4` on. -/
theorem fb3_timed_token_lost :
    Timed (fbNet 3 1) (fun _ => 1) (fun _ => 4) (runTrace (fbReset 3 1) [1, 0, 1, 3]) ∧
    runTrace (fbReset 3 1) [1, 0, 1, 3] 0 = fbReset 3 1 ∧
    Ring.D 3 (runTrace (fbReset 3 1) [1, 0, 1, 3] 0) = 2 ∧
    ∀ t, 4 ≤ t → Ring.D 3 (runTrace (fbReset 3 1) [1, 0, 1, 3] t) = 0 := by
  obtain ⟨hr, h2, h0, hd⟩ := fb3_token_lost
  refine ⟨realize hr hd (by decide), runTrace_zero _ _, ?_, fun t ht => ?_⟩
  · rw [runTrace_zero]; exact h2
  · rw [runTrace_final (by simp; omega)]; exact h0

end Formal.Net.Bridge.Wire
