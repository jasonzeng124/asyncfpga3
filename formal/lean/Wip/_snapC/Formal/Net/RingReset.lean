import Formal.Net.BridgeRing

/-!
# Probe C-9d (a): what bdc's reset puts in a ring, and the token count from it

9a's `ring_three` assumes the ring holds ONE four-phase token (two wavefronts, `D = 2`):
H_ONE_TOKEN. Where does that token come from in a circuit bdc emits?

## 1. The reset state: every ring is empty
bdc emits every link as `bd_link_ctl` = `bd_c2n` (INIT `0x00B2…`, rst on I3); it never
emits `bd_c2n_set`/`bd_c2_set` (the only `_set` cell in an emitted design is the arbiter's
state node inside `bd_arb`, which is not on a handshake ring). Every other control cell on
a loop clears on rst too: `bd_c2` (fork/join/mux acks), `bd_c3`, `bd_c4`, and the two join
LUTs of `bd_mux` (`uj0` 0xAE08, `uj1` 0xEA80, rst on I4). Proved here from the INITs
(`*_rst_clear`). So at release of reset (H_RESET_CLEAN) every node of every ring is 0:
the closed link ring is `resetState 0`, `D = 0`, no token, and it stays frozen on every
timed trace (`bdc_closed_ring_empty`, from 8d's `timed_ring_degenerate`). H_ONE_TOKEN is
therefore NOT a property of the reset state: the loop token must come in through the
loop's entry.

## 2. The loop ring with its entry and exit (`loopStep`)
The shape bdc emits for a loop and that emit.py's comment says was measured ("mux ->
steer -> storage -> mux"): a two-input `bd_mux` (entry on `x`, back edge on `y`), `N`
link controllers, a `bd_steer` whose branch 1 (`req1 = req·s`) returns to the mux's `y`
and whose branch 0 leaves the loop into a `bd_snk`. Every gate is its real LUT (INITs
verbatim from `bd_mux.v`, `bd_ctl.v`, `bd_ce.v`, `bd_end.v`), H_SI (one gate at a time).
The `bd_delay` chain behind the mux's OR is folded into the OR gate (a buffer chain is
a sequence of buffers, H_DELAY_AS_GATE). The environment (named hypotheses, all
stated as the allowed environment moves in `envSucc`):
* H_START_ONCE: the entry `x_req` rises once (when `x_ack = 0`), falls after `x_ack`
  rises, never again (four-phase, one token offered).
* H_CTL_ENV: the mux's control channel is a free source (`ctl_req = ¬ctl_ack`, the
  `bd_src` LUT, `ctl_ack = z_ack`); its select level `s` is 0 for the entry transaction
  and switches to 1 (loop back) once, only after the entry token was accepted
  (`x_req = 0`) and the mux is idle (both joins, the OR and both acks at 0).
* H_EXIT_ENV: the steer select is 1 (loop back) and may switch to 0 once, only while the
  steer is idle (its request, both branch requests and its ack at 0) and the loop has
  closed (mux select 1). Runs that never exit are included.

The certificate file `RingResetCert` checks, by kernel evaluation of a closed reachable
set, for `N = 3, 4, 5`: from the all-zero reset, before the entry no wavefront is on the
links; while the token loops (mux select 1, not exited) the link ring carries exactly
`D = 2` (one four-phase token) and some gate is excited (no deadlock); the only states
with no move at all are after the exit with `D = 0` (the token left); every reachable
state has `D ∈ {0, 2}`; and the gates are persistent (speed-independent). For `N = 1, 2`
an explicit run reaches a deadlock with the token stuck inside the loop. So the mux and
the steer add no storage (the floor is still 3 links), and the one-token hypothesis of
9a follows from bdc's reset + H_START_ONCE (+ H_CTL_ENV, H_EXIT_ENV).

Not covered: the real select/control sources (the control_merge index ring that drives
the mux's ctl channel; the loop condition's data path driving the steer), N > 5 for the
loop (`timed`/SI results for the closed ring are for every N), data latches.
-/

namespace Formal.Net.RingReset
open Formal.Cells Formal.Net

/-! ## 1. Reset values of the control cells, from the INITs -/

/-- `bd_mux.v` `uj0`: `I0=x_req I1=ctl_req I2=s I3=j0 I4=rst I5=0`. -/
def INIT_mux_j0 : Nat := 0x0000AE080000AE08
/-- `bd_mux.v` `uj1`: `I0=y_req I1=ctl_req I2=s I3=j1 I4=rst I5=0`. -/
def INIT_mux_j1 : Nat := 0x0000EA800000EA80
/-- `bd_ctl.v` `bd_steer`: `LUT6_2`, `I0=req I1=s I5=1`; `O6 = req1`, `O5 = req0`. -/
def INIT_steer : Nat := 0x8888888822222222
/-- `LUT2 #(.INIT(4'hE))` (mux `uor`, steer `uack`). -/
def INIT_or2 : Nat := 0xE
/-- `bd_end.v` `bd_src`: `LUT1 #(.INIT(2'h1))`, `I0=ack`. -/
def INIT_src : Nat := 0x1

theorem c2n_rst_clear : ∀ a b q : Bool, CElemFn.c2nB a b q true = false := by decide
theorem c2_rst_clear : ∀ a b q : Bool, CElemFn.c2B a b q true = false := by decide
theorem c3_rst_clear : ∀ a b c q : Bool, CElemFn.c3B a b c q true = false := by decide
theorem c4_rst_clear : ∀ a b c d q : Bool, CElemFn.c4B a b c d q true = false := by decide
theorem mux_j0_rst_clear : ∀ a b c q : Bool, lutB INIT_mux_j0 [a, b, c, q, true, false] = false := by
  decide
theorem mux_j1_rst_clear : ∀ a b c q : Bool, lutB INIT_mux_j1 [a, b, c, q, true, false] = false := by
  decide
/-- The only `_set` cell (arbiter state, not used on rings by bdc) comes up at 1. -/
theorem c2nset_rst_set : ∀ a b q : Bool, CElemFn.c2nsetB a b q true = true := by decide

/-- The link controller in run mode is 9a's `ctl`. -/
theorem c2n_is_ctl : ∀ a b q : Bool, CElemFn.c2nB a b q false = Ring.ctl a b q := Ring.c2n_run

/-- Functional reading of the mux joins, steer, OR and source LUTs (run mode). -/
theorem mux_j0_fn : ∀ x c s q : Bool, lutB INIT_mux_j0 [x, c, s, q, false, false] =
    ((x && c && !s) || (q && (x || (c && !s)))) := by decide
theorem mux_j1_fn : ∀ y c s q : Bool, lutB INIT_mux_j1 [y, c, s, q, false, false] =
    ((y && c && s) || (q && (y || (c && s)))) := by decide
theorem steer_fn : ∀ r s : Bool,
    lutB INIT_steer [r, s, false, false, false, true] = (r && s) ∧
    lutB (INIT_steer % 2 ^ 32) [r, s, false, false, false] = (r && !s) := by decide
theorem or2_fn : ∀ a b : Bool, lutB INIT_or2 [a, b] = (a || b) := by decide
theorem src_fn : ∀ a : Bool, lutB INIT_src [a] = !a := by decide

/-- **bdc's closed link ring is empty at reset and stays frozen.** Every link bdc emits is
`bd_c2n`, so with `rst` held every stage drives 0 (`Ring.gate_rst` at `K = 0`); the release
state `resetState 0` has no wavefront, and every inertial timed trace from it is constant. -/
theorem bdc_closed_ring_empty (n : Nat) {lo hi : Nat → Nat} {x : Nat → Ring.State}
    (hx : Bridge.Timed (Bridge.RingT.ringNet n 0) lo hi x) (h0 : x 0 = Ring.resetState 0) :
    (∀ s i, Ring.gate n 0 true s i = false) ∧ Ring.D n (Ring.resetState 0) = 0 ∧
      ∀ t, x t = Ring.resetState 0 := by
  refine ⟨fun s i => by rw [Ring.gate_rst]; rfl, Ring.D_reset_degenerate (Or.inl rfl), ?_⟩
  exact Bridge.RingT.timed_ring_degenerate (Or.inl rfl) hx h0

/-! ## 2. The loop ring: mux → N links → steer → mux, as a bit-vector transition system -/

def bit (s k : Nat) : Bool := s.testBit k
def flip (s k : Nat) : Nat := s ^^^ (1 <<< k)

section Idx
variable (N : Nat)
/-- Node indices: links `0 … N-1`, then the mux, steer, sink, then the environment. -/
def J0 := N
def J1 := N + 1
def ZQ := N + 2    -- mux z_req (OR of the joins, through the delay chain)
def XA := N + 3    -- mux x_ack  (bd_c2 uxa)
def YA := N + 4    -- mux y_ack  (bd_c2 uya)
def CQ := N + 5    -- ctl_req of the free control source (bd_src)
def R1 := N + 6    -- steer req1 (back to the mux's y)
def R0 := N + 7    -- steer req0 (exit)
def A0 := N + 8    -- exit sink ack (bd_snk: ack = req)
def SA := N + 9    -- steer ack (OR)
def XQ := N + 10   -- env: entry x_req
def SM := N + 11   -- env: mux select
def CNT := N + 12  -- env: entry token offered (once)
def SS := N + 13   -- env: steer select (1 = loop back)
def EX := N + 14   -- env: exit taken
end Idx

/-- The value each gate's LUT drives in state `s` (run mode, rst = 0). -/
def gateVal (N s g : Nat) : Bool :=
  if g < N then
    CElemFn.c2nB (if g = 0 then bit s (ZQ N) else bit s (g - 1))
      (if g = N - 1 then bit s (SA N) else bit s (g + 1)) (bit s g) false
  else if g = J0 N then lutB INIT_mux_j0 [bit s (XQ N), bit s (CQ N), bit s (SM N), bit s g, false, false]
  else if g = J1 N then lutB INIT_mux_j1 [bit s (R1 N), bit s (CQ N), bit s (SM N), bit s g, false, false]
  else if g = ZQ N then lutB INIT_or2 [bit s (J0 N), bit s (J1 N)]
  else if g = XA N then CElemFn.c2B (bit s (J0 N)) (bit s 0) (bit s g) false
  else if g = YA N then CElemFn.c2B (bit s (J1 N)) (bit s 0) (bit s g) false
  else if g = CQ N then lutB INIT_src [bit s 0]
  else if g = R1 N then lutB INIT_steer [bit s (N - 1), bit s (SS N), false, false, false, true]
  else if g = R0 N then lutB (INIT_steer % 2 ^ 32) [bit s (N - 1), bit s (SS N), false, false, false]
  else if g = A0 N then bit s (R0 N)
  else if g = SA N then lutB INIT_or2 [bit s (A0 N), bit s (YA N)]
  else bit s g

/-- The gates (every node that is a LUT output). -/
def gates (N : Nat) : List Nat := List.range (N + 10)

def excB (N s g : Nat) : Bool := gateVal N s g != bit s g

def muxIdle (N s : Nat) : Bool :=
  !(bit s (J0 N) || bit s (J1 N) || bit s (ZQ N) || bit s (XA N) || bit s (YA N))

def steerIdle (N s : Nat) : Bool :=
  !(bit s (N - 1) || bit s (R1 N) || bit s (R0 N) || bit s (A0 N) || bit s (SA N))

/-- The environment moves (H_START_ONCE, H_CTL_ENV, H_EXIT_ENV). -/
def envSucc (N s : Nat) : List Nat :=
  (if !bit s (XQ N) && !bit s (XA N) && !bit s (CNT N) && !bit s (SM N)
    then [flip (flip s (XQ N)) (CNT N)] else []) ++
  (if bit s (XQ N) && bit s (XA N) then [flip s (XQ N)] else []) ++
  (if bit s (CNT N) && !bit s (XQ N) && !bit s (SM N) && muxIdle N s
    then [flip s (SM N)] else []) ++
  (if bit s (SM N) && bit s (SS N) && !bit s (EX N) && steerIdle N s
    then [flip (flip s (SS N)) (EX N)] else [])

/-- One SI step: fire one excited gate, or one environment move. -/
def succ (N s : Nat) : List Nat := ((gates N).filter (excB N s)).map (flip s) ++ envSucc N s

/-- Reset: every LUT node 0 (section 1); environment: steer select 1, nothing offered yet. -/
def s0 (N : Nat) : Nat := 1 <<< SS N

inductive Reach (N : Nat) : Nat → Prop
  | refl : Reach N (s0 N)
  | step {s t : Nat} : Reach N s → t ∈ succ N s → Reach N t

/-- Wavefronts on the link ring (closed through the mux and steer). -/
def Dl (N s : Nat) : Nat :=
  ((List.range N).filter (fun i => bit s i != bit s (if i = 0 then N - 1 else i - 1))).length

def anyExc (N s : Nat) : Bool := (gates N).any (excB N s)

/-- The properties certified on every reachable state. -/
def goodB (N s : Nat) : Bool :=
  (Dl N s == 0 || Dl N s == 2) &&
  (bit s (CNT N) || Dl N s == 0) &&
  (!(bit s (SM N) && !bit s (EX N)) || (Dl N s == 2 && anyExc N s)) &&
  (anyExc N s || !(envSucc N s).isEmpty || (bit s (EX N) && Dl N s == 0)) &&
  (gates N).all (fun g => (gates N).all (fun h =>
    g == h || !excB N s g || !excB N s h || excB N (flip s g) h))

def closedB (N : Nat) (L : List Nat) : Bool :=
  L.all (fun s => (succ N s).all (fun t => L.contains t))

theorem cert_sound {N : Nat} {L : List Nat} (h0 : L.contains (s0 N) = true)
    (hc : closedB N L = true) {s : Nat} (hs : Reach N s) : L.contains s = true := by
  induction hs with
  | refl => exact h0
  | step _ ht ih =>
    have := List.all_eq_true.1 hc _ (List.contains_iff_mem.1 ih)
    exact List.all_eq_true.1 this _ ht

theorem cert_good {N : Nat} {L : List Nat} (h0 : L.contains (s0 N) = true)
    (hc : closedB N L = true) (hg : L.all (goodB N) = true) {s : Nat} (hs : Reach N s) :
    goodB N s = true :=
  List.all_eq_true.1 hg _ (List.contains_iff_mem.1 (cert_sound h0 hc hs))

/-- What `goodB` says, unpacked. -/
structure Good (N s : Nat) : Prop where
  two      : Dl N s = 0 ∨ Dl N s = 2
  preEntry : bit s (CNT N) = false → Dl N s = 0
  looping  : bit s (SM N) = true → bit s (EX N) = false → Dl N s = 2 ∧ ∃ g, g ∈ gates N ∧ excB N s g = true
  stop     : anyExc N s = false → envSucc N s = [] → bit s (EX N) = true ∧ Dl N s = 0
  persist  : ∀ g h, g ∈ gates N → h ∈ gates N → g ≠ h → excB N s g = true → excB N s h = true →
               excB N (flip s g) h = true

theorem good_of {N s : Nat} (h : goodB N s = true) : Good N s := by
  unfold goodB at h
  simp only [Bool.and_eq_true, Bool.or_eq_true, beq_iff_eq, Bool.not_eq_true',
    List.all_eq_true] at h
  obtain ⟨⟨⟨⟨h1, h2⟩, h3⟩, h4⟩, h5⟩ := h
  refine ⟨h1, ?_, ?_, ?_, ?_⟩
  · intro hc; rcases h2 with h | h
    · rw [hc] at h; exact absurd h (by decide)
    · exact h
  · intro hsm hex
    rcases h3 with h | h
    · simp [hsm, hex] at h
    · refine ⟨h.1, ?_⟩
      have := h.2; unfold anyExc at this
      obtain ⟨g, hg, he⟩ := List.any_eq_true.1 this
      exact ⟨g, hg, he⟩
  · intro ha he
    rcases h4 with (h | h) | h
    · rw [ha] at h; exact absurd h (by decide)
    · rw [he] at h; exact absurd h (by decide)
    · exact h
  · intro g k hg hk hne heg hek
    have := h5 g hg k hk
    rcases this with ((h | h) | h) | h
    · exact absurd h hne
    · rw [heg] at h; exact absurd h (by decide)
    · rw [hek] at h; exact absurd h (by decide)
    · exact h

/-! ### Witness runs (for the dead small rings) -/

/-- `pathB N s p`: each state of `p` is a successor of the previous one. -/
def pathB (N : Nat) : Nat → List Nat → Bool
  | _, [] => true
  | s, t :: p => (succ N s).contains t && pathB N t p

def lastOf : Nat → List Nat → Nat
  | s, [] => s
  | _, t :: p => lastOf t p

theorem reach_path {N : Nat} : ∀ {p : List Nat} {s : Nat}, Reach N s → pathB N s p = true →
    Reach N (lastOf s p) := by
  intro p
  induction p with
  | nil => intro s hs _; exact hs
  | cons t p ih =>
    intro s hs h
    simp only [pathB, Bool.and_eq_true] at h
    exact ih (Reach.step hs (List.contains_iff_mem.1 h.1)) h.2

/-- A reachable deadlock that is not the clean "token has left" stop. -/
def stuckB (N s : Nat) : Bool := !anyExc N s && (envSucc N s).isEmpty && !bit s (EX N)

theorem stuck_of {N s : Nat} (h : stuckB N s = true) :
    (∀ g, g ∈ gates N → excB N s g = false) ∧ succ N s = [] ∧ bit s (EX N) = false := by
  unfold stuckB anyExc at h
  simp only [Bool.and_eq_true, Bool.not_eq_true', List.isEmpty_iff] at h
  obtain ⟨⟨h1, h2⟩, h3⟩ := h
  have hall : ∀ g, g ∈ gates N → excB N s g = false := by
    intro g hg
    cases e : excB N s g
    · rfl
    · have : (gates N).any (excB N s) = true := List.any_eq_true.2 ⟨g, hg, e⟩
      rw [this] at h1; exact absurd h1 (by decide)
  refine ⟨hall, ?_, h3⟩
  unfold succ
  rw [h2, List.append_nil]
  have : (gates N).filter (excB N s) = [] := List.filter_eq_nil_iff.2 (fun g hg => by simp [hall g hg])
  rw [this]; rfl

end Formal.Net.RingReset
