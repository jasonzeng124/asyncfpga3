import Formal.Cells.LibCtlMergeMux

/-!
# Probe Lib3: `bd_merge` and `bd_mux` at the handshake level (speed independence)

Cells (`cells/rtl/bd_merge.v`, `cells/rtl/bd_mux.v`), every gate evaluated from
its real INIT through Lib1's definitions (`Formal.Cells.LibCtlMergeMux`):
`or2B` (LUT2 `E`: `uor`, `usel`), `c2B` (`bd_c2`, `00E8_00E8_00E8_00E8`:
`uxa`, `uya`), `j0B`/`j1B` (`uj0` `0000_AE08_0000_AE08`, `uj1`
`0000_EA80_0000_EA80`, own output fed back to `I3`). `rst` is tied to 0
(states start at the reset values: all wires low).

## Model (same style as `LinkHandshake` Section 3)

A state is a `Nat` of bits. Interleaving semantics: one variable changes per
step. A gate variable is *excited* when its LUT (read on its pins) differs from
its output; firing sets it to the LUT value (atomic gate, own feedback pin
read with no delay = `H_FB_FAST` of LinkHandshake / CElemTiming). A fork
branch is its own variable copying its driver with an unbounded delay; a fork
declared *isochronic* has its readers read the driver node directly (its branch
variables are then frozen at 0 and unused). `bd_delay` (`either -> z_req`) is
one buffer variable. Environment: four-phase clients and a four-phase server
(`z_ack` copies `z_req`) that MAY move whenever their protocol allows; the
named environment hypotheses are scheduling filters (`allow`), i.e. trace-level
constraints: a run is admissible iff each step it takes satisfies them in the
state where it is taken.

Checked per reachable state (a kernel-checked over-approximation `STree` of
the reachable set: contains reset, closed under every allowed step):
* **spec** (refinement): every allowed step is a step of the cell's
  specification automaton, kept in ghost bits above the wires: which client
  owns the current server transaction (`o`), and per client whether the server
  has acknowledged that client's token (`gx`, `gy`; mux also `gk`, the control
  token consumed). In words: `z_req` rises only for exactly one requesting
  client (merge) / for the client selected by `s` with `ctl_req` high (mux); a
  client's acknowledge rises only after the server acknowledged *that* client's
  token, and falls only after the server's transaction returned to zero.
  Hence every server transaction acknowledges exactly the client that
  requested it, and nothing else.
* **persistence** (no hazard): an excited gate or wire stays excited when any
  other allowed step fires. Exempt: the data-path select cone (merge `sel` and
  its two input branches; mux `s` at `uj0`/`uj1`/datamux, see below), which is
  data, allowed to glitch, and covered by `H_BUNDLED_Z` / `H_BUNDLED_S`.
* **liveness**: some allowed step other than a free toggle of `s` is enabled.
* **data**: while the server samples, the data-mux select names the owner.
  `early` window: `z_req = 1, z_ack = 0`; `broad` window: `z_req = 1` or
  `z_ack = 1` (the library's convention, data held until the acknowledge falls).
-/

namespace Formal.Cells.MergeMuxSI
open Formal.Cells Formal.Cells.LibCtlMergeMux

/-! ## 0. Generic finite checker -/

/-- A search tree of states (keys are state `Nat`s). -/
inductive STree where
  | leaf
  | node (l : STree) (k : Nat) (r : STree)

namespace STree
def mem : STree → Nat → Bool
  | leaf, _ => false
  | node l k r, s => if s < k then mem l s else if k < s then mem r s else true

def all (p : Nat → Bool) : STree → Bool
  | leaf => true
  | node l k r => all p l && p k && all p r

theorem all_mem {p : Nat → Bool} {t : STree} {s : Nat} (ha : all p t = true)
    (hm : mem t s = true) : p s = true := by
  induction t with
  | leaf => simp [mem] at hm
  | node l k r ihl ihr =>
    simp only [all, Bool.and_eq_true] at ha
    simp only [mem] at hm
    by_cases h1 : s < k
    · simp only [h1, ite_true] at hm; exact ihl ha.1.1 hm
    · by_cases h2 : k < s
      · simp only [h1, h2, ite_true, ite_false] at hm; exact ihr ha.2 hm
      · have : s = k := by omega
        subst this; exact ha.1.2
end STree

/-- A finite interleaving model. Variables `0 .. V-1` are wires/gates; bits
above are ghost state written only by `fire`. -/
structure Sys where
  V : Nat
  nx : Nat → Nat → Bool
  allow : Nat → Nat → Bool
  fire : Nat → Nat → Nat
  spec : Nat → Nat → Bool
  good : Nat → Bool
  hz : Nat → Bool
  live : Nat → Bool

namespace Sys
def ex (m : Sys) (s v : Nat) : Bool := m.nx s v != s.testBit v
/-- Variable `v` may fire in `s`: it exists, is excited, and the environment
hypotheses allow it. -/
def can (m : Sys) (s v : Nat) : Bool := decide (v < m.V) && m.ex s v && m.allow s v

/-- Reachable from reset (state `0`: every wire, gate and ghost low). -/
inductive Reach (m : Sys) : Nat → Prop
  | init : Reach m 0
  | step {s v} : Reach m s → m.can s v = true → Reach m (m.fire s v)

def rng (n : Nat) (p : Nat → Bool) : Bool := (List.range n).all p

theorem rng_spec {n p} (h : rng n p = true) {k} (hk : k < n) : p k = true :=
  List.all_eq_true.1 h k (List.mem_range.2 hk)

def okSt (m : Sys) (T : STree) (s : Nat) : Bool :=
  rng m.V (fun u => !m.can s u || (T.mem (m.fire s u) && m.spec s u &&
     rng m.V (fun v => u == v || !m.hz v || !m.ex s v || m.ex (m.fire s u) v))) &&
  (List.range m.V).any (fun v => m.live v && m.can s v) &&
  m.good s

def check (m : Sys) (T : STree) : Bool := T.mem 0 && T.all (m.okSt T)

/-- The properties a successful check gives in a reachable state. -/
structure Props (m : Sys) (s : Nat) : Prop where
  /-- Every allowed step is a step of the specification automaton. -/
  spec : ∀ u, m.can s u = true → m.spec s u = true
  /-- No hazard: firing `u` never withdraws the excitation of another
  (non-exempt) variable. -/
  persist : ∀ u v, m.can s u = true → v < m.V → u ≠ v → m.hz v = true →
    m.ex s v = true → m.ex (m.fire s u) v = true
  /-- No deadlock. -/
  live : ∃ v, m.live v = true ∧ m.can s v = true
  /-- The data-select invariant. -/
  good : m.good s = true

theorem can_lt {m : Sys} {s u} (h : m.can s u = true) : u < m.V := by
  simp only [can, Bool.and_eq_true, decide_eq_true_eq] at h; exact h.1.1

theorem sound {m : Sys} {T : STree} (hc : m.check T = true) {s} (h : Reach m s) :
    T.mem s = true ∧ Props m s := by
  simp only [check, Bool.and_eq_true] at hc
  obtain ⟨h0, hall⟩ := hc
  have key : ∀ {s}, T.mem s = true → Props m s ∧
      (∀ u, m.can s u = true → T.mem (m.fire s u) = true) := by
    intro s hm
    have hok := STree.all_mem hall hm
    simp only [okSt, Bool.and_eq_true] at hok
    obtain ⟨⟨hA, hL⟩, hG⟩ := hok
    have per : ∀ u, m.can s u = true → (T.mem (m.fire s u) = true ∧ m.spec s u = true) ∧
        rng m.V (fun v => u == v || !m.hz v || !m.ex s v || m.ex (m.fire s u) v) = true := by
      intro u hu
      have := rng_spec hA (can_lt hu)
      simpa [hu, Bool.and_eq_true] using this
    refine ⟨⟨fun u hu => (per u hu).1.2, ?_, ?_, hG⟩, fun u hu => (per u hu).1.1⟩
    · intro u v hu hv huv hz hex
      have := rng_spec (per u hu).2 hv
      simpa [huv, hz, hex] using this
    · obtain ⟨v, hv, hvv⟩ := List.any_eq_true.1 hL
      simp only [Bool.and_eq_true] at hvv
      exact ⟨v, hvv.1, hvv.2⟩
  induction h with
  | init => exact ⟨h0, (key h0).1⟩
  | step _ hc ih =>
    have hm := (key ih.1).2 _ hc
    exact ⟨hm, (key hm).1⟩

/-- Replay a run (a list of fired variables) from a state; `none` if some
step is not allowed. -/
def run (m : Sys) : List Nat → Nat → Option Nat
  | [], s => some s
  | v :: vs, s => if m.can s v then run m vs (m.fire s v) else none

theorem run_reach {m : Sys} : ∀ (p : List Nat) {s t}, Reach m s → run m p s = some t → Reach m t
  | [], _, _, h, hr => by simp [run] at hr; exact hr ▸ h
  | v :: vs, s, t, h, hr => by
    simp only [run] at hr
    by_cases hc : m.can s v = true
    · simp only [hc, ite_true] at hr; exact run_reach vs (Reach.step h hc) hr
    · simp [hc] at hr
end Sys

/-! ## Bit helpers -/

def tb (s i : Nat) : Bool := s.testBit i
/-- Overwrite bit `i` with `b`. -/
def setB (t i : Nat) (b : Bool) : Nat := if t.testBit i == b then t else t ^^^ 2 ^ i
/-- The 2-bit owner field at bit `p`. -/
def getO (p s : Nat) : Nat := (s >>> p) % 4
def setO (p t o : Nat) : Nat := t - getO p t * 2 ^ p + o * 2 ^ p

/-! ## 1. `bd_merge`

Variables (bit = index):
`0 x_req` (client x), `1 y_req` (client y),
`2 xr@uor 3 xr@uxa 4 xr@usel` (branches of x_req), `5 yr@uor 6 yr@uya`,
`7 either` (`uor`), `8 z_req` (`bd_delay` output), `9 z_ack` (server),
`10 za@uxa 11 za@uya`, `12 x_ack` (`uxa`), `13 y_ack` (`uya`),
`14 xa@usel 15 xa@client-x`, `16 sel` (`usel`).
Ghosts: `17-18 o` (0 none, 1 x, 2 y), `19 gx`, `20 gy`.
Fork groups: `xr` {2,3,4}, `yr` {5,6}, `za` {10,11}, `xa` {14,15}. -/

/-- Which merge forks are isochronic. -/
structure MIso where
  xr : Bool
  yr : Bool
  za : Bool
  xa : Bool

def mRd (iso : Bool) (s branch node : Nat) : Bool := if iso then tb s node else tb s branch

def mNx (I : MIso) (s v : Nat) : Bool :=
  if v = 0 then (if tb s 0 == mRd I.xa s 15 12 then !tb s 0 else tb s 0)   -- client x, four-phase
  else if v = 1 then (if tb s 1 == tb s 13 then !tb s 1 else tb s 1)       -- client y, four-phase
  else if v = 2 ∨ v = 3 ∨ v = 4 then (if I.xr then tb s v else tb s 0)
  else if v = 5 ∨ v = 6 then (if I.yr then tb s v else tb s 1)
  else if v = 7 then or2B (mRd I.xr s 2 0) (mRd I.yr s 5 1)                -- uor
  else if v = 8 then tb s 7                                                  -- bd_delay
  else if v = 9 then tb s 8                                                  -- server
  else if v = 10 ∨ v = 11 then (if I.za then tb s v else tb s 9)
  else if v = 12 then c2B (mRd I.xr s 3 0) (mRd I.za s 10 9) (tb s 12) false  -- uxa
  else if v = 13 then c2B (mRd I.yr s 6 1) (mRd I.za s 11 9) (tb s 13) false  -- uya
  else if v = 14 ∨ v = 15 then (if I.xa then tb s v else tb s 12)
  else if v = 16 then or2B (mRd I.xr s 4 0) (mRd I.xa s 14 12)             -- usel
  else tb s v

def mEx (I : MIso) (s v : Nat) : Bool := mNx I s v != tb s v

/-- **H_MERGE_SEQ** (trace-level environment constraint): a client raises its
request only when the OTHER client's request and acknowledge are both low,
i.e. the other client's transaction has fully completed (its acknowledge has
fallen). Read on the wires themselves (the earliest instant any outside path
could react), which is the most adversarial reading. Physical source: the
program's control structure (the merge is emitted only where its two inputs are
mutually sequenced). Test: GLS/board, assert at each `x_req`/`y_req` rise that
the other channel is idle (both wires low). -/
def H_MERGE_SEQ (s v : Nat) : Bool :=
  if v = 0 ∧ tb s 0 = false then !tb s 1 && !tb s 13
  else if v = 1 ∧ tb s 1 = false then !tb s 0 && !tb s 12
  else true

/-- **H_BUNDLED_Z** (merge, the matched `bd_delay`): `z_req` rises only after
the select cone has settled: `usel` and both of its input branches (`xr@usel`,
`xa@usel`) are quiescent. Physically: `bd_delay`'s DELAY covers the data path
through `usel` and the data mux. The `xa@usel` conjunct also asks that a
previous x transaction's `x_ack` fall has reached `usel` (relative timing on
the `x_ack` fork, with the whole delay line as slack). Test: rule A / GLS
"z_data valid at z_req". -/
def H_BUNDLED_Z_M (I : MIso) (s v : Nat) : Bool :=
  if v = 8 ∧ tb s 8 = false then !mEx I s 16 && !mEx I s 4 && !mEx I s 14 else true

def mCandX (s : Nat) : Bool := tb s 0 && !tb s 12 && !tb s 19
def mCandY (s : Nat) : Bool := tb s 1 && !tb s 13 && !tb s 20

def mFire (s v : Nat) : Nat :=
  let t := s ^^^ 2 ^ v
  if v = 8 then (if tb s 8 then t else setO 17 t (if mCandX s then 1 else 2))
  else if v = 9 then
    (if tb s 9 then setO 17 t 0
     else if getO 17 s = 1 then setB t 19 true
     else if getO 17 s = 2 then setB t 20 true else t)
  else if v = 12 then (if tb s 12 then setB t 19 false else t)
  else if v = 13 then (if tb s 13 then setB t 20 false else t)
  else t

/-- The merge specification automaton (see the module doc). -/
def mSpec (s v : Nat) : Bool :=
  let o := getO 17 s
  if v = 8 then
    (if tb s 8 = false then o == 0 && !tb s 9 && (mCandX s != mCandY s)
     else o != 0 && tb s 9 && !(if o == 1 then tb s 0 else tb s 1))
  else if v = 9 then
    (if tb s 9 = false then tb s 8 && o != 0 && !tb s (if o == 1 then 19 else 20)
     else !tb s 8)
  else if v = 12 then
    (if tb s 12 = false then tb s 19 && tb s 0 else tb s 19 && !tb s 0 && o != 1)
  else if v = 13 then
    (if tb s 13 = false then tb s 20 && tb s 1 else tb s 20 && !tb s 1 && o != 2)
  else true

/-- Data: in the window, `sel` names the owner. -/
def mGood (broad : Bool) (s : Nat) : Bool :=
  let o := getO 17 s
  let w := if broad then tb s 8 || tb s 9 else tb s 8 && !tb s 9
  !w || (o != 0 && (tb s 16 == (o == 1)))

def merge (I : MIso) (seq broad : Bool) : Sys where
  V := 17
  nx := mNx I
  allow := fun s v => (!seq || H_MERGE_SEQ s v) && H_BUNDLED_Z_M I s v
  fire := mFire
  spec := mSpec
  good := mGood broad
  hz := fun v => !(v == 16 || v == 4 || v == 14)
  live := fun _ => true

/-- Isochronic: only `z_ack` and `x_ack`. -/
def mIsoA : MIso := ⟨false, false, true, true⟩
/-- Isochronic: only `z_ack`. -/
def mIsoB : MIso := ⟨false, false, true, false⟩
def mIsoAll : MIso := ⟨true, true, true, true⟩
/-- Every fork isochronic except `z_ack`'s. -/
def mIsoNoZa : MIso := ⟨true, true, false, true⟩

def TmA : STree := (.node (.node (.node (.node (.node (.node (.node .leaf 0 .leaf) 1 .leaf) 2 (.node (.node .leaf 5 .leaf) 9 .leaf)) 13 (.node (.node (.node .leaf 17 .leaf) 21 .leaf) 25 (.node .leaf 29 .leaf))) 34 (.node (.node (.node (.node .leaf 66 .leaf) 98 .leaf) 133 (.node (.node .leaf 141 .leaf) 149 .leaf)) 157 (.node (.node (.node .leaf 162 .leaf) 226 .leaf) 65536 (.node .leaf 65537 .leaf)))) 65538 (.node (.node (.node (.node (.node .leaf 65541 .leaf) 65545 .leaf) 65549 (.node (.node .leaf 65552 .leaf) 65553 .leaf)) 65554 (.node (.node (.node .leaf 65557 .leaf) 65561 .leaf) 65565 (.node .leaf 65570 .leaf))) 65586 (.node (.node (.node (.node .leaf 65602 .leaf) 65618 .leaf) 65634 (.node .leaf 65650 .leaf)) 65669 (.node (.node (.node .leaf 65677 .leaf) 65685 .leaf) 65693 (.node .leaf 65698 .leaf))))) 65714 (.node (.node (.node (.node (.node (.node .leaf 65762 .leaf) 65778 .leaf) 197013 (.node (.node .leaf 197021 .leaf) 262562 .leaf)) 262626 (.node (.node (.node .leaf 593920 .leaf) 593928 .leaf) 593936 (.node .leaf 593944 .leaf))) 721813 (.node (.node (.node (.node .leaf 721821 .leaf) 725504 .leaf) 725512 (.node (.node .leaf 725520 .leaf) 725528 .leaf)) 725760 (.node (.node (.node .leaf 725768 .leaf) 725776 .leaf) 725784 (.node .leaf 725888 .leaf)))) 725892 (.node (.node (.node (.node (.node .leaf 725896 .leaf) 725900 .leaf) 725904 (.node (.node .leaf 725908 .leaf) 725912 .leaf)) 725916 (.node (.node (.node .leaf 725917 .leaf) 1056768 .leaf) 1056832 (.node .leaf 1311650 .leaf))) 1311714 (.node (.node (.node (.node .leaf 1319424 .leaf) 1319488 .leaf) 1319680 (.node .leaf 1319744 .leaf)) 1319808 (.node (.node (.node .leaf 1319840 .leaf) 1319872 .leaf) 1319904 (.node .leaf 1319906 .leaf))))))

theorem mergeA_check : (merge mIsoA true true).check TmA = true := by decide +kernel

/-- **bd_merge is speed independent and correct (broad data window)** under
H_MERGE_SEQ and H_BUNDLED_Z, with unbounded gate and wire delays on every fork
branch except two isochronic forks: `z_ack -> {uxa, uya}` and
`x_ack -> {usel, client x}`. Every reachable state: every step is a spec step
(each server transaction acknowledges exactly its requester), no hazard,
no deadlock, `sel` names the owner whenever `z_req` or `z_ack` is high. The
`x_req` and `y_req` forks need no isochrony. -/
theorem merge_ok {s} (h : (merge mIsoA true true).Reach s) :
    Sys.Props (merge mIsoA true true) s := (Sys.sound mergeA_check h).2

def TmB : STree := (.node (.node (.node (.node (.node (.node (.node (.node .leaf 0 .leaf) 1 (.node .leaf 2 .leaf)) 5 (.node (.node .leaf 9 .leaf) 13 (.node .leaf 17 .leaf))) 21 (.node (.node (.node .leaf 25 .leaf) 29 (.node .leaf 34 .leaf)) 66 (.node (.node .leaf 98 .leaf) 133 .leaf))) 141 (.node (.node (.node (.node .leaf 149 .leaf) 157 (.node .leaf 162 .leaf)) 226 (.node (.node .leaf 16384 .leaf) 16385 .leaf)) 16386 (.node (.node (.node .leaf 16389 .leaf) 16393 (.node .leaf 16397 .leaf)) 16401 (.node (.node .leaf 16405 .leaf) 16409 .leaf)))) 16413 (.node (.node (.node (.node (.node .leaf 16418 .leaf) 16450 (.node .leaf 16482 .leaf)) 16517 (.node (.node .leaf 16525 .leaf) 16533 (.node .leaf 16541 .leaf))) 16546 (.node (.node (.node .leaf 16610 .leaf) 32768 (.node .leaf 32770 .leaf)) 32802 (.node (.node .leaf 32834 .leaf) 32866 .leaf))) 32930 (.node (.node (.node (.node .leaf 32994 .leaf) 49152 (.node .leaf 49154 .leaf)) 49186 (.node (.node .leaf 49218 .leaf) 49250 .leaf)) 49314 (.node (.node (.node .leaf 49378 .leaf) 65536 (.node .leaf 65537 .leaf)) 65538 (.node (.node .leaf 65541 .leaf) 65545 .leaf))))) 65549 (.node (.node (.node (.node (.node (.node .leaf 65552 .leaf) 65553 (.node .leaf 65554 .leaf)) 65557 (.node (.node .leaf 65561 .leaf) 65565 (.node .leaf 65570 .leaf))) 65586 (.node (.node (.node .leaf 65602 .leaf) 65618 (.node .leaf 65634 .leaf)) 65650 (.node (.node .leaf 65669 .leaf) 65677 .leaf))) 65685 (.node (.node (.node (.node .leaf 65693 .leaf) 65698 (.node .leaf 65714 .leaf)) 65762 (.node (.node .leaf 65778 .leaf) 81920 .leaf)) 81921 (.node (.node (.node .leaf 81922 .leaf) 81925 (.node .leaf 81929 .leaf)) 81933 (.node (.node .leaf 81936 .leaf) 81937 .leaf)))) 81938 (.node (.node (.node (.node (.node .leaf 81941 .leaf) 81945 (.node .leaf 81949 .leaf)) 81954 (.node (.node .leaf 81970 .leaf) 81986 (.node .leaf 82002 .leaf))) 82018 (.node (.node (.node .leaf 82034 .leaf) 82053 (.node .leaf 82061 .leaf)) 82069 (.node (.node .leaf 82077 .leaf) 82082 .leaf))) 82098 (.node (.node (.node (.node .leaf 82146 .leaf) 82162 (.node .leaf 98304 .leaf)) 98306 (.node (.node .leaf 98320 .leaf) 98322 .leaf)) 98338 (.node (.node (.node .leaf 98354 .leaf) 98370 (.node .leaf 98386 .leaf)) 98402 (.node (.node .leaf 98418 .leaf) 98466 .leaf)))))) 98482 (.node (.node (.node (.node (.node (.node (.node .leaf 98530 .leaf) 98546 (.node .leaf 114688 .leaf)) 114690 (.node (.node .leaf 114704 .leaf) 114706 (.node .leaf 114722 .leaf))) 114738 (.node (.node (.node .leaf 114754 .leaf) 114770 (.node .leaf 114786 .leaf)) 114802 (.node (.node .leaf 114850 .leaf) 114866 .leaf))) 114914 (.node (.node (.node (.node .leaf 114930 .leaf) 197013 (.node .leaf 197021 .leaf)) 262562 (.node (.node .leaf 262626 .leaf) 295330 .leaf)) 295394 (.node (.node (.node .leaf 561152 .leaf) 561160 (.node .leaf 577536 .leaf)) 577544 (.node (.node .leaf 626688 .leaf) 626696 .leaf)))) 626704 (.node (.node (.node (.node (.node .leaf 626712 .leaf) 643072 (.node .leaf 643080 .leaf)) 643088 (.node (.node .leaf 643096 .leaf) 692736 (.node .leaf 692744 .leaf))) 692992 (.node (.node (.node .leaf 693000 .leaf) 693120 (.node .leaf 693124 .leaf)) 693128 (.node (.node .leaf 693132 .leaf) 709120 .leaf))) 709128 (.node (.node (.node (.node .leaf 709376 .leaf) 709384 (.node .leaf 709504 .leaf)) 709508 (.node (.node .leaf 709512 .leaf) 709516 .leaf)) 721813 (.node (.node (.node .leaf 721821 .leaf) 725917 (.node .leaf 742301 .leaf)) 758272 (.node (.node .leaf 758280 .leaf) 758288 .leaf))))) 758296 (.node (.node (.node (.node (.node (.node .leaf 758528 .leaf) 758536 (.node .leaf 758544 .leaf)) 758552 (.node (.node .leaf 758656 .leaf) 758660 (.node .leaf 758664 .leaf))) 758668 (.node (.node (.node .leaf 758672 .leaf) 758676 (.node .leaf 758680 .leaf)) 758684 (.node (.node .leaf 758685 .leaf) 774656 .leaf))) 774664 (.node (.node (.node (.node .leaf 774672 .leaf) 774680 (.node .leaf 774912 .leaf)) 774920 (.node (.node .leaf 774928 .leaf) 774936 .leaf)) 775040 (.node (.node (.node .leaf 775044 .leaf) 775048 (.node .leaf 775052 .leaf)) 775056 (.node (.node .leaf 775060 .leaf) 775064 .leaf)))) 775068 (.node (.node (.node (.node (.node .leaf 775069 .leaf) 1056768 (.node .leaf 1056832 .leaf)) 1089536 (.node (.node .leaf 1089600 .leaf) 1311650 .leaf)) 1311714 (.node (.node (.node .leaf 1319424 .leaf) 1319488 (.node .leaf 1319680 .leaf)) 1319744 (.node (.node .leaf 1319808 .leaf) 1319840 .leaf))) 1319872 (.node (.node (.node (.node .leaf 1319904 .leaf) 1319906 (.node .leaf 1344418 .leaf)) 1344482 (.node (.node .leaf 1352192 .leaf) 1352256 .leaf)) 1352448 (.node (.node (.node .leaf 1352512 .leaf) 1352576 (.node .leaf 1352608 .leaf)) 1352640 (.node (.node .leaf 1352672 .leaf) 1352674 .leaf)))))))

theorem mergeB_check : (merge mIsoB true false).check TmB = true := by decide +kernel

/-- **Only the `z_ack` fork isochronic, early data window:** the same, with
the data claim weakened to the window `z_req = 1, z_ack = 0`. -/
theorem merge_ok_early {s} (h : (merge mIsoB true false).Reach s) :
    Sys.Props (merge mIsoB true false) s := (Sys.sound mergeB_check h).2

/-- **...but the broad window needs the `x_ack` fork.** A run (only `z_ack`
isochronic) in which `x_ack@usel` lags behind `x_ack@client`: client x sees its
acknowledge, drops `x_req`, and `sel` falls while `z_ack` is still high: the
select changes before the acknowledge falls ("the select cannot be the
request", reappearing through the fork). -/
theorem merge_broad_needs_iso_xa :
    ∃ s, (merge mIsoB true false).Reach s ∧ mGood true s = false :=
  ⟨693132, Sys.run_reach [0, 2, 3, 4, 7, 16, 8, 9, 12, 15, 0, 4, 16] Sys.Reach.init (by decide +kernel), by decide⟩

/-- **Without H_MERGE_SEQ the merge acknowledges a token it never carried**
(even with every fork isochronic): y's transaction is in flight (`z_req`
high), x raises its request, the server acknowledges, and `x_ack = C(x_req,
z_ack)` is excited and allowed although the server acknowledged y's token
(spec step fails). This is the header's obligation. -/
theorem merge_needs_seq :
    ∃ s, (merge mIsoAll false true).Reach s ∧ (merge mIsoAll false true).can s 12 = true ∧
      mSpec s 12 = false :=
  ⟨1311619, Sys.run_reach [1, 7, 8, 0, 9] Sys.Reach.init (by decide +kernel),
    by decide +kernel, by decide⟩

/-- **H_ISO_FORK is needed on `z_ack -> {uxa, uya}`** (every other fork
isochronic, H_MERGE_SEQ and H_BUNDLED_Z assumed): in a y transaction
`za@uxa` follows `z_ack`'s rise but not yet its fall; y completes (`y_ack`
falls), x then starts legally (y idle), and `x_ack` fires on the stale
`z_ack`: a spurious acknowledge. -/
theorem merge_needs_iso_za :
    ∃ s, (merge mIsoNoZa true true).Reach s ∧ (merge mIsoNoZa true true).can s 12 = true ∧
      mSpec s 12 = false :=
  ⟨1025, Sys.run_reach [1, 7, 8, 9, 10, 11, 13, 1, 7, 8, 9, 11, 13, 0] Sys.Reach.init (by decide +kernel),
    by decide +kernel, by decide⟩

/-! ## 2. `bd_mux`

Variables: `0 x_req 1 y_req 2 ctl_req 3 s` (environment; `s` is the control
token's data bit), `4 s@uj0 5 s@uj1 6 s@datamux`, `7 cr@uj0 8 cr@uj1`,
`9 j0` (`uj0`) `10 j1` (`uj1`), `11 j0@uor 12 j0@uxa 13 j1@uor 14 j1@uya`,
`15 either` (`uor`), `16 z_req` (`bd_delay`), `17 z_ack` (server),
`18 za@uxa 19 za@uya 20 za@ctl (ctl_ack)`, `21 x_ack 22 y_ack`.
Ghosts: `23-24 o`, `25 gx`, `26 gy`, `27 gk` (control token consumed).
Fork groups: `s` {4,5,6}, `cr` {7,8}, `j0` {11,12}, `j1` {13,14}, `za` {18,19,20}. -/

structure XIso where
  s : Bool
  cr : Bool
  j0 : Bool
  j1 : Bool
  za : Bool

/-- What pin `b` reads (the branch, or the driver if the fork is isochronic). -/
def xRd (I : XIso) (s b : Nat) : Bool :=
  if b = 4 ∨ b = 5 ∨ b = 6 then (if I.s then tb s 3 else tb s b)
  else if b = 7 ∨ b = 8 then (if I.cr then tb s 2 else tb s b)
  else if b = 11 ∨ b = 12 then (if I.j0 then tb s 9 else tb s b)
  else if b = 13 ∨ b = 14 then (if I.j1 then tb s 10 else tb s b)
  else if b = 18 ∨ b = 19 ∨ b = 20 then (if I.za then tb s 17 else tb s b)
  else tb s b

def xNx (I : XIso) (s v : Nat) : Bool :=
  if v = 0 then (if tb s 0 == tb s 21 then !tb s 0 else tb s 0)            -- client x
  else if v = 1 then (if tb s 1 == tb s 22 then !tb s 1 else tb s 1)       -- client y
  else if v = 2 then (if tb s 2 == xRd I s 20 then !tb s 2 else tb s 2)    -- ctl client
  else if v = 3 then !tb s 3                                               -- s: free data bit
  else if v = 4 ∨ v = 5 ∨ v = 6 then (if I.s then tb s v else tb s 3)
  else if v = 7 ∨ v = 8 then (if I.cr then tb s v else tb s 2)
  else if v = 9 then j0B (tb s 0) (xRd I s 7) (xRd I s 4) (tb s 9) false    -- uj0
  else if v = 10 then j1B (tb s 1) (xRd I s 8) (xRd I s 5) (tb s 10) false  -- uj1
  else if v = 11 ∨ v = 12 then (if I.j0 then tb s v else tb s 9)
  else if v = 13 ∨ v = 14 then (if I.j1 then tb s v else tb s 10)
  else if v = 15 then or2B (xRd I s 11) (xRd I s 13)                        -- uor
  else if v = 16 then tb s 15                                               -- bd_delay
  else if v = 17 then tb s 16                                               -- server
  else if v = 18 ∨ v = 19 ∨ v = 20 then (if I.za then tb s v else tb s 17)
  else if v = 21 then c2B (xRd I s 12) (xRd I s 18) (tb s 21) false          -- uxa
  else if v = 22 then c2B (xRd I s 14) (xRd I s 19) (tb s 22) false          -- uya
  else tb s v

def xEx (I : XIso) (s v : Nat) : Bool := xNx I s v != tb s v

/-- **H_BUNDLED_S, sender side** (trace-level, on the control channel), in two
strengths: `hs = 1` (the probe brief's form): `s` changes only while
`ctl_req` is low; `hs = 2` (the header's form): `s` changes only while
`ctl_req` is low and the control sender sees `ctl_ack` low, i.e. `s` is held
from before `ctl_req` rises until `ctl_ack` falls. `hs = 0`: no constraint.
Test: GLS assertion on the control channel of every emitted bd_mux. -/
def H_CTL_HOLD (hs : Nat) (I : XIso) (s v : Nat) : Bool :=
  if v = 3 then (hs == 0 || !tb s 2) && (hs != 2 || !xRd I s 20) else true

/-- **H_BUNDLED_S, receiver pins** (wire timing): at each join, the `s` pin
settles before the `ctl_req` pin rises, and the `s` pin moves only while the
`ctl_req` pin is low. Physically: bundling skew `s -> uj_i` vs
`ctl_req -> uj_i`, setup and hold, at both joins. While the `ctl_req` pin of a
join is low the join ignores its `s` pin (Lib1 `j0_s_free_idle`), which is why
`s@uj0`/`s@uj1` are exempt from the hazard check. -/
def H_BUNDLED_S_PIN (pin : Bool) (I : XIso) (s v : Nat) : Bool :=
  if !pin then true
  else if v = 3 then (!I.s || (!xRd I s 7 && !xRd I s 8))
  else if v = 4 then !xRd I s 7
  else if v = 5 then !xRd I s 8
  else if v = 7 ∧ tb s 7 = false then xRd I s 4 == tb s 3
  else if v = 8 ∧ tb s 8 = false then xRd I s 5 == tb s 3
  else if v = 2 ∧ tb s 2 = false ∧ I.cr = true then xRd I s 4 == tb s 3 && xRd I s 5 == tb s 3
  else true

/-- **H_MUX_RTZ** (relative timing, found by this probe): after `z_ack`
falls, the acknowledge C-element of the previous transaction (`uxa`/`uya`,
excited to fall) fires before `z_ack` rises again at its pin. Without it, the
next transaction (other input, new control token) can raise `z_ack` while
`x_ack` is still falling: `x_ack`'s fall is withdrawn (runt on `x_ack`).
Slack: `z_ack`-fall -> control sender -> `ctl_req` -> join -> `uor` -> DELAY
-> server -> `z_ack`-rise, against one LUT. Test: GLS, min of that loop vs
max `z_ack -> x_ack` fall. -/
def H_MUX_RTZ (rtz : Bool) (I : XIso) (s v : Nat) : Bool :=
  if !rtz then true
  else if v = 17 ∧ tb s 17 = false ∧ I.za = true then !xEx I s 21 && !xEx I s 22
  else if v = 18 ∧ tb s 18 = false ∧ I.za = false then !xEx I s 21
  else if v = 19 ∧ tb s 19 = false ∧ I.za = false then !xEx I s 22
  else true

/-- **H_BUNDLED_Z** (mux): `z_req` rises only after `s@datamux` has settled. -/
def H_BUNDLED_Z_X (I : XIso) (s v : Nat) : Bool :=
  if v = 16 ∧ tb s 16 = false then !xEx I s 6 else true

def xFire (s v : Nat) : Nat :=
  let t := s ^^^ 2 ^ v
  if v = 16 then (if tb s 16 then t else setB (setO 23 t (if tb s 3 then 2 else 1)) 27 true)
  else if v = 17 then
    (if tb s 17 then setB (setO 23 t 0) 27 false
     else if getO 23 s = 1 then setB t 25 true
     else if getO 23 s = 2 then setB t 26 true else t)
  else if v = 21 then (if tb s 21 then setB t 25 false else t)
  else if v = 22 then (if tb s 22 then setB t 26 false else t)
  else t

/-- The mux specification automaton: `z_req` rises only with `ctl_req` high,
an unconsumed control token, and the client SELECTED BY `s` requesting and not
yet served; it falls only after `z_ack`, with the owner's request and
`ctl_req` low (join semantics); client acknowledges as in the merge; the
control sender drops `ctl_req` only after `ctl_ack`. -/
def xSpec (s v : Nat) : Bool :=
  let o := getO 23 s
  if v = 16 then
    (if tb s 16 = false then
       o == 0 && !tb s 17 && tb s 2 && !tb s 27 &&
       (if tb s 3 then tb s 1 && !tb s 22 && !tb s 26 else tb s 0 && !tb s 21 && !tb s 25)
     else o != 0 && tb s 17 && !tb s 2 && !(if o == 1 then tb s 0 else tb s 1))
  else if v = 17 then
    (if tb s 17 = false then tb s 16 && o != 0 && !tb s (if o == 1 then 25 else 26)
     else !tb s 16)
  else if v = 21 then
    (if tb s 21 = false then tb s 25 && tb s 0 else tb s 25 && !tb s 0 && o != 1)
  else if v = 22 then
    (if tb s 22 = false then tb s 26 && tb s 1 else tb s 26 && !tb s 1 && o != 2)
  else if v = 2 then (if tb s 2 then tb s 17 else true)
  else true

def xGood (I : XIso) (broad : Bool) (s : Nat) : Bool :=
  let o := getO 23 s
  let w := if broad then tb s 16 || tb s 17 else tb s 16 && !tb s 17
  !w || (o != 0 && (xRd I s 6 == (o == 2)))

def mux (I : XIso) (hs : Nat) (pin rtz broad : Bool) : Sys where
  V := 23
  nx := xNx I
  allow := fun s v => H_CTL_HOLD hs I s v && H_BUNDLED_S_PIN pin I s v &&
    H_MUX_RTZ rtz I s v && H_BUNDLED_Z_X I s v
  fire := xFire
  spec := xSpec
  good := xGood I broad
  hz := fun v => !(v == 6 || v == 4 || v == 5)
  live := fun v => v != 3

/-- Isochronic: only `ctl_req` and `z_ack`. -/
def xIsoA : XIso := ⟨false, true, false, false, true⟩
def xIsoAll : XIso := ⟨true, true, true, true, true⟩
def xIsoNoZa : XIso := ⟨true, true, true, true, false⟩
def xIsoNoCr : XIso := ⟨true, false, true, true, true⟩

def TxA : STree := (.node (.node (.node (.node (.node (.node (.node (.node (.node (.node .leaf 0 .leaf) 1 .leaf) 2 (.node .leaf 3 .leaf)) 4 (.node (.node .leaf 5 .leaf) 6 (.node .leaf 7 .leaf))) 8 (.node (.node (.node (.node .leaf 9 .leaf) 10 .leaf) 11 (.node .leaf 16 .leaf)) 17 (.node (.node .leaf 18 .leaf) 19 (.node .leaf 24 .leaf)))) 25 (.node (.node (.node (.node (.node .leaf 26 .leaf) 27 .leaf) 32 (.node .leaf 33 .leaf)) 34 (.node (.node .leaf 35 .leaf) 40 (.node .leaf 41 .leaf))) 42 (.node (.node (.node (.node .leaf 43 .leaf) 48 .leaf) 49 (.node .leaf 50 .leaf)) 51 (.node (.node .leaf 56 .leaf) 57 (.node .leaf 58 .leaf))))) 59 (.node (.node (.node (.node (.node (.node .leaf 60 .leaf) 61 .leaf) 62 (.node .leaf 63 .leaf)) 64 (.node (.node .leaf 65 .leaf) 66 (.node .leaf 67 .leaf))) 68 (.node (.node (.node (.node .leaf 69 .leaf) 70 .leaf) 71 (.node .leaf 72 .leaf)) 73 (.node (.node .leaf 74 .leaf) 75 (.node .leaf 80 .leaf)))) 81 (.node (.node (.node (.node (.node .leaf 82 .leaf) 83 .leaf) 88 (.node .leaf 89 .leaf)) 90 (.node (.node .leaf 91 .leaf) 96 (.node .leaf 97 .leaf))) 98 (.node (.node (.node .leaf 99 .leaf) 104 (.node .leaf 105 .leaf)) 106 (.node (.node .leaf 107 .leaf) 112 (.node .leaf 113 .leaf)))))) 114 (.node (.node (.node (.node (.node (.node (.node .leaf 115 .leaf) 120 .leaf) 121 (.node .leaf 122 .leaf)) 123 (.node (.node .leaf 124 .leaf) 125 (.node .leaf 126 .leaf))) 127 (.node (.node (.node (.node .leaf 517 .leaf) 519 .leaf) 581 (.node .leaf 583 .leaf)) 1086 (.node (.node .leaf 1087 .leaf) 1150 (.node .leaf 1151 .leaf)))) 2565 (.node (.node (.node (.node (.node .leaf 2567 .leaf) 2629 .leaf) 2631 (.node .leaf 4613 .leaf)) 4615 (.node (.node .leaf 4677 .leaf) 4679 (.node .leaf 6661 .leaf))) 6663 (.node (.node (.node .leaf 6725 .leaf) 6727 (.node .leaf 9278 .leaf)) 9279 (.node (.node .leaf 9342 .leaf) 9343 (.node .leaf 17470 .leaf))))) 17471 (.node (.node (.node (.node (.node (.node .leaf 17534 .leaf) 17535 .leaf) 25662 (.node .leaf 25663 .leaf)) 25726 (.node (.node .leaf 25727 .leaf) 35333 (.node .leaf 35335 .leaf))) 35397 (.node (.node (.node (.node .leaf 35399 .leaf) 39429 .leaf) 39431 (.node .leaf 39493 .leaf)) 39495 (.node (.node .leaf 42046 .leaf) 42047 (.node .leaf 42110 .leaf)))) 42111 (.node (.node (.node (.node (.node .leaf 58430 .leaf) 58431 .leaf) 58494 (.node .leaf 58495 .leaf)) 35651584 (.node (.node .leaf 35651586 .leaf) 35651588 (.node .leaf 35651590 .leaf))) 35651592 (.node (.node (.node .leaf 35651594 .leaf) 35651600 (.node .leaf 35651602 .leaf)) 35651608 (.node (.node .leaf 35651610 .leaf) 35651616 (.node .leaf 35651618 .leaf))))))) 35651624 (.node (.node (.node (.node (.node (.node (.node (.node .leaf 35651626 .leaf) 35651632 .leaf) 35651634 (.node .leaf 35651640 .leaf)) 35651642 (.node (.node .leaf 35651644 .leaf) 35651646 (.node .leaf 35651648 .leaf))) 35651650 (.node (.node (.node (.node .leaf 35651652 .leaf) 35651654 .leaf) 35651656 (.node .leaf 35651658 .leaf)) 35651664 (.node (.node .leaf 35651666 .leaf) 35651672 (.node .leaf 35651674 .leaf)))) 35651680 (.node (.node (.node (.node (.node .leaf 35651682 .leaf) 35651688 .leaf) 35651690 (.node .leaf 35651696 .leaf)) 35651698 (.node (.node .leaf 35651704 .leaf) 35651706 (.node .leaf 35651708 .leaf))) 35651710 (.node (.node (.node .leaf 35652670 .leaf) 35652734 (.node .leaf 35655680 .leaf)) 35655682 (.node (.node .leaf 35655684 .leaf) 35655686 (.node .leaf 35655688 .leaf))))) 35655690 (.node (.node (.node (.node (.node (.node .leaf 35655696 .leaf) 35655698 .leaf) 35655704 (.node .leaf 35655706 .leaf)) 35655712 (.node (.node .leaf 35655714 .leaf) 35655720 (.node .leaf 35655722 .leaf))) 35655728 (.node (.node (.node (.node .leaf 35655730 .leaf) 35655736 .leaf) 35655738 (.node .leaf 35655740 .leaf)) 35655742 (.node (.node .leaf 35655744 .leaf) 35655746 (.node .leaf 35655748 .leaf)))) 35655750 (.node (.node (.node (.node (.node .leaf 35655752 .leaf) 35655754 .leaf) 35655760 (.node .leaf 35655762 .leaf)) 35655768 (.node (.node .leaf 35655770 .leaf) 35655776 (.node .leaf 35655778 .leaf))) 35655784 (.node (.node (.node .leaf 35655786 .leaf) 35655792 (.node .leaf 35655794 .leaf)) 35655800 (.node (.node .leaf 35655802 .leaf) 35655804 (.node .leaf 35655806 .leaf)))))) 35656766 (.node (.node (.node (.node (.node (.node (.node .leaf 35656830 .leaf) 35660862 .leaf) 35660926 (.node .leaf 35664958 .leaf)) 35665022 (.node (.node .leaf 35669054 .leaf) 35669118 (.node .leaf 35673150 .leaf))) 35673214 (.node (.node (.node (.node .leaf 35677246 .leaf) 35677310 .leaf) 35681342 (.node .leaf 35681406 .leaf)) 35693630 (.node (.node .leaf 35693694 .leaf) 35697726 (.node .leaf 35697790 .leaf)))) 35710014 (.node (.node (.node (.node (.node .leaf 35710078 .leaf) 35714110 .leaf) 35714174 (.node .leaf 71303168 .leaf)) 71303169 (.node (.node .leaf 71303172 .leaf) 71303173 (.node .leaf 71303176 .leaf))) 71303177 (.node (.node (.node .leaf 71303184 .leaf) 71303185 (.node .leaf 71303192 .leaf)) 71303193 (.node (.node .leaf 71303200 .leaf) 71303201 (.node .leaf 71303208 .leaf))))) 71303209 (.node (.node (.node (.node (.node (.node .leaf 71303216 .leaf) 71303217 .leaf) 71303224 (.node .leaf 71303225 .leaf)) 71303228 (.node (.node .leaf 71303229 .leaf) 71303232 (.node .leaf 71303233 .leaf))) 71303236 (.node (.node (.node (.node .leaf 71303237 .leaf) 71303240 .leaf) 71303241 (.node .leaf 71303248 .leaf)) 71303249 (.node (.node .leaf 71303256 .leaf) 71303257 (.node .leaf 71303264 .leaf)))) 71303265 (.node (.node (.node (.node (.node .leaf 71303272 .leaf) 71303273 .leaf) 71303280 (.node .leaf 71303281 .leaf)) 71303288 (.node (.node .leaf 71303289 .leaf) 71303292 (.node .leaf 71303293 .leaf))) 71303685 (.node (.node (.node .leaf 71303749 .leaf) 71305733 (.node .leaf 71305797 .leaf)) 71307781 (.node (.node .leaf 71307845 .leaf) 71309829 (.node .leaf 71309893 .leaf)))))))) 71319552 (.node (.node (.node (.node (.node (.node (.node (.node (.node .leaf 71319553 .leaf) 71319556 .leaf) 71319557 (.node .leaf 71319560 .leaf)) 71319561 (.node (.node .leaf 71319568 .leaf) 71319569 (.node .leaf 71319576 .leaf))) 71319577 (.node (.node (.node (.node .leaf 71319584 .leaf) 71319585 .leaf) 71319592 (.node .leaf 71319593 .leaf)) 71319600 (.node (.node .leaf 71319601 .leaf) 71319608 (.node .leaf 71319609 .leaf)))) 71319612 (.node (.node (.node (.node (.node .leaf 71319613 .leaf) 71319616 .leaf) 71319617 (.node .leaf 71319620 .leaf)) 71319621 (.node (.node .leaf 71319624 .leaf) 71319625 (.node .leaf 71319632 .leaf))) 71319633 (.node (.node (.node .leaf 71319640 .leaf) 71319641 (.node .leaf 71319648 .leaf)) 71319649 (.node (.node .leaf 71319656 .leaf) 71319657 (.node .leaf 71319664 .leaf))))) 71319665 (.node (.node (.node (.node (.node (.node .leaf 71319672 .leaf) 71319673 .leaf) 71319676 (.node .leaf 71319677 .leaf)) 71320069 (.node (.node .leaf 71320133 .leaf) 71322117 (.node .leaf 71322181 .leaf))) 71324165 (.node (.node (.node (.node .leaf 71324229 .leaf) 71326213 .leaf) 71326277 (.node .leaf 71338501 .leaf)) 71338565 (.node (.node .leaf 71342597 .leaf) 71342661 (.node .leaf 71354885 .leaf)))) 71354949 (.node (.node (.node (.node (.node .leaf 71358981 .leaf) 71359045 .leaf) 106954752 (.node .leaf 106954756 .leaf)) 106954760 (.node (.node .leaf 106954768 .leaf) 106954776 (.node .leaf 106954784 .leaf))) 106954792 (.node (.node (.node .leaf 106954800 .leaf) 106954808 (.node .leaf 106954812 .leaf)) 106954816 (.node (.node .leaf 106954820 .leaf) 106954824 (.node .leaf 106954832 .leaf)))))) 106954840 (.node (.node (.node (.node (.node (.node (.node .leaf 106954848 .leaf) 106954856 .leaf) 106954864 (.node .leaf 106954872 .leaf)) 106954876 (.node (.node .leaf 106958848 .leaf) 106958852 (.node .leaf 106958856 .leaf))) 106958864 (.node (.node (.node (.node .leaf 106958872 .leaf) 106958880 .leaf) 106958888 (.node .leaf 106958896 .leaf)) 106958904 (.node (.node .leaf 106958908 .leaf) 106958912 (.node .leaf 106958916 .leaf)))) 106958920 (.node (.node (.node (.node (.node .leaf 106958928 .leaf) 106958936 .leaf) 106958944 (.node .leaf 106958952 .leaf)) 106958960 (.node (.node .leaf 106958968 .leaf) 106958972 (.node .leaf 106971136 .leaf))) 106971140 (.node (.node (.node .leaf 106971144 .leaf) 106971152 (.node .leaf 106971160 .leaf)) 106971168 (.node (.node .leaf 106971176 .leaf) 106971184 (.node .leaf 106971192 .leaf))))) 106971196 (.node (.node (.node (.node (.node (.node .leaf 106971200 .leaf) 106971204 .leaf) 106971208 (.node .leaf 106971216 .leaf)) 106971224 (.node (.node .leaf 106971232 .leaf) 106971240 (.node .leaf 106971248 .leaf))) 106971256 (.node (.node (.node (.node .leaf 106971260 .leaf) 106975232 .leaf) 106975236 (.node .leaf 106975240 .leaf)) 106975248 (.node (.node .leaf 106975256 .leaf) 106975264 (.node .leaf 106975272 .leaf)))) 106975280 (.node (.node (.node (.node (.node .leaf 106975288 .leaf) 106975292 .leaf) 106975296 (.node .leaf 106975300 .leaf)) 106975304 (.node (.node .leaf 106975312 .leaf) 106975320 (.node .leaf 106975328 .leaf))) 106975336 (.node (.node (.node .leaf 106975344 .leaf) 106975352 (.node .leaf 106975356 .leaf)) 142707205 (.node (.node .leaf 142707207 .leaf) 142711301 (.node .leaf 142711303 .leaf))))))) 151102590 (.node (.node (.node (.node (.node (.node (.node (.node .leaf 151102591 .leaf) 151118974 .leaf) 151118975 (.node .leaf 176392705 .leaf)) 176392707 (.node (.node .leaf 176392709 .leaf) 176392711 (.node .leaf 176396801 .leaf))) 176396803 (.node (.node (.node (.node .leaf 176396805 .leaf) 176396807 .leaf) 178388992 (.node .leaf 178388994 .leaf)) 178393088 (.node (.node .leaf 178393090 .leaf) 178454528 (.node .leaf 178454530 .leaf)))) 178458624 (.node (.node (.node (.node (.node .leaf 178458626 .leaf) 178487296 .leaf) 178487298 (.node .leaf 178489344 .leaf)) 178489346 (.node (.node .leaf 178491392 .leaf) 178491394 (.node .leaf 178493440 .leaf))) 178493442 (.node (.node (.node .leaf 178493952 .leaf) 178493953 (.node .leaf 178493954 .leaf)) 178493955 (.node (.node .leaf 178493956 .leaf) 178493957 (.node .leaf 178493958 .leaf))))) 178493959 (.node (.node (.node (.node (.node (.node .leaf 186754174 .leaf) 186758270 .leaf) 186770558 (.node .leaf 186774654 .leaf)) 214010373 (.node (.node .leaf 214014469 .leaf) 214026757 (.node .leaf 214030853 .leaf))) 218342522 (.node (.node (.node (.node .leaf 218342523 .leaf) 218342526 .leaf) 218342527 (.node .leaf 218358906 .leaf)) 218358907 (.node (.node .leaf 218358910 .leaf) 218358911 (.node .leaf 222429304 .leaf)))) 222429305 (.node (.node (.node (.node (.node .leaf 222445688 .leaf) 222445689 .leaf) 222494840 (.node .leaf 222494841 .leaf)) 222511224 (.node (.node .leaf 222511225 .leaf) 222527608 (.node .leaf 222527609 .leaf))) 222535800 (.node (.node (.node .leaf 222535801 .leaf) 222543992 (.node .leaf 222543993 .leaf)) 222552184 (.node (.node .leaf 222552185 .leaf) 222553208 (.node .leaf 222553209 .leaf)))))) 222553210 (.node (.node (.node (.node (.node (.node (.node .leaf 222553211 .leaf) 222553212 .leaf) 222553213 (.node .leaf 222553214 .leaf)) 222553215 (.node (.node .leaf 247695873 .leaf) 247695877 (.node .leaf 247699969 .leaf))) 247699973 (.node (.node (.node (.node .leaf 247712257 .leaf) 247712261 .leaf) 247716353 (.node .leaf 247716357 .leaf)) 249692160 (.node (.node .leaf 249696256 .leaf) 249708544 (.node .leaf 249712640 .leaf)))) 249757696 (.node (.node (.node (.node (.node .leaf 249761792 .leaf) 249774080 .leaf) 249778176 (.node .leaf 249790464 .leaf)) 249792512 (.node (.node .leaf 249794560 .leaf) 249796608 (.node .leaf 249797120 .leaf))) 249797121 (.node (.node (.node .leaf 249797124 .leaf) 249797125 (.node .leaf 249806848 .leaf)) 249808896 (.node (.node .leaf 249810944 .leaf) 249812992 (.node .leaf 249813504 .leaf))))) 249813505 (.node (.node (.node (.node (.node (.node .leaf 249813508 .leaf) 249813509 .leaf) 253994106 (.node .leaf 253994110 .leaf)) 253998202 (.node (.node .leaf 253998206 .leaf) 254010490 (.node .leaf 254010494 .leaf))) 254014586 (.node (.node (.node (.node .leaf 254014590 .leaf) 258080888 .leaf) 258084984 (.node .leaf 258097272 .leaf)) 258101368 (.node (.node .leaf 258146424 .leaf) 258150520 (.node .leaf 258162808 .leaf)))) 258166904 (.node (.node (.node (.node (.node .leaf 258179192 .leaf) 258183288 .leaf) 258187384 (.node .leaf 258191480 .leaf)) 258195576 (.node (.node .leaf 258199672 .leaf) 258203768 (.node .leaf 258204792 .leaf))) 258204794 (.node (.node (.node .leaf 258204796 .leaf) 258204798 (.node .leaf 258207864 .leaf)) 258208888 (.node (.node .leaf 258208890 .leaf) 258208892 (.node .leaf 258208894 .leaf)))))))))

theorem muxA_check : (mux xIsoA 2 true true true).check TxA = true := by decide +kernel

/-- **bd_mux is correct and hazard-free (broad data window)** under
H_BUNDLED_S (header form `hs = 2`, both sender and pin parts), H_MUX_RTZ and
H_BUNDLED_Z, with unbounded gate delays and unbounded wire delays on the
branches of `s`, `j0` and `j1`; isochronic forks: `ctl_req -> {uj0, uj1}` and
`z_ack -> {uxa, uya, ctl sender}`. Only the selected input is acknowledged,
each control token is consumed by exactly one server transaction, no hazard,
no deadlock, the data select names the owner over `z_req ∨ z_ack`. -/
theorem mux_ok {s} (h : (mux xIsoA 2 true true true).Reach s) :
    Sys.Props (mux xIsoA 2 true true true) s := (Sys.sound muxA_check h).2

/-- **With the brief's weaker H_BUNDLED_S (`s` held only until `ctl_req`
falls), the broad window fails** (the matching positive result for the early
window, `mux_ok_weak_early`, is in `Wip/Cells/MergeMuxWeak.lean`: its 2000-state
check is too heavy for a claimed file): `s` moves after `ctl_req` fell
while `z_ack` is still high, so `z_data` changes before the acknowledge falls.
The header's "held until ctl_ack falls" is the form the broad protocol needs. -/
theorem mux_weak_broad_fails :
    ∃ s, (mux xIsoA 1 true true false).Reach s ∧ xGood xIsoA true s = false :=
  ⟨176392777, Sys.run_reach [0, 2, 9, 11, 15, 16, 17, 2, 3, 6] Sys.Reach.init (by decide +kernel), by decide⟩

/-- **bd_mux is NOT speed independent without H_MUX_RTZ** (every fork
isochronic, header-form H_BUNDLED_S): x's transaction ends, `x_ack` is excited
to fall; a new control token selects y (already waiting), the y transaction
raises `z_ack`, which withdraws `x_ack`'s excitation: a hazard on `x_ack`. -/
theorem mux_needs_rtz :
    ∃ s, (mux xIsoAll 2 true false true).Reach s ∧ (mux xIsoAll 2 true false true).can s 17 = true ∧
      xEx xIsoAll s 21 = true ∧ xEx xIsoAll (xFire s 17) 21 = false :=
  ⟨186745870, Sys.run_reach [0, 1, 2, 9, 15, 16, 17, 2, 21, 0, 9, 15, 16, 17, 3, 2, 10, 15, 16] Sys.Reach.init (by decide +kernel),
    by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **H_ISO_FORK needed on `z_ack -> {uxa, uya, ctl}`** (all else isochronic,
all hypotheses): `za@uya` lags a whole y transaction, and later `y_ack` fires on
the stale value: a spurious acknowledge (spec step fails). -/
theorem mux_needs_iso_za :
    ∃ s, (mux xIsoNoZa 2 true true true).Reach s ∧ (mux xIsoNoZa 2 true true true).can s 22 = true ∧
      xSpec s 22 = false :=
  ⟨36439054, Sys.run_reach [0, 1, 2, 9, 15, 16, 17, 18, 19, 20, 2, 21, 0, 9, 15, 16, 17, 20, 3, 2, 10] Sys.Reach.init (by decide +kernel),
    by decide +kernel, by decide⟩

/-- **H_ISO_FORK needed on `ctl_req -> {uj0, uj1}`** (all else isochronic,
all hypotheses): the control sender sees `ctl_ack` and drops `ctl_req` before
the rise reached the deselected join: `cr@uj1`'s excitation is withdrawn (a
runt on that wire; a transport-delayed pulse could reach `uj1` after `s`
changed and fire it). -/
theorem mux_needs_iso_cr :
    ∃ s, (mux xIsoNoCr 2 true true true).Reach s ∧ (mux xIsoNoCr 2 true true true).can s 2 = true ∧
      xEx xIsoNoCr s 8 = true ∧ xEx xIsoNoCr (xFire s 2) 8 = false :=
  ⟨176390789, Sys.run_reach [0, 2, 7, 9, 15, 16, 17] Sys.Reach.init (by decide +kernel),
    by decide +kernel, by decide +kernel, by decide +kernel⟩

/-- **Without H_BUNDLED_S the wrong input is transferred** (every fork
isochronic): `ctl_req` high with `s = 0`, `j0` fires on x's request, then `s`
flips; `z_req` rises for a token whose `s` now names y (spec step fails). -/
theorem mux_needs_bundled_s :
    ∃ s, (mux xIsoAll 0 false true true).Reach s ∧ (mux xIsoAll 0 false true true).can s 16 = true ∧
      xSpec s 16 = false :=
  ⟨33293, Sys.run_reach [0, 2, 9, 3, 15] Sys.Reach.init (by decide +kernel),
    by decide +kernel, by decide⟩

/-- ...and `s` moving while `ctl_req` is high withdraws `j0`'s excitation: a
hazard on the join. -/
theorem mux_needs_bundled_s_hazard :
    ∃ s, (mux xIsoAll 0 false true true).Reach s ∧ (mux xIsoAll 0 false true true).can s 3 = true ∧
      xEx xIsoAll s 9 = true ∧ xEx xIsoAll (xFire s 3) 9 = false :=
  ⟨5, Sys.run_reach [0, 2] Sys.Reach.init (by decide +kernel),
    by decide +kernel, by decide +kernel, by decide +kernel⟩

end Formal.Cells.MergeMuxSI
