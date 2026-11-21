import Formal.Core.Trace.Discrete
import Formal.Core.Delay.SAF

/-!
# The research GLS's board-fidelity LUT channel (`GLS_MODEL=fid`), formalised

Source, read-only: `origin/claude/research` at `6524fa3`, file `cells/gls/fid_core.vh`
(written `R:fid_core.vh:<line>` below) and `cells/gls/prims.v` (`R:prims.v:<line>`).
`gen.py` with `GLS_MODEL=fid` and `build_fid.sh` compile the *baked* netlist with
`-DGLS_TRANSPORT_IC -DGLS_FID` (`R:cells/gls/fid/build_fid.sh:71-73`), so:

* every routed wire is an `ICBUF` with `always @(I) o <= #D I` (`R:prims.v:51-54`): a
  transport delay `D`; here `icbuf D = delay D`;
* every `SLICE_LUTX` is `FID_LUT6` (`R:prims.v:116-132`): each pin `Ak` is copied by its own
  transport non-blocking assignment `ak <= #(dk) Ak` (`R:fid_core.vh:172-182`), with
  `dk = max(T_k + level_k - 1, 0)` (`:152-158`); the output is the zero-time mux tree of
  the copies (`:191-202`), resampled 1 ps later by `FID_SAMPLE` (`:122-131,208-210`), and
  passed through `FID_RESOLVE` (`:47-119`), which is the identity unless the LUT is a
  single-cell state node (`en = 1` and `TLOOP > 0`, `:72-73`);
* `MUXF7/MUXF8` are `FID_MUX2` (`:216-227`): the same per-pin transport form.

Discrete time, one step = 1 ps (`timescale 1ps/1ps`). Binary values. The model reads
signals at the end of each step, which is exactly what `FID_SAMPLE` is for: it removes the
zero-width glitches that two copies landing in the same step produce (`:204-207`). We
checked the sampler's ordering with iverilog 11 on the unmodified `fid_core.vh`
(scratch testbench, notes/A-gls-pass-2.md §1): a 1 ps input pulse on one pin comes out as a
1 ps output pulse, and two pins whose copies land 1 ps apart give a 1 ps output pulse, so
`FID_SAMPLE` is a plain 1-step delay of the end-of-step value (`sample = delay 1`).

What this file does NOT model (stated, see the notes):
* the time-0 X window: every copy starts at `1'bx` until its first scheduled update at
  `dk` (`:160-171`), so the real output is X on `[0, max_k T_k)`. Here signals are constant
  before time 0 (the `Trace.Discrete` convention), so `t < max_k T_k` is not faithful;
* Kleene X values (the mux tree resolves X when both branches agree, `:184-190`);
* the state-node resolver's trace behaviour: only its decision rule (`:77-98`) is
  formalised (`resolve`), not its event scheduling.
-/

namespace Formal.Core.GLSFid

open Formal.Core.TraceDiscrete
open Formal.Core.DelaySAF (saf Faithful saf_eq_delay_iff)

/-! ## The mux tree (R:fid_core.vh:191-202) -/

/-- The Verilog part-select `v[lo + w - 1 : lo]`. -/
def slice (v lo w : Nat) : Nat := v / 2 ^ lo % 2 ^ w

theorem testBit_slice (v lo w i : Nat) :
    (slice v lo w).testBit i = (decide (i < w) && v.testBit (i + lo)) := by
  simp [slice, Nat.testBit_mod_two_pow, Nat.testBit_div_two_pow]

/-- `f6`, transcribed line by line from `R:fid_core.vh:191-196` (A6 at the root). -/
def muxTree6 (INIT : Nat) (a1 a2 a3 a4 a5 a6 : Bool) : Bool :=
  let u5 := if a6 then slice INIT 32 32 else slice INIT 0 32
  let u4 := if a5 then slice u5 16 16 else slice u5 0 16
  let u3 := if a4 then slice u4 8 8 else slice u4 0 8
  let u2 := if a3 then slice u3 4 4 else slice u3 0 4
  let u1 := if a2 then slice u2 2 2 else slice u2 0 2
  if a1 then u1.testBit 1 else u1.testBit 0

/-- `f5`, transcribed from `R:fid_core.vh:198-202` (reads `INIT[31:0]`, A5 at the root). -/
def muxTree5 (INIT : Nat) (b1 b2 b3 b4 b5 : Bool) : Bool :=
  let v4 := if b5 then slice INIT 16 16 else slice INIT 0 16
  let v3 := if b4 then slice v4 8 8 else slice v4 0 8
  let v2 := if b3 then slice v3 4 4 else slice v3 0 4
  let v1 := if b2 then slice v2 2 2 else slice v2 0 2
  if b1 then v1.testBit 1 else v1.testBit 0

/-- The physical address (A1 = bit 0, `R:prims.v:25-27`). -/
def idx6 (a1 a2 a3 a4 a5 a6 : Bool) : Nat :=
  a1.toNat + 2 * a2.toNat + 4 * a3.toNat + 8 * a4.toNat + 16 * a5.toNat + 32 * a6.toNat

def idx5 (b1 b2 b3 b4 b5 : Bool) : Nat :=
  b1.toNat + 2 * b2.toNat + 4 * b3.toNat + 8 * b4.toNat + 16 * b5.toNat

/-- The mux tree is the INIT lookup at the physical address, for every INIT (binary inputs). -/
theorem muxTree6_eq (INIT : Nat) (a1 a2 a3 a4 a5 a6 : Bool) :
    muxTree6 INIT a1 a2 a3 a4 a5 a6 = INIT.testBit (idx6 a1 a2 a3 a4 a5 a6) := by
  cases a1 <;> cases a2 <;> cases a3 <;> cases a4 <;> cases a5 <;> cases a6 <;>
    simp only [muxTree6, idx6, testBit_slice, ite_true, ite_false, Bool.false_eq_true,
      Bool.toNat_true, Bool.toNat_false, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT,
      decide_true, Bool.true_and]

theorem muxTree5_eq (INIT : Nat) (b1 b2 b3 b4 b5 : Bool) :
    muxTree5 INIT b1 b2 b3 b4 b5 = INIT.testBit (idx5 b1 b2 b3 b4 b5) := by
  cases b1 <;> cases b2 <;> cases b3 <;> cases b4 <;> cases b5 <;>
    simp only [muxTree5, idx5, testBit_slice, ite_true, ite_false, Bool.false_eq_true,
      Bool.toNat_true, Bool.toNat_false, Nat.reduceAdd, Nat.reduceMul, Nat.reduceLT,
      decide_true, Bool.true_and]

/-- The LUT function on a pin vector `a` (pin `k` = A(k+1)). -/
def lut6 (INIT : Nat) (a : Nat → Bool) : Bool := muxTree6 INIT (a 0) (a 1) (a 2) (a 3) (a 4) (a 5)
def lut5 (INIT : Nat) (a : Nat → Bool) : Bool := muxTree5 INIT (a 0) (a 1) (a 2) (a 3) (a 4)

/-! ## Per-pin delays (R:fid_core.vh:146-158) -/

/-- `+FID_LEVEL_PS=lv` offsets on the O6 copies (`:152-153`): A1 gets `+(5lv)/2`, ...,
A6 `-(5lv)/2`. `lv` is read with `%d`; a negative value is not modelled (`lv : Nat`), so
Verilog's truncating division is `Nat` division here. Default `lv = 0`. -/
def off6 (lv : Nat) : Nat → Int
  | 0 => (((5 * lv) / 2 : Nat) : Int)
  | 1 => (((3 * lv) / 2 : Nat) : Int)
  | 2 => ((lv / 2 : Nat) : Int)
  | 3 => -((lv / 2 : Nat) : Int)
  | 4 => -(((3 * lv) / 2 : Nat) : Int)
  | _ => -(((5 * lv) / 2 : Nat) : Int)

/-- The O5 offsets (`:154`): `+2lv, +lv, 0, -lv, -2lv` on A1..A5. -/
def off5 (lv : Nat) : Nat → Int
  | 0 => 2 * (lv : Int)
  | 1 => (lv : Int)
  | 2 => 0
  | 3 => -(lv : Int)
  | _ => -2 * (lv : Int)

/-- The copy delay `dk = T + off - 1`, clamped at 0 (`:152-158`). -/
def copyDelay (T : Nat) (off : Int) : Nat := ((T : Int) + off - 1).toNat

/-- The pin's total arc: the copy delay plus the sampler's 1 ps. -/
def pinDelay (T : Nat) (off : Int) : Nat := copyDelay T off + 1

/-- With the default `lv = 0` and an arc `T ≥ 1`, the pin's total delay is exactly its SDF
arc (the "minus 1" of `:150-151` is given back by the sampler). -/
theorem pinDelay_default {T : Nat} (hT : 1 ≤ T) (k : Nat) : pinDelay T (off6 0 k) = T := by
  unfold pinDelay copyDelay off6
  match k with
  | 0 | 1 | 2 | 3 | 4 | _ + 5 => simp; omega

theorem pinDelay5_default {T : Nat} (hT : 1 ≤ T) (k : Nat) : pinDelay T (off5 0 k) = T := by
  unfold pinDelay copyDelay off5
  match k with
  | 0 | 1 | 2 | 3 | _ + 4 => simp; omega

/-- A fid pin never responds in less than one step (whatever the level offset). -/
theorem one_le_pinDelay (T : Nat) (off : Int) : 1 ≤ pinDelay T off := by
  unfold pinDelay; omega

/-- The clamp: once the (negative) level offset reaches the arc, the pin's delay is 1 ps,
not less. So `FID_LEVEL_PS` can reorder arrivals, but only down to one quantum. -/
theorem pinDelay_clamp {T : Nat} {off : Int} (h : (T : Int) + off ≤ 1) : pinDelay T off = 1 := by
  unfold pinDelay copyDelay; omega

/-! ## The channel -/

/-- The pin's transport copy, `always @(Ak) ak <= #(dk) Ak` (`:172-182`). -/
def copy (d : Nat) (A : Sig) : Sig := delay d A

/-- `FID_SAMPLE` (`:122-131`) on end-of-step values: a 1-step delay. -/
def sample (f : Sig) : Sig := delay 1 f

/-- A routed wire in the fid (baked) build: `ICBUF` with `-DGLS_TRANSPORT_IC`
(`R:prims.v:51-54`). -/
def icbuf (D : Nat) (I : Sig) : Sig := delay D I

/-- `FID_LUT6`'s O6 for a non-state LUT (`FID_RESOLVE` with `en ≠ 1` is `o_r = f`,
`:72-73`). `T k` is the SDF arc of pin A(k+1) to O6, `A k` the signal at that pin. -/
def fidO6 (INIT : Nat) (T : Nat → Nat) (lv : Nat) (A : Nat → Sig) : Sig :=
  sample (fun t => lut6 INIT (fun k => copy (copyDelay (T k) (off6 lv k)) (A k) t))

/-- `FID_LUT6`'s O5 for a non-state LUT. -/
def fidO5 (INIT : Nat) (T : Nat → Nat) (lv : Nat) (A : Nat → Sig) : Sig :=
  sample (fun t => lut5 INIT (fun k => copy (copyDelay (T k) (off5 lv k)) (A k) t))

/-- The per-pin pure-delay gate: pin `k` is read `D k` steps ago, then the zero-time
function `F`. This is the abstract form of every fid combinational primitive. -/
def perPin (F : (Nat → Bool) → Bool) (D : Nat → Nat) (A : Nat → Sig) : Sig :=
  fun t => F (fun k => A k (t - D k))

/-- **The fid LUT is the per-pin pure-delay gate** with pin delays `pinDelay`. -/
theorem fidO6_perPin (INIT : Nat) (T : Nat → Nat) (lv : Nat) (A : Nat → Sig) :
    fidO6 INIT T lv A = perPin (lut6 INIT) (fun k => pinDelay (T k) (off6 lv k)) A := by
  funext t
  simp only [fidO6, sample, copy, delay, perPin, pinDelay]
  congr 1; funext k; congr 1; omega

theorem fidO5_perPin (INIT : Nat) (T : Nat → Nat) (lv : Nat) (A : Nat → Sig) :
    fidO5 INIT T lv A = perPin (lut5 INIT) (fun k => pinDelay (T k) (off5 lv k)) A := by
  funext t
  simp only [fidO5, sample, copy, delay, perPin, pinDelay]
  congr 1; funext k; congr 1; omega

/-- Default level (`lv = 0`) and arcs `≥ 1`: pin `k` is read exactly `T k` ps ago. -/
theorem fidO6_default (INIT : Nat) {T : Nat → Nat} (hT : ∀ k, 1 ≤ T k) (A : Nat → Sig) :
    fidO6 INIT T 0 A = perPin (lut6 INIT) T A := by
  rw [fidO6_perPin]
  congr 1; funext k; exact pinDelay_default (hT k) k

theorem fidO5_default (INIT : Nat) {T : Nat → Nat} (hT : ∀ k, 1 ≤ T k) (A : Nat → Sig) :
    fidO5 INIT T 0 A = perPin (lut5 INIT) T A := by
  rw [fidO5_perPin]
  congr 1; funext k; exact pinDelay5_default (hT k) k

/-- A wire then a fid pin is again a per-pin pure delay (wire + arc). -/
theorem perPin_icbuf (F : (Nat → Bool) → Bool) (D W : Nat → Nat) (A : Nat → Sig) :
    perPin F D (fun k => icbuf (W k) (A k)) = perPin F (fun k => W k + D k) A := by
  funext t; simp only [perPin, icbuf, delay]; congr 1; funext k; congr 1; omega

/-- Each pin of the fid gate is a `Transport d d` read: the fid channel is one point of the
per-pin transport envelope. -/
theorem perPin_pin_transport (D : Nat → Nat) (A : Nat → Sig) (k : Nat) :
    Transport (D k) (D k) (A k) (fun t => A k (t - D k)) :=
  delay_transport (D k) (A k)

/-! ## Equal arcs: the fid LUT is the pure delay of its function value, and SAF agrees
with it exactly when SAF is `Faithful` -/

/-- With one delay on every pin, the per-pin gate is the pure delay of the function value. -/
theorem perPin_equal (F : (Nat → Bool) → Bool) (d : Nat) (A : Nat → Sig) :
    perPin F (fun _ => d) A = delay d (fun t => F (fun k => A k t)) := rfl

/-- The default (SAF) model and the fid model with all arcs equal to `d` give the same
output iff the SAF run is `Faithful` (A-delay-saf's monitor). -/
theorem fid_eq_saf_iff (F : (Nat → Bool) → Bool) (d : Nat) (A : Nat → Sig) :
    saf d (fun t => F (fun k => A k t)) = perPin F (fun _ => d) A ↔
      Faithful d (fun t => F (fun k => A k t)) := by
  rw [perPin_equal]; exact saf_eq_delay_iff

/-! ## `FID_MUX2` (R:fid_core.vh:216-227): MUXF7/MUXF8 -/

/-- `E = T > 0 ? T - 1 : 0` (`:218-219`), which is `copyDelay T 0`. -/
def fidMux2 (TD0 TD1 TS0 : Nat) (D0 D1 S0 : Sig) : Sig :=
  sample (fun t => if copy (copyDelay TS0 0) S0 t then copy (copyDelay TD1 0) D1 t
                   else copy (copyDelay TD0 0) D0 t)

theorem fidMux2_eq {TD0 TD1 TS0 : Nat} (h0 : 1 ≤ TD0) (h1 : 1 ≤ TD1) (hs : 1 ≤ TS0)
    (D0 D1 S0 : Sig) :
    fidMux2 TD0 TD1 TS0 D0 D1 S0 =
      fun t => if S0 (t - TS0) then D1 (t - TD1) else D0 (t - TD0) := by
  funext t
  simp only [fidMux2, sample, copy, delay, copyDelay]
  have e0 : t - 1 - ((TD0 : Int) + 0 - 1).toNat = t - TD0 := by omega
  have e1 : t - 1 - ((TD1 : Int) + 0 - 1).toNat = t - TD1 := by omega
  have es : t - 1 - ((TS0 : Int) + 0 - 1).toNat = t - TS0 := by omega
  simp only [e0, e1, es]

/-! ## What the fid channel does with pulses and multi-input changes -/

/-- Pulses of every width pass a fid pin (it is a transport copy). A buffer LUT (`F a = a 0`)
on a 1 ps pulse outputs that 1 ps pulse, delayed by the arc. -/
theorem perPin_pulse_passes (D : Nat → Nat) (a : Bool) (p w : Nat) :
    perPin (fun v => v 0) D (fun _ => pulse a p w) =
      delay (D 0) (pulse a p w) := rfl

/-- A multi-input change produces the function hazard its arrival order implies: an XOR
whose two pins see one rising edge at `p` with arcs `d0 < d1` outputs exactly the pulse
`[p + d0, p + d1)`. -/
theorem perPin_xor_hazard (d0 d1 p : Nat) (hp : 1 ≤ p) (h : d0 ≤ d1) (t : Nat) :
    perPin (fun v => v 0 != v 1) (fun k => if k = 0 then d0 else d1)
      (fun _ s => decide (p ≤ s)) t = decide (p + d0 ≤ t ∧ t < p + d1) := by
  simp only [perPin, ite_true, show ((1 : Nat) = 0) = False from by decide, ite_false]
  by_cases h1 : p ≤ t - d0 <;> by_cases h2 : p ≤ t - d1 <;>
    simp only [h1, h2, decide_true, decide_false, bne_self_eq_false, Bool.true_bne,
      Bool.false_bne, Bool.not_false] <;>
    (first | (symm; simp only [decide_eq_true_eq]; omega) | (symm; simp only [decide_eq_false_iff_not]; omega))

/-! ## The state-node resolver's decision rule (R:fid_core.vh:77-98)

On a state node (`en = 1`, `TLOOP > 0`), an output reversal that comes back to the value
before the last edge, less than `TLOOP` after that edge (`:77-78`), is a runt of width
`p`. One Gaussian draw `noise` (`$dist_normal(seed, 0, win/4)`, `:81`) decides it:
`delta = p - (TLOOP - win/2) + noise` (`:82`); `delta ≤ -(win/2)` rejects (`:83-90`),
otherwise the node resolves to the runt value if `delta > 0`, else back (`:92`). Only this
decision is formalised. NB (iverilog, notes §1): before the decision, `o_r = f` was already
executed at the runt's first edge (`:113-115`), so even a "rejected" runt has been emitted
on the output wire as a full-swing pulse of width `p`. -/

inductive Res | reject | commit | back
  deriving DecidableEq

/-- `:82-92`. All quantities are Verilog `integer`s. -/
def resolve (p tloop win noise : Int) : Res :=
  if p - (tloop - win / 2) + noise ≤ -(win / 2) then .reject
  else if p - (tloop - win / 2) + noise > 0 then .commit else .back

/-- For every runt width, every loop delay and every window `win ≥ 2`, each of the three
outcomes is reached by some noise draw. So which outcome a run shows is decided by the
draw (`META_SEED` and the cell's `SEED`), not by the circuit or its delays. -/
theorem resolve_all_outcomes (p tloop win : Int) (hw : 2 ≤ win) :
    (∃ n, resolve p tloop win n = .reject) ∧ (∃ n, resolve p tloop win n = .commit) ∧
      (∃ n, resolve p tloop win n = .back) := by
  have h2 : 1 ≤ win / 2 := by omega
  refine ⟨⟨-(win / 2) - (p - (tloop - win / 2)), ?_⟩, ⟨1 - (p - (tloop - win / 2)), ?_⟩,
    ⟨-(p - (tloop - win / 2)), ?_⟩⟩
  all_goals
    unfold resolve
    split
    · first | rfl | (exfalso; omega)
    · split
      · first | rfl | (exfalso; omega)
      · first | rfl | (exfalso; omega)

end Formal.Core.GLSFid
