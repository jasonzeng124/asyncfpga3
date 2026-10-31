import Formal.Core.Prims.SeqFlop

/-!
# Formal.Core.Prims.SeqSync — the two-flop synchronizer, in the digital model

Shard A, probe PrimsSeq. Core Lean only. Notes: `formal/notes/A-prims-seq.md`.

The gcd_hw rig samples asynchronous signals with two flops on one clock
(`cells/hw/gcd_hw.v`: `rs0 <= sample_bus; rs1 <= rs0;`, and CLAUDE.md: "an async signal
entering a clocked FSM needs a synchronizer"). In this model:

* the first flop may see its D move inside its window (any asynchronous input does,
  sometimes): its output is X for at most `cqHi + res`, then one definite value
  (`x_contained`);
* the wire from flop 0 to flop 1 is a fixed delay `w` (K3: `d1 t = q0 (t - w)`);
* if the clock period leaves room for the X window and the wire,
  `cqHi + res + w < P + dLo`, and the wire covers flop 1's hold, `dHi ≤ cqLo + w`, then
  **flop 1 captures a definite value cleanly at the next edge: no X at all at flop 1**
  (`sync_two_flop`). Which value it is (old or new input) is not determined.

Assumed: both flops have the same timing `T`, the same binary clock, flop 1's CE = 1 and
R = 0 cleanly at `e'` (flop 0's CE/R may be anything), no edge between `e` and `e'` nor in
`(e', e' + cqLo]`, and the period exceeds the X window (`e + cqHi + res < e'`). Not covered: an X window longer
than `res` (H_FF_RESOLVE is exactly the assumption a synchronizer depends on; no MTBF),
clock skew between the two flops, a variable wire delay (use `Win`).
-/

namespace Formal.Core.Prims.Seq

open Formal.Core Formal.Core.K3 Formal.Core.Substrate

variable (T : FFTiming)

/-- **Two-flop synchronizer.** Flop 0 samples an arbitrary (asynchronous) `d0` at edge `e`;
flop 1 samples `q0` through a wire of delay `w` at the next edge `e'`. Under the period and
wire conditions, flop 1's output after `e' + cqHi` is one definite value, until its next
edge. -/
theorem sync_two_flop (hok : T.Ok) {rv init0 init1 : Bool} {ck : Sig} {r ce d0 q0 q1 : KSig}
    {w : Nat}
    (h0 : FlopRel T false rv init0 ck r ce d0 q0)
    (h1 : FlopRel T false rv init1 ck r ce (fun t => q0 (t - w)) q1)
    {e e' : Nat} (he : rises ck e) (he' : rises ck e') (hee : e < e') (hn : NoRise ck e e')
    (hn' : NoRise ck e' (e' + T.cqLo + 1))
    (hce1 : EqOn ce one (wpt e' T.ceLo) (wpt e' T.ceHi))
    (hr1 : EqOn r zero (wpt e' T.srLo) (wpt e' T.srHi))
    (hP0 : e + T.cqHi + T.res < e')
    (hP : (e : Int) + T.cqHi + T.res + w < e' + T.dLo)
    (hH : T.dHi ≤ (T.cqLo : Int) + w) :
    ∃ b : Bool, ∀ t, e' + T.cqHi < t → NoRise ck e' t → q1 t = ofBool b := by
  obtain ⟨b, hb⟩ := x_contained T h0 he
  have hq0e' : q0 e' = ofBool b := hb e' hP0 hn (guard_sync T _ _ _)
  have hq0 : ∀ s, e + T.cqHi + T.res < s → s ≤ e' + T.cqLo → q0 s = ofBool b := by
    intro s h1s h2s
    by_cases hs : s ≤ e'
    · exact hb s h1s (fun u hu1 hu2 => hn u hu1 (by omega)) (guard_sync T _ _ _)
    · rw [h0.hold e' s he' (by omega) (fun u hu1 hu2 => hn' u hu1 (by omega))
        (guard_sync T _ _ _) h2s, hq0e']
  refine ⟨b, fun t ht hnt => capture T hok h1 he' (by omega) hnt (guard_sync T _ _ _) ?_ hce1 hr1 ht⟩
  intro s hs1 hs2
  show q0 (s - w) = ofBool b
  unfold wpt at hs1 hs2
  exact hq0 (s - w) (by omega) (by omega)

end Formal.Core.Prims.Seq
