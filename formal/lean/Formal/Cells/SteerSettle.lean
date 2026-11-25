import Formal.Cells.ChainHold

/-!
# Formal.Cells.SteerSettle — a steer sees the settled condition whenever it sees its request (shard B, 2026-11-20)

**Problem, plainly.** A branch steer (`bd_steer`) is a LUT that reads a request and a condition. Research's rule E asks
that the condition has settled at the steer before the request arrives; post-route trims (research/data/trim) and the
link-latch path of FOR-RESEARCH B21 eat into that. `tools-B/auto/steersafe.py` bounds the race per route from two
windows: the request's source is 0 until `A + R` (ChainHold / CtlChain.hold_mem), the condition's source shows its new
value from `A + D` on (SettleAll). This file is the step that turns those two windows into the property itself, in the
Spec gate model (collapsed gate relation `CGateOK`, every delay of the band, glitches included).

**Proved.**
* `steer_reads_settled`: if the request source is `false` on `[S0, A + R]`, the condition source shows `v` on
  `[A + D, E]`, the pins' composite delays are in `[Lp, Up]` (request) and `[Lq, Uq]` (condition), and
  `D + Uq ≤ R + Lp`, then at every time `t ≥ max S (S0 + Up)` at which the gate reads its request pin as `true`, and
  `t ≤ E + Lq`, the gate reads its condition pin as `v`.
* `steer_out_forced`: the same, used on the gate's output: if every address with the request pin `true` and the
  condition pin `v` gives the INIT bit `w` (e.g. the not-taken output stays 0), the output is `w` whenever the request
  pin reads `true` in that window. So a steer cannot send a token the wrong way, nor pulse its other output, from a
  condition still in flight.

**Not shown.** The numbers of any route: `steersafe.py` extracts `R`, `D` and the pin bands from a decoded route
(untrusted); the windows' own premises (the operand latches hold from `A`; the steer's join is 0 at `A`); what
happens when the condition changes while the request is still high (the hold half, rule H / I's job).
-/

namespace Formal.Cells.SteerSettle
open Formal.Target Formal.Timing.SpecChain

/-- **A steer reads the settled condition whenever it reads its request.** -/
theorem steer_reads_settled {p : DelayPar} {c : ℚ} {x : Beh} (g : Gate) (src : Nat → Nat) (arcs : Nat → List Arc)
    (S : Nat) (F : Nat → Nat → Nat)
    (hF : ∀ t, S ≤ t → (∀ i, i < g.k → F i t ≤ t ∧ SumAdm p c (arcs i) (t - F i t)))
    (pr pc : Nat) (hpr : pr < g.k) (hpc : pc < g.k)
    (Lp Up Lq Uq : Nat)
    (hbp : ∀ D, SumAdm p c (arcs pr) D → Lp ≤ D ∧ D ≤ Up)
    (hbq : ∀ D, SumAdm p c (arcs pc) D → Lq ≤ D ∧ D ≤ Uq)
    (S0 A R D E : Nat) (v : Bool)
    (hreq : ∀ u, S0 ≤ u → u ≤ A + R → x (src pr) u = false)
    (hcond : ∀ u, A + D ≤ u → u ≤ E → x (src pc) u = v)
    (hslack : D + Uq ≤ R + Lp)
    (t : Nat) (hS : S ≤ t) (hS0 : S0 + Up ≤ t) (hE : t ≤ E + Lq)
    (hon : x (src pr) (F pr t) = true) :
    x (src pc) (F pc t) = v := by
  have hrd := hF t hS
  obtain ⟨rp1, rp2⟩ := hrd pr hpr
  obtain ⟨rq1, rq2⟩ := hrd pc hpc
  obtain ⟨bp1, bp2⟩ := hbp _ rp2
  obtain ⟨bq1, bq2⟩ := hbq _ rq2
  -- the request pin reads a time ≥ S0, so (it reads `true`) a time after A + R
  have hlate : A + R < F pr t := by
    by_contra hcon
    have := hreq (F pr t) (by omega) (by omega)
    rw [this] at hon; exact Bool.false_ne_true hon
  exact hcond (F pc t) (by omega) (by omega)

/-- **The steer's output, forced.** If the INIT is `w` at every address whose request pin is `true` and whose
condition pin is `v` (tied pins at their constants), then, with the gate's own read times `F`, the output is `w` at every
`t` in the window at which the request pin reads `true`. Instance: the not-taken output of a steer stays 0 whenever it
sees the request, so it cannot pulse from a condition still in flight. -/
theorem steer_out_forced {p : DelayPar} {c : ℚ} {x : Beh} (g : Gate) (src : Nat → Nat) (arcs : Nat → List Arc)
    (S : Nat) (hg : CGateOK p c g src arcs S x)
    (pr pc : Nat) (hpr : pr < g.k) (hpc : pc < g.k)
    (Lp Up Lq Uq : Nat)
    (hbp : ∀ D, SumAdm p c (arcs pr) D → Lp ≤ D ∧ D ≤ Up)
    (hbq : ∀ D, SumAdm p c (arcs pc) D → Lq ≤ D ∧ D ≤ Uq)
    (S0 A R D E : Nat) (v w : Bool) (held ov : Nat → Bool)
    (hh : ∀ i, i < g.k → held i = true → ∀ t, x (src i) t = ov i)
    (hreq : ∀ u, S0 ≤ u → u ≤ A + R → x (src pr) u = false)
    (hcond : ∀ u, A + D ≤ u → u ≤ E → x (src pc) u = v)
    (hslack : D + Uq ≤ R + Lp)
    (hinit : ∀ a : Nat → Bool, (∀ i, i < g.k → held i = true → a i = ov i) → a pr = true → a pc = v →
      g.init.testBit (addr g.k a) = w) :
    ∃ F : Nat → Nat → Nat, ∀ t, S ≤ t → S0 + Up ≤ t → t ≤ E + Lq →
      x (src pr) (F pr t) = true → x g.out t = w := by
  obtain ⟨F, -, hFt⟩ := hg
  refine ⟨F, fun t hS hS0 hE hon => ?_⟩
  obtain ⟨hrd, ho⟩ := hFt t hS
  rw [ho]
  refine hinit _ (fun i hi hhi => hh i hi hhi _) hon ?_
  exact steer_reads_settled g src arcs S F (fun t ht => (hFt t ht).1) pr pc hpr hpc Lp Up Lq Uq hbp hbq S0 A R D E v
    hreq hcond hslack t hS hS0 hE hon

end Formal.Cells.SteerSettle
