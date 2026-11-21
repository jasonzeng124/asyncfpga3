import Formal.Cells.SteerSettle

/-!
# Formal.Cells.SteerSettleMulti — a steer race with several launches (shard B, 2026-11-21)

**Problem, plainly.** `steersafe.py` bounds a steer race with one term per launch: a compare reading two input links
has one term per link's ctl (the B27 fix); a steer whose condition sits in a link latch has a term from that latch's
own ctl and a term from the compute that feeds it (B21), and since B29 that feeder may be a one-channel compare whose
launch is its input link's ctl. Each term `i` says: the request is still 0 until `A i + R i`, and the part of the
condition launched at `A i` has arrived by `A i + D i`; the tool reports the smallest slack over the terms. This file
states why "every term has slack" is enough: the condition is settled once every launch's part has arrived, and the
request cannot be seen high before every launch's own bound has passed.

**Proved.**
* `steer_reads_settled_multi`: with `n` launches, the request source `false` on `[S0, A i + R i]` for every `i < n`,
  the condition source `v` on `[u, E]` for any `u` at or after every `A i + D i`, pin bands as in
  `SteerSettle.steer_reads_settled`, and `D i + Uq ≤ R i + Lp` for every `i < n`: whenever the gate reads its request
  pin `true` (at `t` in the window), it reads its condition pin as `v`.
* `steer_out_forced_multi`: the same on the gate's output, with an INIT fact (as `steer_out_forced`).

**Not shown.** That the tool's terms are the right ones (its extraction is untrusted), or the window premises
themselves (each term's condition cone settles by `A i + D i` given the others' roots settled: `SettleAll` with the
per-term roots; each request bound: `ChainHold` / `CtlChain.hold_mem`).
-/

namespace Formal.Cells.SteerSettleMulti
open Formal.Target Formal.Timing.SpecChain

/-- **Several launches: every term's slack is enough.** -/
theorem steer_reads_settled_multi {p : DelayPar} {c : ℚ} {x : Beh} (g : Gate) (src : Nat → Nat)
    (arcs : Nat → List Arc) (S : Nat) (F : Nat → Nat → Nat)
    (hF : ∀ t, S ≤ t → (∀ i, i < g.k → F i t ≤ t ∧ SumAdm p c (arcs i) (t - F i t)))
    (pr pc : Nat) (hpr : pr < g.k) (hpc : pc < g.k)
    (Lp Up Lq Uq : Nat)
    (hbp : ∀ D, SumAdm p c (arcs pr) D → Lp ≤ D ∧ D ≤ Up)
    (hbq : ∀ D, SumAdm p c (arcs pc) D → Lq ≤ D ∧ D ≤ Uq)
    (n S0 E : Nat) (A R D : Nat → Nat) (v : Bool)
    (hreq : ∀ i, i < n → ∀ u, S0 ≤ u → u ≤ A i + R i → x (src pr) u = false)
    (hcond : ∀ u, (∀ i, i < n → A i + D i ≤ u) → u ≤ E → x (src pc) u = v)
    (hslack : ∀ i, i < n → D i + Uq ≤ R i + Lp)
    (t : Nat) (hS : S ≤ t) (hS0 : S0 + Up ≤ t) (hE : t ≤ E + Lq)
    (hon : x (src pr) (F pr t) = true) :
    x (src pc) (F pc t) = v := by
  have hrd := hF t hS
  obtain ⟨rp1, rp2⟩ := hrd pr hpr
  obtain ⟨rq1, rq2⟩ := hrd pc hpc
  obtain ⟨bp1, bp2⟩ := hbp _ rp2
  obtain ⟨bq1, bq2⟩ := hbq _ rq2
  refine hcond (F pc t) (fun i hi => ?_) (by omega)
  have hlate : A i + R i < F pr t := by
    by_contra hcon
    have := hreq i hi (F pr t) (by omega) (by omega)
    rw [this] at hon; exact Bool.false_ne_true hon
  have := hslack i hi
  omega

/-- **The steer's output, forced, with several launches.** -/
theorem steer_out_forced_multi {p : DelayPar} {c : ℚ} {x : Beh} (g : Gate) (src : Nat → Nat)
    (arcs : Nat → List Arc) (S : Nat) (hg : CGateOK p c g src arcs S x)
    (pr pc : Nat) (hpr : pr < g.k) (hpc : pc < g.k)
    (Lp Up Lq Uq : Nat)
    (hbp : ∀ D, SumAdm p c (arcs pr) D → Lp ≤ D ∧ D ≤ Up)
    (hbq : ∀ D, SumAdm p c (arcs pc) D → Lq ≤ D ∧ D ≤ Uq)
    (n S0 E : Nat) (A R D : Nat → Nat) (v w : Bool) (held ov : Nat → Bool)
    (hh : ∀ i, i < g.k → held i = true → ∀ t, x (src i) t = ov i)
    (hreq : ∀ i, i < n → ∀ u, S0 ≤ u → u ≤ A i + R i → x (src pr) u = false)
    (hcond : ∀ u, (∀ i, i < n → A i + D i ≤ u) → u ≤ E → x (src pc) u = v)
    (hslack : ∀ i, i < n → D i + Uq ≤ R i + Lp)
    (hinit : ∀ a : Nat → Bool, (∀ i, i < g.k → held i = true → a i = ov i) → a pr = true → a pc = v →
      g.init.testBit (addr g.k a) = w) :
    ∃ F : Nat → Nat → Nat, ∀ t, S ≤ t → S0 + Up ≤ t → t ≤ E + Lq →
      x (src pr) (F pr t) = true → x g.out t = w := by
  obtain ⟨F, -, hFt⟩ := hg
  refine ⟨F, fun t hS hS0 hE hon => ?_⟩
  obtain ⟨hrd, ho⟩ := hFt t hS
  rw [ho]
  refine hinit _ (fun i hi hhi => hh i hi hhi _) hon ?_
  exact steer_reads_settled_multi g src arcs S F (fun t ht => (hFt t ht).1) pr pc hpr hpc Lp Up Lq Uq hbp hbq
    n S0 E A R D v hreq hcond hslack t hS hS0 hE hon

/-- Non-vacuity check: one launch is `SteerSettle.steer_reads_settled` (its window premise implies this one's). -/
theorem one_launch_premise (x : Beh) (s : Nat) (A0 D0 E : Nat) (v : Bool)
    (hcond : ∀ u, A0 + D0 ≤ u → u ≤ E → x s u = v) :
    ∀ u, (∀ i, i < 1 → (fun _ => A0) i + (fun _ => D0) i ≤ u) → u ≤ E → x s u = v :=
  fun u h hE => hcond u (h 0 (by decide)) hE

end Formal.Cells.SteerSettleMulti
