import Formal.Cells.Bundling
import Formal.Cells.AMergeTimedW

/-!
# Probe Bfd: H_FORK_DATA (fork branch data vs request) and H_AMERGE_IDX

Rows C14 and C11 of `formal/out/gcd_hw_hypotheses.md`; note `formal/notes/B-fork-data.md`.

## What bdc emits (bdc/emit.py `_op_fork`, cells/rtl/bd_ctl.v `bd_fork`)

    bd_fork #(.N(n)) f (.req(x_req), .ack(x_ack), .req_out({o_k_req}), .ack_in({o_k_ack}));
    assign o_k_data = x_data;          -- for every branch k

`req_out = {N{req}}`: the request fan-out is a WIRE, the acknowledge is a
`bd_ctree` (C-element tree). The data bus is the SAME net for every branch;
each branch only has its own route from that driver to its consumer's pins.
The fork has no gate on the forward path, so its whole forward obligation is
the bundling of each branch at its consumer's pins.

gcd_hw (re-emitted with the pads build, 139 branches over all `bd_fork`
instances of `bdc_gcd`, including the `_f` forks behind every control_merge):
53 branches end at a `bd_link`/`bd_pipe` (controller `bd_c2n`, data into a
`bd_latch`), 59 at a `bd_join` (its data then feeds a steer select or a compute
unit), 12 at a nested `bd_fork`, 6 at a `bd_snk`, 9 at control-only inputs
(amerge inputs with `in_data(1'b0)`, compute unit control ports, `p_end`).
This file treats the latch consumer, the one where the branch data is
captured directly.

## Model (Bundling's, unchanged)

Time `Nat` ps, `Sig := Nat → Bool`, every pin a window `[lo, hi]` (route + site
pin + LUT arc), the latch bit is `LatchRel` (Kleene mux of the real INIT,
`odd_latch`/`pair_o5_latch`/`pair_o6_latch`). For one branch `B`:

* `dlo/dhi`: shared data net driver -> THIS branch's latch D pin -> latch out.
* `elo/ehi`: consumer node (its `bd_c2n` output) -> latch EN pin -> latch out.
* `flo/fhi`: the latch's own loop (feedback wire + I2 site pin + I2 arc).
* `rlo`: producer request net -> fork wire to this branch -> consumer `bd_c2n`
  req pin -> node rise (min). H_REQ_LO: the node cannot rise before `Tr + rlo`.
* `wlo`: node rise -> node fall (min): ack (node) -> DACK (FASTRISE rise) ->
  fork C-tree -> producer -> producer req fall -> fork wire -> node fall.
  H_EN_WIDTH. This is the credit rule I computes as `t_ack + t_fall`.
* `alo`: node fall -> producer's next change of the shared data net (min).
  H_REL_LO.

## Results

* `H_FORK_DATA`: `Td + dhi + fhi ≤ Tr + rlo + elo`, the "data before request"
  form at the consumer's pins (data_hi + latch setup through its loop ≤ req_lo).
* `H_FORK_DATA_W`: `Td + dhi + fhi ≤ Tr + rlo + wlo + elo` (the same with the
  round-trip credit). This is `bd_latch.setup_data` (L1) with the launch at
  the fork's producer.
* `branch_capture` (sufficiency): H_FORK_DATA_W + H_FORK_PULSE + H_FORK_HOLD
  give `q = v` over the whole capture interval, for every trace of the gate
  relation. `edge_implies_W`: H_FORK_DATA ⇒ H_FORK_DATA_W.
* `fork_capture`: all branches of one fork, one shared data net.
* `fork_data_needed` (necessity): for EVERY branch with point windows
  (transport delays, a special case of the windows) violating H_FORK_DATA_W by
  exactly 1 ps at the minimal environment, a trace of the real odd-bit INIT
  satisfying every other hypothesis of `branch_capture` latches a STALE value:
  `q = !v` at the closing instant and once every loop period for ever.
* `fork_data_good` (non-vacuity, parametric) and `edge_form_not_needed`: at a
  Muller link consumer H_FORK_DATA is sufficient but NOT necessary (a witness
  that violates it by 850 ps and captures).
* C11: `H_AMERGE_IDX` = Cm2's three races (`BidxA`, `BidxB`, `IdxAckFork`),
  with `amerge_idx_sufficient`, `amerge_idx_necessary` (the three exact legs),
  `amerge_idx_nonvacuous`, and `amerge_data_const` (the data-mux leg is empty in
  gcd_hw: every amerge is `bdc_amerge*_0`, inputs `1'b0`, `z_data` unconnected).
-/

namespace Formal.Cells.ForkData
open Formal.Cells Formal.Cells.Bundling

/-! ## 1. One fork branch with a latch consumer -/

/-- Delays of one fork branch at its consumer (ps; every field a routed
quantity, see the header). -/
structure Br where
  dlo : Nat
  dhi : Nat
  elo : Nat
  ehi : Nat
  flo : Nat
  fhi : Nat
  rlo : Nat
  wlo : Nat
  alo : Nat

/-- **H_FORK_DATA** (data before request, at the consumer's pins): the latest
the branch's data can be through the latch and once round its loop is no later
than the earliest the branch's request can have opened the latch. -/
abbrev H_FORK_DATA (B : Br) (Td Tr : Nat) : Prop := Td + B.dhi + B.fhi ≤ Tr + B.rlo + B.elo

/-- **H_FORK_DATA_W** (the exact form at a Muller link): the same against the
earliest enable FALL, a whole handshake (`wlo`) after the request. -/
abbrev H_FORK_DATA_W (B : Br) (Td Tr : Nat) : Prop :=
  Td + B.dhi + B.fhi ≤ Tr + B.rlo + B.wlo + B.elo

/-- **H_FORK_PULSE**: the consumer's enable pulse is long enough for the latch
to settle through its loop (`bd_latch.setup_pulse`, L2). -/
abbrev H_FORK_PULSE (B : Br) : Prop := B.ehi + B.fhi ≤ B.wlo + B.elo

/-- **H_FORK_HOLD**: the shared bus cannot change at this latch before its
enable has fallen (`bd_latch.hold`, L3, rule H with the fork's ack path in `alo`). -/
abbrev H_FORK_HOLD (B : Br) : Prop := B.ehi ≤ B.alo + B.dlo

/-- A run of one branch: shared data net `d` (value `v` on `[Td, Tnew)`), the
consumer node `en` (clean pulse `[Ton, Toff)`, low until `Tnext`), the latch bit
`q`, and the three environment bounds. -/
structure BrRun (B : Br) (d en q : Sig) (Tr Td Ton Toff Tnext Tnew : Nat) (v : Bool) : Prop where
  latch : LatchRel d en q B.dlo B.dhi B.elo B.ehi B.flo B.fhi
  hdw : B.dlo ≤ B.dhi
  hew : B.elo ≤ B.ehi
  hfw : B.flo ≤ B.fhi
  H_LOOP_POS : 1 ≤ B.flo
  h_on : ∀ t, Ton ≤ t → t < Toff → en t = true
  h_off : ∀ t, Toff ≤ t → t < Tnext → en t = false
  h_d : ∀ t, Td ≤ t → t < Tnew → d t = v
  H_REQ_LO : Tr + B.rlo ≤ Ton
  H_EN_WIDTH : Ton + B.wlo ≤ Toff
  H_REL_LO : Toff + B.alo ≤ Tnew

theorem edge_implies_W (B : Br) (Td Tr : Nat) (h : H_FORK_DATA B Td Tr) : H_FORK_DATA_W B Td Tr := by
  unfold H_FORK_DATA at h; unfold H_FORK_DATA_W; omega

/-- **Sufficiency.** The branch's latch holds the producer's value from when it
can have settled to the next enable rise. Reuses `Bundling.capture`. -/
theorem branch_capture {B : Br} {d en q : Sig} {Tr Td Ton Toff Tnext Tnew : Nat} {v : Bool}
    (R : BrRun B d en q Tr Td Ton Toff Tnext Tnew v)
    (H : H_FORK_DATA_W B Td Tr) (HP : H_FORK_PULSE B) (HH : H_FORK_HOLD B) :
    ∀ t, max (Ton + B.ehi) (Td + B.dhi) ≤ t → t < Tnext + B.elo → q t = v := by
  have h1 := R.H_REQ_LO; have h2 := R.H_EN_WIDTH; have h3 := R.H_REL_LO
  unfold H_FORK_DATA_W at H; unfold H_FORK_PULSE at HP; unfold H_FORK_HOLD at HH
  exact capture d en q B.dlo B.dhi B.elo B.ehi B.flo B.fhi R.latch R.hdw R.hew R.hfw R.H_LOOP_POS
    Ton Toff Tnext Td Tnew v R.h_on R.h_off R.h_d (by omega) (by omega)

/-- **The whole fork.** Branches `i : ι` read ONE data net `d` (the shared
bus), each through its own windows and its own request path. If every branch
meets its three conditions, every branch's latch captures `v`. -/
theorem fork_capture {ι : Type} (B : ι → Br) (d : Sig) (en q : ι → Sig)
    (Tr Td Tnew : Nat) (Ton Toff Tnext : ι → Nat) (v : Bool)
    (R : ∀ i, BrRun (B i) d (en i) (q i) Tr Td (Ton i) (Toff i) (Tnext i) Tnew v)
    (H : ∀ i, H_FORK_DATA_W (B i) Td Tr) (HP : ∀ i, H_FORK_PULSE (B i)) (HH : ∀ i, H_FORK_HOLD (B i)) :
    ∀ i t, max (Ton i + (B i).ehi) (Td + (B i).dhi) ≤ t → t < Tnext i + (B i).elo → q i t = v :=
  fun i => branch_capture (R i) (H i) (HP i) (HH i)

/-! ## 2. Counter-trace family: violated by 1 ps, the latch keeps a stale value

Point windows (`lo = hi`: transport delay, which the window relation admits by
`transport_gate`), the minimal environment (node rises at `Tr + rlo`, falls
`wlo` later), data changes from `!v` to `v` at `Td` and never again. With
`P = Td + dd` the latch output is `!v` before `P`, then `v` except at every
`f`-th instant: the `!v` still in the loop when the latch closed circulates. -/

def cEn (Ton Toff : Nat) : Sig := fun t => decide (Ton ≤ t ∧ t < Toff)
def cD (Td : Nat) (v : Bool) : Sig := fun t => if t < Td then !v else v
/-- The stale-value trace. -/
def cQ (P f : Nat) (v : Bool) : Sig := fun t =>
  if t < P then !v else if (t + 1 - P) % f = 0 then !v else v
/-- The good trace (captured). -/
def gQ (P : Nat) (v : Bool) : Sig := fun t => if t < P then !v else v

theorem cQ_step (Ton Toff Td dd e f : Nat) (v : Bool) (hTd : 1 ≤ Td) (hf : 1 ≤ f)
    (hon : Ton + e ≤ Td + dd) (hoff : Toff + e + 1 = Td + dd + f) (t : Nat) :
    cQ (Td + dd) f v t =
      (if cEn Ton Toff (t - e) then cD Td v (t - dd) else cQ (Td + dd) f v (t - f)) := by
  unfold cEn
  by_cases hen : Ton ≤ t - e ∧ t - e < Toff
  · rw [if_pos (by simpa using hen)]
    unfold cQ cD
    by_cases hP : t < Td + dd
    · rw [if_pos hP, if_pos (by omega)]
    · rw [if_neg hP]
      have hlt : t + 1 - (Td + dd) < f := by omega
      rw [Nat.mod_eq_of_lt hlt, if_neg (show ¬ t + 1 - (Td + dd) = 0 by omega),
        if_neg (show ¬ t - dd < Td by omega)]
  · rw [if_neg (by simpa using hen)]
    unfold cQ
    by_cases hP : t < Td + dd
    · rw [if_pos hP, if_pos (by omega)]
    · rw [if_neg hP]
      have ht : Toff + e ≤ t := by omega
      by_cases hP' : t - f < Td + dd
      · rw [if_pos hP']
        have : t + 1 - (Td + dd) = f := by omega
        rw [this, Nat.mod_self, if_pos rfl]
      · rw [if_neg hP']
        have : t + 1 - (Td + dd) = (t - f + 1 - (Td + dd)) + f := by omega
        rw [this, Nat.add_mod_right]

theorem gQ_step (Ton Toff Td dd e f : Nat) (v : Bool) (hTd : 1 ≤ Td) (hTon : 1 ≤ Ton)
    (hW : max (Ton + e) (Td + dd) + f ≤ Toff + e) (t : Nat) :
    gQ (max (Ton + e) (Td + dd)) v t =
      (if cEn Ton Toff (t - e) then cD Td v (t - dd) else gQ (max (Ton + e) (Td + dd)) v (t - f)) := by
  unfold cEn
  by_cases hen : Ton ≤ t - e ∧ t - e < Toff
  · rw [if_pos (by simpa using hen)]
    unfold gQ cD
    by_cases hP : t < max (Ton + e) (Td + dd)
    · rw [if_pos hP, if_pos (by omega)]
    · rw [if_neg hP, if_neg (by omega)]
  · rw [if_neg (by simpa using hen)]
    unfold gQ
    by_cases hP : t < max (Ton + e) (Td + dd)
    · rw [if_pos hP, if_pos (by omega)]
    · rw [if_neg hP, if_neg (by omega)]

/-- A transport trace of the odd-bit LUT6 (real INIT) is a `LatchRel` with
point windows. -/
theorem odd_point {d en q : Sig} {dd e f : Nat}
    (h : ∀ t, q t = (if en (t - e) then d (t - dd) else q (t - f))) :
    LatchRel d en q dd dd e e f f := by
  have hT : Transport ODD [(d, dd), (en, e), (q, f), (zero, 0), (zero, 0), (zero, 0)] q := by
    intro t
    show q t = lutB ODD [d (t - dd), en (t - e), q (t - f), false, false, false]
    rw [odd_bin]; exact h t
  exact odd_latch (transport_gate ODD [(d, dd, dd, dd), (en, e, e, e), (q, f, f, f),
    (zero, 0, 0, 0), (zero, 0, 0, 0), (zero, 0, 0, 0)] q (by simp) hT)

theorem cQ_stale (P f k : Nat) (v : Bool) (hf : 1 ≤ f) :
    cQ P f v (P + f - 1 + k * f) = !v := by
  unfold cQ
  rw [if_neg (by omega)]
  have : P + f - 1 + k * f + 1 - P = (k + 1) * f := by rw [Nat.succ_mul]; omega
  rw [this, Nat.mul_mod_left, if_pos rfl]

/-- **Necessity of H_FORK_DATA_W (exact by one ps).** Every branch with point
windows, a positive loop and a data change (`1 ≤ Td`) that meets H_FORK_PULSE
but misses H_FORK_DATA_W by exactly one ps has a trace of the real odd-bit
latch INIT that satisfies every `BrRun` field (for every `Tnext` and every
release `Tnew` allowed by H_REL_LO; the data never changes again, so the hold
side is untouched whatever `alo` is) and in which the latch shows the STALE
value `!v` at the closing instant `Toff + elo` and every loop period after it.
The closing instant lies inside the interval `branch_capture` would promise. -/
theorem fork_data_needed (B : Br) (Tr Td : Nat) (v : Bool)
    (hpt : B.dlo = B.dhi ∧ B.elo = B.ehi ∧ B.flo = B.fhi)
    (H_LOOP_POS : 1 ≤ B.flo) (hTd : 1 ≤ Td) (HP : H_FORK_PULSE B)
    (hviol : Td + B.dhi + B.fhi = Tr + B.rlo + B.wlo + B.elo + 1) :
    ¬ H_FORK_DATA_W B Td Tr ∧
    ∃ d en q : Sig,
      (∀ Tnext Tnew, Tr + B.rlo + B.wlo + B.alo ≤ Tnew →
        BrRun B d en q Tr Td (Tr + B.rlo) (Tr + B.rlo + B.wlo) Tnext Tnew v) ∧
      (∀ k, q (Tr + B.rlo + B.wlo + B.elo + k * B.fhi) = !v) ∧
      max (Tr + B.rlo + B.ehi) (Td + B.dhi) ≤ Tr + B.rlo + B.wlo + B.elo := by
  obtain ⟨h1, h2, h3⟩ := hpt
  unfold H_FORK_PULSE at HP
  refine ⟨by unfold H_FORK_DATA_W; omega, cD Td v, cEn (Tr + B.rlo) (Tr + B.rlo + B.wlo),
    cQ (Td + B.dhi) B.fhi v, ?_, ?_, by omega⟩
  · intro Tnext Tnew hTn
    have hL : LatchRel (cD Td v) (cEn (Tr + B.rlo) (Tr + B.rlo + B.wlo)) (cQ (Td + B.dhi) B.fhi v)
        B.dhi B.dhi B.elo B.elo B.fhi B.fhi :=
      odd_point (cQ_step _ _ Td B.dhi B.elo B.fhi v hTd (by omega) (by omega) (by omega))
    exact
      { latch := by rw [h1, ← h2, h3]; exact hL
        hdw := by omega
        hew := by omega
        hfw := by omega
        H_LOOP_POS := H_LOOP_POS
        h_on := fun t a b => by simp [cEn]; omega
        h_off := fun t a _ => by simp [cEn]; omega
        h_d := fun t a _ => by simp [cD]; omega
        H_REQ_LO := Nat.le_refl _
        H_EN_WIDTH := Nat.le_refl _
        H_REL_LO := by omega }
  · intro k
    have e : Tr + B.rlo + B.wlo + B.elo = Td + B.dhi + B.fhi - 1 := by omega
    rw [e]; exact cQ_stale _ _ k v (by omega)

/-- **Non-vacuity (parametric).** Every branch with point windows meeting
H_FORK_DATA_W and H_FORK_PULSE has a run (real odd-bit INIT, minimal
environment) of `BrRun`, and in it `q` really changes: `!v` before
`max (Tr + rlo + elo) (Td + dhi)` (the later of the latch opening and the data
arriving), `v` from there on. Needs `1 ≤ Tr + rlo` (no request at time 0, where
truncated subtraction would read the past as the present). -/
theorem fork_data_good (B : Br) (Tr Td : Nat) (v : Bool)
    (hpt : B.dlo = B.dhi ∧ B.elo = B.ehi ∧ B.flo = B.fhi)
    (H_LOOP_POS : 1 ≤ B.flo) (hTd : 1 ≤ Td) (hTr : 1 ≤ Tr + B.rlo)
    (HP : H_FORK_PULSE B) (H : H_FORK_DATA_W B Td Tr) :
    (∀ Tnext Tnew, Tr + B.rlo + B.wlo + B.alo ≤ Tnew →
      BrRun B (cD Td v) (cEn (Tr + B.rlo) (Tr + B.rlo + B.wlo))
        (gQ (max (Tr + B.rlo + B.elo) (Td + B.dhi)) v)
        Tr Td (Tr + B.rlo) (Tr + B.rlo + B.wlo) Tnext Tnew v) ∧
    (∀ t, t < max (Tr + B.rlo + B.elo) (Td + B.dhi) →
      gQ (max (Tr + B.rlo + B.elo) (Td + B.dhi)) v t = !v) ∧
    (∀ t, max (Tr + B.rlo + B.elo) (Td + B.dhi) ≤ t →
      gQ (max (Tr + B.rlo + B.elo) (Td + B.dhi)) v t = v) := by
  obtain ⟨h1, h2, h3⟩ := hpt
  unfold H_FORK_PULSE at HP; unfold H_FORK_DATA_W at H
  refine ⟨?_, fun t ht => by simp only [gQ, if_pos ht],
    fun t ht => by simp only [gQ, if_neg (Nat.not_lt.2 ht)]⟩
  intro Tnext Tnew hTn
  have hL : LatchRel (cD Td v) (cEn (Tr + B.rlo) (Tr + B.rlo + B.wlo))
      (gQ (max (Tr + B.rlo + B.elo) (Td + B.dhi)) v) B.dhi B.dhi B.elo B.elo B.fhi B.fhi :=
    odd_point (gQ_step _ _ Td B.dhi B.elo B.fhi v hTd hTr (by omega))
  exact
    { latch := by rw [h1, ← h2, h3]; exact hL
      hdw := by omega
      hew := by omega
      hfw := by omega
      H_LOOP_POS := H_LOOP_POS
      h_on := fun t a b => by simp [cEn]; omega
      h_off := fun t a _ => by simp [cEn]; omega
      h_d := fun t a _ => by simp [cD]; omega
      H_REQ_LO := Nat.le_refl _
      H_EN_WIDTH := Nat.le_refl _
      H_REL_LO := by omega }

/-- A numeric branch (ps, arc-like magnitudes; not a routed instance):
D path 400, enable path 300, loop 150, request path 200, round trip 900,
release 500. -/
def Bnum : Br := ⟨400, 400, 300, 300, 150, 150, 200, 900, 500⟩

/-- The necessity theorem's hypotheses are satisfiable: `Td = 851` misses
H_FORK_DATA_W by one ps (1401 against 1400); the stale trace shows `0` for `v = 1`
at the closing instant 1400. -/
theorem fork_data_needed_num :
    (Bnum.dlo = Bnum.dhi ∧ Bnum.elo = Bnum.ehi ∧ Bnum.flo = Bnum.fhi) ∧ 1 ≤ Bnum.flo ∧
    H_FORK_PULSE Bnum ∧ 851 + Bnum.dhi + Bnum.fhi = 0 + Bnum.rlo + Bnum.wlo + Bnum.elo + 1 ∧
    ¬ H_FORK_DATA_W Bnum 851 0 ∧ cQ (851 + 400) 150 true (0 + 200 + 900 + 300) = false := by
  decide

/-- **H_FORK_DATA is not necessary at a Muller link.** `Td = 800`: the data is
through the latch and its loop at 1350, 850 ps after the request can have opened
the latch (H_FORK_DATA: 1350 ≤ 500 fails), yet H_FORK_DATA_W holds (1350 ≤ 1400)
and the latch captures: `q` is 0 until 1199 and 1 from 1200 on. -/
theorem edge_form_not_needed :
    ¬ H_FORK_DATA Bnum 800 0 ∧ H_FORK_DATA_W Bnum 800 0 ∧ H_FORK_PULSE Bnum ∧ H_FORK_HOLD Bnum ∧
    (∀ Tnext Tnew, 0 + 200 + 900 + 500 ≤ Tnew →
      BrRun Bnum (cD 800 true) (cEn (0 + 200) (0 + 200 + 900)) (gQ (max (0 + 200 + 300) (800 + 400)) true)
        0 800 (0 + 200) (0 + 200 + 900) Tnext Tnew true) ∧
    gQ (max (0 + 200 + 300) (800 + 400)) true 1199 = false ∧
    gQ (max (0 + 200 + 300) (800 + 400)) true 1200 = true := by
  refine ⟨by decide, by decide, by decide, by decide, ?_, by decide, by decide⟩
  exact (fork_data_good Bnum 0 800 true (by decide) (by decide) (by decide) (by decide) (by decide)
    (by decide)).1

end Formal.Cells.ForkData

/-! ## 3. C11: H_AMERGE_IDX (bdc_amerge index bundling against R0) -/

namespace Formal.Cells.ForkData.AMerge
open Formal.Cells Formal.Cells.ArbHeldTimed Formal.Cells.ArbHeldTimed2
open Formal.Cells.AMergeTimed Formal.Cells.AMergeTimedW

/-- **H_AMERGE_IDX** (row C11): `index = g2 | in1_ack` must name the token's
owner at the consumer `su` before that token's request does, in all three races
Cm2 found: the new owner's grant (`BidxA`), the previous owner's ack/grant fall
(`BidxB`), and the `in1_ack` fork into the index LUT (`IdxAckFork`). The
consumer is the abstract capture point of `AMergeTimed.Wd` (`wid`, `su`, `dz`). -/
structure H_AMERGE_IDX (D : Dl) (W : Wd) (cmin : Int) : Prop where
  new_owner : BidxA D W
  old_owner : BidxB D W
  ack_fork : IdxAckFork D W cmin

/-- **Sufficiency** (with the arbiter's own RT2b): in a client 1 -> client 2
handover the consumer reads 1 from `su` before the capture; in client 2 ->
client 1 it reads 0; while client 2's ack is high the index LUT says 1. Every
run of the real arbiter, every server, every capture instant allowed by
H_REQ_PATH. -/
theorem amerge_idx_sufficient {D : Dl} {W : Wd} {cmin : Int} (H : H_AMERGE_IDX D W cmin)
    (H_RT2 : RT2b D) :
    (∀ (s : Sigs) (t0 ta TA TA2 Hz Zr : Int), Run D s → Scn D s t0 ta TA TA2 Hz →
      ReqZ s (TR D t0) Hz Zr W.dz →
      ∀ t, Zr - W.su ≤ t → t - W.wid - W.wgi - W.xr < Hz → Cons W s t = true) ∧
    (∀ (s : Sigs) (t0 ta TA TA2 Hz Zr : Int), Run D s → Scn2 D s t0 ta TA TA2 Hz →
      ReqZ s (TRb D t0) Hz Zr W.dz →
      ∀ t, Zr - W.su ≤ t → t - W.wid < Hz → Cons W s t = false) ∧
    (∀ (s : Sigs) (Tq Ar t1 Hz : Int),
      (∀ t, s.g2 t =
        (FG2 (s.r1 (t - D.wr1g - D.g2r)) (s.r2 (t - D.wr2g - D.g2r)) (s.q (t - D.wq - D.g2r)) ||
         FG2 (s.r1 (t - D.wr1g - D.g2f)) (s.r2 (t - D.wr2g - D.g2f)) (s.q (t - D.wq - D.g2f)))) →
      FkScn D W s Tq Ar t1 Hz cmin → ∀ t, Ar ≤ t → t < Hz → Idx W s t = true) :=
  ⟨fun _ _ _ _ _ _ _ R S hZ => bidx_new_owner R S hZ H.new_owner,
   fun _ _ _ _ _ _ _ R S hZ => bidx_old_owner R S H_RT2 hZ H.old_owner,
   fun _ _ _ _ _ hg F => idx_ack_fork_hold hg F H.ack_fork⟩

/-- **Necessity of the exact legs.** (a) `¬ BidxA` (with 7g's A0 fork and
H_Z_IN_SRV): at the minimal request path the consumer still reads the
previous owner. (b) At a consistent corner (`xr = xf`), failing `BidxB.ack`:
the consumer still reads 1 for client 1's token. (c) With the minimal client,
`¬ IdxAckFork`: the index is 0 while `in1_ack` is high. The `gack`/`grant` legs
of `BidxB` are sufficient only here (Cm2: `grant` has its own counter-trace
`bidx_old_owner_counter_g`, `gack` none). -/
theorem amerge_idx_necessary {D : Dl} {W : Wd} {cmin : Int} :
    (A0Fork D → W.dz ≤ D.smin → ¬ BidxA D W →
      ∀ (s : Sigs) (t0 ta TA TA2 Hz : Int), Run D s → Scn D s t0 ta TA TA2 Hz →
        Cons W s (RR D TA + W.dz - W.su) = false) ∧
    (W.xr = W.xf →
      ¬ (D.wa02 + D.c2f + W.wai + W.xf + W.wid + W.su ≤ D.wa0s + D.qr + D.wfb + D.Rrq + W.dz) →
      ∀ (s : Sigs) (t0 ta TA TA2 Hz : Int), Run D s → Scn2 D s t0 ta TA TA2 Hz →
        RRb D TA + W.dz - W.su - W.wid - W.wai - W.xr < Hz →
        Cons W s (RRb D TA + W.dz - W.su) = true) ∧
    (¬ IdxAckFork D W cmin →
      ∀ (s : Sigs) (Tq Ar t1 Hz : Int),
        (∀ t, s.g2 t =
          (FG2 (s.r1 (t - D.wr1g - D.g2r)) (s.r2 (t - D.wr2g - D.g2r)) (s.q (t - D.wq - D.g2r)) ||
           FG2 (s.r1 (t - D.wr1g - D.g2f)) (s.r2 (t - D.wr2g - D.g2f)) (s.q (t - D.wq - D.g2f)))) →
        FkScn D W s Tq Ar t1 Hz cmin → t1 = Ar + cmin →
        t1 + D.wr2g + D.g2f + W.wgi + W.xf < Hz →
        s.A2 (t1 + D.wr2g + D.g2f + W.wgi + W.xf) = true ∧
        Idx W s (t1 + D.wr2g + D.g2f + W.wgi + W.xf) = false) :=
  ⟨fun hf hz hn _ _ _ _ _ _ R S => bidx_new_owner_counter R S hf hz hn,
   fun hx hn _ _ _ _ _ _ R S hz => bidx_old_owner_counter R S (by rw [hx]; omega) hz,
   fun hn _ _ _ _ _ hg F hm hz => idx_ack_fork_counter_minclient hg F hm hn hz⟩

/-- **Non-vacuity.** At SLOW_MAX with DELAY = 12 (Cm2's `Ds`, `Ws`) and a
two-arc client (`cmin = 248`), all of H_AMERGE_IDX and the arbiter's RT2b hold;
the runs that realise both handovers are `AMergeTimedW.nonvacuous_slow`. -/
theorem amerge_idx_nonvacuous : H_AMERGE_IDX Ds Ws 248 ∧ RT2b Ds := by
  have h := nonvacuous_slow
  refine ⟨⟨h.1, h.2.1, ?_⟩, h.2.2.2.1⟩
  simp [IdxAckFork, Ds, Ws, dW, wW]

/-- **The data-mux leg is empty in gcd_hw.** Every control_merge there is
`bdc_amerge2_0`/`bdc_amerge3_0` (width 0): `in_k_data` are tied `1'b0` and
`z_data` is left unconnected, so `z_data = index ? in1_data : in0_data` is the
constant 0 whatever the index does: no timing obligation. -/
theorem amerge_data_const (sel : Bool) : (if sel then false else false) = false := by
  cases sel <;> rfl

end Formal.Cells.ForkData.AMerge
