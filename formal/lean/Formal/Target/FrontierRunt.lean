import Formal.Target.SpecMono
import Formal.Target.SpecRunt
import Formal.Target.CexRunt44.Refute

/-!
# Formal.Target.FrontierRunt — the headline statement under H_RUNT(w): monotonicity and where it is false

Shard A, 2026-11-07.

**Problem, plainly.** The owner's headline is THE statement with the runt hypothesis H_RUNT(20 ps)
(`SpecRunt.NetCorrectSeqRunt 20`). Its margin is reported as a (g, κ) frontier, as for the plain statement. Two
questions: is that margin a down-set (so one refutation covers every larger g, κ), and where is it known to fail?

**Proved.**
* `seqRuntOn_anti_p`: for every pin class `L`, `w`, netlist, boundary and arbiter list, `NetCorrectSeqRuntOn L w`
  at `(g', κ')` implies it at every `(g, κ)` inside (`DelayPar.LE`), exactly as `SpecMono.seq_anti_p` for the
  plain statement; `seqRuntOn_anti_w`: proved at `w` implies proved at every larger `w'` (a larger `w` filters
  more, so fewer behaviours), i.e. a refutation at `w'` is one at every `w ≤ w'`.
* `not_seqRunt20_above44`: with `CexRunt44.not_netCorrectSeqRunt20` (shard C's adversary, checked here under
  H_RUNT(20)), THE headline statement `NetCorrectSeqRunt 20` on THE target is false for every `g ≥ 1`,
  `κ ≥ 11/25`, `T ≥ 123`, any `su`, `Δo ≤ 3000`, reset 400 ns; and so for every `w ≤ 20` as well
  (`not_seqRunt_le20_above44`).

**Not shown.** Any point where the statement holds (shard B proves the binding race row safe for κ ≤ 0.41, one row
only); `w > 20`; other reset lengths.
-/

namespace Formal.Target.FrontierRunt
open Formal.Target Formal.Target.DecodedPS

theorem gateOKRuntOn_mono {L : Gate → Bool} {w : Nat} {p p' : DelayPar} (hp : p.LE p') {c : ℚ} (h0 : 0 ≤ c)
    (h1 : c ≤ 1) {g : Gate} {x : Beh} (h : GateOKRuntOn L w p c g x) : GateOKRuntOn L w p' c g x := by
  obtain ⟨f, hm, ht⟩ := h
  refine ⟨f, hm, fun t hs => ?_⟩
  have := ht t (le_trans (start_mono hp g) hs)
  exact ⟨fun i hi => ⟨(this.1 i hi).1, adm_mono hp h0 h1 (this.1 i hi).2.1, (this.1 i hi).2.2⟩, this.2⟩

theorem behavesRuntOn_mono {L : Gate → Bool} {w : Nat} {p p' : DelayPar} (hp : p.LE p') {N : Net} {x : Beh}
    (h : BehavesRuntOn L w p N x) : BehavesRuntOn L w p' N x := by
  obtain ⟨c, h0, h1, hg⟩ := h
  exact ⟨c, h0, h1, fun g hg' => gateOKRuntOn_mono hp h0 h1 (hg g hg')⟩

/-- **The runt-filtered margin is a down-set in (g, κ).** -/
theorem seqRuntOn_anti_p {L : Gate → Bool} {w : Nat} {N : Net} {B : Boundary} {A : List ArbNodes}
    {p p' : DelayPar} {T R su Δo : Nat} (hp : p.LE p') (h : NetCorrectSeqRuntOn L w N B A p' T R su Δo) :
    NetCorrectSeqRuntOn L w N B A p T R su Δo :=
  fun x n va vb hb ha he hs => h x n va vb (behavesRuntOn_mono hp hb) ha he hs

theorem noRuntRead_anti {w w' : Nat} (hw : w ≤ w') {s : Sig} {u : Nat} (h : NoRuntRead w' s u) :
    NoRuntRead w s u :=
  fun a b hp hab hu => h a b hp (by omega) hu

/-- **Proved at `w` gives proved at every larger `w'`** (H_RUNT(w') admits fewer behaviours). -/
theorem seqRuntOn_anti_w {L : Gate → Bool} {w w' : Nat} (hw : w ≤ w') {N : Net} {B : Boundary}
    {A : List ArbNodes} {p : DelayPar} {T R su Δo : Nat} (h : NetCorrectSeqRuntOn L w N B A p T R su Δo) :
    NetCorrectSeqRuntOn L w' N B A p T R su Δo := by
  intro x n va vb hb ha he hs
  refine h x n va vb ?_ ha he hs
  obtain ⟨c, h0, h1, hg⟩ := hb
  refine ⟨c, h0, h1, fun g hg' => ?_⟩
  obtain ⟨f, hm, ht⟩ := hg g hg'
  exact ⟨f, hm, fun t h2 => ⟨fun i hi => ⟨((ht t h2).1 i hi).1, ((ht t h2).1 i hi).2.1,
    fun hL => noRuntRead_anti hw (((ht t h2).1 i hi).2.2 hL)⟩, (ht t h2).2⟩⟩

/-- **THE headline statement (H_RUNT(20 ps)) is false on THE target for every `g ≥ 1`, `κ ≥ 11/25`.** -/
theorem not_seqRunt20_above44 {p : DelayPar} (hg : 1 ≤ p.g) (hk : 11 / 25 ≤ p.κ)
    (T su Δo : Nat) (hT : 123 ≤ T) (hΔ : Δo ≤ 3000) :
    ¬ NetCorrectSeqRunt 20 net boundary arbs p T 400000 su Δo := by
  intro h
  have hle : (Formal.Target.CexRuntP.pP 11).LE p := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Formal.Target.CexRuntP.pP] <;> norm_num <;> linarith
  exact Formal.Target.CexRunt44.not_netCorrectSeqRunt20 T su Δo hT hΔ (seqRuntOn_anti_p hle h)

/-- And for every runt width `w ≤ 20` ps. -/
theorem not_seqRunt_le20_above44 {w : Nat} (hw : w ≤ 20) {p : DelayPar} (hg : 1 ≤ p.g) (hk : 11 / 25 ≤ p.κ)
    (T su Δo : Nat) (hT : 123 ≤ T) (hΔ : Δo ≤ 3000) :
    ¬ NetCorrectSeqRunt w net boundary arbs p T 400000 su Δo :=
  fun h => not_seqRunt20_above44 hg hk T su Δo hT hΔ (seqRuntOn_anti_w hw h)

end Formal.Target.FrontierRunt
