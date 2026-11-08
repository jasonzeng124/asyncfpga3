import Formal.Target.SpecMono
import Formal.Target.SpecRunt
import Formal.Cells.CexX16.Refute

/-!
# Formal.Cells.CexX16.Frontier — the κ = 0.40 refutation for every larger (g, κ), every w ≤ 20, and w = 0

Shard B, 2026-11-08.

**Problem, plainly.** `CexX16.not_netCorrectSeqRunt20` refutes THE headline statement at exactly `⟨1, 10/25⟩`. Is it
also false at every larger guard and scatter, for every narrower runt filter, and for the plain statement (no runt
hypothesis)?

**Proved.** Yes, by shard A's monotonicity lemmas (`seqRuntOn_anti_p`, `seqRuntOn_anti_w`, copied here from `FrontierRunt`) and
`SpecRunt.seqRunt_of_seq`:
* `not_seqRunt20_above40`: `NetCorrectSeqRunt 20` is false for every `g ≥ 1`, `κ ≥ 10/25` (with `κ ≤ 1` not needed
  for the larger parameter), `T ≥ 132`, `Δo ≤ 3000`, reset 400 ns;
* `not_seqRunt_le20_above40`: the same for every runt width `w ≤ 20`;
* `not_seq_above40`: the plain statement `NetCorrectSeq` is false there too.

**Not shown.** Other reset lengths (only R = 400 ns; shard C's `Net/Stretch` route is not applied here), κ < 10/25.
-/

namespace Formal.Cells.CexX16.Frontier
open Formal.Target Formal.Target.DecodedPS

/-! Shard A's monotonicity lemmas, copied verbatim from `Formal.Target.FrontierRunt` (importing that file would
build its two witnesses as well). -/

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


/-- **THE headline statement (H_RUNT(20 ps)) is false on THE target for every `g ≥ 1`, `κ ≥ 10/25`.** -/
theorem not_seqRunt20_above40 {p : DelayPar} (hg : 1 ≤ p.g) (hk : 10 / 25 ≤ p.κ)
    (T su Δo : Nat) (hT : 132 ≤ T) (hΔ : Δo ≤ 3000) :
    ¬ NetCorrectSeqRunt 20 net boundary arbs p T 400000 su Δo := by
  intro h
  have hle : Formal.Cells.CexX16.pK.LE p := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Formal.Cells.CexX16.pK] <;> norm_num <;> linarith
  exact Formal.Cells.CexX16.not_netCorrectSeqRunt20 T su Δo hT hΔ (seqRuntOn_anti_p hle h)

/-- And for every runt width `w ≤ 20` ps. -/
theorem not_seqRunt_le20_above40 {w : Nat} (hw : w ≤ 20) {p : DelayPar} (hg : 1 ≤ p.g) (hk : 10 / 25 ≤ p.κ)
    (T su Δo : Nat) (hT : 132 ≤ T) (hΔ : Δo ≤ 3000) :
    ¬ NetCorrectSeqRunt w net boundary arbs p T 400000 su Δo :=
  fun h => not_seqRunt20_above40 hg hk T su Δo hT hΔ (seqRuntOn_anti_w hw h)

/-- **The plain statement `NetCorrectSeq` is false there too.** -/
theorem not_seq_above40 {p : DelayPar} (hg : 1 ≤ p.g) (hk : 10 / 25 ≤ p.κ)
    (T su Δo : Nat) (hT : 132 ≤ T) (hΔ : Δo ≤ 3000) :
    ¬ NetCorrectSeq net boundary arbs p T 400000 su Δo :=
  fun h => not_seqRunt20_above40 hg hk T su Δo hT hΔ (seqRunt_of_seq _ 20 h)

end Formal.Cells.CexX16.Frontier
