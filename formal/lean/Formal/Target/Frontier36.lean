import Formal.Target.SpecMono
import Formal.Target.SpecRunt
import Formal.Target.CexQ36.Refute
import Formal.Target.CexQ36.AnyR

/-!
# The κ = 9/25 livelock refutation carried to the frontier (shard A, 2026-11-09)

**Problem, plainly.** Where, on the (g, κ, w) axes, does the κ = 0.36 livelock (`CexQ36.Refute`) refute THE
statement?

**Proved.** `not_seqRunt_le20_above36`: THE headline statement `NetCorrectSeqRunt w` on THE target is false for every
runt width `w ≤ 20`, every guard `g ≥ 1`, every scatter `κ ≥ 9/25`, every `T ≥ 140`, any `su`, `Δo ≤ 3000`, reset
400 ns; `not_seq_above36`: so is the plain frozen statement `NetCorrectSeq` (w = 0, `SpecRunt.runt_zero`).
The monotonicity lemmas are copies of `FrontierRunt`'s (that module imports the κ = 11/25 and g = 8/5 witnesses,
whose builds this file does not need).

`not_seqRunt_le20_above36_R`, `not_seq_above36_R`: the same for every reset length R ≥ 400 ns (`CexQ36.AnyR`).

**Not shown.** κ < 9/25.
-/

namespace Formal.Target.Frontier36
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

/-- **THE headline statement is false for every `w ≤ 20`, `g ≥ 1`, `κ ≥ 9/25`** (T ≥ 140, Δo ≤ 3 ns, reset 400 ns),
by a livelock. -/
theorem not_seqRunt_le20_above36 {w : Nat} (hw : w ≤ 20) {p : DelayPar} (hg : 1 ≤ p.g) (hk : 9 / 25 ≤ p.κ)
    (T su Δo : Nat) (hT : 140 ≤ T) (hΔ : Δo ≤ 3000) :
    ¬ NetCorrectSeqRunt w net boundary arbs p T 400000 su Δo := by
  intro h
  have hle : (Formal.Target.CexRuntP.pP 9).LE p := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Formal.Target.CexRuntP.pP] <;> norm_num <;> linarith
  exact Formal.Target.CexQ36.not_netCorrectSeqRunt20 T su Δo hT hΔ (seqRuntOn_anti_p hle (seqRuntOn_anti_w hw h))

/-- **The plain frozen statement too** (every `g ≥ 1`, `κ ≥ 9/25`). -/
theorem not_seq_above36 {p : DelayPar} (hg : 1 ≤ p.g) (hk : 9 / 25 ≤ p.κ)
    (T su Δo : Nat) (hT : 140 ≤ T) (hΔ : Δo ≤ 3000) :
    ¬ NetCorrectSeq net boundary arbs p T 400000 su Δo :=
  fun h => not_seqRunt_le20_above36 (w := 0) (by norm_num) hg hk T su Δo hT hΔ (runt_zero.mpr h)

/-- **For every reset length `R ≥ 400 ns`**: every `w ≤ 20`, `g ≥ 1`, `κ ≥ 9/25`, `T ≥ 140`, `Δo ≤ 3 ns`. -/
theorem not_seqRunt_le20_above36_R {w : Nat} (hw : w ≤ 20) {p : DelayPar} (hg : 1 ≤ p.g) (hk : 9 / 25 ≤ p.κ)
    (R T su Δo : Nat) (hR : 400000 ≤ R) (hT : 140 ≤ T) (hΔ : Δo ≤ 3000) :
    ¬ NetCorrectSeqRunt w net boundary arbs p T R su Δo := by
  intro h
  have hle : (Formal.Target.CexRuntP.pP 9).LE p := by
    refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> simp only [Formal.Target.CexRuntP.pP] <;> norm_num <;> linarith
  exact Formal.Target.CexQ36.AnyR.not_netCorrectSeqRunt20_R R T su Δo hR hT hΔ
    (seqRuntOn_anti_p hle (seqRuntOn_anti_w hw h))

/-- **The plain frozen statement, every reset length `R ≥ 400 ns`.** -/
theorem not_seq_above36_R {p : DelayPar} (hg : 1 ≤ p.g) (hk : 9 / 25 ≤ p.κ)
    (R T su Δo : Nat) (hR : 400000 ≤ R) (hT : 140 ≤ T) (hΔ : Δo ≤ 3000) :
    ¬ NetCorrectSeq net boundary arbs p T R su Δo :=
  fun h => not_seqRunt_le20_above36_R (w := 0) (by norm_num) hg hk R T su Δo hR hT hΔ (runt_zero.mpr h)

end Formal.Target.Frontier36
