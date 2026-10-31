import Formal.Cells.ZeroDelayTok
open Formal.Core.LutList

/-!
# ZeroDelayTokChain: the closed-loop `bd_link` chain carrying `k` tokens (physical half)

Probe Bzd3 (shard B); note `formal/notes/B-zero-delay-tok.md`. `ZeroDelayNetPhys`'s closed
loop (stage `i+1`'s request pin reads stage `i`'s node, stage `i`'s acknowledge pin reads stage
`i+1`'s node, stage `i+1`'s data pin reads stage `i`'s latch; only the source and the sink are
environment wires), now with `k` tokens: every stage is a `ZeroDelayTok` stage.

## Hypotheses (`ChainCellK`, every one named)

* per stage: `WfK`, the rows `RowsK` (LinkExact's six per token plus H_REARM);
* **H_LOOP_K**: token `j`'s request windows of stage `i+1` ARE stage `i`'s node windows of
  token `j`; token `j`'s acknowledge windows of stage `i` ARE stage `i+1`'s;
* H_WIRE_POS, H_RST_SEEN (as in `ZeroDelayNetPhys`, token 0);
* **H_DATA_LOOP_K**: stage `i+1`'s data window of token `j` starts once stage `i`'s latch surely
  outputs token `j` and ENDS no later than stage `i`'s next opening can first be read
  (`Tn_{i+1} j ≤ U0_i (j+1) + Elo_i`). With the hold row of stage `i+1` this is the cross-stage
  hold condition `V1_{i+1} j + Ehi_{i+1} ≤ U0_i (j+1) + Elo_i + Dlo_{i+1}`.

In the loop, H_REARM of stage `i` reads `V1_{i+1} j + Bhi_i ≤ U1_i (j+1)`: stage `i`'s next
rise must be surely read after its downstream neighbour has surely fallen. Both are triggered
by stage `i`'s own fall (through the downstream request pin, and through the upstream
acknowledge pin and back), so this is a genuine race in the closed loop, not implied.

## Results

* `chain_rstK`, `chain_tokK` (joint time induction for the reset phase; then, token by token,
  the high phases by induction over the stage index, then the low phases), `chain_specK`:
  every stage meets `SpecK` IN THE CLOSED LOOP, for `k` tokens.
* `chain2_witness`: two stages, two tokens (values 1 then 0), nonzero reads everywhere
  (380..900 ps), traces from a joint simulator: every hypothesis holds, so every stage meets
  the two-token spec.

NOT covered: the ABSTRACT half for `k` tokens (C's `Link` on a `k`-token zero-delay chain run
and one key retiming for it); see the note for what is missing and the lo-causality finding.
Core Lean only.
-/

namespace Formal.Cells.ZeroDelayTok
open Formal.Cells
open Formal.Cells.CElemFn
open Formal.Cells.LibGapSteer (Rd Rd.const)
open Formal.Cells.LibGapMux (int_ind)
open Formal.Cells.LibGapLatch
open Formal.Cells.LinkExact
open Formal.Cells.ZeroDelayNet (Rds)

/-- **The closed-loop chain with `k` tokens, cell level.** -/
structure ChainCellK (N : Nat) (P : Nat → ParK) : Prop where
  pos : 1 ≤ N
  kk : ∀ i < N, (P i).k = (P 0).k
  wf : ∀ i < N, WfK (P i)
  rows : ∀ i < N, RowsK (P i)
  /-- **H_LOOP_K** (request side). -/
  loop_a : ∀ i, i + 1 < N → ∀ j < (P 0).k, (P (i + 1)).Ra j = ((P i).tok j).U0 ∧
    (P (i + 1)).Ra1 j = ((P i).tok j).U1 ∧ (P (i + 1)).Fa j = ((P i).tok j).V0 ∧
    (P (i + 1)).Fa1 j = ((P i).tok j).V1
  /-- **H_LOOP_K** (acknowledge side). -/
  loop_b : ∀ i, i + 1 < N → ∀ j < (P 0).k, (P i).Rb j = ((P (i + 1)).tok j).U0 ∧
    (P i).Rb1 j = ((P (i + 1)).tok j).U1 ∧ (P i).Fb j = ((P (i + 1)).tok j).V0 ∧
    (P i).Fb1 j = ((P (i + 1)).tok j).V1
  /-- **H_WIRE_POS**. -/
  H_WIRE_POS : ∀ i, i + 1 < N → 1 ≤ (P (i + 1)).Alo ∧ 1 ≤ (P i).Blo
  /-- **H_RST_SEEN** (token 0). -/
  H_RST_SEEN : ∀ i, i + 1 < N → (P i).Rhi + (P (i + 1)).Ahi ≤ (P (i + 1)).W + (P (i + 1)).Rlo ∧
    (P (i + 1)).Rhi + (P i).Bhi ≤ (P i).W + (P i).Rlo
  /-- **H_DATA_LOOP_K**. -/
  H_DATA_LOOP : ∀ i, i + 1 < N → ∀ j < (P 0).k,
    ((P i).tok j).U1 + (P i).Ehi ≤ (P (i + 1)).Td j ∧ (P i).Td j + (P i).Dhi ≤ (P (i + 1)).Td j ∧
    (j + 1 < (P 0).k → (P (i + 1)).Tn j ≤ ((P i).tok (j + 1)).U0 + (P i).Elo)

/-- **A physical behaviour of the closed-loop `k`-token chain** (as `ZeroDelayNetPhys.ChainBeh`;
the source and the sink send / answer `k` tokens). -/
structure ChainBehK (N : Nat) (P : Nat → ParK) (vs : Nat → Bool) (rd : Nat → Rds) (r : Int → K3)
    (A B D C Q : Nat → Int → K3) : Prop where
  box : ∀ i < N, Box ((P i).tok 0) (rd i).pa (rd i).pb (rd i).pq (rd i).pr (rd i).pd (rd i).pe
    (rd i).pf
  r_hi : ∀ i < N, ∀ x, 0 ≤ x → x < (P i).W → r x = .t
  r_lo : ∀ i < N, ∀ x, (P i).W1 ≤ x → r x = .f
  ctl : ∀ i < N, CtlEq (rd i).pa (rd i).pb (rd i).pq (rd i).pr r (A i) (B i) (C i)
  lat : ∀ i < N, LutEq (rd i).pd (rd i).pe (rd i).pf (D i) (C i) (Q i)
  wa : ∀ i, i + 1 < N → A (i + 1) = C i
  wb : ∀ i, i + 1 < N → B i = C (i + 1)
  wd : ∀ i, i + 1 < N → D (i + 1) = Q i
  src_lo0 : ∀ x, x < (P 0).Ra 0 → A 0 x = .f
  src_hi : ∀ j < (P 0).k, ∀ x, (P 0).Ra1 j ≤ x → x < (P 0).Fa j → A 0 x = .t
  src_lo : ∀ j < (P 0).k, ∀ x, (P 0).Fa1 j ≤ x → (j + 1 < (P 0).k → x < (P 0).Ra (j + 1)) →
    A 0 x = .f
  snk_lo0 : ∀ x, x < (P (N - 1)).Rb 0 → B (N - 1) x = .f
  snk_hi : ∀ j < (P 0).k, ∀ x, (P (N - 1)).Rb1 j ≤ x → x < (P (N - 1)).Fb j → B (N - 1) x = .t
  snk_lo : ∀ j < (P 0).k, ∀ x, (P (N - 1)).Fb1 j ≤ x →
    (j + 1 < (P 0).k → x < (P (N - 1)).Rb (j + 1)) → B (N - 1) x = .f
  dat : DStabK (P 0) vs (D 0)

section chain
variable {N : Nat} {P : Nat → ParK} {vs : Nat → Bool} {rd : Nat → Rds} {r : Int → K3}
  {A B D C Q : Nat → Int → K3}

/-- **Reset phase, all stages at once** (joint time induction; `ZeroDelayNetPhys.chain_rst`). -/
theorem chain_rstK (CC : ChainCellK N P) (Bh : ChainBehK N P vs rd r A B D C Q) :
    ∀ t, ∀ i < N, (P i).Rhi ≤ t → t < ((P i).tok 0).U0 → C i t = .f := by
  have k0 := (CC.wf 0 CC.pos).pos
  apply int_ind (fun t => ∀ i < N, (P i).Rhi ≤ t → t < ((P i).tok 0).U0 → C i t = .f)
  · intro t ht i hi h1
    have := ((CC.wf i hi).wf 0 (CC.wf i hi).pos).hR; simp only [ParK.tok] at this; omega
  · intro t ht ih i hi h1 h2
    have W := (CC.wf i hi).wf 0 (CC.wf i hi).pos; have Bx := Bh.box i hi
    have Hc := (CC.rows i hi).conj 0 (CC.wf i hi).pos
    have s1 := W.hR; have s2 := W.hQ; have s3 := W.hA; have s4 := W.hB; have s5 := W.ha
    have s6 := W.hW
    have b1 := Bx.a; have b2 := Bx.b; have b3 := Bx.q; have b4 := Bx.r
    have c1 := Hc.H_RST_WIDTH; have c2 := Hc.H_RACE_UP
    simp only [ParK.tok, Par.U0, Par.U1, Par.Rel] at c2 h2 s1 s2 s3 s4 s5 s6 b1 b2 b3 b4 c1 ⊢
    rw [Bh.ctl i hi t ht]
    have g1 := (rd i).pr.ge t; have g2 := (rd i).pr.le t; have g3 := (rd i).pq.ge t
    have g4 := (rd i).pq.le t; have g5 := (rd i).pa.le t; have g6 := (rd i).pb.le t
    have g7 := (rd i).pa.ge t; have g8 := (rd i).pb.ge t
    by_cases hw : t < (P i).W + (P i).Rlo
    · rw [Bh.r_hi i hi _ (by omega) (by omega), c_rst]
    · have ha : A i ((rd i).pa.σ t) = .f := by
        rcases i with _ | j
        · exact Bh.src_lo0 _ (by omega)
        · rw [Bh.wa j hi]
          have la := CC.loop_a j hi 0 k0; have rs := (CC.H_RST_SEEN j hi).1
          have wp := (CC.H_WIRE_POS j hi).1
          simp only [ParK.tok, Par.U0] at la
          exact ih _ (by omega) j (by omega) (by omega) (by simp only [ParK.tok, Par.U0]; omega)
      have hb : B i ((rd i).pb.σ t) = .f := by
        by_cases e : i + 1 < N
        · rw [Bh.wb i e]
          have lb := CC.loop_b i e 0 k0; have rs := (CC.H_RST_SEEN i e).2
          have wp := (CC.H_WIRE_POS i e).2
          simp only [ParK.tok, Par.U0] at lb
          exact ih _ (by omega) (i + 1) e (by omega) (by simp only [ParK.tok, Par.U0]; omega)
        · have hi' : i = N - 1 := by omega
          subst hi'
          exact Bh.snk_lo0 _ (by omega)
      have hq : C i ((rd i).pq.σ t) = .f :=
        ih _ (by omega) i hi (by omega) (by simp only [ParK.tok, Par.U0]; omega)
      rw [ha, hb, hq, c_idle]

/-- The acknowledge pin of every stage is low where token `j`'s high phase reads it: before
token 0 from the reset phase (H_RST_SEEN), later from the downstream node's previous low phase
and H_REARM. -/
theorem chain_bloK (CC : ChainCellK N P) (Bh : ChainBehK N P vs rd r A B D C Q) {j : Nat}
    (hj : j < (P 0).k)
    (hlo : j ≠ 0 → ∀ i < N, ∀ t, ((P i).tok (j - 1)).V1 ≤ t → Bef (P i) (j - 1) t → C i t = .f) :
    ∀ i < N, ∀ x, ((P i).tok j).U1 - (P i).Bhi ≤ x → x < (P i).Rb j → B i x = .f := by
  intro i hi x h1 h2
  have kk := CC.kk i hi
  rcases j with _ | m
  · by_cases e : i + 1 < N
    · rw [Bh.wb i e]
      have lb := CC.loop_b i e 0 hj; have rs := (CC.H_RST_SEEN i e).2
      have W := (CC.wf i hi).wf 0 (CC.wf i hi).pos
      have := W.hR; have := W.hW; have := W.H_RST_EARLY; have := W.ha; have := W.hA
      simp only [ParK.tok, Par.U0, Par.U1] at *
      exact chain_rstK CC Bh x (i + 1) e (by omega) (by simp only [ParK.tok, Par.U0]; omega)
    · have hi' : i = N - 1 := by omega
      subst hi'
      exact Bh.snk_lo0 _ h2
  · have hr := (CC.rows i hi).rearm m (by omega)
    have hn := (CC.wf i hi).H_NEXT m (by omega)
    have wb := ((CC.wf i hi).wf m (by omega)).hb
    simp only [Rearm, ParK.tok, Par.U1] at hr h1 h2 wb
    by_cases e : i + 1 < N
    · rw [Bh.wb i e]
      have lb := CC.loop_b i e m (by omega); have lb' := CC.loop_b i e (m + 1) hj
      simp only [ParK.tok, Par.U0, Par.V1] at lb lb'
      refine hlo (by omega) (i + 1) e x ?_ ?_
      · simp only [ParK.tok, Par.V1, Nat.add_sub_cancel]; omega
      · intro _; simp only [ParK.tok, Par.U0, Nat.add_sub_cancel]; omega
    · have hi' : i = N - 1 := by omega
      subst hi'
      exact Bh.snk_lo m (by omega) x (by omega) (fun _ => h2)

/-- **Token by token**: for every token `j`, every stage's high phase (induction over the stage
index, using the previous token's low phases), then every stage's low phase. -/
theorem chain_tokK (CC : ChainCellK N P) (Bh : ChainBehK N P vs rd r A B D C Q) :
    ∀ j < (P 0).k,
      (∀ i < N, ∀ t, ((P i).tok j).U1 ≤ t → t < ((P i).tok j).V0 → C i t = .t) ∧
      (∀ i < N, ∀ t, ((P i).tok j).V1 ≤ t → Bef (P i) j t → C i t = .f) := by
  intro j
  induction j with
  | zero =>
    intro hj
    exact chain_phase CC Bh hj (fun h => absurd rfl h)
  | succ m ih =>
    intro hj
    exact chain_phase CC Bh hj (fun _ => (ih (by omega)).2)
where
  chain_phase (CC : ChainCellK N P) (Bh : ChainBehK N P vs rd r A B D C Q) {j : Nat}
      (hj : j < (P 0).k)
      (hlo : j ≠ 0 → ∀ i < N, ∀ t, ((P i).tok (j - 1)).V1 ≤ t → Bef (P i) (j - 1) t →
        C i t = .f) :
      (∀ i < N, ∀ t, ((P i).tok j).U1 ≤ t → t < ((P i).tok j).V0 → C i t = .t) ∧
      (∀ i < N, ∀ t, ((P i).tok j).V1 ≤ t → Bef (P i) j t → C i t = .f) := by
    have blo := chain_bloK CC Bh hj hlo
    have hiP : ∀ i < N, ∀ t, ((P i).tok j).U1 ≤ t → t < ((P i).tok j).V0 → C i t = .t := by
      intro i
      induction i with
      | zero =>
        intro hi
        exact ZeroDelayNet.node_hi_loc ((CC.wf 0 hi).wf j hj) (box_tok (Bh.box 0 hi) j)
          (Bh.ctl 0 hi) ((CC.rows 0 hi).conj j hj).H_RACE_UP (Bh.r_lo 0 hi) (Bh.src_hi j hj)
          (blo 0 hi)
      | succ i ih =>
        intro hi
        have kk := CC.kk (i + 1) hi
        have la := CC.loop_a i hi j hj
        refine ZeroDelayNet.node_hi_loc ((CC.wf _ hi).wf j (by omega)) (box_tok (Bh.box _ hi) j)
          (Bh.ctl _ hi) ((CC.rows _ hi).conj j (by omega)).H_RACE_UP (Bh.r_lo _ hi)
          (fun x h1 h2 => ?_) (blo _ hi)
        rw [Bh.wa i hi]
        simp only [ParK.tok] at h1 h2
        rw [la.2.1] at h1; rw [la.2.2.1] at h2
        exact ih (by omega) x h1 h2
    refine ⟨hiP, ?_⟩
    have bhi : ∀ i < N, ∀ x, (P i).Rb1 j ≤ x → x < (P i).Fb j → B i x = .t := by
      intro i hi x h1 h2
      by_cases e : i + 1 < N
      · rw [Bh.wb i e]
        have lb := CC.loop_b i e j hj
        rw [lb.2.1] at h1; rw [lb.2.2.1] at h2
        exact hiP (i + 1) e x h1 h2
      · have hi' : i = N - 1 := by omega
        subst hi'
        exact Bh.snk_hi j hj _ h1 h2
    intro i
    induction i with
    | zero =>
      intro hi
      exact node_lo_loc_k (CC.wf 0 hi) (Bh.box 0 hi) (Bh.ctl 0 hi) hj
        ((CC.rows 0 hi).conj j hj).H_RACE_DN (Bh.src_lo j hj) (bhi 0 hi)
    | succ i ih =>
      intro hi
      have kk := CC.kk (i + 1) hi; have kk0 := CC.kk i (by omega)
      have la := CC.loop_a i hi j hj
      refine node_lo_loc_k (CC.wf _ hi) (Bh.box _ hi) (Bh.ctl _ hi) (by omega)
        ((CC.rows _ hi).conj j (by omega)).H_RACE_DN (fun x h1 h2 => ?_) (bhi _ hi)
      rw [Bh.wa i hi]
      rw [la.2.2.2] at h1
      refine ih (by omega) x h1 (fun h => ?_)
      have := h2 (by omega)
      have la' := CC.loop_a i hi (j + 1) (by omega)
      rw [la'.1] at this
      exact this

/-- **Every stage meets the `k`-token spec in the closed loop.** -/
theorem chain_specK (CC : ChainCellK N P) (Bh : ChainBehK N P vs rd r A B D C Q) :
    ∀ i < N, SpecK (P i) vs (rd i).pd (rd i).pe (C i) (Q i) := by
  have T := chain_tokK CC Bh
  have sp : ∀ i (hi : i < N), DStabK (P i) vs (D i) →
      SpecK (P i) vs (rd i).pd (rd i).pe (C i) (Q i) := by
    intro i hi hd
    have kk := CC.kk i hi
    exact spec_of_phases (CC.wf i hi) (CC.rows i hi) (Bh.box i hi) (Bh.lat i hi) hd
      (fun t h1 h2 => chain_rstK CC Bh t i hi h1 h2)
      (fun j hj => (T j (by omega)).1 i hi) (fun j hj => (T j (by omega)).2 i hi)
  intro i
  induction i with
  | zero => intro hi; exact sp 0 hi Bh.dat
  | succ m ih =>
    intro hi
    apply sp _ hi
    have Sm := ih (by omega)
    have kk := CC.kk (m + 1) hi; have kk0 := CC.kk m (by omega)
    intro j hj x h1 h2
    have dl := CC.H_DATA_LOOP m hi j (by omega)
    have bx := Bh.box m (by omega)
    have := bx.e; have := bx.d
    simp only [ParK.tok] at this
    rw [Bh.wd m hi]
    refine Sm.out j (by omega) x (by simp only [ParK.tok] at *; omega)
      (by simp only [ParK.tok] at *; omega) (fun h => ?_)
    have := dl.2.2 (by omega)
    simp only [ParK.tok, Par.U0] at this ⊢
    omega

end chain

end Formal.Cells.ZeroDelayTok
