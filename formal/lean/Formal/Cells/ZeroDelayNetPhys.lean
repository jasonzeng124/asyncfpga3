import Formal.Cells.ZeroDelayNet

/-!
# ZeroDelayNetPhys: the whole physical link chain refines ONE zero-delay run of C's chain

Probe Bzd2 (shard B); note `formal/notes/B-zero-delay-net.md`. The trace-level half of
`ZeroDelayNet`: every stage is a real `LinkExact` behaviour (bd_c2n node at its real INIT,
Kleene, per-pin read maps in their boxes; bd_latch bit), and the stages are WIRED to each
other: stage `i+1`'s request pin reads stage `i`'s node, stage `i`'s acknowledge pin reads
stage `i+1`'s node, stage `i+1`'s data pin reads stage `i`'s latch output (each through its
own read map, the wire folded into the pin's window). Only the source (request + data of
stage 0) and the sink (acknowledge of stage `N-1`) are open environment wires.

## Model (every hypothesis named)

* `ChainCell`: the parameter-level closed loop `ChainPar` (H_LOOP, `Wf` per stage, H_SRC,
  H_SNK), plus per stage the six `bd_link.stage` rows (`Conj`), plus three loop hypotheses:
  **H_WIRE_POS** (an inter-stage read takes at least 1 ps: `Alo, Blo ≥ 1` on internal pins),
  **H_RST_SEEN** (reset is still read high on a stage until its neighbours' nodes are surely
  read out of power-up: `Rhi_nbr + pinHi ≤ W + Rlo`), **H_DATA_LOOP** (stage `i+1`'s data
  window starts once stage `i`'s latch output is the token, `Td_{i+1} ≥ U1_i + Ehi_i` and
  `≥ Td_i + Dhi_i`; it then never ends, one token).
* `ChainBeh`: the traces. Power-up of every node and latch is ARBITRARY (X included) before
  time 0, as in LinkExact; so the internal request/acknowledge wires are NOT quiet at
  power-up (LinkExact's `Env.a_lo0` is not available, which is why H_RST_SEEN is needed).

## Results

* `chain_spec`: every stage meets LinkExact's `Spec` (node a window token with the
  input-derived windows, latch captures and holds the token) IN THE CLOSED LOOP. The reset
  phase is a joint time induction over all stages (`chain_rst`, needs H_WIRE_POS); the high
  and low phases are inductions over the stage index (`chain_hi`, `chain_lo`).
* **Headline** `chain_refines`: the physical chain refines ONE zero-delay run of C's chain
  network (`chain_abstract`: `Link` at every stage on the shared channels, `Protocol` and
  `Held` on every channel), with one global monotone retiming (`net_mono`) whose restriction
  to every stage is monotone (`stage_mono`), every node and every wire a window image
  (`NetRef`), every latch capturing the token.
* `chain_witness`: two stages, nonzero delays everywhere (reads 380..900 ps), traces built by
  a joint simulator (`jr`) of the coupled stages: every hypothesis holds, so the conclusion
  applies.

NOT covered: zero-delay inter-stage reads (H_WIRE_POS: the joint induction needs a strictly
earlier read; whether the result survives 0 ps is not decided); `DELAY`/`DACK` lines (the
asymmetric FASTRISE line is covered only if lumped into a symmetric read window); more than
one data bit beyond "one `LutEq` per bit, shared node"; a ring (initial tokens); fork/join and
the steer→mux diamond. Core Lean only.
-/

namespace Formal.Cells.ZeroDelayNet
open Formal.Cells
open Formal.Cells.CElemFn
open Formal.Cells.LibGapSteer (Rd Rd.const)
open Formal.Cells.LibGapMux (int_ind)
open Formal.Cells.LibGapLatch
open Formal.Cells.LinkExact
open Formal.Cells.ZeroDelayRefine

/-! ## 0. Per-stage node lemmas with only the LOCAL environment facts they read -/

section loc
variable {P : Par} {pa pb pq pr pd pe pf : Rd} {r a b c d q : Int → K3}

/-- LinkExact's `node_hi`, reading the acknowledge only on `[U1 - Bhi, Rb)`. -/
theorem node_hi_loc (S : Wf P) (B : Box P pa pb pq pr pd pe pf)
    (hc : CtlEq pa pb pq pr r a b c) (h2 : P.U1 + P.Qhi ≤ P.Rel)
    (r_lo : ∀ x, P.W1 ≤ x → r x = .f) (a_hi : ∀ x, P.Ra1 ≤ x → x < P.Fa → a x = .t)
    (b_lo : ∀ x, P.U1 - P.Bhi ≤ x → x < P.Rb → b x = .f) :
    ∀ t, P.U1 ≤ t → t < P.V0 → c t = .t := by
  have s1 := S.hR; have s2 := S.hQ; have s3 := S.hA; have s4 := S.hB; have s5 := S.ha
  have s6 := S.H_RST_EARLY; have s7 := S.hW
  have b1 := B.a; have b2 := B.b; have b3 := B.q; have b4 := B.r
  simp only [Par.U1, Par.Rel, Par.V0] at *
  apply int_ind (fun t => P.Ra1 + P.Ahi ≤ t → t < max (P.Fa + P.Alo) (P.Rb + P.Blo) → c t = .t)
    (fun t ht h => by omega)
  intro t ht ih h3 h4
  rw [hc t ht]
  have g1 := pr.ge t; have g3 := pq.ge t; have g4 := pq.le t
  have g5 := pa.le t; have g6 := pb.le t; have g7 := pa.ge t; have g8 := pb.ge t
  rw [r_lo _ (by omega)]
  by_cases h5 : t < P.Fa + P.Alo ∧ t < P.Rb + P.Blo
  · rw [a_hi _ (by omega) (by omega), b_lo _ (by omega) (by omega), c_follow1]
  · rw [ih _ (by omega) (by omega) (by omega)]
    by_cases h6 : t < P.Fa + P.Alo
    · rw [a_hi _ (by omega) (by omega), c_holdB]
    · rw [b_lo _ (by omega) (by omega), c_holdA]

/-- LinkExact's `node_lo` with only the local facts it reads. -/
theorem node_lo_loc (S : Wf P) (B : Box P pa pb pq pr pd pe pf)
    (hc : CtlEq pa pb pq pr r a b c) (h3 : P.V1 + P.Qhi ≤ P.Fb + P.Blo)
    (a_lo : ∀ x, P.Fa1 ≤ x → a x = .f) (b_hi : ∀ x, P.Rb1 ≤ x → x < P.Fb → b x = .t) :
    ∀ t, P.V1 ≤ t → c t = .f := by
  have s1 := S.hR; have s2 := S.hQ; have s3 := S.hA; have s4 := S.hB; have s5 := S.ha
  have s6 := S.H_RST_EARLY; have s7 := S.hW; have s8 := S.hb
  have b1 := B.a; have b2 := B.b; have b3 := B.q
  simp only [Par.V1] at *
  apply int_ind (fun t => max (P.Fa1 + P.Ahi) (P.Rb1 + P.Bhi) ≤ t → c t = .f)
    (fun t ht h => by omega)
  intro t ht ih h4
  rw [hc t ht]
  have g3 := pq.ge t; have g4 := pq.le t
  have g5 := pa.ge t; have g6 := pb.le t; have g7 := pb.ge t
  rw [a_lo _ (by omega)]
  by_cases h5 : t < P.Fb + P.Blo
  · rw [b_hi _ (by omega) (by omega), c_follow0]
  · rw [ih _ (by omega) (by omega), c_hold0]

/-- LinkExact's `sufficient`, from the three node phases (however obtained). -/
theorem spec_loc {v : Bool} (S : Wf P) (H : Conj P) (B : Box P pa pb pq pr pd pe pf)
    (lat : LutEq pd pe pf d c q) (dat : DStab v P.Td P.Tn d)
    (N1 : ∀ t, P.Rhi ≤ t → t < P.U0 → c t = .f) (N2 : ∀ t, P.U1 ≤ t → t < P.V0 → c t = .t)
    (N3 : ∀ t, P.V1 ≤ t → c t = .f) : Spec P v pd pe c q := by
  have s1 := S.hR; have s2 := S.hQ; have s3 := S.hA; have s4 := S.hB; have s5 := S.ha
  have s6 := S.H_RST_EARLY; have s7 := S.hW; have s8 := S.hb; have s9 := S.hD
  have s10 := S.hE; have s11 := S.hF
  have b1 := B.d; have b2 := B.e; have b3 := B.f
  have h1 := H.H_RACE_UP; have h2 := H.H_SETUP_PULSE; have h3 := H.H_SETUP_DATA
  have h4 := H.H_HOLD
  simp only [Par.U0, Par.U1, Par.Rel, Par.V0, Par.V1] at *
  have hT : EnTok (P.Ra1 + P.Ahi) (max (P.Fa + P.Alo) (P.Rb + P.Blo))
      (max (P.Fa1 + P.Ahi) (P.Rb1 + P.Bhi)) c := ⟨N2, N3⟩
  have hcap : Capt v (max (P.Fa + P.Alo) (P.Rb + P.Blo)) pe q :=
    latch_pin_ok v _ _ _ P.Td P.Tn pd pe pf d c q (by omega) (by omega) (by omega) hT dat
      lat (by omega) (by omega) (by omega)
  refine ⟨by simp only [Par.U1, Par.V0]; omega, N1, N2, N3, hcap, ?_⟩
  intro t ht1 ht2
  simp only [Par.U1] at ht1
  have g1 := pe.ge t; have g2 := pe.le t; have g3 := pd.ge t; have g4 := pd.le t
  by_cases hB : max (P.Fa + P.Alo) (P.Rb + P.Blo) ≤ pe.σ t
  · exact hcap t (by omega) hB
  · rw [lat t (by omega), N2 _ (by omega) (by omega), m_t]
    exact dat _ (by omega) (by omega)

end loc

/-! ## 1. The closed-loop chain: hypotheses and behaviours -/

/-- The seven read maps of one stage. -/
structure Rds where
  pa : Rd
  pb : Rd
  pq : Rd
  pr : Rd
  pd : Rd
  pe : Rd
  pf : Rd

/-- **The closed-loop chain, cell level.** -/
structure ChainCell (N : Nat) (P : Nat → Par) : Prop where
  par : ChainPar N P
  conj : ∀ i < N, Conj (P i)
  /-- **H_WIRE_POS**: an inter-stage read takes at least 1 ps. -/
  H_WIRE_POS : ∀ i, i + 1 < N → 1 ≤ (P (i + 1)).Alo ∧ 1 ≤ (P i).Blo
  /-- **H_RST_SEEN**: a stage still reads reset high until its neighbours' nodes (definite
  from their own `Rhi`) are surely read through its request / acknowledge pin. -/
  H_RST_SEEN : ∀ i, i + 1 < N → (P i).Rhi + (P (i + 1)).Ahi ≤ (P (i + 1)).W + (P (i + 1)).Rlo ∧
    (P (i + 1)).Rhi + (P i).Bhi ≤ (P i).W + (P i).Rlo
  /-- **H_DATA_LOOP**: stage `i+1`'s data window starts once stage `i`'s latch output is
  surely the token (LinkExact's `Spec.out` time, box form). -/
  H_DATA_LOOP : ∀ i, i + 1 < N → (P i).U1 + (P i).Ehi ≤ (P (i + 1)).Td ∧
    (P i).Td + (P i).Dhi ≤ (P (i + 1)).Td

/-- **A physical behaviour of the closed-loop chain.** `A i`, `B i`, `D i`: stage `i`'s
request, acknowledge and data pin drivers; `C i` its node, `Q i` its latch bit; `r` the shared
reset. Internal wires are the neighbours' nodes / latch outputs (`wa`, `wb`, `wd`); only the
source (`A 0`, `D 0`) and the sink (`B (N-1)`) are environment wires (LinkExact's `Env`
windows). Power-up (`t < 0`) of every node and latch: arbitrary. -/
structure ChainBeh (N : Nat) (P : Nat → Par) (v : Bool) (rd : Nat → Rds) (r : Int → K3)
    (A B D C Q : Nat → Int → K3) : Prop where
  box : ∀ i < N, Box (P i) (rd i).pa (rd i).pb (rd i).pq (rd i).pr (rd i).pd (rd i).pe (rd i).pf
  r_hi : ∀ i < N, ∀ x, 0 ≤ x → x < (P i).W → r x = .t
  r_lo : ∀ i < N, ∀ x, (P i).W1 ≤ x → r x = .f
  ctl : ∀ i < N, CtlEq (rd i).pa (rd i).pb (rd i).pq (rd i).pr r (A i) (B i) (C i)
  lat : ∀ i < N, LutEq (rd i).pd (rd i).pe (rd i).pf (D i) (C i) (Q i)
  wa : ∀ i, i + 1 < N → A (i + 1) = C i
  wb : ∀ i, i + 1 < N → B i = C (i + 1)
  wd : ∀ i, i + 1 < N → D (i + 1) = Q i
  src_lo0 : ∀ x, x < (P 0).Ra → A 0 x = .f
  src_hi : ∀ x, (P 0).Ra1 ≤ x → x < (P 0).Fa → A 0 x = .t
  src_lo : ∀ x, (P 0).Fa1 ≤ x → A 0 x = .f
  snk_lo0 : ∀ x, x < (P (N - 1)).Rb → B (N - 1) x = .f
  snk_hi : ∀ x, (P (N - 1)).Rb1 ≤ x → x < (P (N - 1)).Fb → B (N - 1) x = .t
  snk_lo : ∀ x, (P (N - 1)).Fb1 ≤ x → B (N - 1) x = .f
  dat : DStab v (P 0).Td (P 0).Tn (D 0)

section chain
variable {N : Nat} {P : Nat → Par} {v : Bool} {rd : Nat → Rds} {r : Int → K3}
  {A B D C Q : Nat → Int → K3}

/-- **Reset phase, all stages at once** (joint time induction). -/
theorem chain_rst (CC : ChainCell N P) (Bh : ChainBeh N P v rd r A B D C Q) :
    ∀ t, ∀ i < N, (P i).Rhi ≤ t → t < (P i).U0 → C i t = .f := by
  apply int_ind (fun t => ∀ i < N, (P i).Rhi ≤ t → t < (P i).U0 → C i t = .f)
  · intro t ht i hi h1
    have := (CC.par.wf i hi).hR; omega
  · intro t ht ih i hi h1 h2
    have W := CC.par.wf i hi; have Bx := Bh.box i hi; have Hc := CC.conj i hi
    have s1 := W.hR; have s2 := W.hQ; have s3 := W.hA; have s4 := W.hB; have s5 := W.ha
    have s6 := W.hW
    have b1 := Bx.a; have b2 := Bx.b; have b3 := Bx.q; have b4 := Bx.r
    have c1 := Hc.H_RST_WIDTH; have c2 := Hc.H_RACE_UP
    simp only [Par.U0, Par.U1, Par.Rel] at c2 h2 ⊢
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
          have la := CC.par.loop_a j hi; have rs := (CC.H_RST_SEEN j hi).1
          have wp := (CC.H_WIRE_POS j hi).1
          simp only [Par.U0] at la
          exact ih _ (by omega) j (by omega) (by omega) (by simp only [Par.U0]; omega)
      have hb : B i ((rd i).pb.σ t) = .f := by
        by_cases e : i + 1 < N
        · rw [Bh.wb i e]
          have lb := CC.par.loop_b i e; have rs := (CC.H_RST_SEEN i e).2
          have wp := (CC.H_WIRE_POS i e).2
          simp only [Par.U0] at lb
          exact ih _ (by omega) (i + 1) e (by omega) (by simp only [Par.U0]; omega)
        · have hi' : i = N - 1 := by omega
          subst hi'
          exact Bh.snk_lo0 _ (by omega)
      have hq : C i ((rd i).pq.σ t) = .f :=
        ih _ (by omega) i hi (by omega) (by simp only [Par.U0]; omega)
      rw [ha, hb, hq, c_idle]

/-- The acknowledge pin of every stage is low where `node_hi_loc` reads it. -/
theorem chain_blo (CC : ChainCell N P) (Bh : ChainBeh N P v rd r A B D C Q) :
    ∀ i < N, ∀ x, (P i).U1 - (P i).Bhi ≤ x → x < (P i).Rb → B i x = .f := by
  intro i hi x h1 h2
  by_cases e : i + 1 < N
  · rw [Bh.wb i e]
    have lb := CC.par.loop_b i e; have rs := (CC.H_RST_SEEN i e).2
    have W := CC.par.wf i hi
    have := W.hR; have := W.hW; have := W.H_RST_EARLY; have := W.ha; have := W.hA
    simp only [Par.U0, Par.U1] at *
    exact chain_rst CC Bh x (i + 1) e (by omega) (by simp only [Par.U0]; omega)
  · have hi' : i = N - 1 := by omega
    subst hi'
    exact Bh.snk_lo0 _ h2

/-- **High phase**, by induction over the stage index. -/
theorem chain_hi (CC : ChainCell N P) (Bh : ChainBeh N P v rd r A B D C Q) :
    ∀ i < N, ∀ t, (P i).U1 ≤ t → t < (P i).V0 → C i t = .t := by
  intro i
  induction i with
  | zero =>
    intro hi
    exact node_hi_loc (CC.par.wf 0 hi) (Bh.box 0 hi) (Bh.ctl 0 hi) (CC.conj 0 hi).H_RACE_UP
      (Bh.r_lo 0 hi) Bh.src_hi (chain_blo CC Bh 0 hi)
  | succ j ih =>
    intro hi
    have la := CC.par.loop_a j hi
    refine node_hi_loc (CC.par.wf _ hi) (Bh.box _ hi) (Bh.ctl _ hi) (CC.conj _ hi).H_RACE_UP
      (Bh.r_lo _ hi) (fun x h1 h2 => ?_) (chain_blo CC Bh _ hi)
    rw [Bh.wa j hi]
    rw [la.2.1] at h1; rw [la.2.2.1] at h2
    exact ih (by omega) x h1 h2

/-- **Low phase**, by induction over the stage index. -/
theorem chain_lo (CC : ChainCell N P) (Bh : ChainBeh N P v rd r A B D C Q) :
    ∀ i < N, ∀ t, (P i).V1 ≤ t → C i t = .f := by
  have bhi : ∀ i < N, ∀ x, (P i).Rb1 ≤ x → x < (P i).Fb → B i x = .t := by
    intro i hi x h1 h2
    by_cases e : i + 1 < N
    · rw [Bh.wb i e]
      have lb := CC.par.loop_b i e
      rw [lb.2.1] at h1; rw [lb.2.2.1] at h2
      exact chain_hi CC Bh (i + 1) e x h1 h2
    · have hi' : i = N - 1 := by omega
      subst hi'
      exact Bh.snk_hi _ h1 h2
  intro i
  induction i with
  | zero =>
    intro hi
    exact node_lo_loc (CC.par.wf 0 hi) (Bh.box 0 hi) (Bh.ctl 0 hi) (CC.conj 0 hi).H_RACE_DN
      Bh.src_lo (bhi 0 hi)
  | succ j ih =>
    intro hi
    have la := CC.par.loop_a j hi
    refine node_lo_loc (CC.par.wf _ hi) (Bh.box _ hi) (Bh.ctl _ hi) (CC.conj _ hi).H_RACE_DN
      (fun x h1 => ?_) (bhi _ hi)
    rw [Bh.wa j hi]
    rw [la.2.2.2] at h1
    exact ih (by omega) x h1

/-- **Every stage meets LinkExact's spec in the closed loop.** -/
theorem chain_spec (CC : ChainCell N P) (Bh : ChainBeh N P v rd r A B D C Q) :
    ∀ i < N, Spec (P i) v (rd i).pd (rd i).pe (C i) (Q i) := by
  have sp : ∀ i (hi : i < N), DStab v (P i).Td (P i).Tn (D i) →
      Spec (P i) v (rd i).pd (rd i).pe (C i) (Q i) := fun i hi hd =>
    spec_loc (CC.par.wf i hi) (CC.conj i hi) (Bh.box i hi) (Bh.lat i hi) hd
      (fun t h1 h2 => chain_rst CC Bh t i hi h1 h2) (chain_hi CC Bh i hi) (chain_lo CC Bh i hi)
  intro i
  induction i with
  | zero => intro hi; exact sp 0 hi Bh.dat
  | succ j ih =>
    intro hi
    apply sp _ hi
    have Sj := ih (by omega)
    have dl := CC.H_DATA_LOOP j hi
    have bx := Bh.box j (by omega)
    have := bx.e; have := bx.d
    intro x h1 _
    rw [Bh.wd j hi]
    exact Sj.out x (by omega) (by omega)

/-! ## 2. The refinement -/

/-- **The physical chain refines the abstract run** (`kS`'s retiming): one global monotone
retiming, monotone per stage; every node, every internal wire (as the neighbour sees it) and
both end wires a window image; every latch captures the token and outputs it. -/
structure NetRef (N : Nat) (P : Nat → Par) (v : Bool) (rd : Nat → Rds) (A B C Q : Nat → Int → K3) :
    Prop where
  mono : MonoF (NE.ok N) (nev N P)
  stage : ∀ i < N, Mono (stageEvs N P i)
  node : ∀ i < N, WinImg (C i) .f .t (P i).Rhi ⟨(P i).U0, (P i).U1⟩ ⟨(P i).V0, (P i).V1⟩
  req_in : ∀ i < N, WinImg (A i) .f .t (P (i - 1)).Rhi
    ⟨(P i).Ra, (P i).Ra1⟩ ⟨(P i).Fa, (P i).Fa1⟩
  ack_out : ∀ i < N, WinImg (B i) .f .t (if i + 1 = N then (P i).Rhi else (P (i + 1)).Rhi)
    ⟨(P i).Rb, (P i).Rb1⟩ ⟨(P i).Fb, (P i).Fb1⟩
  capt : ∀ i < N, Capt v (P i).V0 (rd i).pe (Q i)
  out : ∀ i < N, ∀ t, (P i).U1 + (rd i).pe.hi ≤ t → (P i).Td + (rd i).pd.hi ≤ t → Q i t = kb v

theorem node_img {P : Par} {v : Bool} {pd pe : Rd} {c q : Int → K3} (Sp : Spec P v pd pe c q) :
    WinImg c .f .t P.Rhi ⟨P.U0, P.U1⟩ ⟨P.V0, P.V1⟩ :=
  ⟨Sp.nonempty, Sp.rst, Sp.hi, Sp.lo⟩

theorem chain_ref (CC : ChainCell N P) (Bh : ChainBeh N P v rd r A B D C Q) :
    NetRef N P v rd A B C Q := by
  have Sp := chain_spec CC Bh
  have pos := CC.par.pos
  refine ⟨net_mono CC.par, stage_mono CC.par, fun i hi => node_img (Sp i hi), fun i hi => ?_,
    fun i hi => ?_, fun i hi => (Sp i hi).capt, fun i hi => (Sp i hi).out⟩
  · rcases i with _ | j
    · have W := CC.par.wf 0 hi; have := W.ha; have := (CC.conj 0 hi).H_RACE_UP
      have := W.hA; have := W.hB
      simp only [Par.U1, Par.Rel] at *
      exact ⟨(pulses_ne W (CC.conj 0 hi)).1, fun x _ h => Bh.src_lo0 x h, fun x h1 h2 => Bh.src_hi x h1 h2,
        fun x h => Bh.src_lo x h⟩
    · have la := CC.par.loop_a j hi
      have I := node_img (Sp j (by omega))
      simp only [Nat.add_sub_cancel]
      rw [Bh.wa j hi, la.1, la.2.1, la.2.2.1, la.2.2.2]
      exact I
  · by_cases e : i + 1 < N
    · have lb := CC.par.loop_b i e
      have I := node_img (Sp (i + 1) e)
      rw [if_neg (by omega), Bh.wb i e, lb.1, lb.2.1, lb.2.2.1, lb.2.2.2]
      exact I
    · have hi' : i = N - 1 := by omega
      rw [if_pos (by omega)]
      subst hi'
      have W := CC.par.wf (N - 1) hi; have := W.hb; have := (CC.conj (N - 1) hi).H_RACE_DN
      have := W.hA; have := W.hB
      simp only [Par.V1] at *
      exact ⟨(pulses_ne W (CC.conj (N - 1) hi)).2, fun x _ h => Bh.snk_lo0 x h, fun x h1 h2 => Bh.snk_hi x h1 h2,
        fun x h => Bh.snk_lo x h⟩

open Formal.Net.Ops.Link (Link) in
open Formal.Net.Handshake (Protocol) in
open Formal.Net.Ops (Held) in
/-- **Headline (goal 2, link chain).** Every physical behaviour of a closed-loop `N`-stage
`bd_link` chain (`ChainCell`: closed loop with nonnegative reads, H_SRC/H_SNK, the six cell
rows per stage, H_WIRE_POS, H_RST_SEEN, H_DATA_LOOP) refines ONE zero-delay run of C's chain
network: C's `Link` at every stage on the shared channels, `Protocol` and `Held` on every
channel `0..N`, abstract latches holding the token value from their opening, and the physical
`NetRef` (one global monotone retiming, monotone on every stage, every node and wire a window
image, every latch capturing `v`). Bzd's `Causal` holds at every stage (derived, not assumed). -/
theorem chain_refines (CC : ChainCell N P) (Bh : ChainBeh N P v rd r A B D C Q) (u : Nat → Nat) :
    (∀ i < N, Link (chA (kS N P) N (vN v) u i) (chA (kS N P) N (vN v) u (i + 1)) (ndA (kS N P) i)) ∧
    (∀ j ≤ N, Protocol (chA (kS N P) N (vN v) u j)) ∧
    (∀ j ≤ N, Held (chA (kS N P) N (vN v) u j)) ∧
    (∀ i n, (kS N P).cu i < n → (chA (kS N P) N (vN v) u (i + 1)).dat n = vN v) ∧
    (∀ i < N, Causal (P i)) ∧ NetRef N P v rd A B C Q := by
  obtain ⟨h1, h2, h3, h4, -, -, h7⟩ := chain_abstract CC.par (vN v) u
  exact ⟨h1, h2, h3, h4, h7, chain_ref CC Bh⟩

end chain

end Formal.Cells.ZeroDelayNet
