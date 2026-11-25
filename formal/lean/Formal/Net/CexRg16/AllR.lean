import Formal.Net.CexRg16.Refute
import Formal.Net.Stretch
import Formal.Net.StretchPS.Smax
import Formal.Target.SpecMono

/-!
# The g = 8/5, κ = 0 refutation holds for every reset length R ≥ 400 ns (shard C, 2026-11-07)

**Problem, plainly.** `not_netCorrectSeqRunt20` refutes THE headline statement for a reset of exactly 400 ns. THE
statement takes the reset length `R` as a parameter, and positive results need long resets (`correct_n0_all`:
`R ≥ ⌈(1+κ)g⌉·(A1 + 87·M1) + 1`, about 706 ns here). Is the statement false for every longer reset too?

**Proved.** `not_netCorrectSeqRunt20_R`: for every `D`, `T ≥ 137`, `su`, `Δo ≤ 3000`,
`¬ NetCorrectSeqRunt 20 net boundary arbs ⟨8/5, 0⟩ T (400000 + D) su Δo`, and `not_netCorrectSeq_R`, the same for
the plain statement. The witness is the run `xR` with its quiet stretch [2000, 399999] ps lengthened by `D`
(`Net/Stretch`): every node of `xR` is constant there (`quiet_xR`, kernel-checked on the node codes), every arc of the
target is at most 698 ps (`StretchPS.smax_all`), so every gate's start is at most 1117 ps; the environment
(`y_hyps`, shard C's proof re-done for a schedule shifted by `D`) and H_ARB (`Stretch.arbOK_stretch`) carry over.

**What it does NOT say.** Nothing about resets shorter than 400 ns, other (g, κ), other corners.
-/

namespace Formal.Net.CexRg16
open Formal.Target Formal.Target.DecodedPS Formal.Net.CViewPS Formal.Net.Stretch Formal.Net.StretchPS

/-! ## The node codes are quiet on [2000, 399999] -/

def BTL.allL (P : Option (Bool × List Nat) → Bool) : BTL → Bool
  | .lf v => P v
  | .nd l r => BTL.allL P l && BTL.allL P r

theorem BTL.get_allL (P : Option (Bool × List Nat) → Bool) (hn : P none = true) :
    ∀ (t : BTL) (d i : Nat), t.allL P = true → P (t.get d i) = true
  | .lf v, _, _, h => by simpa [BTL.allL, BTL.get] using h
  | .nd _ _, 0, _, _ => by simpa [BTL.get] using hn
  | .nd l r, d + 1, i, h => by
    simp only [BTL.allL, Bool.and_eq_true] at h
    simp only [BTL.get]
    split
    · exact BTL.get_allL P hn l d _ h.1
    · exact BTL.get_allL P hn r d _ h.2

def qP (e : Option (Bool × List Nat)) : Bool := (thrL e).all fun θ => decide (θ ≤ 2000) || decide (399999 < θ)

theorem q000 : l000.allL qP = true := by decide +kernel
theorem q001 : l001.allL qP = true := by decide +kernel
theorem q002 : l002.allL qP = true := by decide +kernel
theorem q003 : l003.allL qP = true := by decide +kernel
theorem q004 : l004.allL qP = true := by decide +kernel
theorem q005 : l005.allL qP = true := by decide +kernel
theorem q006 : l006.allL qP = true := by decide +kernel
theorem q007 : l007.allL qP = true := by decide +kernel
theorem q008 : l008.allL qP = true := by decide +kernel
theorem q009 : l009.allL qP = true := by decide +kernel
theorem q010 : l010.allL qP = true := by decide +kernel
theorem q011 : l011.allL qP = true := by decide +kernel
theorem q012 : l012.allL qP = true := by decide +kernel
theorem q013 : l013.allL qP = true := by decide +kernel
theorem q014 : l014.allL qP = true := by decide +kernel
theorem q015 : l015.allL qP = true := by decide +kernel
theorem q016 : l016.allL qP = true := by decide +kernel
theorem q017 : l017.allL qP = true := by decide +kernel
theorem q018 : l018.allL qP = true := by decide +kernel
theorem q019 : l019.allL qP = true := by decide +kernel
theorem q020 : l020.allL qP = true := by decide +kernel
theorem q021 : l021.allL qP = true := by decide +kernel
theorem q022 : l022.allL qP = true := by decide +kernel
theorem q023 : l023.allL qP = true := by decide +kernel
theorem q024 : l024.allL qP = true := by decide +kernel
theorem q025 : l025.allL qP = true := by decide +kernel
theorem q026 : l026.allL qP = true := by decide +kernel
theorem q027 : l027.allL qP = true := by decide +kernel
theorem q028 : l028.allL qP = true := by decide +kernel
theorem q029 : l029.allL qP = true := by decide +kernel
theorem q030 : l030.allL qP = true := by decide +kernel
theorem q031 : l031.allL qP = true := by decide +kernel
theorem q032 : l032.allL qP = true := by decide +kernel
theorem q033 : l033.allL qP = true := by decide +kernel
theorem q034 : l034.allL qP = true := by decide +kernel
theorem q035 : l035.allL qP = true := by decide +kernel
theorem q036 : l036.allL qP = true := by decide +kernel
theorem q037 : l037.allL qP = true := by decide +kernel
theorem q038 : l038.allL qP = true := by decide +kernel
theorem q039 : l039.allL qP = true := by decide +kernel
theorem q040 : l040.allL qP = true := by decide +kernel
theorem q041 : l041.allL qP = true := by decide +kernel
theorem q042 : l042.allL qP = true := by decide +kernel
theorem q043 : l043.allL qP = true := by decide +kernel
theorem q044 : l044.allL qP = true := by decide +kernel
theorem q045 : l045.allL qP = true := by decide +kernel
theorem q046 : l046.allL qP = true := by decide +kernel
theorem q047 : l047.allL qP = true := by decide +kernel
theorem q048 : l048.allL qP = true := by decide +kernel
theorem q049 : l049.allL qP = true := by decide +kernel
theorem q050 : l050.allL qP = true := by decide +kernel
theorem q051 : l051.allL qP = true := by decide +kernel
theorem q052 : l052.allL qP = true := by decide +kernel
theorem q053 : l053.allL qP = true := by decide +kernel
theorem q054 : l054.allL qP = true := by decide +kernel
theorem q055 : l055.allL qP = true := by decide +kernel
theorem q056 : l056.allL qP = true := by decide +kernel
theorem q057 : l057.allL qP = true := by decide +kernel
theorem q058 : l058.allL qP = true := by decide +kernel
theorem q059 : l059.allL qP = true := by decide +kernel
theorem q060 : l060.allL qP = true := by decide +kernel
theorem q061 : l061.allL qP = true := by decide +kernel
theorem q062 : l062.allL qP = true := by decide +kernel
theorem q063 : l063.allL qP = true := by decide +kernel
theorem q064 : l064.allL qP = true := by decide +kernel
theorem q065 : l065.allL qP = true := by decide +kernel
theorem q066 : l066.allL qP = true := by decide +kernel
theorem q067 : l067.allL qP = true := by decide +kernel
theorem q068 : l068.allL qP = true := by decide +kernel
theorem q069 : l069.allL qP = true := by decide +kernel
theorem q070 : l070.allL qP = true := by decide +kernel
theorem q071 : l071.allL qP = true := by decide +kernel
theorem q072 : l072.allL qP = true := by decide +kernel
theorem q073 : l073.allL qP = true := by decide +kernel
theorem q074 : l074.allL qP = true := by decide +kernel

theorem q_all : (llR.all fun t => t.allL qP) = true := by
  simp only [llR, List.all_cons, List.all_nil, q000, q001, q002, q003, q004, q005, q006, q007, q008, q009, q010, q011, q012, q013, q014, q015, q016, q017, q018, q019, q020, q021, q022, q023, q024, q025, q026, q027, q028, q029, q030, q031, q032, q033, q034, q035, q036, q037, q038, q039, q040, q041, q042, q043, q044, q045, q046, q047, q048, q049, q050, q051, q052, q053, q054, q055, q056, q057, q058, q059, q060, q061, q062, q063, q064, q065, q066, q067, q068, q069, q070, q071, q072, q073, q074, Bool.and_self]

theorem qP_encR (n : Nat) : qP (encR n) = true := by
  unfold encR lookL
  apply BTL.get_allL qP rfl
  rw [List.getD_eq_getElem?_getD]
  cases h : llR[n / 2500]? with
  | none => rfl
  | some t => exact List.all_eq_true.mp q_all t (List.mem_of_getElem? h)

theorem quiet_xR : Quiet xR 2000 399999 := by
  intro n t h1 h2
  apply sigL_eq
  intro θ hθ
  have := List.all_eq_true.mp (qP_encR n) θ hθ
  simp only [Bool.or_eq_true, decide_eq_true_eq] at this
  omega

/-! ## The stretched run's boundary signals -/

theorem stretch_pulse {n p q : Nat} (h : encR n = some (false, [p, q])) (hp : 399999 < p) (hpq : p < q) (D : Nat) :
    stretch xR 399999 D n = pls (p + D) (q + D) := by
  funext t
  show xR n (σ 399999 D t) = _
  rw [r_sig h hpq]
  unfold pls σ
  by_cases h1 : t ≤ 399999
  · rw [if_pos h1]
    have a1 : ¬ p ≤ t := by omega
    have a2 : ¬ p + D ≤ t := by omega
    simp [a1, a2]
  · rw [if_neg h1]
    by_cases h2 : t ≤ 399999 + D
    · rw [if_pos h2]
      have a1 : ¬ p ≤ 399999 := by omega
      have a2 : ¬ p + D ≤ t := by omega
      simp [a1, a2]
    · rw [if_neg h2]
      have e1 : (p ≤ t - D) = (p + D ≤ t) := by apply propext; omega
      have e2 : (q ≤ t - D) = (q + D ≤ t) := by apply propext; omega
      simp only [e1, e2]

theorem stretch_none {n : Nat} (h : encR n = none) (D : Nat) : stretch xR 399999 D n = fun _ => false := by
  funext t; show xR n _ = _; rw [r_none h]

theorem stretch_rst (D : Nat) (t : Nat) : stretch xR 399999 D 186905 t = !decide (400000 + D ≤ t) := by
  show xR 186905 (σ 399999 D t) = _
  simp only [xR, r_codes.1]; rw [step_val]
  simp only [σ]
  split_ifs <;> simp <;> omega

theorem stretch_busVal (d : List Nat) (D t : Nat) : busVal (stretch xR 399999 D) d t = busVal xR d (σ 399999 D t) := rfl

/-! ## The environment, for a schedule shifted by `D` -/

theorem y_hyps (D : Nat) (y : Beh) (hrst : ∀ t, y 186905 t = !decide (400000 + D ≤ t))
    (hreq : y 186985 = pls (401000 + D) (461903 + D)) (haA : y 104576 = pls (423300 + D) (470887 + D))
    (haB : y 104695 = pls (423571 + D) (471172 + D)) (haS : y 147972 = pls (461902 + D) (484862 + D))
    (hpe : y 104477 = pls (404000 + D) (464903 + D)) (h6 : y 160957 = fun _ => false) (h7 : y 154859 = fun _ => false)
    (hda : ∀ t, busVal y boundary.a.data t = 1071) (hdb : ∀ t, busVal y boundary.b.data t = 462)
    (su Δo : Nat) (hΔ : Δo ≤ 3000) :
    Env y boundary (400000 + D) su Δo (some 1) (fun _ => 1071) (fun _ => 462) ∧ SeqEnv y boundary (400000 + D) := by
  obtain ⟨b1, b2, b3, b4, b5, b6, b7, b8, b9, b10, b11⟩ := bnd_facts
  have rq := hreq
  have rs : ∀ t, rises (y 186985) (400000 + D) t = if (401000 + D) ≤ t then 1 else 0 :=
    rises_pulse _ (400000 + D) (401000 + D) (461903 + D) (by omega) (by omega) (fun t => by rw [rq]; rfl)
  have ein : ∀ (ch : InCh) (vals : Nat → Nat) (p q : Nat), ch.req = 186985 → (401000 + D) < p → p ≤ (461902 + D) →
      (461903 + D) < q → y ch.ack = pls p q → (∀ t, busVal y ch.data t = vals 0) →
      EnvIn y ch (400000 + D) su (some 1) vals := by
    intro ch vals p q hq hp1 hp2 hq2 hack hdat
    have r1 : ∀ t, rises (y ch.req) (400000 + D) t - 1 = 0 := fun t => by rw [hq, rs]; split <;> rfl
    refine ⟨fun t ht => ?_, fun t ht hne => ?_, fun t ht he hc => ?_, fun t ht hr => ?_,
      fun t ht _ _ s _ _ => by rw [r1]; exact hdat s, fun t ht _ _ => by rw [r1]; exact hdat t⟩
    · rw [hq, rq, pls_false]; omega
    · rw [hq, rq] at hne ⊢; rw [hack]
      rcases pls_change hne with h | h
      · have e1 : pls (401000 + D) (461903 + D) t = false := pls_false.mpr (by omega)
        have e2 : pls p q t = false := pls_false.mpr (by omega)
        rw [e1, e2]
      · have e1 : pls (401000 + D) (461903 + D) t = true := pls_true.mpr (by omega)
        have e2 : pls p q t = true := pls_true.mpr (by omega)
        rw [e1, e2]
    · rw [hq, rq, hack] at he; rw [hq, rs, rq] at hc; rw [hq]
      by_cases h1 : t < (401000 + D)
      · exact ⟨(401000 + D), by omega, by rw [rq, hack, (pls_true.mpr (by omega) : pls (401000 + D) (461903 + D) (401000 + D) = true),
          (pls_false.mpr (by omega) : pls p q (401000 + D) = false)]; simp⟩
      · by_cases h2 : t < (461903 + D)
        · exact ⟨(461903 + D), by omega, by rw [rq, hack, (pls_false.mpr (by omega) : pls (401000 + D) (461903 + D) (461903 + D) = false),
            (pls_true.mpr (by omega) : pls p q (461903 + D) = true)]; simp⟩
        · exfalso
          have e1 : pls (401000 + D) (461903 + D) t = false := pls_false.mpr (by omega)
          rw [e1] at hc
          simp only [Bool.false_eq_true, false_or, Offered] at hc
          have : (if (401000 + D) ≤ t then 1 else 0) = 1 := by simp; omega
          rw [this] at hc; omega
    · rw [hq, rs]; rw [hq, rq, pls_true] at hr
      simp only [Offered]; split <;> omega
  refine ⟨⟨fun t ht => ?_, fun t ht => ?_, fun k hk => ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_⟩
  · rw [b1, hrst]; simp; omega
  · rw [b1, hrst]; simp; omega
  · simp only [Offered] at hk; have : k = 0 := by omega
    subst this; decide
  · exact ein _ _ (423300 + D) (470887 + D) b2 (by omega) (by omega) (by omega) (by rw [b5]; exact haA)
      hda
  · exact ein _ _ (423571 + D) (471172 + D) b3 (by omega) (by omega) (by omega) (by rw [b6]; exact haB)
      hdb
  · exact ein _ _ (461902 + D) (484862 + D) b4 (by omega) (by omega) (by omega) (by rw [b7]; exact haS)
      (fun t => by rw [show boundary.start.data = [] from rfl]; rfl)
  · -- out0: request and acknowledge never move
    rw [show boundary.out0 = ⟨160957, 154859, boundary.out0.data⟩ from rfl]
    refine ⟨fun t _ => ?_, fun t _ hne => ?_, fun t _ hne => ?_, fun t _ _ h5 _ _ _ => ?_⟩
    · simp only [h7]
    · simp only [h7] at hne; exact absurd rfl hne
    · simp only [h7, h6] at hne; exact absurd rfl hne
    · simp only [h7] at h5; exact absurd h5 (by simp)
  · -- pend: the shared request, acknowledged 3 ns after each of its moves
    rw [show boundary.pend = ⟨186985, 104477, boundary.pend.data⟩ from rfl]
    have ha := hpe
    refine ⟨fun t ht => ?_, fun t ht hne => ?_, fun t ht hne => ?_, fun t ht h4 h5 s hs1 hs2 => ?_⟩
    · show y 104477 t = false
      rw [ha, pls_false]; omega
    · show y 104477 t ≠ y 186985 t
      change y 104477 (t + 1) ≠ y 104477 t at hne
      rw [ha] at hne ⊢; rw [rq]
      rcases pls_change hne with h | h
      · rw [(pls_false.mpr (by omega) : pls (404000 + D) (464903 + D) t = false),
          (pls_true.mpr (by omega) : pls (401000 + D) (461903 + D) t = true)]; simp
      · rw [(pls_true.mpr (by omega) : pls (404000 + D) (464903 + D) t = true),
          (pls_false.mpr (by omega) : pls (401000 + D) (461903 + D) t = false)]; simp
    · change y 104477 t ≠ y 186985 t at hne
      rw [ha, rq] at hne
      by_cases e1 : (401000 + D) ≤ t ∧ t < (404000 + D)
      · exact ⟨(404000 + D), by omega, by
          show y 104477 (404000 + D) = y 186985 (404000 + D)
          rw [ha, rq, (pls_true.mpr (by omega) : pls (404000 + D) (464903 + D) (404000 + D) = true),
            (pls_true.mpr (by omega) : pls (401000 + D) (461903 + D) (404000 + D) = true)]⟩
      · by_cases e2 : (461903 + D) ≤ t ∧ t < (464903 + D)
        · exact ⟨(464903 + D), by omega, by
            show y 104477 (464903 + D) = y 186985 (464903 + D)
            rw [ha, rq, (pls_false.mpr (by omega) : pls (404000 + D) (464903 + D) (464903 + D) = false),
              (pls_false.mpr (by omega) : pls (401000 + D) (461903 + D) (464903 + D) = false)]⟩
        · exfalso; apply hne
          by_cases e3 : (404000 + D) ≤ t ∧ t < (461903 + D)
          · rw [(pls_true.mpr (by omega) : pls (404000 + D) (464903 + D) t = true), (pls_true.mpr (by omega) : pls (401000 + D) (461903 + D) t = true)]
          · rw [(pls_false.mpr (by omega) : pls (404000 + D) (464903 + D) t = false), (pls_false.mpr (by omega) : pls (401000 + D) (461903 + D) t = false)]
    · change y 104477 t = false at h4; change y 104477 (t + 1) = true at h5
      show y 186985 s = true
      rw [ha, pls_false] at h4; rw [ha, pls_true] at h5; rw [rq, pls_true]; omega
  · intro ch hch t ht h1 h2
    simp only [List.mem_cons, List.not_mem_nil, or_false] at hch
    have hq : ch.req = 186985 := by rcases hch with rfl | rfl | rfl <;> assumption
    rw [hq, rq, pls_false] at h1; rw [hq, rq, pls_true] at h2
    have : t = (400999 + D) := by omega
    subst this
    rw [hq, rs, b8, b9, h6, h7]
    refine ⟨by simp, rfl, rfl⟩


theorem y_not_correct (D : Nat) (y : Beh) (h6 : y 160957 = fun _ => false) (Δo : Nat) :
    ¬ Correct y boundary (400000 + D) Δo (some 1) (fun _ => 1071) (fun _ => 462) := by
  intro h
  obtain ⟨T, hT⟩ := h.2.2.2.2.2.2 1 rfl
  have h1 := (hT T (le_refl _)).2.1
  have hz : rises (y boundary.out0.req) (400000 + D) T = 0 :=
    rises_false _ _ (fun t => by rw [show boundary.out0.req = 160957 from rfl, h6]) T
  omega

/-! ## Assembly -/

theorem start_le_1117 : ∀ g ∈ (circuit net boundary).gates, 2000 + g.start pK ≤ 399999 := by
  intro g hg
  rw [circuit_gates, List.mem_filter] at hg
  have h := start_le_of_smax (p := pK) (by simp [pK]; norm_num) g (smax_all g hg.1)
  have hq : (1 + pK.κ) * ((698 : Nat) : ℚ) * pK.g ≤ 1117 := by simp [pK]; norm_num
  have h2 : Rat.ceil ((1 + pK.κ) * ((698 : Nat) : ℚ) * pK.g) ≤ 1117 := by
    rw [rat_ceil_eq]; exact Int.ceil_le.mpr (by exact_mod_cast hq)
  omega

/-- **THE headline statement is false at g = 8/5, κ = 0 for every reset of at least 400 ns.** -/
theorem not_netCorrectSeqRunt20_R (D T su Δo : Nat) (hT : 137 ≤ T) (hΔ : Δo ≤ 3000) :
    ¬ NetCorrectSeqRunt 20 net boundary arbs pK T (400000 + D) su Δo := by
  intro h
  set y := stretch xR 399999 D
  have hb : BehavesRunt 20 pK (circuit net boundary) y :=
    behavesRuntOn_stretch (circuit_wf net_wf) quiet_xR start_le_1117 (by norm_num) behavesRunt_r
  have ha : ArbOK T arbs y := arbOK_mono hT (arbOK_stretch quiet_xR (by norm_num) (r_arbOK 137 le_rfl))
  have c := r_codes
  obtain ⟨he, hs⟩ := y_hyps D y (stretch_rst D) (stretch_pulse c.2.1 (by norm_num) (by norm_num) D)
    (stretch_pulse c.2.2.1 (by norm_num) (by norm_num) D) (stretch_pulse c.2.2.2.1 (by norm_num) (by norm_num) D)
    (stretch_pulse c.2.2.2.2.1 (by norm_num) (by norm_num) D)
    (stretch_pulse c.2.2.2.2.2.2.2 (by norm_num) (by norm_num) D)
    (stretch_none c.2.2.2.2.2.1 D) (stretch_none c.2.2.2.2.2.2.1 D)
    (fun t => by rw [stretch_busVal, busVal_const _ r_data.1]; exact r_data.2.2.1)
    (fun t => by rw [stretch_busVal, busVal_const _ r_data.2.1]; exact r_data.2.2.2)
    su Δo hΔ
  exact y_not_correct D y (stretch_none c.2.2.2.2.2.1 D) Δo (h y (some 1) (fun _ => 1071) (fun _ => 462) hb ha he hs)

/-- The plain statement (no runt filtering) is false there too (`SpecRunt.seqRunt_of_seq`). -/
theorem not_netCorrectSeq_R (D T su Δo : Nat) (hT : 137 ≤ T) (hΔ : Δo ≤ 3000) :
    ¬ NetCorrectSeq net boundary arbs pK T (400000 + D) su Δo :=
  fun h => not_netCorrectSeqRunt20_R D T su Δo hT hΔ (seqRunt_of_seq lutGate 20 h)

end Formal.Net.CexRg16
