import Formal.Timing.SpecSettle

/-!
# Symbolic settle windows: a combinational cone holds its zero-delay values (shard C, piece 2 of notes/C-allpairs.md)

**Problem, plainly.** `SpecSettle.cert_sound` certifies stability windows with CONCRETE values, so it speaks about one
operand pair. For every pair we need: if a datapath unit's inputs hold (any values) on their windows, then every gate
of the unit holds a constant on its window, and at any time inside all windows the gate outputs satisfy the
zero-delay gate equations of their inputs at that time. With that, `Net.Compute.OnDecoded.Settled` holds of the
snapshot `fun w => x w t`, and a unit theorem such as `uselect1_ps` gives the unit's output word as its MLIR operation
of the input words at time `t`.

**Proved.**
* `gateRuleS`/`certOKS`: the window rule of `SpecSettle.gateRule` without values (an STA pass in topological order);
* `certS_sound`: in every behaviour (GateOK at one corner), if the `known` nodes are constant on their windows,
  every gate output of the list is constant on its window and, while all its inputs are inside their windows, equals
  its INIT bit at the address of its inputs' current values;
* `certS_sound_net`: the same for gates of a well-formed netlist under `Behaves`;
* `certN_sound_net`: for every sane `p`, from a value-free certificate in prjxray slow-max units (`certOKN`,
  decidable): windows `[T0 + ⌈(1+κ)g⌉·SN n, T1]`.

**Not shown here.** Which windows a design needs; feedback (an input must be external or earlier in the list).
-/

namespace Formal.Timing.SpecSettle
open Formal.Target

/-- Node `n` holds one value on `[S n, U n]`. -/
def ConstW (S U : Nat → Nat) (x : Beh) (n : Nat) : Prop :=
  ∀ t, S n ≤ t → t ≤ U n → x n t = x n (S n)

/-- The window rule of one gate, without values. -/
def gateRuleS (p : DelayPar) (S U : Nat → Nat) (g : Gate) : Bool :=
  decide (g.start p ≤ S g.out) &&
  (List.range g.k).all (fun i =>
    decide (S (pinOf g i) + dmax p (arcOf g i) ≤ S g.out) &&
    decide (U g.out ≤ U (pinOf g i) + dmin p (arcOf g i)))

def certOKS (p : DelayPar) (S U : Nat → Nat) : List Nat → List Gate → Bool
  | _, [] => true
  | known, g :: gs =>
    (List.range g.k).all (fun i => known.contains (pinOf g i)) && gateRuleS p S U g &&
      certOKS p S U (g.out :: known) gs

/-- What a certified gate satisfies: constant on its window, and the gate equation at every time inside its own and
its inputs' windows. -/
def GateSettled (S U : Nat → Nat) (x : Beh) (g : Gate) : Prop :=
  ConstW S U x g.out ∧
  ∀ t, S g.out ≤ t → t ≤ U g.out → (∀ i, i < g.k → S (pinOf g i) ≤ t ∧ t ≤ U (pinOf g i)) →
    x g.out t = g.init.testBit (addr g.k (fun i => x (pinOf g i) t))

theorem gateRuleS_sound {p : DelayPar} {c : ℚ} {S U : Nat → Nat} {g : Gate} {x : Beh}
    (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hw : ArcsOK g) (hg : GateOK p c g x) (hr : gateRuleS p S U g = true)
    (hin : ∀ i, i < g.k → ConstW S U x (pinOf g i)) : GateSettled S U x g := by
  simp only [gateRuleS, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hr
  obtain ⟨hst, hpins⟩ := hr
  -- the value the output holds: the INIT bit at the inputs' held values
  have key : ∀ t, S g.out ≤ t → t ≤ U g.out →
      x g.out t = g.init.testBit (addr g.k (fun i => x (pinOf g i) (S (pinOf g i)))) := by
    intro t h1 h2
    apply gate_stable hp hc0 hc1 hw hg (fun i => S (pinOf g i)) (fun i => U (pinOf g i))
      (fun i => x (pinOf g i) (S (pinOf g i))) (fun i hi t' a b => hin i hi t' a b) t (by omega)
    intro i hi
    have := hpins i hi
    exact ⟨by omega, by omega⟩
  refine ⟨fun t h1 h2 => ?_, fun t h1 h2 hins => ?_⟩
  · have hle : S g.out ≤ U g.out := by omega
    rw [key t h1 h2, key (S g.out) (Nat.le_refl _) hle]
  · rw [key t h1 h2]
    congr 1
    apply addr_congr
    intro i hi
    exact (hin i hi t (hins i hi).1 (hins i hi).2).symm

theorem certS_sound {p : DelayPar} {c : ℚ} {S U : Nat → Nat} {x : Beh} (hp : Sane p) (hc0 : 0 ≤ c) (hc1 : c ≤ 1) :
    ∀ (known : List Nat) (gs : List Gate), (∀ g ∈ gs, ArcsOK g) →
      (∀ n ∈ known, ConstW S U x n) → (∀ g ∈ gs, GateOK p c g x) → certOKS p S U known gs = true →
      ∀ g ∈ gs, GateSettled S U x g
  | _, [], _, _, _, _ => fun g hg => absurd hg List.not_mem_nil
  | known, g :: gs, hws, hk, hgs, hc => by
    simp only [certOKS, Bool.and_eq_true, List.all_eq_true, List.mem_range,
      List.contains_iff_mem] at hc
    obtain ⟨⟨hpin, hr⟩, hrest⟩ := hc
    have hout : GateSettled S U x g :=
      gateRuleS_sound hp hc0 hc1 (hws g List.mem_cons_self) (hgs g List.mem_cons_self) hr
        (fun i hi => hk _ (hpin i hi))
    intro g' hg'
    rcases List.mem_cons.mp hg' with e | e
    · subst e; exact hout
    · exact certS_sound hp hc0 hc1 (g.out :: known) gs (fun g'' h'' => hws g'' (List.mem_cons_of_mem _ h''))
        (fun n hn => by
          rcases List.mem_cons.mp hn with e' | e'
          · subst e'; exact hout.1
          · exact hk n e')
        (fun g'' h'' => hgs g'' (List.mem_cons_of_mem _ h'')) hrest g' e

/-- **On a netlist.** -/
theorem certS_sound_net {p : DelayPar} {N : Net} {x : Beh} (hp : Sane p) (hN : N.WF) (hb : Behaves p N x)
    {S U : Nat → Nat} (known : List Nat) (gs : List Gate) (hsub : ∀ g ∈ gs, g ∈ N.gates)
    (hk : ∀ n ∈ known, ConstW S U x n) (hc : certOKS p S U known gs = true) :
    ∀ g ∈ gs, GateSettled S U x g := by
  obtain ⟨c, hc0, hc1, hall⟩ := hb
  exact certS_sound hp hc0 hc1 known gs (fun g hg => arcsOK_of_wf hN (hsub g hg)) hk
    (fun g hg => hall g (hsub g hg)) hc

/-! ## Every guard and scatter: windows from prjxray slow-max sums -/

/-- The scale of every upper delay bound: `⌈(1+κ)·g⌉`. -/
def cScale (p : DelayPar) : Nat := (⌈(1 + p.κ) * p.g⌉).toNat

theorem dmax_le_scale {p : DelayPar} (hp : Sane p) (e : Arc) : dmax p e ≤ cScale p * e.smax := by
  obtain ⟨hk0, hk1, hg⟩ := hp
  unfold dmax cScale
  have h1 : (1 + p.κ) * (e.smax : ℚ) * p.g ≤ ((⌈(1 + p.κ) * p.g⌉ : ℤ) : ℚ) * e.smax := by
    have := Int.le_ceil ((1 + p.κ) * p.g)
    have hs : (0 : ℚ) ≤ e.smax := by positivity
    nlinarith
  have h2 : ⌈(1 + p.κ) * (e.smax : ℚ) * p.g⌉ ≤ ⌈(1 + p.κ) * p.g⌉ * (e.smax : ℤ) := by
    apply Int.ceil_le.mpr; push_cast; exact h1
  have h3 : 0 ≤ ⌈(1 + p.κ) * p.g⌉ := Int.ceil_nonneg (by positivity)
  rw [Int.toNat_le]; push_cast; rw [Int.toNat_of_nonneg h3]; exact h2

/-- A gate's start bound in slow-max units. -/
def startSN (g : Gate) : Nat := (g.arcs.map fun e => e.smax).foldr max 0

theorem start_le_scale {p : DelayPar} (hp : Sane p) (g : Gate) : g.start p ≤ cScale p * startSN g := by
  unfold Gate.start startSN
  induction g.arcs with
  | nil => simp
  | cons e es ih =>
    simp only [List.map_cons, List.foldr_cons]
    have h1 : (Rat.ceil ((1 + p.κ) * e.smax * p.g)).toNat ≤ cScale p * e.smax := by
      have : Rat.ceil ((1 + p.κ) * e.smax * p.g) = ⌈(1 + p.κ) * (e.smax : ℚ) * p.g⌉ := by
        rw [Rat.ceil_eq_neg_floor_neg]; rfl
      rw [this]; exact dmax_le_scale hp e
    rw [← Nat.mul_max_mul_left]
    exact max_le_max h1 ih

/-- The window rule in slow-max units (no `p`): decidable on a netlist. -/
def gateRuleN (SN : Nat → Nat) (g : Gate) : Bool :=
  decide (startSN g ≤ SN g.out) &&
  (List.range g.k).all (fun i => decide (SN (pinOf g i) + (arcOf g i).smax ≤ SN g.out))

def certOKN (SN : Nat → Nat) : List Nat → List Gate → Bool
  | _, [] => true
  | known, g :: gs =>
    (List.range g.k).all (fun i => known.contains (pinOf g i)) && gateRuleN SN g && certOKN SN (g.out :: known) gs

theorem certOKS_of_N {p : DelayPar} (hp : Sane p) (SN : Nat → Nat) (T0 T1 : Nat) :
    ∀ known gs, certOKN SN known gs = true →
      certOKS p (fun n => T0 + cScale p * SN n) (fun _ => T1) known gs = true
  | _, [], _ => rfl
  | known, g :: gs, h => by
    simp only [certOKN, Bool.and_eq_true] at h
    obtain ⟨⟨hpin, hr⟩, hrest⟩ := h
    simp only [certOKS, Bool.and_eq_true]
    refine ⟨⟨hpin, ?_⟩, certOKS_of_N hp SN T0 T1 _ gs hrest⟩
    simp only [gateRuleN, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range] at hr
    simp only [gateRuleS, Bool.and_eq_true, decide_eq_true_eq, List.all_eq_true, List.mem_range]
    refine ⟨?_, fun i hi => ⟨?_, by omega⟩⟩
    · have := start_le_scale hp g
      have := Nat.mul_le_mul_left (cScale p) hr.1
      omega
    · have h1 := dmax_le_scale hp (arcOf g i)
      have h2 := Nat.mul_le_mul_left (cScale p) (hr.2 i hi)
      rw [Nat.mul_add] at h2
      omega

/-- **Every `(g, κ)`.** If the `known` nodes hold on `[T0 + C·SN n, T1]` (`C = ⌈(1+κ)g⌉`) and a slow-max certificate
`certOKN SN` passes, every gate of the list holds on `[T0 + C·SN out, T1]` and satisfies its gate equation at every
time inside its own and its inputs' windows. -/
theorem certN_sound_net {p : DelayPar} {N : Net} {x : Beh} (hp : Sane p) (hN : N.WF) (hb : Behaves p N x)
    (SN : Nat → Nat) (T0 T1 : Nat) (known : List Nat) (gs : List Gate) (hsub : ∀ g ∈ gs, g ∈ N.gates)
    (hk : ∀ n ∈ known, ConstW (fun n => T0 + cScale p * SN n) (fun _ => T1) x n) (hc : certOKN SN known gs = true) :
    ∀ g ∈ gs, GateSettled (fun n => T0 + cScale p * SN n) (fun _ => T1) x g :=
  certS_sound_net hp hN hb known gs hsub hk (certOKS_of_N hp SN T0 T1 known gs hc)

end Formal.Timing.SpecSettle
