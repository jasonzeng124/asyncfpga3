import Formal.Core.Prims.SeqXray

/-!
# Formal.Core.Prims.SeqGls — the research GLS's flop reads X on CE/SR as 0 (trace counterexample)

Shard A, probe PrimsSeq. Core Lean only. Notes: `formal/notes/A-prims-seq.md`;
FOR-RESEARCH §7 ("SLICE_FFX hides X on SR and CE", formerly §8), `notes/A-forres.md`.

## The GLS model, as a relation

`origin/claude/research:cells/gls/prims.v` default `SLICE_FFX`:

```
initial Q = INIT;
always @(posedge CK) begin
  if (TSU > 0 && ... $time - t_in < TSU) Q <= 1'bx;   // setup violation message
  else if (SR) Q <= SRVAL; else if (CE) Q <= D;
end
always @(D or CE) if (THD > 0 && ... $time - t_ck < THD) Q <= 1'bx;  // hold violation
specify (posedge CK => (Q +: D)) = TCKQ; endspecify
```

`GlsRel` below is that code on **runs with no SETUP/HOLD VIOLATION message** (`GlsQuiet`:
D and CE do not move within TSU before or THD after an edge): at the posedge instant
`e + 1` it computes `glsNext` (`SeqNext`: an `X` condition takes the `else` branch) on the
point values, and Q shows it `TCKQ` later.

## The counterexample (`gls_vs_kleene_ce`, `gls_vs_kleene_sr`)

FDRE, INIT 0, R = 0, D = 1, CE = X (e.g. driven by a LUT with an X input), one clock edge
at 1000 ps. The GLS run has Q = 0 at every time, prints no violation, and is a run of
`GlsRel`. In the Kleene model (`FlopRel`, any well-formed timing with `cqLo < cqHi`, in
particular every prjxray corner) EVERY run has Q = X at `1000 + cqHi`, and the completion
CE = 1 has Q = 1 from then on (`capture`): the GLS's definite 0 is contradicted by a real
behaviour. The SR case: FDSE with SR = X, CE = 1, D = 0: GLS 0, Kleene X, completion SR = 1
gives 1.

What this does NOT show: that a design here drives X into a CE or SR pin (the gcd_hw rig's
flops have CE/SR from rig logic, see the census); only that a GLS pass cannot exclude it.
-/

namespace Formal.Core.Prims.Seq

open Formal.Core Formal.Core.K3 Formal.Core.Substrate

/-- `x` does not move on `[a, b]`. -/
def Quiet (x : KSig) (a b : Nat) : Prop := ∀ s, a ≤ s → s ≤ b → x s = x a

/-- No SETUP/HOLD VIOLATION message is printed. -/
def GlsQuiet (tsu thd : Nat) (ck : Sig) (ce d : KSig) : Prop :=
  ∀ e, rises ck e → Quiet d (e + 1 - tsu) (e + 1 + thd) ∧ Quiet ce (e + 1 - tsu) (e + 1 + thd)

/-- The default-GLS `SLICE_FFX` on violation-free runs. -/
structure GlsRel (tckq : Nat) (rv init : Bool) (ck : Sig) (r ce d q : KSig) : Prop where
  init : ∀ t, (∀ u, u < t → ¬ rises ck u) → q t = ofBool init
  edge : ∀ e t, rises ck e → e < t → NoRise ck e t →
    q t = if t < e + 1 + tckq then q e
          else glsNext rv (r (e + 1)) (ce (e + 1)) (d (e + 1)) (q e)

/-- The scenario: one rising edge at 1000. -/
def ck1000 : Sig := fun t => decide (1001 ≤ t)

theorem ck1000_rises (u : Nat) : rises ck1000 u ↔ u = 1000 := by
  unfold rises ck1000
  constructor
  · intro ⟨h1, h2⟩
    have a := of_decide_eq_false h1; have b := of_decide_eq_true h2; omega
  · intro h; subst h; exact ⟨by decide, by decide⟩

/-- The GLS run: Q = 0 throughout, for FDRE (CE = X, D = 1) and for FDSE (SR = X, CE = 1, D = 0). -/
theorem gls_run_ce (tckq tsu thd : Nat) :
    GlsRel tckq false false ck1000 (fun _ => zero) (fun _ => X) (fun _ => one) (fun _ => zero) ∧
      GlsQuiet tsu thd ck1000 (fun _ => X) (fun _ => one) := by
  refine ⟨⟨fun _ _ => rfl, fun e t _ _ _ => ?_⟩, fun _ _ => ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩⟩
  split <;> rfl

theorem gls_run_sr (tckq tsu thd : Nat) :
    GlsRel tckq true false ck1000 (fun _ => X) (fun _ => one) (fun _ => zero) (fun _ => zero) ∧
      GlsQuiet tsu thd ck1000 (fun _ => one) (fun _ => zero) := by
  refine ⟨⟨fun _ _ => rfl, fun e t _ _ _ => ?_⟩, fun _ _ => ⟨fun _ _ _ => rfl, fun _ _ _ => rfl⟩⟩
  split <;> rfl

theorem norise_after (t : Nat) : NoRise ck1000 1000 t := fun u h1 _ hr => by
  have := (ck1000_rises u).1 hr; omega

theorem norise_before (t : Nat) (ht : t ≤ 1000) : ∀ u, u < t → ¬ rises ck1000 u := fun u hu hr => by
  have := (ck1000_rises u).1 hr; omega

theorem rises1000 : rises ck1000 1000 := (ck1000_rises 1000).2 rfl

theorem const_eqOn (v : K3) (a b : Nat) : EqOn (fun _ => v) v a b := fun _ _ _ => rfl

/-- **Kleene model, CE = X**: every run has Q = X at `1000 + cqHi`. -/
theorem kleene_ce_X (T : FFTiming) (hok : T.Ok) (hb : T.cqLo < T.cqHi) {q : KSig}
    (h : FlopRel T false false false ck1000 (fun _ => zero) (fun _ => X) (fun _ => one) q) :
    q (1000 + T.cqHi) = X := by
  have hq0 : q 1000 = zero := h.init 1000 (norise_before 1000 (Nat.le_refl _)) (fun h => absurd h (by decide))
  rw [h.band 1000 _ rises1000 (by omega) (norise_after _) (guard_sync T _ _ _) (by omega) (Nat.le_refl _)]
  simp only [nextAt, ap, winVal_const (wpt_le hok.1) (const_eqOn one _ _),
    winVal_const (wpt_le hok.2.1) (const_eqOn X _ _),
    winVal_const (wpt_le hok.2.2.1) (const_eqOn zero _ _), hq0, knext, kmux]
  rfl

/-- The completion CE = 1 of the same inputs captures D = 1. -/
theorem kleene_ce_one (T : FFTiming) (hok : T.Ok) {q : KSig}
    (h : FlopRel T false false false ck1000 (fun _ => zero) (fun _ => one) (fun _ => one) q)
    (t : Nat) (ht : 1000 + T.cqHi < t) : q t = one :=
  capture T hok h rises1000 (by omega) (norise_after t) (guard_sync T _ _ _)
    (v := true) (const_eqOn one _ _) (const_eqOn one _ _) (const_eqOn zero _ _) ht

/-- **The counterexample (CE).** A violation-free GLS run with Q = 0 at `1000 + cqHi`, where
every Kleene run has X, and the Boolean completion CE = 1 has 1. Holds at every prjxray
corner (`regFF`). -/
theorem gls_vs_kleene_ce (T : FFTiming) (hok : T.Ok) (hb : T.cqLo < T.cqHi) (tckq tsu thd : Nat) :
    (∃ qg, GlsRel tckq false false ck1000 (fun _ => zero) (fun _ => X) (fun _ => one) qg ∧
        GlsQuiet tsu thd ck1000 (fun _ => X) (fun _ => one) ∧ qg (1000 + T.cqHi) = zero) ∧
      (∀ q, FlopRel T false false false ck1000 (fun _ => zero) (fun _ => X) (fun _ => one) q →
        q (1000 + T.cqHi) = X) ∧
      (∀ q, FlopRel T false false false ck1000 (fun _ => zero) (fun _ => one) (fun _ => one) q →
        q (1000 + T.cqHi + 1) = one) ∧
      X ⊑ one :=
  ⟨⟨_, (gls_run_ce tckq tsu thd).1, (gls_run_ce tckq tsu thd).2, rfl⟩,
    fun _ h => kleene_ce_X T hok hb h, fun _ h => kleene_ce_one T hok h _ (by omega), X_le _⟩

/-- **The counterexample (SR)**, FDSE: SR = X, CE = 1, D = 0, INIT 0. -/
theorem gls_vs_kleene_sr (T : FFTiming) (hok : T.Ok) (hb : T.cqLo < T.cqHi) (tckq tsu thd : Nat) :
    (∃ qg, GlsRel tckq true false ck1000 (fun _ => X) (fun _ => one) (fun _ => zero) qg ∧
        GlsQuiet tsu thd ck1000 (fun _ => one) (fun _ => zero) ∧ qg (1000 + T.cqHi) = zero) ∧
      (∀ q, FlopRel T false true false ck1000 (fun _ => X) (fun _ => one) (fun _ => zero) q →
        q (1000 + T.cqHi) = X) ∧
      (∀ q, FlopRel T false true false ck1000 (fun _ => one) (fun _ => one) (fun _ => zero) q →
        q (1000 + T.cqHi + 1) = one) := by
  refine ⟨⟨_, (gls_run_sr tckq tsu thd).1, (gls_run_sr tckq tsu thd).2, rfl⟩, fun q h => ?_,
    fun q h => capture_reset T hok h rises1000 (by omega) (norise_after _) (guard_sync T _ _ _)
      (const_eqOn one _ _) (by omega)⟩
  have hq0 : q 1000 = zero := h.init 1000 (norise_before 1000 (Nat.le_refl _)) (fun h => absurd h (by decide))
  rw [h.band 1000 _ rises1000 (by omega) (norise_after _) (guard_sync T _ _ _) (by omega) (Nat.le_refl _)]
  simp only [nextAt, ap, winVal_const (wpt_le hok.1) (const_eqOn zero _ _),
    winVal_const (wpt_le hok.2.1) (const_eqOn one _ _),
    winVal_const (wpt_le hok.2.2.1) (const_eqOn X _ _), hq0, knext, kmux]
  rfl

/-- At the prjxray AFF..DFF flop, both corners (any `res`). -/
theorem gls_vs_kleene_prjxray (c : XCorner) (res tckq tsu thd : Nat) :
    ∀ q, FlopRel (regFF c false res) false false false ck1000 (fun _ => zero) (fun _ => X)
      (fun _ => one) q → q (1000 + (regFF c false res).cqHi) = X :=
  fun _ h => kleene_ce_X _ (regFF_ok c false res) (by cases c <;> decide) h

end Formal.Core.Prims.Seq
