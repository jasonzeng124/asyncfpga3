import Formal.Core.XSimChan
import Formal.Core.XAudit.Fast

/-!
# Formal.Core.XAudit.SoundCells — the executable's timed verdicts, cell by cell, any time domain

Probe XSound2 (shard A). See `formal/notes/A-xsound2.md`.

`Design.lean`/`Fast.lean` state what `xaudit`'s timed verdicts mean for
DISCRETE behaviours (`ℕ → Bool`, transport warps). Here the same verdicts,
read from the very function the executable runs (`Fast.auditF`, rows read with
`Fast.valF`), are theorems about behaviours in ANY time domain `τ` with a cell
map `c : τ → ℕ`, whose gates are the parsed LUTs (INIT bit `addr(pins)`, zero
delay, `excT_toLGate`) followed by channels satisfying `XSimChan.ChanCells`.
`XSimChanReal`/`SoundPhys` instantiate this with `ℝ` time and the `Core/Delay`
transport and inertial channels.

* `valF_sound_cells`: every printed value covers the concrete value at every
  instant of its cell.
* `noXF_sound_cells`: "no X at `w` on steps `[t1, t2]`" ⇒ at every instant of
  the cells `t1..t2`, `w` has the printed binary value, in every behaviour; so
  every behaviour has the same waveform there, constant within each cell.
* `constF_sound_cells`: if the printed values on `[t1, t2]` are all `v`
  (`allEqF`, a Boolean check on the rows), `w` is `v` at every instant of those
  cells: binary and constant, no glitch.
* `settledF_cells`: the FIXED POINT verdict: binary values of row `T` hold at
  every instant of every cell `≥ T`.
-/

namespace Formal.Core.XAudit.SoundCells

open Formal.Core K3
open Formal.Core.XSim
open Formal.Core.XSimChan
open Formal.Core.XAudit
open Formal.Core.XAudit.Fast

variable {τ : Type}

/-- The zero-delay function of a parsed gate is INIT bit `addr(pin values)`. -/
theorem excT_toLGate (d : Design) (g : GSpec) (x : Fin d.n → τ → Bool) :
    excT (g.toLGate d) x =
      fun t => g.init.testBit (addr (fun p : Fin g.k => x (d.wire (g.ins.getD p.val 0)) t)) := by
  funext t
  exact g.lut_entry _ (addr_lt _)

/-- **The physical gate hypothesis, step level.** Every parsed gate's output
wire is its zero-delay INIT function followed by a `ChanCells` channel with
the gate's step band. -/
def SatCells (d : Design) (c : τ → Nat) (x : Fin d.n → τ → Bool) : Prop :=
  ∀ g ∈ d.gates, ChanCells c g.lo g.hi (excT (g.toLGate d) x) (x (d.wire g.out))

/-- The concrete inputs are covered, cell by cell, by the abstract stimulus. -/
def InputsCoveredT (d : Design) (u : Fin d.n → Nat → K3) (c : τ → Nat)
    (x : Fin d.n → τ → Bool) : Prop :=
  ∀ w, Undriven (build d) w → ∀ t, u w (c t) ⊑ ofBool (x w t)

theorem satCells_build {d : Design} {c : τ → Nat} {x : Fin d.n → τ → Bool}
    (h : SatCells d c x) : ∀ G ∈ build d, ChanCells c G.lo G.hi (excT G x) (x G.out) := by
  intro G hG
  simp only [build, List.mem_map] at hG
  obtain ⟨g, hg, rfl⟩ := hG
  exact h g hg

/-- Abstract cover of every instant (the kernel `XSim.val` form). -/
theorem val_sound_cells (d : Design) (hwf : d.WF) (u : Fin d.n → Nat → K3) (c : τ → Nat)
    (x : Fin d.n → τ → Bool) (hsat : SatCells d c x) (hin : InputsCoveredT d u c x) :
    ∀ t w, val (build d) u a0X (c t) w ⊑ ofBool (x w t) :=
  sound_cells (build d) u a0X c (build_lo d hwf) x (satCells_build hsat) hin
    (fun _ _ _ _ => X_le _)

/-- **Every value printed by the executable covers every instant of its cell.** -/
theorem valF_sound_cells (d : Design) (hwf : d.WF) (u : Fin d.n → Nat → K3) (T : Nat)
    (c : τ → Nat) (x : Fin d.n → τ → Bool) (hsat : SatCells d c x)
    (hin : InputsCoveredT d u c x) (t : τ) (ht : c t ≤ T) (w : Fin d.n) :
    valF (auditF d u T) (c t) w.val ⊑ ofBool (x w t) := by
  rw [auditF_eq d hwf u T (c t) ht w, valAt_audit d u T (c t) ht w]
  exact val_sound_cells d hwf u c x hsat hin t w

/-- **Meaning of "no X at `w` on steps `[t1, t2]`"**, any time domain: at every
instant of the cells `t1..t2`, `w` has the printed value, in every behaviour. -/
theorem noXF_sound_cells (d : Design) (hwf : d.WF) (u : Fin d.n → Nat → K3) (T : Nat)
    (w : Fin d.n) (t1 t2 : Nat) (ht2 : t2 ≤ T) (h : noXF (auditF d u T) w.val t1 t2 = true)
    (c : τ → Nat) (x : Fin d.n → τ → Bool) (hsat : SatCells d c x)
    (hin : InputsCoveredT d u c x) :
    ∀ t, t1 ≤ c t → c t ≤ t2 → x w t = pick (valF (auditF d u T) (c t) w.val) := by
  intro t h1 h2
  simp only [noXF, List.all_eq_true, List.mem_range'_1, bne_iff_ne, ne_eq] at h
  obtain ⟨v, hv⟩ := ne_X_iff.mp (h (c t) ⟨h1, by omega⟩)
  rw [defined_eq (valF_sound_cells d hwf u T c x hsat hin t (by omega) w) hv, hv]
  cases v <;> rfl

/-- Two behaviours agree on `w` at every instant of an X-free stretch of cells. -/
theorem noXF_deterministic_cells (d : Design) (hwf : d.WF) (u : Fin d.n → Nat → K3) (T : Nat)
    (w : Fin d.n) (t1 t2 : Nat) (ht2 : t2 ≤ T) (h : noXF (auditF d u T) w.val t1 t2 = true)
    (c : τ → Nat) (x y : Fin d.n → τ → Bool) (hx : SatCells d c x) (hy : SatCells d c y)
    (hix : InputsCoveredT d u c x) (hiy : InputsCoveredT d u c y) :
    ∀ t, t1 ≤ c t → c t ≤ t2 → x w t = y w t := by
  intro t h1 h2
  rw [noXF_sound_cells d hwf u T w t1 t2 ht2 h c x hx hix t h1 h2,
    noXF_sound_cells d hwf u T w t1 t2 ht2 h c y hy hiy t h1 h2]

/-- Boolean check on the rows: every printed value of `w` on `[t1, t2]` is `v`. -/
def allEqF (H : Array (Array K3)) (w t1 t2 : Nat) (v : Bool) : Bool :=
  (List.range' t1 (t2 + 1 - t1)).all (fun s => valF H s w == ofBool v)

/-- **Binary and constant.** If the executable prints `v` at every step of
`[t1, t2]` for `w`, then in every behaviour `w = v` at every instant of the
cells `t1..t2`: no X and no glitch, for every admissible delay. -/
theorem constF_sound_cells (d : Design) (hwf : d.WF) (u : Fin d.n → Nat → K3) (T : Nat)
    (w : Fin d.n) (t1 t2 : Nat) (ht2 : t2 ≤ T) (v : Bool)
    (h : allEqF (auditF d u T) w.val t1 t2 v = true)
    (c : τ → Nat) (x : Fin d.n → τ → Bool) (hsat : SatCells d c x)
    (hin : InputsCoveredT d u c x) :
    ∀ t, t1 ≤ c t → c t ≤ t2 → x w t = v := by
  intro t h1 h2
  simp only [allEqF, List.all_eq_true, List.mem_range'_1, beq_iff_eq] at h
  exact defined_eq (valF_sound_cells d hwf u T c x hsat hin t (by omega) w) (h (c t) ⟨h1, by omega⟩)

/-- **FIXED POINT** (any time domain): stimulus constant from `T ≥ 1`, the last
`maxHi + 1` fast rows equal ⇒ every binary value of row `T` holds at every
instant of every cell `≥ T`, in every behaviour. -/
theorem settledF_cells (d : Design) (hwf : d.WF) (u : Fin d.n → Nat → K3) (T : Nat) (hT : 1 ≤ T)
    (hu : ∀ w, Undriven (build d) w → ∀ t, T ≤ t → u w t = u w T)
    (hfix : rowsFixedF (auditF d u T) T d.maxHi = true)
    (c : τ → Nat) (x : Fin d.n → τ → Bool) (hsat : SatCells d c x)
    (hin : InputsCoveredT d u c x) (w : Fin d.n) (v : Bool)
    (hv : valF (auditF d u T) T w.val = ofBool v) : ∀ t, T ≤ c t → x w t = v := by
  intro t ht
  have hs := val_stationary (build d) u a0X d.maxHi T hT (build_lo d hwf) (build_lohi d hwf)
    (build_hi d) hu (rowsFixedF_spec d hwf u T hfix) (c t) w ht
  have hc := val_sound_cells d hwf u c x hsat hin t w
  rw [hs, ← valAt_audit d u T T (Nat.le_refl _) w, ← auditF_eq d hwf u T T (Nat.le_refl _) w,
    hv] at hc
  exact defined_eq hc rfl

end Formal.Core.XAudit.SoundCells
