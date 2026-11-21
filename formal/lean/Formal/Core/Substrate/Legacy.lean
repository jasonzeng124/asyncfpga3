import Formal.Core.Substrate.Chan
import Formal.Cells.CElemTiming
import Formal.Net.Prelim
import Formal.Timing.Semantics

/-!
# Substrate, part 4: bridges from the shards' local channels (porting aid)

Shard B (`Formal.Cells.Prelim`, `Formal.Cells.CElemTiming`) and shard C
(`Formal.Net.Prelim`, `Formal.Timing.Semantics`) defined their own discrete
channels before Core existed. This file relates them to the substrate's
`Win` / `WinR` so their theorems apply to substrate behaviours today, and so
the port is a renaming. It is the ONLY substrate file that imports the
shards' preliminaries: when B and C delete `Prelim`, delete this file (or the
affected section) with it. Values (B's `K3`, `lutB`, `lutK`) are already
bridged to `Formal.Core.K3` / `Formal.Core.Lut` by `Formal.Core.Bridge`
(`isoCells`, `cells_lutB_eq_eval`, `cells_lutK_eq_keval`).

* Shard B: `win_iff_winDelay` (`Win` IS `WinDelay`, `Iff.rfl`),
  `transport_fixed_win` (B's fixed `Transport d`), `loop_iff` (B's `Loop`
  is two `Win` relations and `H_LOOP_POS`).
* Shard C: `winR_boundedDelay` (`WinR ⊆ BoundedDelay`), `winR_quiet`
  (`WinR` gives H_QUIESCENT), `boundedDelay_not_winR` (strict: a
  `BoundedDelay` output may hold an old value while the input chatters, an
  inertial-like behaviour no window admits), `runOfWinR` (a netlist
  whose arcs are `WinR` channels is a `Timing.Run`, so C's checker soundness
  applies to substrate behaviours).
-/

namespace Formal.Core.Substrate

/-! ## Shard B -/

/-- `Win` is, by definition, shard B's `WinDelay`. -/
theorem win_iff_winDelay {lo hi : Nat} {i o : Sig} :
    Win lo hi i o ↔ Formal.Cells.CElemTiming.WinDelay lo hi i o := Iff.rfl

/-- B's fixed transport delay (`o (t + d) = i t`, power-up free) is a `Win`
behaviour for any band containing `d`. -/
theorem transport_fixed_win {lo hi d : Nat} {i o : Sig} (h1 : lo ≤ d) (h2 : d ≤ hi)
    (h : Formal.Cells.CElemTiming.Transport d i o) : Win lo hi i o :=
  shift_win h1 h2 h

/-- B's feedback-LUT cell relation in substrate terms. -/
theorem loop_iff {init : Nat} {a b rst O qp : Sig} {dlmin dlmax dwmin dwmax : Nat} :
    Formal.Cells.CElemTiming.Loop init a b rst O qp dlmin dlmax dwmin dwmax ↔
      Win dlmin dlmax (fun t => Formal.Cells.CElemTiming.exc init (a t) (b t) (qp t) (rst t)) O ∧
      Win dwmin dwmax O qp ∧ 0 < dlmin + dwmin :=
  ⟨fun L => ⟨L.H_LUT, L.H_FB, L.H_LOOP_POS⟩, fun ⟨h1, h2, h3⟩ => ⟨h1, h2, h3⟩⟩

/-! ## Shard C -/

/-- C's `Timing.shift` is Core's fixed delay. -/
theorem timing_shift_eq_delay (d : Nat) (i : Sig) : Formal.Timing.shift d i = TraceDiscrete.delay d i := by
  funext t
  simp only [Formal.Timing.shift, TraceDiscrete.delay]
  split <;> first | rfl | (congr 1; omega)

/-- `WinR` gives H_QUIESCENT: the output starts at the input's value. -/
theorem winR_quiet {lo hi : Nat} {i o : Sig} (h : WinR lo hi i o) : o 0 = i 0 := by
  obtain ⟨s, _, h2, e⟩ := h 0
  have : s = 0 := by omega
  rw [e, this]

/-- **`WinR ⊆ BoundedDelay`** (shard C's H_BOUNDED_DELAY). -/
theorem winR_boundedDelay {lo hi : Nat} {i o : Sig} (h : WinR lo hi i o) :
    Formal.Net.BoundedDelay lo hi i o := by
  have hl := winR_le h
  constructor
  · intro t ht
    obtain ⟨s, a1, a2, e⟩ := h (t + 1)
    -- an output change before `lo` is impossible: both steps read `i 0`
    have hlt : lo ≤ t + 1 := by
      refine Nat.le_of_not_lt fun hc => ht ?_
      obtain ⟨s0, b1, b2, e0⟩ := h t
      have : s = 0 := by omega
      have : s0 = 0 := by omega
      subst_vars; rw [e0, e]
    exact ⟨t + 1 - s, by omega, by omega, by omega, by rw [e]; congr 1; omega⟩
  · intro t ht hs
    obtain ⟨s, a1, a2, e⟩ := h t
    rw [e, hs s a1 (by omega), hs t (by omega) (Nat.le_refl _)]

/-- A chattering input (period 3, never stable for 3 steps) and a constant
output. -/
def chatter : Sig := fun t => t % 3 != 2

/-- **Strict:** `BoundedDelay 1 2` admits holding `false` forever against the
chattering input (no output change; the input is never stable long enough to
force settling); no `WinR 1 2` behaviour does. -/
theorem boundedDelay_not_winR :
    Formal.Net.BoundedDelay 1 2 chatter (fun _ => false) ∧
    ¬ WinR 1 2 chatter (fun _ => false) := by
  refine ⟨⟨fun t ht => absurd rfl ht, fun t ht hs => ?_⟩, fun h => ?_⟩
  · exfalso
    have e2 := hs (t - 1) (by omega) (by omega)
    have e3 := hs t (by omega) (Nat.le_refl _)
    simp only [chatter] at e2 e3
    have : t % 3 = 0 ∨ t % 3 = 1 ∨ t % 3 = 2 := by omega
    rcases this with h | h | h
    · have h1 : (t - 1) % 3 = 2 := by omega
      have h2 : (t - 2) % 3 = 1 := by omega
      rw [h1, h2] at e2; exact absurd e2 (by decide)
    · have h2 : (t - 2) % 3 = 2 := by omega
      rw [h, h2] at e3; exact absurd e3 (by decide)
    · have h2 : (t - 2) % 3 = 0 := by omega
      rw [h, h2] at e3; exact absurd e3 (by decide)
  · obtain ⟨s, a1, a2, e⟩ := h 2
    have : s = 0 ∨ s = 1 := by omega
    rcases this with rfl | rfl <;> simp [chatter] at e

open Formal.Timing in

/-- **Substrate behaviours are runs of C's timing semantics.** If every arc's
pin trace is a `WinR` copy of its source, together with C's launch, locality
and node hypotheses, the data form a `Run`; so every theorem C proves for all
runs (checker soundness included) holds for it. -/
def runOfWinR {net : Netlist} {sig : Nat → Formal.Net.Trace} (pin : Nat → Formal.Net.Trace)
    (g : Nat → (Nat → Bool) → Bool)
    (launch : ∀ t, Formal.Net.changes (sig 0) t → t = 0)
    (hw : ∀ k a, net.arcs[k]? = some a → WinR a.lo a.hi (sig a.src) (pin k))
    (local_ : ∀ v, Local net v (g v))
    (node : ∀ v, v ≠ 0 → ∀ t, sig v t = g v (fun k => pin k t)) : Run net sig where
  pin := pin
  g := g
  launch := launch
  bd := fun k a hk => winR_boundedDelay (hw k a hk)
  quiet := fun k a hk => winR_quiet (hw k a hk)
  local_ := local_
  node := node

end Formal.Core.Substrate
