set_option linter.unusedSimpArgs false

/-!
# Formal.Cells.ArbT — the held `bd_arbiter` under H_ARB(T), Boolean read-time semantics

Shard B, THE goal (owner 2026-10-31): "the arbiter under H_ARB(T)". Core Lean only.
Notes: `formal/notes/B-arbT.md`.

## Semantics (mirrors Spec v1's `GateOK`, weaker)

A gate with `k` pins and an INIT table (bit `a` = output at address `a`, pin 0 the least
significant address bit, as `Formal.Target.addr`) holds on `y` from `t0` on if there is a
read map `f i t` with `f i t + lo i ≤ t ≤ f i t + hi i` and `y t = INIT[addr (pin i (f i t))]`
for every `t ≥ t0` (`RGate`). Spec v1's `GateOK` also asks each `f i` to be monotone; that
is omitted here, so every positive theorem below holds a fortiori for `GateOK`
(and every behaviour in the counterexample is monotone anyway: `cex_reads_mono`).

The four cells are the real `bd_arbiter` INITs (`cells/rtl/bd_arb.v`), with tied pins
folded (ugrant's I3 = I4 = 0, ua's I4 = I5 = 0; ustate's I5 = 1 selects `INIT[63:32]` for
`q` and O5 reads `INIT[31:0]`):
* `qInit  = 0xFFF0FFB2`, pins r1, r2, q, rst, A0  (`q = rst + C(r1, ~r2)`, frozen while A0)
* `r0Init = 0xACACACAC`, same pins               (`R0 = r1 q + r2 ~q`)
* `g1Init = 0xA0`, `g2Init = 0x0C`, pins r1, r2, q (`g1 = r1 q`, `g2 = r2 ~q`)
* `uaInit = 0x00E8`, pins g, A0, A, rst          (`A = C(g, A0)`, cleared by rst)
`*_eq` check each table against its Boolean equation (all inputs, `decide`).

## Results

* `q_stays`: if q is `b` on its feedback window before `s`, and on `[s, e]` every
  combination of pin reads CONFIRMS `b` (the table with q = b gives b: hold, A0 freeze, or
  the set/reset that agrees with b), then q is `b` on all of `[s, e]`. No race, no H_ARB
  needed. Corollaries: `confirm_freeze` (A0 = 1, rst = 0: any requests), `confirm_tie`
  (r1 = r2 = 1, rst = 0: any A0).
* `grant_excl`: q constant on the grant gates' read windows at `t` => not both grants.
* `ack_stays_low`: the C-element ua holds 0 while its grant reads 0 (whatever A0 does).
* `one_ack`: q = b settled on `[ta - W, e]` => the LOSING client's acknowledge does not rise
  on `[ta, e]`, for any A0 waveform. So: **a server transaction acknowledges at most one
  client, if q is settled `W` before A0 rises** (`W` = grant + ua read windows).
* **`double_ack` (counterexample, H_ARB(T) too weak when T exceeds the server latency):** a
  behaviour of the four cells (every gate holds, unit read delays except q's own feedback
  band [2, 3]) with H_ARB(T) for every `T ≥ 7` in its strong form (`ArbOK2`: all four
  non-feedback pins of ustate constant on `[t1, t2]` => q constant on `[t1 + T, t2]`), a
  near-tie (r1 rises at 10, r2 at 11), q oscillating (the circulating runt that is this
  model's metastability) until 20, the server raising A0 at 18 (6 after R0 rose at 12),
  in which BOTH acknowledges rise (A1 at 19, A2 at 20) inside one server transaction.

## What it means for THE theorem

Under H_ARB(T) alone the arbiter is not safe: q may still be unresolved when A0 rises if
`T` exceeds the time from the race to A0's rise, and then both clients are acknowledged
for one transaction (the double-ack shard A found in the research fid model, here from the
Spec semantics). `one_ack` gives the matching sufficient condition: q settled `W` before A0
rises. With H_ARB(T) that is a timing obligation on the circuit: from the last edge at
ustate's pins to A0's rise at ua must be at least `T + W` -- a path through the server, which
the checker must generate and prove from the bands; it cannot be assumed. At an arbiter where a
race can occur, the theorem's `T` margin is therefore bounded by the shortest such server path;
where arbitrations are separated (`ArbClean`), `T` does not enter at all (the target's simulated
arbitrations are all of that kind, JOURNAL-B 2026-11-01).

## Not covered
The whole-cell contract (four-phase on every channel, liveness, chaining phases): only the
exclusion core is here. The H_ARB form used (`ArbOK2`) is B's repair of Spec v1's `ArbOK`
(see `Wip/Bspec/ArbOKVacuous.lean`), not yet adopted by shard A.
-/

namespace Formal.Cells.ArbT

abbrev Sig := Nat → Bool

/-- Address of `k` pin values, pin 0 = bit 0 (as Spec v1's `addr`). -/
def addr : (k : Nat) → (Nat → Bool) → Nat
  | 0, _ => 0
  | k + 1, v => addr k v + (if v k then 2 ^ k else 0)

/-- A table read. -/
def lutF (init k : Nat) (v : Nat → Bool) : Bool := init.testBit (addr k v)

/-- **Read-time gate** from `t0` on: pin `i` read at `f i t`, delay in `[lo i, hi i]`. -/
def RGate (k init : Nat) (pin : Nat → Sig) (lo hi : Nat → Nat) (t0 : Nat) (y : Sig) : Prop :=
  ∃ f : Nat → Nat → Nat, ∀ t, t0 ≤ t →
    (∀ i, i < k → f i t + lo i ≤ t ∧ t ≤ f i t + hi i) ∧ y t = lutF init k (fun i => pin i (f i t))

/-- Pin list as a function (default: constant false). -/
def pins (l : List Sig) : Nat → Sig := fun i => l.getD i (fun _ => false)

def qInit : Nat := 0xFFF0FFB2
def r0Init : Nat := 0xACACACAC
def g1Init : Nat := 0xA0
def g2Init : Nat := 0x0C
def uaInit : Nat := 0x00E8

/-- Five pin values as an address function. -/
def v5 (a b c d e : Bool) : Nat → Bool := fun i =>
  if i = 0 then a else if i = 1 then b else if i = 2 then c else if i = 3 then d else e

def v3 (a b c : Bool) : Nat → Bool := v5 a b c false false
def v4 (a b c d : Bool) : Nat → Bool := v5 a b c d false

/-- The ustate table on pins (r1, r2, q, rst, A0): `q' = rst ∨ (A0 ? q : C(r1, ¬r2, q))`. -/
theorem q_eq : ∀ r1 r2 q rst a0 : Bool, lutF qInit 5 (v5 r1 r2 q rst a0) =
    (rst || (if a0 then q else ((r1 && !r2) || (q && !(!r1 && r2))))) := by decide

theorem r0_eq : ∀ r1 r2 q rst a0 : Bool, lutF r0Init 5 (v5 r1 r2 q rst a0) =
    ((r1 && q) || (r2 && !q)) := by decide

theorem g1_eq : ∀ r1 r2 q : Bool, lutF g1Init 3 (v3 r1 r2 q) = (r1 && q) := by decide
theorem g2_eq : ∀ r1 r2 q : Bool, lutF g2Init 3 (v3 r1 r2 q) = (r2 && !q) := by decide

/-- ua = bd_c2 on pins (g, A0, A, rst): majority, cleared by rst. -/
theorem ua_eq : ∀ g a0 a rst : Bool, lutF uaInit 4 (v4 g a0 a rst) =
    (!rst && ((g && a0) || (g && a) || (a0 && a))) := by decide

/-- The tables read only their first `k` pins. -/
theorem addr_congr : ∀ (k : Nat) (u v : Nat → Bool), (∀ i, i < k → u i = v i) → addr k u = addr k v
  | 0, _, _, _ => rfl
  | k + 1, u, v, h => by
    simp only [addr]
    rw [addr_congr k u v (fun i hi => h i (by omega)), h k (by omega)]

theorem lutF5 (init : Nat) (u : Nat → Bool) :
    lutF init 5 u = lutF init 5 (v5 (u 0) (u 1) (u 2) (u 3) (u 4)) :=
  rfl

theorem lutF3 (init : Nat) (u : Nat → Bool) :
    lutF init 3 u = lutF init 3 (v3 (u 0) (u 1) (u 2)) :=
  rfl

theorem lutF4 (init : Nat) (u : Nat → Bool) :
    lutF init 4 u = lutF init 4 (v4 (u 0) (u 1) (u 2) (u 3)) :=
  rfl

/-! ## q stays settled while the pins confirm it -/

/-- The pins (other than q) confirm the value `b`: the table with q = b gives b. -/
def Confirms (b r1 r2 rst a0 : Bool) : Prop := lutF qInit 5 (v5 r1 r2 b rst a0) = b

instance (b r1 r2 rst a0 : Bool) : Decidable (Confirms b r1 r2 rst a0) := by
  unfold Confirms; infer_instance

/-- A0 high, rst low: every request pattern confirms either value (the freeze). -/
theorem confirm_freeze (b r1 r2 : Bool) : Confirms b r1 r2 false true := by
  revert b r1 r2; decide

/-- Both requests high, rst low: either value is confirmed whatever A0 is (the tie hold). -/
theorem confirm_tie (b a0 : Bool) : Confirms b true true false a0 := by
  revert b a0; decide

/-- **q stays.** q gate on pins `[r1, r2, q, rst, a0]` with feedback delay `≥ 1`; q is `b`
on `[s - hi 2, s)`; on `[s, e]` every read combination confirms `b`. Then q is `b` on
`[s, e]`. -/
theorem q_stays {r1 r2 q rst a0 : Sig} {lo hi : Nat → Nat} {t0 s e : Nat} {b : Bool}
    (hg : RGate 5 qInit (pins [r1, r2, q, rst, a0]) lo hi t0 q) (hlo : 1 ≤ lo 2) (hs : t0 ≤ s)
    (hpre : ∀ t, s ≤ t + hi 2 → t < s → q t = b)
    (hconf : ∀ t, s ≤ t → t ≤ e → ∀ u0 u1 u3 u4 : Nat,
      u0 + lo 0 ≤ t → t ≤ u0 + hi 0 → u1 + lo 1 ≤ t → t ≤ u1 + hi 1 →
      u3 + lo 3 ≤ t → t ≤ u3 + hi 3 → u4 + lo 4 ≤ t → t ≤ u4 + hi 4 →
      Confirms b (r1 u0) (r2 u1) (rst u3) (a0 u4)) :
    ∀ t, s ≤ t → t ≤ e → q t = b := by
  obtain ⟨f, hf⟩ := hg
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro hst hte
    obtain ⟨hr, hy⟩ := hf t (by omega)
    have hq2 : q (f 2 t) = b := by
      have h2 := hr 2 (by omega)
      by_cases hc : s ≤ f 2 t
      · exact ih (f 2 t) (by omega) hc (by omega)
      · exact hpre (f 2 t) (by omega) (by omega)
    have h0 := hr 0 (by omega); have h1 := hr 1 (by omega)
    have h3 := hr 3 (by omega); have h4 := hr 4 (by omega)
    have hc := hconf t hst hte (f 0 t) (f 1 t) (f 3 t) (f 4 t) h0.1 h0.2 h1.1 h1.2 h3.1 h3.2 h4.1 h4.2
    rw [hy, lutF5]
    simp only [pins, List.getD_cons_zero, List.getD_cons_succ]
    rw [hq2]; exact hc

/-! ## Grant exclusion from a settled q -/

theorem grant_excl {r1 r2 q g1 g2 : Sig} {lo1 hi1 lo2 hi2 : Nat → Nat} {t0 t : Nat} {b : Bool}
    (h1 : RGate 3 g1Init (pins [r1, r2, q]) lo1 hi1 t0 g1)
    (h2 : RGate 3 g2Init (pins [r1, r2, q]) lo2 hi2 t0 g2) (ht : t0 ≤ t)
    (hq : ∀ s, s + lo1 2 ≤ t → t ≤ s + hi1 2 → q s = b)
    (hq' : ∀ s, s + lo2 2 ≤ t → t ≤ s + hi2 2 → q s = b) :
    ¬ (g1 t = true ∧ g2 t = true) := by
  obtain ⟨f1, hf1⟩ := h1
  obtain ⟨f2, hf2⟩ := h2
  obtain ⟨hr1, hy1⟩ := hf1 t ht
  obtain ⟨hr2, hy2⟩ := hf2 t ht
  have a := hq (f1 2 t) (hr1 2 (by omega)).1 (hr1 2 (by omega)).2
  have c := hq' (f2 2 t) (hr2 2 (by omega)).1 (hr2 2 (by omega)).2
  have e1 : g1 t = (r1 (f1 0 t) && q (f1 2 t)) := by rw [hy1, lutF3, g1_eq]; simp [pins]
  have e2 : g2 t = (r2 (f2 1 t) && !q (f2 2 t)) := by rw [hy2, lutF3, g2_eq]; simp [pins]
  rw [e1, e2, a, c]
  cases b <;> simp

/-! ## The losing acknowledge stays low -/

/-- ua on pins `[g, a0, A, rst]`: if A is 0 on its feedback window before `s` and every read
of g on `[s, e]` is 0, A is 0 on `[s, e]`, whatever A0 and rst do. -/
theorem ack_stays_low {g a0 A rst : Sig} {lo hi : Nat → Nat} {t0 s e : Nat}
    (hg : RGate 4 uaInit (pins [g, a0, A, rst]) lo hi t0 A) (hlo : 1 ≤ lo 2) (hs : t0 ≤ s)
    (hpre : ∀ t, s ≤ t + hi 2 → t < s → A t = false)
    (hglow : ∀ t u, s ≤ t → t ≤ e → u + lo 0 ≤ t → t ≤ u + hi 0 → g u = false) :
    ∀ t, s ≤ t → t ≤ e → A t = false := by
  obtain ⟨f, hf⟩ := hg
  intro t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro hst hte
    obtain ⟨hr, hy⟩ := hf t (by omega)
    have hA : A (f 2 t) = false := by
      have h2 := hr 2 (by omega)
      by_cases hc : s ≤ f 2 t
      · exact ih (f 2 t) (by omega) hc (by omega)
      · exact hpre (f 2 t) (by omega) (by omega)
    have hgr := hglow t (f 0 t) hst hte (hr 0 (by omega)).1 (hr 0 (by omega)).2
    rw [hy, lutF4, ua_eq]
    simp only [pins, List.getD_cons_zero, List.getD_cons_succ]
    rw [hA, hgr]; simp

/-- **At most one acknowledge per server transaction, if q is settled in time.** q = true on
every instant g2's gate reads at `[s - hi0, e]` (in particular, q settled `W = hi0 + hi_g`
before), A2 low on its feedback window before `s`: A2 stays low on `[s, e]` whatever A0
does. (The mirror, q = false, keeps A1 low.) -/
theorem one_ack {r1 r2 q g2 a0 A2 rst : Sig} {log hig loa hia : Nat → Nat} {t0 s e : Nat}
    (hg2 : RGate 3 g2Init (pins [r1, r2, q]) log hig t0 g2)
    (ha2 : RGate 4 uaInit (pins [g2, a0, A2, rst]) loa hia t0 A2)
    (hlo : 1 ≤ loa 2) (hs : t0 + hia 0 ≤ s)
    (hq : ∀ u, s ≤ u + hia 0 + hig 2 → u ≤ e → q u = true)
    (hpre : ∀ t, s ≤ t + hia 2 → t < s → A2 t = false) :
    ∀ t, s ≤ t → t ≤ e → A2 t = false := by
  apply ack_stays_low ha2 hlo (by omega) hpre
  intro t u hst hte hu1 hu2
  obtain ⟨f, hf⟩ := hg2
  obtain ⟨hr, hy⟩ := hf u (by omega)
  have h2 := hr 2 (by omega)
  have hqr : q (f 2 u) = true := hq (f 2 u) (by omega) (by omega)
  rw [hy, lutF3, g2_eq]
  simp only [pins, List.getD_cons_zero, List.getD_cons_succ]
  rw [hqr]; simp

/-! ## Counterexample: q unresolved when A0 rises => both clients acknowledged -/

/-- A signal is constant on `[t1, t2]` (Spec v1's `ConstOn`). -/
def ConstOn (s : Sig) (t1 t2 : Nat) : Prop := ∀ t, t1 ≤ t → t ≤ t2 → s t = s t1

/-- **H_ARB(T), B's form**: every non-feedback pin of the state LUT (r1, r2, rst, A0)
constant on `[t1, t2]` => q constant on `[t1 + T, t2]`. -/
def ArbOK2 (T : Nat) (r1 r2 rst a0 q : Sig) : Prop :=
  ∀ t1 t2, ConstOn r1 t1 t2 → ConstOn r2 t1 t2 → ConstOn rst t1 t2 → ConstOn a0 t1 t2 →
    ConstOn q (t1 + T) t2

def cr1 : Sig := fun t => decide (10 ≤ t)
def cr2 : Sig := fun t => decide (11 ≤ t)
def crst : Sig := fun _ => false
def ca0 : Sig := fun t => decide (18 ≤ t)
def cq : Sig := fun t => decide (11 ≤ t ∧ t < 20 ∧ t % 2 = 1)
def cR0 : Sig := fun t => decide (12 ≤ t)
def cg1 : Sig := fun t => decide (12 ≤ t ∧ t ≤ 20 ∧ t % 2 = 0)
def cg2 : Sig := fun t => decide (12 ≤ t ∧ ¬ (t ≤ 20 ∧ t % 2 = 0))
def cA1 : Sig := fun t => decide (19 ≤ t)
def cA2 : Sig := fun t => decide (20 ≤ t)

def one : Nat → Nat := fun _ => 1
/-- q's own feedback band `[2, 3]`, every other pin exactly 1. -/
def qlo : Nat → Nat := fun i => if i = 2 then 2 else 1
def qhi : Nat → Nat := fun i => if i = 2 then 3 else 1
/-- q's read map: delay 2 on the feedback, except one read at delay 3 at `t = 21` that
swallows the circulating runt (the resolution). -/
def qread : Nat → Nat → Nat := fun i t => if i = 2 then (if t = 21 then 18 else t - 2) else t - 1

theorem cex_reads_mono : ∀ i a b, a ≤ b → 3 ≤ a → qread i a ≤ qread i b := by
  intro i a b hab ha; unfold qread; repeat' split
  all_goals omega

/-- Beyond 40 every signal is constant. -/
theorem cex_q (t : Nat) (ht : 3 ≤ t) :
    cq t = lutF qInit 5 (fun i => pins [cr1, cr2, cq, crst, ca0] i (qread i t)) := by
  by_cases h : t < 40
  · have key : ∀ t, t < 40 → 3 ≤ t → cq t = lutF qInit 5 (fun i => pins [cr1, cr2, cq, crst, ca0] i (qread i t)) := by decide
    exact key t h ht
  · rw [lutF5]
    simp only [pins, List.getD_cons_zero, List.getD_cons_succ, qread]
    simp only [cq, cr1, cr2, crst, ca0, show ¬ t = 21 by omega, ite_false]
    rw [q_eq]
    simp [show ¬ (t < 20) by omega, show ¬ (t - 2 < 20) by omega, show 18 ≤ t - 1 by omega]

theorem cex_R0 (t : Nat) (ht : 3 ≤ t) :
    cR0 t = lutF r0Init 5 (fun i => pins [cr1, cr2, cq, crst, ca0] i (t - 1)) := by
  by_cases h : t < 40
  · have key : ∀ t, t < 40 → 3 ≤ t → cR0 t = lutF r0Init 5 (fun i => pins [cr1, cr2, cq, crst, ca0] i (t - 1)) := by decide
    exact key t h ht
  · rw [lutF5]
    simp only [pins, List.getD_cons_zero, List.getD_cons_succ]
    rw [r0_eq]; simp [cR0, cr1, cr2, cq, show 10 ≤ t - 1 by omega, show 11 ≤ t - 1 by omega, show 12 ≤ t - 1 by omega, show 18 ≤ t - 1 by omega, show 19 ≤ t - 1 by omega, show 20 ≤ t - 1 by omega, show ¬ (t - 1 < 20) by omega, show ¬ (t - 1 ≤ 20) by omega, show 12 ≤ t by omega, show 19 ≤ t by omega, show 20 ≤ t by omega, show ¬ (t ≤ 20) by omega]

theorem cex_g1 (t : Nat) (ht : 3 ≤ t) :
    cg1 t = lutF g1Init 3 (fun i => pins [cr1, cr2, cq] i (t - 1)) := by
  by_cases h : t < 40
  · have key : ∀ t, t < 40 → 3 ≤ t → cg1 t = lutF g1Init 3 (fun i => pins [cr1, cr2, cq] i (t - 1)) := by decide
    exact key t h ht
  · rw [lutF3]
    simp only [pins, List.getD_cons_zero, List.getD_cons_succ]
    rw [g1_eq]; simp [cg1, cr1, cq, show 10 ≤ t - 1 by omega, show 11 ≤ t - 1 by omega, show 12 ≤ t - 1 by omega, show 18 ≤ t - 1 by omega, show 19 ≤ t - 1 by omega, show 20 ≤ t - 1 by omega, show ¬ (t - 1 < 20) by omega, show ¬ (t - 1 ≤ 20) by omega, show 12 ≤ t by omega, show 19 ≤ t by omega, show 20 ≤ t by omega, show ¬ (t ≤ 20) by omega]

theorem cex_g2 (t : Nat) (ht : 3 ≤ t) :
    cg2 t = lutF g2Init 3 (fun i => pins [cr1, cr2, cq] i (t - 1)) := by
  by_cases h : t < 40
  · have key : ∀ t, t < 40 → 3 ≤ t → cg2 t = lutF g2Init 3 (fun i => pins [cr1, cr2, cq] i (t - 1)) := by decide
    exact key t h ht
  · rw [lutF3]
    simp only [pins, List.getD_cons_zero, List.getD_cons_succ]
    rw [g2_eq]; simp [cg2, cr2, cq, show 10 ≤ t - 1 by omega, show 11 ≤ t - 1 by omega, show 12 ≤ t - 1 by omega, show 18 ≤ t - 1 by omega, show 19 ≤ t - 1 by omega, show 20 ≤ t - 1 by omega, show ¬ (t - 1 < 20) by omega, show ¬ (t - 1 ≤ 20) by omega, show 12 ≤ t by omega, show 19 ≤ t by omega, show 20 ≤ t by omega, show ¬ (t ≤ 20) by omega]

theorem cex_A1 (t : Nat) (ht : 3 ≤ t) :
    cA1 t = lutF uaInit 4 (fun i => pins [cg1, ca0, cA1, crst] i (t - 1)) := by
  by_cases h : t < 40
  · have key : ∀ t, t < 40 → 3 ≤ t → cA1 t = lutF uaInit 4 (fun i => pins [cg1, ca0, cA1, crst] i (t - 1)) := by decide
    exact key t h ht
  · rw [lutF4]
    simp only [pins, List.getD_cons_zero, List.getD_cons_succ]
    rw [ua_eq]; simp [cA1, ca0, crst, show 10 ≤ t - 1 by omega, show 11 ≤ t - 1 by omega, show 12 ≤ t - 1 by omega, show 18 ≤ t - 1 by omega, show 19 ≤ t - 1 by omega, show 20 ≤ t - 1 by omega, show ¬ (t - 1 < 20) by omega, show ¬ (t - 1 ≤ 20) by omega, show 12 ≤ t by omega, show 19 ≤ t by omega, show 20 ≤ t by omega, show ¬ (t ≤ 20) by omega]

theorem cex_A2 (t : Nat) (ht : 3 ≤ t) :
    cA2 t = lutF uaInit 4 (fun i => pins [cg2, ca0, cA2, crst] i (t - 1)) := by
  by_cases h : t < 40
  · have key : ∀ t, t < 40 → 3 ≤ t → cA2 t = lutF uaInit 4 (fun i => pins [cg2, ca0, cA2, crst] i (t - 1)) := by decide
    exact key t h ht
  · rw [lutF4]
    simp only [pins, List.getD_cons_zero, List.getD_cons_succ]
    rw [ua_eq]; simp [cA2, ca0, crst, show 10 ≤ t - 1 by omega, show 11 ≤ t - 1 by omega, show 12 ≤ t - 1 by omega, show 18 ≤ t - 1 by omega, show 19 ≤ t - 1 by omega, show 20 ≤ t - 1 by omega, show ¬ (t - 1 < 20) by omega, show ¬ (t - 1 ≤ 20) by omega, show 12 ≤ t by omega, show 19 ≤ t by omega, show 20 ≤ t by omega, show ¬ (t ≤ 20) by omega]

theorem unit_reads (k : Nat) (t : Nat) (ht : 3 ≤ t) :
    ∀ i, i < k → (fun _ t => t - 1) i t + one i ≤ t ∧ t ≤ (fun _ t => t - 1) i t + one i :=
  fun _ _ => by simp only [one]; omega

theorem cex_gates :
    RGate 5 qInit (pins [cr1, cr2, cq, crst, ca0]) qlo qhi 3 cq ∧
    RGate 5 r0Init (pins [cr1, cr2, cq, crst, ca0]) one one 3 cR0 ∧
    RGate 3 g1Init (pins [cr1, cr2, cq]) one one 3 cg1 ∧
    RGate 3 g2Init (pins [cr1, cr2, cq]) one one 3 cg2 ∧
    RGate 4 uaInit (pins [cg1, ca0, cA1, crst]) one one 3 cA1 ∧
    RGate 4 uaInit (pins [cg2, ca0, cA2, crst]) one one 3 cA2 := by
  refine ⟨⟨qread, fun t ht => ⟨fun i _ => ?_, cex_q t ht⟩⟩,
    ⟨fun _ t => t - 1, fun t ht => ⟨unit_reads 5 t ht, cex_R0 t ht⟩⟩,
    ⟨fun _ t => t - 1, fun t ht => ⟨unit_reads 3 t ht, cex_g1 t ht⟩⟩,
    ⟨fun _ t => t - 1, fun t ht => ⟨unit_reads 3 t ht, cex_g2 t ht⟩⟩,
    ⟨fun _ t => t - 1, fun t ht => ⟨unit_reads 4 t ht, cex_A1 t ht⟩⟩,
    ⟨fun _ t => t - 1, fun t ht => ⟨unit_reads 4 t ht, cex_A2 t ht⟩⟩⟩
  unfold qread qlo qhi
  repeat' split
  all_goals omega

/-- The counterexample meets H_ARB(T) in B's strong form for every `T ≥ 7`. -/
theorem cex_arb (T : Nat) (hT : 7 ≤ T) : ArbOK2 T cr1 cr2 crst ca0 cq := by
  intro t1 t2 h1 h2 _ h4 t ht1 ht2
  by_cases hlate : 20 ≤ t1 + T
  · simp only [cq]; simp [show ¬ (t < 20) by omega, show ¬ (t1 + T < 20) by omega]
  · by_cases hearly : t2 ≤ 10
    · simp only [cq]; simp [show ¬ (11 ≤ t) by omega, show ¬ (11 ≤ t1 + T) by omega]
    · exfalso
      by_cases a : t1 ≤ 9
      · have := h1 10 (by omega) (by omega); simp [cr1] at this; omega
      · by_cases b : t1 = 10
        · have := h2 11 (by omega) (by omega); simp [cr2] at this; omega
        · have := h4 18 (by omega) (by omega); simp [ca0] at this; omega

/-- **Double acknowledge.** Every cell gate holds, H_ARB(T) holds for every `T ≥ 7`; the
server raises A0 at 18, six after R0 rose (at 12, and R0 stays high: one transaction);
both A1 (at 19) and A2 (at 20) rise while A0 is high. -/
theorem double_ack (T : Nat) (hT : 7 ≤ T) :
    ArbOK2 T cr1 cr2 crst ca0 cq ∧
    (∀ t, cR0 t = decide (12 ≤ t)) ∧ (∀ t, ca0 t = decide (18 ≤ t)) ∧
    cA1 18 = false ∧ cA1 19 = true ∧ cA2 19 = false ∧ cA2 20 = true ∧
    cr1 19 = true ∧ cr2 20 = true :=
  ⟨cex_arb T hT, fun _ => rfl, fun _ => rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

end Formal.Cells.ArbT
