import Formal.Cells.CElemTiming
import Formal.Cells.LibCtlMergeMux

/-!
# Probe Lib4: the `bd_mux` return-to-zero race (H_MUX_RTZ) as a timing inequality

Lib3 (`MergeMuxSI.mux_needs_rtz`) found that `bd_mux` is not speed independent:
after x's transaction `z_ack` falls and `x_ack = C(j0, z_ack)` (`uxa`, a
`bd_c2`) is excited to fall; a new control token selecting y, whose request is
already waiting, makes the server raise `z_ack` again, which withdraws the
pending fall. This file puts that race in the timed model of `CElemTiming`
(time `Nat`, 1 tick = 1 ps intended; window channels; REAL INITs).

## Results

* §1 duality: with `rst = 0`, `bd_c2`'s INIT is self-dual, so a negated loop
  behaviour is a loop behaviour (`loop_dual`, `inertial_not`). The pending-fall
  race is the exact dual of `CElemTiming`'s minimum pulse width.
* §2 cell level (`uxa` alone, inputs as seen at its pins):
  - `rtz_safe`: if `j0` and `z_ack` are both low at uxa's pins on
    `[te, tr)` with **H_RTZ: `te + dlmax + dwmax ≤ tr`** (the fall goes through
    the LUT AND round its own feedback wire before `z_ack`'s next rise reaches
    its pin), then `x_ack` is low on `[te + dlmax, t2 + dlmin]` for as long as
    `j0` stays low, whatever `z_ack` does after `tr`.
  - `rtz_counter`: for EVERY fixed `dl, dw` and every low-window `0 < w < dl+dw`
    a closed-form trace satisfying all gate relations (transport delays) in
    which, with `j0 = 0` and `z_ack = 1` forever after the window, `x_ack`
    oscillates forever (low runts of width `w`, period `dl + dw`): a runt
    train the x client can read as fall-then-acknowledge.
  - `rtz_inertial_lost`: with an inertial LUT whose threshold exceeds the
    window, the fall is LOST: `x_ack` stays 1 through the next (y) transaction
    (the C-element re-latched; x's handshake stalls on a stale acknowledge).
  - So for fixed delays the inequality is EXACT: `w ≥ dl + dw` safe,
    `w < dl + dw` misbehaves.
* §3 environment level (`mux_rtz_env_safe`): the window `tr - te` derived from
  the mux's environment. A trace-level chain through the control sender
  (named hypothesis `H_CTL`), the routed wires, `uj1` (REAL INIT, a feedback
  loop), `uor` (REAL INIT), the request delay line (`H_DLY`), the server
  (`H_SRV`) and the `z_ack` wire back to `uxa`. Inequality H_RTZ_ENV:

      te + dlmax + dwmax ≤ Tzf + (wzc + dc + wcr + dl1 + wjo + dlo + dz + ds) + wux

  `Tzf`: z_ack falls at the server; `te ≥ Tzf + Wux`: the fall has reached
  uxa (and j0 is low there). All path terms are MINIMUM delays.
* §4 bd_merge (`merge_rtz_of_latency`): there the next `z_ack` rise is
  causally after `x_ack`'s fall was SEEN (H_MERGE_SEQ / four-phase), so the
  race reduces to CElemTiming's H_ENV_LATENCY (`dlmax + dwmax ≤ dlmin + E`),
  the generic C-element condition; no mux-like race.
* §5 numbers: the inequality at consistent prjxray corners for the bdc
  configuration (`bd_link` control sender and server). See the notes file.

Core Lean; proofs by `omega`, strong induction, small `decide`.
-/

namespace Formal.Cells.MuxRtzTimed
open Formal.Cells
open Formal.Cells.CElemTiming

/-! ## 1. Duality -/

/-- `bd_c2` with `rst = 0` is self-dual (from the REAL INIT, 8 rows). -/
theorem c2_dual (a b q : Bool) :
    exc INIT_c2 (!a) (!b) (!q) false = !(exc INIT_c2 a b q false) := by
  cases a <;> cases b <;> cases q <;> decide

theorem winDelay_not {dmin dmax : Nat} {x y : Trace} (h : WinDelay dmin dmax x y) :
    WinDelay dmin dmax (fun t => !x t) (fun t => !y t) := by
  intro t ht
  obtain ⟨s, h1, h2, e⟩ := h t ht
  exact ⟨s, h1, h2, by simp [e]⟩

/-- **Negated behaviours are behaviours** (rst held at 0). -/
theorem loop_dual {a b rst O qp : Trace} {dlmin dlmax dwmin dwmax : Nat}
    (L : Loop INIT_c2 a b rst O qp dlmin dlmax dwmin dwmax) (hr : ∀ t, rst t = false) :
    Loop INIT_c2 (fun t => !a t) (fun t => !b t) rst (fun t => !O t) (fun t => !qp t)
      dlmin dlmax dwmin dwmax := by
  have e : (fun t => exc INIT_c2 (!a t) (!b t) (!qp t) (rst t)) =
      (fun t => !(exc INIT_c2 (a t) (b t) (qp t) (rst t))) := by
    funext t; rw [hr t]; exact c2_dual _ _ _
  refine ⟨?_, winDelay_not L.H_FB, L.H_LOOP_POS⟩
  show WinDelay dlmin dlmax (fun t => exc INIT_c2 (!a t) (!b t) (!qp t) (rst t)) _
  rw [e]; exact winDelay_not L.H_LUT

theorem inertial_not {d : Nat} {x y : Trace} (H : Inertial d x y) :
    Inertial d (fun t => !x t) (fun t => !y t) := by
  intro t
  have h := H t
  simp only
  by_cases hc : ∀ k, k < d → x (t + k) = x t
  · have hc' : ∀ k, k < d → (!x (t + k)) = !x t := fun k hk => by rw [hc k hk]
    rw [h, ite_eq_left_of_eq_true _ _ (eq_true hc), ite_eq_left_of_eq_true _ _ (eq_true hc')]
  · have hc' : ¬ ∀ k, k < d → (!x (t + k)) = !x t := by
      intro h'; apply hc; intro k hk
      have := h' k hk
      cases h1 : x (t + k) <;> cases h2 : x t <;> simp_all
    rw [h, ite_eq_right_of_eq_false _ _ (eq_false hc), ite_eq_right_of_eq_false _ _ (eq_false hc')]

/-! ## 2. Cell level: `uxa = bd_c2 (a = j0, b = z_ack)` -/

section cell
variable {j0 za rst xa qp : Trace} {dlmin dlmax dwmin dwmax : Nat}

/-- **Sufficiency of H_RTZ.** Inputs as seen at uxa's pins.
* `H_NORST`: rst low on `[te, t2]`.
* `H_J0_LOW`: `j0` low on `[te, t2]` (x's join stays low: the new token
  selects y, H_BUNDLED_S keeps `s = 1`).
* `H_ZA_LOW`: `z_ack` low on `[te, tr)` (between the fall's arrival and the
  next rise's arrival at uxa).
* `H_NEXT`: `tr ≤ t2` (the next rise comes while j0 is still low).
* **`H_RTZ : te + (dlmax + dwmax) ≤ tr`**.
Then `x_ack` is low on `[te + dlmax, t2 + dlmin]` (and the feedback pin on
`[te + Dmax, t2 + Dmin]`): the fall completes and z_ack's re-rise is harmless. -/
theorem rtz_safe (L : Loop INIT_c2 j0 za rst xa qp dlmin dlmax dwmin dwmax)
    (te tr t2 : Nat)
    (H_NORST : ∀ s, te ≤ s → s ≤ t2 → rst s = false)
    (H_J0_LOW : ∀ s, te ≤ s → s ≤ t2 → j0 s = false)
    (H_ZA_LOW : ∀ s, te ≤ s → s < tr → za s = false)
    (H_NEXT : tr ≤ t2)
    (H_RTZ : te + (dlmax + dwmax) ≤ tr) :
    (∀ t, te + dlmax ≤ t → t ≤ t2 + dlmin → xa t = false) ∧
    (∀ t, te + (dlmax + dwmax) ≤ t → t ≤ t2 + (dlmin + dwmin) → qp t = false) :=
  c2_follow_hold L false te t2
    (fun s h1 h2 => ⟨H_J0_LOW s h1 (by omega), H_ZA_LOW s h1 (by omega), H_NORST s h1 (by omega)⟩)
    H_NORST (fun s h1 h2 => Or.inl (H_J0_LOW s h1 h2))

end cell

section counter
variable (dl dw w t0 : Nat)

/-- The counter-trace: `j0 = 0` throughout, `z_ack` low exactly on
`[t0, t0 + w)`, then high again (the next token's acknowledge). -/
def j0C : Trace := fun _ => false
def zaC : Trace := fun t => !(bR w t0 t)
def xaC : Trace := fun t => !(OR dl dw w t0 t)
def qpC : Trace := fun t => !(qpR dl dw w t0 t)

/-- The counter-trace satisfies every gate relation of uxa (fixed transport
delays `dl`, `dw`; the dual of `CElemTiming.runt_loop`). -/
theorem rtz_counter_loop (hw : w < dl + dw) (hpos : 0 < dl + dw) :
    Loop INIT_c2 j0C (zaC w t0) rstR (xaC dl dw w t0) (qpC dl dw w t0) dl dl dw dw :=
  loop_dual (runt_loop dl dw w t0 hw hpos) (fun _ => rfl)

/-- **Necessity (counter-trace).** If the low window of `z_ack` at uxa is
shorter than the loop delay (`0 < w < dl + dw`), then although after `t0 + w`
the pins are constant forever (`j0 = 0`, `z_ack = 1`, rst 0: x_ack should
have fallen), `x_ack` is 0 at `t0 + dl + D n` and back to 1 at
`t0 + dl + D n + w` for every `n`: it never settles low. -/
theorem rtz_counter (hw0 : 0 < w) (hw : w < dl + dw) :
    (∀ t, t0 + w ≤ t → j0C t = false ∧ zaC w t0 t = true ∧ rstR t = false) ∧
    (∀ n, xaC dl dw w t0 (t0 + dl + (dl + dw) * n) = false ∧
          xaC dl dw w t0 (t0 + dl + (dl + dw) * n + w) = true) ∧
    (∀ n, qpC dl dw w t0 (t0 + (dl + dw) * (n + 1)) = false ∧
          qpC dl dw w t0 (t0 + (dl + dw) * (n + 1) + w) = true) := by
  obtain ⟨h1, h2, h3⟩ := runt_oscillates dl dw w t0 hw0 hw
  refine ⟨fun t ht => ?_, fun n => ?_, fun n => ?_⟩
  · obtain ⟨_, hb, _⟩ := h1 t ht
    exact ⟨rfl, by simp [zaC, hb], rfl⟩
  · obtain ⟨a, b⟩ := h3 n; exact ⟨by simp [xaC, a], by simp [xaC, b]⟩
  · obtain ⟨a, b⟩ := h2 n; exact ⟨by simp [qpC, a], by simp [qpC, b]⟩

/-- Exactness for fixed delays, both directions in one statement:
`w ≥ dl + dw` gives the safe fall (from `rtz_safe`), `w < dl + dw` the
oscillation of `rtz_counter`. The safe half, for the transport channel. -/
theorem rtz_exact_safe {j0 za rst xa qp : Trace}
    (L : Loop INIT_c2 j0 za rst xa qp dl dl dw dw) (te t2 : Nat)
    (H_NORST : ∀ s, te ≤ s → s ≤ t2 → rst s = false)
    (H_J0_LOW : ∀ s, te ≤ s → s ≤ t2 → j0 s = false)
    (H_ZA_LOW : ∀ s, te ≤ s → s < te + w → za s = false)
    (H_NEXT : te + w ≤ t2) (hW : dl + dw ≤ w) :
    ∀ t, te + dl ≤ t → t ≤ t2 + dl → xa t = false :=
  (rtz_safe L te (te + w) t2 H_NORST H_J0_LOW H_ZA_LOW H_NEXT (by omega)).1

end counter

/-- **Inertial LUT: the fall is lost.** uxa with an inertial LUT of threshold
`dl` and a transport feedback wire; `j0 = 0`; `z_ack` low exactly on
`[t0, t0 + w)` with `w < dl`; x_ack high before (`xa = 1` on `[0, t0+dl)`,
`qp = 1` on `[0, dw)`). Then `x_ack` stays 1 forever: the cell re-latched the
old acknowledge into the next transaction (dual of `c2_inertial_runt_lost`). -/
theorem rtz_inertial_lost {dl dw w t0 : Nat} {za xa qp : Trace}
    (hw : w < dl)
    (Hza : ∀ t, za t = !decide (t0 ≤ t ∧ t < t0 + w))
    (H_LUT_INERTIAL : Inertial dl (excT INIT_c2 j0C za rstR qp) xa)
    (H_FB : Transport dw xa qp)
    (hO0 : ∀ t, t < t0 + dl → xa t = true)
    (hq0 : ∀ t, t < dw → qp t = true) :
    ∀ t, xa t = true ∧ qp t = true := by
  have e : excT INIT_c2 aR (fun t => !za t) rstR (fun t => !qp t) =
      (fun t => !(excT INIT_c2 j0C za rstR qp t)) := by
    funext t
    simp only [excT, aR, rstR, j0C]
    have := c2_dual false (za t) (qp t)
    simpa using this
  have H1 : Inertial dl (excT INIT_c2 aR (fun t => !za t) rstR (fun t => !qp t))
      (fun t => !xa t) := by
    rw [e]; exact inertial_not H_LUT_INERTIAL
  have H2 : Transport dw (fun t => !xa t) (fun t => !qp t) := by
    intro t; show (!qp (t + dw)) = !xa t; rw [H_FB t]
  have := c2_inertial_runt_lost (t0 := t0) (b := fun t => !za t) hw
    (fun t => by simp [Hza]) H1 H2
    (fun t ht => by simp [hO0 t ht]) (fun t ht => by simp [hq0 t ht])
  intro t
  obtain ⟨h1, h2⟩ := this t
  simp at h1 h2
  exact ⟨h1, h2⟩

/-! ## 3. Environment level: the window from the control token's round trip -/

/-- A wire or stateless LUT stage keeps a value `v` it saw for long enough. -/
theorem win_low {dmin dmax : Nat} {e y : Trace} {v : Bool} (H : WinDelay dmin dmax e y)
    (a b : Nat) (he : ∀ s, a ≤ s → s < b → e s = v) :
    ∀ t, a + dmax ≤ t → t < b + dmin → y t = v := by
  intro t h1 h2
  obtain ⟨s, ha, hb, e'⟩ := H t (by omega)
  rw [e']; exact he s (by omega) (by omega)

/-- **Min-delay causality of an environment stage** (event form, any gate):
while `x` holds `bx` on `[ti, T)`, `y` holds `bY` on `[to, T + d)`. This is
what a static timing checker's min path delay asserts. -/
def Causal (x y : Trace) (bx bY : Bool) (ti to d : Nat) : Prop :=
  ∀ T, (∀ s, ti ≤ s → s < T → x s = bx) → ∀ t, to ≤ t → t < T + d → y t = bY

/-- A feedback-LUT cell with an arbitrary next-state function `g t q` (pins
other than the feedback, at time `t`, are inside `g`). `CElemTiming.Loop` is
the instance `g t q = exc init (a t) (b t) q (rst t)` (`loop_floop`). -/
structure FLoop (g : Nat → Bool → Bool) (O qp : Trace) (dlmin dlmax dwmin dwmax : Nat) : Prop where
  /-- **H_LUT** as in `CElemTiming.Loop`. -/
  H_LUT : WinDelay dlmin dlmax (fun t => g t (qp t)) O
  /-- **H_FB** as in `CElemTiming.Loop`: the routed `O -> feedback pin` net. -/
  H_FB : WinDelay dwmin dwmax O qp
  /-- **H_LOOP_POS**. -/
  H_LOOP_POS : 0 < dlmin + dwmin

theorem loop_floop {init : Nat} {a b rst O qp : Trace} {dlmin dlmax dwmin dwmax : Nat}
    (L : Loop init a b rst O qp dlmin dlmax dwmin dwmax) :
    FLoop (fun t q => exc init (a t) (b t) q (rst t)) O qp dlmin dlmax dwmin dwmax :=
  ⟨L.H_LUT, L.H_FB, L.H_LOOP_POS⟩

/-- **A settled-low feedback cell whose enabling input is blocked stays low
until `dlmin` after the block ends** (proved from the gate relations, any
next-state function blocked by `x = bx` when fed back 0). -/
theorem floop_causal {g : Nat → Bool → Bool} {O qp x : Trace} {bx : Bool}
    {dlmin dlmax dwmin dwmax ti to : Nat}
    (L : FLoop g O qp dlmin dlmax dwmin dwmax)
    (hblk : ∀ t, ti ≤ t → x t = bx → g t false = false)
    (hti : ti ≤ to + dwmax)
    (hset : ∀ t, to ≤ t → t < to + (dwmax + dlmax) → O t = false) :
    Causal x O bx false ti to dlmin := by
  intro T hT t
  induction t using Nat.strongRecOn with
  | _ t ih =>
    intro h1 h2
    by_cases hlt : t < to + (dwmax + dlmax)
    · exact hset t h1 hlt
    · obtain ⟨s, ha, hb, e⟩ := L.H_LUT t (by omega)
      obtain ⟨s', ha', hb', e'⟩ := L.H_FB s (by omega)
      have hpos := L.H_LOOP_POS
      have hq : qp s = false := by rw [e']; exact ih s' (by omega) (by omega) (by omega)
      rw [e]; show g s (qp s) = false
      rw [hq]; exact hblk s (by omega) (hT s (by omega) (by omega))

/-- `bd_mux.uj1`'s REAL INIT (`cells/rtl/bd_mux.v`; same constant as
`LibCtlMergeMux.INIT_j1`), pins `I0 = y_req, I1 = ctl_req, I2 = s, I3 = j1`
(feedback), `I4 = rst`, `I5 = 0`. -/
def INIT_uj1 : Nat := 0x0000EA800000EA80

theorem INIT_uj1_lib : INIT_uj1 = LibCtlMergeMux.INIT_j1 := rfl

/-- The INIT is `~rst · maj(y_req, ctl_req·s, j1)` (32 rows). -/
theorem uj1_eq (y cr s q r : Bool) :
    lutB INIT_uj1 [y, cr, s, q, r, false] = (!r && ((y && (cr && s)) || (y && q) || ((cr && s) && q))) := by
  cases y <;> cases cr <;> cases s <;> cases q <;> cases r <;> decide

/-- `uj1` is blocked (stays 0 when fed back 0) while its `ctl_req` pin is low. -/
theorem uj1_blocked (y s r : Bool) : lutB INIT_uj1 [y, false, s, false, r, false] = false := by
  cases y <;> cases s <;> cases r <;> decide

/-- `bd_mux.uor`: LUT2 INIT `E`, `I0 = j0, I1 = j1`. -/
theorem uor_eq (a b : Bool) : lutB 0xE [a, b] = (a || b) := by
  cases a <;> cases b <;> decide

/-- **H_RTZ from the environment.** Signals (each as seen where stated):
`zs` z_ack at the server's output; `zc` at the control sender; `cr` ctl_req
at the sender; `crj` ctl_req at uj1's pin; `y, s, rst` uj1's other pins;
`j1`/`j1q` uj1's output / feedback pin; `j1o`, `j0o` the joins at uor's pins;
`ei` uor's output (`either`); `zr` z_req at the server's pin; `zx` z_ack at
uxa's pin; `j0x` j0 at uxa's pin; `xa`/`xq` uxa's output / feedback pin.

Named hypotheses:
* `H_W_ZC`, `H_W_CR`, `H_W_J1`, `H_W_ZX`: routed wires (window channels with
  min/max from the route's prjxray/SDF delays). `H_W_ZX` is the SAME wire for
  z_ack's fall and its next rise.
* `H_CTL` (environment: the control sender): while it sees `ctl_ack` high it
  keeps `ctl_req` low, and raises it no sooner than `dc` after `ctl_ack` falls
  at its pin (bd_link: one bd_c2n arc; derivable by `floop_causal`).
* `H_UJ1`: uj1 is a feedback LUT (REAL INIT) with delays `[dl1,Dl1]`,
  `[dw1,Dw1]`; `H_J1_SETTLED`: it has been low long enough (it did not fire
  in x's transaction).
* `H_UOR`: uor (REAL INIT) with delay `[dlo, Dlo]`; `H_J0_OR`: j0 is low at
  uor's pin on `[t0o, Tend)` (it fell before z_req fell).
* `H_DLY` (the matched delay line, rising edge): `z_req` at the server stays
  low until `dz` after `either` rises (N hops; FASTFALL lines are covered,
  only the rise matters).
* `H_SRV` (environment: the server): from `Tzf` its acknowledge is low, and it
  rises no sooner than `ds` after z_req rises at its pin.
* `H_ZA_HIGH`: z_ack at the server was high on `[tch, Tzf)` (x's transaction).
* start-time orderings `hs1..hs6` (each stage's window starts after the
  previous one's), and `hEnd` (j0 stays low at uor past the window).
* uxa: `L` its gate relations; `H_NORST`, `H_J0_LOW` on `[te, t2]`,
  `hte : Tzf + Wux ≤ te` (the fall has arrived), `H_NEXT`.
* **`H_RTZ_ENV : te + (dlmax + dwmax) ≤ Tzf + Lmin + wux`** with
  `Lmin = wzc + dc + wcr + dl1 + wjo + dlo + dz + ds`.
Conclusion: `x_ack` low on `[te + dlmax, t2 + dlmin]`. -/
theorem mux_rtz_env_safe
    {zs zc cr crj y s rst j1 j1q j1o j0o ei zr zx j0x rstx xa xq : Trace}
    {wzc Wzc dc tc0 tc1 wcr Wcr dl1 Dl1 dw1 Dw1 tj wjo Wjo dlo Dlo t0o Tend
     dz te0 te1 ds tz0 Tzf tch wux Wux dlmin dlmax dwmin dwmax te t2 : Nat}
    (H_W_ZC : WinDelay wzc Wzc zs zc)
    (H_CTL : Causal zc cr true false tc0 tc1 dc)
    (H_W_CR : WinDelay wcr Wcr cr crj)
    (H_UJ1 : FLoop (fun t q => lutB INIT_uj1 [y t, crj t, s t, q, rst t, false]) j1 j1q
      dl1 Dl1 dw1 Dw1)
    (H_J1_SETTLED : ∀ t, tj ≤ t → t < tj + (Dw1 + Dl1) → j1 t = false)
    (H_W_J1 : WinDelay wjo Wjo j1 j1o)
    (H_UOR : WinDelay dlo Dlo (fun t => lutB 0xE [j0o t, j1o t]) ei)
    (H_J0_OR : ∀ t, t0o ≤ t → t < Tend → j0o t = false)
    (H_DLY : Causal ei zr false false te0 te1 dz)
    (H_SRV : Causal zr zs false false tz0 Tzf ds)
    (H_ZA_HIGH : ∀ t, tch ≤ t → t < Tzf → zs t = true)
    (H_W_ZX : WinDelay wux Wux zs zx)
    (hs1 : tch + Wzc ≤ tc0) (hs2 : tc1 + Wcr ≤ tj + Dw1)
    (hs3 : t0o ≤ tj + Wjo) (hs4 : tj + Wjo + Dlo ≤ te0) (hs5 : te1 ≤ tz0)
    (hEnd : Tzf + wzc + dc + wcr + dl1 + wjo ≤ Tend)
    (L : Loop INIT_c2 j0x zx rstx xa xq dlmin dlmax dwmin dwmax)
    (H_NORST : ∀ u, te ≤ u → u ≤ t2 → rstx u = false)
    (H_J0_LOW : ∀ u, te ≤ u → u ≤ t2 → j0x u = false)
    (hte : Tzf + Wux ≤ te)
    (H_NEXT : Tzf + (wzc + dc + wcr + dl1 + wjo + dlo + dz + ds) + wux ≤ t2)
    (H_RTZ_ENV : te + (dlmax + dwmax) ≤ Tzf + (wzc + dc + wcr + dl1 + wjo + dlo + dz + ds) + wux) :
    ∀ t, te + dlmax ≤ t → t ≤ t2 + dlmin → xa t = false := by
  -- 1. the control sender sees z_ack high until Tzf + wzc
  have c1 := win_low H_W_ZC tch Tzf H_ZA_HIGH
  -- 2. ctl_req stays low until Tzf + wzc + dc
  have c2 := H_CTL (Tzf + wzc) (fun u h1 h2 => c1 u (by omega) h2)
  -- 3. at uj1's pin
  have c3 := win_low H_W_CR tc1 (Tzf + wzc + dc) (fun u h1 h2 => c2 u h1 h2)
  -- 4. j1 stays low
  have c4 := floop_causal (x := crj) (bx := false) (ti := tc1 + Wcr) H_UJ1
    (fun t _ hx => by simp only [hx]; exact uj1_blocked _ _ _) hs2 H_J1_SETTLED
    (Tzf + wzc + dc + wcr) (fun u h1 h2 => c3 u h1 h2)
  -- 5. at uor's pin
  have c5 := win_low H_W_J1 tj (Tzf + wzc + dc + wcr + dl1) (fun u h1 h2 => c4 u h1 h2)
  -- 6. either stays low
  have c6 := win_low H_UOR (tj + Wjo) (Tzf + wzc + dc + wcr + dl1 + wjo) (v := false)
    (fun u h1 h2 => by
      show lutB 0xE [j0o u, j1o u] = false
      rw [uor_eq, H_J0_OR u (by omega) (by omega), c5 u h1 h2]; rfl)
  -- 7. z_req at the server
  have c7 := H_DLY (Tzf + wzc + dc + wcr + dl1 + wjo + dlo) (fun u h1 h2 => c6 u (by omega) h2)
  -- 8. the server's acknowledge stays low
  have c8 := H_SRV (Tzf + wzc + dc + wcr + dl1 + wjo + dlo + dz) (fun u h1 h2 => c7 u (by omega) h2)
  -- 9. at uxa's pin: low on [Tzf + Wux, Tzf + Lmin + wux)
  have c9 := win_low H_W_ZX Tzf (Tzf + wzc + dc + wcr + dl1 + wjo + dlo + dz + ds)
    (fun u h1 h2 => c8 u h1 h2)
  exact (rtz_safe L te (Tzf + (wzc + dc + wcr + dl1 + wjo + dlo + dz + ds) + wux) t2
    H_NORST H_J0_LOW (fun u h1 h2 => c9 u (by omega) (by omega)) H_NEXT H_RTZ_ENV).1

/-! ## 4. bd_merge: the analogous race reduces to the generic C-element latency -/

/-- In `bd_merge` (`x_ack = C(x_req, z_ack)`), under H_MERGE_SEQ a new request
(y's, or x's own next one) is raised only after `x_ack` was SEEN low; so the
next `z_ack` rise at uxa (`tr`) comes at least `E` after some instant `u ≥ te`
with `x_ack u = 0` (`H_CAUSAL`). `x_ack` cannot be low before `te + dlmin`
(`H_PREV_HIGH`, it was high: CElemTiming's `R k`). With CElemTiming's
`H_ENV_LATENCY` this gives H_RTZ, so `rtz_safe` applies: no mux-like race,
only the generic C-element condition. -/
theorem merge_rtz_of_latency {xa : Trace} {te tr E dlmin dlmax dwmax : Nat}
    (H_PREV_HIGH : ∀ u, te ≤ u → u < te + dlmin → xa u = true)
    (H_CAUSAL : ∃ u, te ≤ u ∧ u + E ≤ tr ∧ xa u = false)
    (H_ENV_LATENCY : dlmax + dwmax ≤ dlmin + E) :
    te + (dlmax + dwmax) ≤ tr := by
  obtain ⟨u, h1, h2, h3⟩ := H_CAUSAL
  have : te + dlmin ≤ u := by
    apply Classical.byContradiction; intro h
    have := H_PREV_HIGH u h1 (by omega); rw [h3] at this; cases this
  omega

/-! ## 5. Numbers at consistent corners (bdc configuration)

bdc: the select comes from a `bd_link` (rule 1 puts storage on every data
operand of a mux; the select is 1 bit wide), the server is the consumer's
`bd_link` node (or something slower). Minimum loop: ctl node (bd_c2n),
uj1, uor, `N` delay LUT1s, server node: `N + 4` LUT O6 arcs and `N + 4`
inter-LUT hops (za->ctl, ctl->uj1, uj1->uor, uor->dly1 .. dlyN->server). The
z_ack->uxa wire appears on both sides; at one corner with rise = fall
(H_RF_ASYM symmetric) it cancels. uxa side: one O6 arc + its own feedback hop.

`Lmin N arc hop = (N+4)*(arc + hop)`, `Dmax arc fb = arc + fb`. Guarded (as
`cells/verify/skew.py`): `GUARD_HI * Dmax ≤ GUARD_LO * Lmin`, i.e.
`1155 * Dmax ≤ 772 * Lmin` in thousandths. -/

def Lmin (N arc hop : Nat) : Nat := (N + 4) * (arc + hop)
def Dmx (arc fb : Nat) : Nat := arc + fb
def guarded (L D : Nat) : Prop := 1155 * D ≤ 772 * L

instance (L D : Nat) : Decidable (guarded L D) := by unfold guarded; infer_instance

/-- SLOW corner (SLOW_MIN 100 on the loop, SLOW_MAX 124 on uxa; hops 434 min,
feedback 945 max, the build's range): even `N = 0` passes guarded, margin
`2136 - 1069 = 1067` ps raw. -/
theorem slow_N0 : Lmin 0 100 434 = 2136 ∧ Dmx 124 945 = 1069 ∧ guarded (Lmin 0 100 434) (Dmx 124 945) := by
  decide

/-- FAST corner, adversarial wire ratios (loop hops at p10 0.37: 434 -> 161;
uxa feedback at p90 0.82: 945 -> 775; FAST_MIN 45 loop, FAST_MAX 56 uxa):
`N = 0` FAILS even raw (824 < 831): the counter-trace regime is reachable in
this estimate. -/
theorem fast_adv_N0_fails : Lmin 0 45 161 = 824 ∧ Dmx 56 775 = 831 ∧ Lmin 0 45 161 < Dmx 56 775 := by
  decide

/-- Same corner: guarded needs `N ≥ 3` (N = 2 fails, N = 3 passes). -/
theorem fast_adv_N : ¬ guarded (Lmin 2 45 161) (Dmx 56 775) ∧ guarded (Lmin 3 45 161) (Dmx 56 775) := by
  decide

/-- FAST corner, median wire ratio 0.55 (434 -> 239, 945 -> 520): `N = 0`
passes guarded. -/
theorem fast_med_N0 : guarded (Lmin 0 45 239) (Dmx 56 520) := by decide

end Formal.Cells.MuxRtzTimed
