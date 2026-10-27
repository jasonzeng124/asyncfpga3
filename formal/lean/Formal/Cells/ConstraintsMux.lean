import Formal.Cells.MuxRtzTimed
import Formal.Cells.Bundling

/-!
# Probe P3d: `bd_mux.uya` return-to-zero race (cell_constraints entry `bd_mux.uya_rtz_env`)

`MuxRtzTimed.mux_rtz_env_safe` proves H_RTZ_ENV for `uxa = bd_c2(j0, z_ack)`:
after x's transaction a control token selecting y re-raises `z_ack` through
`uj1`. The mirror race on `uya = bd_c2(j1, z_ack)` (after y's transaction, a
token selecting x re-raises `z_ack` through `uj0`) was only claimed by
symmetry. This file proves it with `uj0`'s REAL INIT `64'h0000_AE08_0000_AE08`
(pins `I0=x_req I1=ctl_req I2=s I3=j0 I4=rst I5=0`, cells/rtl/bd_mux.v) and
`uor`'s `4'hE` with the roles of its two pins swapped (`j1` now the quiet
input on I1). The cell-level theorem (`rtz_safe`) and the counter-trace
(`rtz_counter`, exactness for fixed delays) are about a generic `bd_c2` loop
and apply verbatim to `uya` (it is the same cell with `a = j1`).

Core Lean only.
-/

namespace Formal.Cells.ConstraintsMux
open Formal.Cells
open Formal.Cells.CElemTiming
open Formal.Cells.MuxRtzTimed

/-- `bd_mux.uj0`'s REAL INIT (same constant as `LibCtlMergeMux.INIT_j0`). -/
def INIT_uj0 : Nat := 0x0000AE080000AE08

theorem INIT_uj0_lib : INIT_uj0 = LibCtlMergeMux.INIT_j0 := rfl

/-- The INIT is `~rst · maj(x_req, ctl_req·~s, j0)` (32 rows). -/
theorem uj0_eq (x cr s q r : Bool) :
    lutB INIT_uj0 [x, cr, s, q, r, false] =
      (!r && ((x && (cr && !s)) || (x && q) || ((cr && !s) && q))) := by
  cases x <;> cases cr <;> cases s <;> cases q <;> cases r <;> decide

/-- `uj0` is blocked (stays 0 when fed back 0) while its `ctl_req` pin is low. -/
theorem uj0_blocked (x s r : Bool) : lutB INIT_uj0 [x, false, s, false, r, false] = false := by
  cases x <;> cases s <;> cases r <;> decide

/-- **H_RTZ from the environment, `uya` (mirror of `mux_rtz_env_safe`).**
Signals: `zs` z_ack at the server; `zc` at the control sender; `cr` ctl_req
at the sender; `crj` ctl_req at uj0's pin; `x, s, rst` uj0's other pins;
`j0`/`j0q` uj0's output / feedback pin; `j0o`, `j1o` the joins at uor's pins;
`ei` uor's output; `zr` z_req at the server's pin; `zy` z_ack at uya's pin;
`j1y` j1 at uya's pin; `ya`/`yq` uya's output / feedback pin.

Named hypotheses, as in the uxa theorem with x and y swapped:
* `H_W_ZC`, `H_W_CR`, `H_W_J0`, `H_W_ZY`: routed wires (window channels).
  `H_W_ZY` is the SAME wire for z_ack's fall and its next rise.
* `H_CTL`: the control sender keeps ctl_req low while it sees ctl_ack high
  and raises it no sooner than `dc` after ctl_ack falls at its pin.
* `H_UJ0`: uj0 is a feedback LUT with the REAL INIT; `H_J0_SETTLED`: it has
  been low long enough (it did not fire in y's transaction).
* `H_UOR`: uor (REAL INIT `4'hE`); `H_J1_OR`: j1 is low at uor's I1 pin on
  `[t1o, Tend)` (it fell before z_req fell).
* `H_DLY`, `H_SRV`, `H_ZA_HIGH`: delay line rise, server, y's transaction.
* start-time orderings `hs1..hs5`, `hEnd`.
* uya: `L` its gate relations; `H_NORST`, `H_J1_LOW` on `[te, t2]`,
  `hte : Tzf + Wuy ≤ te`, `H_NEXT`.
* **`H_RTZ_ENV : te + (dlmax + dwmax) ≤ Tzf + Lmin + wuy`** with
  `Lmin = wzc + dc + wcr + dl0 + wjo + dlo + dz + ds` (all MIN delays).
Conclusion: `y_ack` low on `[te + dlmax, t2 + dlmin]`. -/
theorem mux_rtz_env_safe_uya
    {zs zc cr crj x s rst j0 j0q j0o j1o ei zr zy j1y rsty ya yq : Trace}
    {wzc Wzc dc tc0 tc1 wcr Wcr dl0 Dl0 dw0 Dw0 tj wjo Wjo dlo Dlo t1o Tend
     dz te0 te1 ds tz0 Tzf tch wuy Wuy dlmin dlmax dwmin dwmax te t2 : Nat}
    (H_W_ZC : WinDelay wzc Wzc zs zc)
    (H_CTL : Causal zc cr true false tc0 tc1 dc)
    (H_W_CR : WinDelay wcr Wcr cr crj)
    (H_UJ0 : FLoop (fun t q => lutB INIT_uj0 [x t, crj t, s t, q, rst t, false]) j0 j0q
      dl0 Dl0 dw0 Dw0)
    (H_J0_SETTLED : ∀ t, tj ≤ t → t < tj + (Dw0 + Dl0) → j0 t = false)
    (H_W_J0 : WinDelay wjo Wjo j0 j0o)
    (H_UOR : WinDelay dlo Dlo (fun t => lutB 0xE [j0o t, j1o t]) ei)
    (H_J1_OR : ∀ t, t1o ≤ t → t < Tend → j1o t = false)
    (H_DLY : Causal ei zr false false te0 te1 dz)
    (H_SRV : Causal zr zs false false tz0 Tzf ds)
    (H_ZA_HIGH : ∀ t, tch ≤ t → t < Tzf → zs t = true)
    (H_W_ZY : WinDelay wuy Wuy zs zy)
    (hs1 : tch + Wzc ≤ tc0) (hs2 : tc1 + Wcr ≤ tj + Dw0)
    (hs3 : t1o ≤ tj + Wjo) (hs4 : tj + Wjo + Dlo ≤ te0) (hs5 : te1 ≤ tz0)
    (hEnd : Tzf + wzc + dc + wcr + dl0 + wjo ≤ Tend)
    (L : Loop INIT_c2 j1y zy rsty ya yq dlmin dlmax dwmin dwmax)
    (H_NORST : ∀ u, te ≤ u → u ≤ t2 → rsty u = false)
    (H_J1_LOW : ∀ u, te ≤ u → u ≤ t2 → j1y u = false)
    (hte : Tzf + Wuy ≤ te)
    (H_NEXT : Tzf + (wzc + dc + wcr + dl0 + wjo + dlo + dz + ds) + wuy ≤ t2)
    (H_RTZ_ENV : te + (dlmax + dwmax) ≤ Tzf + (wzc + dc + wcr + dl0 + wjo + dlo + dz + ds) + wuy) :
    ∀ t, te + dlmax ≤ t → t ≤ t2 + dlmin → ya t = false := by
  have c1 := win_low H_W_ZC tch Tzf H_ZA_HIGH
  have c2 := H_CTL (Tzf + wzc) (fun u h1 h2 => c1 u (by omega) h2)
  have c3 := win_low H_W_CR tc1 (Tzf + wzc + dc) (fun u h1 h2 => c2 u h1 h2)
  have c4 := floop_causal (x := crj) (bx := false) (ti := tc1 + Wcr) H_UJ0
    (fun t _ hx => by simp only [hx]; exact uj0_blocked _ _ _) hs2 H_J0_SETTLED
    (Tzf + wzc + dc + wcr) (fun u h1 h2 => c3 u h1 h2)
  have c5 := win_low H_W_J0 tj (Tzf + wzc + dc + wcr + dl0) (fun u h1 h2 => c4 u h1 h2)
  have c6 := win_low H_UOR (tj + Wjo) (Tzf + wzc + dc + wcr + dl0 + wjo) (v := false)
    (fun u h1 h2 => by
      show lutB 0xE [j0o u, j1o u] = false
      rw [uor_eq, H_J1_OR u (by omega) (by omega), c5 u h1 h2]; rfl)
  have c7 := H_DLY (Tzf + wzc + dc + wcr + dl0 + wjo + dlo) (fun u h1 h2 => c6 u (by omega) h2)
  have c8 := H_SRV (Tzf + wzc + dc + wcr + dl0 + wjo + dlo + dz) (fun u h1 h2 => c7 u (by omega) h2)
  have c9 := win_low H_W_ZY Tzf (Tzf + wzc + dc + wcr + dl0 + wjo + dlo + dz + ds)
    (fun u h1 h2 => c8 u h1 h2)
  exact (rtz_safe L te (Tzf + (wzc + dc + wcr + dl0 + wjo + dlo + dz + ds) + wuy) t2
    H_NORST H_J1_LOW (fun u h1 h2 => c9 u (by omega) (by omega)) H_NEXT H_RTZ_ENV).1

/-! Exactness at the cell: `MuxRtzTimed.rtz_counter` / `rtz_inertial_lost` are
stated for a generic `bd_c2` loop whose `a` input is held at 0; with `a = j1`
they are runs of `uya` verbatim, so the cell-level inequality is exact for
fixed delays for uya as for uxa. -/


/-! ## H_BUNDLED_S_PIN as a timed statement at the join pins
(cell_constraints entries `bd_mux.bundled_s_setup`, `bd_mux.bundled_s_hold`)

Bundling's window model (`Gate`, Kleene closure of the REAL INIT,
H_KLEENE_LUT) applied to the joins `uj0`/`uj1` (pins `I0 req, I1 ctl_req,
I2 s, I3 own output (feedback), I4 rst, I5 0`).

* `j1_sel_is_c2`, `j0_sel_is_c2`: whenever `s` reads definitely at the
  selecting value at the join's I2 select, the join's gate relation IS
  `bd_c2`'s on `(req, ctl_req)` (81 Kleene rows each): every C-element result
  (CElemTiming, ConstraintsSel) applies to the selected join.
* `j0_unsel_low`, `j1_unsel_low`: the UNSELECTED join stays low through the
  whole control phase if at every instant either `s` reads definitely at the
  other value or `ctl_req` reads definitely low (Kleene rows).
* `unsel_low_timed`: the timed form: `s` stable at its driver on `[Ts, Ts']`,
  `ctl_req` high on `[Tc, Tcf)`, low on `[C0, Tc)` and `[Tcf, Tc2)`.
  **H_BUNDLED_S_SETUP_T** `Ts + shi ≤ Tc + clo` (s settled at the select
  before the earliest ctl_req rise arrives) and **H_BUNDLED_S_HOLD_T**
  `Tcf + chi ≤ Ts' + slo` (s held until the latest ctl_req fall has arrived)
  keep the unselected join low on the whole window, given it started low
  for one loop window.
* `j0_s_x_hazard`: necessity at the select: with `x_req` and `ctl_req` high
  and `s` mid-edge (`x`) the unselected join's closure is `x` (a runt can be
  launched on the wrong join), the timed counterpart of
  `MergeMuxSI.mux_needs_bundled_s_hazard`.
-/

section joins
open Formal.Cells.Bundling

/-- `uj1` with `s = 1` at its select is `bd_c2(y_req, ctl_req)`, Kleene, all rows. -/
theorem j1_sel_is_c2 : ∀ y cr q r : K3,
    lutK INIT_uj1 [y, cr, .t, q, r, .f] = lutK INIT_c2 [y, cr, q, r, .f, .f] := by decide

/-- `uj0` with `s = 0` at its select is `bd_c2(x_req, ctl_req)`. -/
theorem j0_sel_is_c2 : ∀ xr cr q r : K3,
    lutK INIT_uj0 [xr, cr, .f, q, r, .f] = lutK INIT_c2 [xr, cr, q, r, .f, .f] := by decide

/-- `uj0` with `s = 1` (y selected) and its own feedback low stays low,
whatever `x_req`, `ctl_req` and `rst` read (even `x`). -/
theorem j0_unsel_s : ∀ xr cr r : K3, lutK INIT_uj0 [xr, cr, .t, .f, r, .f] = .f := by decide
/-- … and with `ctl_req` low it stays low whatever `s` reads. -/
theorem j0_unsel_cr : ∀ xr s r : K3, lutK INIT_uj0 [xr, .f, s, .f, r, .f] = .f := by decide
theorem j1_unsel_s : ∀ y cr r : K3, lutK INIT_uj1 [y, cr, .f, .f, r, .f] = .f := by decide
theorem j1_unsel_cr : ∀ y s r : K3, lutK INIT_uj1 [y, .f, s, .f, r, .f] = .f := by decide

/-- **Necessity at the select**: `s` mid-edge while `x_req` and `ctl_req` are
high and the join is low: the closure is `x` (a runt may launch). -/
theorem j0_s_x_hazard : lutK INIT_uj0 [.t, .t, .x, .f, .f, .f] = .x ∧
    lutK INIT_uj1 [.t, .t, .x, .f, .f, .f] = .x := by decide

/-- The join gate: pins `(req, ctl_req, s, own output, rst, 0)` with windows. -/
abbrev JoinGate (init : Nat) (rq cr s j rst : Sig)
    (rlo rhi clo chi slo shi flo fhi tlo thi : Nat) : Prop :=
  Gate init [(rq, rlo, rhi), (cr, clo, chi), (s, slo, shi), (j, flo, fhi), (rst, tlo, thi),
    (zero, 0, 0)] j

/-- **The unselected join stays low** (generic in which join, via `hU`):
while at every instant of `[A, B)` either `s` reads definitely `sv` (the
value that deselects this join) or `ctl_req` reads definitely low, and the
join was low on `[P, A)` with `P + fhi ≤ A` (one loop window), the join is
low on `[P, B)`. `H_LOOP_POS : 1 ≤ flo`. -/
theorem unsel_low {init : Nat} {sv : K3}
    (hU : ∀ rq cr r : K3, lutK init [rq, cr, sv, .f, r, .f] = .f)
    (hC : ∀ rq s r : K3, lutK init [rq, .f, s, .f, r, .f] = .f)
    {rq cr s j rst : Sig} {rlo rhi clo chi slo shi flo fhi tlo thi : Nat}
    (hg : JoinGate init rq cr s j rst rlo rhi clo chi slo shi flo fhi tlo thi)
    (hfw : flo ≤ fhi) (H_LOOP_POS : 1 ≤ flo) (P A B : Nat) (hPA : P + fhi ≤ A)
    (h_init : ∀ t, P ≤ t → t < A → j t = false)
    (H_SEL : ∀ t, A ≤ t → t < B → winK s slo shi t = sv ∨ winK cr clo chi t = .f) :
    ∀ t, P ≤ t → t < B → j t = false := by
  suffices H : ∀ n, ∀ t, t < n → P ≤ t → t < B → j t = false
    from fun t h1 h2 => H (t + 1) t (Nat.lt_succ_self t) h1 h2
  intro n
  induction n with
  | zero => intro t h; omega
  | succ n ih =>
    intro t htn h1 h2
    by_cases hA : t < A
    · exact h_init t h1 hA
    · have hq : winK j flo fhi t = .f :=
        win_eq (b := false) hfw (fun u hu1 hu2 => ih u (by omega) (by omega) (by omega))
      apply hg t false
      show lutK init [winK rq rlo rhi t, winK cr clo chi t, winK s slo shi t, winK j flo fhi t,
        winK rst tlo thi t, winK zero 0 0 t] = _
      rw [winK_zero, hq]
      rcases H_SEL t (by omega) h2 with hs | hc
      · rw [hs]; exact hU _ _ _
      · rw [hc]; exact hC _ _ _

/-- **H_BUNDLED_S_PIN, timed (setup and hold halves), at the unselected
join.** `s` at `sb` (the deselecting value) at its driver on `[Ts, Ts']`;
`ctl_req` low on `[C0, Tc)`, high on `[Tc, Tcf)`, low on `[Tcf, Tc2)`.
* **H_BUNDLED_S_SETUP_T** `Ts + shi ≤ Tc + clo`;
* **H_BUNDLED_S_HOLD_T** `Tcf + chi ≤ Ts' + slo`;
* `hA1 : C0 + chi ≤ A`: ctl_req's low phase covers the start of the window
  (only instants where ctl_req can read non-low need `s`).
Then the unselected join is low until `Tc2 + clo` (the next ctl_req rise). -/
theorem unsel_low_timed {init : Nat} (sb : Bool)
    (hU : ∀ rq cr r : K3, lutK init [rq, cr, K3.ofBool sb, .f, r, .f] = .f)
    (hC : ∀ rq s r : K3, lutK init [rq, .f, s, .f, r, .f] = .f)
    {rq cr s j rst : Sig} {rlo rhi clo chi slo shi flo fhi tlo thi : Nat}
    (hg : JoinGate init rq cr s j rst rlo rhi clo chi slo shi flo fhi tlo thi)
    (hcw : clo ≤ chi) (hsw : slo ≤ shi) (hfw : flo ≤ fhi) (H_LOOP_POS : 1 ≤ flo)
    (Ts Ts' C0 Tc Tcf Tc2 P A : Nat)
    (h_s : ∀ t, Ts ≤ t → t ≤ Ts' → s t = sb)
    (h_c0 : ∀ t, C0 ≤ t → t < Tc → cr t = false)
    (h_c1 : ∀ t, Tcf ≤ t → t < Tc2 → cr t = false)
    (hPA : P + fhi ≤ A) (hA1 : C0 + chi ≤ A)
    (h_init : ∀ t, P ≤ t → t < A → j t = false)
    (H_BUNDLED_S_SETUP_T : Ts + shi ≤ Tc + clo)
    (H_BUNDLED_S_HOLD_T : Tcf + chi ≤ Ts' + slo) :
    ∀ t, P ≤ t → t < Tc2 + clo → j t = false := by
  apply unsel_low hU hC hg hfw H_LOOP_POS P A (Tc2 + clo) hPA h_init
  intro t h1 h2
  by_cases hx : t < Tc + clo
  · exact Or.inr (win_eq (b := false) hcw (fun u hu1 hu2 => h_c0 u (by omega) (by omega)))
  · by_cases hy : t < Tcf + chi
    · exact Or.inl (win_eq hsw (fun u hu1 hu2 => h_s u (by omega) (by omega)))
    · exact Or.inr (win_eq (b := false) hcw (fun u hu1 hu2 => h_c1 u (by omega) (by omega)))

/-- Instances: `uj0` deselected by `s = 1`, `uj1` by `s = 0`. -/
theorem uj0_unsel_low_timed {rq cr s j rst : Sig} {rlo rhi clo chi slo shi flo fhi tlo thi : Nat}
    (hg : JoinGate INIT_uj0 rq cr s j rst rlo rhi clo chi slo shi flo fhi tlo thi)
    (hcw : clo ≤ chi) (hsw : slo ≤ shi) (hfw : flo ≤ fhi) (H_LOOP_POS : 1 ≤ flo)
    (Ts Ts' C0 Tc Tcf Tc2 P A : Nat)
    (h_s : ∀ t, Ts ≤ t → t ≤ Ts' → s t = true)
    (h_c0 : ∀ t, C0 ≤ t → t < Tc → cr t = false)
    (h_c1 : ∀ t, Tcf ≤ t → t < Tc2 → cr t = false)
    (hPA : P + fhi ≤ A) (hA1 : C0 + chi ≤ A)
    (h_init : ∀ t, P ≤ t → t < A → j t = false)
    (H_BUNDLED_S_SETUP_T : Ts + shi ≤ Tc + clo)
    (H_BUNDLED_S_HOLD_T : Tcf + chi ≤ Ts' + slo) :
    ∀ t, P ≤ t → t < Tc2 + clo → j t = false :=
  unsel_low_timed true j0_unsel_s j0_unsel_cr hg hcw hsw hfw H_LOOP_POS Ts Ts' C0 Tc Tcf Tc2 P A
    h_s h_c0 h_c1 hPA hA1 h_init H_BUNDLED_S_SETUP_T H_BUNDLED_S_HOLD_T

theorem uj1_unsel_low_timed {rq cr s j rst : Sig} {rlo rhi clo chi slo shi flo fhi tlo thi : Nat}
    (hg : JoinGate INIT_uj1 rq cr s j rst rlo rhi clo chi slo shi flo fhi tlo thi)
    (hcw : clo ≤ chi) (hsw : slo ≤ shi) (hfw : flo ≤ fhi) (H_LOOP_POS : 1 ≤ flo)
    (Ts Ts' C0 Tc Tcf Tc2 P A : Nat)
    (h_s : ∀ t, Ts ≤ t → t ≤ Ts' → s t = false)
    (h_c0 : ∀ t, C0 ≤ t → t < Tc → cr t = false)
    (h_c1 : ∀ t, Tcf ≤ t → t < Tc2 → cr t = false)
    (hPA : P + fhi ≤ A) (hA1 : C0 + chi ≤ A)
    (h_init : ∀ t, P ≤ t → t < A → j t = false)
    (H_BUNDLED_S_SETUP_T : Ts + shi ≤ Tc + clo)
    (H_BUNDLED_S_HOLD_T : Tcf + chi ≤ Ts' + slo) :
    ∀ t, P ≤ t → t < Tc2 + clo → j t = false :=
  unsel_low_timed false j1_unsel_s j1_unsel_cr hg hcw hsw hfw H_LOOP_POS Ts Ts' C0 Tc Tcf Tc2 P A
    h_s h_c0 h_c1 hPA hA1 h_init H_BUNDLED_S_SETUP_T H_BUNDLED_S_HOLD_T

/-- **The selected join is `bd_c2` at the window level** while `s` reads
definitely selecting at its pin: any value the `bd_c2` closure over the same
`(req, ctl_req, own output, rst)` windows makes definite, the join outputs. -/
theorem uj1_selected_c2 {rq cr s j rst : Sig} {rlo rhi clo chi slo shi flo fhi tlo thi : Nat}
    (hg : JoinGate INIT_uj1 rq cr s j rst rlo rhi clo chi slo shi flo fhi tlo thi)
    (t : Nat) (hs : winK s slo shi t = .t) (b : Bool)
    (h : lutK INIT_c2 [winK rq rlo rhi t, winK cr clo chi t, winK j flo fhi t,
      winK rst tlo thi t, .f, .f] = K3.ofBool b) : j t = b := by
  apply hg t b
  show lutK INIT_uj1 [winK rq rlo rhi t, winK cr clo chi t, winK s slo shi t, winK j flo fhi t,
    winK rst tlo thi t, winK zero 0 0 t] = _
  rw [winK_zero, hs, j1_sel_is_c2]; exact h

theorem uj0_selected_c2 {rq cr s j rst : Sig} {rlo rhi clo chi slo shi flo fhi tlo thi : Nat}
    (hg : JoinGate INIT_uj0 rq cr s j rst rlo rhi clo chi slo shi flo fhi tlo thi)
    (t : Nat) (hs : winK s slo shi t = .f) (b : Bool)
    (h : lutK INIT_c2 [winK rq rlo rhi t, winK cr clo chi t, winK j flo fhi t,
      winK rst tlo thi t, .f, .f] = K3.ofBool b) : j t = b := by
  apply hg t b
  show lutK INIT_uj0 [winK rq rlo rhi t, winK cr clo chi t, winK s slo shi t, winK j flo fhi t,
    winK rst tlo thi t, winK zero 0 0 t] = _
  rw [winK_zero, hs, j0_sel_is_c2]; exact h

end joins

/-! ## H_BUNDLED_Z as a timed statement (`bd_mux.bundled_z`, `bd_merge.bundled_z`)

`bd_datamux` (cells/rtl/bd_latch.v): odd bit `LUT3 8'hE4` (`I0 s, I1 a,
I2 b`), pair `LUT6_2 64'hFFAA_5500_E4E4_E4E4` (`I0 s, I1 a0, I2 b0, I3 a1,
I4 b1, I5 1`; O5 = bit 0, O6 = bit 1); `z = s ? b : a`. `bd_merge.usel` is
`LUT2 4'hE` (`sel = x_req | x_ack`). Results:
* `dm_odd_kleene`, `dm_pair_o5_kleene`, `dm_pair_o6_kleene`: each output is
  the Kleene mux `s ? b : a` of its own bit's pins, for ALL Kleene inputs
  (the other bit of a pair never reaches it).
* `dm_settles`: with `s` stable at its pin and the selected input stable,
  `z` is the selected value from `max (Ts + shi) (Td + dhi)`.
* `usel_settles`: the merge's select is settled `1` from `Txr + hi` while
  `x_req` is high, and `0` while both `x_req` and `x_ack` are low.
* `bundled_z_capture`: the consumer latch bit captures the selected value
  under the CLASSIC bundling form at the consumer's pins (rule A's form:
  data settled through the select cone and the datamux, plus the route to the
  bit, no later than the enable rise) plus the enable pulse condition and
  H_HOLD. Sufficient; not necessary (`Bundling.setup_not_classic`: the exact
  condition is H_SETUP against the enable FALL).
-/

section bundledZ
open Formal.Cells.Bundling

def DM_ODD : Nat := 0xE4
def DM_PAIR : Nat := 0xFFAA5500E4E4E4E4

theorem dm_odd_kleene : ∀ s a b : K3, lutK DM_ODD [s, a, b] = K3.mux s a b := by decide
theorem dm_pair_o5_kleene : ∀ s a0 b0 a1 b1 : K3,
    o5K DM_PAIR [s, a0, b0, a1, b1, .t] = K3.mux s a0 b0 := by decide
theorem dm_pair_o6_kleene : ∀ s a0 b0 a1 b1 : K3,
    o6K DM_PAIR [s, a0, b0, a1, b1, .t] = K3.mux s a1 b1 := by decide
theorem usel_kleene : ∀ a b : K3, lutK 0xE [a, b] = (if a = .t ∨ b = .t then .t
    else if a = .f ∧ b = .f then .f else .x) := by decide

/-- The datamux relation of one output bit: Kleene mux over the windows. -/
def DmRel (s a b z : Sig) (slo shi alo ahi blo bhi : Nat) : Prop :=
  ∀ t v, K3.mux (winK s slo shi t) (winK a alo ahi t) (winK b blo bhi t) = K3.ofBool v → z t = v

theorem dm_odd_rel {s a b z : Sig} {slo shi alo ahi blo bhi : Nat}
    (hg : Gate DM_ODD [(s, slo, shi), (a, alo, ahi), (b, blo, bhi)] z) :
    DmRel s a b z slo shi alo ahi blo bhi := by
  intro t v h; apply hg t v
  show lutK DM_ODD [winK s slo shi t, winK a alo ahi t, winK b blo bhi t] = _
  rw [dm_odd_kleene]; exact h

theorem dm_pair_o5_rel {s a0 b0 a1 b1 z : Sig} {slo shi alo ahi blo bhi l3 h3 l4 h4 : Nat}
    (hg : Gate (DM_PAIR % 2 ^ 32) [(s, slo, shi), (a0, alo, ahi), (b0, blo, bhi),
      (a1, l3, h3), (b1, l4, h4)] z) :
    DmRel s a0 b0 z slo shi alo ahi blo bhi := by
  intro t v h; apply hg t v
  show lutK (DM_PAIR % 2 ^ 32) [winK s slo shi t, winK a0 alo ahi t, winK b0 blo bhi t,
    winK a1 l3 h3 t, winK b1 l4 h4 t] = _
  have := dm_pair_o5_kleene (winK s slo shi t) (winK a0 alo ahi t) (winK b0 blo bhi t)
    (winK a1 l3 h3 t) (winK b1 l4 h4 t)
  simp only [o5K, List.take] at this
  rw [this]; exact h

theorem dm_pair_o6_rel {s a0 b0 a1 b1 z : Sig} {slo shi alo ahi blo bhi l1 h1 l2 h2 : Nat}
    (hg : Gate DM_PAIR [(s, slo, shi), (a0, l1, h1), (b0, l2, h2),
      (a1, alo, ahi), (b1, blo, bhi), (one, 0, 0)] z) :
    DmRel s a1 b1 z slo shi alo ahi blo bhi := by
  intro t v h; apply hg t v
  show lutK DM_PAIR [winK s slo shi t, winK a0 l1 h1 t, winK b0 l2 h2 t,
    winK a1 alo ahi t, winK b1 blo bhi t, winK one 0 0 t] = _
  rw [winK_one]
  have := dm_pair_o6_kleene (winK s slo shi t) (winK a0 l1 h1 t) (winK b0 l2 h2 t)
    (winK a1 alo ahi t) (winK b1 blo bhi t)
  simp only [o6K] at this
  rw [this]; exact h

/-- **The datamux settles.** `s` at `sv` on `[Ts, Ts']`, the selected input
(`b` if `sv`, else `a`) at `v` on `[Td, Td']` (both at their drivers): `z = v`
on `[max (Ts + shi) (Td + dhi), min (Ts' + slo) (Td' + dlo)]` where
`[dlo, dhi]` is the selected input's window. -/
theorem dm_settles {s a b z : Sig} {slo shi alo ahi blo bhi : Nat}
    (hR : DmRel s a b z slo shi alo ahi blo bhi)
    (hsw : slo ≤ shi) (haw : alo ≤ ahi) (hbw : blo ≤ bhi)
    (sv v : Bool) (Ts Ts' Td Td' : Nat)
    (h_s : StableOn s sv Ts Ts') (h_d : StableOn (if sv then b else a) v Td Td') :
    StableOn z v (max (Ts + shi) (Td + (if sv then bhi else ahi)))
      (min (Ts' + slo) (Td' + (if sv then blo else alo))) := by
  intro t h1 h2
  apply hR t v
  have hs : winK s slo shi t = K3.ofBool sv := win_of_stable hsw h_s (by omega) (by omega)
  cases sv with
  | true =>
    simp only [↓reduceIte] at h_d h1 h2
    rw [hs, win_of_stable hbw h_d (by omega) (by omega)]; rfl
  | false =>
    simp only [Bool.false_eq_true, ↓reduceIte] at h_d h1 h2
    rw [hs, win_of_stable haw h_d (by omega) (by omega)]; rfl

/-- **The merge's select.** `usel = x_req | x_ack` (real INIT `4'hE`): `1`
while `x_req` reads high; `0` while both read low. -/
theorem usel_high {xr xa sel : Sig} {lo hi lo' hi' : Nat}
    (hg : Gate 0xE [(xr, lo, hi), (xa, lo', hi')] sel) (hw : lo ≤ hi) (T T' : Nat)
    (hx : StableOn xr true T T') : StableOn sel true (T + hi) (T' + lo) := by
  intro t h1 h2
  apply hg t true
  show lutK 0xE [winK xr lo hi t, winK xa lo' hi' t] = _
  rw [win_of_stable hw hx (by omega) (by omega), usel_kleene]; simp [K3.ofBool]

theorem usel_low {xr xa sel : Sig} {lo hi lo' hi' : Nat}
    (hg : Gate 0xE [(xr, lo, hi), (xa, lo', hi')] sel) (hw : lo ≤ hi) (hw' : lo' ≤ hi')
    (T T' : Nat) (hx : StableOn xr false T T') (ha : StableOn xa false T T') :
    StableOn sel false (T + max hi hi') (T' + min lo lo') := by
  intro t h1 h2
  apply hg t false
  show lutK 0xE [winK xr lo hi t, winK xa lo' hi' t] = _
  rw [win_of_stable hw hx (by omega) (by omega), win_of_stable hw' ha (by omega) (by omega),
    usel_kleene]; rfl

/-- **H_BUNDLED_Z, classic timed form (sufficient).** The datamux output
`z` (one bit) is `v` on `[Tz, Tz']` (from `dm_settles`); the consumer latch
bit reads it through `[zlo, zhi]`; its enable is a clean pulse `[Ton, Toff)`.
* **H_BUNDLED_Z_T** `Tz + zhi ≤ Ton + ehi`: the selected data, through the
  select cone, the datamux and the route to the bit, arrives no later than
  the enable rise's latest arrival (rule A's form; `Ton ≥` join edge + uor +
  the matched line's rise + the consumer's C-element, by `Bundling.sym_edge`
  / `slow_not_early`);
* **H_PW** `Ton + ehi + fhi ≤ Toff + elo`;
* **H_HOLD** `Toff + ehi ≤ Tz' + 1 + zlo`.
Then the bit holds `v` from `Ton + ehi` until `Tnext + elo`. -/
theorem bundled_z_capture (z en q : Sig) (zlo zhi elo ehi flo fhi : Nat)
    (hL : LatchRel z en q zlo zhi elo ehi flo fhi)
    (hzw : zlo ≤ zhi) (hew : elo ≤ ehi) (hfw : flo ≤ fhi) (H_LOOP_POS : 1 ≤ flo)
    (Ton Toff Tnext Tz Tz' : Nat) (v : Bool)
    (h_on : ∀ t, Ton ≤ t → t < Toff → en t = true)
    (h_off : ∀ t, Toff ≤ t → t < Tnext → en t = false)
    (h_z : StableOn z v Tz Tz')
    (H_BUNDLED_Z_T : Tz + zhi ≤ Ton + ehi)
    (H_PW : Ton + ehi + fhi ≤ Toff + elo)
    (H_HOLD : Toff + ehi ≤ Tz' + 1 + zlo) :
    ∀ t, Ton + ehi ≤ t → t < Tnext + elo → q t = v := by
  have hc := capture z en q zlo zhi elo ehi flo fhi hL hzw hew hfw H_LOOP_POS
    Ton Toff Tnext Tz (Tz' + 1) v h_on h_off (fun t h1 h2 => h_z t h1 (by omega))
    (classic_implies_setup Ton Toff Tz zhi ehi elo fhi H_BUNDLED_Z_T H_PW) H_HOLD
  intro t h1 h2
  exact hc t (by omega) h2

end bundledZ

end Formal.Cells.ConstraintsMux
