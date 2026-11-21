import Formal.Cells.Bundling
import Formal.Cells.Latch
open Formal.Core.LutList

/-!
# Probe P3b: timed theorems for `bd_latch_rst` (cell_constraints entries
`bd_latch_rst.setup_data`, `bd_latch_rst.setup_pulse`, `bd_latch_rst.hold`)

`Bundling.capture` is the timed capture theorem for the odd latch LUT
(`64'hB8B8...`) and the pair; `Latch.rst0_kleene`/`rst1_kleene` give the
Kleene function of the resettable bit, but no timed theorem was stated for its
INITs `64'h00B8_00B8_00B8_00B8` (RESET_VALUE 0) and `64'hFFB8_FFB8_FFB8_FFB8`
(RESET_VALUE 1), pins `I0=d I1=en I2=q I3=rst I4=I5=0` (cells/rtl/bd_latch.v).

Model: `Bundling.Gate` (window channels per pin, Kleene closure of the REAL
INIT; H_KLEENE_LUT), with the rst pin as a fourth windowed pin `[rlo, rhi]`
(routed rst wire + I3 arc). Results:

* `rst_latch_on`: whenever the rst pin's window reads definitely 0, the bit
  is exactly `Bundling.LatchRel` (the Kleene mux `en ? d : q`), for both INITs.
* `capture_rst`: `Bundling.capture` for the resettable bit, with the same
  H_SETUP (data part `Td + dhi + fhi ≤ Toff + elo`, enable part
  `Ton + ehi + fhi ≤ Toff + elo`) and H_HOLD (`Toff + ehi ≤ Tnew + dlo`), plus
  **H_RST_DONE** (rst low at the pin from `Rl`, `Rl + rhi ≤` start of the
  window).
* `capture_rst_from_request`: the request-side form (`setup_pulse`:
  `ehi + fhi ≤ W + elo`) via `Bundling.setup_from_request`.
* `reset_loads`, `reset_holds`: the reset itself is a timed theorem: rst high
  at the pin for `[R0, R1)` loads the reset value from `R0 + rhi`; if the
  pulse fills the loop (**H_RST_PW** `R0 + rhi + fhi ≤ R1 + rlo`) and the
  enable is closed when the release arrives (**H_EN_CLOSED_AT_RELEASE**), the
  bit HOLDS the reset value after rst falls, until the next enable rise
  reaches it (the initial token).
* `counter_rule_I_rst0/1`, `counter_rule_H_rst0/1`: Bundling's counter-traces
  are runs of the resettable INITs with rst tied low: H_SETUP with the loop
  window (rule I's missing I2 arc) and H_HOLD are each needed (exactness on a
  witness, as for the odd bit).

Core Lean only.
-/

namespace Formal.Cells.ConstraintsLatchRst
open Formal.Cells
open Formal.Cells.Bundling

/-- The two INITs, from `Latch` (verbatim from the RTL). -/
abbrev RST0 : Nat := Latch.RST0
abbrev RST1 : Nat := Latch.RST1

/-- The Kleene function of a resettable bit with reset value `rv`. -/
def IsRstLatch (init : Nat) (rv : Bool) : Prop :=
  ∀ d en q rst : K3, lutK init [d, en, q, rst, .f, .f] = K3.mux rst (K3.mux en q d) (K3.ofBool rv)

theorem rst0_isRst : IsRstLatch RST0 false := fun d en q rst => Latch.rst0_kleene d en q rst
theorem rst1_isRst : IsRstLatch RST1 true := fun d en q rst => Latch.rst1_kleene d en q rst

/-- The gate relation of one resettable bit: pins `d, en, q (feedback), rst`,
I4/I5 tied 0. -/
abbrev RstGate (init : Nat) (d en q rst : Sig) (dlo dhi elo ehi flo fhi rlo rhi : Nat) : Prop :=
  Gate init [(d, dlo, dhi), (en, elo, ehi), (q, flo, fhi), (rst, rlo, rhi),
    (zero, 0, 0), (zero, 0, 0)] q

/-- **With rst definitely low at its pin, the bit is the latch mux.** -/
theorem rst_latch_on {init : Nat} {rv : Bool} (hI : IsRstLatch init rv)
    {d en q rst : Sig} {dlo dhi elo ehi flo fhi rlo rhi : Nat}
    (hg : RstGate init d en q rst dlo dhi elo ehi flo fhi rlo rhi) (t : Nat)
    (hr : winK rst rlo rhi t = .f) (b : Bool)
    (h : K3.mux (winK en elo ehi t) (winK q flo fhi t) (winK d dlo dhi t) = K3.ofBool b) :
    q t = b := by
  apply hg t b
  show lutK init [winK d dlo dhi t, winK en elo ehi t, winK q flo fhi t, winK rst rlo rhi t,
    winK zero 0 0 t, winK zero 0 0 t] = _
  rw [winK_zero, hr, hI]; exact h

/-- **Capture theorem for `bd_latch_rst`** (both reset polarities).
Hypotheses as `Bundling.capture` (H_LOOP_POS, H_EN_CLEAN as `h_on`/`h_off`,
`h_d`, **H_SETUP**, **H_HOLD**), plus
* **H_RST_LOW**: rst low at its driver from `Rl` on (the reset was released);
* **H_RST_DONE** `Rl + rhi ≤ max (Ton + ehi) (Td + dhi)`: the release has
  reached the I3 select (latest) before the window starts. Test: SDF of the
  rst net (slow max) against the first enable rise after reset.
Conclusion: `q = v` from `max (Ton + ehi) (Td + dhi)` until `Tnext + elo`. -/
theorem capture_rst {init : Nat} {rv : Bool} (hI : IsRstLatch init rv)
    (d en q rst : Sig) (dlo dhi elo ehi flo fhi rlo rhi : Nat)
    (hg : RstGate init d en q rst dlo dhi elo ehi flo fhi rlo rhi)
    (hdw : dlo ≤ dhi) (hew : elo ≤ ehi) (hfw : flo ≤ fhi) (hrw : rlo ≤ rhi)
    (H_LOOP_POS : 1 ≤ flo)
    (Ton Toff Tnext Td Tnew Rl : Nat) (v : Bool)
    (h_on : ∀ t, Ton ≤ t → t < Toff → en t = true)
    (h_off : ∀ t, Toff ≤ t → t < Tnext → en t = false)
    (h_d : ∀ t, Td ≤ t → t < Tnew → d t = v)
    (H_RST_LOW : ∀ t, Rl ≤ t → rst t = false)
    (H_RST_DONE : Rl + rhi ≤ max (Ton + ehi) (Td + dhi))
    (H_SETUP : max (Ton + ehi) (Td + dhi) + fhi ≤ Toff + elo)
    (H_HOLD : Toff + ehi ≤ Tnew + dlo) :
    ∀ t, max (Ton + ehi) (Td + dhi) ≤ t → t < Tnext + elo → q t = v := by
  have hL : ∀ t, max (Ton + ehi) (Td + dhi) ≤ t → ∀ b,
      K3.mux (winK en elo ehi t) (winK q flo fhi t) (winK d dlo dhi t) = K3.ofBool b → q t = b :=
    fun t ht b h => rst_latch_on hI hg t
      (win_eq (b := false) hrw (fun u hu1 _ => H_RST_LOW u (by omega))) b h
  suffices H : ∀ n, ∀ t, t < n → max (Ton + ehi) (Td + dhi) ≤ t → t < Tnext + elo → q t = v
    from fun t h1 h2 => H (t + 1) t (Nat.lt_succ_self t) h1 h2
  intro n
  induction n with
  | zero => intro t h; omega
  | succ n ih =>
    intro t htn h1 h2
    by_cases hA : t < Toff + elo
    · have he : winK en elo ehi t = .t :=
        win_eq (b := true) hew (fun u hu1 hu2 => h_on u (by omega) (by omega))
      have hd : winK d dlo dhi t = K3.ofBool v :=
        win_eq hdw (fun u hu1 hu2 => h_d u (by omega) (by omega))
      exact hL t h1 v (by rw [he, hd]; rfl)
    · have hq : winK q flo fhi t = K3.ofBool v :=
        win_eq hfw (fun u hu1 hu2 => ih u (by omega) (by omega) (by omega))
      by_cases hB : t < Toff + ehi
      · have hd : winK d dlo dhi t = K3.ofBool v :=
          win_eq hdw (fun u hu1 hu2 => h_d u (by omega) (by omega))
        exact hL t h1 v (by rw [hq, hd, mux_same])
      · have he : winK en elo ehi t = .f :=
          win_eq (b := false) hew (fun u hu1 hu2 => h_off u (by omega) (by omega))
        exact hL t h1 v (by rw [he, hq]; rfl)

/-- **Request-side form** (`setup_pulse` entry): with the node rising no
earlier than `Tr + Rlo` and high for at least `W`, the data part
`Td + dhi + fhi ≤ Tr + Rlo + W + elo` and the pulse part `ehi + fhi ≤ W + elo`
give `capture_rst`'s conclusion. -/
theorem capture_rst_from_request {init : Nat} {rv : Bool} (hI : IsRstLatch init rv)
    (d en q rst : Sig) (dlo dhi elo ehi flo fhi rlo rhi : Nat)
    (hg : RstGate init d en q rst dlo dhi elo ehi flo fhi rlo rhi)
    (hdw : dlo ≤ dhi) (hew : elo ≤ ehi) (hfw : flo ≤ fhi) (hrw : rlo ≤ rhi)
    (H_LOOP_POS : 1 ≤ flo)
    (Ton Toff Tnext Td Tnew Rl Tr Rlo W : Nat) (v : Bool)
    (h_on : ∀ t, Ton ≤ t → t < Toff → en t = true)
    (h_off : ∀ t, Toff ≤ t → t < Tnext → en t = false)
    (h_d : ∀ t, Td ≤ t → t < Tnew → d t = v)
    (H_RST_LOW : ∀ t, Rl ≤ t → rst t = false)
    (H_RST_DONE : Rl + rhi ≤ max (Ton + ehi) (Td + dhi))
    (H_REQ_LO : Tr + Rlo ≤ Ton) (H_EN_WIDTH : Ton + W ≤ Toff)
    (H_SETUP_DATA : Td + dhi + fhi ≤ Tr + Rlo + W + elo)
    (H_PW : ehi + fhi ≤ W + elo)
    (H_HOLD : Toff + ehi ≤ Tnew + dlo) :
    ∀ t, max (Ton + ehi) (Td + dhi) ≤ t → t < Tnext + elo → q t = v :=
  capture_rst hI d en q rst dlo dhi elo ehi flo fhi rlo rhi hg hdw hew hfw hrw H_LOOP_POS
    Ton Toff Tnext Td Tnew Rl v h_on h_off h_d H_RST_LOW H_RST_DONE
    (setup_from_request Ton Toff Td Tr Rlo W dhi ehi elo fhi H_REQ_LO H_EN_WIDTH
      H_SETUP_DATA H_PW) H_HOLD

/-! ## The reset itself -/

/-- **Reset loads.** rst high at its driver on `[R0, R1)`: the bit is the
reset value on `[R0 + rhi, R1 + rlo)`, whatever `d`, `en` and the loop do
(`Latch.rst_forces`, with windows). -/
theorem reset_loads {init : Nat} {rv : Bool} (hI : IsRstLatch init rv)
    {d en q rst : Sig} {dlo dhi elo ehi flo fhi rlo rhi : Nat}
    (hg : RstGate init d en q rst dlo dhi elo ehi flo fhi rlo rhi) (hrw : rlo ≤ rhi)
    (R0 R1 : Nat) (h_rst : ∀ t, R0 ≤ t → t < R1 → rst t = true) :
    ∀ t, R0 + rhi ≤ t → t < R1 + rlo → q t = rv := by
  intro t h1 h2
  apply hg t rv
  have hr : winK rst rlo rhi t = .t :=
    win_eq (b := true) hrw (fun u hu1 hu2 => h_rst u (by omega) (by omega))
  show lutK init [winK d dlo dhi t, winK en elo ehi t, winK q flo fhi t, winK rst rlo rhi t,
    winK zero 0 0 t, winK zero 0 0 t] = _
  rw [winK_zero, hr, hI]; rfl

/-- **Reset holds after release (the initial token).** rst high on
`[R0, R1)`, then anything (it may fall, glitch to X at the pin, or rise);
`en` low at its driver on `[E0, Tnext)`. Hypotheses:
* **H_RST_PW** `R0 + rhi + fhi ≤ R1 + rlo`: the reset pulse at the pin lasts
  at least one full loop window (the loop is filled with the reset value).
* **H_EN_CLOSED_AT_RELEASE** `E0 + ehi ≤ R1 + rlo`: the enable is
  definitely closed at the I1 select before the release can reach I3.
Then the bit holds `rv` on `[R0 + rhi, Tnext + elo)`: until the first enable
rise reaches it, independent of what rst does after `R1` (the INIT's
consensus: with `en = 0` and `q = rv`, rst is a mux select between equal legs). -/
theorem reset_holds {init : Nat} {rv : Bool} (hI : IsRstLatch init rv)
    {d en q rst : Sig} {dlo dhi elo ehi flo fhi rlo rhi : Nat}
    (hg : RstGate init d en q rst dlo dhi elo ehi flo fhi rlo rhi)
    (hew : elo ≤ ehi) (hfw : flo ≤ fhi) (hrw : rlo ≤ rhi) (H_LOOP_POS : 1 ≤ flo)
    (R0 R1 E0 Tnext : Nat)
    (h_rst : ∀ t, R0 ≤ t → t < R1 → rst t = true)
    (h_off : ∀ t, E0 ≤ t → t < Tnext → en t = false)
    (H_RST_PW : R0 + rhi + fhi ≤ R1 + rlo)
    (H_EN_CLOSED_AT_RELEASE : E0 + ehi ≤ R1 + rlo) :
    ∀ t, R0 + rhi ≤ t → t < Tnext + elo → q t = rv := by
  suffices H : ∀ n, ∀ t, t < n → R0 + rhi ≤ t → t < Tnext + elo → q t = rv
    from fun t h1 h2 => H (t + 1) t (Nat.lt_succ_self t) h1 h2
  intro n
  induction n with
  | zero => intro t h; omega
  | succ n ih =>
    intro t htn h1 h2
    by_cases hA : t < R1 + rlo
    · exact reset_loads hI hg hrw R0 R1 h_rst t h1 hA
    · have hq : winK q flo fhi t = K3.ofBool rv :=
        win_eq hfw (fun u hu1 hu2 => ih u (by omega) (by omega) (by omega))
      have he : winK en elo ehi t = .f :=
        win_eq (b := false) hew (fun u hu1 hu2 => h_off u (by omega) (by omega))
      apply hg t rv
      show lutK init [winK d dlo dhi t, winK en elo ehi t, winK q flo fhi t, winK rst rlo rhi t,
        winK zero 0 0 t, winK zero 0 0 t] = _
      rw [winK_zero, hI, he, hq]
      exact mux_same _ rv

/-! ## Counter-traces: Bundling's, with the resettable INITs and rst tied low -/

theorem rst0_bin_odd : ∀ d en q : Bool,
    lutB RST0 [d, en, q, false, false, false] = lutB ODD [d, en, q, false, false, false] := by
  decide
theorem rst1_bin_odd : ∀ d en q : Bool,
    lutB RST1 [d, en, q, false, false, false] = lutB ODD [d, en, q, false, false, false] := by
  decide

/-- A transport run of the odd LUT with I3..I5 tied 0 is a run of either
resettable INIT with rst tied 0. -/
theorem transport_rst_of_odd (init : Nat)
    (he : ∀ d en q : Bool, lutB init [d, en, q, false, false, false] =
      lutB ODD [d, en, q, false, false, false])
    (d en q : Sig) (a b c : Nat)
    (h : Transport ODD [(d, a), (en, b), (q, c), (zero, 0), (zero, 0), (zero, 0)] q) :
    Transport init [(d, a), (en, b), (q, c), (zero, 0), (zero, 0), (zero, 0)] q := by
  intro t
  rw [h t]
  show lutB ODD [d (t - a), en (t - b), q (t - c), false, false, false] =
    lutB init [d (t - a), en (t - b), q (t - c), false, false, false]
  rw [he]

/-- **Rule I counter-trace, resettable bit** (RESET_VALUE 0 and 1): rst tied
low, the data part of rule I without the I2 arc holds with margin 0, H_SETUP
fails by the I2 arc, H_HOLD holds, and the bit is wrong at 11. -/
theorem counter_rule_I_rst (init : Nat)
    (he : ∀ d en q : Bool, lutB init [d, en, q, false, false, false] =
      lutB ODD [d, en, q, false, false, false]) :
    RstGate init caD caEn caQ zero 1 1 1 1 3 3 0 0 ∧
    (8 + 1 + 2 ≤ 10 + 1) ∧ ¬ (max (0 + 1) (8 + 1) + 3 ≤ 10 + 1) ∧ (10 + 1 ≤ 1000 + 1) ∧
    caQ 11 = false := by
  refine ⟨?_, by decide, by decide, by decide, by decide⟩
  exact transport_gate init [(caD, 1, 1, 1), (caEn, 1, 1, 1), (caQ, 3, 3, 3),
      (zero, 0, 0, 0), (zero, 0, 0, 0), (zero, 0, 0, 0)] caQ (by simp)
    (transport_rst_of_odd init he caD caEn caQ 1 1 3 caQ_transport)

/-- **Rule H counter-trace, resettable bit**: H_SETUP holds, H_HOLD fails,
the token is lost. -/
theorem counter_rule_H_rst (init : Nat)
    (he : ∀ d en q : Bool, lutB init [d, en, q, false, false, false] =
      lutB ODD [d, en, q, false, false, false]) :
    RstGate init cbD cbEn cbQ zero 0 0 2 2 1 1 0 0 ∧
    (∀ t, 5 ≤ t → t < 10 → cbD t = true) ∧
    max (0 + 2) (5 + 0) + 1 ≤ 10 + 2 ∧ ¬ (10 + 2 ≤ 10 + 0) ∧
    cbQ 12 = false := by
  refine ⟨?_, ?_, by decide, by decide, by decide⟩
  · exact transport_gate init [(cbD, 0, 0, 0), (cbEn, 2, 2, 2), (cbQ, 1, 1, 1),
        (zero, 0, 0, 0), (zero, 0, 0, 0), (zero, 0, 0, 0)] cbQ (by simp)
      (transport_rst_of_odd init he cbD cbEn cbQ 0 2 1 cbQ_transport)
  · intro t h1 h2; simp [cbD]; omega

/-- Instances: both reset polarities (the INITs differ only in the rst = 1 half). -/
theorem counter_rules_rst0 :
    RstGate RST0 caD caEn caQ zero 1 1 1 1 3 3 0 0 ∧ caQ 11 = false ∧
    RstGate RST0 cbD cbEn cbQ zero 0 0 2 2 1 1 0 0 ∧ cbQ 12 = false :=
  ⟨(counter_rule_I_rst RST0 rst0_bin_odd).1, (counter_rule_I_rst RST0 rst0_bin_odd).2.2.2.2,
   (counter_rule_H_rst RST0 rst0_bin_odd).1, (counter_rule_H_rst RST0 rst0_bin_odd).2.2.2.2⟩
theorem counter_rules_rst1 :
    RstGate RST1 caD caEn caQ zero 1 1 1 1 3 3 0 0 ∧ caQ 11 = false ∧
    RstGate RST1 cbD cbEn cbQ zero 0 0 2 2 1 1 0 0 ∧ cbQ 12 = false :=
  ⟨(counter_rule_I_rst RST1 rst1_bin_odd).1, (counter_rule_I_rst RST1 rst1_bin_odd).2.2.2.2,
   (counter_rule_H_rst RST1 rst1_bin_odd).1, (counter_rule_H_rst RST1 rst1_bin_odd).2.2.2.2⟩

end Formal.Cells.ConstraintsLatchRst
