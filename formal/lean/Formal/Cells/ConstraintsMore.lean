import Formal.Cells.Bundling
import Formal.Cells.LibEndMemMlink
import Formal.Cells.LinkHandshake
open Formal.Core.LutList

/-!
# Probe P3e: H_QFB_FIRST as a timed inequality (`bd_mlink.qfb_first`,
`bd_flink.qfb_first`), and the BRAM clock widths (`bd_mem.clk_high_width`)

`LibEndMemMlink` proved the MOUSETRAP request bit correct under H_QFB_FIRST
as an UNTIMED schedule restriction (`allowH`: the enable LUT does not move
while the latch's own feedback pin still differs from `done`), and gave the
runt/cycle without it. The cell-constraint JSON's inequality
`done -> uq.I2 (max) <= done -> ux.I0 (min) + ux arc (min) + en -> uq.I1 (min)`
was the doc's physical reading. This file proves it in Bundling's timed window
model with the REAL INITs:

* `bd_mlink_ctl`: `uq` = `bd_latch #(.W(1))` (`64'hB8B8...`, `I0 d=req_in,
  I1 en, I2 q=done`), `ux` = `LUT3 8'hF9` (`I0 done, I1 ack, I2 rst`).
* `bd_flink_ctl`: `uq` = `LUT3 8'hE2` (`I0 req_in, I1 ck, I2 done`,
  transparent while `ck = 0`), `uck` = `LUT3 8'h06` (`I0 done, I1 ack, I2 rst`).

Results:
* `capture_gap`: `Bundling.capture` allowing an undefined enable between its
  last-high and first-low instants (the enable LUT's own transition).
* `ux_open`, `uck_open`: the enable LUT keeps the latch open until
  `wlo` (done -> ux/uck pin wire min + LUT arc min) after `done` first shows
  the new value: the causality that makes the race a self-race.
* `mlink_qfb_first_timed`, `flink_qfb_first_timed`: under
  **H_QFB_FIRST_T** `max (Ton + ehi) (Td + dhi) + fhi ≤ Tq + wlo + elo`
  (`Tq`: the instant up to which `done` still shows the old value) the request
  bit captures the new token and holds it until the next enable re-opening.
  `qfb_clean_form`: when `done` makes one clean edge (`Tq` = the settle
  instant) this is exactly the JSON's `fhi ≤ wlo + elo`.
* `qfb_counter`: a closed-form transport run of the WHOLE mlink request-bit
  loop (latch + ux, real INITs, `ack` held low, no rst) with `fhi = 3 >
  wlo + elo = 2`: `done` rises at 6, falls back at 8 and oscillates with
  period 3 forever (the timed form of `mlink_runt`/`mlink_cycle`).
  `qfb_clean`: the same environment with `fhi = 2 = wlo + elo`: one clean
  edge. So the inequality is exact on this witness (equality is safe,
  one tick less is not).
* `MemPort.clk_high_ok` / `clk_low_ok`: the RAM clock's high and low widths
  meet `tPWH` / `tPWL` under the stated line inequalities.

Core Lean only.
-/

namespace Formal.Cells.ConstraintsMore
open Formal.Cells
open Formal.Cells.Bundling

/-! ## 1. Capture with an undefined gap in the enable -/

/-- `Bundling.capture` with the enable true on `[Ton, Toff)`, ANYTHING on
`[Toff, Toff2)` (the enable LUT switching, possibly glitching or X), false on
`[Toff2, Tnext)`. H_SETUP is against the first instant the enable can stop
being high (`Toff + elo`), H_HOLD against the last instant it can still be
non-low (`Toff2 + ehi`). -/
theorem capture_gap (d en q : Sig) (dlo dhi elo ehi flo fhi : Nat)
    (hL : LatchRel d en q dlo dhi elo ehi flo fhi)
    (hdw : dlo ≤ dhi) (hew : elo ≤ ehi) (hfw : flo ≤ fhi) (H_LOOP_POS : 1 ≤ flo)
    (Ton Toff Toff2 Tnext Td Tnew : Nat) (v : Bool) (hgap : Toff ≤ Toff2)
    (h_on : ∀ t, Ton ≤ t → t < Toff → en t = true)
    (h_off : ∀ t, Toff2 ≤ t → t < Tnext → en t = false)
    (h_d : ∀ t, Td ≤ t → t < Tnew → d t = v)
    (H_SETUP : max (Ton + ehi) (Td + dhi) + fhi ≤ Toff + elo)
    (H_HOLD : Toff2 + ehi ≤ Tnew + dlo) :
    ∀ t, max (Ton + ehi) (Td + dhi) ≤ t → t < Tnext + elo → q t = v := by
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
      exact hL t v (by rw [he, hd]; rfl)
    · have hq : winK q flo fhi t = K3.ofBool v :=
        win_eq hfw (fun u hu1 hu2 => ih u (by omega) (by omega) (by omega))
      by_cases hB : t < Toff2 + ehi
      · have hd : winK d dlo dhi t = K3.ofBool v :=
          win_eq hdw (fun u hu1 hu2 => h_d u (by omega) (by omega))
        exact hL t v (by rw [hq, hd, mux_same])
      · have he : winK en elo ehi t = .f :=
          win_eq (b := false) hew (fun u hu1 hu2 => h_off u (by omega) (by omega))
        exact hL t v (by rw [he, hq]; rfl)

/-! ## 2. The enable LUTs keep the latch open until `done` has been seen -/

theorem ux_K_open (u : Bool) : lutK LibEndMemMlink.INIT_UX [K3.ofBool u, K3.ofBool u, .f] = .t := by
  cases u <;> decide
theorem uck_K_closed_low (u : Bool) :
    lutK LibEndMemMlink.INIT_UCK [K3.ofBool u, K3.ofBool u, .f] = .f := by
  cases u <;> decide

/-- **`ux` (mlink) stays open.** `done` shows the old value `u` on `[A, Tq)`,
`ack` shows `u` on `[B, C)` (H_ACK_STABLE: the downstream has not answered).
Then `en` (ux's output, before its route to `uq.I1`) is high on
`[max (A + whi) (B + ahi), min (Tq + wlo) (C + alo))`; `[wlo, whi]` is the
`done -> ux.I0` route plus the I0 arc. -/
theorem ux_open {done ack en : Sig} {wlo whi alo ahi : Nat}
    (hg : Gate LibEndMemMlink.INIT_UX [(done, wlo, whi), (ack, alo, ahi), (zero, 0, 0)] en)
    (hw : wlo ≤ whi) (ha : alo ≤ ahi) (u : Bool) (A Tq B C : Nat)
    (hd : ∀ t, A ≤ t → t < Tq → done t = u) (hk : ∀ t, B ≤ t → t < C → ack t = u) :
    ∀ t, max (A + whi) (B + ahi) ≤ t → t < min (Tq + wlo) (C + alo) → en t = true := by
  intro t h1 h2
  apply hg t true
  show lutK _ [winK done wlo whi t, winK ack alo ahi t, winK zero 0 0 t] = _
  rw [win_eq (b := u) hw (fun s hs1 hs2 => hd s (by omega) (by omega)),
    win_eq (b := u) ha (fun s hs1 hs2 => hk s (by omega) (by omega)), winK_zero]
  exact ux_K_open u

/-- **`uck` (flink) stays low (latch transparent).** Same shape. -/
theorem uck_open {done ack ck : Sig} {wlo whi alo ahi : Nat}
    (hg : Gate LibEndMemMlink.INIT_UCK [(done, wlo, whi), (ack, alo, ahi), (zero, 0, 0)] ck)
    (hw : wlo ≤ whi) (ha : alo ≤ ahi) (u : Bool) (A Tq B C : Nat)
    (hd : ∀ t, A ≤ t → t < Tq → done t = u) (hk : ∀ t, B ≤ t → t < C → ack t = u) :
    ∀ t, max (A + whi) (B + ahi) ≤ t → t < min (Tq + wlo) (C + alo) → ck t = false := by
  intro t h1 h2
  apply hg t false
  show lutK _ [winK done wlo whi t, winK ack alo ahi t, winK zero 0 0 t] = _
  rw [win_eq (b := u) hw (fun s hs1 hs2 => hd s (by omega) (by omega)),
    win_eq (b := u) ha (fun s hs1 hs2 => hk s (by omega) (by omega)), winK_zero]
  exact uck_K_closed_low u

/-! ## 3. The request latches as `LatchRel` (real INITs) -/

theorem lat_is_odd : LibEndMemMlink.INIT_LAT = ODD := rfl

/-- `bd_mlink_ctl.uq` is a `LatchRel` (it is the odd latch bit). -/
theorem mlink_uq_latch {d en q : Sig} {dlo dhi elo ehi flo fhi : Nat}
    (hg : Gate LibEndMemMlink.INIT_LAT [(d, dlo, dhi), (en, elo, ehi), (q, flo, fhi),
      (zero, 0, 0), (zero, 0, 0), (zero, 0, 0)] q) :
    LatchRel d en q dlo dhi elo ehi flo fhi :=
  odd_latch hg

theorem fq_kleene : ∀ r k q : K3, lutK LibEndMemMlink.INIT_FQ [r, k, q] = K3.mux k r q := by
  decide

theorem winVals_not (x : Sig) (lo hi t : Nat) :
    winVals (fun s => !x s) lo hi t = (winVals x lo hi t).map (!·) := by
  unfold winVals; rw [List.map_map]; rfl

theorem winK_not (x : Sig) (lo hi t : Nat) (hlh : lo ≤ hi) :
    winK (fun s => !x s) lo hi t = K3.not (winK x lo hi t) := by
  unfold winK
  rw [winVals_not, List.all_map, List.all_map]
  have e1 : ((id ∘ fun b : Bool => !b)) = (fun b : Bool => !b) := rfl
  have e2 : ((fun b : Bool => !b) ∘ fun b : Bool => !b) = id := by funext b; cases b <;> rfl
  rw [e1, e2]
  by_cases h1 : (winVals x lo hi t).all id = true
  · by_cases h2 : (winVals x lo hi t).all (!·) = true
    · -- both: the list is empty
      have hnil : winVals x lo hi t = [] := by
        cases hl : winVals x lo hi t with
        | nil => rfl
        | cons b bs =>
          rw [hl] at h1 h2
          simp at h1 h2
          exact absurd h1.1 (by simp [h2.1])
      have hm : x (t - lo) ∈ winVals x lo hi t := mem_winVals.2 ⟨lo, Nat.le_refl _, hlh, rfl⟩
      rw [hnil] at hm; simp at hm
    · simp [h1, h2, K3.not]
  · by_cases h2 : (winVals x lo hi t).all (!·) = true
    · simp [h1, h2, K3.not]
    · simp [h1, h2, K3.not]

theorem mux_not (k a b : K3) : K3.mux (K3.not k) a b = K3.mux k b a := by
  cases k <;> cases a <;> cases b <;> rfl

/-- `bd_flink_ctl.uq` is a `LatchRel` with enable `!ck`. -/
theorem flink_uq_latch {d ck q : Sig} {dlo dhi elo ehi flo fhi : Nat} (hew : elo ≤ ehi)
    (hg : Gate LibEndMemMlink.INIT_FQ [(d, dlo, dhi), (ck, elo, ehi), (q, flo, fhi)] q) :
    LatchRel d (fun s => !ck s) q dlo dhi elo ehi flo fhi := by
  intro t b h
  apply hg t b
  show lutK _ [winK d dlo dhi t, winK ck elo ehi t, winK q flo fhi t] = _
  rw [fq_kleene, ← h, winK_not ck elo ehi t hew, mux_not]

/-! ## 4. H_QFB_FIRST, timed -/

/-- **mlink request bit, timed H_QFB_FIRST (sufficient).**
Signals at their drivers: `req` (`req_in`), `en` (ux output), `done`, `ack`.
Windows: `uq` reads `req` `[dlo, dhi]`, `en` `[elo, ehi]` (route + I1 arc),
`done` `[flo, fhi]` (the feedback route + I2 arc); `ux` reads `done`
`[wlo, whi]` (route + I0 arc + ux's arc) and `ack` `[alo, ahi]`.
Named hypotheses:
* `h_old`: `done` shows the old value `!v` on `[A, Tq)`;
* **H_ACK_STABLE**: `ack` shows `!v` on `[B, C)` with `Tq + wlo ≤ C + alo`
  (the downstream does not answer before ux has seen the new `done`);
* `h_d`: `req` is the new value `v` on `[Td, Tnew)`;
* `h_off`: `en` low on `[Toff2, Tnext)` (ux has closed; anything between
  `Tq + wlo` and `Toff2`, **H_GAP** `Tq + wlo ≤ Toff2`);
* **H_QFB_FIRST_T** `max (Ton + ehi) (Td + dhi) + fhi ≤ Tq + wlo + elo` with
  `Ton = max (A + whi) (B + ahi)`;
* **H_HOLD** `Toff2 + ehi ≤ Tnew + dlo`.
Conclusion: `done = v` from `max (Ton + ehi) (Td + dhi)` until `Tnext + elo`:
no runt, the token is captured and held. -/
theorem mlink_qfb_first_timed {req en done ack : Sig}
    {dlo dhi elo ehi flo fhi wlo whi alo ahi : Nat}
    (hq : Gate LibEndMemMlink.INIT_LAT [(req, dlo, dhi), (en, elo, ehi), (done, flo, fhi),
      (zero, 0, 0), (zero, 0, 0), (zero, 0, 0)] done)
    (hx : Gate LibEndMemMlink.INIT_UX [(done, wlo, whi), (ack, alo, ahi), (zero, 0, 0)] en)
    (hdw : dlo ≤ dhi) (hew : elo ≤ ehi) (hfw : flo ≤ fhi) (hww : wlo ≤ whi) (haw : alo ≤ ahi)
    (H_LOOP_POS : 1 ≤ flo)
    (v : Bool) (A Tq B C Td Tnew Toff2 Tnext : Nat)
    (h_old : ∀ t, A ≤ t → t < Tq → done t = !v)
    (H_ACK_STABLE : (∀ t, B ≤ t → t < C → ack t = !v) ∧ Tq + wlo ≤ C + alo)
    (h_d : ∀ t, Td ≤ t → t < Tnew → req t = v)
    (h_off : ∀ t, Toff2 ≤ t → t < Tnext → en t = false)
    (H_QFB_FIRST_T : max (max (A + whi) (B + ahi) + ehi) (Td + dhi) + fhi ≤ Tq + wlo + elo)
    (H_GAP : Tq + wlo ≤ Toff2)
    (H_HOLD : Toff2 + ehi ≤ Tnew + dlo) :
    ∀ t, max (max (A + whi) (B + ahi) + ehi) (Td + dhi) ≤ t → t < Tnext + elo → done t = v := by
  have hon := ux_open hx hww haw (!v) A Tq B C h_old H_ACK_STABLE.1
  have hmin : min (Tq + wlo) (C + alo) = Tq + wlo := Nat.min_eq_left H_ACK_STABLE.2
  rw [hmin] at hon
  exact capture_gap req en done dlo dhi elo ehi flo fhi (mlink_uq_latch hq) hdw hew hfw H_LOOP_POS
    (max (A + whi) (B + ahi)) (Tq + wlo) Toff2 Tnext Td Tnew v H_GAP hon h_off h_d
    (by omega) H_HOLD

/-- **flink request bit, timed H_QFB_FIRST (sufficient).** As
`mlink_qfb_first_timed` with `uq = 8'hE2` (transparent while `ck = 0`) and
`uck = 8'h06`; `h_off` is now `ck` HIGH on `[Toff2, Tnext)`. -/
theorem flink_qfb_first_timed {req ck done ack : Sig}
    {dlo dhi elo ehi flo fhi wlo whi alo ahi : Nat}
    (hq : Gate LibEndMemMlink.INIT_FQ [(req, dlo, dhi), (ck, elo, ehi), (done, flo, fhi)] done)
    (hx : Gate LibEndMemMlink.INIT_UCK [(done, wlo, whi), (ack, alo, ahi), (zero, 0, 0)] ck)
    (hdw : dlo ≤ dhi) (hew : elo ≤ ehi) (hfw : flo ≤ fhi) (hww : wlo ≤ whi) (haw : alo ≤ ahi)
    (H_LOOP_POS : 1 ≤ flo)
    (v : Bool) (A Tq B C Td Tnew Toff2 Tnext : Nat)
    (h_old : ∀ t, A ≤ t → t < Tq → done t = !v)
    (H_ACK_STABLE : (∀ t, B ≤ t → t < C → ack t = !v) ∧ Tq + wlo ≤ C + alo)
    (h_d : ∀ t, Td ≤ t → t < Tnew → req t = v)
    (h_off : ∀ t, Toff2 ≤ t → t < Tnext → ck t = true)
    (H_QFB_FIRST_T : max (max (A + whi) (B + ahi) + ehi) (Td + dhi) + fhi ≤ Tq + wlo + elo)
    (H_GAP : Tq + wlo ≤ Toff2)
    (H_HOLD : Toff2 + ehi ≤ Tnew + dlo) :
    ∀ t, max (max (A + whi) (B + ahi) + ehi) (Td + dhi) ≤ t → t < Tnext + elo → done t = v := by
  have hon := uck_open hx hww haw (!v) A Tq B C h_old H_ACK_STABLE.1
  have hmin : min (Tq + wlo) (C + alo) = Tq + wlo := Nat.min_eq_left H_ACK_STABLE.2
  rw [hmin] at hon
  exact capture_gap req (fun s => !ck s) done dlo dhi elo ehi flo fhi (flink_uq_latch hew hq)
    hdw hew hfw H_LOOP_POS
    (max (A + whi) (B + ahi)) (Tq + wlo) Toff2 Tnext Td Tnew v H_GAP
    (fun t h1 h2 => by simp [hon t h1 h2]) (fun t h1 h2 => by simp [h_off t h1 h2]) h_d
    (by omega) H_HOLD

/-- **The JSON's form.** If `done` still shows the old value up to the
instant the latch has settled (`S ≤ Tq`: one clean edge, no early partial
flip), H_QFB_FIRST_T is exactly `fhi ≤ wlo + elo`: feedback route max (with
its site pin and I2 arc) ≤ done -> ux route min + ux arc min + en -> uq.I1
route min. -/
theorem qfb_clean_form (S Tq fhi wlo elo : Nat) (hS : S ≤ Tq) (h : fhi ≤ wlo + elo) :
    S + fhi ≤ Tq + wlo + elo := by omega

/-! ## 5. Counter-trace: the whole mlink request-bit loop with `fhi > wlo + elo`

Transport run, real INITs: `uq` reads `req` 1 tick, `en` 1 tick, its own
`done` 3 ticks (the slow feedback); `ux` reads `done` 1 tick, `ack = 0`.
`req` rises at 5 (token `0 -> 1`). `fhi = 3 > wlo + elo = 1 + 1`: `done`
rises at 6, ux closes at 7, the latch closes at 8 reading `done`(5) = 0:
`done` falls back at 8, ux reopens, and the loop oscillates with period 3. -/

def qReq : Sig := fun t => decide (5 ≤ t)
def qDone : Sig := fun t => if t < 6 then false else decide ((t - 6) % 3 ≠ 2)
def qEn : Sig := fun t => if t < 7 then true else !(qDone (t - 1))

theorem lat_bin (d e q : Bool) : lutB LibEndMemMlink.INIT_LAT [d, e, q, false, false, false] =
    (if e then d else q) := by
  cases d <;> cases e <;> cases q <;> decide
theorem ux_bin (d a : Bool) : lutB LibEndMemMlink.INIT_UX [d, a, false] = (d == a) := by
  cases d <;> cases a <;> decide

theorem qDone_transport : Transport LibEndMemMlink.INIT_LAT [(qReq, 1), (qEn, 1), (qDone, 3),
    (zero, 0), (zero, 0), (zero, 0)] qDone := by
  intro t
  show qDone t = lutB _ [qReq (t - 1), qEn (t - 1), qDone (t - 3), false, false, false]
  rw [lat_bin]
  by_cases ht : t < 20
  · revert t; decide
  · have r1 : qReq (t - 1) = true := by simp [qReq]; omega
    have hk : (t - 6) % 3 = 0 ∨ (t - 6) % 3 = 1 ∨ (t - 6) % 3 = 2 := by omega
    have a1 : ¬ t < 6 := by omega
    have a2 : ¬ t - 1 < 7 := by omega
    have a3 : ¬ t - 1 - 1 < 6 := by omega
    have a4 : ¬ t - 3 < 6 := by omega
    simp only [qDone, qEn, a1, a2, a3, a4, ↓reduceIte, r1]
    rcases hk with h | h | h
    · have e1 : (t - 1 - 1 - 6) % 3 = 1 := by omega
      have e2 : (t - 3 - 6) % 3 = 0 := by omega
      simp [h, e1, e2]
    · have e1 : (t - 1 - 1 - 6) % 3 = 2 := by omega
      simp [h, e1]
    · have e1 : (t - 1 - 1 - 6) % 3 = 0 := by omega
      have e2 : (t - 3 - 6) % 3 = 2 := by omega
      simp [h, e1, e2]

theorem qEn_transport : Transport LibEndMemMlink.INIT_UX [(qDone, 1), (zero, 0), (zero, 0)] qEn := by
  intro t
  show qEn t = lutB _ [qDone (t - 1), false, false]
  rw [ux_bin]
  by_cases ht : t < 7
  · have : qDone (t - 1) = false := by simp [qDone]; omega
    simp [qEn, ht, this]
  · simp [qEn, ht]

/-- **Exactness witness.** Both gate relations hold (real INITs, transport
delays inside the windows), the old value is held before 6 and `ack` is
stable, H_QFB_FIRST_T's clean form fails by one tick (`3 > 1 + 1`), and
`done` makes a runt (1 at 6, 0 at 8) and keeps oscillating. -/
theorem qfb_counter :
    Gate LibEndMemMlink.INIT_LAT [(qReq, 1, 1), (qEn, 1, 1), (qDone, 3, 3),
      (zero, 0, 0), (zero, 0, 0), (zero, 0, 0)] qDone ∧
    Gate LibEndMemMlink.INIT_UX [(qDone, 1, 1), (zero, 0, 0), (zero, 0, 0)] qEn ∧
    ¬ (3 ≤ 1 + 1) ∧
    qDone 5 = false ∧ qDone 6 = true ∧ qDone 8 = false ∧
    (∀ k, qDone (6 + 3 * k) = true ∧ qDone (8 + 3 * k) = false) := by
  refine ⟨transport_gate _ [(qReq, 1, 1, 1), (qEn, 1, 1, 1), (qDone, 3, 3, 3),
      (zero, 0, 0, 0), (zero, 0, 0, 0), (zero, 0, 0, 0)] qDone (by simp) qDone_transport,
    transport_gate _ [(qDone, 1, 1, 1), (zero, 0, 0, 0), (zero, 0, 0, 0)] qEn (by simp)
      qEn_transport, by decide, by decide, by decide, by decide, ?_⟩
  intro k
  constructor
  · have a : ¬ 6 + 3 * k < 6 := by omega
    simp [qDone, a]
  · have a : ¬ 8 + 3 * k < 6 := by omega
    have b : (8 + 3 * k - 6) % 3 = 2 := by omega
    simp [qDone, a, b]

/-- The same environment with `fhi = 2 = wlo + elo`: one clean edge at 6. -/
def jDone : Sig := fun t => decide (6 ≤ t)
def jEn : Sig := fun t => decide (t < 7)

theorem qfb_clean :
    Gate LibEndMemMlink.INIT_LAT [(qReq, 1, 1), (jEn, 1, 1), (jDone, 2, 2),
      (zero, 0, 0), (zero, 0, 0), (zero, 0, 0)] jDone ∧
    Gate LibEndMemMlink.INIT_UX [(jDone, 1, 1), (zero, 0, 0), (zero, 0, 0)] jEn ∧
    (2 ≤ 1 + 1) ∧ ∀ t, jDone t = decide (6 ≤ t) := by
  refine ⟨transport_gate _ [(qReq, 1, 1, 1), (jEn, 1, 1, 1), (jDone, 2, 2, 2),
      (zero, 0, 0, 0), (zero, 0, 0, 0), (zero, 0, 0, 0)] jDone (by simp) ?_,
    transport_gate _ [(jDone, 1, 1, 1), (zero, 0, 0, 0), (zero, 0, 0, 0)] jEn (by simp) ?_,
    by decide, fun _ => rfl⟩
  · intro t
    show jDone t = lutB _ [qReq (t - 1), jEn (t - 1), jDone (t - 2), false, false, false]
    rw [lat_bin]
    by_cases ht : t < 20
    · revert t; decide
    · have e1 : jEn (t - 1) = false := by simp [jEn]; omega
      have e2 : jDone (t - 2) = true := by simp [jDone]; omega
      have e3 : jDone t = true := by simp [jDone]; omega
      rw [e1, e2, e3]; rfl
  · intro t
    show jEn t = lutB _ [jDone (t - 1), false, false]
    rw [ux_bin]
    simp only [jEn, jDone]
    by_cases h : t < 7
    · have : ¬ 6 ≤ t - 1 := by omega
      simp [h, this]
    · have : 6 ≤ t - 1 := by omega
      simp [h, this]

/-! ## 6. `bd_mem`: RAM clock pulse widths against the datasheet -/

namespace MemPort
open LibEndMemMlink
variable (m : LibEndMemMlink.MemPort)

/-- **Clock high width meets `tPWH`** whenever the handshake round trip's
minimum, less the setup line's spread, covers it:
`tPWH + dsHi ≤ dsLo + dcLo + dsLoF` (from `clk_high_width`). -/
theorem clk_high_ok (tPWH : Nat) (h : tPWH + m.dsHi ≤ m.dsLo + m.dcLo + m.dsLoF) :
    m.tClkR + tPWH ≤ m.tClkF := by
  have := m.clk_high_width
  have := m.H_SETUP_LINE
  have := m.H_CO_LINE
  have := m.H_FOUR_PHASE_ENV
  omega

/-- **Clock low width meets `tPWL`** whenever `tPWL ≤ dcLoF + dsLo` (from
`rtz_serialised`). -/
theorem clk_low_ok (tPWL : Nat) (h : tPWL ≤ m.dcLoF + m.dsLo) :
    m.tClkF + tPWL ≤ m.tClkR2 := by
  have := m.rtz_serialised
  omega

end MemPort

/-! ## 7. `bd_link_dctl.ult`: the gate-level content of H_LT_FIRST (partial)

`ult` is `LUT6 64'h0101...01` (`I0 b, I1 a, I2 gate (= ack_out with BROAD,
else 0)`, I3..I5 tied 0): `lt = ~b · ~a · ~gate` (`LinkHandshake.dctl_eqs`).
What is proved here is the LUT-level part of the header's assumption, NOT
its link to the untimed schedule `ltFirst` (see the notes):
* `ult_kleene`: the Kleene closure is the Kleene NOR (all 27 rows).
* `lt_settles`: inputs stable at their drivers on `[T, T']` give
  `lt = NOR` on `[T + max hi, T' + min lo]`.
* `lt_first_window`: if the next change of any `ult` input (a neighbour's
  response through `b`/`a`/`ack_out`) is no earlier than `T + R`
  (**H_ROUND_TRIP**), and **H_LT_FIRST_T** `H + wlt_hi ≤ R + L + wlt_lo`
  (`H`/`L` the max/min of the three input windows, `[wlt_lo, wlt_hi]` the
  `lt -> consumer pin` route), then every consumer pin of `lt` reads the
  settled value at some instant before the next input change can reach it:
  the stale value never survives a whole handshake.
* `lt_opposite_x`: two inputs moving in opposite directions within `ult`'s
  window give `x` (a possible glitch on the latch enable): the hazard
  `LinkHandshake.dctl_si_hazard` exhibits in the untimed model.
-/

section dctl

theorem ult_kleene : ∀ b a g : K3,
    lutK LinkHandshake.INIT_DLT [b, a, g, .f, .f, .f] =
      (if b = .t ∨ a = .t ∨ g = .t then .f else if b = .f ∧ a = .f ∧ g = .f then .t else .x) := by
  decide

theorem lt_settles {b a g lt : Sig} {blo bhi alo ahi glo ghi : Nat}
    (hg : Gate LinkHandshake.INIT_DLT [(b, blo, bhi), (a, alo, ahi), (g, glo, ghi),
      (zero, 0, 0), (zero, 0, 0), (zero, 0, 0)] lt)
    (hbw : blo ≤ bhi) (haw : alo ≤ ahi) (hgw : glo ≤ ghi)
    (vb va vg : Bool) (T T' : Nat)
    (hb : StableOn b vb T T') (ha : StableOn a va T T') (hgg : StableOn g vg T T') :
    StableOn lt (!(vb || va || vg)) (T + max bhi (max ahi ghi)) (T' + min blo (min alo glo)) := by
  intro t h1 h2
  apply hg t
  show lutK _ [winK b blo bhi t, winK a alo ahi t, winK g glo ghi t,
    winK zero 0 0 t, winK zero 0 0 t, winK zero 0 0 t] = _
  rw [winK_zero, win_of_stable hbw hb (by omega) (by omega),
    win_of_stable haw ha (by omega) (by omega), win_of_stable hgw hgg (by omega) (by omega),
    ult_kleene]
  cases vb <;> cases va <;> cases vg <;> rfl

/-- **H_LT_FIRST, the LUT-level timed reading (sufficient for the stated
conclusion).** With the three `ult` inputs stable on `[T, T']`, the next
change no earlier than `T + R` (H_ROUND_TRIP, `R ≥ 1`), and
`H + wlt_hi ≤ R + L + wlt_lo`, the consumer pin (reading `lt` through
`[wlt_lo, wlt_hi]`) sees the settled NOR at instant `T + H + wlt_hi`. -/
theorem lt_first_window {b a g lt : Sig} {blo bhi alo ahi glo ghi wlt_lo wlt_hi : Nat}
    (hg : Gate LinkHandshake.INIT_DLT [(b, blo, bhi), (a, alo, ahi), (g, glo, ghi),
      (zero, 0, 0), (zero, 0, 0), (zero, 0, 0)] lt)
    (hbw : blo ≤ bhi) (haw : alo ≤ ahi) (hgw : glo ≤ ghi) (hww : wlt_lo ≤ wlt_hi)
    (vb va vg : Bool) (T R : Nat) (hR : 1 ≤ R)
    (H_ROUND_TRIP : StableOn b vb T (T + R - 1) ∧ StableOn a va T (T + R - 1) ∧
      StableOn g vg T (T + R - 1))
    (H_LT_FIRST_T : max bhi (max ahi ghi) + wlt_hi ≤ R - 1 + min blo (min alo glo) + wlt_lo) :
    winK lt wlt_lo wlt_hi (T + max bhi (max ahi ghi) + wlt_hi) = K3.ofBool (!(vb || va || vg)) := by
  have hs := lt_settles hg hbw haw hgw vb va vg T (T + R - 1)
    H_ROUND_TRIP.1 H_ROUND_TRIP.2.1 H_ROUND_TRIP.2.2
  exact win_of_stable hww hs (by omega) (by omega)

/-- `b` falling while `a` rises inside the window (static-0 of the true
function before and after): the closure is `x`, a possible glitch on the
latch enable; with one input definitely high the other's edge is masked. -/
theorem lt_opposite_x : lutK LinkHandshake.INIT_DLT [.x, .x, .f, .f, .f, .f] = .x ∧
    lutK LinkHandshake.INIT_DLT [.x, .t, .f, .f, .f, .f] = .f := by decide

end dctl

end Formal.Cells.ConstraintsMore
