import Formal.Net.Prelim

/-!
# Track 8a: four-phase bundled-data channels and pipeline composition

Discrete time (`Nat`, one tick = 1 ps), `Formal.Net.Prelim` traces.

* `Chan`: a request wire, an acknowledge wire and a data bus (`Nat → Nat`,
  the bus read as a number; a W-bit bus is a value `< 2^W`, nothing here
  depends on W).
* Protocol (LIBRARY.md, "The four-phase bundled-data protocol"):
  `req↑ ack↑ req↓ ack↓`, no phase skipped, no new request before the previous
  ack fell. Split into the two parties' obligations, one step `t → t+1` at a
  time:
  - `SendStep c t`: the sender moves `req` only when `req = ack`
    (raise after ack fell, lower after ack rose);
  - `RecvStep c t`: the receiver moves `ack` only when `ack ≠ req`.
  `phase_step` proves the two rules give exactly the 4-cycle order.
* Bundling. Two forms:
  - `Bundled m h c` (the LIBRARY.md form): data stable from `m` ticks before
    `req↑` until `h` ticks after the matching `ack↓`.
  - `SetupHold m h c` (what a transparent-latch consumer actually needs):
    data stable on `[e+1-m, e+h]` around every `ack↓` step `e` (the close).
  `bundled_setupHold` derives the second from the first plus a control-only
  timing fact (the matching `req↑` is early enough).
* `StageSpec m h i o`: assume-guarantee spec of one stage. Protocol part is
  *causal* (guarantee at step `t` from the assumptions at steps `< t`); data
  part: if the input link meets `SetupHold m h`, the stage `Transfers` tokens
  in order.
* `pipeline_protocol`: n stages + environment ⇒ every link obeys the protocol.
  The assume-guarantee reasoning is circular (stage k's receiver behaviour
  needs stage k-1's sender behaviour, which needs stage k's ...). It is broken
  by strong induction on time, which is sound because each guarantee at step
  `t` uses the assumptions only at steps `< t`.
* `pipeline_fifo`, `pipeline_prefix`, `pipeline_count`: the pipeline is a
  FIFO: the k-th token out equals the k-th token in, and the number of
  tokens out never exceeds the number in (safety).
-/

namespace Formal.Net.Handshake
open Formal.Net

structure Chan where
  req : Trace
  ack : Trace
  dat : Nat → Nat

/-! ## Protocol -/

/-- Sender's obligation at step `t → t+1`. -/
def SendStep (c : Chan) (t : Nat) : Prop := c.req (t + 1) ≠ c.req t → c.req t = c.ack t
/-- Receiver's obligation at step `t → t+1`. -/
def RecvStep (c : Chan) (t : Nat) : Prop := c.ack (t + 1) ≠ c.ack t → c.ack t ≠ c.req t
/-- Reset state: both wires low. -/
def Init (c : Chan) : Prop := c.req 0 = false ∧ c.ack 0 = false
def Rules (c : Chan) (t : Nat) : Prop := SendStep c t ∧ RecvStep c t
def Protocol (c : Chan) : Prop := Init c ∧ ∀ t, SendStep c t ∧ RecvStep c t

/-- The four phases: 0 = idle (00), 1 = requested (10), 2 = acknowledged (11),
3 = returning (01). -/
def phase : Bool → Bool → Nat
  | false, false => 0
  | true, false => 1
  | true, true => 2
  | false, true => 3

theorem phase_step_bool : ∀ r a r' a' : Bool, (r' ≠ r → r = a) → (a' ≠ a → a ≠ r) →
    phase r' a' = phase r a ∨ phase r' a' = (phase r a + 1) % 4 := by decide

/-- The two rules give exactly the order `req↑ ack↑ req↓ ack↓`: every step
keeps the phase or advances it by one (mod 4); no phase is skipped and the two
wires never move in the same step. -/
theorem phase_step {c : Chan} {t : Nat} (hs : SendStep c t) (hr : RecvStep c t) :
    phase (c.req (t+1)) (c.ack (t+1)) = phase (c.req t) (c.ack t) ∨
    phase (c.req (t+1)) (c.ack (t+1)) = (phase (c.req t) (c.ack t) + 1) % 4 :=
  phase_step_bool _ _ _ _ hs hr

/-- No new request before the previous ack has fallen. -/
theorem req_rise_ack_low {c : Chan} {t : Nat} (hs : SendStep c t)
    (h0 : c.req t = false) (h1 : c.req (t+1) = true) : c.ack t = false := by
  have := hs (by rw [h0, h1]; decide); rw [← this, h0]

/-- ack falls only after req fell. -/
theorem ack_fall_req_low {c : Chan} {t : Nat} (hr : RecvStep c t)
    (h0 : c.ack t = true) (h1 : c.ack (t+1) = false) : c.req t = false := by
  have := hr (by rw [h0, h1]; decide)
  rw [h0] at this; cases h : c.req t <;> simp_all

/-! ## Counting events -/

/-- Number of steps `s < t` with `f s`. -/
def cnt (f : Nat → Bool) : Nat → Nat
  | 0 => 0
  | t + 1 => cnt f t + if f t then 1 else 0

def fallB (s : Trace) (t : Nat) : Bool := s t && !s (t + 1)
def riseB (s : Trace) (t : Nat) : Bool := !s t && s (t + 1)

theorem cnt_mono (f : Nat → Bool) {a b : Nat} (h : a ≤ b) : cnt f a ≤ cnt f b := by
  induction b with
  | zero => rw [Nat.le_zero.mp h]; exact Nat.le_refl _
  | succ b ih =>
    rcases Nat.lt_or_eq_of_le h with h | h
    · have := ih (Nat.le_of_lt_succ h); simp only [cnt]; omega
    · rw [h]; exact Nat.le_refl _

theorem cnt_succ_of {f : Nat → Bool} {e : Nat} (h : f e = true) :
    cnt f (e + 1) = cnt f e + 1 := by simp [cnt, h]

/-- If `k+1` events happened before `t`, the `k`-th one happened at some `e < t`. -/
theorem cnt_witness (f : Nat → Bool) : ∀ t k, cnt f t = k + 1 →
    ∃ e, e < t ∧ f e = true ∧ cnt f e = k := by
  intro t
  induction t with
  | zero => intro k h; simp [cnt] at h
  | succ t ih =>
    intro k h
    by_cases hf : f t = true
    · refine ⟨t, Nat.lt_succ_self t, hf, ?_⟩
      simp [cnt, hf] at h; exact h
    · simp [cnt, hf] at h
      obtain ⟨e, he, hfe, hc⟩ := ih k h
      exact ⟨e, Nat.lt_succ_of_lt he, hfe, hc⟩

/-- The last fall of a signal that is low at `t` and has fallen `k+1` times
before `t`: it is the `k`-th fall, and the signal stays low from then to `t`. -/
theorem last_fall (s : Trace) : ∀ t k, s t = false → cnt (fallB s) t = k + 1 →
    ∃ e, e < t ∧ fallB s e = true ∧ cnt (fallB s) e = k ∧
      ∀ u, e < u → u ≤ t → s u = false := by
  intro t
  induction t with
  | zero => intro k _ h; simp [cnt] at h
  | succ t ih =>
    intro k hlow h
    by_cases hf : fallB s t = true
    · refine ⟨t, Nat.lt_succ_self t, hf, ?_, ?_⟩
      · simp [cnt, hf] at h; exact h
      · intro u h1 h2; have : u = t + 1 := by omega
        rw [this]; exact hlow
    · have hst : s t = false := by
        simp [fallB, hlow] at hf; exact hf
      simp [cnt, hf] at h
      obtain ⟨e, he, hfe, hc, hl⟩ := ih k hst h
      refine ⟨e, Nat.lt_succ_of_lt he, hfe, hc, ?_⟩
      intro u h1 h2
      rcases Nat.lt_or_eq_of_le h2 with h2 | h2
      · exact hl u h1 (Nat.le_of_lt_succ h2)
      · rw [h2]; exact hlow

/-- The last rise of a signal that starts low and is high at `t`. -/
theorem last_rise (s : Trace) (h0 : s 0 = false) : ∀ t, s t = true →
    ∃ r, r < t ∧ s r = false ∧ s (r + 1) = true ∧ ∀ u, r < u → u ≤ t → s u = true := by
  intro t
  induction t with
  | zero => intro h; rw [h0] at h; cases h
  | succ t ih =>
    intro h
    cases hst : s t
    · exact ⟨t, Nat.lt_succ_self t, hst, h, fun u h1 h2 => by
        have : u = t + 1 := by omega
        rw [this]; exact h⟩
    · obtain ⟨r, hr, h1, h2, hl⟩ := ih hst
      refine ⟨r, Nat.lt_succ_of_lt hr, h1, h2, fun u hu1 hu2 => ?_⟩
      rcases Nat.lt_or_eq_of_le hu2 with hu2 | hu2
      · exact hl u hu1 (Nat.le_of_lt_succ hu2)
      · rw [hu2]; exact h

theorem falls_bool : ∀ (X Y : Nat) (r a r' a' : Bool),
    X = Y + (if r = false ∧ a = true then 1 else 0) → (r' ≠ r → r = a) → (a' ≠ a → a ≠ r) →
    X + (if (r && !r') = true then 1 else 0) =
      Y + (if (a && !a') = true then 1 else 0) + (if r' = false ∧ a' = true then 1 else 0) := by
  intro X Y r a r' a'
  cases r <;> cases a <;> cases r' <;> cases a' <;> simp <;> omega

/-- Count invariant of a channel obeying the protocol: falls of `req` and of
`ack` before `t` differ by one exactly in phase 3 (`req = 0, ack = 1`). -/
theorem falls_inv {c : Chan} (hp : Protocol c) : ∀ t,
    cnt (fallB c.req) t = cnt (fallB c.ack) t + (if c.req t = false ∧ c.ack t = true then 1 else 0) := by
  intro t
  induction t with
  | zero => simp [cnt, hp.1.1, hp.1.2]
  | succ t ih =>
    simp only [cnt, fallB]
    exact falls_bool _ _ _ _ _ _ ih (hp.2 t).1 (hp.2 t).2

/-! ## Tokens and bundling -/

/-- The `k`-th transaction of `c` closes at step `e`: `ack` falls at `e`
(`ack e = 1`, `ack (e+1) = 0`) and `k` falls happened before. The token's value
is `c.dat e`, the bus at the close (what a latch consumer keeps). -/
def TokAt (c : Chan) (k e : Nat) : Prop := fallB c.ack e = true ∧ cnt (fallB c.ack) e = k

/-- LIBRARY.md bundling with named margins: data stable from `m` ticks before
each `req↑` (step `t`) until `h` ticks after the matching `ack↓` (step `e`, the
first ack fall after `t`). -/
def Bundled (m h : Nat) (c : Chan) : Prop :=
  ∀ t e, riseB c.req t = true → t < e → fallB c.ack e = true →
    (∀ u, t ≤ u → u < e → fallB c.ack u = false) →
    ∀ s, t + 1 - m ≤ s → s ≤ e + h → c.dat s = c.dat e

/-- What a transparent-latch consumer needs (setup `m`, hold `h`) around each
close step `e` (`ack↓`). -/
def SetupHold (m h : Nat) (c : Chan) : Prop :=
  ∀ e, fallB c.ack e = true → ∀ s, e + 1 - m ≤ s → s ≤ e + h → c.dat s = c.dat e

/-- Control-only timing fact: every close step `e` comes at least `w` steps
after the request that opened its transaction (the last `req↑` before it). -/
def OpenWidth (w : Nat) (c : Chan) : Prop :=
  ∀ t e, riseB c.req t = true → t < e → fallB c.ack e = true →
    (∀ u, t ≤ u → u < e → fallB c.ack u = false) → t + w ≤ e

/-- Classic bundling with margin `m'` plus a long enough handshake (`m ≤ m' + w`)
gives the latch's setup/hold. -/
theorem bundled_setupHold {m m' h w : Nat} {c : Chan} (hp : Protocol c)
    (hb : Bundled m' h c) (hw : OpenWidth w c) (hm : m ≤ m' + w) : SetupHold m h c := by
  intro e he s hs1 hs2
  have hae : c.ack e = true := by simp [fallB] at he; exact he.1
  -- last ack rise before e
  obtain ⟨ra, hra, ha0, ha1, hal⟩ := last_rise c.ack hp.1.2 e hae
  have hreq_ra : c.req ra = true := by
    have := (hp.2 ra).2 (by rw [ha0, ha1]; decide)
    rw [ha0] at this; cases h : c.req ra <;> simp_all
  obtain ⟨rr, hrr, hr0, hr1, hrl⟩ := last_rise c.req hp.1.1 ra hreq_ra
  have hack_rr : c.ack rr = false := req_rise_ack_low (hp.2 rr).1 hr0 hr1
  have hnofall : ∀ u, rr ≤ u → u < e → fallB c.ack u = false := by
    intro u h1 h2
    by_cases hu : u < ra
    · -- req high on (rr, ra], so ack cannot fall while req high (needs req low)
      rcases Nat.lt_or_eq_of_le h1 with h1 | h1
      · have hq : c.req u = true := hrl u h1 (Nat.le_of_lt hu)
        cases hau : c.ack u
        · simp [fallB, hau]
        · cases hau1 : c.ack (u+1)
          · have := ack_fall_req_low (hp.2 u).2 hau hau1; rw [hq] at this; cases this
          · simp [fallB, hau, hau1]
      · subst h1; simp [fallB, hack_rr]
    · have : c.ack (u + 1) = true := hal (u+1) (by omega) (by omega)
      simp [fallB, this]
  have hrise : riseB c.req rr = true := by simp [riseB, hr0, hr1]
  have hre : rr < e := by omega
  have hwid := hw rr e hrise hre he hnofall
  exact hb rr e hrise hre he hnofall s (by omega) hs2

/-- The stage passes tokens in order: every token out was the token in with
the same index, closed earlier, with the same value. -/
def Transfers (i o : Chan) : Prop :=
  ∀ k e', TokAt o k e' → ∃ e, e < e' ∧ TokAt i k e ∧ o.dat e' = i.dat e

theorem transfers_trans {a b c : Chan} (h1 : Transfers a b) (h2 : Transfers b c) :
    Transfers a c := by
  intro k e'' hk
  obtain ⟨e', he', hk', hv'⟩ := h2 k e'' hk
  obtain ⟨e, he, hk0, hv⟩ := h1 k e' hk'
  exact ⟨e, Nat.lt_trans he he', hk0, hv'.trans hv⟩

/-- Safety in counts: no more tokens out than in, at every time. -/
theorem transfers_count {i o : Chan} (h : Transfers i o) :
    ∀ t, cnt (fallB o.ack) t ≤ cnt (fallB i.ack) t := by
  intro t
  cases hk : cnt (fallB o.ack) t with
  | zero => exact Nat.zero_le _
  | succ k =>
    obtain ⟨e', he', hf', hc'⟩ := cnt_witness _ t k hk
    obtain ⟨e, he, ⟨hf, hc⟩, _⟩ := h k e' ⟨hf', hc'⟩
    have := cnt_mono (fallB i.ack) (show e + 1 ≤ t by omega)
    rw [cnt_succ_of hf, hc] at this; exact this

/-! ## Stage spec (assume-guarantee) -/

/-- One stage between input link `i` and output link `o`.
* `ag`: CAUSAL assume-guarantee. If up to (excluding) step `t` both links
  obeyed both rules (the environment's: `SendStep i`, `RecvStep o`; and the
  stage's own earlier guarantees), the stage obeys `RecvStep i` and
  `SendStep o` at step `t`. A stage whose gates see delayed copies of their
  inputs needs all four (`HandshakeMuller.mullerW_stageSpec`).
* `initIn`, `initOut`: reset leaves `ack_in` and `req_out` low.
* `xfer`: with the protocol on both links and setup/hold `(m, h)` on the input
  link, tokens are transferred in order. -/
structure StageSpec (m h : Nat) (i o : Chan) : Prop where
  ag : ∀ t, (∀ s, s < t → Rules i s ∧ Rules o s) → RecvStep i t ∧ SendStep o t
  initIn : i.ack 0 = false
  initOut : o.req 0 = false
  xfer : Protocol i → Protocol o → SetupHold m h i → Transfers i o

/-! ## The pipeline -/

/-- A linear pipeline of `n` stages over links `ch 0 .. ch n`, stage `j`
between `ch j` and `ch (j+1)`, with a source on `ch 0` and a sink on `ch n`.
The environment is also causal assume-guarantee. -/
structure Pipeline (m h n : Nat) (ch : Nat → Chan) : Prop where
  stage : ∀ j, j < n → StageSpec m h (ch j) (ch (j + 1))
  srcInit : (ch 0).req 0 = false
  snkInit : (ch n).ack 0 = false
  src : ∀ t, (∀ s, s < t → Rules (ch 0) s) → SendStep (ch 0) t
  snk : ∀ t, (∀ s, s < t → Rules (ch n) s) → RecvStep (ch n) t

/-- Every link of the pipeline obeys the four-phase protocol.
The circular assume-guarantee argument is discharged by strong induction on
time: the claim for all links at step `t` uses the claim for all links at steps
`< t` only. -/
theorem pipeline_protocol {m h n : Nat} {ch : Nat → Chan} (P : Pipeline m h n ch) :
    ∀ j, j ≤ n → Protocol (ch j) := by
  have step : ∀ t, ∀ j, j ≤ n → SendStep (ch j) t ∧ RecvStep (ch j) t := by
    intro t
    induction t using Nat.strongRecOn with
    | _ t ih =>
      intro j hj
      constructor
      · cases j with
        | zero => exact P.src t (fun s hs => ih s hs 0 (Nat.zero_le _))
        | succ j =>
          exact ((P.stage j (by omega)).ag t (fun s hs =>
            ⟨ih s hs j (by omega), ih s hs (j+1) hj⟩)).2
      · by_cases hjn : j = n
        · subst hjn; exact P.snk t (fun s hs => ih s hs j (Nat.le_refl _))
        · exact ((P.stage j (by omega)).ag t (fun s hs =>
            ⟨ih s hs j hj, ih s hs (j+1) (by omega)⟩)).1
  intro j hj
  refine ⟨⟨?_, ?_⟩, fun t => step t j hj⟩
  · cases j with
    | zero => exact P.srcInit
    | succ j => exact (P.stage j (by omega)).initOut
  · by_cases hjn : j = n
    · subst hjn; exact P.snkInit
    · exact (P.stage j (by omega)).initIn

/-- FIFO safety: if the input link and every internal link meets its
setup/hold obligation (`SetupHold m h (ch j)` for `j < n`), the pipeline
(`n ≥ 1` stages) transfers tokens from `ch 0` to `ch n` in order. -/
theorem pipeline_fifo {m h n : Nat} {ch : Nat → Chan} (P : Pipeline m h n ch)
    (H_LINK_SETUP_HOLD : ∀ j, j < n → SetupHold m h (ch j)) (hn : 0 < n) :
    Transfers (ch 0) (ch n) := by
  have hp := pipeline_protocol P
  have hst : ∀ j, j < n → Transfers (ch j) (ch (j + 1)) := fun j hj =>
    (P.stage j hj).xfer (hp j (by omega)) (hp (j+1) hj) (H_LINK_SETUP_HOLD j hj)
  have : ∀ j, j < n → Transfers (ch 0) (ch (j + 1)) := by
    intro j
    induction j with
    | zero => intro h0; exact hst 0 h0
    | succ j ih => intro hj; exact transfers_trans (ih (by omega)) (hst (j+1) hj)
  have h := this (n - 1) (by omega)
  rwa [show n - 1 + 1 = n by omega] at h

/-- The output value sequence is a prefix of the input value sequence:
the `k`-th token out (closing at `e'`) is the `k`-th token in, and the
number of tokens out by any time is at most the number in. -/
theorem pipeline_prefix {m h n : Nat} {ch : Nat → Chan} (P : Pipeline m h n ch)
    (H_LINK_SETUP_HOLD : ∀ j, j < n → SetupHold m h (ch j)) (hn : 0 < n) :
    (∀ t, cnt (fallB (ch n).ack) t ≤ cnt (fallB (ch 0).ack) t) ∧
    (∀ k e', TokAt (ch n) k e' → ∃ e, e < e' ∧ TokAt (ch 0) k e ∧ (ch n).dat e' = (ch 0).dat e) :=
  let T := pipeline_fifo P H_LINK_SETUP_HOLD hn
  ⟨transfers_count T, T⟩

end Formal.Net.Handshake
