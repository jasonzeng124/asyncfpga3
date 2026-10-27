import Formal.Net.Handshake
import Formal.Cells.Prelim

/-!
# Track 8a: the Muller stage (`bd_link`, default build) meets `StageSpec`

`cells/rtl/bd_link.v` (no `BD_LINK_DC`): `c = bd_c2n(req_in, ack_out, rst)`,
`bd_latch(d = data_in, en = c, q = data_out)`, `req_out = Δ_DELAY(c)`,
`ack_in = Δ_DACK(c)`. We take `DELAY = DACK = 0` (the defaults).

Gate model of one stage, every assumption a named field of `MullerStage`:

* `H_NODE`: `req_out` and `ack_in` ARE the node `c` (DELAY = DACK = 0 and
  zero wire skew between the two branches of the fork of `c`: an isochronic
  fork). Fidelity: the routed fork has two different wires; skew of a few
  hundred ps is normal. The receiver-side and sender-side views of `c` differ
  for that long; the model does not see it. Test: SDF INTERCONNECT of the
  `c` net, `req_out` vs `ack_in` sinks.
* `H_RESET`: `c 0 = 0` (rst held, then released; rst is I3 of the LUT and is
  0 for every `t` the model covers).
* `H_CEL_SI`: at each step the C-element node either keeps its value or takes
  the value of its LUT function, evaluated with `Formal.Cells.Prelim.lutB` on
  the REAL INIT of `bd_c2n` (`64'h00B2_00B2_00B2_00B2`, pins
  `I0 = req_in, I1 = ack_out, I2 = c, I3 = rst = 0`). This is the
  speed-independent (unbounded inertial gate delay, zero wire delay) model:
  arbitrary but atomic gate delays, binary values, no runts. It is weaker than
  H_BOUNDED_DELAY on the delay (any delay is allowed, so all safety results
  hold for every delay) and stronger on wires (zero wire delay). Fidelity: the
  binary LUT function is the silicon's for settled inputs (shard B,
  `CElemFn`); the wire-delay idealisation is what makes the protocol
  guarantees below unconditional (see notes).
* `H_LATCH m h`: the latch, as an abstract cell contract: if the latch enable
  `c` falls at step `e` and its data input is stable on `[e+1-m, e+h]`, then
  its output equals `d e` at every later time until the enable rises again.
  This is the contract shard B proves for the real LUT latch in
  `Formal/Cells/Latch.lean` (`holds_value_bin`, with `m` ≥ the loop delay `L`
  and `h` covering the enable's fall at the pin), NOT re-proved here; the
  bridge is not mechanised (different value types: B uses `K3` per bit, we a
  bus value). Fidelity: inherits B's; plus it lumps the W bits of the bus,
  which needs the enable fan-out skew (DACK, rule H) inside `h`.
-/

namespace Formal.Net.Handshake
open Formal.Net Formal.Cells

/-- `bd_c2n` INIT, verbatim from `cells/rtl/bd_ce.v`. -/
def INIT_c2n : Nat := 0x00B600B600B600B6 -- MUTANT M6 bit 2 flipped

/-- The C-element node function, from the INIT: pins `[req_in, ack_out, c, rst=0]`. -/
def celN (r a q : Bool) : Bool := lutB INIT_c2n [r, a, q, false, false, false]

/-- The INIT is `C(req_in, ~ack_out)` (majority with feedback). -/
theorem celN_eq : ∀ r a q : Bool, celN r a q = ((r && !a) || (r && q) || (!a && q)) := by
  decide

structure MullerStage (m h : Nat) (i o : Chan) : Prop where
  H_NODE : ∀ t, o.req t = i.ack t
  H_RESET : i.ack 0 = false
  H_CEL_SI : ∀ t, i.ack (t + 1) = i.ack t ∨ i.ack (t + 1) = celN (i.req t) (o.ack t) (i.ack t)
  H_LATCH : ∀ e, fallB i.ack e = true →
    (∀ s, e + 1 - m ≤ s → s ≤ e + h → i.dat s = i.dat e) →
    ∀ s, e < s → (∀ u, e < u → u ≤ s → i.ack u = false) → o.dat s = i.dat e

/-- The node changes only when it is excited, i.e. when `req_in ≠ c` and
`ack_out = c` (`C(r, ~a)` with `r = ~a ≠ c`). -/
theorem cel_change : ∀ r a q q' : Bool, (q' = q ∨ q' = celN r a q) → q' ≠ q → q ≠ r ∧ q = a := by
  decide

/-- The data half of a stage needs only the node identity and the latch
contract (no C-element model): the downstream close of token `k` happens while
the upstream latch is closed on token `k`. -/
theorem node_latch_transfers {m h : Nat} {i o : Chan}
    (H_NODE : ∀ t, o.req t = i.ack t)
    (H_LATCH : ∀ e, fallB i.ack e = true →
      (∀ s, e + 1 - m ≤ s → s ≤ e + h → i.dat s = i.dat e) →
      ∀ s, e < s → (∀ u, e < u → u ≤ s → i.ack u = false) → o.dat s = i.dat e) :
    Protocol o → SetupHold m h i → Transfers i o := by
    intro hpo hsh k e' ⟨hf', hc'⟩
    -- at the downstream close, the upstream node is low (ack falls only after req fell)
    have hao : o.ack e' = true := by simp [fallB] at hf'; exact hf'.1
    have hao1 : o.ack (e'+1) = false := by simp [fallB] at hf'; exact hf'.2
    have hreq : o.req e' = false := ack_fall_req_low (hpo.2 e').2 hao hao1
    have hlow : i.ack e' = false := by rw [← H_NODE]; exact hreq
    -- and has fallen exactly k+1 times
    have hinv := falls_inv hpo e'
    rw [hreq, hao] at hinv
    simp only [and_self, ite_true] at hinv
    have hcnt : cnt (fallB i.ack) e' = k + 1 := by
      have : cnt (fallB o.req) e' = cnt (fallB i.ack) e' := by
        have hfun : o.req = i.ack := funext H_NODE
        rw [hfun]
      omega
    obtain ⟨e, he, hfe, hce, hl⟩ := last_fall i.ack e' k hlow hcnt
    refine ⟨e, he, ⟨hfe, hce⟩, ?_⟩
    exact H_LATCH e hfe (hsh e hfe) e' he hl


/-- **The Muller stage satisfies the stage spec.** In this model the protocol
guarantees do not even use the causal assumption: `RecvStep i` and `SendStep o`
hold at every step outright (the circularity is vacuous here; see notes). -/
theorem muller_stageSpec {m h : Nat} {i o : Chan} (M : MullerStage m h i o) :
    StageSpec m h i o where
  ag := by
    intro t _
    have key : i.ack (t+1) ≠ i.ack t → i.ack t ≠ i.req t ∧ i.ack t = o.ack t :=
      cel_change _ _ _ _ (M.H_CEL_SI t)
    refine ⟨fun hc => (key hc).1, fun hc => ?_⟩
    simp only [M.H_NODE] at hc ⊢
    exact (key hc).2
  initIn := M.H_RESET
  initOut := by rw [M.H_NODE]; exact M.H_RESET
  xfer := fun _ hpo hsh => node_latch_transfers M.H_NODE M.H_LATCH hpo hsh

/-! ## The same stage with wire delay on the controller's input pins

`MullerStageW`: the C-element sees `req_in` and `ack_out` through wires of one
tick (`H_CEL_SI_W`; `c 1 = c 0` covers the first tick). Now the protocol
guarantees are NOT combinational invariants: a request withdrawn before the
stale copy reaches the pin would make `c` move against the protocol. The proof
uses the environment's rules AND the stage's own guarantee one step earlier:
the assume-guarantee loop is genuinely circular, and `pipeline_protocol`'s
induction on time is what discharges it. (A general bounded wire delay `≤ D`
needs the same argument over a window of `D` steps; not done.) -/

structure MullerStageW (m h : Nat) (i o : Chan) : Prop where
  H_NODE : ∀ t, o.req t = i.ack t
  H_RESET : i.ack 0 = false ∧ i.ack 1 = false
  H_CEL_SI_W : ∀ t, i.ack (t + 2) = i.ack (t + 1) ∨
    i.ack (t + 2) = celN (i.req t) (o.ack t) (i.ack (t + 1))
  H_LATCH : ∀ e, fallB i.ack e = true →
    (∀ s, e + 1 - m ≤ s → s ≤ e + h → i.dat s = i.dat e) →
    ∀ s, e < s → (∀ u, e < u → u ≤ s → i.ack u = false) → o.dat s = i.dat e

theorem mullerW_stageSpec {m h : Nat} {i o : Chan} (M : MullerStageW m h i o) :
    StageSpec m h i o where
  ag := by
    intro t ih
    cases t with
    | zero =>
      refine ⟨fun hc => absurd (M.H_RESET.2.trans M.H_RESET.1.symm) hc, fun hc => ?_⟩
      simp only [M.H_NODE] at hc
      exact absurd (M.H_RESET.2.trans M.H_RESET.1.symm) hc
    | succ t =>
      have key : i.ack (t+2) ≠ i.ack (t+1) → i.ack (t+1) ≠ i.req t ∧ i.ack (t+1) = o.ack t :=
        cel_change _ _ _ _ (M.H_CEL_SI_W t)
      have hi := ih t (by omega)
      refine ⟨fun hc => ?_, fun hc => ?_⟩
      · -- RecvStep i (t+1)
        have ⟨k1, _⟩ := key hc
        by_cases hr : i.req (t+1) = i.req t
        · rw [hr]; exact k1
        · exfalso
          have hs : i.req t = i.ack t := hi.1.1 hr
          have hcch : i.ack (t+1) ≠ i.ack t := by
            intro he; exact k1 (he.trans hs.symm)
          exact hi.1.2 hcch hs.symm
      · -- SendStep o (t+1)
        simp only [M.H_NODE] at hc ⊢
        have ⟨_, k2⟩ := key hc
        by_cases ha : o.ack (t+1) = o.ack t
        · rw [ha]; exact k2
        · exfalso
          have hr : o.ack t ≠ o.req t := hi.2.2 ha
          rw [M.H_NODE] at hr
          have hcch : i.ack (t+1) ≠ i.ack t := by
            intro he; exact hr (k2.symm.trans he)
          have hs := hi.2.1 (by simp only [M.H_NODE]; exact hcch)
          rw [M.H_NODE] at hs
          exact hr hs.symm
  initIn := M.H_RESET.1
  initOut := by rw [M.H_NODE]; exact M.H_RESET.1
  xfer := fun _ hpo hsh => node_latch_transfers M.H_NODE M.H_LATCH hpo hsh

/-! ## Internal links: data obligations reduce to control-event separations -/

/-- **H_SEP m** (per internal link, control only): the downstream close
(`o.ack↓` at `e'`) comes at least `m` ticks after the upstream close (`i.ack↓`
at `e`) that it follows. In `bd_pipe` this is the controller arc plus
`SDELAY` against the latch setup (rule I). -/
def Sep (m : Nat) (i o : Chan) : Prop :=
  ∀ e e', fallB i.ack e = true → fallB o.ack e' = true → e < e' →
    (∀ u, e < u → u ≤ e' → i.ack u = false) → e + m ≤ e'

/-- **H_HOLD h** (per internal link, control only): the upstream node does not
reopen (rise) within `h` ticks after the downstream close. In `bd_link` this is
what `DACK` lengthens (rule H). -/
def Hold (h : Nat) (i o : Chan) : Prop :=
  ∀ e' s, fallB o.ack e' = true → e' < s → s ≤ e' + h → i.ack s = false

/-- `Hold 1` is free in the speed-independent model (the upstream C-element
cannot rise in the same step the downstream one falls). Any `h > 1` is a
timing obligation. -/
theorem muller_hold1 {m h : Nat} {i o : Chan} (M : MullerStage m h i o) (hpo : Protocol o) :
    Hold 1 i o := by
  intro e' s hf h1 h2
  have hs : s = e' + 1 := by omega
  subst hs
  have hao : o.ack e' = true := by simp [fallB] at hf; exact hf.1
  have hao1 : o.ack (e'+1) = false := by simp [fallB] at hf; exact hf.2
  have hlow : i.ack e' = false := by
    rw [← M.H_NODE]; exact ack_fall_req_low (hpo.2 e').2 hao hao1
  rcases M.H_CEL_SI e' with h | h
  · rw [h, hlow]
  · rw [h, hlow, hao, celN_eq]; cases i.req e' <;> rfl

/-- If the input link meets `SetupHold m h`, and the control traces meet
`Sep m'` and `Hold h'`, the stage's OUTPUT link meets `SetupHold m' h'`:
the latch output, held since the upstream close, is stable over the whole
setup/hold window of the downstream close. -/
theorem muller_out_setupHold {m h m' h' : Nat} {i o : Chan} (M : MullerStage m h i o)
    (hpo : Protocol o) (hsh : SetupHold m h i) (H_SEP : Sep m' i o) (H_HOLD : Hold h' i o) :
    SetupHold m' h' o := by
  intro e' hf' s hs1 hs2
  have hao : o.ack e' = true := by simp [fallB] at hf'; exact hf'.1
  have hao1 : o.ack (e'+1) = false := by simp [fallB] at hf'; exact hf'.2
  have hreq : o.req e' = false := ack_fall_req_low (hpo.2 e').2 hao hao1
  have hlow : i.ack e' = false := by rw [← M.H_NODE]; exact hreq
  have hinv := falls_inv hpo e'
  rw [hreq, hao] at hinv
  simp only [and_self, ite_true] at hinv
  have hfun : o.req = i.ack := funext M.H_NODE
  rw [hfun] at hinv
  obtain ⟨e, he, hfe, _, hl⟩ := last_fall i.ack e' (cnt (fallB o.ack) e') hlow hinv
  have hsep := H_SEP e e' hfe hf' he hl
  have hlow' : ∀ x, e < x → x ≤ e' + h' → i.ack x = false := by
    intro x h1 h2
    by_cases hx : x ≤ e'
    · exact hl x h1 hx
    · exact H_HOLD e' x hf' (by omega) h2
  have v1 := M.H_LATCH e hfe (hsh e hfe) s (by omega) (fun u h1 h2 => hlow' u h1 (by omega))
  have v2 := M.H_LATCH e hfe (hsh e hfe) e' he hl
  rw [v1, v2]

/-! ## The Muller pipeline (`bd_pipe` without matched lines) -/

/-- **Muller pipeline, FIFO safety.** `n ≥ 1` Muller stages over links
`ch 0 .. ch n`, a causal source/sink obeying the protocol, and the per-link
obligations:
* `H_SRC_SETUP_HOLD`: the source's data meets setup `m` / hold `h` around each
  close of link 0 (data obligation of the environment);
* `H_SEP j`, `H_HOLD j` for every internal link `j+1` (`j+1 < n`): control-only
  event separations (`Sep m`, `Hold h`) between the closes of stage `j` and
  `j+1`.
Then every link obeys the protocol and the pipeline is a FIFO from `ch 0` to
`ch n`: the `k`-th token out is the `k`-th token in, and tokens out ≤ tokens in. -/
theorem muller_pipeline {m h n : Nat} {ch : Nat → Chan}
    (H_STAGE : ∀ j, j < n → MullerStage m h (ch j) (ch (j + 1)))
    (srcInit : (ch 0).req 0 = false) (snkInit : (ch n).ack 0 = false)
    (src : ∀ t, (∀ s, s < t → Rules (ch 0) s) → SendStep (ch 0) t)
    (snk : ∀ t, (∀ s, s < t → Rules (ch n) s) → RecvStep (ch n) t)
    (H_SRC_SETUP_HOLD : SetupHold m h (ch 0))
    (H_SEP : ∀ j, j + 1 < n → Sep m (ch j) (ch (j + 1)))
    (H_HOLD : ∀ j, j + 1 < n → Hold h (ch j) (ch (j + 1)))
    (hn : 0 < n) :
    (∀ j, j ≤ n → Protocol (ch j)) ∧
    (∀ t, cnt (fallB (ch n).ack) t ≤ cnt (fallB (ch 0).ack) t) ∧
    (∀ k e', TokAt (ch n) k e' → ∃ e, e < e' ∧ TokAt (ch 0) k e ∧ (ch n).dat e' = (ch 0).dat e) := by
  have P : Pipeline m h n ch :=
    { stage := fun j hj => muller_stageSpec (H_STAGE j hj)
      srcInit, snkInit, src, snk }
  have hp := pipeline_protocol P
  have hsh : ∀ j, j < n → SetupHold m h (ch j) := by
    intro j
    induction j with
    | zero => intro _; exact H_SRC_SETUP_HOLD
    | succ j ih =>
      intro hj
      exact muller_out_setupHold (H_STAGE j (by omega)) (hp (j+1) (by omega))
        (ih (by omega)) (H_SEP j hj) (H_HOLD j hj)
  exact ⟨hp, pipeline_prefix P hsh hn⟩

/-- Pipeline of wire-delayed Muller stages: every link obeys the protocol.
Here the time induction of `pipeline_protocol` is doing real work (each
stage's guarantee at step `t+1` uses both neighbours' and its own rules at
step `t`). -/
theorem mullerW_pipeline_protocol {m h n : Nat} {ch : Nat → Chan}
    (H_STAGE : ∀ j, j < n → MullerStageW m h (ch j) (ch (j + 1)))
    (srcInit : (ch 0).req 0 = false) (snkInit : (ch n).ack 0 = false)
    (src : ∀ t, (∀ s, s < t → Rules (ch 0) s) → SendStep (ch 0) t)
    (snk : ∀ t, (∀ s, s < t → Rules (ch n) s) → RecvStep (ch n) t) :
    ∀ j, j ≤ n → Protocol (ch j) :=
  pipeline_protocol (m := m) (h := h)
    { stage := fun j hj => mullerW_stageSpec (H_STAGE j hj), srcInit, snkInit, src, snk }

end Formal.Net.Handshake
