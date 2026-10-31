import Formal.Cells.OpsTimedMux
import Formal.Cells.OpsTimed2
import Formal.Cells.MuxN3
open Formal.Core.LutList

/-!
# Shard B probe Mn: timed `bdc_muxn3_32` (gcd_hw's 3-way loop header)

`bdc/emit.py` `emit_muxn(32, 3)` (1 instance in gcd_hw, `umux21`, DELAY 12),
with the LUTs yosys infers (H_YOSYS_MAP, `B-amerge.md`, `AMergeGates`):

    sel_i : LUT3 (sel0 8'h10: I0 s0, I1 s1, I2 ctl_req; sel1 8'h40: I0 s1, I1 s0, I2 ctl_req;
                  sel2 8'h40: I0 s0, I1 s1, I2 ctl_req)                  -- ctl_req & (s == i)
    uj_i  : bd_c2 (I0 in_i_req, I1 sel_i, I2 own output, I3 rst)  INIT 0x00E8_00E8_00E8_00E8
    |j    : LUT3 8'hFE (I0 j2, I1 j1, I2 j0) -> uor (LUT1 2'h2) -> bd_delay_gated(.gate(|j)) -> z_req
    ua_i  : bd_c2 (I0 j_i, I1 z_ack)                              -> in_i_ack
    ctl_ack = z_ack
    z_data[b] : LUT5 32'hF0AA_CCF0 (I0 in2[b], I1 in1[b], I2 in0[b], I3 s0, I4 s1)

This is the N = 3, timed analogue of probe Lt's `mux_ok` (`OpsTimedMux`) and
probe Lt2's `mux_data_ok` (`OpsTimed2`), in the same model:

* every LUT a FIFO bounded-delay arc (**H_LUT_FIFO**) evaluated on its REAL
  INIT (`AMergeGates.sel0/sel1/sel2/or3` = `lutB` of the inferred INITs,
  `LibCtlMergeMux.c2B` = `lutB` of bd_c2's INIT);
* every fork branch its own FIFO wire (**H_WIRE_FIFO**), no fork assumed
  isochronic;
* the C-elements' own-output nets window channels `[wl, wh]` (`CEl`);
* the request line `uor` + `bd_delay_gated` (BDC_FASTFALL = 1, the default
  emitted in gcd_hw) in Lt2's FIFO model of a FASTFALL line (`FFLine`): stage
  0 reads `|j` through the composite path `|j -> uor -> wire -> LUT1`
  (`H 0`, a FIFO channel by `PipeTimed.fifo_comp`), each AND stage reads the
  previous stage through its hop `H i` and `|j` (the `gate` net) through its
  tap `Tp i`;
* the data LUT5 a Bundling window relation (`Gate`) over its REAL INIT.

Inputs are indexed by `i ∈ {0, 1, 2}`; every per-input delay is a function
of `i`. Control token `k` carries the index `sv k` (`< 3`, **H_S_RANGE**);
input `i`'s `m`-th token is consumed by control token `κ i m`.

Main results: `muxn3_ok` (event form), `muxn3_timing_of_static` and
`muxn3_ok_static` (port-level causal partners + per-arc static
inequalities), `muxn3_s_pin_of_static` (the decode's select setup/hold as
static inequalities), `muxn3_data_ok` (the LUT5 delivers the selected
input's bit), and the unit-delay witness `Mn3Wit` in which each input is
selected.
-/

namespace Formal.Cells.MuxN3Timed
open Formal.Cells
open Formal.Cells.OpsTimed
open Formal.Cells.PipeTimed (Ret Trace)
open Formal.Cells.LibCtlMergeMux (c2B cSpec c2_spec)
open Formal.Cells.AMergeGates (sel0 sel1 sel2 or3 sel0_eq sel1_eq sel2_eq or3_eq)

/-! ## 1. Gate-level facts -/

/-- The two index bits of `v` (`s[0]`, `s[1]`). -/
def b0 (v : Nat) : Bool := decide (v % 2 = 1)
def b1 (v : Nat) : Bool := decide (v / 2 % 2 = 1)

/-- The decode LUT3 of input `i` (REAL inferred INITs, through `lutB`). -/
def selF : Nat → Bool → Bool → Bool → Bool
  | 0 => sel0
  | 1 => sel1
  | _ => sel2

/-- The decode ignores `s` while `ctl_req` is low (any `i`). -/
theorem selF_off (i : Nat) (a b : Bool) : selF i a b false = false := by
  match i with
  | 0 => cases a <;> cases b <;> decide
  | 1 => cases a <;> cases b <;> decide
  | _ + 2 => show sel2 a b false = false; cases a <;> cases b <;> decide

/-- With the index bits of `v < 3` on its `s` pins, decode `i` is
`ctl_req · (v = i)`: from the INITs (`sel*_eq`), not assumed. -/
theorem selF_idx {i v : Nat} (hi : i < 3) (hv : v < 3) (c : Bool) :
    selF i (b0 v) (b1 v) c = (c && decide (v = i)) := by
  obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
  all_goals obtain rfl | rfl | rfl : v = 0 ∨ v = 1 ∨ v = 2 := by omega
  all_goals cases c <;> decide

/-- `|j` LUT3 `8'hFE` is the OR of its three pins (`or3_eq`). -/
theorem or3_spec (a b c : Bool) : or3 a b c = (a || b || c) := or3_eq a b c

/-- Copied from `OpsCounter` (probe Lt3, `Tok.slot_of` / `Tok.retime`; not imported
here to keep the import set small). -/
theorem tok_slot_of {e : Nat → Nat} :
    ∀ n t, e 0 ≤ t → t < e n → ∃ i, e i ≤ t ∧ t < e (i + 1) := by
  intro n
  induction n with
  | zero => intro t h1 h2; omega
  | succ n ih =>
    intro t h1 h2
    by_cases h : t < e n
    · exact ih t h1 h
    · exact ⟨n, by omega, h2⟩

/-- **Re-timing a token trace.** If `S` is monotone and equals `e` on every
gate-on slot, the trace is also a token trace on `S` (with `e` unbounded,
every instant outside the gate-on slots is low; `e` need not be monotone). -/
theorem tok_retime {T : Nat} {x : Trace} {e : Nat → Nat} {g : Nat → Bool} (h : Tok T x e g) (eunb : ∀ t, ∃ n, t < e n)
    {S : Nat → Nat} (smono : ∀ a b, a ≤ b → S a ≤ S b)
    (hS : ∀ k, g k = true → S (2 * k) = e (2 * k) ∧ S (2 * k + 1) = e (2 * k + 1)) :
    Tok T x S g := by
  -- an instant inside a gate-on slot of `e` lies in the same slot of `S`
  have on : ∀ t, T ≤ t → x t = true → ∃ k, g k = true ∧ S (2 * k) ≤ t ∧ t < S (2 * k + 1) := by
    intro t hT hx
    by_cases h0 : t < e 0
    · rw [h.pre t hT h0] at hx; exact absurd hx (by simp)
    · obtain ⟨n, hn⟩ := eunb t
      obtain ⟨i, hi1, hi2⟩ := tok_slot_of (e := e) n t (by omega) hn
      by_cases hl : Tok.SlotLow g i
      · rw [h.low_slot i t hl hT hi1 hi2] at hx; exact absurd hx (by simp)
      · have hi : i % 2 = 0 ∧ g (i / 2) = true := by
          unfold Tok.SlotLow at hl; constructor
          · omega
          · cases hg : g (i / 2)
            · exact absurd (Or.inr hg) hl
            · rfl
        obtain ⟨k, rfl⟩ : ∃ k, i = 2 * k := ⟨i / 2, by omega⟩
        rw [show 2 * k / 2 = k by omega] at hi
        have e1 := hS k hi.2
        exact ⟨k, hi.2, by omega, by omega⟩
  -- so any instant in a low slot of `S` (or before `S 0`) is low
  have low : ∀ t, T ≤ t → (t < S 0 ∨ ∃ j, Tok.SlotLow g j ∧ S j ≤ t ∧ t < S (j + 1)) → x t = false := by
    intro t hT hc
    cases hx : x t
    · rfl
    · obtain ⟨k, hk, h1, h2⟩ := on t hT hx
      exfalso
      rcases hc with hc | ⟨j, hj, h3, h4⟩
      · have := smono 0 (2 * k) (Nat.zero_le _); omega
      · rcases Nat.lt_trichotomy j (2 * k) with c | c | c
        · have := smono (j + 1) (2 * k) (by omega); omega
        · subst c
          unfold Tok.SlotLow at hj
          rcases hj with hj | hj
          · omega
          · rw [show 2 * k / 2 = k by omega, hk] at hj; exact absurd hj (by simp)
        · have := smono (2 * k + 1) j (by omega); omega
  refine ⟨fun t hT h2 => low t hT (Or.inl h2), fun k t hT h1 h2 => ?_,
    fun k t hT h1 h2 => low t hT (Or.inr ⟨2 * k + 1, Or.inl (by omega), h1, h2⟩)⟩
  cases hg : g k
  · exact low t hT (Or.inr ⟨2 * k, Tok.slotLow_even hg, h1, h2⟩)
  · have e1 := hS k hg
    rw [h.hi k t hT (by omega) (by omega), hg]


/-- A two-bit gated function of a clean token trace (the decode LUT3). -/
theorem tok_gate2 {T : Nat} {x : Trace} {e : Nat → Nat} (h : Tok T x e (fun _ => true))
    (f : Bool → Bool → Bool → Bool) (hf : ∀ a b, f a b false = false) {s0 s1 : Trace}
    {v0 v1 : Nat → Bool}
    (hs : ∀ k t, T ≤ t → e (2 * k) ≤ t → t < e (2 * k + 1) → s0 t = v0 k ∧ s1 t = v1 k) :
    Tok T (fun t => f (s0 t) (s1 t) (x t)) e (fun k => f (v0 k) (v1 k) true) := by
  refine ⟨fun t h1 h2 => ?_, fun k t h1 h2 h3 => ?_, fun k t h1 h2 h3 => ?_⟩
  · show f _ _ (x t) = false; rw [h.pre t h1 h2, hf]
  · show f (s0 t) (s1 t) (x t) = _
    rw [h.hi k t h1 h2 h3, (hs k t h1 h2 h3).1, (hs k t h1 h2 h3).2]
  · show f _ _ (x t) = false; rw [h.lo k t h1 h2 h3, hf]

/-- OR of three token traces on the SAME edges whose gates cover every token. -/
theorem or3_same {T : Nat} {a b c : Trace} {S : Nat → Nat} {g0 g1 g2 : Nat → Bool}
    (h0 : Tok T a S g0) (h1 : Tok T b S g1) (h2 : Tok T c S g2)
    (hg : ∀ k, (g0 k || g1 k || g2 k) = true) :
    Tok T (fun t => a t || b t || c t) S (fun _ => true) := by
  refine ⟨fun t hT h => ?_, fun k t hT e1 e2 => ?_, fun k t hT e1 e2 => ?_⟩
  · simp [h0.pre t hT h, h1.pre t hT h, h2.pre t hT h]
  · show (a t || b t || c t) = true
    rw [h0.hi k t hT e1 e2, h1.hi k t hT e1 e2, h2.hi k t hT e1 e2]; exact hg k
  · simp [h0.lo k t hT e1 e2, h1.lo k t hT e1 e2, h2.lo k t hT e1 e2]

/-- Lower bound of a FASTFALL line's edges: every stage edge comes at least
`Dl` after the input edge, if `Dl` is below stage 0's path and every tap. -/
theorem ffE_ge {H Tp : Nat → Ret} {e : Nat → Nat} {N Dl : Nat} (he : ∀ j, 1 ≤ e j)
    (h0 : Dl ≤ (H 0).lo) (ht : ∀ i, 1 ≤ i → i < N → Dl ≤ (Tp i).lo) :
    ∀ i, 1 ≤ i → i ≤ N → ∀ j, e j + Dl ≤ ffE H Tp e i j := by
  intro i
  induction i with
  | zero => intro h; omega
  | succ i ih =>
    intro _ hiN j
    rcases Nat.eq_zero_or_pos i with h | h
    · subst h; show e j + Dl ≤ (H 0).fst (e j)
      have := fl (H 0) (he j); omega
    · obtain ⟨i', rfl⟩ : ∃ i', i = i' + 1 := ⟨i - 1, by omega⟩
      have IH := ih (by omega) (by omega) j
      have a1 := (H (i' + 1)).fst_ge (ffE H Tp e (i' + 1) j)
      have a2 := fl (Tp (i' + 1)) (he j)
      have a3 := ht (i' + 1) (by omega) (by omega)
      show e j + Dl ≤ andEdges (fun j => (H (i' + 1)).fst (ffE H Tp e (i' + 1) j))
        (fun j => (Tp (i' + 1)).fst (e j)) j
      unfold andEdges; dsimp only; split <;> omega

/-! ## 2. The run, the gates, the environment -/

/-- Delay realisation of one run of `bdc_muxn3`, the environment's event
times and the three enumerations. Index `i` = input `i`. -/
structure MN3Run where
  /-- wire `in_i_req → uj_i.I0` -/
  Wx : Nat → Ret
  /-- wire `ctl_req → sel_i.I2` (one branch of the ctl_req fork per decode) -/
  Wc : Nat → Ret
  /-- decode LUT3 arc of `sel_i` (lumped over its pins, H_LUT_FIFO) -/
  Ls : Nat → Ret
  /-- wire `sel_i → uj_i.I1` (the extra gate+wire bd_mux does not have) -/
  Wsj : Nat → Ret
  /-- join arc and its own-output (feedback) window -/
  Lj : Nat → Ret
  wjl : Nat → Nat
  wjh : Nat → Nat
  /-- wires `j_i → |j` pin and `j_i → ua_i.I0` -/
  Wjo : Nat → Ret
  Wja : Nat → Ret
  /-- `|j` LUT3 arc -/
  Lo : Ret
  /-- request line: `H 0` = `|j → uor → wire → stage-0 LUT1` (composite FIFO
  path); `H i` (i ≥ 1) = hop into AND stage `i`; `Tp i` = tap `|j → stage i.I1`;
  `N` = DELAY; the wire to the server is folded into the last stage. -/
  H : Nat → Ret
  Tp : Nat → Ret
  N : Nat
  /-- wire `z_ack → ua_i.I1`, ack C-element arc and feedback window, wire
  `ua_i → client i` -/
  Wza : Nat → Ret
  La : Nat → Ret
  wal : Nat → Nat
  wah : Nat → Nat
  Wak : Nat → Ret
  /-- environment: `ξ i` client i's request edges (i-indexed), `γ` ctl_req,
  `ζ` z_ack (control-indexed); `sv k` the index of control token `k`;
  `κ i m` the control token consuming input `i`'s `m`-th token. -/
  ξ : Nat → Nat → Nat
  γ : Nat → Nat
  ζ : Nat → Nat
  sv : Nat → Nat
  κ : Nat → Nat → Nat

namespace MN3Run
variable (P : MN3Run)
/-- Token `k` selects input `i`. -/
def g (i k : Nat) : Bool := decide (P.sv k = i)
/-- in_i_req at uj_i.I0 (i-indexed). -/
def Xp (i j : Nat) : Nat := (P.Wx i).fst (P.ξ i j)
/-- ctl_req at sel_i.I2 (control-indexed). -/
def Cp (i j : Nat) : Nat := (P.Wc i).fst (P.γ j)
/-- sel_i at uj_i.I1 (control-indexed edges; low in tokens not selecting i). -/
def Sd (i j : Nat) : Nat := (P.Wsj i).fst ((P.Ls i).fst (P.Cp i j))
/-- ... and on input i's own tokens. -/
def D (i : Nat) : Nat → Nat := rx (P.Sd i) (P.κ i)
/-- uj_i's phase starts and node edges (i-indexed). -/
def c (i j : Nat) : Nat := max (P.Xp i j) (P.D i j)
def τ (i j : Nat) : Nat := (P.Lj i).fst (P.c i j)
/-- The selected join's node edges, control-indexed. -/
def E (j : Nat) : Nat := P.τ (P.sv (j / 2)) (2 * idx (P.κ (P.sv (j / 2))) (j / 2) + j % 2)
/-- j_i at its |j pin; the selected one; |j's output; z_req at the server. -/
def Op (i j : Nat) : Nat := (P.Wjo i).fst (P.E j)
def Sor (j : Nat) : Nat := P.Op (P.sv (j / 2)) j
def OJ (j : Nat) : Nat := P.Lo.fst (P.Sor j)
def Z (j : Nat) : Nat := ffE P.H P.Tp P.OJ P.N j
/-- ua_i's pins, phase starts, and in_i_ack at client i. -/
def A (i j : Nat) : Nat := (P.Wja i).fst (P.E j)
def ZA (i j : Nat) : Nat := (P.Wza i).fst (P.ζ j)
def cx (i j : Nat) : Nat := max (P.A i j) (P.ZA i j)
def XA (i j : Nat) : Nat := (P.Wak i).fst ((P.La i).fst (P.cx i j))
/-- Start of the clean windows of |j, z_req and the acks. -/
def Tj : Nat := (P.Lj 0).hi + (P.Wjo 0).hi + ((P.Lj 1).hi + (P.Wjo 1).hi) + ((P.Lj 2).hi + (P.Wjo 2).hi)
def To : Nat := P.Tj + P.Lo.hi
def Ta (i : Nat) : Nat := (P.La i).hi + (P.Wak i).hi
end MN3Run

/-- **The gate relations** (one field per primitive, REAL INITs). Traces
indexed by `i` are per input. `s0p i`, `s1p i` are `s[0]`, `s[1]` at
`sel_i`'s pins; `cp i` is ctl_req at `sel_i.I2`; `sl i` the decode output;
`sj i` the decode at `uj_i.I1`; `j i` the join node and `q i` its feedback
pin; `jo i` j_i at the |j pin; `orj` the |j net (also `udly.gate`); `s n` the
line's stage `n` (`s P.N` = z_req at the server); `ja i`, `zx i` ua_i's pins;
`a i`, `qa i` its node and feedback pin; `ak i` in_i_ack at client i. -/
structure MN3Gates (P : MN3Run) (rst ctl za : Trace) (x xj cp s0p s1p sl sj j q jo : Nat → Trace)
    (orj : Trace) (s : Nat → Trace) (ja zx a qa ak : Nat → Trace) : Prop where
  H_WX : ∀ i, i < 3 → ∀ t, (P.Wx i).hi ≤ t → xj i t = x i ((P.Wx i).σ t)
  H_WC : ∀ i, i < 3 → ∀ t, (P.Wc i).hi ≤ t → cp i t = ctl ((P.Wc i).σ t)
  /-- **H_LUT_FIFO** for the decode `sel_i` (inferred INITs `8'h10`, `8'h40`,
  `8'h40`, pin maps of H_YOSYS_MAP; the three pins read at one instant: per-pin
  arc differences are folded into the pin wires). -/
  H_SEL : ∀ i, i < 3 → ∀ t, (P.Ls i).hi ≤ t →
    sl i t = selF i (s0p i ((P.Ls i).σ t)) (s1p i ((P.Ls i).σ t)) (cp i ((P.Ls i).σ t))
  H_WSJ : ∀ i, i < 3 → ∀ t, (P.Wsj i).hi ≤ t → sj i t = sl i ((P.Wsj i).σ t)
  /-- **H_LUT_FIFO** for `uj_i` (`bd_c2`, REAL INIT `0x00E800E800E800E8`). -/
  H_UJ : ∀ i, i < 3 → ∀ t, (P.Lj i).hi ≤ t →
    j i t = c2B (xj i ((P.Lj i).σ t)) (sj i ((P.Lj i).σ t)) (q i ((P.Lj i).σ t)) (rst ((P.Lj i).σ t))
  /-- **H_FB** for `uj_i` (the `(* keep *)` O → I2 net), window channel. -/
  H_UJ_FB : ∀ i, i < 3 → CElemTiming.WinDelay (P.wjl i) (P.wjh i) (j i) (q i)
  H_UJ_POS : ∀ i, i < 3 → 1 ≤ (P.Lj i).lo + P.wjl i
  H_WJO : ∀ i, i < 3 → ∀ t, (P.Wjo i).hi ≤ t → jo i t = j i ((P.Wjo i).σ t)
  /-- **H_LUT_FIFO** for `|j` (inferred LUT3 `8'hFE`). -/
  H_OR3 : ∀ t, P.Lo.hi ≤ t → orj t = or3 (jo 0 (P.Lo.σ t)) (jo 1 (P.Lo.σ t)) (jo 2 (P.Lo.σ t))
  /-- **H_LINE** (`uor` + `bd_delay_gated`, FASTFALL = 1): Lt2's FIFO model of
  the line with input AND gate net `|j` (`FFLine`). -/
  H_LINE : FFLine orj s P.H P.Tp P.N
  H_WJA : ∀ i, i < 3 → ∀ t, (P.Wja i).hi ≤ t → ja i t = j i ((P.Wja i).σ t)
  H_WZA : ∀ i, i < 3 → ∀ t, (P.Wza i).hi ≤ t → zx i t = za ((P.Wza i).σ t)
  /-- **H_LUT_FIFO** for `ua_i` (`bd_c2`, REAL INIT). -/
  H_UA : ∀ i, i < 3 → ∀ t, (P.La i).hi ≤ t →
    a i t = c2B (ja i ((P.La i).σ t)) (zx i ((P.La i).σ t)) (qa i ((P.La i).σ t)) (rst ((P.La i).σ t))
  H_UA_FB : ∀ i, i < 3 → CElemTiming.WinDelay (P.wal i) (P.wah i) (a i) (qa i)
  H_UA_POS : ∀ i, i < 3 → 1 ≤ (P.La i).lo + P.wal i
  H_WAK : ∀ i, i < 3 → ∀ t, (P.Wak i).hi ≤ t → ak i t = a i ((P.Wak i).σ t)

/-- **The environment**: clean four-phase partners, the index range, the
enumerations, and the decode's select bundling at each decode's pins. -/
structure MN3Env (P : MN3Run) (rst ctl za : Trace) (x s0p s1p : Nat → Trace) (R : Nat) : Prop where
  H_RST_HI : ∀ t, t < R → rst t = true
  H_RST_LO : ∀ t, R ≤ t → rst t = false
  /-- **H_SND_CLEAN** (clients, control sender), **H_SRV_CLEAN** (server). -/
  H_X : ∀ i, i < 3 → Tok 0 (x i) (P.ξ i) (fun _ => true)
  H_CTL : Tok 0 ctl P.γ (fun _ => true)
  H_ZA : Tok 0 za P.ζ (fun _ => true)
  /-- **H_S_RANGE**: the index is 0, 1 or 2 (from `amerge3_ok`'s `good` in gcd_hw). -/
  H_RANGE : ∀ k, P.sv k < 3
  H_ENUM : ∀ i, i < 3 → Enum (P.g i) (P.κ i)
  /-- **H_S_PIN** at each decode (`bdc_muxn.s_setup` + `s_hold`, pin form):
  while ctl_req is high at `sel_i.I2`, `sel_i`'s `s` pins show the token's
  index bits. Static form: `muxn3_s_pin_of_static`. -/
  H_S_PIN : ∀ i, i < 3 → ∀ k t, P.Cp i (2 * k) ≤ t → t < P.Cp i (2 * k + 1) →
    s0p i t = b0 (P.sv k) ∧ s1p i t = b1 (P.sv k)

/-- **The event-form timing obligations.** -/
structure MN3Timing (P : MN3Run) (R : Nat) : Prop where
  /-- **H_RST_LONG**: reset outlasts each pin path and each loop. -/
  H_RST_LONG : ∀ i, i < 3 → (P.Wx i).hi ≤ R ∧ (P.Wc i).hi + (P.Ls i).hi + (P.Wsj i).hi ≤ R ∧
    (P.Lj i).hi + P.wjh i ≤ R ∧ (P.Lj i).hi + (P.Wja i).hi ≤ R ∧ (P.Wza i).hi ≤ R ∧
    (P.La i).hi + P.wah i ≤ R
  /-- **H_RST_EARLY**: no first edge reaches a C-element before reset is released. -/
  H_RST_EARLY : ∀ i, i < 3 → R ≤ P.Xp i 0 ∧ R ≤ P.D i 0 ∧ R ≤ P.A i 0 ∧ R ≤ P.ZA i 0
  /-- **H_DEP_J** (uj_i env latency): in_i_req and the decode leave their phase
  value at uj_i's pins only after uj_i's loop settled. -/
  H_DEP_J : ∀ i, i < 3 → ∀ j, P.c i j + (P.Lj i).hi + P.wjh i ≤ P.Xp i (j + 1) ∧
    P.c i j + (P.Lj i).hi + P.wjh i ≤ P.D i (j + 1)
  /-- **H_DEP_A** (ua_i env latency, control-indexed: includes the tokens not
  selecting `i`, where j_i stays low and only z_ack pulses: there it is
  **H_MUX_RTZ**, `bdc_muxn.rtz`). -/
  H_DEP_A : ∀ i, i < 3 → ∀ j, P.cx i j + (P.La i).hi + P.wah i ≤ P.A i (j + 1) ∧
    P.cx i j + (P.La i).hi + P.wah i ≤ P.ZA i (j + 1)
  /-- **H_FLUSH_STAGE** of the FASTFALL line (`bd_delay[FASTFALL].flush_per_stage`). -/
  H_FLUSH : ∀ i, 1 ≤ i → i < P.N → ∀ k,
    (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 1)) ≤ (P.Tp i).fst (P.OJ (2 * k + 2)) ∧
    (P.Tp i).fst (P.OJ (2 * k + 1)) ≤ (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 2))
  H_N : 1 ≤ P.N

/-- **Port-level causality of the partners.** Client `i` moves its request
`Ex` after seeing its ack move; the control sender moves ctl_req `Ec` after
seeing ctl_ack = z_ack through `Wzc`; the server answers `Es` after z_req's
edge reached it. -/
structure MN3Causal (P : MN3Run) (Wzc : Ret) (Ex Ec Es : Nat) : Prop where
  H_XC_FALL : ∀ i, i < 3 → ∀ m, P.XA i (2 * P.κ i m) + Ex ≤ P.ξ i (2 * m + 1)
  H_XC_RISE : ∀ i, i < 3 → ∀ m, P.XA i (2 * P.κ i m + 1) + Ex ≤ P.ξ i (2 * m + 2)
  H_CTL_C : ∀ j, Wzc.fst (P.ζ j) + Ec ≤ P.γ (j + 1)
  H_SRV : ∀ j, P.Z j + Es ≤ P.ζ j
  H_ES : 1 ≤ Es
  H_POS : ∀ j, 1 ≤ P.γ j

/-! ## 3. Event-time lemmas -/

section ev
variable {P : MN3Run}

theorem hit_sv {i : Nat} (h : Enum (P.g i) (P.κ i)) (m : Nat) : P.sv (P.κ i m) = i := by
  have := h.hit m; unfold MN3Run.g at this; simpa using this

theorem E_rx {i : Nat} (h : Enum (P.g i) (P.κ i)) (j : Nat) : rx P.E (P.κ i) j = P.τ i j := by
  unfold rx MN3Run.E
  have h1 : (2 * P.κ i (j / 2) + j % 2) / 2 = P.κ i (j / 2) := by omega
  have h2 : (2 * P.κ i (j / 2) + j % 2) % 2 = j % 2 := by omega
  rw [h1, h2, hit_sv h, idx_κ h, show 2 * (j / 2) + j % 2 = j by omega]

/-- The selected decode edge at the selected join, control-indexed. -/
theorem D_sel (hE : ∀ i, i < 3 → Enum (P.g i) (P.κ i)) (hR : ∀ k, P.sv k < 3) (j : Nat) :
    P.D (P.sv (j / 2)) (2 * idx (P.κ (P.sv (j / 2))) (j / 2) + j % 2) = P.Sd (P.sv (j / 2)) j := by
  have he := hE _ (hR (j / 2))
  have hk := κ_idx he (k := j / 2) (by unfold MN3Run.g; simp)
  unfold MN3Run.D rx
  rw [show (2 * idx (P.κ (P.sv (j / 2))) (j / 2) + j % 2) / 2 = idx (P.κ (P.sv (j / 2))) (j / 2) by omega,
    show (2 * idx (P.κ (P.sv (j / 2))) (j / 2) + j % 2) % 2 = j % 2 by omega, hk,
    show 2 * (j / 2) + j % 2 = j by omega]

/-- ctl_req's edge reaches the selected join's node through the selected
decode: `γ j + Wc.lo + Ls.lo + Wsj.lo + Lj.lo ≤ E j`. -/
theorem γ_le_E (hE : ∀ i, i < 3 → Enum (P.g i) (P.κ i)) (hR : ∀ k, P.sv k < 3)
    (hpos : ∀ j, 1 ≤ P.γ j) (j : Nat) :
    P.γ j + (P.Wc (P.sv (j / 2))).lo + (P.Ls (P.sv (j / 2))).lo + (P.Wsj (P.sv (j / 2))).lo +
      (P.Lj (P.sv (j / 2))).lo ≤ P.E j := by
  have hD := D_sel hE hR j
  have h1 := hpos j
  have a1 := fl (P.Wc (P.sv (j / 2))) h1
  have a2 := fl (P.Ls (P.sv (j / 2))) (c := P.Cp (P.sv (j / 2)) j) (by unfold MN3Run.Cp; omega)
  have a3 := fl (P.Wsj (P.sv (j / 2))) (c := (P.Ls (P.sv (j / 2))).fst (P.Cp (P.sv (j / 2)) j))
    (by unfold MN3Run.Cp at *; omega)
  have a4 := fl (P.Lj (P.sv (j / 2)))
    (c := P.c (P.sv (j / 2)) (2 * idx (P.κ (P.sv (j / 2))) (j / 2) + j % 2))
    (by unfold MN3Run.c; unfold MN3Run.Sd MN3Run.Cp at hD; unfold MN3Run.Cp at *; omega)
  unfold MN3Run.E MN3Run.τ
  unfold MN3Run.c at *; unfold MN3Run.Sd MN3Run.Cp at hD; unfold MN3Run.Cp at *
  omega

/-- Along the request path: `E j ≤ Sor j ≤ OJ j ≤ Z j`, with lower bounds. -/
theorem E_le_Z (hE : ∀ i, i < 3 → Enum (P.g i) (P.κ i)) (hR : ∀ k, P.sv k < 3)
    (hpos : ∀ j, 1 ≤ P.γ j) {wo Dl : Nat} (hwo : ∀ i, i < 3 → wo ≤ (P.Wjo i).lo)
    (h0 : Dl ≤ (P.H 0).lo) (ht : ∀ i, 1 ≤ i → i < P.N → Dl ≤ (P.Tp i).lo) (hN : 1 ≤ P.N) (j : Nat) :
    P.E j + wo ≤ P.Sor j ∧ P.Sor j + P.Lo.lo ≤ P.OJ j ∧ P.OJ j + Dl ≤ P.Z j := by
  have hEp : ∀ j, 1 ≤ P.E j := fun j => by have := γ_le_E hE hR hpos j; have := hpos j; omega
  have hS : ∀ j, P.E j + wo ≤ P.Sor j := fun j => by
    have := hwo _ (hR (j / 2)); have := fl (P.Wjo (P.sv (j / 2))) (hEp j)
    unfold MN3Run.Sor MN3Run.Op; omega
  have hO : ∀ j, P.Sor j + P.Lo.lo ≤ P.OJ j := fun j => by
    have := hEp j; have := hS j; exact fl P.Lo (by omega)
  refine ⟨hS j, hO j, ?_⟩
  exact ffE_ge (fun j => by have := hEp j; have := hS j; have := hO j; omega) h0 ht P.N hN
    (Nat.le_refl _) j

/-- **The selected edges are strictly increasing, from causality alone**:
`E j ≤ Z j < ζ j ≤ γ (j+1) ≤ E (j+1)` (no fork-skew condition). -/
theorem E_step {Wzc : Ret} {Ex Ec Es : Nat} (hE : ∀ i, i < 3 → Enum (P.g i) (P.κ i))
    (hR : ∀ k, P.sv k < 3) (Cs : MN3Causal P Wzc Ex Ec Es) (hN : 1 ≤ P.N) (j : Nat) :
    P.E j ≤ P.Sor j ∧ P.Sor j < P.E (j + 1) := by
  have h := E_le_Z hE hR Cs.H_POS (wo := 0) (Dl := 0) (fun _ _ => Nat.zero_le _) (Nat.zero_le _)
    (fun _ _ _ => Nat.zero_le _) hN j
  have h1 := Cs.H_SRV j; have h2 := Cs.H_CTL_C j; have h3 := Wzc.fst_ge (P.ζ j)
  have h4 := γ_le_E hE hR Cs.H_POS (j + 1); have := Cs.H_ES
  omega

end ev

/-! ## 4. `muxn3_ok`: the handshake theorem -/

/-- **`muxn3_ok`.** Under the gate relations (real INITs), a clean
environment, the event-form timing obligations and port-level causality
(used only to order the selected edges, no skew condition):
(1) join `i` fires exactly in the control tokens selecting `i`, once per
token; (2) `|j` and z_req at the server are one clean four-phase transaction
per control token; (3) `in_i_ack` pulses exactly in the tokens selecting `i`,
i.e. once per input-`i` token, never during another input's transaction (the
other two inputs keep their tokens); (4) order: join `i` fires for its `m`-th
token only after both its request and the decode reached it; each ack rises
after the server's. -/
theorem muxn3_ok {P : MN3Run} {R : Nat} {Wzc : Ret} {Ex Ec Es : Nat} {rst ctl za orj : Trace}
    {x xj cp s0p s1p sl sj j q jo s ja zx a qa ak : Nat → Trace}
    (G : MN3Gates P rst ctl za x xj cp s0p s1p sl sj j q jo orj s ja zx a qa ak)
    (V : MN3Env P rst ctl za x s0p s1p R) (TM : MN3Timing P R) (Cs : MN3Causal P Wzc Ex Ec Es) :
    (∀ i, i < 3 → Tok (P.Lj i).hi (j i) P.E (P.g i)) ∧
    Tok P.To orj P.OJ (fun _ => true) ∧
    Tok (ffT P.H P.Tp P.To P.N) (s P.N) P.Z (fun _ => true) ∧
    (∀ i, i < 3 → Tok (P.Ta i) (ak i) (P.XA i) (P.g i) ∧
      Tok (P.Ta i) (ak i) (rx (P.XA i) (P.κ i)) (fun _ => true)) ∧
    (∀ i, i < 3 → ∀ m, P.Xp i (2 * m) ≤ P.E (2 * P.κ i m) ∧ P.D i (2 * m) ≤ P.E (2 * P.κ i m)) ∧
    (∀ i, i < 3 → ∀ j, P.ζ j ≤ P.XA i j) := by
  have st := E_step V.H_ENUM V.H_RANGE Cs TM.H_N
  have Em : ∀ a b, a ≤ b → P.E a ≤ P.E b :=
    mono_of_step P.E (fun j => by have := st j; omega)
  have Eu : ∀ j, j ≤ P.E j := by
    intro j; induction j with
    | zero => omega
    | succ j ih => have := st j; omega
  have Sm : ∀ a b, a ≤ b → P.Sor a ≤ P.Sor b :=
    mono_of_step P.Sor (fun j => by have := st j; have := st (j + 1); omega)
  -- the joins
  have joinE : ∀ i, i < 3 → Tok (P.Lj i).hi (j i) P.E (P.g i) := by
    intro i hi
    obtain ⟨r1, r2, r3, -, -, -⟩ := TM.H_RST_LONG i hi
    obtain ⟨u1, u2, -, -⟩ := TM.H_RST_EARLY i hi
    have hxj : Tok R (xj i) (P.Xp i) (fun _ => true) :=
      ((V.H_X i hi).fifo (P.Wx i) (G.H_WX i hi)).mono (by omega)
    have hcp : Tok (0 + (P.Wc i).hi) (cp i) (P.Cp i) (fun _ => true) :=
      V.H_CTL.fifo (P.Wc i) (G.H_WC i hi)
    have hdec : Tok (0 + (P.Wc i).hi) (fun t => selF i (s0p i t) (s1p i t) (cp i t)) (P.Cp i)
        (P.g i) := by
      have := tok_gate2 hcp (selF i) (selF_off i) (v0 := fun k => b0 (P.sv k))
        (v1 := fun k => b1 (P.sv k)) (fun k t _ h1 h2 => V.H_S_PIN i hi k t h1 h2)
      exact this.gcongr (fun k => by rw [selF_idx hi (V.H_RANGE k)]; rfl)
    have hsl := hdec.fifo (P.Ls i) (y := sl i) (G.H_SEL i hi)
    have hsj := hsl.fifo (P.Wsj i) (G.H_WSJ i hi)
    have hD : Tok R (sj i) (P.D i) (fun _ => true) :=
      (hsj.reindex (V.H_ENUM i hi)).mono (by omega)
    have C : CEl (xj i) (sj i) rst (j i) (q i)
        (fun t => c2B (xj i t) (sj i t) (q i t) (rst t)) (P.Lj i) (P.wjl i) (P.wjh i) :=
      ⟨fun t => c2_spec _ _ _ _, G.H_UJ i hi, G.H_UJ_FB i hi, G.H_UJ_POS i hi⟩
    have n := cel_node C (cel_run C hxj hD V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r3 u1 u2
      (TM.H_DEP_J i hi))
    have n' := n.gcongr (fun _ => Bool.true_and _)
    exact (n'.congr (fun j => (E_rx (V.H_ENUM i hi) j).symm)).lift (V.H_ENUM i hi)
      (fun j => Em j (j + 1) (by omega))
  -- |j: retime each pin onto the selected edges, then OR
  have pin : ∀ i, i < 3 → Tok P.Tj (jo i) P.Sor (P.g i) := by
    intro i hi
    have p := (joinE i hi).fifo (P.Wjo i) (G.H_WJO i hi)
    have p' : Tok P.Tj (jo i) (P.Op i) (P.g i) :=
      p.mono (by unfold MN3Run.Tj; obtain rfl | rfl | rfl : i = 0 ∨ i = 1 ∨ i = 2 := by omega
                 all_goals omega)
    refine tok_retime p' (fun t => ⟨t + 1, ?_⟩) Sm (fun k hk => ?_)
    · have := Eu (t + 1); have := (P.Wjo i).fst_ge (P.E (t + 1)); unfold MN3Run.Op; omega
    · have hs : P.sv k = i := by unfold MN3Run.g at hk; simpa using hk
      unfold MN3Run.Sor
      rw [show 2 * k / 2 = k by omega, show (2 * k + 1) / 2 = k by omega, hs]; exact ⟨rfl, rfl⟩
  have o := or3_same (pin 0 (by omega)) (pin 1 (by omega)) (pin 2 (by omega)) (fun k => by
    have := V.H_RANGE k; unfold MN3Run.g
    obtain h | h | h : P.sv k = 0 ∨ P.sv k = 1 ∨ P.sv k = 2 := by omega
    all_goals simp [h])
  have oj : Tok P.To orj P.OJ (fun _ => true) :=
    o.fifo P.Lo (fun t ht => by rw [G.H_OR3 t ht, or3_spec])
  have zt := ff_tok G.H_LINE oj TM.H_FLUSH P.N TM.H_N (Nat.le_refl _)
  -- the acknowledge C-elements
  have ack : ∀ i, i < 3 → Tok (P.Ta i) (ak i) (P.XA i) (P.g i) := by
    intro i hi
    obtain ⟨-, -, -, r4, r5, r6⟩ := TM.H_RST_LONG i hi
    obtain ⟨-, -, u3, u4⟩ := TM.H_RST_EARLY i hi
    have hja : Tok R (ja i) (P.A i) (P.g i) :=
      ((joinE i hi).fifo (P.Wja i) (G.H_WJA i hi)).mono (by omega)
    have hzx : Tok R (zx i) (P.ZA i) (fun _ => true) :=
      (V.H_ZA.fifo (P.Wza i) (G.H_WZA i hi)).mono (by omega)
    have C : CEl (ja i) (zx i) rst (a i) (qa i)
        (fun t => c2B (ja i t) (zx i t) (qa i t) (rst t)) (P.La i) (P.wal i) (P.wah i) :=
      ⟨fun t => c2_spec _ _ _ _, G.H_UA i hi, G.H_UA_FB i hi, G.H_UA_POS i hi⟩
    have n := cel_node C (cel_run C hja hzx V.H_RST_HI V.H_RST_LO (Nat.le_refl R) r6 u3 u4
      (TM.H_DEP_A i hi))
    exact (n.fifo (P.Wak i) (G.H_WAK i hi)).gcongr (fun k => by simp)
  refine ⟨joinE, oj, zt, fun i hi => ⟨ack i hi, (ack i hi).reindex (V.H_ENUM i hi)⟩,
    fun i hi m => ?_, fun i hi j => ?_⟩
  · have e := E_rx (V.H_ENUM i hi) (2 * m); rw [rx_e] at e; rw [e]
    have := (P.Lj i).fst_ge (P.c i (2 * m))
    unfold MN3Run.τ MN3Run.c at *; omega
  · unfold MN3Run.XA MN3Run.cx MN3Run.ZA
    have := (P.Wza i).fst_ge (P.ζ j)
    have := (P.La i).fst_ge (max (P.A i j) ((P.Wza i).fst (P.ζ j)))
    have := (P.Wak i).fst_ge ((P.La i).fst (max (P.A i j) ((P.Wza i).fst (P.ζ j))))
    omega

/-! ## 5. The event-form obligations from per-arc static inequalities

`Kz = wo + Lo.lo + Dl + Es` is the minimum from a selected join's node edge to
the server's z_ack edge (join → |j pin, |j, the line, the server);
`Kc = Wzc.lo + Ec + (wc + ls + wsj + lj)` the minimum from a z_ack edge to the
next selected join's node edge (z_ack → control sender → ctl_req → decode →
join). `wc, ls, wsj, lj, wo` are lower bounds over the three inputs, `Dl` a
lower bound on the line (stage 0's composite path and every tap; the rise of
a FASTFALL line is slower than that, so `Dl` is conservative for rise
edges). -/

/-- **Static per-arc obligations of `bdc_muxn3`.** -/
structure MN3Static (P : MN3Run) (Wzc : Ret) (Ex Ec Es wc ls wsj lj wo Dl : Nat) : Prop where
  H_MIN : ∀ i, i < 3 → wc ≤ (P.Wc i).lo ∧ ls ≤ (P.Ls i).lo ∧ wsj ≤ (P.Wsj i).lo ∧
    lj ≤ (P.Lj i).lo ∧ wo ≤ (P.Wjo i).lo
  H_DL0 : Dl ≤ (P.H 0).lo
  H_DLT : ∀ i, 1 ≤ i → i < P.N → Dl ≤ (P.Tp i).lo
  /-- **S_J_X** (uj_i env latency through client i, `bd_c2.env_latency` at uj_i). -/
  S_J_X : ∀ i, i < 3 → (P.Lj i).hi + P.wjh i ≤
    (P.Lj i).lo + (P.Wja i).lo + (P.La i).lo + (P.Wak i).lo + Ex + (P.Wx i).lo
  /-- **S_J_C** (uj_i env latency through the server, the control sender and
  decode `i`: the timed content of `bdc_muxn.iso_ctl` for branch `i`). -/
  S_J_C : ∀ i, i < 3 → (P.Lj i).hi + P.wjh i ≤
    (P.Lj i).lo + (wo + P.Lo.lo + Dl + Es) + Wzc.lo + Ec + (P.Wc i).lo + (P.Ls i).lo + (P.Wsj i).lo
  /-- **S_A_FORK** (`bdc_muxn.iso_zack`, branch `ua_i` vs the ctl sender): a
  z_ack edge settles ua_i's loop before the next join edge, launched by the
  same z_ack edge through the control sender, reaches ua_i. -/
  S_A_FORK : ∀ i, i < 3 → (P.Wza i).hi + ((P.La i).hi + P.wah i) ≤
    (Wzc.lo + Ec + (wc + ls + wsj + lj)) + (P.Wja i).lo
  /-- **S_A_RTZ** (`bdc_muxn.rtz` = H_MUX_RTZ): z_ack's pulse at ua_i (either
  polarity) outlasts ua_i's arc + feedback loop plus the z_ack wire's spread. -/
  S_A_RTZ : ∀ i, i < 3 → (P.Wza i).hi + ((P.La i).hi + P.wah i) ≤
    (P.Wza i).lo + (Wzc.lo + Ec + (wc + ls + wsj + lj)) + (wo + P.Lo.lo + Dl + Es)
  /-- **S_A_J**: j_i's edge at ua_i outlasts ua_i's loop until the next j edge
  and the next z_ack edge. -/
  S_A_J : ∀ i, i < 3 →
    (P.Wja i).hi + ((P.La i).hi + P.wah i) ≤
      (wo + P.Lo.lo + Dl + Es) + (Wzc.lo + Ec + (wc + ls + wsj + lj)) + (P.Wja i).lo ∧
    (P.Wja i).hi + ((P.La i).hi + P.wah i) ≤
      2 * (wo + P.Lo.lo + Dl + Es) + (Wzc.lo + Ec + (wc + ls + wsj + lj)) + (P.Wza i).lo

/-- **S_A_RTZ is redundant in the static family when the z_ack branch's
spread is at most the j branch's** (in particular for any fixed-delay run):
S_A_FORK + the second half of S_A_J imply it. So no transport-delay run can
violate S_A_RTZ while satisfying every other field of `MN3Static`; its
necessity is the untimed `MuxN3Proof.muxn3_needs_rtz` (a runt on in0_ack)
and, physically, the event-form `H_DEP_A` instance against `ZA (2k+2)`. -/
theorem rtz_of_fork_j (Wza Wja : Ret) (L Kc Kz : Nat)
    (hsp : Wza.hi + Wja.lo ≤ Wja.hi + Wza.lo)
    (hF : Wza.hi + L ≤ Kc + Wja.lo) (hJ : Wja.hi + L ≤ 2 * Kz + Kc + Wza.lo) :
    Wza.hi + L ≤ Wza.lo + Kc + Kz := by
  omega

section static
variable {P : MN3Run} {Wzc : Ret} {Ex Ec Es wc ls wsj lj wo Dl : Nat}

theorem GE_min (hE : ∀ i, i < 3 → Enum (P.g i) (P.κ i)) (hR : ∀ k, P.sv k < 3)
    (Cs : MN3Causal P Wzc Ex Ec Es) (S : MN3Static P Wzc Ex Ec Es wc ls wsj lj wo Dl) (j : Nat) :
    P.γ j + (wc + ls + wsj + lj) ≤ P.E j := by
  have := γ_le_E hE hR Cs.H_POS j; have := S.H_MIN _ (hR (j / 2)); omega

theorem EZ_min (hE : ∀ i, i < 3 → Enum (P.g i) (P.κ i)) (hR : ∀ k, P.sv k < 3)
    (Cs : MN3Causal P Wzc Ex Ec Es) (S : MN3Static P Wzc Ex Ec Es wc ls wsj lj wo Dl) (hN : 1 ≤ P.N)
    (j : Nat) : P.E j + (wo + P.Lo.lo + Dl + Es) ≤ P.ζ j := by
  have := E_le_Z hE hR Cs.H_POS (fun i hi => (S.H_MIN i hi).2.2.2.2) S.H_DL0 S.H_DLT hN j
  have := Cs.H_SRV j; omega

theorem ZE_min (hE : ∀ i, i < 3 → Enum (P.g i) (P.κ i)) (hR : ∀ k, P.sv k < 3)
    (Cs : MN3Causal P Wzc Ex Ec Es) (S : MN3Static P Wzc Ex Ec Es wc ls wsj lj wo Dl) (hN : 1 ≤ P.N)
    (j : Nat) : P.ζ j + (Wzc.lo + Ec + (wc + ls + wsj + lj)) ≤ P.E (j + 1) := by
  have h1 := Cs.H_CTL_C j
  have hz : 1 ≤ P.ζ j := by
    have := EZ_min hE hR Cs S hN j; have := GE_min hE hR Cs S j; have := Cs.H_POS j; omega
  have h2 := fl Wzc hz
  have h3 := GE_min hE hR Cs S (j + 1)
  omega

theorem γ_mono' (hE : ∀ i, i < 3 → Enum (P.g i) (P.κ i)) (hR : ∀ k, P.sv k < 3)
    (Cs : MN3Causal P Wzc Ex Ec Es) (S : MN3Static P Wzc Ex Ec Es wc ls wsj lj wo Dl) (hN : 1 ≤ P.N) :
    ∀ a b, a ≤ b → P.γ a ≤ P.γ b :=
  mono_of_step P.γ (fun j => by
    have := GE_min hE hR Cs S j; have := EZ_min hE hR Cs S hN j; have := Cs.H_CTL_C j
    have := Wzc.fst_ge (P.ζ j); omega)

theorem Sd_ge (hpos : ∀ j, 1 ≤ P.γ j) (i j : Nat) :
    P.γ j + (P.Wc i).lo + (P.Ls i).lo + (P.Wsj i).lo ≤ P.Sd i j := by
  have h1 := hpos j
  have a1 := fl (P.Wc i) h1
  have a2 := fl (P.Ls i) (c := P.Cp i j) (by unfold MN3Run.Cp; omega)
  have a3 := fl (P.Wsj i) (c := (P.Ls i).fst (P.Cp i j)) (by unfold MN3Run.Cp at *; omega)
  unfold MN3Run.Sd; unfold MN3Run.Cp at *; omega

/-- **The event-form obligations follow from port-level causality and the
static per-arc inequalities** (reset sequencing, the line's flush and `1 ≤ N`
stay as given). -/
theorem muxn3_timing_of_static {R : Nat} (hE : ∀ i, i < 3 → Enum (P.g i) (P.κ i))
    (hR : ∀ k, P.sv k < 3) (Cs : MN3Causal P Wzc Ex Ec Es)
    (S : MN3Static P Wzc Ex Ec Es wc ls wsj lj wo Dl)
    (hRL : ∀ i, i < 3 → (P.Wx i).hi ≤ R ∧ (P.Wc i).hi + (P.Ls i).hi + (P.Wsj i).hi ≤ R ∧
      (P.Lj i).hi + P.wjh i ≤ R ∧ (P.Lj i).hi + (P.Wja i).hi ≤ R ∧ (P.Wza i).hi ≤ R ∧
      (P.La i).hi + P.wah i ≤ R)
    (hRE : ∀ i, i < 3 → R ≤ P.Xp i 0 ∧ R ≤ P.D i 0 ∧ R ≤ P.A i 0 ∧ R ≤ P.ZA i 0)
    (hFL : ∀ i, 1 ≤ i → i < P.N → ∀ k,
      (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 1)) ≤ (P.Tp i).fst (P.OJ (2 * k + 2)) ∧
      (P.Tp i).fst (P.OJ (2 * k + 1)) ≤ (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 2)))
    (hN : 1 ≤ P.N) : MN3Timing P R := by
  have EZ := EZ_min hE hR Cs S hN
  have ZE := ZE_min hE hR Cs S hN
  have GE := GE_min hE hR Cs S
  have GM := γ_mono' hE hR Cs S hN
  have Ep : ∀ j, 1 ≤ P.E j := fun j => by have := GE j; have := Cs.H_POS j; omega
  refine ⟨hRL, hRE, fun i hi j => ⟨?_, ?_⟩, fun i hi j => ⟨?_, ?_⟩, hFL, hN⟩
  · -- uj_i, through client i
    have e0 : P.τ i j = P.E (2 * P.κ i (j / 2) + j % 2) := by
      have := E_rx (hE i hi) j; unfold rx at this; exact this.symm
    have hXA : P.XA i (2 * P.κ i (j / 2) + j % 2) + Ex ≤ P.ξ i (j + 1) := by
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m := ⟨j / 2, by omega⟩
        have := Cs.H_XC_FALL i hi m
        rw [show 2 * m / 2 = m by omega, show 2 * m % 2 = 0 by omega, Nat.add_zero]; exact this
      · obtain ⟨m, rfl⟩ : ∃ m, j = 2 * m + 1 := ⟨j / 2, by omega⟩
        have := Cs.H_XC_RISE i hi m
        rw [show (2 * m + 1) / 2 = m by omega, show (2 * m + 1) % 2 = 1 by omega]; exact this
    have hA : ∀ n, P.E n + (P.Wja i).lo + (P.La i).lo + (P.Wak i).lo ≤ P.XA i n := by
      intro n
      have := Ep n
      have a := fl (P.Wja i) (Ep n)
      have hc : P.A i n ≤ P.cx i n := by unfold MN3Run.cx; omega
      have hAe : P.A i n = (P.Wja i).fst (P.E n) := rfl
      have b := fl (P.La i) (c := P.cx i n) (by omega)
      have c := fl (P.Wak i) (c := (P.La i).fst (P.cx i n)) (by omega)
      show _ ≤ (P.Wak i).fst ((P.La i).fst (P.cx i n)); omega
    have := hA (2 * P.κ i (j / 2) + j % 2)
    have hp : 1 ≤ P.ξ i (j + 1) := by have := Ep (2 * P.κ i (j / 2) + j % 2); omega
    have := fl (P.Wx i) hp
    have : P.Xp i (j + 1) = (P.Wx i).fst (P.ξ i (j + 1)) := rfl
    have t0 : P.c i j + (P.Lj i).lo ≤ P.τ i j := fl (P.Lj i) (by
      have := Cs.H_POS (2 * P.κ i (j / 2) + j % 2)
      have := Sd_ge Cs.H_POS i (2 * P.κ i (j / 2) + j % 2)
      have : P.D i j = P.Sd i (2 * P.κ i (j / 2) + j % 2) := rfl
      unfold MN3Run.c; omega)
    have := S.S_J_X i hi
    omega
  · -- uj_i, through the server, the control sender and decode i
    have e0 : P.τ i j = P.E (2 * P.κ i (j / 2) + j % 2) := by
      have := E_rx (hE i hi) j; unfold rx at this; exact this.symm
    have hk : P.D i (j + 1) = P.Sd i (2 * P.κ i ((j + 1) / 2) + (j + 1) % 2) := rfl
    have hge : 2 * P.κ i (j / 2) + j % 2 + 1 ≤ 2 * P.κ i ((j + 1) / 2) + (j + 1) % 2 := by
      rcases Nat.mod_two_eq_zero_or_one j with hj | hj
      · rw [show (j + 1) / 2 = j / 2 by omega]; omega
      · have := (hE i hi).mono (j / 2); rw [show (j + 1) / 2 = j / 2 + 1 by omega]; omega
    have g := GM _ _ hge
    have hS := Sd_ge Cs.H_POS i (2 * P.κ i ((j + 1) / 2) + (j + 1) % 2)
    have hz := EZ (2 * P.κ i (j / 2) + j % 2)
    have hc := Cs.H_CTL_C (2 * P.κ i (j / 2) + j % 2)
    have hzz : 1 ≤ P.ζ (2 * P.κ i (j / 2) + j % 2) := by
      have := Ep (2 * P.κ i (j / 2) + j % 2); omega
    have hw := fl Wzc hzz
    have t0 : P.c i j + (P.Lj i).lo ≤ P.τ i j := fl (P.Lj i) (by
      have := Cs.H_POS (2 * P.κ i (j / 2) + j % 2)
      have := Sd_ge Cs.H_POS i (2 * P.κ i (j / 2) + j % 2)
      have : P.D i j = P.Sd i (2 * P.κ i (j / 2) + j % 2) := rfl
      unfold MN3Run.c; omega)
    have := S.S_J_C i hi
    omega
  · -- ua_i against the next j edge
    have := (P.Wja i).fst_le (P.E j); have := (P.Wza i).fst_le (P.ζ j)
    have := fl (P.Wja i) (Ep (j + 1))
    have := ZE j; have := EZ j; have := S.S_A_FORK i hi; have := S.S_A_J i hi
    unfold MN3Run.cx MN3Run.A MN3Run.ZA; omega
  · -- ua_i against the next z_ack edge (H_MUX_RTZ)
    have := (P.Wja i).fst_le (P.E j); have := (P.Wza i).fst_le (P.ζ j)
    have hz1 : 1 ≤ P.ζ (j + 1) := by have := EZ (j + 1); have := Ep (j + 1); omega
    have := fl (P.Wza i) hz1
    have := ZE j; have := EZ j; have := EZ (j + 1); have := S.S_A_RTZ i hi; have := S.S_A_J i hi
    unfold MN3Run.cx MN3Run.A MN3Run.ZA; omega

/-- **`muxn3_ok_static`**: `muxn3_ok` from causal partners and per-arc static
inequalities (reset sequencing and the line's flush as given). -/
theorem muxn3_ok_static {R : Nat} {rst ctl za orj : Trace}
    {x xj cp s0p s1p sl sj j q jo s ja zx a qa ak : Nat → Trace}
    (G : MN3Gates P rst ctl za x xj cp s0p s1p sl sj j q jo orj s ja zx a qa ak)
    (V : MN3Env P rst ctl za x s0p s1p R) (Cs : MN3Causal P Wzc Ex Ec Es)
    (S : MN3Static P Wzc Ex Ec Es wc ls wsj lj wo Dl)
    (hRL : ∀ i, i < 3 → (P.Wx i).hi ≤ R ∧ (P.Wc i).hi + (P.Ls i).hi + (P.Wsj i).hi ≤ R ∧
      (P.Lj i).hi + P.wjh i ≤ R ∧ (P.Lj i).hi + (P.Wja i).hi ≤ R ∧ (P.Wza i).hi ≤ R ∧
      (P.La i).hi + P.wah i ≤ R)
    (hRE : ∀ i, i < 3 → R ≤ P.Xp i 0 ∧ R ≤ P.D i 0 ∧ R ≤ P.A i 0 ∧ R ≤ P.ZA i 0)
    (hFL : ∀ i, 1 ≤ i → i < P.N → ∀ k,
      (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 1)) ≤ (P.Tp i).fst (P.OJ (2 * k + 2)) ∧
      (P.Tp i).fst (P.OJ (2 * k + 1)) ≤ (P.H i).fst (ffE P.H P.Tp P.OJ i (2 * k + 2)))
    (hN : 1 ≤ P.N) :
    (∀ i, i < 3 → Tok (P.Lj i).hi (j i) P.E (P.g i)) ∧
    Tok (ffT P.H P.Tp P.To P.N) (s P.N) P.Z (fun _ => true) ∧
    (∀ i, i < 3 → Tok (P.Ta i) (ak i) (P.XA i) (P.g i) ∧
      Tok (P.Ta i) (ak i) (rx (P.XA i) (P.κ i)) (fun _ => true)) := by
  have h := muxn3_ok G V (muxn3_timing_of_static V.H_ENUM V.H_RANGE Cs S hRL hRE hFL hN) Cs
  exact ⟨h.1, h.2.2.1, h.2.2.2.1⟩

/-! ## 6. The decode's select bundling (`bdc_muxn.s_setup`, `s_hold`) in static form -/

/-- **`muxn3_s_pin_of_static`**: H_S_PIN at decode `i` from the s wires
`Ws0 i`, `Ws1 i` (driver → `sel_i` pins, FIFO), the control sender's data
contract (index bits valid on `[sS k, sE k]`, settled `Lsd` before ctl_req
rises, **held until the sender has seen ctl_ack fall**: the `bdc_muxn`
header's "held from ctl_req-rise to ctl_ack-fall") and two static
inequalities per pin: **S_S_SETUP** `Ws.hi ≤ Lsd + Wc.lo` and **S_S_HOLD**
`Wc.hi ≤ (wc + ls + wsj + lj) + Kz + Wzc.lo + Ws.lo` (ctl_req's fall reaches
`sel_i.I2` before the NEXT index, launched by the sender only after it saw
ctl_ack fall, i.e. after a whole return-to-zero through the selected join,
the line and the server, reaches `sel_i`'s s pin). -/
theorem muxn3_s_pin_of_static {s0d s1d : Trace} {s0p s1p : Nat → Trace} {Ws0 Ws1 : Nat → Ret}
    {sS sE : Nat → Nat} {Lsd : Nat}
    (hE : ∀ i, i < 3 → Enum (P.g i) (P.κ i)) (hR : ∀ k, P.sv k < 3)
    (Cs : MN3Causal P Wzc Ex Ec Es) (S : MN3Static P Wzc Ex Ec Es wc ls wsj lj wo Dl) (hN : 1 ≤ P.N)
    (hw0 : ∀ i, i < 3 → ∀ t, (Ws0 i).hi ≤ t → s0p i t = s0d ((Ws0 i).σ t))
    (hw1 : ∀ i, i < 3 → ∀ t, (Ws1 i).hi ≤ t → s1p i t = s1d ((Ws1 i).σ t))
    (H_S_DATA : ∀ k t, sS k ≤ t → t ≤ sE k → s0d t = b0 (P.sv k) ∧ s1d t = b1 (P.sv k))
    (H_S_LEAD : ∀ k, sS k + Lsd ≤ P.γ (2 * k))
    (H_S_HOLD : ∀ k, Wzc.fst (P.ζ (2 * k + 1)) ≤ sE k)
    (S_S_SETUP : ∀ i, i < 3 → (Ws0 i).hi ≤ Lsd + (P.Wc i).lo ∧ (Ws1 i).hi ≤ Lsd + (P.Wc i).lo)
    (S_S_HOLD : ∀ i, i < 3 →
      (P.Wc i).hi ≤ (wc + ls + wsj + lj) + (wo + P.Lo.lo + Dl + Es) + Wzc.lo + (Ws0 i).lo ∧
      (P.Wc i).hi ≤ (wc + ls + wsj + lj) + (wo + P.Lo.lo + Dl + Es) + Wzc.lo + (Ws1 i).lo) :
    ∀ i, i < 3 → ∀ k t, P.Cp i (2 * k) ≤ t → t < P.Cp i (2 * k + 1) →
      s0p i t = b0 (P.sv k) ∧ s1p i t = b1 (P.sv k) := by
  intro i hi k t h1 h2
  have EZ := EZ_min hE hR Cs S hN (2 * k + 1)
  have GE := GE_min hE hR Cs S (2 * k + 1)
  have hz : 1 ≤ P.ζ (2 * k + 1) := by have := Cs.H_POS (2 * k + 1); omega
  have hzc := fl Wzc hz
  have hH := H_S_HOLD k; have hL := H_S_LEAD k
  have c1 := fl (P.Wc i) (Cs.H_POS (2 * k)); have c2 := (P.Wc i).fst_le (P.γ (2 * k + 1))
  unfold MN3Run.Cp at h1 h2
  have su := S_S_SETUP i hi; have sh := S_S_HOLD i hi
  have a1 := (Ws0 i).ge t; have a2 := (Ws0 i).le t
  have b1 := (Ws1 i).ge t; have b2 := (Ws1 i).le t
  rw [hw0 i hi t (by omega), hw1 i hi t (by omega)]
  exact ⟨(H_S_DATA k _ (by omega) (by omega)).1, (H_S_DATA k _ (by omega) (by omega)).2⟩

end static

/-! ## 7. The data path: LUT5 `32'hF0AA_CCF0` per bit -/

open Formal.Cells.Bundling (Gate StableOn winK win_of_stable) in
open Formal.Cells.AMergeGates (DM5) in
/-- **Kleene data LUT5** (H_KLEENE_LUT): with the index bits of `v < 3` on
`I3`, `I4` (definite), the output is the selected data pin's reading,
WHATEVER the two other data pins read (`x` included). Kernel-checked on the
real INIT. -/
theorem dm5_sel (v : Nat) (hv : v < 3) (w0 w1 w2 : K3) (b : Bool)
    (hw : (if v = 0 then w0 else if v = 1 then w1 else w2) = K3.ofBool b) :
    lutK DM5 [w2, w1, w0, K3.ofBool (b0 v), K3.ofBool (b1 v)] = K3.ofBool b := by
  obtain rfl | rfl | rfl : v = 0 ∨ v = 1 ∨ v = 2 := by omega
  · simp only [ite_true] at hw; subst hw
    cases w1 <;> cases w2 <;> cases b <;> decide
  · simp only [show (1 : Nat) ≠ 0 by decide, ite_false, ite_true] at hw; subst hw
    cases w0 <;> cases w2 <;> cases b <;> decide
  · simp only [show (2 : Nat) ≠ 0 by decide, show (2 : Nat) ≠ 1 by decide, ite_false] at hw; subst hw
    cases w0 <;> cases w1 <;> cases b <;> decide

/-- **Data contracts of the four senders** (one data bit). -/
structure MN3DataEnv (P : MN3Run) (Wzc : Ret) (s0d s1d : Trace) (d : Nat → Trace)
    (sS sE : Nat → Nat) (dS dE : Nat → Nat → Nat) (xv : Nat → Nat → Bool) (Lsd Ld : Nat) : Prop where
  /-- **H_S_DATA**: the control sender drives the index bits of `sv k` on `[sS k, sE k]`. -/
  H_S_DATA : ∀ k t, sS k ≤ t → t ≤ sE k → s0d t = b0 (P.sv k) ∧ s1d t = b1 (P.sv k)
  /-- **H_D_DATA**: client `i` drives its `m`-th token's bit on `[dS i m, dE i m]`. -/
  H_D_DATA : ∀ i, i < 3 → ∀ m t, dS i m ≤ t → t ≤ dE i m → d i t = xv i m
  /-- **H_*_LEAD**: settled `Lsd` / `Ld` before the request rises at the port. -/
  H_S_LEAD : ∀ k, sS k + Lsd ≤ P.γ (2 * k)
  H_D_LEAD : ∀ i, i < 3 → ∀ m, dS i m + Ld ≤ P.ξ i (2 * m)
  /-- **H_S_HOLD**: index held until the sender has seen ctl_ack fall. -/
  H_S_HOLD : ∀ k, Wzc.fst (P.ζ (2 * k + 1)) ≤ sE k
  /-- **H_D_HOLD**: client data held until the client has seen its ack rise. -/
  H_D_HOLD : ∀ i, i < 3 → ∀ m, P.XA i (2 * P.κ i m) ≤ dE i m
  H_XPOS : ∀ i, i < 3 → ∀ j, 1 ≤ P.ξ i j

/-- **Data-side static obligations** (EndpointOK forms; `sh0, sh1, dh i` the
LUT5 pins' upper windows from the drivers, `sl0, sl1, dl i` the lower ones,
`Mz` the consumer's margin before z_req, `Hm` the hold margin after z_ack). -/
structure MN3DataStatic (P : MN3Run) (Wzc : Ret) (wc ls wsj lj wo Dl sl0 sh0 sl1 sh1 Mz Hm Lsd Ld : Nat)
    (dl dh : Nat → Nat) : Prop where
  /-- **S_Z_S** (`bdc_muxn.s_setup`, data-LUT form): launch = index settled at
  the sender; data: s wire → zdat.I3/I4 (hi) + `Mz`; request: lead + ctl_req →
  decode → join → |j → line (lo). -/
  S_Z_S : sh0 + Mz ≤ Lsd + (wc + ls + wsj + lj) + wo + P.Lo.lo + Dl ∧
    sh1 + Mz ≤ Lsd + (wc + ls + wsj + lj) + wo + P.Lo.lo + Dl
  /-- **S_Z_D** (data bundling of input `i`): launch = client data settled;
  data: data wire → zdat.I2/I1/I0 (hi) + `Mz`; request: lead + in_i_req → uj_i
  → |j → line (lo). -/
  S_Z_D : ∀ i, i < 3 → dh i + Mz ≤ Ld + (P.Wx i).lo + (P.Lj i).lo + wo + P.Lo.lo + Dl
  /-- **S_HM** (hold margins are sums of MIN delays). -/
  S_HM : Hm ≤ Wzc.lo + sl0 ∧ Hm ≤ Wzc.lo + sl1 ∧
    ∀ i, i < 3 → Hm ≤ (P.Wza i).lo + (P.La i).lo + (P.Wak i).lo + dl i

open Formal.Cells.Bundling (Gate StableOn winK win_of_stable) in
open Formal.Cells.AMergeGates (DM5) in
/-- **`muxn3_data_ok`: the LUT5 delivers the selected input's bit.** For every
control token `k`, from `Mz` before z_req's rise reaches the server until `Hm`
after the server raises z_ack, the output bit `z` equals the bit of input
`sv k`'s token consumed by `k` (`idx (κ (sv k)) k`), with the REAL INIT
`32'hF0AA_CCF0` (Kleene window relation; the two unselected inputs may do
anything, including move). -/
theorem muxn3_data_ok {P : MN3Run} {Wzc : Ret} {Ex Ec Es wc ls wsj lj wo Dl : Nat}
    {s0d s1d z : Trace} {d : Nat → Trace} {sS sE : Nat → Nat} {dS dE : Nat → Nat → Nat}
    {xv : Nat → Nat → Bool} {Lsd Ld sl0 sh0 sl1 sh1 Mz Hm : Nat} {dl dh : Nat → Nat}
    (hz : Gate DM5 [(d 2, dl 2, dh 2), (d 1, dl 1, dh 1), (d 0, dl 0, dh 0), (s0d, sl0, sh0),
      (s1d, sl1, sh1)] z)
    (hw : sl0 ≤ sh0 ∧ sl1 ≤ sh1 ∧ ∀ i, i < 3 → dl i ≤ dh i)
    (hE : ∀ i, i < 3 → Enum (P.g i) (P.κ i)) (hR : ∀ k, P.sv k < 3)
    (Cs : MN3Causal P Wzc Ex Ec Es) (S : MN3Static P Wzc Ex Ec Es wc ls wsj lj wo Dl) (hN : 1 ≤ P.N)
    (D : MN3DataEnv P Wzc s0d s1d d sS sE dS dE xv Lsd Ld)
    (SD : MN3DataStatic P Wzc wc ls wsj lj wo Dl sl0 sh0 sl1 sh1 Mz Hm Lsd Ld dl dh) :
    ∀ k t, P.Z (2 * k) ≤ t + Mz → t ≤ P.ζ (2 * k) + Hm →
      z t = xv (P.sv k) (idx (P.κ (P.sv k)) k) := by
  intro k t h1 h2
  have hv := hR k
  have he := hE _ hv
  have hm := κ_idx he (k := k) (by unfold MN3Run.g; simp)
  -- request-path lower bounds
  have hEZ := E_le_Z hE hR Cs.H_POS (fun i hi => (S.H_MIN i hi).2.2.2.2) S.H_DL0 S.H_DLT hN (2 * k)
  have GE := GE_min hE hR Cs S (2 * k)
  have EZ := EZ_min hE hR Cs S hN (2 * k)
  have EZ1 := EZ_min hE hR Cs S hN (2 * k + 1)
  have ZE := ZE_min hE hR Cs S hN (2 * k)
  have hz0 : 1 ≤ P.ζ (2 * k) := by have := Cs.H_POS (2 * k); omega
  have hz1 : 1 ≤ P.ζ (2 * k + 1) := by have := Cs.H_POS (2 * k); omega
  -- the index pins
  have hsH := D.H_S_HOLD k; have hsL := D.H_S_LEAD k
  have hzc := fl Wzc hz1
  have s0st : StableOn s0d (b0 (P.sv k)) (sS k) (sE k) := fun u a b => (D.H_S_DATA k u a b).1
  have s1st : StableOn s1d (b1 (P.sv k)) (sS k) (sE k) := fun u a b => (D.H_S_DATA k u a b).2
  obtain ⟨hw0, hw1, hwd⟩ := hw
  obtain ⟨hm0, hm1, hmd⟩ := SD.S_HM
  have w0 : winK s0d sl0 sh0 t = K3.ofBool (b0 (P.sv k)) :=
    win_of_stable hw0 s0st (by have := SD.S_Z_S; omega) (by omega)
  have w1 : winK s1d sl1 sh1 t = K3.ofBool (b1 (P.sv k)) :=
    win_of_stable hw1 s1st (by have := SD.S_Z_S; omega) (by omega)
  -- the selected data pin
  have hE2 : P.E (2 * k) = P.τ (P.sv k) (2 * idx (P.κ (P.sv k)) k) := by
    unfold MN3Run.E; rw [show 2 * k / 2 = k by omega, show 2 * k % 2 = 0 by omega, Nat.add_zero]
  have hX : P.Xp (P.sv k) (2 * idx (P.κ (P.sv k)) k) + (P.Lj (P.sv k)).lo ≤ P.E (2 * k) := by
    rw [hE2]; unfold MN3Run.τ
    have hx1 := (P.Wx (P.sv k)).fst_ge (P.ξ (P.sv k) (2 * idx (P.κ (P.sv k)) k))
    have hx2 := D.H_XPOS _ hv (2 * idx (P.κ (P.sv k)) k)
    have := fl (P.Lj (P.sv k)) (c := P.c (P.sv k) (2 * idx (P.κ (P.sv k)) k)) (by
      show 1 ≤ max (P.Xp (P.sv k) (2 * idx (P.κ (P.sv k)) k)) (P.D (P.sv k) (2 * idx (P.κ (P.sv k)) k))
      unfold MN3Run.Xp; omega)
    have : P.Xp (P.sv k) (2 * idx (P.κ (P.sv k)) k) ≤ P.c (P.sv k) (2 * idx (P.κ (P.sv k)) k) := by
      unfold MN3Run.c; omega
    omega
  have hxp := fl (P.Wx (P.sv k)) (D.H_XPOS _ hv (2 * idx (P.κ (P.sv k)) k))
  have hdL := D.H_D_LEAD _ hv (idx (P.κ (P.sv k)) k)
  have hdH := D.H_D_HOLD _ hv (idx (P.κ (P.sv k)) k)
  rw [hm] at hdH
  have hXA : P.ζ (2 * k) + (P.Wza (P.sv k)).lo + (P.La (P.sv k)).lo + (P.Wak (P.sv k)).lo ≤
      P.XA (P.sv k) (2 * k) := by
    have a := fl (P.Wza (P.sv k)) hz0
    have hc : P.ZA (P.sv k) (2 * k) ≤ P.cx (P.sv k) (2 * k) := by unfold MN3Run.cx; omega
    have hZ : P.ZA (P.sv k) (2 * k) = (P.Wza (P.sv k)).fst (P.ζ (2 * k)) := rfl
    have b := fl (P.La (P.sv k)) (c := P.cx (P.sv k) (2 * k)) (by omega)
    have c := fl (P.Wak (P.sv k)) (c := (P.La (P.sv k)).fst (P.cx (P.sv k) (2 * k))) (by omega)
    show _ ≤ (P.Wak (P.sv k)).fst ((P.La (P.sv k)).fst (P.cx (P.sv k) (2 * k))); omega
  have dst : StableOn (d (P.sv k)) (xv (P.sv k) (idx (P.κ (P.sv k)) k))
      (dS (P.sv k) (idx (P.κ (P.sv k)) k)) (dE (P.sv k) (idx (P.κ (P.sv k)) k)) :=
    fun u a b => D.H_D_DATA _ hv _ u a b
  have wd : winK (d (P.sv k)) (dl (P.sv k)) (dh (P.sv k)) t =
      K3.ofBool (xv (P.sv k) (idx (P.κ (P.sv k)) k)) :=
    win_of_stable (hwd _ hv) dst (by have := SD.S_Z_D _ hv; unfold MN3Run.Xp at hX; omega)
      (by have := hmd _ hv; omega)
  apply hz t
  show lutK DM5 [winK (d 2) (dl 2) (dh 2) t, winK (d 1) (dl 1) (dh 1) t, winK (d 0) (dl 0) (dh 0) t,
    winK s0d sl0 sh0 t, winK s1d sl1 sh1 t] = _
  rw [w0, w1]
  apply dm5_sel (P.sv k) hv
  obtain h | h | h : P.sv k = 0 ∨ P.sv k = 1 ∨ P.sv k = 2 := by omega
  · rw [h] at wd ⊢; simpa using wd
  · rw [h] at wd ⊢; simpa using wd
  · rw [h] at wd ⊢; simpa using wd

/-! ## 8. Non-vacuity: a unit-delay run in which every input is selected

Every LUT, wire and feedback net one tick (`uW = Ret.shift 1`, windows
`[1, 1]`), DELAY = 1 (the line is stage 0 only, so `H_FLUSH` is vacuous),
reset high on `[0, 4)`. Control token `k` selects input `k % 3`
(`0, 1, 2, 0, 1, 2, …`), period 20 ticks. Client `i` raises its request for
control token `k` 18 ticks before ctl_req, i.e. during the PREVIOUS token's
transaction (another input's), and waits at its join. The partners are
causal (`MN3Causal run uW 1 1 1`), every static obligation holds (`static`),
`MN3Timing` is DERIVED by `muxn3_timing_of_static`, and `muxn3_ok` applies.
The cell's internal traces are DEFINED by the gate relations (C-elements by
recursion through their own feedback net), so `MN3Gates` holds by
definition. -/
namespace Mn3Wit

def svW (k : Nat) : Nat := k % 3

def run : MN3Run where
  Wx _ := uW
  Wc _ := uW
  Ls _ := uW
  Wsj _ := uW
  Lj _ := uW
  wjl _ := 1
  wjh _ := 1
  Wjo _ := uW
  Wja _ := uW
  Lo := uW
  H _ := uW
  Tp _ := uW
  N := 1
  Wza _ := uW
  La _ := uW
  wal _ := 1
  wah _ := 1
  Wak _ := uW
  ξ i j := 60 * (j / 2) + 20 * i + 10 + 30 * (j % 2)
  γ j := 20 * (j / 2) + 28 + 10 * (j % 2)
  ζ j := 20 * (j / 2) + 36 + 10 * (j % 2)
  sv := svW
  κ i m := 3 * m + i

-- environment
def x (i t : Nat) : Bool := decide (20 * i + 10 ≤ t ∧ (t - (20 * i + 10)) % 60 < 30)
def ctl (t : Nat) : Bool := decide (28 ≤ t ∧ (t - 28) % 20 < 10)
def za (t : Nat) : Bool := decide (36 ≤ t ∧ (t - 36) % 20 < 10)
/-- The control sender's index bits: token `k`'s index from `20k + 28` (its
ctl_req rise) to `20k + 47` (it has seen ctl_ack fall). -/
def s0d (t : Nat) : Bool := b0 (svW ((t - 28) / 20))
def s1d (t : Nat) : Bool := b1 (svW ((t - 28) / 20))
-- the cell, one tick per primitive
def xj (i t : Nat) : Bool := x i (t - 1)
def cp (_ : Nat) (t : Nat) : Bool := ctl (t - 1)
def s0p (_ : Nat) (t : Nat) : Bool := s0d (t - 1)
def s1p (_ : Nat) (t : Nat) : Bool := s1d (t - 1)
def sl (i t : Nat) : Bool := selF i (s0p i (t - 1)) (s1p i (t - 1)) (cp i (t - 1))
def sj (i t : Nat) : Bool := sl i (t - 1)
def jW (i : Nat) : Nat → Bool
  | 0 => false
  | 1 => c2B (xj i 0) (sj i 0) false (rstW 0)
  | t + 2 => c2B (xj i (t + 1)) (sj i (t + 1)) (jW i t) (rstW (t + 1))
def q (i t : Nat) : Bool := jW i (t - 1)
def jo (i t : Nat) : Bool := jW i (t - 1)
def orj (t : Nat) : Bool := or3 (jo 0 (t - 1)) (jo 1 (t - 1)) (jo 2 (t - 1))
def line (n t : Nat) : Bool := orj (t - n)
def ja (i t : Nat) : Bool := jW i (t - 1)
def zx (_ : Nat) (t : Nat) : Bool := za (t - 1)
def aW (i : Nat) : Nat → Bool
  | 0 => false
  | 1 => c2B (ja i 0) (zx i 0) false (rstW 0)
  | t + 2 => c2B (ja i (t + 1)) (zx i (t + 1)) (aW i t) (rstW (t + 1))
def qa (i t : Nat) : Bool := aW i (t - 1)
def ak (i t : Nat) : Bool := aW i (t - 1)
/-- z_req at the server (the line's last stage, DELAY = 1). -/
def zr (t : Nat) : Bool := line 1 t

theorem gates : MN3Gates run rstW ctl za x xj cp s0p s1p sl sj jW q jo orj line ja zx aW qa ak where
  H_WX _ _ _ _ := rfl
  H_WC _ _ _ _ := rfl
  H_SEL _ _ _ _ := rfl
  H_WSJ _ _ _ _ := rfl
  H_UJ i _ t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UJ_FB _ _ := win11 (fun _ _ => rfl)
  H_UJ_POS _ _ := Nat.le_of_ble_eq_true rfl
  H_WJO _ _ _ _ := rfl
  H_OR3 _ _ := rfl
  H_LINE := ⟨fun _ _ => rfl, fun i h1 h2 => by
    have : (1 : Nat) ≤ i := h1
    have : i < 1 := h2
    omega⟩
  H_WJA _ _ _ _ := rfl
  H_WZA _ _ _ _ := rfl
  H_UA i _ t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UA_FB _ _ := win11 (fun _ _ => rfl)
  H_UA_POS _ _ := Nat.le_of_ble_eq_true rfl
  H_WAK _ _ _ _ := rfl

theorem enum (i : Nat) (hi : i < 3) : Enum (run.g i) (run.κ i) where
  mono m := by show 3 * m + i < 3 * (m + 1) + i; omega
  hit m := by show decide ((3 * m + i) % 3 = i) = true; simp; omega
  all k h := ⟨k / 3, by
    have h : decide (k % 3 = i) = true := h
    simp at h; show 3 * (k / 3) + i = k; omega⟩

theorem idx_eq (i k : Nat) (hi : i < 3) (hk : k % 3 = i) : idx (run.κ i) k = k / 3 := by
  have := idx_κ (enum i hi) (k / 3)
  rw [show run.κ i (k / 3) = k by show 3 * (k / 3) + i = k; omega] at this
  exact this

/-! Closed forms of the derived edges. -/
theorem Xp_eq (i j : Nat) : run.Xp i j = 60 * (j / 2) + 20 * i + 11 + 30 * (j % 2) := by
  show uW.fst (60 * (j / 2) + 20 * i + 10 + 30 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem Cp_eq (i j : Nat) : run.Cp i j = 20 * (j / 2) + 29 + 10 * (j % 2) := by
  show uW.fst (20 * (j / 2) + 28 + 10 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem Sd_eq (i j : Nat) : run.Sd i j = 20 * (j / 2) + 31 + 10 * (j % 2) := by
  show uW.fst (uW.fst (run.Cp i j)) = _
  rw [Cp_eq, fuW (20 * (j / 2) + 29 + 10 * (j % 2)) (by omega),
    fuW (20 * (j / 2) + 29 + 10 * (j % 2) + 1) (by omega)]; omega
theorem D_eq (i j : Nat) : run.D i j = 60 * (j / 2) + 20 * i + 31 + 10 * (j % 2) := by
  show run.Sd i (2 * (3 * (j / 2) + i) + j % 2) = _; rw [Sd_eq]; omega
theorem c_eq (i j : Nat) : run.c i j = 60 * (j / 2) + 20 * i + 31 + 10 * (j % 2) := by
  show max (run.Xp i j) (run.D i j) = _; rw [Xp_eq, D_eq]; omega
theorem τ_eq (i j : Nat) : run.τ i j = 60 * (j / 2) + 20 * i + 32 + 10 * (j % 2) := by
  show uW.fst (run.c i j) = _; rw [c_eq, fuW _ (by omega)]; omega

theorem E_eq (j : Nat) : run.E j = 20 * (j / 2) + 32 + 10 * (j % 2) := by
  unfold MN3Run.E
  have hs : run.sv (j / 2) = j / 2 % 3 := rfl
  rw [hs, idx_eq (j / 2 % 3) (j / 2) (by omega) rfl, τ_eq]
  omega

theorem Op_eq (i j : Nat) : run.Op i j = run.E j + 1 := by
  show uW.fst (run.E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem A_eq (i j : Nat) : run.A i j = run.E j + 1 := by
  show uW.fst (run.E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
theorem ZA_eq (i j : Nat) : run.ZA i j = 20 * (j / 2) + 37 + 10 * (j % 2) := by
  show uW.fst (20 * (j / 2) + 36 + 10 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem OJ_eq (j : Nat) : run.OJ j = run.E j + 2 := by
  show uW.fst (run.Op (run.sv (j / 2)) j) = _
  rw [Op_eq, fuW _ (by omega)]
theorem Z_eq (j : Nat) : run.Z j = run.E j + 3 := by
  show uW.fst (run.OJ j) = _
  rw [OJ_eq, fuW _ (by omega)]
theorem XA_eq (i j : Nat) : run.XA i j = 20 * (j / 2) + 39 + 10 * (j % 2) := by
  have hm : max (run.E j + 1) (20 * (j / 2) + 37 + 10 * (j % 2)) = 20 * (j / 2) + 37 + 10 * (j % 2) := by
    rw [E_eq]; omega
  show uW.fst (uW.fst (max (run.A i j) (run.ZA i j))) = _
  rw [A_eq, ZA_eq, hm, fuW (20 * (j / 2) + 37 + 10 * (j % 2)) (by omega),
    fuW (20 * (j / 2) + 37 + 10 * (j % 2) + 1) (by omega)]; omega

theorem env : MN3Env run rstW ctl za x s0p s1p 4 where
  H_RST_HI := rstW_hi
  H_RST_LO := rstW_lo
  H_X i _ := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 60 * (0 / 2) + 20 * i + 10 + 30 * (0 % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
    · have h1 : 60 * (2 * k / 2) + 20 * i + 10 + 30 * (2 * k % 2) ≤ t := h1
      have h2 : t < 60 * ((2 * k + 1) / 2) + 20 * i + 10 + 30 * ((2 * k + 1) % 2) := h2
      simp only [x, decide_eq_true_eq]; omega
    · have h1 : 60 * ((2 * k + 1) / 2) + 20 * i + 10 + 30 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 60 * ((2 * k + 2) / 2) + 20 * i + 10 + 30 * ((2 * k + 2) % 2) := h2
      simp only [x, decide_eq_false_iff_not]; omega
  H_CTL := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 20 * (0 / 2) + 28 + 10 * (0 % 2) := h2
      simp only [ctl, decide_eq_false_iff_not]; omega
    · have h1 : 20 * (2 * k / 2) + 28 + 10 * (2 * k % 2) ≤ t := h1
      have h2 : t < 20 * ((2 * k + 1) / 2) + 28 + 10 * ((2 * k + 1) % 2) := h2
      simp only [ctl, decide_eq_true_eq]; omega
    · have h1 : 20 * ((2 * k + 1) / 2) + 28 + 10 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 20 * ((2 * k + 2) / 2) + 28 + 10 * ((2 * k + 2) % 2) := h2
      simp only [ctl, decide_eq_false_iff_not]; omega
  H_ZA := by
    refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
    · have h2 : t < 20 * (0 / 2) + 36 + 10 * (0 % 2) := h2
      simp only [za, decide_eq_false_iff_not]; omega
    · have h1 : 20 * (2 * k / 2) + 36 + 10 * (2 * k % 2) ≤ t := h1
      have h2 : t < 20 * ((2 * k + 1) / 2) + 36 + 10 * ((2 * k + 1) % 2) := h2
      simp only [za, decide_eq_true_eq]; omega
    · have h1 : 20 * ((2 * k + 1) / 2) + 36 + 10 * ((2 * k + 1) % 2) ≤ t := h1
      have h2 : t < 20 * ((2 * k + 2) / 2) + 36 + 10 * ((2 * k + 2) % 2) := h2
      simp only [za, decide_eq_false_iff_not]; omega
  H_RANGE k := by show k % 3 < 3; omega
  H_ENUM := enum
  H_S_PIN i _ k t h1 h2 := by
    rw [Cp_eq] at h1 h2
    have e : (t - 1 - 28) / 20 = k := by omega
    show b0 (svW ((t - 1 - 28) / 20)) = b0 (svW k) ∧ b1 (svW ((t - 1 - 28) / 20)) = b1 (svW k)
    rw [e]; exact ⟨rfl, rfl⟩

/-- The partners are causal: each reacts one tick after the edge it sees. -/
theorem causal : MN3Causal run uW 1 1 1 where
  H_XC_FALL i _ m := by
    rw [XA_eq]; show _ ≤ 60 * ((2 * m + 1) / 2) + 20 * i + 10 + 30 * ((2 * m + 1) % 2)
    show 20 * (2 * (3 * m + i) / 2) + 39 + 10 * (2 * (3 * m + i) % 2) + 1 ≤ _; omega
  H_XC_RISE i _ m := by
    rw [XA_eq]; show _ ≤ 60 * ((2 * m + 2) / 2) + 20 * i + 10 + 30 * ((2 * m + 2) % 2)
    show 20 * ((2 * (3 * m + i) + 1) / 2) + 39 + 10 * ((2 * (3 * m + i) + 1) % 2) + 1 ≤ _; omega
  H_CTL_C j := by
    show uW.fst (20 * (j / 2) + 36 + 10 * (j % 2)) + 1 ≤ 20 * ((j + 1) / 2) + 28 + 10 * ((j + 1) % 2)
    rw [fuW _ (by omega)]; omega
  H_SRV j := by
    rw [Z_eq, E_eq]; show _ ≤ 20 * (j / 2) + 36 + 10 * (j % 2); omega
  H_ES := Nat.le_refl 1
  H_POS j := by show 1 ≤ 20 * (j / 2) + 28 + 10 * (j % 2); omega

/-- Every static per-arc obligation holds with unit delays (bounds all 1). -/
theorem static : MN3Static run uW 1 1 1 1 1 1 1 1 1 where
  H_MIN _ _ := ⟨Nat.le_refl 1, Nat.le_refl 1, Nat.le_refl 1, Nat.le_refl 1, Nat.le_refl 1⟩
  H_DL0 := Nat.le_refl 1
  H_DLT _ _ _ := Nat.le_refl 1
  S_J_X _ _ := Nat.le_of_ble_eq_true rfl
  S_J_C _ _ := Nat.le_of_ble_eq_true rfl
  S_A_FORK _ _ := Nat.le_of_ble_eq_true rfl
  S_A_RTZ _ _ := Nat.le_of_ble_eq_true rfl
  S_A_J _ _ := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

theorem timing : MN3Timing run 4 :=
  muxn3_timing_of_static enum env.H_RANGE causal static
    (fun _ _ => ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
      Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩)
    (fun i _ => ⟨by rw [Xp_eq]; omega, by rw [D_eq]; omega, by rw [A_eq, E_eq]; omega,
      by rw [ZA_eq]; omega⟩)
    (fun i h1 h2 => by have : (1 : Nat) ≤ i := h1; have : i < 1 := h2; omega)
    (Nat.le_refl 1)

/-- **Non-vacuity of `muxn3_ok`** on the unit-delay run: every hypothesis is
discharged (timing derived from causality + static obligations), so its
conclusions hold: one z_req transaction per control token, and in_i_ack
exactly in the tokens selecting `i` (`k % 3 = i`). -/
theorem witness :
    (∀ i, i < 3 → Tok (run.Lj i).hi (jW i) run.E (run.g i)) ∧
    Tok (ffT run.H run.Tp run.To run.N) (line run.N) run.Z (fun _ => true) ∧
    (∀ i, i < 3 → Tok (run.Ta i) (ak i) (run.XA i) (run.g i)) := by
  have h := muxn3_ok gates env timing causal
  exact ⟨h.1, h.2.2.1, fun i hi => (h.2.2.2.1 i hi).1⟩

/-- The s-pin bundling of the run is also an INSTANCE of the static form
(`muxn3_s_pin_of_static`): s driver bits valid on `[20k + 28, 20k + 47]`
(from ctl_req's rise until ctl_ack's fall has been seen), one-tick s wires. -/
theorem s_pin_static :
    ∀ i, i < 3 → ∀ k t, run.Cp i (2 * k) ≤ t → t < run.Cp i (2 * k + 1) →
      s0p i t = b0 (run.sv k) ∧ s1p i t = b1 (run.sv k) :=
  muxn3_s_pin_of_static (Ws0 := fun _ => uW) (Ws1 := fun _ => uW) (sS := fun k => 20 * k + 28)
    (sE := fun k => 20 * k + 47) (Lsd := 0) enum env.H_RANGE causal static (Nat.le_refl 1)
    (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl)
    (fun k t h1 h2 => by
      have e : (t - 28) / 20 = k := by omega
      show b0 (svW ((t - 28) / 20)) = b0 (svW k) ∧ b1 (svW ((t - 28) / 20)) = b1 (svW k)
      rw [e]; exact ⟨rfl, rfl⟩)
    (fun k => by show 20 * k + 28 + 0 ≤ 20 * (2 * k / 2) + 28 + 10 * (2 * k % 2); omega)
    (fun k => by
      show uW.fst (20 * ((2 * k + 1) / 2) + 36 + 10 * ((2 * k + 1) % 2)) ≤ 20 * k + 47
      rw [fuW _ (by omega)]; omega)
    (fun _ _ => ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩)
    (fun _ _ => ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩)

set_option maxRecDepth 100000 in
/-- Sample values (kernel `decide` on the simulated traces): token 0
(input 0): in0_ack high at 40, in1_ack and in2_ack low; token 1 (input 1):
in1_ack high at 60, the others low; token 2 (input 2): in2_ack high at 80, the
others low; z_req high in each of the three tokens (at `Z(2k) = 20k + 35`)
and low between; input 1's request is high at 30 while its join is still low
(it waits during input 0's transaction). -/
theorem witness_values :
    ak 0 40 = true ∧ ak 1 40 = false ∧ ak 2 40 = false ∧
    ak 0 60 = false ∧ ak 1 60 = true ∧ ak 2 60 = false ∧
    ak 0 80 = false ∧ ak 1 80 = false ∧ ak 2 80 = true ∧
    zr 35 = true ∧ zr 55 = true ∧ zr 75 = true ∧ zr 50 = false ∧
    x 1 30 = true ∧ jW 1 30 = false := by
  decide

/-! ### The data path on the same run

One data bit per input: client `i`'s `m`-th token carries
`xvW i m = (3m + i even)` (= parity of the control token that consumes it),
driven from its request rise `60m + 20i + 10` for 60 ticks; the LUT5 is the
REAL INIT `32'hF0AA_CCF0` with a one-tick transport delay on every pin
(window relation by `Bundling.transport_gate`). -/

def xvW (i m : Nat) : Bool := decide ((3 * m + i) % 2 = 0)
def dW (i t : Nat) : Bool := xvW i ((t - (20 * i + 10)) / 60)
def zW (t : Nat) : Bool :=
  lutB Formal.Cells.AMergeGates.DM5 [dW 2 (t - 1), dW 1 (t - 1), dW 0 (t - 1), s0d (t - 1), s1d (t - 1)]

theorem zW_gate : Formal.Cells.Bundling.Gate Formal.Cells.AMergeGates.DM5
    [(dW 2, 1, 1), (dW 1, 1, 1), (dW 0, 1, 1), (s0d, 1, 1), (s1d, 1, 1)] zW :=
  Formal.Cells.Bundling.transport_gate Formal.Cells.AMergeGates.DM5
    [(dW 2, 1, 1, 1), (dW 1, 1, 1, 1), (dW 0, 1, 1, 1), (s0d, 1, 1, 1), (s1d, 1, 1, 1)] zW
    (by intro p hp; simp only [List.mem_cons, List.not_mem_nil, or_false] at hp
        rcases hp with rfl | rfl | rfl | rfl | rfl <;> exact ⟨Nat.le_refl _, Nat.le_refl _⟩)
    (fun _ => rfl)

theorem data_env : MN3DataEnv run uW s0d s1d dW (fun k => 20 * k + 28) (fun k => 20 * k + 47)
    (fun i m => 60 * m + 20 * i + 10) (fun i m => 60 * m + 20 * i + 69) xvW 0 0 where
  H_S_DATA k t h1 h2 := by
    have e : (t - 28) / 20 = k := by omega
    show b0 (svW ((t - 28) / 20)) = b0 (svW k) ∧ b1 (svW ((t - 28) / 20)) = b1 (svW k)
    rw [e]; exact ⟨rfl, rfl⟩
  H_D_DATA i _ m t h1 h2 := by
    show xvW i ((t - (20 * i + 10)) / 60) = xvW i m
    rw [show (t - (20 * i + 10)) / 60 = m by omega]
  H_S_LEAD k := by show 20 * k + 28 + 0 ≤ 20 * (2 * k / 2) + 28 + 10 * (2 * k % 2); omega
  H_D_LEAD i _ m := by show 60 * m + 20 * i + 10 + 0 ≤ 60 * (2 * m / 2) + 20 * i + 10 + 30 * (2 * m % 2); omega
  H_S_HOLD k := by
    show uW.fst (20 * ((2 * k + 1) / 2) + 36 + 10 * ((2 * k + 1) % 2)) ≤ 20 * k + 47
    rw [fuW _ (by omega)]; omega
  H_D_HOLD i _ m := by
    rw [XA_eq]; show 20 * (2 * (3 * m + i) / 2) + 39 + 10 * (2 * (3 * m + i) % 2) ≤ _; omega
  H_XPOS i _ j := by show 1 ≤ 60 * (j / 2) + 20 * i + 10 + 30 * (j % 2); omega

theorem data_static : MN3DataStatic run uW 1 1 1 1 1 1 1 1 1 1 0 2 0 0 (fun _ => 1) (fun _ => 1) where
  S_Z_S := ⟨by decide, by decide⟩
  S_Z_D _ _ := Nat.le_of_ble_eq_true rfl
  S_HM := ⟨by decide, by decide, fun _ _ => Nat.le_of_ble_eq_true rfl⟩

/-- **Non-vacuity of `muxn3_data_ok`**: in every control token `k`, from
z_req's arrival at the server until 2 ticks after z_ack rises, the LUT5's
output is the bit of input `k % 3`'s token `k / 3`. -/
theorem data_witness : ∀ k t, run.Z (2 * k) ≤ t + 0 → t ≤ run.ζ (2 * k) + 2 →
    zW t = xvW (k % 3) (idx (run.κ (k % 3)) k) :=
  muxn3_data_ok zW_gate ⟨Nat.le_refl _, Nat.le_refl _, fun _ _ => Nat.le_refl _⟩ enum env.H_RANGE
    causal static (Nat.le_refl 1) data_env data_static

set_option maxRecDepth 100000 in
/-- Not degenerate: in tokens 0..5 (inputs 0, 1, 2, 0, 1, 2) the delivered
bit at `Z(2k) = 20k + 35` is `1, 0, 1, 0, 1, 0`, and in each token at least one
unselected input carries the opposite bit at that instant. -/
theorem data_values :
    zW 35 = true ∧ zW 55 = false ∧ zW 75 = true ∧ zW 95 = false ∧ zW 115 = true ∧ zW 135 = false ∧
    dW 1 34 = false ∧ dW 0 54 = true ∧ dW 1 74 = false ∧ dW 2 94 = true ∧ dW 0 114 = false ∧
    dW 1 134 = true := by
  decide

end Mn3Wit

/-! ## 9. One-tick counter-run for the decode's select setup (`bdc_muxn.s_setup`)

Same cell and control timing as `Mn3Wit`, but every client re-raises its
request as EARLY as causality allows (`Ex = 1` after its ack fell, i.e. two
control tokens before the one that consumes it), so that at the start of
every control token the client the PREVIOUS token selected is already
waiting at its join. Two runs of this environment:

* `bnd`: s wires one tick (`S_S_SETUP` holds with equality: `Ws.hi = 1 =
  Lsd + Wc.lo`). All hypotheses of `muxn3_ok_static` hold (H_S_PIN through
  `muxn3_s_pin_of_static`) and its conclusions follow (`bnd_ok`).
* `cex`: s wires TWO ticks (`S_S_SETUP` fails by one tick; every other
  hypothesis of `muxn3_s_pin_of_static` and of `muxn3_ok_static` except
  H_S_PIN holds, by the same proofs). For one tick at the start of each
  control token every decode reads the previous token's index, so decode
  `sv (k-1)` emits a one-tick runt; the waiting client's join takes it as a
  request and FIRES in a token that does not select it (`cex_fails`): join 0
  is high at 52, inside control token 1 (which selects input 1), and in0_ack
  then rises in token 1 too: input 0's token is consumed by the wrong control
  token. -/
namespace Mn3Cex
open Mn3Wit (svW ctl za s0d s1d cp sl sj)

/-- Client `i`'s request edges: rise at `60m + 20i + 10` for `m = 0`, at
`60m + 20i - 10` (one tick after its previous ack fell) for `m ≥ 1`; fall at
`60m + 20i + 40` (one tick after its ack rose). -/
def ξC (i j : Nat) : Nat := 60 * (j / 2) + 20 * i + 10 + 30 * (j % 2) - 20 * min (j / 2) (1 - j % 2)

def run : MN3Run := { Mn3Wit.run with ξ := ξC }

def x (i t : Nat) : Bool :=
  decide ((20 * i + 10 ≤ t ∧ t < 20 * i + 40) ∨ (20 * i + 50 ≤ t ∧ (t - (20 * i + 50)) % 60 < 50))

/-- s pins through a wire of `d` ticks (`d = 1`: boundary, `d = 2`: violation). -/
def s0p (d : Nat) (_ : Nat) (t : Nat) : Bool := s0d (t - d)
def s1p (d : Nat) (_ : Nat) (t : Nat) : Bool := s1d (t - d)
def xj (i t : Nat) : Bool := x i (t - 1)
def slD (d i t : Nat) : Bool := selF i (s0p d i (t - 1)) (s1p d i (t - 1)) (cp i (t - 1))
def sjD (d i t : Nat) : Bool := slD d i (t - 1)
def jD (d i : Nat) : Nat → Bool
  | 0 => false
  | 1 => c2B (xj i 0) (sjD d i 0) false (rstW 0)
  | t + 2 => c2B (xj i (t + 1)) (sjD d i (t + 1)) (jD d i t) (rstW (t + 1))
def q (d i t : Nat) : Bool := jD d i (t - 1)
def jo (d i t : Nat) : Bool := jD d i (t - 1)
def orj (d t : Nat) : Bool := or3 (jo d 0 (t - 1)) (jo d 1 (t - 1)) (jo d 2 (t - 1))
def line (d n t : Nat) : Bool := orj d (t - n)
def ja (d i t : Nat) : Bool := jD d i (t - 1)
def aD (d i : Nat) : Nat → Bool
  | 0 => false
  | 1 => c2B (ja d i 0) (Mn3Wit.zx i 0) false (rstW 0)
  | t + 2 => c2B (ja d i (t + 1)) (Mn3Wit.zx i (t + 1)) (aD d i t) (rstW (t + 1))
def qa (d i t : Nat) : Bool := aD d i (t - 1)
def ak (d i t : Nat) : Bool := aD d i (t - 1)

theorem gates (d : Nat) : MN3Gates run rstW ctl za x xj cp (s0p d) (s1p d) (slD d) (sjD d) (jD d)
    (q d) (jo d) (orj d) (line d) (ja d) Mn3Wit.zx (aD d) (qa d) (ak d) where
  H_WX _ _ _ _ := rfl
  H_WC _ _ _ _ := rfl
  H_SEL _ _ _ _ := rfl
  H_WSJ _ _ _ _ := rfl
  H_UJ i _ t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UJ_FB _ _ := win11 (fun _ _ => rfl)
  H_UJ_POS _ _ := Nat.le_of_ble_eq_true rfl
  H_WJO _ _ _ _ := rfl
  H_OR3 _ _ := rfl
  H_LINE := ⟨fun _ _ => rfl, fun i h1 h2 => by
    have : (1 : Nat) ≤ i := h1
    have : i < 1 := h2
    omega⟩
  H_WJA _ _ _ _ := rfl
  H_WZA _ _ _ _ := rfl
  H_UA i _ t ht := by
    match t, ht with
    | 1, _ => rfl
    | t + 2, _ => rfl
  H_UA_FB _ _ := win11 (fun _ _ => rfl)
  H_UA_POS _ _ := Nat.le_of_ble_eq_true rfl
  H_WAK _ _ _ _ := rfl

theorem enum (i : Nat) (hi : i < 3) : Enum (run.g i) (run.κ i) := Mn3Wit.enum i hi

theorem Xp_eq (i j : Nat) : run.Xp i j = ξC i j + 1 := by
  show uW.fst (ξC i j) = _; rw [fuW _ (by unfold ξC; omega)]
theorem D_eq (i j : Nat) : run.D i j = 60 * (j / 2) + 20 * i + 31 + 10 * (j % 2) := Mn3Wit.D_eq i j
theorem c_eq (i j : Nat) : run.c i j = 60 * (j / 2) + 20 * i + 31 + 10 * (j % 2) := by
  show max (run.Xp i j) (run.D i j) = _; rw [Xp_eq, D_eq]; unfold ξC; omega
theorem τ_eq (i j : Nat) : run.τ i j = 60 * (j / 2) + 20 * i + 32 + 10 * (j % 2) := by
  show uW.fst (run.c i j) = _; rw [c_eq, fuW _ (by omega)]; omega
theorem E_eq (j : Nat) : run.E j = 20 * (j / 2) + 32 + 10 * (j % 2) := by
  unfold MN3Run.E
  have hs : run.sv (j / 2) = j / 2 % 3 := rfl
  have hi : idx (run.κ (j / 2 % 3)) (j / 2) = j / 2 / 3 := by
    have := idx_κ (enum (j / 2 % 3) (by omega)) (j / 2 / 3)
    rw [show run.κ (j / 2 % 3) (j / 2 / 3) = j / 2 by show 3 * (j / 2 / 3) + j / 2 % 3 = j / 2; omega]
      at this
    exact this
  rw [hs, hi, τ_eq]
  omega
theorem E_same (j : Nat) : run.E j = Mn3Wit.run.E j := by rw [E_eq, Mn3Wit.E_eq]
theorem ZA_eq (i j : Nat) : run.ZA i j = 20 * (j / 2) + 37 + 10 * (j % 2) := by
  show uW.fst (20 * (j / 2) + 36 + 10 * (j % 2)) = _; rw [fuW _ (by omega)]; omega
theorem XA_eq (i j : Nat) : run.XA i j = 20 * (j / 2) + 39 + 10 * (j % 2) := by
  have hm : max (run.E j + 1) (20 * (j / 2) + 37 + 10 * (j % 2)) = 20 * (j / 2) + 37 + 10 * (j % 2) := by
    rw [E_eq]; omega
  have hA : run.A i j = run.E j + 1 := by
    show uW.fst (run.E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
  show uW.fst (uW.fst (max (run.A i j) (run.ZA i j))) = _
  rw [hA, ZA_eq, hm, fuW (20 * (j / 2) + 37 + 10 * (j % 2)) (by omega),
    fuW (20 * (j / 2) + 37 + 10 * (j % 2) + 1) (by omega)]; omega
theorem Z_eq (j : Nat) : run.Z j = run.E j + 3 := by
  have h1 : run.Op (run.sv (j / 2)) j = run.E j + 1 := by
    show uW.fst (run.E j) = _; rw [fuW _ (by rw [E_eq]; omega)]
  show uW.fst (uW.fst (run.Op (run.sv (j / 2)) j)) = _
  rw [h1, fuW (run.E j + 1) (by omega), fuW (run.E j + 1 + 1) (by omega)]

theorem H_X : ∀ i, i < 3 → Tok 0 (x i) (run.ξ i) (fun _ => true) := by
  intro i _
  refine ⟨fun t _ h2 => ?_, fun k t _ h1 h2 => ?_, fun k t _ h1 h2 => ?_⟩
  · have h2 : t < ξC i 0 := h2
    unfold ξC at h2
    simp only [x, decide_eq_false_iff_not]; omega
  · have h1 : ξC i (2 * k) ≤ t := h1
    have h2 : t < ξC i (2 * k + 1) := h2
    unfold ξC at h1 h2
    simp only [x, decide_eq_true_eq]; omega
  · have h1 : ξC i (2 * k + 1) ≤ t := h1
    have h2 : t < ξC i (2 * k + 2) := h2
    unfold ξC at h1 h2
    simp only [x, decide_eq_false_iff_not]; omega

theorem causal : MN3Causal run uW 1 1 1 where
  H_XC_FALL i _ m := by
    rw [XA_eq]; show _ ≤ ξC i (2 * m + 1); unfold ξC
    show 20 * (2 * (3 * m + i) / 2) + 39 + 10 * (2 * (3 * m + i) % 2) + 1 ≤ _; omega
  H_XC_RISE i _ m := by
    rw [XA_eq]; show _ ≤ ξC i (2 * m + 2); unfold ξC
    show 20 * ((2 * (3 * m + i) + 1) / 2) + 39 + 10 * ((2 * (3 * m + i) + 1) % 2) + 1 ≤ _; omega
  H_CTL_C j := by
    show uW.fst (20 * (j / 2) + 36 + 10 * (j % 2)) + 1 ≤ 20 * ((j + 1) / 2) + 28 + 10 * ((j + 1) % 2)
    rw [fuW _ (by omega)]; omega
  H_SRV j := by
    rw [Z_eq, E_eq]; show _ ≤ 20 * (j / 2) + 36 + 10 * (j % 2); omega
  H_ES := Nat.le_refl 1
  H_POS j := by show 1 ≤ 20 * (j / 2) + 28 + 10 * (j % 2); omega

theorem static : MN3Static run uW 1 1 1 1 1 1 1 1 1 where
  H_MIN _ _ := ⟨Nat.le_refl 1, Nat.le_refl 1, Nat.le_refl 1, Nat.le_refl 1, Nat.le_refl 1⟩
  H_DL0 := Nat.le_refl 1
  H_DLT _ _ _ := Nat.le_refl 1
  S_J_X _ _ := Nat.le_of_ble_eq_true rfl
  S_J_C _ _ := Nat.le_of_ble_eq_true rfl
  S_A_FORK _ _ := Nat.le_of_ble_eq_true rfl
  S_A_RTZ _ _ := Nat.le_of_ble_eq_true rfl
  S_A_J _ _ := ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩

/-- The s-pin hypotheses of `muxn3_s_pin_of_static` other than S_S_SETUP,
for s wires of `d ≥ 1` ticks. -/
theorem s_data : ∀ k t, 20 * k + 28 ≤ t → t ≤ 20 * k + 47 → s0d t = b0 (run.sv k) ∧ s1d t = b1 (run.sv k) :=
  fun k t h1 h2 => by
    have e : (t - 28) / 20 = k := by omega
    show b0 (svW ((t - 28) / 20)) = b0 (svW k) ∧ b1 (svW ((t - 28) / 20)) = b1 (svW k)
    rw [e]; exact ⟨rfl, rfl⟩
theorem s_lead : ∀ k, 20 * k + 28 + 0 ≤ run.γ (2 * k) := fun k => by
  show 20 * k + 28 + 0 ≤ 20 * (2 * k / 2) + 28 + 10 * (2 * k % 2); omega
theorem s_hold : ∀ k, uW.fst (run.ζ (2 * k + 1)) ≤ 20 * k + 47 := fun k => by
  show uW.fst (20 * ((2 * k + 1) / 2) + 36 + 10 * ((2 * k + 1) % 2)) ≤ 20 * k + 47
  rw [fuW _ (by omega)]; omega

/-- **Boundary run (`S_S_SETUP` with equality)**: `muxn3_ok_static` applies;
in particular join 0 is low throughout control token 1. -/
theorem bnd_ok :
    (∀ i, i < 3 → Tok (run.Lj i).hi (jD 1 i) run.E (run.g i)) ∧
    (∀ i, i < 3 → Tok (run.Ta i) (ak 1 i) (run.XA i) (run.g i)) := by
  have hpin := muxn3_s_pin_of_static (P := run) (s0p := s0p 1) (s1p := s1p 1)
    (Ws0 := fun _ => uW) (Ws1 := fun _ => uW) (sS := fun k => 20 * k + 28)
    (sE := fun k => 20 * k + 47) (Lsd := 0) enum (fun k => Nat.mod_lt _ (by omega)) causal static
    (Nat.le_refl 1) (fun _ _ _ _ => rfl) (fun _ _ _ _ => rfl) s_data s_lead s_hold
    (fun _ _ => ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩)
    (fun _ _ => ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩)
  have V : MN3Env run rstW ctl za x (s0p 1) (s1p 1) 4 :=
    ⟨rstW_hi, rstW_lo, H_X, Mn3Wit.env.H_CTL, Mn3Wit.env.H_ZA, fun k => Nat.mod_lt _ (by omega),
      enum, hpin⟩
  have h := muxn3_ok_static (gates 1) V causal static
    (fun _ _ => ⟨Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl,
      Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl, Nat.le_of_ble_eq_true rfl⟩)
    (fun i _ => ⟨by rw [Xp_eq]; unfold ξC; omega, by rw [D_eq]; omega,
      by show uW.fst (run.E 0) ≥ 4; rw [E_eq, fuW _ (by omega)]; omega,
      by rw [ZA_eq]; omega⟩)
    (fun i h1 h2 => by have : (1 : Nat) ≤ i := h1; have : i < 1 := h2; omega)
    (Nat.le_refl 1)
  exact ⟨h.1, fun i hi => (h.2.2 i hi).1⟩

/-- **The violation is exactly one tick of S_S_SETUP** (s wire 2 ticks): it
fails, while S_S_HOLD and all other hypotheses (`gates 2`, `H_X`, `causal`,
`static`, `s_data`, `s_lead`, `s_hold`) are the same proofs as `bnd_ok`'s. -/
theorem cex_setup_violated :
    ¬ ((Ret.shift 2).hi ≤ 0 + (run.Wc 0).lo) ∧
    (run.Wc 0).hi ≤ (1 + 1 + 1 + 1) + (1 + run.Lo.lo + 1 + 1) + uW.lo + (Ret.shift 2).lo := by
  decide

set_option maxRecDepth 100000 in
/-- **The conclusion fails** in the violating run: join 0 is high at 52,
inside control token 1's slot `[E 2, E 3) = [52, 62)` (token 1 selects input
1, `g 0 1 = false`), and in0_ack is high at 59 (in token 1). (The traces
show more: the one-tick runt is shorter than join 0's two-tick loop, and
join 0 and in0_ack OSCILLATE with period 2 for the rest of token 1.) In the boundary
run both are low at those instants. -/
theorem cex_values :
    run.E 2 = 52 ∧ run.E 3 = 62 ∧ run.g 0 1 = false ∧
    jD 2 0 52 = true ∧ ak 2 0 59 = true ∧ jD 1 0 52 = false ∧ ak 1 0 59 = false := by
  refine ⟨by rw [E_eq], by rw [E_eq], rfl, ?_⟩
  decide

/-- Hence `muxn3_ok`'s first conclusion is FALSE for the violating run. -/
theorem cex_fails : ¬ Tok (run.Lj 0).hi (jD 2 0) run.E (run.g 0) := by
  intro h
  obtain ⟨e2, e3, g01, j53, -⟩ := cex_values
  have := h.hi 1 52 (by show 1 ≤ 52; omega) (by rw [show 2 * 1 = 2 by rfl, e2]; omega)
    (by rw [show 2 * 1 + 1 = 3 by rfl, e3]; omega)
  rw [g01, j53] at this; exact absurd this (by decide)

end Mn3Cex

end Formal.Cells.MuxN3Timed
