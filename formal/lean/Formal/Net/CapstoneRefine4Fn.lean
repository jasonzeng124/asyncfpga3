import Formal.Net.CapstoneRefine4
import Formal.Gen.Cells

/-!
# Probe C-8x4 (2b): H_FN as a decidable check against the generated library cells

`Row`'s H_FN says: the zero-delay data value of the obligation netlist (`zdBus`) is the Ops cell
function `fnOf` of the launch values. It mixes two claims:

1. **H_ZD_BITS** (netlist correspondence, stays a hypothesis): bit `j` of the obligation's
   zero-delay data is the bdc LIBRARY cell's output bit `j`, evaluated with the LUT tables of
   `Formal.Gen.Cells` (yosys output of `cells/rtl/*.v`) on the launch bits: `genBit`. For a fork
   branch it is a wire; for a data steer (`fd = var 0`) a wire that drops the condition bit;
   for a link the `bd_latch` slice with the enable high (`latBit`); for a mux the `bd_datamux`
   slice (`muxBit`). Pairs of bits share one LUT6_2 (O5/O6) and an odd last bit uses its own LUT,
   as in the generated W=3 instances.
2. **The LUT function is the Ops function** (decidable, checked): `dmCheck` / `latCheck` read the
   INITs and pin maps of `bd_datamux_W3` and `bd_latch_W3` from `Formal.Gen.Cells` and check
   them exhaustively (`decide +kernel`); `fnOK k` is the per-operator check (by datapath class
   `dpOf`), **`fnOK_census`** runs it, by kernel `decide`, on the producer of each of gcd_hw's 221
   sampled channels: it passes for 176; the other 45 (38 `bjoin` = compare + data, 4 compute
   `join`, the two branches of the one data steer whose projection is `extui`, and out0 = the
   3-input mux) have no generated library netlist here (bdc's synthesized arithmetic, `extui`,
   `bdc_muxn3`), so H_FN stays a hypothesis there (`openIds`).

* `hfn_of_bits`: `fnOK k` + H_ZD_BITS + H_WIDTH (the value fits the bus) ⇒ H_FN.
* `RowG` (= `Row` with H_FN replaced by H_ZD_BITS + H_WIDTH), `row_of_rowG`.
* **`gcd_hw_circuit_safe_phys5_gen`**: phys5 with `RowG` on the 176 checked sampled channels,
  `Row` (H_FN assumed) on the 45 open ones, the field on the 244 ghosts.
-/

namespace Formal.Net.OpsBusy3
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.OpsBusy
open Formal.Timing Formal.Net.CapstoneRefine

/-! ## Bits -/

/-- Bit `j` of `v`. -/
def bitN (v j : Nat) : Bool := v / 2 ^ j % 2 == 1

theorem bv_bitN : ∀ W v, bv W (fun j => bitN v j) = v % 2 ^ W
  | 0, v => by simp [bv, Nat.mod_one]
  | W + 1, v => by
    simp only [bv]
    rw [bv_bitN W v, Nat.mod_pow_succ]
    have h := Nat.mod_two_eq_zero_or_one (v / 2 ^ W)
    rcases h with h | h <;> simp [bitN, h]

theorem bitN_div2 (v j : Nat) : bitN (v / 2) j = bitN v (j + 1) := by
  simp only [bitN, Nat.div_div_eq_div_mul, Nat.pow_succ, Nat.mul_comm]

/-! ## The generated library cells -/

/-- Output `p` of the generated cell `name` of `nl` on the pin values `ins` (binary reading). -/
def genOut (nl : Formal.Gen.Netlist) (name : String) (p : Formal.Gen.Pin) (ins : List Bool) :
    Option Bool :=
  (nl.cell? name).bind (fun c => c.out Formal.Gen.boolSem p ins)

abbrev dm : Formal.Gen.Netlist := Formal.Gen.Cells.bd_datamux_W3
abbrev lt : Formal.Gen.Netlist := Formal.Gen.Cells.bd_latch_W3

/-- `bd_datamux`, bit `j` of a `W`-bit instance: bits `2i, 2i+1` share a LUT6_2 (O5/O6, pins
`[s, a_lo, b_lo, a_hi, b_hi, 1]`), an odd last bit has a LUT3 (`[s, a, b]`). -/
def muxBit (W j : Nat) (s : Bool) (a b : Nat → Bool) : Option Bool :=
  if j % 2 = 0 then
    if j + 1 < W then genOut dm "pair[0].u" .O5 [s, a j, b j, a (j + 1), b (j + 1), true]
    else genOut dm "odd.u" .O [s, a j, b j]
  else genOut dm "pair[0].u" .O6 [s, a (j - 1), b (j - 1), a j, b j, true]

/-- `bd_latch`, bit `j`, enable high, settled (`q = d`): pins `[d_lo, en, q_lo, d_hi, q_hi, 1]`
(LUT6_2) and `[d, en, q, 0, 0, 0]` (LUT6). -/
def latBit (W j : Nat) (d : Nat → Bool) : Option Bool :=
  if j % 2 = 0 then
    if j + 1 < W then genOut lt "pair[0].u" .O5 [d j, true, d j, d (j + 1), d (j + 1), true]
    else genOut lt "odd.u" .O [d j, true, d j, false, false, false]
  else genOut lt "pair[0].u" .O6 [d (j - 1), true, d (j - 1), d j, d j, true]

/-- **The datamux check**: the generated cells have the pin maps `muxBit` assumes, and their
tables compute `s ? b : a`. -/
def dmCheck : Bool :=
  dm.lutIs "pair[0].u" .lut6_2 0xFFAA5500E4E4E4E4 ["s", "a[0]", "b[0]", "a[1]", "b[1]", "1"]
      ["z[0]", "z[1]"] &&
  dm.lutIs "odd.u" (.lut 3) 0xE4 ["s", "a[2]", "b[2]"] ["z[2]"] &&
  decide (∀ s a0 b0 a1 b1 : Bool,
    genOut dm "pair[0].u" .O5 [s, a0, b0, a1, b1, true] = some (if s then b0 else a0) ∧
    genOut dm "pair[0].u" .O6 [s, a0, b0, a1, b1, true] = some (if s then b1 else a1) ∧
    genOut dm "odd.u" .O [s, a0, b0] = some (if s then b0 else a0))

/-- **The latch check**: pin maps as `latBit` assumes; enable high ⇒ transparent (for every
stored bit), enable low ⇒ opaque. -/
def latCheck : Bool :=
  lt.lutIs "pair[0].u" .lut6_2 0xFF33CC00B8B8B8B8 ["d[0]", "en", "q[0]", "d[1]", "q[1]", "1"]
      ["q[0]", "q[1]"] &&
  lt.lutIs "odd.u" (.lut 6) 0xB8B8B8B8B8B8B8B8 ["d[2]", "en", "q[2]", "0", "0", "0"] ["q[2]"] &&
  decide (∀ d0 q0 d1 q1 en : Bool,
    genOut lt "pair[0].u" .O5 [d0, en, q0, d1, q1, true] = some (if en then d0 else q0) ∧
    genOut lt "pair[0].u" .O6 [d0, en, q0, d1, q1, true] = some (if en then d1 else q1) ∧
    genOut lt "odd.u" .O [d0, en, q0, false, false, false] = some (if en then d0 else q0))

set_option maxRecDepth 100000 in
theorem dmCheck_ok : dmCheck = true := by decide +kernel

set_option maxRecDepth 100000 in
theorem latCheck_ok : latCheck = true := by decide +kernel

theorem muxBit_ok (h : dmCheck = true) {W j : Nat} (_hj : j < W) (s : Bool) (a b : Nat → Bool) :
    muxBit W j s a b = some (if s then b j else a j) := by
  simp only [dmCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have H := h.2
  unfold muxBit
  by_cases hp : j % 2 = 0
  · rw [if_pos hp]
    by_cases hw : j + 1 < W
    · rw [if_pos hw]; exact (H s (a j) (b j) (a (j + 1)) (b (j + 1))).1
    · rw [if_neg hw]; exact (H s (a j) (b j) false false).2.2
  · rw [if_neg hp]
    have := (H s (a (j - 1)) (b (j - 1)) (a j) (b j)).2.1
    exact this

theorem latBit_ok (h : latCheck = true) {W j : Nat} (_hj : j < W) (d : Nat → Bool) :
    latBit W j d = some (d j) := by
  simp only [latCheck, Bool.and_eq_true, decide_eq_true_eq] at h
  have H := h.2
  unfold latBit
  by_cases hp : j % 2 = 0
  · rw [if_pos hp]
    by_cases hw : j + 1 < W
    · rw [if_pos hw]; simpa using (H (d j) (d j) (d (j + 1)) (d (j + 1)) true).1
    · rw [if_neg hw]; simpa using (H (d j) (d j) false false true).2.2
  · rw [if_neg hp]
    simpa using (H (d (j - 1)) (d (j - 1)) (d j) (d j) true).2.1

/-! ## Per operator -/

variable {n : Nat}

/-- Datapath class of an operator's output bus. -/
inductive DP
  | wire | shift | latch | dmux | open_
  deriving DecidableEq, Repr

def dpOf : K n → DP
  | .forkG .. => .wire
  | .forkH .. => .wire
  | .steerD _ _ _ (.var 0) _ => .shift
  | .link .. => .latch
  | .mux .. => .dmux
  | _ => .open_

/-- **The per-operator H_FN check** (decidable): the generated library cell of the operator's
datapath class computes its Ops function. -/
def fnOK (k : K n) : Bool :=
  match dpOf k with
  | .wire | .shift => true
  | .latch => latCheck
  | .dmux => dmCheck
  | .open_ => false

/-- Bit `j` of the library cell's output on the launch values `v`. -/
def genBit (k : K n) (W j : Nat) (v : Fin n → Nat) : Option Bool :=
  match k with
  | .forkG i _ => some (bitN (v i) j)
  | .forkH i _ _ _ _ _ => some (bitN (v i) j)
  | .steerD jj _ _ (.var 0) _ => some (bitN (v jj) (j + 1))
  | .link i _ => latBit W j (fun j => bitN (v i) j)
  | .mux c x y _ _ => muxBit W j (sel2 (v c)) (fun j => bitN (v x) j) (fun j => bitN (v y) j)
  | _ => none

theorem genBit_ok (sv : Nat → Nat) {k : K n} (hk : fnOK k = true) {W j : Nat} (hj : j < W)
    (v : Fin n → Nat) (b : Bool) : genBit k W j v = some (bitN (fnOf sv k v b) j) := by
  cases k with
  | forkG i os => rfl
  | forkH i os l h d hs => rfl
  | steerD jj tt f fd sw =>
    match fd, hk with
    | .var 0, _ =>
      show some (bitN (v jj) (j + 1)) = some (bitN ((GcdHw.E.var 0).eval [v jj / 2]) j)
      rw [show (GcdHw.E.var 0).eval [v jj / 2] = v jj / 2 from rfl, bitN_div2]
    | .var (_ + 1), hk => simp [fnOK, dpOf] at hk
    | .lit _, hk => simp [fnOK, dpOf] at hk
    | .un _ _ _, hk => simp [fnOK, dpOf] at hk
    | .bin _ _ _ _, hk => simp [fnOK, dpOf] at hk
    | .sel _ _ _, hk => simp [fnOK, dpOf] at hk
  | link i o =>
    exact latBit_ok hk hj _
  | mux c x y z mw =>
    show muxBit W j _ _ _ = some (bitN (if sel2 (v c) then v y else v x) j)
    rw [muxBit_ok hk hj]
    cases sel2 (v c) <;> rfl
  | join => simp [fnOK, dpOf] at hk
  | bjoin => simp [fnOK, dpOf] at hk
  | steerC => simp [fnOK, dpOf] at hk
  | muxn => simp [fnOK, dpOf] at hk
  | amerge => simp [fnOK, dpOf] at hk
  | src => simp [fnOK, dpOf] at hk
  | sink => simp [fnOK, dpOf] at hk

/-- **H_FN from the bit-level correspondence and the checked library cell.** -/
theorem hfn_of_bits (sv : Nat → Nat) {k : K n} (hk : fnOK k = true) {net : Netlist}
    {sig : Nat → Nat → Trace} {data : List Nat} (runs : ∀ m, Run net (sig m))
    (vin : Nat → Fin n → Nat) (vb : Nat → Bool)
    (H_ZD_BITS : ∀ m j, j < data.length →
      some (zdEval net (runs m).g (sig m 0 1) (data.getD j 0)) = genBit k data.length j (vin m))
    (H_WIDTH : ∀ m, fnOf sv k (vin m) (vb m) < 2 ^ data.length) :
    ∀ m, zdBus runs data m = fnOf sv k (vin m) (vb m) := by
  intro m
  unfold zdBus
  rw [bv_congr data.length (f' := fun j => bitN (fnOf sv k (vin m) (vb m)) j) (fun j hj =>
    Option.some.inj ((H_ZD_BITS m j hj).trans (genBit_ok sv hk hj (vin m) (vb m)))),
    bv_bitN, Nat.mod_eq_of_lt (H_WIDTH m)]

/-- `Row` with H_FN replaced by the bit-level correspondence H_ZD_BITS and H_WIDTH. -/
inductive RowG (ch : Fin n → Chan) (sv : Nat → Nat) (k : K n) (w : Nat → Trace) (c : Fin n) :
    Prop
  | mk (net : Netlist) (hwf : net.WF) (sig : Nat → Nat → Trace) (data : List Nat)
      (R : Nat → Nat → Prop) (runs : ∀ m, Run net (sig m)) (X : TxWin (ch c) sig data R)
      (hsep : ∀ m v, R m v → ∀ d ∈ data, ∀ s, changes (sig m d) s → s ≤ v)
      (vin : Nat → Fin n → Nat) (vb : Nat → Bool)
      (H_ZD_BITS : ∀ m j, j < data.length →
        some (zdEval net (runs m).g (sig m 0 1) (data.getD j 0)) = genBit k data.length j (vin m))
      (H_WIDTH : ∀ m, fnOf sv k (vin m) (vb m) < 2 ^ data.length)
      (H_LAUNCH : ∀ m r, OffAt (ch c) m r →
        (∀ i ∈ k.insC, vin m i = (ch i).dat (r + 1)) ∧ vb m = wonOf ch k w (r + 1)) :
      RowG ch sv k w c

theorem row_of_rowG {ch : Fin n → Chan} {sv : Nat → Nat} {k : K n} {w : Nat → Trace} {c : Fin n}
    (hk : fnOK k = true) (h : RowG ch sv k w c) : Row ch sv k w c := by
  obtain ⟨net, hwf, sig, data, R, runs, X, hsep, vin, vb, HZ, HW, HL⟩ := h
  exact Row.mk net hwf sig data R runs X hsep vin vb (hfn_of_bits sv hk runs vin vb HZ HW) HL

end Formal.Net.OpsBusy3

namespace Formal.Net.CapNet.Gcd
open Formal.Net Formal.Net.Handshake Formal.Net.Ops Formal.Net.CapNet Formal.Net.OpsBusy
open Formal.Net.CapstoneRefine Formal.Net.OpsBusy2 Formal.Net.OpsBusy3

/-- The 45 sampled channels whose producer has no generated library datapath (H_FN open). -/
def openIds : List Nat := (sampIds.filter (fun c => !fnOK (ops.getD (prodT.getD c 0).val (K.sink 0))))

set_option maxRecDepth 100000 in
/-- **The per-operator H_FN check, run on gcd_hw** (kernel `decide`): 176 of the 221 sampled
channels have a producer whose library datapath passes `fnOK`; the 45 others are listed (38
`bjoin` outputs 418..455, 4 compute `join` outputs 51, 116, 344, 410, the `extui` data steer's two
branches 71, 74, and out0 = 416, the 3-input mux). -/
theorem fnOK_census : openIds = [51, 71, 74, 116, 344, 410, 416, 418, 419, 420, 421, 422, 423,
    424, 425, 426, 427, 428, 429, 430, 431, 432, 433, 434, 435, 436, 437, 438, 439, 440, 441, 442,
    443, 444, 445, 446, 447, 448, 449, 450, 451, 452, 453, 454, 455] ∧ openIds.length = 45 := by
  decide +kernel

set_option maxRecDepth 100000 in
/-- The same check over all 367 operators: 268 pass (44 fork, 28 data steer with `fd = var 0`,
175 link, 21 mux); 99 have no generated datapath here (38 `bjoin`, 20 `join`, 9 arbiter stages,
9 `steerC` (W = 0), 1 `extui` steer, the 3-input mux, 3 sources, 18 sinks). -/
theorem fnOK_ops : ((List.range NO).filter (fun o => fnOK (ops.getD o (K.sink 0)))).length = 268 := by
  decide +kernel

/-- Rows per class: checked library datapath ⇒ `RowG` (H_FN derived), else `Row`. -/
def CellPgen (ch : Fin NC → Chan) (sv : Nat → Nat) (o : Fin NO) : Prop :=
  ∃ w, HS ch sv (opAt o) w ∧ ∀ c ∈ (opAt o).outsC,
    (isSampled c = true → fnOK (opAt o) = true → RowG ch sv (opAt o) w c) ∧
    (isSampled c = true → fnOK (opAt o) = false → Row ch sv (opAt o) w c) ∧
    (isSampled c = false → FieldOf ch sv (opAt o) w c)

theorem cls_of_gen {ch : Fin NC → Chan} {sv : Nat → Nat} {o : Fin NO} (h : CellPgen ch sv o) :
    CellPcls ch sv o := by
  obtain ⟨w, hs, hd⟩ := h
  refine ⟨w, hs, fun c hc => ⟨fun e => ?_, (hd c hc).2.2⟩⟩
  cases hk : fnOK (opAt o)
  · exact (hd c hc).2.1 e hk
  · exact row_of_rowG hk ((hd c hc).1 e hk)

/-- **phys5, H_FN discharged where a generated library datapath exists**: H_ZD_BITS + H_WIDTH on
the 176 checked sampled channels, H_FN on the 45 open ones (`openIds`), fields on the ghosts. -/
theorem gcd_hw_circuit_safe_phys5_gen (a b : Nat) (ha : a < 2 ^ 31) (hb : b < 2 ^ 31)
    (ch : Fin NC → Chan)
    (H_CELLS_P : ∀ o : Fin NO, CellPgen ch (srcV a b) o)
    (H_START_ONCE : ∀ t, Handshake.cnt (riseB (ch start).req) t ≤ 1)
    (H_TCHECK_ROOT : ∀ c, isRoot3 c = true → BCert (ch c)) :
    (∀ k e, TokAt (ch out0) k e → (ch out0).dat e = Nat.gcd a b) ∧
    (∀ t, closedVals (ch out0) t =
      List.replicate (Handshake.cnt (fallB (ch out0).ack) t) (Nat.gcd a b)) :=
  gcd_hw_circuit_safe_phys5_cls a b ha hb ch (fun o => cls_of_gen (H_CELLS_P o)) H_START_ONCE
    H_TCHECK_ROOT

end Formal.Net.CapNet.Gcd
