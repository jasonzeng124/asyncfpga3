import Formal.Core.LutList
import Formal.Cells.MuxTree
open Formal.Core.LutList

/-!
# Shard B, probe Lib2: `bd_end.v`, `bd_mem.v`, `bd_mlink.v`, and the parts of
# `bd_link.v` / `bd_latch.v` (`bd_link_dctl`, `bd_delay_gated`) not yet covered

Every LUT is evaluated from its real INIT and pin map (verbatim from
`cells/rtl/`) with Prelim's `lutB` / `lutK`. Nothing in Prelim is changed;
every helper is local to namespace `Formal.Cells.LibEndMemMlink`.

LUT instances covered (INIT, pins `[I0, I1, ...]`):

| cell | instance | INIT | pins |
|---|---|---|---|
| `bd_src` (`bd_end.v`) | `u` | `2'h1` | `[ack]` -> `req` |
| `bd_mem` (USE_BUFG=0) | `gplain.ubuf` | `2'h2` | `[strobe]` -> `ram_clk` |
| `bd_mlink_ctl` | `ux` | `8'hF9` | `[done, ack, rst]` -> `en0` |
| `bd_mlink_ctl` (NOPEN>1) | `uz` | `16'hAA82` | `[s, done, ack, rst]` -> `en` |
| `bd_mlink_ctl` | `uq` = `bd_latch #(.W(1))` | `64'hB8B8...` | `[req_in, en, done, 0,0,0]` -> `done` |
| `bd_flink_ctl` | `uck` | `8'h06` | `[done, ack, rst]` -> `ck` |
| `bd_flink_ctl` | `uq` | `8'hE2` | `[req_in, ck, done]` -> `done` |
| `bd_link_dctl` | `ub` `ua` `uld` `ult` | see Section 1 | see Section 1 |
| `bd_delay_gated` | `g0`, `g[i>=1]` | `2'h2`, `4'h8` | `[s_i]`, `[s_i, gate]` |

`bd_snk` and `bd_mem`'s RAMB18E1 have no LUT. `bd_mem`'s `bd_delay` lines
(symmetric, LUT1 `2'h2`) are `Bundling.lean`'s `sym_chain`; here they enter
only through the named timing hypotheses of Section 7.

Already covered elsewhere and NOT repeated: `bd_link_dctl`'s binary equations
with `rst = 0, s = 1` (`LinkHandshake.dctl_eqs`) and its interleaving check
(`dctl_ok0/1`); `bd_latch` (`Latch.lean`); the 4'h8 side stage as a Kleene
fast stage (`Bundling.fastfall_line`). New here for `bd_link_dctl`: `rst`,
the `s` pin (`LDN > 0`), the tied `I5` (and `I3..I5` of `ult`), Kleene
single-X per pin, and the X-on-feedback structure of `ub`, `ua`, `uld`.
-/

namespace Formal.Cells.LibEndMemMlink

open Formal.Cells

/-- Local: decide `∀ k : K3, P k` by three cases. -/
instance k3DecForall {P : K3 → Prop} [DecidablePred P] : Decidable (∀ k, P k) :=
  if h : P .f ∧ P .t ∧ P .x then
    isTrue (fun k => by cases k <;> simp_all)
  else
    isFalse (fun H => h ⟨H _, H _, H _⟩)

/-! ## 0. Single-X glitch freedom holds for EVERY INIT (under H_KLEENE_LUT)

`CElemFn.SingleX` proves, per INIT by enumeration, that X on one pin gives the
join of the two endpoint values. Under Prelim's closure semantics this is true
of every INIT and every input width; we prove it once here. Consequence: a
per-cell single-X check has no cell-specific content: it can never fail.
All of the content sits in H_KLEENE_LUT itself (per-mux reading: MuxTree.lean,
`muxTree_eq_lutK`). The per-cell `decide` versions are still given below, as
the task asks, and as a cross-check of this theorem. -/

theorem completions_ofBool (v : List Bool) : completions (v.map K3.ofBool) = [v] := by
  induction v with
  | nil => rfl
  | cons b vs ih => cases b <;> simp [completions, ih, K3.ofBool, K3.admits]

theorem completions_setx (v : List Bool) (i : Nat) (h : i < v.length) :
    completions ((v.map K3.ofBool).set i .x) = [v.set i false, v.set i true] := by
  induction v generalizing i with
  | nil => simp at h
  | cons b vs ih =>
    cases i with
    | zero => simp [completions, completions_ofBool, K3.admits]
    | succ k =>
      have hk : k < vs.length := by simp at h; omega
      cases b <;> simp [completions, ih k hk, K3.ofBool, K3.admits]

/-- **Single-X theorem, any INIT, any width.** X on pin `i` of a binary input
vector gives the join of the LUT's values with that pin at 0 and at 1. So the
output during a single-pin change is definite (= the common value) whenever the
two endpoints agree: no static hazard on a single-input change, for every LUT,
under H_KLEENE_LUT. -/
theorem singleX_any (init : Nat) (v : List Bool) (i : Nat) (h : i < v.length) :
    lutK init ((v.map K3.ofBool).set i .x)
      = K3.join (.ofBool (lutB init (v.set i false))) (.ofBool (lutB init (v.set i true))) := by
  rw [MuxTree.lutK_eq_closure]
  rw [completions_setx v i h]
  simp only [List.map_cons, List.map_nil]
  cases lutB init (v.set i false) <;> cases lutB init (v.set i true) <;> rfl

/-- Kleene agrees with binary on definite inputs (any INIT). -/
theorem lutK_ofBool (init : Nat) (v : List Bool) :
    lutK init (v.map K3.ofBool) = .ofBool (lutB init v) := by
  rw [MuxTree.lutK_eq_closure, completions_ofBool]
  simp only [List.map_cons, List.map_nil]
  cases lutB init v <;> rfl

/-- The CElemFn-style per-INIT statement (6 pins, endpoints `v` and `v` with
pin `i` flipped), checked by enumeration below for each INIT. -/
def allVecs : Nat → List (List Bool)
  | 0 => [[]]
  | n + 1 => (allVecs n).map (false :: ·) ++ (allVecs n).map (true :: ·)

def SingleX (init : Nat) : Prop :=
  ∀ v ∈ allVecs 6, ∀ i, i < 6 →
    lutK init ((v.map K3.ofBool).set i .x)
      = K3.join (.ofBool (lutB init v)) (.ofBool (lutB init (v.set i (!v.getD i false))))

/-! ## 1. INITs, verbatim from `cells/rtl/` -/

/-- `bd_src.u`: `LUT1 #(.INIT(2'h1))`, `I0 = ack`, `O = req`. -/
def INIT_INV : Nat := 0x1
/-- `bd_mem.gplain.ubuf`, and every symmetric `bd_delay` hop, and
`bd_delay_gated`'s head `g0`: `LUT1 #(.INIT(2'h2))`. -/
def INIT_BUF : Nat := 0x2
/-- `bd_mlink_ctl.ux`: `LUT3 #(.INIT(8'hF9))`, `I0 done, I1 ack, I2 rst`. -/
def INIT_UX : Nat := 0xF9
/-- `bd_mlink_ctl.slow_reopen.uz`: `LUT4 #(.INIT(16'hAA82))`, `I0 s, I1 done, I2 ack, I3 rst`. -/
def INIT_UZ : Nat := 0xAA82
/-- `bd_latch` odd bit (`bd_mlink_ctl.uq` is `bd_latch #(.W(1))`): `I0 d, I1 en, I2 q`. -/
def INIT_LAT : Nat := 0xB8B8B8B8B8B8B8B8
/-- `bd_flink_ctl.uck`: `LUT3 #(.INIT(8'h06))`, `I0 done, I1 ack, I2 rst`. -/
def INIT_UCK : Nat := 0x06
/-- `bd_flink_ctl.uq`: `LUT3 #(.INIT(8'hE2))`, `I0 req_in, I1 ck, I2 done` (its own output). -/
def INIT_FQ : Nat := 0xE2
/-- `bd_link_dctl.ub`: `I0 req_in, I1 ack_out, I2 ld, I3 b, I4 rst, I5 0`. -/
def INIT_DB  : Nat := 0x0000F3200000F320
/-- `bd_link_dctl.ua`: `I0 req_in, I1 b, I2 ld, I3 a, I4 rst, I5 0`. -/
def INIT_DA  : Nat := 0x0000FA800000FA80
/-- `bd_link_dctl.uld`: `I0 lt, I1 s, I2 a, I3 ld, I4 rst, I5 0`. -/
def INIT_DLD : Nat := 0x00000F0800000F08
/-- `bd_link_dctl.ult`: `I0 b, I1 a, I2 gate, I3..I5 0`. -/
def INIT_DLT : Nat := 0x0101010101010101
/-- `bd_delay_gated.g[i>=1]` (and `bd_delay` FASTFALL side stage): `LUT2 #(.INIT(4'h8))`,
`I0 s[i]` (chain), `I1 gate` (tap). -/
def INIT_AND : Nat := 0x8

/-! ### Physical 6-input form of the small LUTs

A LUT1..LUT4 occupies a 6-input LUT BEL. **H_REPLICATED_INIT**: the toolchain
either replicates the small INIT across the unused pins or ties them to a
constant. We prove the replicated 64-bit INIT computes the small function for
every value of the unused pins, binary and Kleene (even X on an unused pin
does not reach O). So either realisation gives the small function.
Test: read the INIT back from the bitstream (`fasm`) of a routed build. -/

def R_INV : Nat := 0x5555555555555555
def R_BUF : Nat := 0xAAAAAAAAAAAAAAAA
def R_UX  : Nat := 0xF9F9F9F9F9F9F9F9
def R_UZ  : Nat := 0xAA82AA82AA82AA82
def R_UCK : Nat := 0x0606060606060606
def R_FQ  : Nat := 0xE2E2E2E2E2E2E2E2
def R_AND : Nat := 0x8888888888888888

theorem rep_inv : ∀ a u1 u2 u3 u4 u5 : Bool,
    lutB R_INV [a, u1, u2, u3, u4, u5] = lutB INIT_INV [a] := by decide
theorem rep_buf : ∀ a u1 u2 u3 u4 u5 : Bool,
    lutB R_BUF [a, u1, u2, u3, u4, u5] = lutB INIT_BUF [a] := by decide
theorem rep_and : ∀ a b u2 u3 u4 u5 : Bool,
    lutB R_AND [a, b, u2, u3, u4, u5] = lutB INIT_AND [a, b] := by decide
theorem rep_ux : ∀ d a r u3 u4 u5 : Bool,
    lutB R_UX [d, a, r, u3, u4, u5] = lutB INIT_UX [d, a, r] := by decide
theorem rep_uck : ∀ d a r u3 u4 u5 : Bool,
    lutB R_UCK [d, a, r, u3, u4, u5] = lutB INIT_UCK [d, a, r] := by decide
theorem rep_fq : ∀ q c d u3 u4 u5 : Bool,
    lutB R_FQ [q, c, d, u3, u4, u5] = lutB INIT_FQ [q, c, d] := by decide
theorem rep_uz : ∀ s d a r u4 u5 : Bool,
    lutB R_UZ [s, d, a, r, u4, u5] = lutB INIT_UZ [s, d, a, r] := by decide

/-- Kleene: X (or anything) on an unused pin never reaches O. -/
theorem rep_ux_K : ∀ d a r u3 u4 u5 : K3,
    lutK R_UX [d, a, r, u3, u4, u5] = lutK INIT_UX [d, a, r] := by decide
theorem rep_uck_K : ∀ d a r u3 u4 u5 : K3,
    lutK R_UCK [d, a, r, u3, u4, u5] = lutK INIT_UCK [d, a, r] := by decide
theorem rep_fq_K : ∀ q c d u3 u4 u5 : K3,
    lutK R_FQ [q, c, d, u3, u4, u5] = lutK INIT_FQ [q, c, d] := by decide
theorem rep_uz_K : ∀ s d a r u4 u5 : K3,
    lutK R_UZ [s, d, a, r, u4, u5] = lutK INIT_UZ [s, d, a, r] := by decide
theorem rep_and_K : ∀ a b u2 u3 u4 u5 : K3,
    lutK R_AND [a, b, u2, u3, u4, u5] = lutK INIT_AND [a, b] := by decide
theorem rep_inv_K : ∀ a u1 u2 u3 u4 u5 : K3,
    lutK R_INV [a, u1, u2, u3, u4, u5] = lutK INIT_INV [a] := by decide
theorem rep_buf_K : ∀ a u1 u2 u3 u4 u5 : K3,
    lutK R_BUF [a, u1, u2, u3, u4, u5] = lutK INIT_BUF [a] := by decide

/-! ## 2. Binary function = header equation (every LUT, every input) -/

/-- `bd_src`: `req = ~ack`. -/
theorem inv_eq : ∀ a : Bool, lutB INIT_INV [a] = !a := by decide
/-- `bd_mem` clock buffer (and every symmetric delay hop): `ram_clk = strobe`. -/
theorem buf_eq : ∀ a : Bool, lutB INIT_BUF [a] = a := by decide
/-- `bd_mlink_ctl.ux`: "rst -> 1, else ~(done ^ ack)". -/
theorem ux_eq : ∀ d a r : Bool, lutB INIT_UX [d, a, r] = (r || !(d ^^ a)) := by decide
/-- `bd_mlink_ctl.uz`: "s & (rst | ~(done ^ ack))". -/
theorem uz_eq : ∀ s d a r : Bool,
    lutB INIT_UZ [s, d, a, r] = (s && (r || !(d ^^ a))) := by decide
/-- `bd_latch` odd bit: `en ? d : q` (also `Latch.odd_bin`; restated for the loop below). -/
theorem lat_eq : ∀ d e q : Bool,
    lutB INIT_LAT [d, e, q, false, false, false] = (if e then d else q) := by decide
/-- `bd_flink_ctl.uck`: "~rst & (done ^ ack)". -/
theorem uck_eq : ∀ d a r : Bool, lutB INIT_UCK [d, a, r] = (!r && (d ^^ a)) := by decide
/-- `bd_flink_ctl.uq`: "ck ? done : req_in". -/
theorem fq_eq : ∀ q c d : Bool, lutB INIT_FQ [q, c, d] = (if c then d else q) := by decide
/-- `bd_delay_gated` side stage: `s[i+1] = s[i] & gate`. -/
theorem and_eq : ∀ s g : Bool, lutB INIT_AND [s, g] = (s && g) := by decide

/-- `cells/verify/inits.py` agrees: `MT_EN = r | ~(d^a)`, `MT_EN_REOPEN =
s & (r | ~(d^a))`, `MT_CK = ~r & (d^a)`, `MT_REQ_LATCH = ck ? done : req`
(the Python lambdas restated; the INITs are the RTL's). -/
theorem mt_en_reopen_from_en0 : ∀ s d a r : Bool,
    lutB INIT_UZ [s, d, a, r] = (s && lutB INIT_UX [d, a, r]) := by decide

/-- `uck` is exactly the complement of `ux` outside reset: the flink clock is
the mlink "closed" condition. In reset they differ (`ux = 1`, `uck = 0`), which
is consistent: both mean "transparent". -/
theorem uck_not_ux : ∀ d a : Bool,
    lutB INIT_UCK [d, a, false] = !lutB INIT_UX [d, a, false] := by decide

/-! ### `bd_link_dctl`, full 6-pin equations (rst, `s` and `I5` included)

Header: `b` set `req.ld.~ack`, reset `ack.~ld`; `a` set `req.b.ld`, reset
`~req.~ld`; `ld` set `lt.s.~a`, reset `a`; `lt = ~b.~a.~gate`. All three state
bits are cleared by `rst` (I4). -/

theorem db_eq : ∀ req ack ld b rst i5 : Bool,
    lutB INIT_DB [req, ack, ld, b, rst, i5]
      = (!rst && ((req && ld && !ack) || (b && !(ack && !ld)))) := by decide
theorem da_eq : ∀ req b ld a rst i5 : Bool,
    lutB INIT_DA [req, b, ld, a, rst, i5]
      = (!rst && ((req && b && ld) || (a && !(!req && !ld)))) := by decide
theorem dld_eq : ∀ lt s a ld rst i5 : Bool,
    lutB INIT_DLD [lt, s, a, ld, rst, i5]
      = (!rst && ((lt && s && !a) || (ld && !a))) := by decide
theorem dlt_eq : ∀ b a g u3 u4 u5 : Bool,
    lutB INIT_DLT [b, a, g, u3, u4, u5] = (!b && !a && !g) := by decide

/-- Set and reset of each dctl state bit are never both asserted (so each is
a clean SR element, no "set and reset" ambiguity in the INIT). -/
theorem dctl_sr_disjoint : ∀ req ack ld b a lt s : Bool,
    !((req && ld && !ack) && (ack && !ld)) ∧
    !((req && b && ld) && (!req && !ld)) ∧
    !((lt && s && !a) && a) := by decide

/-- `I5` (tied `1'b0`) is a don't-care even at X; likewise `I3..I5` of `ult`. -/
theorem db_i5_K : ∀ p0 p1 p2 p3 p4 u : K3,
    lutK INIT_DB [p0, p1, p2, p3, p4, u] = lutK INIT_DB [p0, p1, p2, p3, p4, .f] := by decide
theorem da_i5_K : ∀ p0 p1 p2 p3 p4 u : K3,
    lutK INIT_DA [p0, p1, p2, p3, p4, u] = lutK INIT_DA [p0, p1, p2, p3, p4, .f] := by decide
theorem dld_i5_K : ∀ p0 p1 p2 p3 p4 u : K3,
    lutK INIT_DLD [p0, p1, p2, p3, p4, u] = lutK INIT_DLD [p0, p1, p2, p3, p4, .f] := by decide
theorem dlt_tied_K : ∀ b a g u3 u4 u5 : K3,
    lutK INIT_DLT [b, a, g, u3, u4, u5] = lutK INIT_DLT [b, a, g, .f, .f, .f] := by decide

/-! ## 3. Single-X per pin, per INIT

The CElemFn-form `SingleX` follows from `singleX_any` for EVERY INIT
(`singleX_all`), so each cell's statement is an instance, not an enumeration.
One enumeration (`ux_singleX_dec`) is kept as an independent cross-check. -/

theorem set_getD_self (v : List Bool) (i : Nat) (h : i < v.length) :
    v.set i (v.getD i false) = v := by
  induction v generalizing i with
  | nil => simp at h
  | cons b vs ih =>
    cases i with
    | zero => simp
    | succ k => simp at h; exact congrArg (b :: ·) (ih k (by omega))

theorem join_comm (a b : K3) : K3.join a b = K3.join b a := by
  cases a <;> cases b <;> rfl

theorem length_allVecs : ∀ n, ∀ v ∈ allVecs n, v.length = n
  | 0, v, h => by simp [allVecs] at h; simp [h]
  | n + 1, v, h => by
    simp only [allVecs, List.mem_append, List.mem_map] at h
    rcases h with ⟨w, hw, rfl⟩ | ⟨w, hw, rfl⟩ <;> simp [length_allVecs n w hw]

theorem singleX_all (init : Nat) : SingleX init := by
  intro v hv i hi
  have hl : i < v.length := by rw [length_allVecs 6 v hv]; exact hi
  rw [singleX_any init v i hl]
  cases hb : v.getD i false
  · have : v.set i false = v := by rw [← hb]; exact set_getD_self v i hl
    simp [this]
  · have : v.set i true = v := by rw [← hb]; exact set_getD_self v i hl
    simp [this, join_comm]

theorem inv_singleX : SingleX R_INV := singleX_all _
theorem buf_singleX : SingleX R_BUF := singleX_all _
theorem ux_singleX  : SingleX R_UX  := singleX_all _
theorem uz_singleX  : SingleX R_UZ  := singleX_all _
theorem lat_singleX : SingleX INIT_LAT := singleX_all _
theorem uck_singleX : SingleX R_UCK := singleX_all _
theorem fq_singleX  : SingleX R_FQ  := singleX_all _
theorem and_singleX : SingleX R_AND := singleX_all _
theorem db_singleX  : SingleX INIT_DB  := singleX_all _
theorem da_singleX  : SingleX INIT_DA  := singleX_all _
theorem dld_singleX : SingleX INIT_DLD := singleX_all _
theorem dlt_singleX : SingleX INIT_DLT := singleX_all _

/-- Independent enumeration, as in CElemFn (cross-check of `singleX_all`). -/
theorem uz_singleX_dec : SingleX R_UZ := by unfold SingleX; decide

end Formal.Cells.LibEndMemMlink

namespace Formal.Cells.LibEndMemMlink
open Formal.Cells

/-! ## 4. Kleene behaviour and the feedback structure of each loop

Named-pin Kleene forms (all 3^k inputs, by `decide`). -/

def invK (a : K3) : K3 := lutK INIT_INV [a]
def uxK (d a r : K3) : K3 := lutK INIT_UX [d, a, r]
def uzK (s d a r : K3) : K3 := lutK INIT_UZ [s, d, a, r]
def latK (d e q : K3) : K3 := lutK INIT_LAT [d, e, q, .f, .f, .f]
def uckK (d a r : K3) : K3 := lutK INIT_UCK [d, a, r]
def fqK (q c d : K3) : K3 := lutK INIT_FQ [q, c, d]

/-! ### `bd_src` closed on a mirror (`bd_snk`, or any consumer that answers
`ack = req`): the loop is the inverter alone. It has no binary fixed point
(it oscillates; the header's "the ring just turns", not storage), and its only
Kleene fixed point is `x`. -/
theorem src_no_fixed : ∀ q : Bool, lutB INIT_INV [q] ≠ q := by decide
theorem src_fixed_K : ∀ q : K3, invK q = q ↔ q = .x := by decide
theorem src_K : ∀ a : K3, invK a = K3.not a := by decide

/-! ### `bd_flink_ctl.uq`: a mux latch on its own output (pin I2)

Kleene: exactly `K3.mux ck req done` (transparent at ck = 0). -/
theorem fq_K : ∀ q c d : K3, fqK q c d = K3.mux c q d := by decide
/-- Binary fixed points: stable iff opaque (ck = 1) or Q already equals D. -/
theorem fq_fixed_iff : ∀ q c d : Bool, lutB INIT_FQ [q, c, d] = d ↔ (c = true ∨ q = d) := by decide
/-- X on the feedback pin is restored iff the latch is transparent and D is
definite; while opaque an X is held (Kleene cannot resolve it). -/
theorem fq_restore : ∀ q c : K3, fqK q c .x ≠ .x ↔ (c = .f ∧ q ≠ .x) := by decide
/-- The closing edge with D = Q is hazard-free (consensus term in the INIT). -/
theorem fq_close_clean : ∀ v : Bool, fqK (.ofBool v) .x (.ofBool v) = .ofBool v := by decide

/-! ### `bd_flink_ctl.uck` and `bd_mlink_ctl.ux` / `uz` -/
theorem uck_K_rst : ∀ d a : K3, uckK d a .t = .f := by decide
theorem ux_K_rst : ∀ d a : K3, uxK d a .t = .t := by decide
/-- XOR/XNOR are sensitive to every pin: X on done or ack with rst = 0 always
gives X. There is no definite value to protect, so no hazard question: the
enable/clock is X exactly while one of its inputs is in transit. -/
theorem ux_x_done : ∀ a : K3, uxK .x a .f = .x := by decide
theorem uck_x_done : ∀ a : K3, uckK .x a .f = .x := by decide
/-- An X reset is harmless when the XNOR already says "open". -/
theorem ux_xrst : ∀ v : Bool, uxK (.ofBool v) (.ofBool v) .x = .t := by decide
/-- `uz`: the CLOSE never waits for the slow reopen line `s`: with done ≠ ack
definite and rst = 0, `en = 0` whatever `s` is (X included). -/
theorem uz_close_any_s : ∀ (s : K3) (v : Bool), uzK s (.ofBool v) (.ofBool (!v)) .f = .f := by decide
/-- A low (or X-free low) `s` holds the stage closed whatever done/ack/rst do. -/
theorem uz_s_low : ∀ d a r : K3, uzK .f d a r = .f := by decide
/-- The reopen needs `s` high: `en = 1` iff `s = 1` and (rst or done = ack). -/
theorem uz_open_iff : ∀ s d a r : K3,
    uzK s d a r = .t ↔ (s = .t ∧ (r = .t ∨ (d ≠ .x ∧ d = a))) := by decide

/-! ### `bd_mlink_ctl`, the composite loop (NOPEN = 1)

`done = latch(req_in, en)`, `en = ux(done, ack, rst)`: two loops on `done`,
the latch's own (pin I2) and the one through `ux` (pin I1). The composite
next-state map (both pins reading the settled `done`): -/

def mlinkF (req ack rst done : Bool) : Bool :=
  lutB INIT_LAT [req, lutB INIT_UX [done, ack, rst], done, false, false, false]
def mlinkFK (req ack rst done : K3) : K3 := latK req (uxK done ack rst) done

/-- Binary: transparent (done = ack, or rst) gives `req`, else hold. -/
theorem mlinkF_eq : ∀ req ack rst done : Bool,
    mlinkF req ack rst done = (if rst || (done == ack) then req else done) := by decide
/-- Fixed points: stable iff the stage is full (done ≠ ack) or `req = done`. -/
theorem mlinkF_fixed_iff : ∀ req ack done : Bool,
    mlinkF req ack false done = done ↔ (done ≠ ack ∨ req = done) := by decide
/-- No oscillation: one application reaches a fixed point (idempotent map). -/
theorem mlinkF_idem : ∀ req ack rst done : Bool,
    mlinkF req ack rst (mlinkF req ack rst done) = mlinkF req ack rst done := by decide
/-- Kleene: an X on `done` is a fixed point of the composite loop whenever
rst = 0, whatever req and ack are; only reset restores it (to `req`). So the
settled-loop (untimed Kleene) model cannot show that a toggle of `req` into an
empty stage produces a definite `done`: that needs the ordering of the two
feedback paths, Section 5. -/
theorem mlink_x_stuck : ∀ req ack : K3, mlinkFK req ack .f .x = .x := by decide
theorem mlink_x_rst : ∀ req ack : K3, mlinkFK req ack .t .x = req := by decide

/-! ### `bd_link_dctl`: three SR state bits, each on its own feedback pin

`ub` (feedback I3), `ua` (I3), `uld` (I3). For each: with the other inputs
definite, X on the feedback pin is restored iff rst, the set or the reset term
is asserted (otherwise the bit is in hold and Kleene keeps the X). Binary
hold: neither set nor reset gives `q`. -/

theorem db_restore : ∀ req ack ld rst : Bool,
    lutK INIT_DB [.ofBool req, .ofBool ack, .ofBool ld, .x, .ofBool rst, .f] ≠ .x ↔
      (rst || (req && ld && !ack) || (ack && !ld)) = true := by decide
theorem da_restore : ∀ req b ld rst : Bool,
    lutK INIT_DA [.ofBool req, .ofBool b, .ofBool ld, .x, .ofBool rst, .f] ≠ .x ↔
      (rst || (req && b && ld) || (!req && !ld)) = true := by decide
theorem dld_restore : ∀ lt s a rst : Bool,
    lutK INIT_DLD [.ofBool lt, .ofBool s, .ofBool a, .x, .ofBool rst, .f] ≠ .x ↔
      (rst || (lt && s && !a) || a) = true := by decide

theorem db_hold : ∀ req ack ld q : Bool,
    (req && ld && !ack) = false → (ack && !ld) = false →
    lutB INIT_DB [req, ack, ld, q, false, false] = q := by decide
theorem da_hold : ∀ req b ld q : Bool,
    (req && b && ld) = false → (!req && !ld) = false →
    lutB INIT_DA [req, b, ld, q, false, false] = q := by decide
theorem dld_hold : ∀ lt s a q : Bool,
    (lt && s && !a) = false → a = false →
    lutB INIT_DLD [lt, s, a, q, false, false] = q := by decide

/-- Reset clears every state bit even with X on all other pins. -/
theorem dctl_rst_K : ∀ p0 p1 p2 p3 : K3,
    lutK INIT_DB [p0, p1, p2, p3, .t, .f] = .f ∧
    lutK INIT_DA [p0, p1, p2, p3, .t, .f] = .f ∧
    lutK INIT_DLD [p0, p1, p2, p3, .t, .f] = .f := by decide

/-- `uld` with LDN > 0: `s` low (the FASTFALL line has flushed) blocks the
set; an `lt` pulse that is X while `s` is low cannot set `ld` (the header's
"an lt pulse too short to set ld is simply lost"). -/
theorem dld_s_low_blocks : ∀ lt a : K3,
    lutK INIT_DLD [lt, .f, a, .f, .f, .f] = .f := by decide

end Formal.Cells.LibEndMemMlink

namespace Formal.Cells.LibEndMemMlink
open Formal.Cells

/-! ## 5. The MOUSETRAP request bit: which feedback path must win

One stage, one token. The stage is empty (`done = ack = v`, enable open) and
the sender toggles `req_in` to `!v`. Wires are separate state bits so that
every interleaving of their arrivals is explored:

* `done` the latch LUT's output (= `ack_in`, and `req_out` before its delay),
* `qp`   the latch's own feedback pin I2 (the routed `done -> uq.I2` wire),
* `dn`   the enable LUT's done pin (the routed `done -> ux.I0` wire),
* `en`   the enable LUT's output, read by the latch's I1 (the en wire is folded
  into the enable LUT's arc; a separate wire would only add interleavings
  that the hypothesis below already orders).
* `seen` ghost bit: `done` has taken the new value `!v` at least once.

Transitions: `L` latch LUT fires, `Q` / `D` the two wires copy `done`, `E` the
enable LUT fires. Each happens only when excited. Two instances, both with the
real INITs: `bd_mlink_ctl` (latch `B8B8..`, enable `ux` with rst = 0) and
`bd_flink_ctl` (latch `E2`, clock `uck` with rst = 0, latch transparent while
ck = 0). State encoding: bit 0 done, 1 qp, 2 dn, 3 en, 4 seen.

**H_QFB_FIRST** (the allowed-schedule restriction `allowH`): the enable LUT
does not change its output while the latch's own feedback pin still differs
from `done`. Physically: `done -> uq.I2` wire delay (max) < `done -> ux.I0`
wire + `ux` arc + `en -> uq.I1` wire (min). Test: the routed SDF, as
`tighten.loop_wire` (max) against the enable path (min) at the slow/fast
corners; or GLS forcing a long `uq.I2` wire. This is the request-bit twin of
the data bits' loop-settle condition. -/

inductive Lbl | L | Q | D | E
  deriving DecidableEq, Repr

def bit (s i : Nat) : Bool := s.testBit i
def mk (done qp dn en seen : Bool) : Nat :=
  (if done then 1 else 0) + (if qp then 2 else 0) + (if dn then 4 else 0) +
  (if en then 8 else 0) + (if seen then 16 else 0)

/-- One cell: latch function `lf req en q`, enable function `ef dn ack`. -/
structure Cell where
  lf : Bool → Bool → Bool → Bool
  ef : Bool → Bool → Bool

def mlinkCell : Cell :=
  ⟨fun r e q => lutB INIT_LAT [r, e, q, false, false, false],
   fun d a => lutB INIT_UX [d, a, false]⟩
def flinkCell : Cell :=
  ⟨fun r c q => lutB INIT_FQ [r, c, q],
   fun d a => lutB INIT_UCK [d, a, false]⟩

/-- The excited transition `l` from `s`, if any (`req = !v`, `ack = v`). -/
def nxt (c : Cell) (v : Bool) (s : Nat) : Lbl → Option Nat
  | .L => let o := c.lf (!v) (bit s 3) (bit s 1)
          if o != bit s 0 then some (mk o (bit s 1) (bit s 2) (bit s 3) (bit s 4 || o == !v)) else none
  | .Q => if bit s 1 != bit s 0 then some (mk (bit s 0) (bit s 0) (bit s 2) (bit s 3) (bit s 4)) else none
  | .D => if bit s 2 != bit s 0 then some (mk (bit s 0) (bit s 1) (bit s 0) (bit s 3) (bit s 4)) else none
  | .E => let e := c.ef (bit s 2) v
          if e != bit s 3 then some (mk (bit s 0) (bit s 1) (bit s 2) e (bit s 4)) else none

def s0 (c : Cell) (v : Bool) : Nat := mk v v v (c.ef v v) false

def allowH (s : Nat) (l : Lbl) : Bool := l != .E || bit s 1 == bit s 0
def allowAny (_ : Nat) (_ : Lbl) : Bool := true

inductive Reach (c : Cell) (v : Bool) (al : Nat → Lbl → Bool) : Nat → Prop
  | init : Reach c v al (s0 c v)
  | step {s t l} : Reach c v al s → al s l = true → nxt c v s l = some t → Reach c v al t

def succs (c : Cell) (v : Bool) (al : Nat → Lbl → Bool) (s : Nat) : List Nat :=
  [Lbl.L, .Q, .D, .E].filterMap (fun l => if al s l then nxt c v s l else none)

/-- A candidate reachable set is every state below 32 that passes a mask. -/
def inMask (m s : Nat) : Bool := m.testBit s
def closedB (c : Cell) (v : Bool) (al : Nat → Lbl → Bool) (m : Nat) : Bool :=
  (List.range 32).all fun s => !inMask m s || (succs c v al s).all (fun t => t < 32 && inMask m t)

theorem mem_succs {c v al s l t} (ha : al s l = true) (hn : nxt c v s l = some t) :
    t ∈ succs c v al s := by
  simp only [succs, List.mem_filterMap]
  exact ⟨l, by cases l <;> simp, by simp [ha, hn]⟩

theorem reach_mask {c v al m} (hc : closedB c v al m = true) (h0 : s0 c v < 32)
    (hm0 : inMask m (s0 c v) = true) {s} (h : Reach c v al s) : s < 32 ∧ inMask m s = true := by
  induction h with
  | init => exact ⟨h0, hm0⟩
  | @step s t l _ ha hn ih =>
    have hall := List.all_eq_true.mp hc s (List.mem_range.mpr ih.1)
    simp only [ih.2, Bool.not_true, Bool.false_or] at hall
    have := List.all_eq_true.mp hall t (mem_succs ha hn)
    simp only [Bool.and_eq_true, decide_eq_true_eq] at this
    exact this

/-- `pot`: number of the four wires not yet at their final value. -/
def fin (c : Cell) (v : Bool) : Nat := mk (!v) (!v) (!v) (c.ef (!v) v) true
def pot (c : Cell) (v : Bool) (s : Nat) : Nat :=
  (List.range 4).countP fun i => bit s i != bit (fin c v) i

/-- The finite facts checked by enumeration over the mask: closed under the
allowed steps; no runt (once `done` has been `!v` it stays `!v`); every
step lowers the potential (so every run terminates); the only state with no
allowed step is `fin` (no deadlock short of the intended final state). -/
def goodH (c : Cell) (v : Bool) (m : Nat) : Bool :=
  closedB c v allowH m && s0 c v < 32 && inMask m (s0 c v) &&
  (List.range 32).all fun s => !inMask m s ||
    ((!bit s 4 || bit s 0 == !v) &&
     (succs c v allowH s).all (fun t => pot c v t < pot c v s) &&
     (!(succs c v allowH s).isEmpty || s == fin c v))

/-- Masks: the reachable sets under H_QFB_FIRST (computed by a BFS run
outside this file, then CHECKED here: `goodH` re-verifies closure, so a wrong
mask can only make the check fail, never make it pass vacuously; `s0` is in
it by the check). -/
def mML0 : Nat := 0xaa800100
def mML1 : Nat := 0x55018000
def mFL0 : Nat := 0x80aa0001
def mFL1 : Nat := 0x1550080

theorem mlink_goodH : goodH mlinkCell false mML0 = true ∧ goodH mlinkCell true mML1 = true := by
  decide
theorem flink_goodH : goodH flinkCell false mFL0 = true ∧ goodH flinkCell true mFL1 = true := by
  decide

theorem good_props {c v m} (hg : goodH c v m = true) {s} (h : Reach c v allowH s) :
    (bit s 4 = true → bit s 0 = !v) ∧
    (∀ t ∈ succs c v allowH s, pot c v t < pot c v s) ∧
    (succs c v allowH s = [] → s = fin c v) := by
  simp only [goodH, Bool.and_eq_true] at hg
  obtain ⟨⟨⟨hc, h32⟩, hm0⟩, hall⟩ := hg
  have hr := reach_mask hc (by simpa using h32) hm0 h
  have hs := List.all_eq_true.mp hall s (List.mem_range.mpr hr.1)
  simp only [hr.2, Bool.not_true, Bool.false_or, Bool.and_eq_true] at hs
  obtain ⟨⟨h1, h2⟩, h3⟩ := hs
  refine ⟨fun hb => ?_, fun t ht => ?_, fun he => ?_⟩
  · simp [hb] at h1; exact h1
  · have := List.all_eq_true.mp h2 t ht; simpa using this
  · simp [he] at h3; exact h3

/-- **MOUSETRAP request bit, `bd_mlink_ctl` (NOPEN = 1), under H_QFB_FIRST.**
For both token polarities, in every reachable state: (a) no runt: once `done`
(= `ack_in`) has toggled it never toggles back; (b) every allowed step lowers
`pot`, so every run is finite (at most 4 steps after the request toggle);
(c) the only state where nothing can move is `fin`: `done = qp = dn = !v` and
the enable closed. So the stage captures the token and closes on it. -/
theorem mlink_req_bit_H (v : Bool) {s} (h : Reach mlinkCell v allowH s) :
    (bit s 4 = true → bit s 0 = !v) ∧
    (∀ t ∈ succs mlinkCell v allowH s, pot mlinkCell v t < pot mlinkCell v s) ∧
    (succs mlinkCell v allowH s = [] → s = fin mlinkCell v) := by
  cases v
  · exact good_props mlink_goodH.1 h
  · exact good_props mlink_goodH.2 h

/-- The same for `bd_flink_ctl` (request bit `uq`, clock `uck`). -/
theorem flink_req_bit_H (v : Bool) {s} (h : Reach flinkCell v allowH s) :
    (bit s 4 = true → bit s 0 = !v) ∧
    (∀ t ∈ succs flinkCell v allowH s, pot flinkCell v t < pot flinkCell v s) ∧
    (succs flinkCell v allowH s = [] → s = fin flinkCell v) := by
  cases v
  · exact good_props flink_goodH.1 h
  · exact good_props flink_goodH.2 h

/-- The closed stage really is closed: in `fin` the enable is shut
(mlink: `en = 0`; flink: `ck = 1`). -/
theorem fin_closed : bit (fin mlinkCell false) 3 = false ∧ bit (fin mlinkCell true) 3 = false ∧
    bit (fin flinkCell false) 3 = true ∧ bit (fin flinkCell true) 3 = true := by decide

/-! ### Without H_QFB_FIRST: runt, and an unbounded runt train

Trace `L D E L`: the latch takes the new request, the enable LUT sees it first
and closes, and the latch, still reading the OLD value on its own feedback
pin, re-latches the old value: `done` (= `ack_in`, and `req_out` after the
delay line) toggles and toggles back. `D E` then reopens the stage with the
request still pending, and the state is the start state again: the trace
`L D E` repeated is an oscillation that pure interleaving does not exclude. -/

def run (c : Cell) (v : Bool) : Nat → List Lbl → Option Nat
  | s, [] => some s
  | s, l :: ls => match nxt c v s l with
    | some t => run c v t ls
    | none => none

theorem reach_run {c v s} (hs : Reach c v allowAny s) :
    ∀ {ls t}, run c v s ls = some t → Reach c v allowAny t := by
  intro ls
  induction ls generalizing s with
  | nil => intro t h; simp [run] at h; subst h; exact hs
  | cons l ls ih =>
    intro t h
    simp only [run] at h
    split at h
    · rename_i u hu; exact ih (Reach.step hs rfl hu) h
    · simp at h

/-- mlink, token `0 -> 1`: after `L D E L` the state is 20: `done = 0`
again although it was 1 (seen), and `en = 0`. -/
theorem mlink_runt : run mlinkCell false (s0 mlinkCell false) [.L, .D, .E, .L] = some 20 ∧
    bit 20 4 = true ∧ bit 20 0 = false := by decide
/-- ... and `D E` returns to the start state (with `seen` set): a cycle. -/
theorem mlink_cycle : run mlinkCell false 20 [.D, .E] = some (s0 mlinkCell false + 16) ∧
    run mlinkCell false (s0 mlinkCell false + 16) [.L, .D, .E, .L, .D, .E] = some (s0 mlinkCell false + 16) := by
  decide
theorem flink_runt : run flinkCell false (s0 flinkCell false) [.L, .D, .E, .L] = some 28 ∧
    bit 28 4 = true ∧ bit 28 0 = false := by decide
theorem flink_cycle :
    run flinkCell false (s0 flinkCell false + 16) [.L, .D, .E, .L, .D, .E] = some (s0 flinkCell false + 16) := by
  decide

/-- Negative control: the closure check can fail. The masks that pass under
H_QFB_FIRST are NOT closed once the restriction is dropped. -/
theorem masks_fail_without_H : closedB mlinkCell false allowAny mML0 = false ∧
    closedB flinkCell false allowAny mFL0 = false := by decide

/-- Stated as reachability in the unrestricted model. -/
theorem mlink_runt_reach : Reach mlinkCell false allowAny 20 :=
  reach_run Reach.init mlink_runt.1
theorem flink_runt_reach : Reach flinkCell false allowAny 28 :=
  reach_run Reach.init flink_runt.1
/-! ## 6. `bd_delay_gated`: same LUTs as a FASTFALL `bd_delay`, taps on `gate`

The INITs are `bd_delay`'s (`2'h2` head, `4'h8` side stages, Bundling.lean's
`fastfall_line` instance). The only difference is the tap net. Stage facts
(Kleene) and the settled value of the whole line for any N. -/

def andK (s g : K3) : K3 := lutK INIT_AND [s, g]
def bufK (a : K3) : K3 := lutK INIT_BUF [a]

theorem buf_K : ∀ a : K3, bufK a = a := by decide
/-- A low tap forces the stage low whatever the chain carries (X included). -/
theorem and_tap_low : ∀ s : K3, andK s .f = .f := by decide
/-- A high tap makes the stage a buffer of the chain pin. -/
theorem and_tap_high : ∀ s : K3, andK s .t = s := by decide
/-- X on the tap with the chain low is contained. -/
theorem and_tap_x_chain_low : andK .f .x = .f := by decide

/-- The settled Kleene value of `bd_delay_gated #(.N(n+1))`: `g0` buffers
`a`, every `g[i>=1]` ANDs with `gate`. -/
def gatedK : Nat → K3 → K3 → K3
  | 0, a, _ => bufK a
  | n + 1, a, g => andK (gatedK n a g) g

/-- With `gate` and `a` carrying the same settled value (the header's
"`a` must be a buffered copy of `gate`", in steady state), the line outputs
that value, for every length. -/
theorem gated_settled (n : Nat) (v : K3) : gatedK n v v = v := by
  induction n with
  | zero => exact buf_K v
  | succ n ih => simp only [gatedK, ih]; cases v <;> decide
/-- A low `gate` forces `z` low after one side stage, whatever `a` is. -/
theorem gated_gate_low (n : Nat) (a : K3) : gatedK (n + 1) a .f = .f := by
  simp only [gatedK]; exact and_tap_low _
/-- The header's warning, as a fact: if `gate` dips while `a` stays high, the
settled line value is low, so the line has been flushed and must re-ripple
from `s[0]`: `a` and `gate` diverging is a request glitch, not a no-op. -/
theorem gated_dip_flushes (n : Nat) : gatedK (n + 1) .t .f = .f := gated_gate_low n .t

/-! ## 7. `bd_mem`: the LUT part and the BRAM interface as named hypotheses

LUTs: the clock buffer `ubuf` (`2'h2`, `buf_eq`, `buf_K`, `rep_buf`) and the
two symmetric `bd_delay` lines (`2'h2` per hop, Bundling.lean `sym_edge`).
`bdc/mem.py` emits `bd_mem` only with `USE_BUFG = 0`, so `ubuf` is the LUT
(the BUFG branch is not modelled; its delay would enter `ds*` below).
The RAMB18E1 is NOT modelled as a gate: it enters only through datasheet
parameters (`tSU`, `tHD`, `tCO`, `tPWH`, `tPWL`) in `MemPort`.

Times are ps (Nat). One access, then the next one's clock rise. -/

structure MemPort where
  -- events of this access
  tReqR : Nat
  tReqF : Nat
  tClkR : Nat
  tClkF : Nat
  tAckR : Nat
  tAckF : Nat
  /-- last change of `addr`/`wdata`/`we` before this access -/
  tPay : Nat
  /-- first change of `addr`/`wdata`/`we` after this access -/
  tPayNext : Nat
  /-- next access: request rise and clock rise -/
  tReqR2 : Nat
  tClkR2 : Nat
  -- line bounds: DSETUP line + `ubuf` + clock net (rise / fall), DCO line + ack wire
  dsLo : Nat
  dsHi : Nat
  dsLoF : Nat
  dsHiF : Nat
  dcLo : Nat
  dcLoF : Nat
  -- RAMB18E1 datasheet / chipdb parameters for CLKARDCLK
  tSU : Nat
  tHD : Nat
  tCO : Nat
  /-- **H_SETUP_LINE**: `req -> usetup -> ubuf -> CLKARDCLK` rise and fall lie
  within the routed bounds (Bundling.sym_edge for the chain, plus the buffer
  and the clock net). Includes **H_NO_INFERRED_BUF**: nothing else is on the
  clock net (`clkbuf_inhibit`, `-noclkbuf`); test: netlist/FASM inspection
  that `ram_clk` has exactly one driver, the `ubuf` LUT. -/
  H_SETUP_LINE : tReqR + dsLo ≤ tClkR ∧ tClkR ≤ tReqR + dsHi ∧
                 tReqF + dsLoF ≤ tClkF ∧ tClkF ≤ tReqF + dsHiF ∧
                 tReqR2 + dsLo ≤ tClkR2
  /-- **H_CO_LINE**: `ram_clk -> uco -> ack`, lower bounds for both edges,
  measured from the SAME net that clocks the RAM (the header's "timing tap
  downstream of the same buffer"). Test: SDF of the route, slow/fast corners. -/
  H_CO_LINE : tClkR + dcLo ≤ tAckR ∧ tClkF + dcLoF ≤ tAckF
  /-- **H_FOUR_PHASE_ENV**: the requester is four-phase and bundled: payload
  settled before req rises; req falls only after ack rose; payload held and the
  next request raised only after ack fell. -/
  H_FOUR_PHASE_ENV : tPay ≤ tReqR ∧ tAckR ≤ tReqF ∧ tAckF ≤ tPayNext ∧ tAckF ≤ tReqR2

namespace MemPort
variable (m : MemPort)

/-- **Setup at the RAM** (`ADDR/DI/WE` before `CLKARDCLK` rise): holds when
the DSETUP line's minimum covers the RAM setup time. This is the cell's
bundling obligation at the RAM boundary. -/
theorem setup_ok (h : m.tSU ≤ m.dsLo) : m.tPay + m.tSU ≤ m.tClkR := by
  have := m.H_SETUP_LINE; have := m.H_FOUR_PHASE_ENV; omega

/-- **Hold at the RAM**: the payload cannot move before
`tClkR + dcLo + dsLoF + dcLoF` (the ack round trip), so hold is met whenever
that exceeds `tHD`; with any non-zero lines it is met by the protocol. -/
theorem hold_ok (h : m.tHD ≤ m.dcLo + m.dsLoF + m.dcLoF) : m.tClkR + m.tHD ≤ m.tPayNext := by
  have := m.H_SETUP_LINE; have := m.H_CO_LINE; have := m.H_FOUR_PHASE_ENV; omega

/-- **Read data before ack**: with `DOA_REG = 0`, `DOADO` is valid `tCO` after
the clock rise; ack rises no earlier than `dcLo` after it. (The consumer's own
`rdata` vs `ack` route skew is a further term, not included: H_RDATA_ROUTE in
the notes.) -/
theorem rdata_before_ack (h : m.tCO ≤ m.dcLo) : m.tClkR + m.tCO ≤ m.tAckR := by
  have := m.H_CO_LINE; omega

/-- **Clock high width** is at least `dsLo + dcLo + dsLoF - dsHi` (the
handshake round trip), whatever the environment does. -/
theorem clk_high_width : m.dsLo + m.dcLo + m.dsLoF ≤ m.tClkF - m.tClkR + m.dsHi := by
  have := m.H_SETUP_LINE; have := m.H_CO_LINE; have := m.H_FOUR_PHASE_ENV; omega

/-- **No return-to-zero overlap** (the failure mode the header names): the next
access's clock rise is at least `dcLoF + dsLo` after this access's clock
fall. The four-phase protocol plus the two lines serialise the port; nothing
about margins is involved. -/
theorem rtz_serialised : m.tClkF + m.dcLoF + m.dsLo ≤ m.tClkR2 := by
  have := m.H_SETUP_LINE; have := m.H_CO_LINE; have := m.H_FOUR_PHASE_ENV; omega

end MemPort

end Formal.Cells.LibEndMemMlink
