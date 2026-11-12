import Formal.Core.Prims.RamXray

/-!
# Formal.Core.Prims.RamBd — the bundled-data obligation `bd_mem` imposes on its RAM

Shard A, probe PrimsRam. Core Lean only. Notes: `formal/notes/A-prims-ram.md` §4.

`cells/rtl/bd_mem.v`:

    req --[ usetup: bd_delay DSETUP ]--> strobe --[ ubuf: LUT1 ]--> ram_clk --+--> CLKARDCLK
                                                                             +--[ uco: bd_delay DCO ]--> ack

The request edge IS the RAM clock edge, and `ack` is the only statement that `rdata` is
valid. So the RAM's windows become bundling obligations. Events of one access, at ONE corner
(`T`), times in ps on the Core grid:

* `r`: `req` rises at bd_mem. The requester is bundled (B's **H_FOUR_PHASE_ENV**): the payload
  (`addr`, `wdata`, `we`) is settled at the requester by `r` and reaches the BRAM pins at most
  `dP` later, so it is settled at the pins from `p ≤ r + dP`; it is held until `q`, and `q ≥ k`
  (it moves only after the acknowledge; bdc's `hold` gate holds it even longer).
* `b`: `ram_clk` rises, `b ≥ r + sLo` (`usetup` + `ubuf`, lower bound).
* `e`: CLKARDCLK rises at the BRAM pin, `b + wLo ≤ e ≤ b + wHi` (the `ram_clk` route).
* `k`: `ack` rises, `k ≥ b + cLo` (`uco` from the SAME net `ram_clk`, header rule "keep the
  capture edge and the timing tap downstream of the same buffer").

## Results
* `access_ok`: the RAM-level statement: payload stable over every window ⇒ DOADO is the
  WRITE_FIRST/read result on `(e + cqHi, next edge]`, and the array is updated.
* `bd_access_ok`: **the derived obligation**. If `dP ≤ sLo + wLo + lo` for each of the
  ADDR/WE/DI windows (setup: the request edge reaches CLKARDCLK after the payload settles plus
  setup) and `wHi + cqHi < cLo` (clock-to-out: `ack` after the slowest DOADO), then DOADO at
  the `ack` edge (and until the next clock edge) is the right value. Hold is implied:
  `hold_from_co` (`hi ≤ cqHi`, true for every pin at both prjxray corners).
* `co_necessary`: if `cLo ≤ wHi + cqHi`, the placement `e = b + wHi`, `k = b + cLo` is
  admissible and EVERY run of the RAM model reads a wrong DOADO at `ack` on the first write of
  a 1 (INIT_A = 0). So the clock-to-out obligation is exact at the band ends.
* `setup_necessary`: a DI change inside the DI window gives X (the setup obligation is not
  slack in the model).
* `bd_obligation_slow`: bd_mem's numbers at the slow corner: `dP + 737 ≤ sLo + wLo` (DI is
  the widest setup; ADDR 566, WE 532) and `wHi + 2454 < cLo`.

## NOT covered
The delay lines themselves (B's `LibEndMemMlink.MemPort` and `Bundling` give their bands);
the route from DOADO to the consumer and the consumer's own capture window
(**H_RDATA_ROUTE**, as in B); the return-to-zero phase and the next access (serialisation is
B's `rtz_serialised` and bdc/mem.py's `hold` gate; here it is the hypothesis that the next
CLKARDCLK edge comes after the time considered); clock runts or pulse width (H_CK_BINARY,
H_BRAM_PERIOD); the automatic-BUFG failure mode (an extra buffer changes `wLo/wHi`, and the
theorem then applies with the larger numbers: it shows why that breaks `wHi + cqHi < cLo`).
-/

namespace Formal.Core.Prims.Ram

open Formal.Core Formal.Core.K3 Formal.Core.Substrate Formal.Core.Prims.Seq

/-- bd_mem's array at power-up: no INIT_xx parameter, so all zero. -/
def bdInit : Mem 10 16 := fun _ _ => zero
/-- bd_mem's DOADO at power-up: no INIT_A, so zero. -/
def bdInitA : KWord 16 := fun _ => zero

/-- The value a WRITE_FIRST access returns: the data written, or the word read. -/
def wfResult {aw dw : Nat} (w : Bool) (v : BAddr aw) (d : Fin dw → Bool) (m : Mem aw dw) :
    KWord dw := if w then ofBoolVec d else m v

section
variable {aw dw : Nat} {T : RamTiming} {rdis : Bool} {init : Mem aw dw} {initA : KWord dw}
  {ck : Sig} {a : Fin aw → KSig} {we : KSig} {din : Fin dw → KSig} {m : Nat → Mem aw dw}
  {dout : Fin dw → KSig}

/-- The payload is stable on `[p, q]`: address `v`, WE `w`, and (for a write) data `d`. -/
def PayloadOn (a : Fin aw → KSig) (we : KSig) (din : Fin dw → KSig) (v : BAddr aw) (w : Bool)
    (d : Fin dw → Bool) (p q : Nat) : Prop :=
  (∀ i, EqOn (a i) (ofBool (v i)) p q) ∧ EqOn we (ofBool w) p q ∧
    (w = true → ∀ j, EqOn (din j) (ofBool (d j)) p q)

theorem eqOn_sub {x : KSig} {v : K3} {p q a b : Nat} (h : EqOn x v p q) (ha : p ≤ a) (hb : b ≤ q) :
    EqOn x v a b := fun s h1 h2 => h s (by omega) (by omega)

/-- **The access at the RAM pins.** Payload stable over `[p, q]`, which covers all three
windows of the edge `e`. Then after `e + cqHi`, until the next edge, DOADO is the WRITE_FIRST
result, and the array is the Boolean update. -/
theorem access_ok (hok : T.Ok) (h : RamRel T .writeFirst rdis init initA ck a we din m dout)
    {e t p q : Nat} {v : BAddr aw} {w : Bool} {d : Fin dw → Bool} (he : rises ck e)
    (het : e < t) (hn : NoRise ck e t) (hP : PayloadOn a we din v w d p q)
    (hsa : (p : Int) ≤ e + T.aLo) (hsw : (p : Int) ≤ e + T.weLo) (hsd : (p : Int) ≤ e + T.dLo)
    (hha : (e : Int) + T.aHi ≤ q) (hhw : (e : Int) + T.weHi ≤ q) (hhd : (e : Int) + T.dHi ≤ q)
    (ht : e + T.cqHi < t) :
    (∀ j, dout j t = wfResult w v d (m e) j) ∧
      m t v = wfResult w v d (m e) ∧ ∀ u, u ≠ v → m t u = m e u := by
  obtain ⟨hA, hW, hD⟩ := hP
  have hA' : AddrOn T a v e := fun i => eqOn_sub (hA i) (by unfold wpt; omega) (by unfold wpt; omega)
  have hW' : WeOn T we w e := eqOn_sub hW (by unfold wpt; omega) (by unfold wpt; omega)
  cases w with
  | false =>
    refine ⟨fun j => ?_, ?_, fun u _ => ?_⟩
    · rw [read_out hok h he het hn hA' hW' ht j]; try rfl
    · rw [mem_read_keeps hok h he het hn hA' hW']; try rfl
    · rw [mem_read_keeps hok h he het hn hA' hW']
  | true =>
    have hD' : DataOn T din d e := fun j =>
      eqOn_sub (hD rfl j) (by unfold wpt; omega) (by unfold wpt; omega)
    obtain ⟨h1, h2⟩ := mem_write hok h he het hn hA' hW' hD'
    exact ⟨fun j => wf_read_during_write hok h he het hn hW' hD' ht j, h1, h2⟩

/-- DOADO keeps the access's value through the next edge's `cqLo`: valid on
`(e + cqHi, e2 + cqLo]` when the next edge is at `e2 > e + cqHi`. -/
theorem out_until_next (h : RamRel T .writeFirst rdis init initA ck a we din m dout)
    {e2 t : Nat} {x : KWord dw} (he2 : rises ck e2) (hlt : e2 < t) (hn2 : NoRise ck e2 t)
    (ht : t ≤ e2 + T.cqLo) (hval : ∀ j, dout j e2 = x j) (j : Fin dw) : dout j t = x j := by
  rw [h.ohold e2 t he2 hlt hn2 ht j, hval j]

/-! ## The derived obligation, in terms of bd_mem's paths -/

/-- **bd_mem's bundled-data obligation, derived.** Bands: payload route `≤ dP`, `req -> ram_clk`
`≥ sLo`, `ram_clk -> CLKARDCLK` in `[wLo, wHi]`, `ram_clk -> ack` `≥ cLo`.
Obligations: (setup) `dP ≤ sLo + wLo + lo` for the ADDR, WE and DI windows, (hold)
`wHi + hi ≤ cLo` for each, (clock-to-out) `wHi + cqHi < cLo`. Then the value on DOADO at the
`ack` edge `k` is the right one (the data written, or the word read), provided no other
CLKARDCLK edge lies in `(e, k]`. -/
theorem bd_access_ok (hok : T.Ok) (h : RamRel T .writeFirst rdis init initA ck a we din m dout)
    {r b e k p q dP sLo wLo wHi cLo : Nat} {v : BAddr aw} {w : Bool} {d : Fin dw → Bool}
    (he : rises ck e) (hn : NoRise ck e (k + 1))
    -- the paths
    (hp : p ≤ r + dP) (hb : r + sLo ≤ b) (he1 : b + wLo ≤ e) (he2 : e ≤ b + wHi)
    (hk : b + cLo ≤ k) (hq : k ≤ q) (hP : PayloadOn a we din v w d p q)
    -- the obligations
    (osa : (dP : Int) ≤ sLo + wLo + T.aLo) (osw : (dP : Int) ≤ sLo + wLo + T.weLo)
    (osd : (dP : Int) ≤ sLo + wLo + T.dLo)
    (oha : (wHi : Int) + T.aHi ≤ cLo) (ohw : (wHi : Int) + T.weHi ≤ cLo)
    (ohd : (wHi : Int) + T.dHi ≤ cLo) (oco : wHi + T.cqHi < cLo) (j : Fin dw) :
    dout j k = wfResult w v d (m e) j := by
  have hnk : NoRise ck e k := fun u h1 h2 => hn u h1 (by omega)
  exact (access_ok hok h he (by omega) hnk hP (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega)).1 j

/-- **Hold follows from the clock-to-out obligation** whenever the hold end of a window is at
most `cqHi` (prjxray: every pin, both corners: 360, 197, 667 ≤ 1098). -/
theorem hold_from_co {wHi cLo cqHi : Nat} {hi : Int} (hle : hi ≤ cqHi) (oco : wHi + cqHi < cLo) :
    (wHi : Int) + hi ≤ cLo := by omega

theorem bram_hold_le_cq (c : XCorner) :
    (bram c .writeFirst).aHi ≤ (bram c .writeFirst).cqHi ∧
    (bram c .writeFirst).weHi ≤ (bram c .writeFirst).cqHi ∧
    (bram c .writeFirst).dHi ≤ (bram c .writeFirst).cqHi := by
  cases c <;> decide

/-! ## Necessity (negative controls that can fail) -/

/-- **The clock-to-out obligation is necessary.** If `cLo ≤ wHi + cqHi`, take the admissible
placement `e = b + wHi` (slowest clock wire) and `k = b + cLo` (fastest ack). On the first
access after power-up (no edge before `e`), with `INIT_A` bit `j` = 0 and a WRITE_FIRST write
of a 1 to bit `j` with WE and DI clean (any address), EVERY run of the model has DOADO bit `j` ≠ 1 at `ack`: the old 0
up to `e + cqLo`, X in the band. (Runs exist: `ramSim_rel`.) -/
theorem co_necessary (hok : T.Ok) (h : RamRel T .writeFirst rdis init initA ck a we din m dout)
    {b wHi cLo : Nat} {d : Fin dw → Bool} {j : Fin dw}
    (hbad : cLo ≤ wHi + T.cqHi)
    (he : rises ck (b + wHi)) (hfirst : ∀ u, u < b + wHi → ¬ rises ck u)
    (hn : NoRise ck (b + wHi) (b + cLo + 1))
    (hW : WeOn T we true (b + wHi))
    (hD : DataOn T din d (b + wHi)) (hinit : initA j = zero) (hdj : d j = true) :
    dout j (b + cLo) ≠ one := by
  have h0 : dout j (b + wHi) = zero := by rw [h.oinit _ hfirst j, hinit]
  by_cases hle : b + cLo ≤ b + wHi
  · have : ∀ u, u < b + cLo → ¬ rises ck u := fun u hu => hfirst u (by omega)
    rw [h.oinit _ this j, hinit]; decide
  have hnk : NoRise ck (b + wHi) (b + cLo) := fun u h1 h2 => hn u h1 (by omega)
  by_cases h1 : b + cLo ≤ b + wHi + T.cqLo
  · rw [h.ohold _ _ he (by omega) hnk h1 j, h0]; decide
  · rw [h.oband _ _ he (by omega) hnk (by omega) (by omega) j, h0, rWE_of hok hW, rD_of hok hD]
    show merge zero (ofBool (d j)) ≠ one
    rw [hdj]; decide

/-- **The setup obligation is not slack.** If the DI bit changes at the pin at a time `p`
inside the DI window (`e + dLo < p ≤ e + dHi`), the stored bit and (WRITE_FIRST) DOADO are X. -/
theorem setup_necessary (hok : T.Ok) (h : RamRel T .writeFirst rdis init initA ck a we din m dout)
    {e t p : Nat} {v : BAddr aw} {j : Fin dw} (he : rises ck e) (het : e < t)
    (hn : NoRise ck e t) (hA : AddrOn T a v e) (hW : WeOn T we true e)
    (hp1 : (e : Int) + T.dLo < p) (hp2 : (p : Int) ≤ e + T.dHi) (hch : din j (p - 1) ≠ din j p) :
    m t v j = X ∧ (e + T.cqHi < t → dout j t = X) :=
  di_violation_X hok h he het hn hA hW (s1 := p - 1) (s2 := p)
    (by unfold wpt; omega) (by unfold wpt; omega) (by unfold wpt; omega) (by unfold wpt; omega) hch

end

/-! ## bd_mem's numbers -/

/-- **bd_mem's obligation at the prjxray slow corner** (WRITE_FIRST): setup reduces to the DI
window (`dP + 737 ≤ sLo + wLo`, which implies ADDR's 566 and WE's 532), hold is implied by
clock-to-out, and clock-to-out is `wHi + 2454 < cLo`. -/
theorem bd_obligation_slow {dP sLo wLo wHi cLo : Nat}
    (hs : dP + 737 ≤ sLo + wLo) (hc : wHi + 2454 < cLo) :
    (dP : Int) ≤ sLo + wLo + (bram .slow .writeFirst).aLo ∧
    (dP : Int) ≤ sLo + wLo + (bram .slow .writeFirst).weLo ∧
    (dP : Int) ≤ sLo + wLo + (bram .slow .writeFirst).dLo ∧
    (wHi : Int) + (bram .slow .writeFirst).aHi ≤ cLo ∧
    (wHi : Int) + (bram .slow .writeFirst).weHi ≤ cLo ∧
    (wHi : Int) + (bram .slow .writeFirst).dHi ≤ cLo ∧
    wHi + (bram .slow .writeFirst).cqHi < cLo := by
  simp only [bram_slow_wf]; omega

/-- The same at the fast corner: `wHi + 1098 < cLo` (the windows are the slow ones,
H_WINDOW_SLOW_ONLY). -/
theorem bd_obligation_fast {dP sLo wLo wHi cLo : Nat}
    (hs : dP + 737 ≤ sLo + wLo) (hc : wHi + 1098 < cLo) :
    (dP : Int) ≤ sLo + wLo + (bram .fast .writeFirst).aLo ∧
    (dP : Int) ≤ sLo + wLo + (bram .fast .writeFirst).weLo ∧
    (dP : Int) ≤ sLo + wLo + (bram .fast .writeFirst).dLo ∧
    (wHi : Int) + (bram .fast .writeFirst).aHi ≤ cLo ∧
    (wHi : Int) + (bram .fast .writeFirst).weHi ≤ cLo ∧
    (wHi : Int) + (bram .fast .writeFirst).dHi ≤ cLo ∧
    wHi + (bram .fast .writeFirst).cqHi < cLo := by
  simp only [bram_fast_wf]; omega

/-- **bd_mem, end to end at the slow corner** (aw = 10, dw = 16, WRITE_FIRST, INIT 0): under
the two numeric obligations, DOADO at `ack` is the right value. -/
theorem bd_mem_slow {rdis : Bool} {ck : Sig} {a : Fin 10 → KSig} {we : KSig}
    {din : Fin 16 → KSig} {m : Nat → Mem 10 16} {dout : Fin 16 → KSig}
    (h : RamRel (bram .slow .writeFirst) .writeFirst rdis bdInit bdInitA ck a we din m dout)
    {r b e k p q dP sLo wLo wHi cLo : Nat} {v : BAddr 10} {w : Bool} {d : Fin 16 → Bool}
    (he : rises ck e) (hn : NoRise ck e (k + 1))
    (hp : p ≤ r + dP) (hb : r + sLo ≤ b) (he1 : b + wLo ≤ e) (he2 : e ≤ b + wHi)
    (hk : b + cLo ≤ k) (hq : k ≤ q) (hP : PayloadOn a we din v w d p q)
    (hs : dP + 737 ≤ sLo + wLo) (hc : wHi + 2454 < cLo) (j : Fin 16) :
    dout j k = wfResult w v d (m e) j := by
  obtain ⟨o1, o2, o3, o4, o5, o6, o7⟩ := bd_obligation_slow hs hc
  exact bd_access_ok (bram_ok .slow .writeFirst) h he hn hp hb he1 he2 hk hq hP
    o1 o2 o3 o4 o5 o6 o7 j

end Formal.Core.Prims.Ram
