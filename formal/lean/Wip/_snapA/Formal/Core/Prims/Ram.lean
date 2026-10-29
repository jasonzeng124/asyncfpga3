import Formal.Core.Prims.SeqFlop

/-!
# Formal.Core.Prims.Ram — RAMB18E1 port A as `bd_mem` instantiates it, as a trace relation

Shard A, probe PrimsRam. Core Lean only (no Mathlib). Notes: `formal/notes/A-prims-ram.md`.
Numbers (prjxray-db `BRAM_L.sdf`): `Formal.Core.Prims.RamXray`. The bundled-data obligation
of `bd_mem`: `Formal.Core.Prims.RamBd`.

## What `cells/rtl/bd_mem.v` instantiates (read from the source, not assumed)

`RAMB18E1 #(.RAM_MODE("TDP"), .READ_WIDTH_A(18), .WRITE_WIDTH_A(18), .READ_WIDTH_B(0),
.WRITE_WIDTH_B(0), .DOA_REG(0), .DOB_REG(0), .WRITE_MODE_A("WRITE_FIRST"), ...)`, with
`CLKARDCLK = ram_clk` (the one explicit buffer after the `DSETUP` line, so the request edge
IS the clock edge), `ENARDEN = 1`, `REGCEAREGCE = 0`, `RSTRAMARSTRAM = RSTREGARSTREG = 0`,
`ADDRARDADDR = {addr, 4'b0000}` (x18: word address = bits [13:4], 1024 words),
`DIADI = wdata` (16 bits), `DIPADIP = 0`, `WEA = {we, we}` (both byte enables on one net),
`DOADO = rdata`, `DOPADOP` unconnected, port B tied off (`CLKBWRCLK = 0`, `ENBWREN = 0`,
`WEBWE = 0`). No `INIT_xx`/`INITP_xx`/`INIT_A` parameter: contents and output latch power
up at 0. So the only live pins are CLKARDCLK, ADDRARDADDR[13:4], DIADI[15:0], WEA (one net)
and DOADO[15:0]; ENARDEN/RST*/REGCE are constants and have no window to violate.

This file is generic in the address width `aw` and data width `dw`; `bd_mem` is
`aw = 10`, `dw = 16` (`RamBd`).

## The model (one corner, `RamTiming`)

* **Synchronous everything, on the rising edge of CLKARDCLK** (a binary clock, as in
  `SeqFlop`: **H_CK_BINARY**). At an edge `e` each live input pin is read over its own
  window `[e + lo, e + hi]` (`SeqFlop.ap`: its value if constant there, else `X`). One
  window for every address bit, one for WE, one for every DI bit (prjxray has one entry per
  bus; **H_BRAM_PINREF**: windows are at the BRAM pins).
* **Address decoder** (`sel`): the Kleene AND of the address literals, so word `w`'s
  wordline is `1` if the read address is exactly `w`, `0` if some *definite* bit disagrees,
  `X` if `w` is only consistent with it. **H_BRAM_DECODE_KLEENE**: a word whose address
  disagrees with a cleanly-sampled address bit is never selected, even during a violation of
  the other bits. (The whole-array-X alternative is strictly more pessimistic; this one is
  the Kleene-exact reading of an AND-of-literals decoder.)
* **Write** (`wnext`): word `w` bit `j` becomes `kmux (we ∧ sel w) (din j) (old)`: written
  if its effective enable is 1, unchanged if 0, `merge old din` if X. So a violation on
  WE/ADDR makes X only on the words of the address cube and only on the bits where old and
  new differ; a DI violation makes X only on that bit of the addressed word.
* **Read** (`kread`): the Kleene merge of the word bits over the address cube (the exact
  Kleene extension of the column mux).
* **Read disturb** (`rdis`): with `rdis = true`, a read with a non-definite address also
  merges every word of the cube with the value read (bitline sharing between several open
  wordlines). With `rdis = false` that is **H_BRAM_READ_NONDESTRUCTIVE**. Every theorem
  below holds for both settings unless it says otherwise.
* **Output latch, `DOA_REG = 0`** (`onext`): WRITE_FIRST: `kmux we din read`;
  READ_FIRST: `read` (old contents); NO_CHANGE: `kmux we old_out read`. The output keeps
  its old value up to `e + cqLo`, is `merge old new` in `(e + cqLo, e + cqHi]`, and the new
  value after `e + cqHi` (the CLK->DOADO band). An X there is NOT resolved to a binary
  value (unlike `SeqFlop.FlopRel`'s H_FF_RESOLVE): it stays X until the next edge, which
  is weaker than silicon and therefore sound.
* **Memory timing.** The array is a hidden state signal `m`; it takes its new value right
  after the edge, and the next edge reads it. **H_BRAM_PERIOD**: no minimum clock period or
  pulse width is modelled (prjxray-db has none for the BRAM); two edges are both trusted.
* **Power-up.** Before the first edge the array is `init` (`INIT_xx`) and DOADO is
  `initA` (`INIT_A`) (**H_GSR**, time 0 = end of configuration).

The relation is not vacuous: `ramSim` builds, for EVERY input, a memory and an output
satisfying it (`ramSim_rel`).

## Main theorems
* `kread_def`, `wnext_self`, `wnext_other`, `onext_wf_write`: on definite inputs the K3 RAM is the Boolean
  RAM; WRITE_FIRST returns the data written whatever the address.
* `wnext_sound`, `onext_sound`, `kread_mono`, `wnext_mono`, `onext_mono`: every Boolean
  completion of the sampled inputs gives a result covered by the K3 one (X is sound).
* `wnext_outside`: X containment in space: words outside the address cube never change.
* Timed (`RamRel`): `mem_write`, `mem_read_keeps`, `read_out`, `wf_read_during_write`,
  `rf_read_during_write`, `nc_keeps_out`, `write_then_read`, `power_up`,
  `x_outside_cube`, `x_flushed_by_read`, `x_flushed_by_write`, `di_violation_X`.

## What is NOT modelled
Port B (tied off in bd_mem), parity bits, cascade, ECC, FIFO mode, the output register
(`DOA_REG = 1`), ENARDEN/RSTRAM/REGCE (constants), the clock's runts or minimum
pulse width, the time a disturbed cell takes to resolve, rise/fall split (prjxray has none),
fast-corner windows (prjxray has only slow-corner TIMINGCHECKs), collisions with port B.
-/

namespace Formal.Core.Prims.Ram

open Formal.Core Formal.Core.K3 Formal.Core.Substrate Formal.Core.Prims.Seq

/-! ## 1. Words, addresses, the decoder -/

/-- A K3 data word. -/
abbrev KWord (n : Nat) := Fin n → K3
/-- A Boolean (word) address. -/
abbrev BAddr (aw : Nat) := Fin aw → Bool
/-- The array: one K3 word per Boolean address. -/
abbrev Mem (aw dw : Nat) := BAddr aw → KWord dw

/-- The sampled address is exactly `w`. -/
def IsAddr {aw : Nat} (a : Fin aw → K3) (w : BAddr aw) : Prop := ∀ i, a i = ofBool (w i)

instance {aw : Nat} (a : Fin aw → K3) (w : BAddr aw) : Decidable (IsAddr a w) :=
  inferInstanceAs (Decidable (∀ _ : Fin aw, _))

/-- The wordline of `w`: Kleene AND of the address literals. -/
def sel {aw : Nat} (a : Fin aw → K3) (w : BAddr aw) : K3 :=
  if IsAddr a w then one else if Consistent a w then X else zero

theorem isAddr_consistent {aw : Nat} {a : Fin aw → K3} {w : BAddr aw} (h : IsAddr a w) :
    Consistent a w := fun i => by rw [h i]; exact le_refl _

theorem isAddr_ofBoolVec {aw : Nat} {v w : BAddr aw} : IsAddr (ofBoolVec v) w ↔ w = v := by
  constructor
  · intro h; funext i; exact (ofBool_inj.mp (h i)).symm
  · intro h; subst h; intro i; rfl

theorem sel_self {aw : Nat} (v : BAddr aw) : sel (ofBoolVec v) v = one := by
  simp [sel, isAddr_ofBoolVec.2 rfl]

theorem sel_other {aw : Nat} {v w : BAddr aw} (h : w ≠ v) : sel (ofBoolVec v) w = zero := by
  have h1 : ¬ IsAddr (ofBoolVec v) w := fun h' => h (isAddr_ofBoolVec.1 h')
  have h2 : ¬ Consistent (ofBoolVec v) w := fun h' => h (consistent_ofBoolVec.1 h')
  simp [sel, h1, h2]

/-- Outside the address cube the wordline is 0. -/
theorem sel_not_consistent {aw : Nat} {a : Fin aw → K3} {w : BAddr aw} (h : ¬ Consistent a w) :
    sel a w = zero := by
  have h1 : ¬ IsAddr a w := fun h' => h (isAddr_consistent h')
  unfold sel; rw [if_neg h1, if_neg h]

/-- A definite address never gives an X wordline. -/
theorem sel_ne_X_of_def {aw : Nat} (v w : BAddr aw) : sel (ofBoolVec v) w ≠ X := by
  by_cases h : w = v
  · subst h; rw [sel_self]; decide
  · rw [sel_other h]; decide

/-- Refinement order on address vectors: `a'` refines `a` pointwise. -/
theorem consistent_of_le {aw : Nat} {a a' : Fin aw → K3} {w : BAddr aw} (h : VLe a a')
    (hc : Consistent a' w) : Consistent a w := fun i => K3.le_trans (h i) (hc i)

theorem isAddr_of_le {aw : Nat} {a a' : Fin aw → K3} {w : BAddr aw} (h : VLe a a')
    (hw : IsAddr a w) : IsAddr a' w := fun i => by
  have := h i; rw [hw i] at this; exact ofBool_le_iff.1 this

theorem sel_mono {aw : Nat} {a a' : Fin aw → K3} (h : VLe a a') (w : BAddr aw) :
    sel a w ⊑ sel a' w := by
  by_cases h1 : IsAddr a w
  · simp [sel, h1, isAddr_of_le h h1]; exact le_refl _
  · by_cases h2 : Consistent a w
    · simp only [sel, h1, h2, ite_false, ite_true]; exact X_le _
    · have h3 : ¬ Consistent a' w := fun h' => h2 (consistent_of_le h h')
      rw [sel_not_consistent h2, sel_not_consistent h3]; exact le_refl _

/-! ## 2. Read, write, output -/

/-- Kleene read of bit `j`: the common value of bit `j` over every word consistent with the
address, else `X`. -/
def kread {aw dw : Nat} (m : Mem aw dw) (a : Fin aw → K3) (j : Fin dw) : K3 :=
  if ∀ w, Consistent a w → m w j = one then one
  else if ∀ w, Consistent a w → m w j = zero then zero else X

theorem kread_def {aw dw : Nat} (m : Mem aw dw) (v : BAddr aw) (j : Fin dw) :
    kread m (ofBoolVec v) j = m v j := by
  have hc : ∀ w, Consistent (ofBoolVec v) w ↔ w = v := fun w => consistent_ofBoolVec
  unfold kread
  cases hm : m v j with
  | one =>
    have h1 : ∀ w, Consistent (ofBoolVec v) w → m w j = one := fun w hw => by
      rw [(hc w).1 hw]; exact hm
    rw [if_pos h1]
  | zero =>
    have h1 : ¬ ∀ w, Consistent (ofBoolVec v) w → m w j = one := fun h => by
      have := h v ((hc v).2 rfl); rw [hm] at this; exact absurd this (by decide)
    have h2 : ∀ w, Consistent (ofBoolVec v) w → m w j = zero := fun w hw => by
      rw [(hc w).1 hw]; exact hm
    rw [if_neg h1, if_pos h2]
  | X =>
    have h1 : ¬ ∀ w, Consistent (ofBoolVec v) w → m w j = one := fun h => by
      have := h v ((hc v).2 rfl); rw [hm] at this; exact absurd this (by decide)
    have h2 : ¬ ∀ w, Consistent (ofBoolVec v) w → m w j = zero := fun h => by
      have := h v ((hc v).2 rfl); rw [hm] at this; exact absurd this (by decide)
    rw [if_neg h1, if_neg h2]

/-- Pointwise refinement of arrays. -/
def MLe {aw dw : Nat} (m m' : Mem aw dw) : Prop := ∀ w j, m w j ⊑ m' w j

theorem kread_mono {aw dw : Nat} {m m' : Mem aw dw} {a a' : Fin aw → K3} (hm : MLe m m')
    (ha : VLe a a') (j : Fin dw) : kread m a j ⊑ kread m' a' j := by
  unfold kread
  by_cases h1 : ∀ w, Consistent a w → m w j = one
  · rw [if_pos h1, if_pos]
    · exact le_refl _
    · intro w hw
      have := hm w j; rw [h1 w (consistent_of_le ha hw)] at this; exact (ofBool_le_iff (b := true)).1 this
  · rw [if_neg h1]
    by_cases h2 : ∀ w, Consistent a w → m w j = zero
    · rw [if_pos h2]
      have h2' : ∀ w, Consistent a' w → m' w j = zero := fun w hw => by
        have := hm w j; rw [h2 w (consistent_of_le ha hw)] at this
        exact (ofBool_le_iff (b := false)).1 this
      have h1' : ¬ ∀ w, Consistent a' w → m' w j = one := fun h => by
        have hp := consistent_pick a'
        have := (h _ hp).symm.trans (h2' _ hp); exact absurd this (by decide)
      rw [if_neg h1', if_pos h2']; exact le_refl _
    · rw [if_neg h2]; exact X_le _

/-- The write: word `w` bit `j`. `rdis` adds read disturb (see the header). -/
def wnext {aw dw : Nat} (rdis : Bool) (we : K3) (a : Fin aw → K3) (din : KWord dw)
    (m : Mem aw dw) : Mem aw dw := fun w j =>
  kmux (K3.and we (sel a w)) (din j)
    (if rdis = true ∧ sel a w = X then merge (m w j) (kread m a j) else m w j)

/-- Write modes of port A (`WRITE_MODE_A`). bd_mem uses `writeFirst`. -/
inductive WMode where
  | writeFirst
  | readFirst
  | noChange
  deriving DecidableEq, Repr

/-- The new DOADO value (`DOA_REG = 0`), from the sampled inputs, the old array and the
old output. -/
def onext {aw dw : Nat} (md : WMode) (we : K3) (a : Fin aw → K3) (din : KWord dw)
    (m : Mem aw dw) (dold : KWord dw) : KWord dw := fun j =>
  match md with
  | .writeFirst => kmux we (din j) (kread m a j)
  | .readFirst => kread m a j
  | .noChange => kmux we (dold j) (kread m a j)

/-! ## 3. Definite inputs: the Boolean RAM -/

/-- **WRITE_FIRST read-during-write** (combinational level): with WE = 1 the output is the
data written, whatever the address (even an X one). -/
theorem onext_wf_write {aw dw : Nat} (a : Fin aw → K3) (din : KWord dw) (m : Mem aw dw)
    (dold : KWord dw) : onext .writeFirst one a din m dold = din := by
  funext j; rfl

theorem onext_rf {aw dw : Nat} (we : K3) (v : BAddr aw) (din : KWord dw) (m : Mem aw dw)
    (dold : KWord dw) : onext .readFirst we (ofBoolVec v) din m dold = m v := by
  funext j; simp [onext, kread_def]

theorem onext_read {aw dw : Nat} (md : WMode) (v : BAddr aw) (din : KWord dw) (m : Mem aw dw)
    (dold : KWord dw) : onext md zero (ofBoolVec v) din m dold = m v := by
  funext j; cases md <;> simp [onext, kread_def]

theorem onext_nc_write {aw dw : Nat} (a : Fin aw → K3) (din : KWord dw) (m : Mem aw dw)
    (dold : KWord dw) : onext .noChange one a din m dold = dold := by
  funext j; rfl

/-- The write with definite WE and address, at the addressed word: `din` if WE = 1. -/
theorem wnext_self {aw dw : Nat} (rdis we : Bool) (v : BAddr aw) (din : KWord dw)
    (m : Mem aw dw) : wnext rdis (ofBool we) (ofBoolVec v) din m v = if we then din else m v := by
  funext j
  have hX : ¬ (rdis = true ∧ sel (ofBoolVec v) v = X) := fun h => sel_ne_X_of_def v v h.2
  unfold wnext; rw [if_neg hX, sel_self]
  cases we <;> rfl

/-- ... and at every other word: unchanged. -/
theorem wnext_other {aw dw : Nat} (rdis : Bool) (we : Bool) {v w : BAddr aw} (din : KWord dw)
    (m : Mem aw dw) (hw : w ≠ v) : wnext rdis (ofBool we) (ofBoolVec v) din m w = m w := by
  funext j
  have hX : ¬ (rdis = true ∧ sel (ofBoolVec v) w = X) := fun h => sel_ne_X_of_def v w h.2
  unfold wnext; rw [if_neg hX, sel_other hw]
  cases we <;> rfl

/-- WE = 0 (definite) with a definite address leaves the array unchanged. -/
theorem wnext_read {aw dw : Nat} (rdis : Bool) (v : BAddr aw) (din : KWord dw) (m : Mem aw dw) :
    wnext rdis zero (ofBoolVec v) din m = m := by
  funext w
  by_cases hw : w = v
  · subst hw; have := wnext_self rdis false w din m; simpa using this
  · exact wnext_other rdis false din m hw

/-- WE = 0 (definite) and no read disturb: the array is unchanged whatever the address. -/
theorem wnext_read_nd {aw dw : Nat} (a : Fin aw → K3) (din : KWord dw) (m : Mem aw dw) :
    wnext false zero a din m = m := by
  funext w j
  have hX : ¬ (false = true ∧ sel a w = X) := fun h => absurd h.1 (by decide)
  unfold wnext; rw [if_neg hX]; rfl

/-- **X containment in space**: a word outside the address cube never changes, whatever WE
and DI were (violated or not), with or without read disturb. -/
theorem wnext_outside {aw dw : Nat} (rdis : Bool) (we : K3) {a : Fin aw → K3} (din : KWord dw)
    (m : Mem aw dw) {w : BAddr aw} (h : ¬ Consistent a w) : wnext rdis we a din m w = m w := by
  funext j
  have hs := sel_not_consistent (w := w) h
  have hX : ¬ (rdis = true ∧ sel a w = X) := fun h' => by rw [hs] at h'; exact absurd h'.2 (by decide)
  unfold wnext; rw [if_neg hX, hs]
  cases we <;> rfl

/-! ## 4. Soundness: monotone in the information order -/

theorem and_mono' {a b a' b' : K3} (h1 : a ⊑ a') (h2 : b ⊑ b') : K3.and a b ⊑ K3.and a' b' :=
  K3.and_mono h1 h2

theorem wnext_mono {aw dw : Nat} (rdis : Bool) {we we' : K3} {a a' : Fin aw → K3}
    {din din' : KWord dw} {m m' : Mem aw dw} (hwe : we ⊑ we') (ha : VLe a a')
    (hd : VLe din din') (hm : MLe m m') : MLe (wnext rdis we a din m) (wnext rdis we' a' din' m') := by
  intro w j
  unfold wnext
  apply kmux_mono (K3.and_mono hwe (sel_mono ha w)) (hd j)
  have hs := sel_mono ha w
  by_cases h1 : rdis = true ∧ sel a w = X
  · rw [if_pos h1]
    by_cases h2 : rdis = true ∧ sel a' w = X
    · rw [if_pos h2]; exact merge_mono (hm w j) (kread_mono hm ha j)
    · rw [if_neg h2]; exact K3.le_trans (merge_le_left _ _) (hm w j)
  · have h2 : ¬ (rdis = true ∧ sel a' w = X) := by
      rintro ⟨hr, hx⟩
      rw [hx] at hs
      rcases hs with hs | hs
      · exact h1 ⟨hr, hs⟩
      · exact h1 ⟨hr, hs⟩
    rw [if_neg h1, if_neg h2]; exact hm w j

theorem onext_mono {aw dw : Nat} (md : WMode) {we we' : K3} {a a' : Fin aw → K3}
    {din din' : KWord dw} {m m' : Mem aw dw} {dold dold' : KWord dw} (hwe : we ⊑ we')
    (ha : VLe a a') (hd : VLe din din') (hm : MLe m m') (ho : VLe dold dold') :
    VLe (onext md we a din m dold) (onext md we' a' din' m' dold') := by
  intro j
  cases md
  · exact kmux_mono hwe (hd j) (kread_mono hm ha j)
  · exact kread_mono hm ha j
  · exact kmux_mono hwe (ho j) (kread_mono hm ha j)

/-- Boolean arrays as K3 arrays. -/
def ofBMem {aw dw : Nat} (m : BAddr aw → Fin dw → Bool) : Mem aw dw := fun w j => ofBool (m w j)

/-- The Boolean RAM write. -/
def bwnext {aw dw : Nat} (we : Bool) (v : BAddr aw) (din : Fin dw → Bool)
    (m : BAddr aw → Fin dw → Bool) : BAddr aw → Fin dw → Bool :=
  fun w j => if we = true ∧ IsAddr (ofBoolVec v) w then din j else m w j

/-- **Soundness of the write**: for every Boolean completion of the sampled WE, address,
data and array, the Boolean write's result is covered by the K3 one. -/
theorem wnext_sound {aw dw : Nat} (rdis : Bool) {we : K3} {a : Fin aw → K3} {din : KWord dw}
    {m : Mem aw dw} {bwe : Bool} {bv : BAddr aw} {bdin : Fin dw → Bool}
    {bm : BAddr aw → Fin dw → Bool} (hwe : we ⊑ ofBool bwe) (ha : Consistent a bv)
    (hd : Consistent din bdin) (hm : MLe m (ofBMem bm)) :
    MLe (wnext rdis we a din m) (ofBMem (bwnext bwe bv bdin bm)) := by
  intro w j
  have h : wnext rdis we a din m w j ⊑
      wnext rdis (ofBool bwe) (ofBoolVec bv) (ofBoolVec bdin) (ofBMem bm) w j :=
    wnext_mono rdis hwe ha hd hm w j
  refine K3.le_trans h ?_
  by_cases hw : w = bv
  · subst hw
    rw [wnext_self]
    have hi : IsAddr (ofBoolVec w) w := isAddr_ofBoolVec.2 rfl
    cases bwe <;> simp [ofBMem, bwnext, hi, ofBoolVec] <;> exact le_refl _
  · rw [wnext_other rdis bwe _ _ hw]
    have hi : ¬ IsAddr (ofBoolVec bv) w := fun h => hw (isAddr_ofBoolVec.1 h)
    simp [ofBMem, bwnext, hi] ; exact le_refl _

/-- The Boolean DOADO. -/
def bonext {aw dw : Nat} (md : WMode) (we : Bool) (v : BAddr aw) (din : Fin dw → Bool)
    (m : BAddr aw → Fin dw → Bool) (dold : Fin dw → Bool) : Fin dw → Bool := fun j =>
  match md with
  | .writeFirst => if we then din j else m v j
  | .readFirst => m v j
  | .noChange => if we then dold j else m v j

/-- **Soundness of the output**: likewise for DOADO. -/
theorem onext_sound {aw dw : Nat} (md : WMode) {we : K3} {a : Fin aw → K3} {din : KWord dw}
    {m : Mem aw dw} {dold : KWord dw} {bwe : Bool} {bv : BAddr aw} {bdin : Fin dw → Bool}
    {bm : BAddr aw → Fin dw → Bool} {bdold : Fin dw → Bool} (hwe : we ⊑ ofBool bwe)
    (ha : Consistent a bv) (hd : Consistent din bdin) (hm : MLe m (ofBMem bm))
    (ho : Consistent dold bdold) :
    Consistent (onext md we a din m dold) (bonext md bwe bv bdin bm bdold) := by
  intro j
  have h : onext md we a din m dold j ⊑
      onext md (ofBool bwe) (ofBoolVec bv) (ofBoolVec bdin) (ofBMem bm) (ofBoolVec bdold) j :=
    onext_mono md hwe ha hd hm ho j
  have e : onext md (ofBool bwe) (ofBoolVec bv) (ofBoolVec bdin) (ofBMem bm) (ofBoolVec bdold) j
      = ofBool (bonext md bwe bv bdin bm bdold j) := by
    cases md <;> cases bwe <;> simp only [onext, bonext, kread_def] <;> rfl
  rw [e] at h; exact h

/-! ## 5. Timing parameters and the trace relation -/

/-- The timing of port A at ONE corner, integer ps, at the BRAM pins (**H_BRAM_PINREF**).
Window offsets are relative to the CLKARDCLK rising edge: `lo = -setup`, `hi = hold`. -/
structure RamTiming where
  /-- CLKARDCLK -> DOADO band (`DOA_REG = 0`). -/
  cqLo : Nat
  cqHi : Nat
  /-- ADDRARDADDR window. -/
  aLo : Int
  aHi : Int
  /-- WEA window. -/
  weLo : Int
  weHi : Int
  /-- DIADI window (depends on `WRITE_MODE_A` in prjxray). -/
  dLo : Int
  dHi : Int
  deriving Repr, DecidableEq

/-- Well-formed: every window nonempty and the CK->DO band ordered. -/
def RamTiming.Ok (T : RamTiming) : Prop :=
  T.aLo ≤ T.aHi ∧ T.weLo ≤ T.weHi ∧ T.dLo ≤ T.dHi ∧ T.cqLo ≤ T.cqHi

section Timed
variable {aw dw : Nat} (T : RamTiming)

/-- The address read over its window at the edge `e`. -/
def rA (a : Fin aw → KSig) (e : Nat) : Fin aw → K3 := fun i => ap (a i) e T.aLo T.aHi
/-- WE read over its window. -/
def rWE (we : KSig) (e : Nat) : K3 := ap we e T.weLo T.weHi
/-- DI read over its window. -/
def rD (din : Fin dw → KSig) (e : Nat) : KWord dw := fun j => ap (din j) e T.dLo T.dHi

/-- **The RAM port.** `ck` = CLKARDCLK, `a` = ADDRARDADDR (word bits), `we` = WEA,
`din` = DIADI, `m` = the array (a hidden state signal), `dout` = DOADO. -/
structure RamRel (md : WMode) (rdis : Bool) (init : Mem aw dw) (initA : KWord dw) (ck : Sig)
    (a : Fin aw → KSig) (we : KSig) (din : Fin dw → KSig) (m : Nat → Mem aw dw)
    (dout : Fin dw → KSig) : Prop where
  minit : ∀ t, (∀ u, u < t → ¬ rises ck u) → m t = init
  mstep : ∀ e t, rises ck e → e < t → NoRise ck e t →
    m t = wnext rdis (rWE T we e) (rA T a e) (rD T din e) (m e)
  oinit : ∀ t, (∀ u, u < t → ¬ rises ck u) → ∀ j, dout j t = initA j
  ohold : ∀ e t, rises ck e → e < t → NoRise ck e t → t ≤ e + T.cqLo → ∀ j, dout j t = dout j e
  oband : ∀ e t, rises ck e → e < t → NoRise ck e t → e + T.cqLo < t → t ≤ e + T.cqHi → ∀ j,
    dout j t = merge (dout j e)
      (onext md (rWE T we e) (rA T a e) (rD T din e) (m e) (fun i => dout i e) j)
  osettle : ∀ e t, rises ck e → e < t → NoRise ck e t → e + T.cqHi < t → ∀ j,
    dout j t = onext md (rWE T we e) (rA T a e) (rD T din e) (m e) (fun i => dout i e) j

/-- Address `v` held on its window at `e`. -/
def AddrOn (a : Fin aw → KSig) (v : BAddr aw) (e : Nat) : Prop :=
  ∀ i, EqOn (a i) (ofBool (v i)) (wpt e T.aLo) (wpt e T.aHi)
/-- WE = `b` on its window. -/
def WeOn (we : KSig) (b : Bool) (e : Nat) : Prop := EqOn we (ofBool b) (wpt e T.weLo) (wpt e T.weHi)
/-- DI = `d` on its window. -/
def DataOn (din : Fin dw → KSig) (d : Fin dw → Bool) (e : Nat) : Prop :=
  ∀ j, EqOn (din j) (ofBool (d j)) (wpt e T.dLo) (wpt e T.dHi)

variable {T}

theorem rA_of {a : Fin aw → KSig} {v : BAddr aw} {e : Nat} (hok : T.Ok) (h : AddrOn T a v e) :
    rA T a e = ofBoolVec v := funext fun i => winVal_const (wpt_le hok.1) (h i)
theorem rWE_of {we : KSig} {b : Bool} {e : Nat} (hok : T.Ok) (h : WeOn T we b e) :
    rWE T we e = ofBool b := winVal_const (wpt_le hok.2.1) h
theorem rD_of {din : Fin dw → KSig} {d : Fin dw → Bool} {e : Nat} (hok : T.Ok)
    (h : DataOn T din d e) : rD T din e = ofBoolVec d :=
  funext fun j => winVal_const (wpt_le hok.2.2.1) (h j)

variable {md : WMode} {rdis : Bool} {init : Mem aw dw} {initA : KWord dw} {ck : Sig}
  {a : Fin aw → KSig} {we : KSig} {din : Fin dw → KSig} {m : Nat → Mem aw dw}
  {dout : Fin dw → KSig}

/-! ## 6. Correct write and read when the windows are respected -/

/-- **Write.** A clean write of `d` to `v` at `e`: until the next edge, word `v` is `d` and
every other word keeps its contents. -/
theorem mem_write (hok : T.Ok) (h : RamRel T md rdis init initA ck a we din m dout)
    {e t : Nat} {v : BAddr aw} {d : Fin dw → Bool} (he : rises ck e) (het : e < t)
    (hn : NoRise ck e t) (hA : AddrOn T a v e) (hW : WeOn T we true e) (hD : DataOn T din d e) :
    m t v = ofBoolVec d ∧ ∀ w, w ≠ v → m t w = m e w := by
  rw [h.mstep e t he het hn, rA_of hok hA, rWE_of hok hW, rD_of hok hD]
  exact ⟨by rw [wnext_self]; try rfl, fun w hw => wnext_other rdis true _ _ hw⟩

/-- **A clean read does not change the array.** -/
theorem mem_read_keeps (hok : T.Ok) (h : RamRel T md rdis init initA ck a we din m dout)
    {e t : Nat} {v : BAddr aw} (he : rises ck e) (het : e < t) (hn : NoRise ck e t)
    (hA : AddrOn T a v e) (hW : WeOn T we false e) : m t = m e := by
  rw [h.mstep e t he het hn, rA_of hok hA, rWE_of hok hW]
  exact wnext_read rdis v _ _

/-- Without read disturb, WE = 0 alone keeps the array (whatever the address does). -/
theorem mem_read_keeps_nd (hok : T.Ok) (h : RamRel T md false init initA ck a we din m dout)
    {e t : Nat} (he : rises ck e) (het : e < t) (hn : NoRise ck e t) (hW : WeOn T we false e) :
    m t = m e := by
  rw [h.mstep e t he het hn, rWE_of hok hW]
  exact wnext_read_nd _ _ _

/-- **Read.** A clean read of `v` at `e` (any write mode): after `cqHi`, until the next
edge, DOADO is the word stored at `v` just before the edge. -/
theorem read_out (hok : T.Ok) (h : RamRel T md rdis init initA ck a we din m dout)
    {e t : Nat} {v : BAddr aw} (he : rises ck e) (het : e < t) (hn : NoRise ck e t)
    (hA : AddrOn T a v e) (hW : WeOn T we false e) (ht : e + T.cqHi < t) (j : Fin dw) :
    dout j t = m e v j := by
  rw [h.osettle e t he het hn ht j, rA_of hok hA, rWE_of hok hW]
  exact congrFun (onext_read md v _ _ _) j

/-- **WRITE_FIRST read-during-write returns the new data.** WE = 1 and DI = `d` on their
windows: after `cqHi` DOADO = `d`. No hypothesis on the address at all (DOADO follows DI
in WRITE_FIRST even if the address window is violated). -/
theorem wf_read_during_write (hok : T.Ok)
    (h : RamRel T .writeFirst rdis init initA ck a we din m dout)
    {e t : Nat} {d : Fin dw → Bool} (he : rises ck e) (het : e < t) (hn : NoRise ck e t)
    (hW : WeOn T we true e) (hD : DataOn T din d e) (ht : e + T.cqHi < t) (j : Fin dw) :
    dout j t = ofBool (d j) := by
  rw [h.osettle e t he het hn ht j, rWE_of hok hW, rD_of hok hD]; rfl

/-- READ_FIRST read-during-write returns the OLD contents. -/
theorem rf_read_during_write (hok : T.Ok)
    (h : RamRel T .readFirst rdis init initA ck a we din m dout)
    {e t : Nat} {v : BAddr aw} (he : rises ck e) (het : e < t) (hn : NoRise ck e t)
    (hA : AddrOn T a v e) (ht : e + T.cqHi < t) (j : Fin dw) : dout j t = m e v j := by
  rw [h.osettle e t he het hn ht j, rA_of hok hA]
  exact congrFun (onext_rf _ v _ _ _) j

/-- NO_CHANGE: a clean write leaves DOADO as it was, at every time until the next edge. -/
theorem nc_keeps_out (hok : T.Ok) (h : RamRel T .noChange rdis init initA ck a we din m dout)
    {e t : Nat} (he : rises ck e) (het : e < t) (hn : NoRise ck e t) (hW : WeOn T we true e)
    (j : Fin dw) : dout j t = dout j e := by
  by_cases h1 : t ≤ e + T.cqLo
  · exact h.ohold e t he het hn h1 j
  have hnx : onext .noChange (rWE T we e) (rA T a e) (rD T din e) (m e) (fun i => dout i e) j
      = dout j e := by rw [rWE_of hok hW]; rfl
  by_cases h2 : t ≤ e + T.cqHi
  · rw [h.oband e t he het hn (by omega) h2 j, hnx, merge_self]
  · rw [h.osettle e t he het hn (by omega) j, hnx]

/-- **Write then read** (consecutive edges `e1 < e2`, both clean, same address): DOADO after
`e2 + cqHi` is the data written at `e1`. Holds in every write mode. -/
theorem write_then_read (hok : T.Ok) (h : RamRel T md rdis init initA ck a we din m dout)
    {e1 e2 t : Nat} {v : BAddr aw} {d : Fin dw → Bool} (he1 : rises ck e1) (he2 : rises ck e2)
    (h12 : e1 < e2) (hn1 : NoRise ck e1 e2) (hn2 : NoRise ck e2 t)
    (hA1 : AddrOn T a v e1) (hW1 : WeOn T we true e1) (hD1 : DataOn T din d e1)
    (hA2 : AddrOn T a v e2) (hW2 : WeOn T we false e2) (ht : e2 + T.cqHi < t) (j : Fin dw) :
    dout j t = ofBool (d j) := by
  rw [read_out hok h he2 (by omega) hn2 hA2 hW2 ht j, (mem_write hok h he1 h12 hn1 hA1 hW1 hD1).1]
  try rfl

/-- **Power-up**: before the first edge the array is INIT and DOADO is INIT_A. -/
theorem power_up (h : RamRel T md rdis init initA ck a we din m dout) {t : Nat}
    (hno : ∀ u, u < t → ¬ rises ck u) : m t = init ∧ ∀ j, dout j t = initA j :=
  ⟨h.minit t hno, h.oinit t hno⟩

/-! ## 7. X containment -/

/-- **X stays inside the address cube.** At ANY edge (violations, X on WE/ADDR/DI, read
disturb on or off), every word whose address is not consistent with the sampled address
keeps its contents. In particular a clean address (`AddrOn`) protects every other word. -/
theorem x_outside_cube (h : RamRel T md rdis init initA ck a we din m dout) {e t : Nat}
    {w : BAddr aw} (he : rises ck e) (het : e < t) (hn : NoRise ck e t)
    (hw : ¬ Consistent (rA T a e) w) : m t w = m e w := by
  rw [h.mstep e t he het hn]; exact wnext_outside rdis _ _ _ hw

/-- A clean address `v` makes every other word unreachable at that edge, whatever WE and DI
do (only `v` can be written, possibly with X). -/
theorem x_only_addressed (hok : T.Ok) (h : RamRel T md rdis init initA ck a we din m dout)
    {e t : Nat} {v w : BAddr aw} (he : rises ck e) (het : e < t) (hn : NoRise ck e t)
    (hA : AddrOn T a v e) (hw : w ≠ v) : m t w = m e w := by
  refine x_outside_cube h he het hn ?_
  rw [rA_of hok hA]; exact fun hc => hw (consistent_ofBoolVec.1 hc)

/-- **X in DOADO does not stick**: a clean read of a definite word gives a definite DOADO
after `cqHi`, whatever DOADO was before (X included). -/
theorem x_flushed_by_read (hok : T.Ok) (h : RamRel T md rdis init initA ck a we din m dout)
    {e t : Nat} {v : BAddr aw} {c : Fin dw → Bool} (he : rises ck e) (het : e < t)
    (hn : NoRise ck e t) (hA : AddrOn T a v e) (hW : WeOn T we false e)
    (hc : m e v = ofBoolVec c) (ht : e + T.cqHi < t) (j : Fin dw) : dout j t = ofBool (c j) := by
  rw [read_out hok h he het hn hA hW ht j, hc]; try rfl

/-- **X in the array does not stick**: a clean write makes the word definite. -/
theorem x_flushed_by_write (hok : T.Ok) (h : RamRel T md rdis init initA ck a we din m dout)
    {e t : Nat} {v : BAddr aw} {d : Fin dw → Bool} (he : rises ck e) (het : e < t)
    (hn : NoRise ck e t) (hA : AddrOn T a v e) (hW : WeOn T we true e)
    (hD : DataOn T din d e) (j : Fin dw) : m t v j ≠ X := by
  rw [(mem_write hok h he het hn hA hW hD).1]; exact ofBool_ne_X _

/-- **A DI violation produces X** (the model is not optimistic): clean address and WE = 1,
but DI bit `j` takes two values inside its window. Then the stored bit is X, and in
WRITE_FIRST so is DOADO bit `j` after `cqHi`. -/
theorem di_violation_X (hok : T.Ok) (h : RamRel T .writeFirst rdis init initA ck a we din m dout)
    {e t s1 s2 : Nat} {v : BAddr aw} {j : Fin dw} (he : rises ck e) (het : e < t)
    (hn : NoRise ck e t) (hA : AddrOn T a v e) (hW : WeOn T we true e)
    (h1a : wpt e T.dLo ≤ s1) (h1b : s1 ≤ wpt e T.dHi) (h2a : wpt e T.dLo ≤ s2)
    (h2b : s2 ≤ wpt e T.dHi) (hne : din j s1 ≠ din j s2) :
    m t v j = X ∧ (e + T.cqHi < t → dout j t = X) := by
  have hx : rD T din e j = X := winVal_X_of_ne h1a h1b h2a h2b hne
  refine ⟨?_, fun ht => ?_⟩
  · rw [h.mstep e t he het hn, rA_of hok hA, rWE_of hok hW]
    have := congrFun (wnext_self rdis true v (rD T din e) (m e)) j
    simp only [ite_true] at this; rw [this, hx]
  · rw [h.osettle e t he het hn ht j, rWE_of hok hW]; exact hx

/-- **A WE violation produces X where old and new differ**: clean address and data, WE
changes inside its window, the stored bit differed from the data: the stored bit is X. -/
theorem we_violation_X (hok : T.Ok) (h : RamRel T md rdis init initA ck a we din m dout)
    {e t s1 s2 : Nat} {v : BAddr aw} {d : Fin dw → Bool} {j : Fin dw} (he : rises ck e)
    (het : e < t) (hn : NoRise ck e t) (hA : AddrOn T a v e) (hD : DataOn T din d e)
    (h1a : wpt e T.weLo ≤ s1) (h1b : s1 ≤ wpt e T.weHi) (h2a : wpt e T.weLo ≤ s2)
    (h2b : s2 ≤ wpt e T.weHi) (hne : we s1 ≠ we s2) (hold : m e v j ≠ ofBool (d j)) :
    m t v j = X := by
  have hx : rWE T we e = X := winVal_X_of_ne h1a h1b h2a h2b hne
  rw [h.mstep e t he het hn, rA_of hok hA, rD_of hok hD, hx]
  have hX : ¬ (rdis = true ∧ sel (ofBoolVec v) v = X) := fun h' => sel_ne_X_of_def v v h'.2
  unfold wnext; rw [if_neg hX, sel_self]
  show merge (ofBool (d j)) (m e v j) = X
  unfold merge; rw [if_neg (Ne.symm hold)]

end Timed

/-! ## 8. Non-vacuity: every input has a memory and an output satisfying the relation -/

section Sim
variable {aw dw : Nat} (T : RamTiming)

/-- The canonical array trace. -/
def simM (rdis : Bool) (init : Mem aw dw) (ck : Sig) (a : Fin aw → KSig) (we : KSig)
    (din : Fin dw → KSig) (t : Nat) : Mem aw dw :=
  match lastRise ck t with
  | none => init
  | some ⟨e, _⟩ => wnext rdis (rWE T we e) (rA T a e) (rD T din e) (simM rdis init ck a we din e)
termination_by t

/-- The canonical DOADO trace. -/
def simO (md : WMode) (rdis : Bool) (init : Mem aw dw) (initA : KWord dw) (ck : Sig)
    (a : Fin aw → KSig) (we : KSig) (din : Fin dw → KSig) (t : Nat) : KWord dw :=
  match lastRise ck t with
  | none => initA
  | some ⟨e, _⟩ =>
    if t ≤ e + T.cqLo then simO md rdis init initA ck a we din e
    else if t ≤ e + T.cqHi then fun j => merge (simO md rdis init initA ck a we din e j)
      (onext md (rWE T we e) (rA T a e) (rD T din e) (simM T rdis init ck a we din e)
        (simO md rdis init initA ck a we din e) j)
    else onext md (rWE T we e) (rA T a e) (rD T din e) (simM T rdis init ck a we din e)
        (simO md rdis init initA ck a we din e)
termination_by t

theorem simM_none {rdis : Bool} {init : Mem aw dw} {ck : Sig} {a : Fin aw → KSig} {we : KSig}
    {din : Fin dw → KSig} {t : Nat} (hno : ∀ u, u < t → ¬ rises ck u) :
    simM T rdis init ck a we din t = init := by
  rw [simM]; simp only [lastRise_none hno]

theorem simM_some {rdis : Bool} {init : Mem aw dw} {ck : Sig} {a : Fin aw → KSig} {we : KSig}
    {din : Fin dw → KSig} {e t : Nat} (he : rises ck e) (het : e < t) (hn : NoRise ck e t) :
    simM T rdis init ck a we din t =
      wnext rdis (rWE T we e) (rA T a e) (rD T din e) (simM T rdis init ck a we din e) := by
  obtain ⟨_, hl⟩ := lastRise_some he het hn
  rw [simM]; simp only [hl]

theorem simO_none {md : WMode} {rdis : Bool} {init : Mem aw dw} {initA : KWord dw} {ck : Sig}
    {a : Fin aw → KSig} {we : KSig} {din : Fin dw → KSig} {t : Nat}
    (hno : ∀ u, u < t → ¬ rises ck u) : simO T md rdis init initA ck a we din t = initA := by
  rw [simO]; simp only [lastRise_none hno]

theorem simO_some {md : WMode} {rdis : Bool} {init : Mem aw dw} {initA : KWord dw} {ck : Sig}
    {a : Fin aw → KSig} {we : KSig} {din : Fin dw → KSig} {e t : Nat} (he : rises ck e)
    (het : e < t) (hn : NoRise ck e t) :
    simO T md rdis init initA ck a we din t =
      (if t ≤ e + T.cqLo then simO T md rdis init initA ck a we din e
       else if t ≤ e + T.cqHi then fun j => merge (simO T md rdis init initA ck a we din e j)
         (onext md (rWE T we e) (rA T a e) (rD T din e) (simM T rdis init ck a we din e)
           (simO T md rdis init initA ck a we din e) j)
       else onext md (rWE T we e) (rA T a e) (rD T din e) (simM T rdis init ck a we din e)
           (simO T md rdis init initA ck a we din e)) := by
  obtain ⟨_, hl⟩ := lastRise_some he het hn
  rw [simO]; simp only [hl]

/-- **Non-vacuity**: the canonical traces satisfy `RamRel`, for every input, every write
mode, both read-disturb settings, and every timing with an ordered CK->DO band. -/
theorem ramSim_rel (md : WMode) (rdis : Bool) (init : Mem aw dw) (initA : KWord dw) (ck : Sig)
    (a : Fin aw → KSig) (we : KSig) (din : Fin dw → KSig) (hcq : T.cqLo ≤ T.cqHi) :
    RamRel T md rdis init initA ck a we din (simM T rdis init ck a we din)
      (fun j t => simO T md rdis init initA ck a we din t j) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro t hno; exact simM_none T hno
  · intro e t he het hn; exact simM_some T he het hn
  · intro t hno j; rw [simO_none T hno]
  · intro e t he het hn h1 j; rw [simO_some T he het hn, if_pos h1]
  · intro e t he het hn h1 h2 j
    rw [simO_some T he het hn, if_neg (show ¬ t ≤ e + T.cqLo by omega), if_pos h2]
  · intro e t he het hn h1 j
    rw [simO_some T he het hn, if_neg (show ¬ t ≤ e + T.cqLo by omega),
      if_neg (show ¬ t ≤ e + T.cqHi by omega)]

theorem ramRel_inhabited (md : WMode) (rdis : Bool) (init : Mem aw dw) (initA : KWord dw)
    (ck : Sig) (a : Fin aw → KSig) (we : KSig) (din : Fin dw → KSig) (hcq : T.cqLo ≤ T.cqHi) :
    ∃ m dout, RamRel T md rdis init initA ck a we din m dout :=
  ⟨_, _, ramSim_rel T md rdis init initA ck a we din hcq⟩

end Sim

end Formal.Core.Prims.Ram
