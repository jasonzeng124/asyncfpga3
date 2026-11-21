import Lean.Data.Json
import Formal.Core.XAudit.Parse
import Formal.Core.XAudit.Events2Design
import Formal.Core.XAudit.Events2Strict

/-!
# `xevents2` (strict) — Events2Main with the own-feedback race checked STRICTLY

Contradiction X2 (`formal/notes/A-contradictions.md`). This file is a copy of
`Events2Main.lean` with exactly these changes: the namespace, the import of
`Events2Strict`, the verdict reads `BackStrict` (margin >= 1 step) instead of
`Back` (margin >= 0), the report labels, and `sound_strict` below. A zero
margin now prints NOT PROVED: at equality the feedback and the neighbour's
answer arrive in the same step, which is safe only under H_ATOMIC_LUT
(`Events2Strict.cx_unsafe`). `BackStrict` implies `Back`
(`Events2Strict.BackStrict.back`), so every CLEAN verdict is still an
instance of `sound`; with `PinSkew 1` it is also an instance of the per-pin
theorem `Events2Strict.safe_strict`.

The original header follows.

# `xevents2` — the generalised counter domain (Events2) on a parsed netlist (executable main)

    xevents2 NETLIST.json [--top T] [--bands BANDS.json] [--env LO:HI] [--rst-ps R]

Probe A-events3 (task 2), on top of A-events2. The domain is `Events2`: open
nets (the environment is a channel), n-input C-elements (`bd_c2*`, `bd_c3`,
`bd_c4`, recognised by their INIT through `InitOK`), pins reached through
chains of 1-input gates (routes, `bd_delay` LUT1 buffers, inverters), and the
period bounds of `Events2Time` from kernel-style certificates.

## What is PROVED here

`sound`: for a design `d`, a list `env` of environment gates, a network
`net`, a stage map `sm` and back walks `back`, if `Recog2 (close d env) net
sm`, `Back sm.bands back` and every environment gate is a 1-input buffer or
inverter (`EnvOK`), then for EVERY behaviour of the parsed netlist (every
gate and route delay in its band, any power-up, reset released once at
`T`) in which every input port read by the control behaves as its
environment gate says (a transport channel from the stage that reads it,
in any sub-band of `[g.lo, g.hi]`), there is one count `M` with
* every C-element output `= ph v (M t j)` at every time (no X, no glitch);
* for EVERY closed walk `w` through `j`: `M (t + wLo w) j ≤ M t j + wTok w`
  (at most `wTok w` events of `j` in any window of `wLo w` steps);
* for EVERY `UpCert` / `LoCert` certificate: the long-run upper / lower
  rates of `Events2Time.rate_upper` / `rate_lower`.

## What is TRUSTED

The parser (`Formal.Core.XAudit.Parse`), the recogniser below (it proposes
`net`, `sm`, the environment gates and `back`), the certificate SEARCH and the
report. None of the recogniser's or the search's output is believed: `main`
prints the verdict only when the compiled `Decidable` instances of `Recog2`,
`Back`, `EnvOK`, `walkOK`, `UpCert` and `LoCert` return `true` on exactly the
objects that `sound` takes. Compiled code is trusted to agree with the kernel
definitions (the Lean compiler, not the kernel, runs it).

## The environment model (a HYPOTHESIS of `sound`, printed with every verdict)

An input port read (through a chain) by a C-element pin is closed by an
eager handshake partner of THAT stage: a 1-input gate from the stage's output
to the port, inverting iff the pin (after its chain parity and the LUT
bubble) must read the opposite of the stage's output to let it fire again.
Band `--env LO:HI` in ps (default `0:500`; `lo` is raised to 1 step). This is
exactly A-events2's `envS`/`envR` for pipe3, found automatically. A port
read by two control pins, or the reset port, is refused.
-/

namespace Formal.Core.XAudit.Events2MainStrict

open Lean (Json)
open Formal.Core
open Formal.Core.XAudit
open Formal.Core.XAudit.Parse
open Formal.Core.XAudit.Events2
open Formal.Core.XSim (toCircuit)
open Formal.Core.TraceDiscrete (Sig Transport)
open Formal.Core.XAudit.Events (ph)

/-! ## The verdict theorem (PROVED) -/

/-- The design closed by its environment gates. Same wires. -/
def close (d : Design) (env : List GSpec) : Design := ⟨d.m, d.gates ++ env⟩

/-- An environment gate is a 1-input buffer (`INIT 2`) or inverter (`INIT 1`). -/
def EnvOK (g : GSpec) : Prop := g.k = 1 ∧ (g.init = 1 ∨ g.init = 2) ∧ g.ins.length = 1

instance (g : GSpec) : Decidable (EnvOK g) := by unfold EnvOK; exact inferInstance

instance {N : Nat} {net : CNet N} (b : Bands net) (σ : (j : Fin N) → Fin (net.ar j))
    (T' K' : Nat) (ρ : Fin N → Nat) : Decidable (Beh.UpCert b σ T' K' ρ) := by
  unfold Beh.UpCert; exact inferInstance

/-- The environment hypothesis on one port is exactly its gate's relation. -/
theorem env_rel (d : Design) (g : GSpec) (hg : EnvOK g) (x : Fin d.n → Sig) (lo hi : Nat)
    (hlo : g.lo ≤ lo) (hhi : hi ≤ g.hi)
    (h : Transport lo hi (fun t => (g.init == 1) ^^ x (d.wire (g.ins.getD 0 0)) t)
      (x (d.wire g.out))) :
    (g.toLGate d).rel x := by
  refine (toLGate_rel d g x).mpr ?_
  have h' := TraceDiscrete.transport_mono hlo hhi h
  obtain ⟨name, k, init, ins, out, glo, ghi⟩ := g
  obtain ⟨hk, hi', hl⟩ := hg
  simp only at hk hi' hl h' ⊢
  subst hk
  obtain ⟨a, rfl⟩ : ∃ a, ins = [a] := by
    match ins, hl with
    | [a], _ => exact ⟨a, rfl⟩
  have e : (fun t => init.testBit (addr (fun p : Fin 1 => x (d.wire ([a].getD p.val 0)) t))) =
      (fun t => (init == 1) ^^ x (d.wire a) t) := by
    funext t
    show init.testBit ((x (d.wire a) t).toNat + 2 * 0) = _
    rcases hi' with rfl | rfl <;> cases x (d.wire a) t <;> rfl
  rw [e]; exact h'

theorem sat_close (d : Design) (env : List GSpec) (x : Fin d.n → Sig)
    (hsat : Circuit.Sat (toCircuit (build d)) x)
    (henv : ∀ g ∈ env, (g.toLGate (close d env)).rel x) :
    Circuit.Sat (toCircuit (build (close d env))) x := by
  refine (sat_build_iff (close d env) x).mpr ?_
  intro g hg
  have hs := (sat_build_iff d x).mp hsat
  simp only [close, List.mem_append] at hg
  rcases hg with hg | hg
  · exact hs g hg
  · exact henv g hg

/-- **What `xevents2` prints is this theorem.** Hypotheses checked by the
executable with compiled `decide`: `hr`, `hB`, `he` (and, for each printed
bound, `walkOK` / `UpCert` / `LoCert` of the printed certificate).
Modelling hypotheses: `hsat` (the netlist's gates and routes are transport
channels in their bands), `henv` (each environment port answers its stage in
a sub-band of its gate's band), `h0`, `hrst` (reset high until `T`). -/
theorem sound {N : Nat} (d : Design) (env : List GSpec) (net : CNet N) (sm : SMap2 net)
    (back : (j : Fin N) → Fin (net.ar j) → List (Arc net))
    (hr : Recog2 (close d env) net sm) (hB : Back sm.bands back) (he : ∀ g ∈ env, EnvOK g)
    (x : Fin d.n → Sig) (hsat : Circuit.Sat (toCircuit (build d)) x)
    (henv : ∀ g ∈ env, ∃ lo hi, g.lo ≤ lo ∧ hi ≤ g.hi ∧
      Transport lo hi (fun t => (g.init == 1) ^^ x (d.wire (g.ins.getD 0 0)) t) (x (d.wire g.out)))
    (h0 : ∀ t, x (d.wire 0) t = false) (T : Nat) (hT : 1 ≤ T)
    (hrst : ∀ t, x (d.wire sm.rst) t = decide (t < T)) :
    ∃ M : Nat → Fin N → Nat, (∀ j a b, a ≤ b → M a j ≤ M b j) ∧ (∀ j, M 0 j = 0) ∧
      (∀ t j, x (d.wire (sm.lut j).out) t = ph (net.v j) (M t j)) ∧
      (∀ (w : List (Arc net)) (j : Fin N), walkOK net j j w = true →
        ∀ t, M (t + wLo sm.bands w) j ≤ M t j + wTok net w) ∧
      (∀ σ T' K' ρ, Beh.UpCert sm.bands σ T' K' ρ → ∀ t j, T' * M t j ≤ K' * t + ρ j + T') ∧
      (∀ Tc K π Dm R, Beh.LoCert sm.bands Tc K π →
        (∀ j p, sm.bands.hiF j + sm.bands.hiG j p ≤ Dm) → (∀ j, T + (sm.rG j).hi ≤ R) →
        ∀ t j, K * t ≤ Tc * M t j + π j + K * (R + Dm)) := by
  have hs := sat_close d env x hsat (fun g hg => by
    obtain ⟨lo, hi, h1, h2, h3⟩ := henv g hg
    exact env_rel (close d env) g (he g hg) x lo hi h1 h2 h3)
  obtain ⟨bh, hc, hrr⟩ := design_beh2 (close d env) net sm hr x hs h0 T hT hrst
  refine ⟨bh.M, fun j a b h => bh.M_mono b j a h, bh.M_zero,
    fun t j => by have := bh.safe hB t j; rw [hc] at this; exact this,
    fun w j hw t => bh.cycle_le w j hw t,
    fun σ T' K' ρ hc' t j => bh.rate_upper hc' t j,
    fun Tc K π Dm R hc' hD hR t j => ?_⟩
  exact bh.rate_lower hc' hD (fun j s hs => hrr j s (Nat.le_trans (hR j) hs)) t j


/-- **What the strict `xevents2` prints is this theorem**: `sound` with the
race hypothesis taken in its strict form (`BackStrict`, margin ≥ 1 step). -/
theorem sound_strict {N : Nat} (d : Design) (env : List GSpec) (net : CNet N) (sm : SMap2 net)
    (back : (j : Fin N) → Fin (net.ar j) → List (Arc net))
    (hr : Recog2 (close d env) net sm) (hB : Events2Strict.BackStrict sm.bands back)
    (he : ∀ g ∈ env, EnvOK g)
    (x : Fin d.n → Sig) (hsat : Circuit.Sat (toCircuit (build d)) x)
    (henv : ∀ g ∈ env, ∃ lo hi, g.lo ≤ lo ∧ hi ≤ g.hi ∧
      Transport lo hi (fun t => (g.init == 1) ^^ x (d.wire (g.ins.getD 0 0)) t) (x (d.wire g.out)))
    (h0 : ∀ t, x (d.wire 0) t = false) (T : Nat) (hT : 1 ≤ T)
    (hrst : ∀ t, x (d.wire sm.rst) t = decide (t < T)) :
    ∃ M : Nat → Fin N → Nat, (∀ j a b, a ≤ b → M a j ≤ M b j) ∧ (∀ j, M 0 j = 0) ∧
      (∀ t j, x (d.wire (sm.lut j).out) t = ph (net.v j) (M t j)) ∧
      (∀ (w : List (Arc net)) (j : Fin N), walkOK net j j w = true →
        ∀ t, M (t + wLo sm.bands w) j ≤ M t j + wTok net w) ∧
      (∀ σ T' K' ρ, Beh.UpCert sm.bands σ T' K' ρ → ∀ t j, T' * M t j ≤ K' * t + ρ j + T') ∧
      (∀ Tc K π Dm R, Beh.LoCert sm.bands Tc K π →
        (∀ j p, sm.bands.hiF j + sm.bands.hiG j p ≤ Dm) → (∀ j, T + (sm.rG j).hi ≤ R) →
        ∀ t j, K * t ≤ Tc * M t j + π j + K * (R + Dm)) :=
  sound d env net sm back hr hB.back he x hsat henv h0 T hT hrst
/-! ## Recognition (TRUSTED; everything it proposes is re-checked) -/

structure PinR where
  src : Nat
  /-- source → pin, including the environment gate first if any -/
  chain : List GSpec
  pw : Nat
  inv : Bool
  neg : Bool
  port : Option String := none
  deriving Inhabited

structure StageR where
  lut : GSpec
  n : Nat
  v : Bool
  negMask : Nat
  pins : Array PinR
  fbG : GSpec
  rG : GSpec
  rstW : Nat
  deriving Inhabited

def isBufFrom (g : GSpec) (w : Nat) : Bool := g.k == 1 && g.init == 2 && g.ins == [w]

def hex (n : Nat) : String := "0x" ++ String.ofList (Nat.toDigits 16 n)

/-- A C-element candidate: a LUT6 one of whose pins is a buffer from its own
output. Returns `(n, v, negMask, fbG, rG)` if some arity/reset/bubble choice
passes `InitOK` with the `bd_ce.v` layout. -/
def asCel (gs : List GSpec) (g : GSpec) : Except String (Nat × Bool × Nat × GSpec × GSpec) := do
  let drv (w : Nat) := gs.find? (·.out == w)
  let fbIdx := (List.range 6).find? (fun i =>
    match drv (g.ins.getD i 0) with
    | some b => isBufFrom b g.out
    | none => false)
  let some n := fbIdx | throw "no own-feedback pin"
  if n == 0 || n > 4 then throw s!"own feedback on I{n}: not the bd_ce.v layout"
  if !((List.range 6).all (fun i => i < n + 2 || g.ins.getD i 0 == 0)) then
    throw s!"pins above I{n+1} are not tied to 0: not the bd_ce.v layout (latch or other storage?)"
  let some fbG := drv (g.ins.getD n 0) | throw "no feedback gate"
  let some rG := drv (g.ins.getD (n + 1) 0) | throw s!"I{n+1} has no driving arc (constant?): not a C-element reset pin"
  if !(rG.k == 1 && rG.init == 2 && rG.ins.length == 1) then throw s!"I{n+1} (reset) is not a routed arc"
  for m in List.range (2 ^ n) do
    for v in [false, true] do
      if decide (InitOK n v (fun p : Fin n => m.testBit p.val) g.init) then
        return (n, v, m, fbG, rG)
  throw s!"INIT {hex g.init} is not a {n}-input C-element (InitOK fails for every reset value and bubble pattern)"

/-- Trace a pin back through 1-input gates to a stage output or an input port. -/
def tracePin (gs : List GSpec) (stageOf : Nat → Option Nat) (portOf : Nat → Option String)
    (pw : Nat) : Except String (List GSpec × Sum Nat (String × Nat)) := do
  let mut cur := pw
  let mut ch : List GSpec := []
  for _ in List.range 256 do
    let some g := gs.find? (·.out == cur) | throw s!"wire {cur} has no driver"
    if !(g.k == 1 && (g.init == 1 || g.init == 2) && g.ins.length == 1) then
      throw s!"{g.name} is not a 1-input buffer/inverter and not a C-element stage (choice, datapath or unsupported logic: E5/E6)"
    ch := g :: ch
    cur := g.ins.getD 0 0
    if let some k := stageOf cur then return (ch, .inl k)
    if let some p := portOf cur then return (ch, .inr (p, cur))
    if cur ≤ 1 then throw s!"{g.name} reads a constant"
  throw "chain longer than 256 gates"

/-! ## Walks, cycles, certificates (TRUSTED search; results re-checked) -/

partial def walksGo (ar : Array Nat) (src : Array (Array Nat)) (b cap : Nat) (cur : Nat)
    (seen : List Nat) (acc : List (Nat × Nat)) (out : List (List (Nat × Nat))) :
    List (List (Nat × Nat)) :=
  (List.range (ar[cur]!)).foldl (fun out p =>
    if out.length ≥ cap then out else
    let nx := src[cur]![p]!
    let acc' := acc ++ [(cur, p)]
    if nx == b then acc' :: out
    else if seen.contains nx then out
    else walksGo ar src b cap nx (nx :: seen) acc' out) out

/-- All simple walks upstream from `a` to `b` (as `(stage, pin)` lists),
at most `cap`; `a = b` gives the empty walk only. -/
def walks (ar : Array Nat) (src : Array (Array Nat)) (a b cap : Nat) : List (List (Nat × Nat)) :=
  if a == b then [[]] else walksGo ar src b cap a [a] [] []

partial def cycGo (ar : Array Nat) (src : Array (Array Nat)) (s cap : Nat) (cur : Nat)
    (seen : List Nat) (acc : List (Nat × Nat)) (out : List (List (Nat × Nat))) :
    List (List (Nat × Nat)) :=
  (List.range (ar[cur]!)).foldl (fun out p =>
    if out.length ≥ cap then out else
    let nx := src[cur]![p]!
    let acc' := acc ++ [(cur, p)]
    if nx == s then acc' :: out
    else if nx < s || seen.contains nx then out
    else cycGo ar src s cap nx (nx :: seen) acc' out) out

/-- Simple cycles (upstream walks from a node back to itself), smallest node
first, at most `cap`. -/
def cyclesU (N : Nat) (ar : Array Nat) (src : Array (Array Nat)) (cap : Nat) :
    List (List (Nat × Nat)) :=
  (List.range N).foldl (fun out s => cycGo ar src s cap s [s] [] out) []

/-- Rotate a cycle so that it starts at node `j`. -/
def rotateTo (c : List (Nat × Nat)) (j : Nat) : Option (List (Nat × Nat)) :=
  match c.findIdx? (·.1 == j) with
  | some i => some (c.drop i ++ c.take i)
  | none => none

def fmtR (num den : Nat) : String :=
  if den == 0 then "inf" else s!"{num / den}.{(num * 10 / den) % 10}"

/-! ## Main -/

def usage : String :=
  "usage: xevents2 NETLIST.json [--top T] [--bands BANDS.json] [--env LO:HI (ps, default 0:500)] [--cap N]"

def parseLoHi (s : String) : Option (Nat × Nat) :=
  match s.splitOn ":" with
  | [a, b] => do pure (← a.toNat?, ← b.toNat?)
  | _ => none

def run (args : List String) : IO UInt32 := do
  let some netf := args.head? | IO.eprintln usage; return 2
  let j ← readJson netf
  let B ← match getArg args "--bands" with
    | some p => pure (parseBands (← readJson p))
    | none => pure ({} : Bands)
  let (tname, top) ← IO.ofExcept (pickTop j (getArg args "--top"))
  let bt ← IO.ofExcept (buildDesign B top)
  let d := bt.d
  let u := bt.unit
  let cap := ((getArg args "--cap").bind String.toNat?).getD 4096
  let some envPs := parseLoHi ((getArg args "--env").getD "0:500")
    | IO.eprintln usage; return 2
  let (elo, ehi, eraised) := toSteps u envPs
  if !d.wfB then IO.eprintln "xevents2: design not well formed (Design.WF failed)"; return 1
  let gs := d.gates
  IO.println s!"xevents2: {netf} top {tname}: {d.n} wires, {gs.length} gates"
  IO.println s!"bands: 1 step = {u} ps; environment answer band [{elo}, {ehi}] steps = [{elo * u}, {ehi * u}] ps{if eraised then " (lo raised to 1 step)" else ""}"
  -- 1. C-element stages
  let cands := gs.filter (fun g => g.k == 6 && (List.range 6).any (fun i =>
    match gs.find? (·.out == g.ins.getD i 0) with
    | some b => isBufFrom b g.out
    | none => false))
  let mut stages : Array (GSpec × Nat × Bool × Nat × GSpec × GSpec) := #[]
  let mut others : List String := []
  for g in cands do
    match asCel gs g with
    | .ok (n, v, m, fb, rg) => stages := stages.push (g, n, v, m, fb, rg)
    | .error e => others := s!"{g.name}: {e}" :: others
  for o in others.reverse do
    IO.println s!"  storage LUT outside the control domain: {o}"
  let N := stages.size
  IO.println s!"{N} C-element stages recognised (InitOK on the bd_ce.v layout)"
  if hN : N = 0 then IO.println "no C-element stage: nothing to check"; return 0
  else
  have hN' : 0 < N := Nat.pos_of_ne_zero hN
  let stageOf (w : Nat) : Option Nat := stages.findIdx? (fun s => s.1.out == w)
  let portOf (w : Nat) : Option String := (bt.inputs.find? (·.2 == w)).map (·.1)
  -- 2. pins
  let mut errs : List String := []
  let mut srs : Array StageR := #[]
  let mut envGs : List GSpec := []
  let mut usedPorts : List String := []
  let rstW := (stages[0]!).2.2.2.2.2.ins.getD 0 0
  for jj in List.range N do
    let (g, n, v, m, fb, rg) := stages[jj]!
    if rg.ins.getD 0 0 != rstW then errs := s!"{g.name}: reset arc reads a different wire" :: errs
    let mut pins : Array PinR := #[]
    for p in List.range n do
      let pw := g.ins.getD p 0
      let neg := m.testBit p
      match tracePin gs stageOf portOf pw with
      | .error e => errs := s!"{g.name} pin I{p}: {e}" :: errs
      | .ok (ch, .inl k) =>
          let cinv := cInv ch
          pins := pins.push { src := k, chain := ch, pw, inv := cinv, neg }
      | .ok (ch, .inr (pn, pwire)) =>
          if pwire == rstW then errs := s!"{g.name} pin I{p}: reads the reset port" :: errs
          if usedPorts.contains pn then errs := s!"{g.name} pin I{p}: port {pn} is read by two control pins: no single handshake partner" :: errs
          usedPorts := pn :: usedPorts
          -- the environment answers the stage: pin (after chain and bubble) = ¬ stage output
          let envInv := !neg ^^ cInv ch
          let eg : GSpec := { name := s!"env:{pn}", k := 1, init := if envInv then 1 else 2,
                              ins := [g.out], out := pwire, lo := elo, hi := ehi }
          envGs := envGs ++ [eg]
          pins := pins.push { src := jj, chain := eg :: ch, pw, inv := !neg, neg, port := some pn }
    srs := srs.push { lut := g, n, v, negMask := m, pins, fbG := fb, rG := rg, rstW }
  if !errs.isEmpty then
    for e in errs.reverse do IO.println s!"  NOT RECOGNISED {e}"
    IO.println "VERDICT: NOT RECOGNISED: the control is not a network of C-elements joined by buffer/inverter chains and handshake ports; the Events2 domain does not apply (choice is E5: see formal/notes/A-events3.md)"
    return 3
  if srs.any (fun s => s.pins.size != s.n) then IO.println "internal: pin count"; return 3
  -- 3. the objects `sound` takes
  let fin (i : Nat) : Fin N := ⟨i % N, Nat.mod_lt _ hN'⟩
  let net : CNet N := {
    v := fun j => (srs[j.val]!).v
    ar := fun j => max 1 (srs[j.val]!).n
    ar_pos := fun _ => Nat.lt_of_lt_of_le Nat.one_pos (Nat.le_max_left _ _)
    src := fun j p => fin ((srs[j.val]!).pins[p.val]!).src
    inv := fun j p => ((srs[j.val]!).pins[p.val]!).inv
    neg := fun j p => ((srs[j.val]!).pins[p.val]!).neg }
  let sm : SMap2 net := {
    lut := fun j => (srs[j.val]!).lut
    chain := fun j p => ((srs[j.val]!).pins[p.val]!).chain
    pw := fun j p => ((srs[j.val]!).pins[p.val]!).pw
    fbG := fun j => (srs[j.val]!).fbG
    rG := fun j => (srs[j.val]!).rG
    rst := rstW }
  let D := close d envGs
  let bd := sm.bands
  let arA : Array Nat := srs.map (fun s => s.n)
  let srcA : Array (Array Nat) := srs.map (fun s => s.pins.map (·.src))
  let toArcs (w : List (Nat × Nat)) : List (Arc net) := w.map (fun (k, p) =>
    ⟨fin k, ⟨p % net.ar (fin k), Nat.mod_lt _ (net.ar_pos _)⟩⟩)
  -- 4. back walks: the walk with the largest fastest traversal among those with few enough tokens
  let mut backA : Array (Array (List (Nat × Nat))) := #[]
  for jj in List.range N do
    let j := fin jj
    let mut row := #[]
    for pp in List.range arA[jj]! do
      let p : Fin (net.ar j) := ⟨pp % net.ar j, Nat.mod_lt _ (net.ar_pos _)⟩
      let ws := (walks arA srcA (srcA[jj]!)[pp]! jj cap).filter (fun w =>
        wTok net (toArcs w) + net.off j p ≤ 1)
      let best := ws.foldl (fun (acc : Option (List (Nat × Nat))) w =>
        match acc with
        | none => some w
        | some a => if wLo bd (toArcs w) > wLo bd (toArcs a) then some w else some a) none
      row := row.push (best.getD [])
    backA := backA.push row
  let back : (j : Fin N) → Fin (net.ar j) → List (Arc net) := fun j p => toArcs ((backA[j.val]!)[p.val]!)
  -- 5. per-stage report
  for jj in List.range N do
    let j := fin jj
    let s := srs[jj]!
    let bub := (List.range s.n).filter (fun p => s.negMask.testBit p)
    IO.println s!"  stage {jj} {s.lut.name} (wire {s.lut.out} '{bt.wname[s.lut.out]?.getD "?"}'): {s.n}-input C-element, reset value {if s.v then 1 else 0}, bubbles on {bub.map (s!"I{·}")}, INIT {hex s.lut.init}; LUT [{bd.loF j * u},{bd.hiF j * u}] ps, own feedback [{bd.loQ j * u},{bd.hiQ j * u}] ps"
    for pp in List.range s.n do
      let p : Fin (net.ar j) := ⟨pp % net.ar j, Nat.mod_lt _ (net.ar_pos _)⟩
      let pin := s.pins[pp]!
      let w := back j p
      let tok := wTok net w + net.off j p
      let okW := walkOK net (net.src j p) j w
      let margin : Int := (Int.ofNat (bd.loG j p + wLo bd w) - Int.ofNat (bd.hiQ j)) * u
      let what := match pin.port with
        | some pn => s!"port {pn} (environment: {if pin.inv then "inverting" else "buffering"} channel from this stage, [{elo * u},{ehi * u}] ps)"
        | none => s!"stage {pin.src} through {pin.chain.length} gate(s){if pin.inv then ", inverted" else ""}"
      IO.println s!"    I{pp} <- {what}; channel [{bd.loG j p * u},{bd.hiG j p * u}] ps, token {net.off j p}"
      let wtxt := if w.isEmpty then "empty walk (the pin closes on this stage)" else
        " -> ".intercalate (w.map (fun a => s!"stage {a.1.val}.I{a.2.val}"))
      IO.println s!"      Back: walk {wtxt}; tokens {tok} (need <= 1), fastest return {(bd.loG j p + wLo bd w) * u} ps vs own feedback max {bd.hiQ j * u} ps: margin {margin} ps{if okW then "" else " (walk invalid)"}"
      if let some _ := pin.port then
        let routeOnly : Int := (Int.ofNat (bd.loG j p) - Int.ofNat elo - Int.ofNat (bd.hiQ j)) * u
        IO.println s!"      BOUNDARY: margin = {routeOnly} ps (port route vs own feedback) + the environment's minimum answer time ({elo * u} ps assumed)"
  -- 6. the checks `sound` needs
  let recog := decide (Recog2 D net sm)
  let backOK := decide (Events2Strict.BackStrict bd back)
  let envOK := envGs.all (fun g => decide (EnvOK g))
  IO.println s!"Recog2 on the netlist closed by {envGs.length} environment gate(s) (proved-decidable): {recog}"
  IO.println s!"BackStrict (every pin, margin >= 1 step = {u} ps, proved-decidable): {backOK}"
  IO.println s!"EnvOK (environment gates are 1-input buffers/inverters): {envOK}"
  -- 7. period bounds
  let cyc := cyclesU N arA srcA cap
  let live := cyc.filter (fun c => wTok net (toArcs c) > 0)
  let dead := cyc.filter (fun c => wTok net (toArcs c) == 0)
  IO.println s!"counter graph: {cyc.length} simple cycles{if cyc.length ≥ cap then " (CAPPED)" else ""}, {dead.length} token-free"
  if !dead.isEmpty then IO.println "  a token-free cycle: its stages can never fire (deadlock)"
  IO.println "per-window upper bounds (Events2Time.cycle_le, via `sound`; walk re-checked with walkOK):"
  for jj in List.range N do
    let j := fin jj
    let cands := live.filterMap (fun c => rotateTo c jj)
    let best := cands.foldl (fun (acc : Option (List (Nat × Nat))) c =>
      let w := toArcs c
      match acc with
      | none => some c
      | some a => let wa := toArcs a
          if wLo bd w * wTok net wa > wLo bd wa * wTok net w then some c else some a) none
    match best with
    | none => IO.println s!"  stage {jj}: on no live cycle: no per-window bound"
    | some c =>
        let w := toArcs c
        let ok := walkOK net j j w
        IO.println s!"  stage {jj}: at most {wTok net w} event(s) in every window of {wLo bd w * u} ps (walk {" -> ".intercalate (c.map (fun a => s!"{a.1}.I{a.2}"))}, checked {ok})"
  -- lower certificate (liveness) from the max hi-ratio cycle
  let gcd := Nat.gcd
  let ratioBest (f : List (Arc net) → Nat) : Option (Nat × Nat) := live.foldl (fun acc c =>
    let w := toArcs c
    let (h, k) := (f w, wTok net w)
    match acc with
    | none => some (h, k)
    | some (h', k') => if h * k' > h' * k then some (h, k) else some (h', k')) none
  let arcsAll : List (Nat × Nat) := (List.range N).flatMap (fun jj => (List.range arA[jj]!).map (jj, ·))
  let Dm := arcsAll.foldl (fun a (jj, pp) =>
    let j := fin jj
    let p : Fin (net.ar j) := ⟨pp % net.ar j, Nat.mod_lt _ (net.ar_pos _)⟩
    max a (bd.hiF j + bd.hiG j p)) 0
  let rhi := (List.range N).foldl (fun a jj => max a (sm.rG (fin jj)).hi) 0
  let mut loLine := "  long-run lower rate: no live cycle"
  let mut loOK := false
  match ratioBest (wHi bd) with
  | none => pure ()
  | some (H, k) =>
      let gg := gcd H k
      let (Tc, K) := (H / gg, k / gg)
      let mut pi : Array Int := Array.replicate N 0
      for _ in List.range (N + 1) do
        for (jj, pp) in arcsAll do
          let j := fin jj
          let p : Fin (net.ar j) := ⟨pp % net.ar j, Nat.mod_lt _ (net.ar_pos _)⟩
          let s := (net.src j p).val
          let cand : Int := pi[s]! + K * (bd.hiF j + bd.hiG j p) - Tc * net.off j p
          if cand > pi[jj]! then pi := pi.set! jj cand
      let mn := pi.foldl min 0
      let piN : Array Nat := pi.map (fun z => (z - mn).toNat)
      let ok := decide (Beh.LoCert bd Tc K (fun j => piN[j.val]!))
      loOK := ok
      loLine := s!"  long-run LOWER rate (liveness, Events2Time.rate_lower via `sound`): {K}·t ≤ {Tc}·M t j + π_j + {K}·(T_rst + {rhi} + {Dm}) steps, π = {piN.toList}: at least {K} event(s) per {Tc * u} ps per stage = max cycle ratio {fmtR (H * u) k} ps/token; certificate checked {ok}"
  let mut upLine := "  long-run upper rate: no live cycle"
  let mut upOK := false
  match live.foldl (fun (acc : Option (List (Nat × Nat))) c =>
      let w := toArcs c
      match acc with
      | none => some c
      | some a => let wa := toArcs a
          if wLo bd w * wTok net wa > wLo bd wa * wTok net w then some c else some a) none with
  | none => pure ()
  | some c =>
      let w := toArcs c
      let (L, kl) := (wLo bd w, wTok net w)
      let gg := gcd L kl
      let (T2, K2) := (L / gg, kl / gg)
      -- σ: the cycle's arcs, then a tree of upstream arcs into it
      let mut sigma : Array (Option Nat) := Array.replicate N none
      let mut rho : Array (Option Int) := Array.replicate N none
      for (k, p) in c do sigma := sigma.set! k (some p)
      let arcLo (jj pp : Nat) : Nat × Nat :=
        let j := fin jj
        let p : Fin (net.ar j) := ⟨pp % net.ar j, Nat.mod_lt _ (net.ar_pos _)⟩
        (bd.loF j + bd.loG j p, net.off j p)
      -- around the cycle (k0, p0), (k1, p1), ... (src k_i p_i = k_{i+1}, src of the last = k0):
      -- ρ k0 = 0, then backwards with equality; the closing arc holds since T2·tok = K2·L
      match c.head? with
      | none => pure ()
      | some (k0, _) =>
          rho := rho.set! k0 (some 0)
          for (k, p) in (c.drop 1).reverse do
            let s := (srcA[k]!)[p]!
            let (lo, off) := arcLo k p
            if let some r := rho[s]! then rho := rho.set! k (some (r + T2 * off - K2 * lo))
      let mut changed := true
      let mut iter := 0
      while changed && iter < N + 1 do
        changed := false
        iter := iter + 1
        for (jj, pp) in arcsAll do
          let s := (srcA[jj]!)[pp]!
          if sigma[jj]!.isNone then
            if let some r := rho[s]! then
              let (lo, off) := arcLo jj pp
              sigma := sigma.set! jj (some pp); rho := rho.set! jj (some (r + T2 * off - K2 * lo)); changed := true
      if sigma.any (·.isNone) || rho.any (·.isNone) then
        upLine := "  long-run upper rate: some stage reaches no critical cycle upstream (no certificate searched)"
      else
        let rr := rho.map (·.getD 0)
        let mn := rr.foldl min 0
        let rhoN : Array Nat := rr.map (fun z => (z - mn).toNat)
        let σ : (j : Fin N) → Fin (net.ar j) := fun j =>
          ⟨((sigma[j.val]!).getD 0) % net.ar j, Nat.mod_lt _ (net.ar_pos _)⟩
        let ok := decide (Beh.UpCert bd σ T2 K2 (fun j => rhoN[j.val]!))
        upOK := ok
        upLine := s!"  long-run UPPER rate (Events2Time.rate_upper via `sound`): {T2}·M t j ≤ {K2}·t + ρ_j + {T2} steps, ρ = {rhoN.toList}: at most {K2} event(s) per {T2 * u} ps per stage = critical cycle {fmtR (L * u) kl} ps/token; certificate checked {ok}"
  IO.println upLine
  IO.println loLine
  if recog && backOK && envOK then
    IO.println s!"VERDICT: CLEAN FOREVER (Events2MainStrict.sound_strict, strict race): every behaviour of the parsed netlist (every delay in the bands, any power-up, reset released once), with every handshake port answered by its stage within [{elo * u}, {ehi * u}] ps (HYPOTHESIS: environment = {envGs.map (·.name)}), has every C-element output = reset value flipped M t j times at every time: no X, no glitch, for all time. Period bounds above hold for the same M (certificates: upper {upOK}, lower {loOK})."
    return 0
  else
    IO.println "VERDICT: NOT PROVED (a hypothesis of Events2MainStrict.sound_strict fails; a zero race margin counts as a failure; see the margins above). This is not a hazard report: run xaudit for the X-window audit."
    return 1

end Formal.Core.XAudit.Events2MainStrict

def main (args : List String) : IO UInt32 := Formal.Core.XAudit.Events2MainStrict.run args
