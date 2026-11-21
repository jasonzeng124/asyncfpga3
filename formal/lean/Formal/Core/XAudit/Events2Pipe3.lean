import Formal.Core.XAudit.Events2Design

/-!
# Formal.Core.XAudit.Events2Pipe3 — pipe3 (an OPEN pipe) in the counter domain, every behaviour, all time

Probe A-events2. `designs/pipe3.json` is `bd_pipe #(.W(2), .N(3))`: three
`bd_c2n` link controllers, a `bd_delay` LUT1 line (`r[i]`) between
consecutive stages, and the latches (which the control does not read).
`xevents` (A-events) refused it: it is open (stage 0 reads the port
`req_in`, stage 2 reads `ack_out`) and two pins come through a LUT1 buffer.

Here:
* E1: the `r[i]` lines are chains `route → LUT1 → route` (band [81, 101]).
* E2: the environment is two extra 1-input gates, stated as hypotheses on
  the two input ports: an eager sender `req_in = ¬ack_in` delayed by
  `[elo, ehi]`, and an eager receiver `ack_out = req_out` delayed by
  `[elo', ehi']`, with `1 ≤ elo`, `ehi ≤ 10^9` steps (10 ms): ANY response
  time of the environment, as long as it answers each event of its partner
  stage, not before it.
* `pipe3_safe`: every behaviour of the parsed netlist with such an
  environment has the three controller outputs (wires 10, 8, 23) equal to
  `ph false (M t j)` at every time: no X, no glitch, for ever.
* `pipe3_rates` (E3): with an environment answering within [1, 50] steps
  (10..500 ps), each controller fires at most once per 135 steps in the
  long run and in every window of 135 steps per token of a critical cycle,
  and at least once per 171 steps in the long run (1.35 .. 1.71 ns per
  event, a cycle of 2.7 .. 3.42 ns per four-phase handshake).

`design` is what `xaudit --emit-lean` printed for `designs/pipe3.json` with
`designs/slow_corner.bands.json` (1 step = 10 ps). Wires: 2 ack_out,
5 req_in, 6 rst, 10 c0 (= ack_in), 8 c1, 23 c2 (= req_out); 0 is const 0.
-/

namespace Formal.Core.XAudit.Events2.Pipe3

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.XSim (toCircuit)
open Formal.Core.TraceDiscrete (Sig Transport Warp)
open Formal.Core.XAudit.Events (ph)

def design : Design := ⟨46, [
    ⟨"stage[0].u.ctl.u/I0", 1, 2, [5], 7, 36, 44⟩,
    ⟨"stage[0].u.ctl.u/I1", 1, 2, [8], 9, 36, 44⟩,
    ⟨"stage[0].u.ctl.u/I2", 1, 2, [10], 11, 27, 33⟩,
    ⟨"stage[0].u.ctl.u/I3", 1, 2, [6], 12, 36, 44⟩,
    ⟨"stage[0].u.ctl.u/O", 6, 50103310370341042, [7, 9, 11, 12, 0, 0], 10, 9, 13⟩,
    ⟨"stage[0].u.lat.pair[0].u/I0", 1, 2, [3], 13, 36, 44⟩,
    ⟨"stage[0].u.lat.pair[0].u/I1", 1, 2, [10], 14, 36, 44⟩,
    ⟨"stage[0].u.lat.pair[0].u/I2", 1, 2, [15], 16, 27, 33⟩,
    ⟨"stage[0].u.lat.pair[0].u/I3", 1, 2, [4], 17, 36, 44⟩,
    ⟨"stage[0].u.lat.pair[0].u/I4", 1, 2, [18], 19, 27, 33⟩,
    ⟨"stage[0].u.lat.pair[0].u/O6", 6, 18389266006955047096, [13, 14, 16, 17, 19, 1], 18, 9, 13⟩,
    ⟨"stage[0].u.lat.pair[0].u/O5", 5, 3099113656, [13, 14, 16, 17, 19], 15, 9, 13⟩,
    ⟨"stage[0].u.rdly.chain.g[0].u/I0", 1, 2, [10], 20, 36, 44⟩,
    ⟨"stage[0].u.rdly.chain.g[0].u/O", 1, 2, [20], 21, 9, 13⟩,
    ⟨"stage[1].u.ctl.u/I0", 1, 2, [21], 22, 36, 44⟩,
    ⟨"stage[1].u.ctl.u/I1", 1, 2, [23], 24, 36, 44⟩,
    ⟨"stage[1].u.ctl.u/I2", 1, 2, [8], 25, 27, 33⟩,
    ⟨"stage[1].u.ctl.u/I3", 1, 2, [6], 26, 36, 44⟩,
    ⟨"stage[1].u.ctl.u/O", 6, 50103310370341042, [22, 24, 25, 26, 0, 0], 8, 9, 13⟩,
    ⟨"stage[1].u.lat.pair[0].u/I0", 1, 2, [15], 27, 36, 44⟩,
    ⟨"stage[1].u.lat.pair[0].u/I1", 1, 2, [8], 28, 36, 44⟩,
    ⟨"stage[1].u.lat.pair[0].u/I2", 1, 2, [29], 30, 27, 33⟩,
    ⟨"stage[1].u.lat.pair[0].u/I3", 1, 2, [18], 31, 36, 44⟩,
    ⟨"stage[1].u.lat.pair[0].u/I4", 1, 2, [32], 33, 27, 33⟩,
    ⟨"stage[1].u.lat.pair[0].u/O6", 6, 18389266006955047096, [27, 28, 30, 31, 33, 1], 32, 9, 13⟩,
    ⟨"stage[1].u.lat.pair[0].u/O5", 5, 3099113656, [27, 28, 30, 31, 33], 29, 9, 13⟩,
    ⟨"stage[1].u.rdly.chain.g[0].u/I0", 1, 2, [8], 34, 36, 44⟩,
    ⟨"stage[1].u.rdly.chain.g[0].u/O", 1, 2, [34], 35, 9, 13⟩,
    ⟨"stage[2].u.ctl.u/I0", 1, 2, [35], 36, 36, 44⟩,
    ⟨"stage[2].u.ctl.u/I1", 1, 2, [2], 37, 36, 44⟩,
    ⟨"stage[2].u.ctl.u/I2", 1, 2, [23], 38, 27, 33⟩,
    ⟨"stage[2].u.ctl.u/I3", 1, 2, [6], 39, 36, 44⟩,
    ⟨"stage[2].u.ctl.u/O", 6, 50103310370341042, [36, 37, 38, 39, 0, 0], 23, 9, 13⟩,
    ⟨"stage[2].u.lat.pair[0].u/I0", 1, 2, [29], 40, 36, 44⟩,
    ⟨"stage[2].u.lat.pair[0].u/I1", 1, 2, [23], 41, 36, 44⟩,
    ⟨"stage[2].u.lat.pair[0].u/I2", 1, 2, [42], 43, 27, 33⟩,
    ⟨"stage[2].u.lat.pair[0].u/I3", 1, 2, [32], 44, 36, 44⟩,
    ⟨"stage[2].u.lat.pair[0].u/I4", 1, 2, [45], 46, 27, 33⟩,
    ⟨"stage[2].u.lat.pair[0].u/O6", 6, 18389266006955047096, [40, 41, 43, 44, 46, 1], 45, 9, 13⟩,
    ⟨"stage[2].u.lat.pair[0].u/O5", 5, 3099113656, [40, 41, 43, 44, 46], 42, 9, 13⟩]⟩

def g (i : Nat) : GSpec := design.gates.getD i default

/-- The environment as gates: sender (inverter, c0 → req_in), receiver
(buffer, c2 → ack_out), band `[1, eh]`. -/
def envS (eh : Nat) : GSpec := ⟨"env.sender", 1, 1, [10], 5, 1, eh⟩
def envR (eh : Nat) : GSpec := ⟨"env.receiver", 1, 2, [23], 2, 1, eh⟩

/-- The design closed by its environment. -/
def D (eh : Nat) : Design := ⟨design.m, design.gates ++ [envS eh, envR eh]⟩

/-- The control network: stage `j` is `stage[j].u.ctl.u` (`bd_c2n`); pin 0
is the request, pin 1 the (bubbled) acknowledge. -/
def net : CNet 3 where
  v := fun _ => false
  ar := fun _ => 2
  ar_pos := fun _ => by decide
  src := fun j p => match j.val, p.val with
    | 0, 0 => 0 | 0, _ => 1 | 1, 0 => 0 | 1, _ => 2 | _, 0 => 1 | _, _ => 2
  inv := fun j p => j.val == 0 && p.val == 0
  neg := fun _ p => p.val == 1

def sm (eh : Nat) : SMap2 net where
  lut := fun j => g ([4, 18, 32].getD j.val 0)
  chain := fun j p => match j.val, p.val with
    | 0, 0 => [envS eh, g 0] | 0, _ => [g 1]
    | 1, 0 => [g 12, g 13, g 14] | 1, _ => [g 15]
    | _, 0 => [g 26, g 27, g 28] | _, _ => [envR eh, g 29]
  pw := fun j p => [[7, 9], [22, 24], [36, 37]].getD j.val [] |>.getD p.val 0
  fbG := fun j => g ([2, 16, 30].getD j.val 0)
  rG := fun j => g ([3, 17, 31].getD j.val 0)
  rst := 6

/-- Back walks: the environment pins close on their own stage (empty walk),
the others through the neighbour's request/acknowledge pin. -/
def back : (j : Fin 3) → Fin (net.ar j) → List (Arc net) := fun j p =>
  match j.val, p.val with
  | 0, 0 => [] | 0, _ => [⟨1, (0 : Fin 2)⟩]
  | 1, 0 => [⟨0, (1 : Fin 2)⟩] | 1, _ => [⟨2, (0 : Fin 2)⟩]
  | _, 0 => [⟨1, (1 : Fin 2)⟩] | _, _ => []

theorem recog : Recog2 (D 1000000000) net (sm 1000000000) := by decide +kernel

theorem backOK : Back (sm 1000000000).bands back := by decide +kernel

theorem recog50 : Recog2 (D 50) net (sm 50) := by decide +kernel

theorem backOK50 : Back (sm 50).bands back := by decide +kernel

/-- The sender gate is exactly the hypothesis on `req_in`. -/
theorem envS_rel (eh : Nat) (x : Fin design.n → Sig) (elo ehi : Nat) (h1 : 1 ≤ elo) (h2 : ehi ≤ eh)
    (h : Transport elo ehi (fun t => !x (design.wire 10) t) (x (design.wire 5))) :
    ((envS eh).toLGate (D eh)).rel x := by
  refine (toLGate_rel (D eh) (envS eh) x).mpr ?_
  have e : (fun t => (envS eh).init.testBit (addr (fun p : Fin (envS eh).k =>
      x ((D eh).wire ((envS eh).ins.getD p.val 0)) t))) = (fun t => !x (design.wire 10) t) := by
    funext t
    show (1 : Nat).testBit ((x (design.wire 10) t).toNat + 2 * 0) = _
    cases x (design.wire 10) t <;> rfl
  rw [e]
  exact TraceDiscrete.transport_mono h1 h2 h

theorem envR_rel (eh : Nat) (x : Fin design.n → Sig) (elo ehi : Nat) (h1 : 1 ≤ elo) (h2 : ehi ≤ eh)
    (h : Transport elo ehi (x (design.wire 23)) (x (design.wire 2))) :
    ((envR eh).toLGate (D eh)).rel x := by
  refine (toLGate_rel (D eh) (envR eh) x).mpr ?_
  have e : (fun t => (envR eh).init.testBit (addr (fun p : Fin (envR eh).k =>
      x ((D eh).wire ((envR eh).ins.getD p.val 0)) t))) = x (design.wire 23) := by
    funext t
    show (2 : Nat).testBit ((x (design.wire 23) t).toNat + 2 * 0) = _
    cases x (design.wire 23) t <;> rfl
  rw [e]
  exact TraceDiscrete.transport_mono h1 h2 h

theorem sat_D (eh : Nat) (x : Fin design.n → Sig) (hsat : Circuit.Sat (toCircuit (build design)) x)
    (hS : ((envS eh).toLGate (D eh)).rel x) (hR : ((envR eh).toLGate (D eh)).rel x) :
    Circuit.Sat (toCircuit (build (D eh))) x := by
  refine (sat_build_iff (D eh) x).mpr ?_
  intro g hg
  have hs := (sat_build_iff design x).mp hsat
  simp only [D, List.mem_append, List.mem_cons, List.not_mem_nil, or_false] at hg
  rcases hg with hg | rfl | rfl
  · exact hs g hg
  · exact hS
  · exact hR

/-- **pipe3 is hazard-free for ever, with any handshaking environment.** -/
theorem pipe3_safe (x : Fin design.n → Sig) (hsat : Circuit.Sat (toCircuit (build design)) x)
    (h0 : ∀ t, x (design.wire 0) t = false) (T : Nat) (hT : 1 ≤ T)
    (hrst : ∀ t, x (design.wire 6) t = decide (t < T))
    (elo ehi elo' ehi' : Nat) (hl : 1 ≤ elo) (hh : ehi ≤ 1000000000)
    (hl' : 1 ≤ elo') (hh' : ehi' ≤ 1000000000)
    (hsnd : Transport elo ehi (fun t => !x (design.wire 10) t) (x (design.wire 5)))
    (hrcv : Transport elo' ehi' (x (design.wire 23)) (x (design.wire 2))) :
    ∃ M : Nat → Fin 3 → Nat, (∀ j a b, a ≤ b → M a j ≤ M b j) ∧ (∀ j, M 0 j = 0) ∧
      ∀ t, x (design.wire 10) t = ph false (M t 0) ∧ x (design.wire 8) t = ph false (M t 1) ∧
        x (design.wire 23) t = ph false (M t 2) := by
  have hs := sat_D 1000000000 x hsat (envS_rel _ x elo ehi hl hh hsnd) (envR_rel _ x elo' ehi' hl' hh' hrcv)
  obtain ⟨M, hm, hz, hc⟩ := design_safe2 (D 1000000000) net (sm 1000000000) recog backOK x hs h0 T hT hrst
  exact ⟨M, hm, hz, fun t => ⟨hc t 0, hc t 1, hc t 2⟩⟩

/-- The rate certificates (from `formal/tools-A/xaudit/events2/cert.py`,
re-checked here). -/
def σ : (j : Fin 3) → Fin (net.ar j) := fun j => if j.val = 0 then (1 : Fin 2) else (0 : Fin 2)

theorem up50 : Beh.UpCert (sm 50).bands σ 135 1 (fun j => [180, 90, 0].getD j.val 0) := by
  unfold Beh.UpCert; decide +kernel

theorem lo50 : Beh.LoCert (sm 50).bands 171 1 (fun j => [0, 114, 228].getD j.val 0) := by
  decide +kernel

theorem hi50 : ∀ j p, (sm 50).bands.hiF j + (sm 50).bands.hiG j p ≤ 114 := by decide +kernel

theorem rst_hi : ∀ j : Fin 3, ((sm 50).rG j).hi = 44 := by decide +kernel

/-- The stage-0/stage-1 cycle (acknowledge pin of 0, request line of 1):
one token, fastest traversal 135 steps. -/
def crit : List (Arc net) := [⟨0, (1 : Fin 2)⟩, ⟨1, (0 : Fin 2)⟩]

theorem crit_ok : walkOK net 0 0 crit = true ∧ wTok net crit = 1 ∧ wLo (sm 50).bands crit = 135 := by
  decide +kernel

/-- **pipe3 rates (E3)**, environment answering within [1, 50] steps:
for every behaviour, stage 0 fires at most once in every window of 135
steps; every stage fires at most once per 135 steps and at least once per
171 steps in the long run (constants: the potentials). -/
theorem pipe3_rates (x : Fin design.n → Sig) (hsat : Circuit.Sat (toCircuit (build design)) x)
    (h0 : ∀ t, x (design.wire 0) t = false) (T : Nat) (hT : 1 ≤ T)
    (hrst : ∀ t, x (design.wire 6) t = decide (t < T))
    (elo ehi elo' ehi' : Nat) (hl : 1 ≤ elo) (hh : ehi ≤ 50) (hl' : 1 ≤ elo') (hh' : ehi' ≤ 50)
    (hsnd : Transport elo ehi (fun t => !x (design.wire 10) t) (x (design.wire 5)))
    (hrcv : Transport elo' ehi' (x (design.wire 23)) (x (design.wire 2))) :
    ∃ M : Nat → Fin 3 → Nat,
      (∀ t j, x (design.wire ((sm 50).lut j).out) t = ph false (M t j)) ∧
      (∀ t, M (t + 135) 0 ≤ M t 0 + 1) ∧
      (∀ t j, 135 * M t j ≤ t + [180, 90, 0].getD j.val 0 + 135) ∧
      (∀ t j, t ≤ 171 * M t j + [0, 114, 228].getD j.val 0 + (T + 44 + 114)) := by
  have hs := sat_D 50 x hsat (envS_rel _ x elo ehi hl hh hsnd) (envR_rel _ x elo' ehi' hl' hh' hrcv)
  obtain ⟨bh, hc, hr⟩ := design_beh2 (D 50) net (sm 50) recog50 x hs h0 T hT hrst
  refine ⟨bh.M, fun t j => by have := bh.safe backOK50 t j; rw [hc] at this; exact this,
    fun t => ?_, fun t j => ?_,
    fun t j => ?_⟩
  · have := bh.cycle_le crit 0 crit_ok.1 t
    rw [crit_ok.2.1, crit_ok.2.2] at this; exact this
  · have := bh.rate_upper up50 t j; omega
  · have := bh.rate_lower (R := T + 44) lo50 hi50 (fun j s hs => hr j s (by rw [rst_hi]; exact hs)) t j
    omega

/-! ## Negative controls (each check can fail) -/

/-- Slow own feedback ([1300, 1500] ps, `designs/slowfb.bands.json`):
`Back` fails (the fastest round trip through stage 1 is 1260 ps). -/
theorem slowfb_neg : ¬ Back { (sm 50).bands with hiQ := fun _ => 150 } back := by decide +kernel

/-- Getting the sender's polarity wrong (a buffer where it inverts) is
rejected by `Recog2`: the chain parity is checked against `inv`. -/
def netB : CNet 3 := { net with inv := fun _ _ => false }

def smB : SMap2 netB where
  lut := (sm 50).lut
  chain := (sm 50).chain
  pw := (sm 50).pw
  fbG := (sm 50).fbG
  rG := (sm 50).rG
  rst := 6

theorem inv_neg : ¬ Recog2 (D 50) netB smB := by decide +kernel

/-- A chain through a non-buffer LUT (the latch `O6`) is not a chain. -/
theorem chain_neg : chainOK (D 50) [g 10] 10 18 = false := by decide +kernel

theorem crit_hi : wHi (sm 50).bands crit = 171 := by decide +kernel

/-- No lower (liveness) certificate beats the max cycle ratio 171 steps/token. -/
theorem lo_tight {T K : Nat} {π : Fin 3 → Nat} (hc : Beh.LoCert (sm 50).bands T K π) : 171 * K ≤ T := by
  have := Beh.LoCert.cycle hc crit 0 crit_ok.1
  rw [crit_hi, crit_ok.2.1] at this; omega

end Formal.Core.XAudit.Events2.Pipe3
