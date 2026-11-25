/-!
# GLSdiff: where does the involution OR loop decide? (Float #eval, NOT a proof)

A Float transcription of `Formal.Cells.CElemInvolution.orb` (the bd_c2 OR loop
`x = b ∨ q`, runt `b = [0, Δ0)`, one involution channel `P` lumping LUT + feedback
wire) with the symmetric exp channel of `Formal.Core.Delay.Involution.expDelay`:
`δ(T) = Tp + τ ln(2 - e^{-(T+Tp)/τ})`, `δ∞ = Tp + τ ln 2`.

`outcome` follows the orbit until the first cancellation (`orb (n+2) ≤ orb (n+1)`):
the survivor is transition `n` (even = rise, so q latched = 'H'; odd = 'L').
`crit` bisects for the boundary between 'L' (runt lost: the LATER request wins)
and 'H' (latched). The fid GLS resolver (`fid_core.vh`) puts that boundary at
`TLOOP - WIN/2` (349 ps for TLOOP 424, WIN 150), measured in
`tools-A/glsdiff/tb_meta_centre.v`. Floats only: this is an experiment, not a claim.
-/
namespace GLSdiff

def dly (Tp tau T : Float) : Option Float :=
  let a := 2 - Float.exp (-(T + Tp) / tau)
  if a ≤ 0 then none else some (Tp + tau * Float.log a)

/-- 'H' latched, 'L' lost, 'O' still oscillating after `fuel` transitions. -/
def outcome (Tp tau s : Float) (fuel : Nat := 20000) : Char :=
  let dinf := Tp + tau * Float.log 2
  match dly Tp tau (s - dinf) with
  | none => 'L'
  | some d1 =>
    let o1 := s + d1
    if o1 ≤ dinf then 'L' else
    -- (o n, o (n+1), n)
    let rec go : Nat → Float → Float → Nat → Char
      | 0, _, _, _ => 'O'
      | k + 1, a, b, n =>
        match dly Tp tau (a - b) with
        | none => if n % 2 == 0 then 'L' else 'H'
        | some d =>
          let c := a + d
          if c ≤ b then (if n % 2 == 0 then 'H' else 'L') else go k b c (n + 1)
    go fuel dinf o1 0

def crit (Tp tau : Float) : Float := Id.run do
  let dinf := Tp + tau * Float.log 2
  let mut lo := 0.001
  let mut hi := dinf - 0.001
  for _ in [0:60] do
    let m := (lo + hi) / 2
    if outcome Tp tau m == 'H' then hi := m else lo := m
  return (lo + hi) / 2

/-- TLOOP = 424 ps (300 ps feedback wire + 124 ps arc), τ in ps. -/
def row (tau : Float) : String :=
  let Tp := 424 - tau * Float.log 2
  s!"tau {tau}: s* = {crit Tp tau}  outcome(s=360) = {outcome Tp tau 360}  outcome(s=300) = {outcome Tp tau 300}"

#eval [40, 60, 100, 150, 200].map row

end GLSdiff
