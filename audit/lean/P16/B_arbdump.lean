import Formal.Cells.BWit3NDefs
/-! Auditor P16: dump the Bwit3 arbiter traces, winner tables and the generated LUT tables. -/
open Formal.Cells Formal.Cells.BWit3 Formal.Net Formal.Net.CapNet Formal.Net.CapNet.Gcd
open Formal.Net.CapNet.Wit (CD)
open Formal.Cells.FiniteNetBoundA (qF r0F gF)

def bits (n k : Nat) : List Bool := (List.range k).map fun i => (n >>> i) % 2 == 1

#eval do
  -- LUT tables: index = r1 + 2 r2 + 4 q + 8 a0, rst separately
  for rst in [false, true] do
    let q := (List.range 16).map fun i => match bits i 4 with
      | [a, b, c, d] => if qF [a, b, c, d] rst then 1 else 0 | _ => 9
    let r := (List.range 16).map fun i => match bits i 4 with
      | [a, b, c, d] => if r0F [a, b, c, d] rst then 1 else 0 | _ => 9
    IO.println s!"LUT rst={rst} qF={q} r0F={r}"
  let g1 := (List.range 8).map fun i => if gF false (bits i 3) false then 1 else 0
  let g2 := (List.range 8).map fun i => if gF true (bits i 3) false then 1 else 0
  IO.println s!"LUT gF false (g1)={g1} gF true (g2)={g2}"

#eval do
  for n in arbList do
    if h : n < NO then
      let o : Fin NO := ⟨n, h⟩
      match ameC (opAt o) with
      | some (x, y, z) =>
        IO.println s!"ARB {n} x={x.val} y={y.val} z={z.val}"
        IO.println s!"  xrq={(cdB x).rq}"
        IO.println s!"  yrq={(cdB y).rq}"
        IO.println s!"  xak={(cdB x).ak}"
        IO.println s!"  yak={(cdB y).ak}"
        IO.println s!"  zrq={(cdB z).rq}"
        IO.println s!"  zak={(cdB z).ak}"
        IO.println s!"  q={aqL.getD n []}"
        IO.println s!"  g1={ag1L.getD n []}"
        IO.println s!"  g2={ag2L.getD n []}"
        IO.println s!"  tab={tabA o}"
        IO.println s!"  arbChk={arbChk o}"
      | none => IO.println s!"ARB {n} not an amerge"
  -- every amerge op in opAt
  let all := (List.finRange NO).filter fun o => (ameC (opAt o)).isSome
  IO.println s!"amerge ops: {all.map (fun (o : Fin NO) => o.val)}"
