import Formal.Core.XAudit.Events9SelC

/-!
# Formal.Core.XAudit.Events9SelHold — the hold half of the select condition, as a checker row

Probe E8SelC (shard A). Notes: `formal/notes/A-e8selc.md` §3.

`design_verdict9_selC` needs H_SEL_TX per real filtered pin and select literal: the mapped
select channel is mid-transaction from `O k` until `hiC - selLo - lo(rg)` after the source's
last time in transaction `k`. That is B's hold condition H_HOLD_PIN
(`LibGapSteer.steer_pin_ok`: `F + pr.hi ≤ S1 + ps.lo`) at this pin. This file splits it into

* a decidable BAND check (`holdBand`), evaluated by `xselhold` on the parsed netlist with the
  corrected bands: for every copy `c` of the pin, `hiC c + 1 ≤ D + selLo + lo(rg)`, where
  `D = plo π` is the low end of a certificate path `π` of the parsed netlist from the
  channel's ACKNOWLEDGE wire down to the source node's output wire (`chainOK`: a connected
  path of existing gate inputs). The printed hold margin is `D + selLo + lo(rg) - hiC - 1`.
* one named trace hypothesis **H_ACK_LAG(D)**: the channel stays mid-transaction from `O k`
  until `D` after the source's last time in transaction `k` (the acknowledge cannot close the
  transaction sooner than the path delay after the source falls).

Proved:
* `tx_of_lag`: `holdBand` + H_ACK_LAG(D) ⇒ H_SEL_TX (soundness of the checker row);
* `hold_pin_of_band`: `holdBand` IS B's H_HOLD_PIN at this pin, for every source time `u`,
  with `F = u + 1`, `S1 = u + D` (stability end), `pr.hi = hiC`, `ps.lo = selLo + lo(rg)`;
* **`design_verdict9_selH`**: `design_verdict9_selC` with H_SEL_TX replaced by the checked
  `chainOK` / `holdBand` rows and H_ACK_LAG.

NOT proved: H_ACK_LAG itself. It is a causality statement (the acknowledge's fall for token
`k` is caused through SOME netlist path from the source's fall); deriving it from SatPin needs
the protocol (that the other inputs on the path do not fall early), i.e. the verdict's own
count conclusion at earlier times, which is circular with SelOK in the present proof
(design_verdict9 proves the wire/count link only from SelOK at all times). `xselhold` uses
the SHORTEST such path (Bellman-Ford over the parsed design, not proved minimal), so the
assumed lag is the smallest one that any causal path gives.
-/

namespace Formal.Core.XAudit.Events9SelHold

open Formal.Core
open Formal.Core.XAudit
open Formal.Core.TraceDiscrete (Sig Warp)
open Formal.Core.XAudit.Events2Pin (SatPin)
open Formal.Core.XAudit.Events5
open Formal.Core.XAudit.Events6
open Formal.Core.XAudit.Events7
open Formal.Core.XAudit.Events8
open Formal.Core.XAudit.Events9
open Formal.Core.XAudit.Events8Bridge
open Formal.Core.XAudit.Events9Sel
open Formal.Core.XAudit.Events9SelC

/-! ## Certificate paths -/

/-- The consecutive-link condition of a path: each element's input wire is the next
element's gate output, and the last element's input wire is `bot`. -/
def links (d : Design) (bot : Nat) : Path → Bool
  | [] => true
  | [(g, i)] => (gt d g).ins.getD i 0 == bot
  | (g, i) :: (g2, i2) :: r => ((gt d g).ins.getD i 0 == (gt d g2).out) && links d bot ((g2, i2) :: r)

/-- **A certificate path** from wire `top` (the gate output at its head) down to wire `bot`:
non-empty, connected, every element an existing gate input (`pathOK`). -/
def chainOK (d : Design) (top bot : Nat) (π : Path) : Bool :=
  match π with
  | [] => false
  | (g, _) :: _ => ((gt d g).out == top) && links d bot π && pathOK d π

/-! ## The band check and its soundness -/

section
variable {N : Nat} (d : Design) (net : Net4 N) (b : Bands4 net) (rn : Fin N → RNode)

/-- **The hold band check** of one select literal (decidable): with `D` the certificate
path's low end, every copy satisfies `hiC + 1 ≤ D + selLo + lo(rg)`. -/
def holdBand (j : Fin N) (p : Fin (net.ar j)) (e : SelEnt) (D : Nat) : Bool :=
  (List.finRange (net.nc j p)).all fun c =>
    decide (b.hiC j p c + 1 ≤ D + selLo d net rn j p + (gt d e.rg).lo)

/-- The printed hold margin of copy `c` (ps; negative = the check fails). -/
def holdMargin (j : Fin N) (p : Fin (net.ar j)) (e : SelEnt) (D : Nat) (c : Fin (net.nc j p)) : Int :=
  (D : Int) + selLo d net rn j p + (gt d e.rg).lo - b.hiC j p c - 1

theorem holdBand_spec {j : Fin N} {p : Fin (net.ar j)} {e : SelEnt} {D : Nat}
    (h : holdBand d net b rn j p e D = true) (c : Fin (net.nc j p)) :
    b.hiC j p c + 1 ≤ D + selLo d net rn j p + (gt d e.rg).lo := by
  unfold holdBand at h
  exact of_decide_eq_true (List.all_eq_true.mp h c (List.mem_finRange c))

theorem holdBand_margin {j : Fin N} {p : Fin (net.ar j)} {e : SelEnt} {D : Nat}
    (h : holdBand d net b rn j p e D = true) (c : Fin (net.nc j p)) :
    0 ≤ holdMargin d net b rn j p e D c := by
  have := holdBand_spec d net b rn h c
  unfold holdMargin; omega

/-- **`holdBand` is B's H_HOLD_PIN** (`LibGapSteer.steer_pin_ok`, `F + pr.hi ≤ S1 + ps.lo`)
at every copy and every source time `u`: request pulse end `F = u + 1`, select stable until
`S1 = u + D`, request read high end `hiC`, select read low end `selLo + lo(rg)` (the stage's
select read from the bus net, through the route arc). -/
theorem hold_pin_of_band {j : Fin N} {p : Fin (net.ar j)} {e : SelEnt} {D : Nat}
    (h : holdBand d net b rn j p e D = true) (c : Fin (net.nc j p)) (u : Nat) :
    ((u + 1 : Nat) : Int) + (b.hiC j p c : Int) ≤
      ((u + D : Nat) : Int) + ((selLo d net rn j p + (gt d e.rg).lo : Nat) : Int) := by
  have := holdBand_spec d net b rn h c
  omega

end

/-- **Soundness of the hold row**: the band check and H_ACK_LAG(D) give H_SEL_TX. -/
theorem tx_of_lag {ch : Formal.Net.Handshake.Chan} {M O : Nat → Nat} {D sLo rLo cHi : Nat}
    (hband : cHi + 1 ≤ D + sLo + rLo)
    (hlag : ∀ k u s, M u = 2 * k + 1 → O k ≤ s → s < u + D → Formal.Net.Ops.inTx ch s = true) :
    ∀ k u s, M u = 2 * k + 1 → O k ≤ s → s + sLo + rLo ≤ u + cHi → Formal.Net.Ops.inTx ch s = true :=
  fun k u s hu hs hw => hlag k u s hu hs (by omega)

/-! ## The verdict with the hold half as a checker row -/

section
variable {N : Nat} {d : Design} {net : Net4 N} {b : Bands4 net} {rn : Fin N → RNode} {rank : Fin N → Nat}
  {rw fuel : Nat} {x : Fin d.n → Sig} {cv : Fin N → Sig}

/-- **`design_verdict9` with the select condition split into C's H_BUNDLE, B's setup, and a
checked hold row.** As `design_verdict9_selC`, with H_SEL_TX replaced by: per real filtered
pin and select literal, a certificate path `π j p i` from the mapped channel's acknowledge
wire to the source node's output wire (`chainOK`, checked) whose low end passes the hold band
check against every copy (`holdBand`, checked), and **H_ACK_LAG(plo π)**: the mapped channel
stays mid-transaction from `O k` until `plo π` after every time the source shows
transaction `k`. -/
theorem design_verdict9_selH (hr : Recog6 d net b rn rank rw fuel) (hOK : net.OK7)
    {parts : List (List Nat)} {log : List Ln} {J : Array Jd} (hJ : runLog net b parts log = some J)
    (back line : (j : Fin N) → Fin (net.ar j) → Nat) (xS xw : Fin N → Nat) (xa : Fin N → List Arm)
    (hl : List HLn9) (gd : (j : Fin N) → Fin (net.ar j) → GD)
    (cp : (j : Fin N) → Fin (net.ar j) → Bool) (cxm : Fin N → Bool) (cl : (j : Fin N) → Fin (net.ar j) → Bool)
    (cg : (j : Fin N) → Fin (net.ar j) → Bool)
    (hcp : ∀ j p, cp j p = true → backOK7 net b J j p (back j p) = true)
    (hcx : ∀ m, cxm m = true → exclOK7 net b parts J m (xS m) (xa m) (xw m) = true)
    (hcl : ∀ j p, cl j p = true → lineOK7 net b J j p (line j p) = true)
    (hcg : ∀ j p, cg j p = true → guardOK8 net b parts J (hl.map (san J)) j p (gd j p) = true)
    (m : (j : Fin N) → Fin (net.ar j) → Nat → SelEnt) (π : (j : Fin N) → Fin (net.ar j) → Nat → Path)
    (hm : ∀ j p (sb : Nat × Bool), (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
      entOK d net rn j p sb.1 (m j p sb.1) = true ∧
      chainOK d (m j p sb.1).ak (gt d (rn (net.src j p)).lut).out (π j p sb.1) = true ∧
      holdBand d net b rn j p (m j p sb.1) (plo d (π j p sb.1)) = true)
    (hsat : SatPin d plG x) (h0 : ∀ t, x (d.wire 0) t = false) (h1 : ∀ t, x (d.wire 1) t = true)
    {T : Nat} (hT : 1 ≤ T) (hrst : ∀ t, x (d.wire rw) t = decide (t < T)) (harb : HARB7 net b rn x cv)
    (sel : Nat → Nat → Bool) :
    ∃ bh : Beh7 net b sel, (∀ j t, bh.c j t = ccOf rn x cv j t) ∧
      (∀ j p s, bh.gc j p s = gcnt net sel j p (bh.cm j p s)) ∧
      (SelPart sel parts →
        (∀ j p s (i : Fin (net.nc j p)), (rn j).virt = true → net.pk j p = PK.filt →
          bh.M (bh.G j p i s) (net.src j p) % 2 = 1 →
          bh.sv j p s = sel (net.grp j p) (bh.M (bh.G j p i s) (net.src j p) / 2)) →
        ∀ (R : (j : Fin N) → Fin (net.ar j) → Nat → Nat)
          (O : (j : Fin N) → Fin (net.ar j) → Nat → Nat → Nat),
        (∀ j p (sb : Nat × Bool), (rn j).virt = false → net.pk j p = PK.filt → sb ∈ selLits net rn j p →
          Formal.Net.Ops.Held ((m j p sb.1).ch x)) →
        (∀ j p (sb : Nat × Bool) k u s, (rn j).virt = false →
          net.pk j p = PK.filt → sb ∈ selLits net rn j p → bh.M u (net.src j p) = 2 * k + 1 →
          O j p sb.1 k ≤ s → s < u + plo d (π j p sb.1) →
          Formal.Net.Ops.inTx ((m j p sb.1).ch x) s = true) →
        (∀ j p (sb : Nat × Bool) (i : Fin (net.nc j p)) k, (rn j).virt = false → net.pk j p = PK.filt →
          sb ∈ selLits net rn j p →
          O j p sb.1 k + (gt d (m j p sb.1).rg).hi + selHi d net rn j p ≤ R j p k + b.loC j p i) →
        (∀ j p u k, (rn j).virt = false → net.pk j p = PK.filt →
          bh.M u (net.src j p) = 2 * k + 1 → R j p k ≤ u) →
        (∀ j p k, (rn j).virt = false → net.pk j p = PK.filt →
          sel (net.grp j p) k = selFn (selLits net rn j p)
            (fun i => x (d.wire (m j p i).dw) (O j p i k))) →
        (∀ j p s, net.mg j = false → net.pk j p ≠ PK.guard → cp j p = false → bh.P j p s ≤ bh.M (bh.Q j s) j + 1) →
        (∀ m s, net.mg m = true → cxm m = false → fodd (net.ar m) (fun p => bh.P m p s) ≤ 1) →
        (∀ j p s, net.pk j p = PK.multi → cl j p = false → ContigF (net.nc j p) (bh.cm j p s)) →
        (∀ j p, net.pk j p = PK.guard → cg j p = false → GuardPin bh j p) →
        ∀ t j, (rn j).virt = false →
          x (d.wire (gt d (rn j).lut).out) t = Formal.Core.XAudit.Events.ph (net.v j) (bh.M t j)) := by
  obtain ⟨bh, hc, hgc, H⟩ := design_verdict9_selC hr hOK hJ back line xS xw xa hl gd cp cxm cl cg
    hcp hcx hcl hcg m (fun j p sb hv hk hs => (hm j p sb hv hk hs).1) hsat h0 h1 hT hrst harb sel
  refine ⟨bh, hc, hgc, fun hp hvirt R O hheld hlag hsetup hwin hsel rB rX rL rG => ?_⟩
  refine H hp hvirt R O hheld ?_ hsetup hwin hsel rB rX rL rG
  intro j p sb i k u s hvf hk hsb hu hs hw
  have hband := holdBand_spec d net b rn (hm j p sb hvf hk hsb).2.2 i
  exact tx_of_lag hband (fun k u s h1 h2 h3 => hlag j p sb k u s hvf hk hsb h1 h2 h3) k u s hu hs hw

end

end Formal.Core.XAudit.Events9SelHold
