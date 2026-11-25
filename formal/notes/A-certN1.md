# Shard A: the Spec end of the one-pair milestone (2026-11-10)

Goal (C's 2026-11-08 plan step 3): "for every admissible delay, THE target computes gcd(12,18)". Its Spec form is
`PlanRPS.NetCorrectSeqOnN (fun a b => a = 12 ∧ b = 18) (· = some 1) p T R su Δo`: every behaviour of THE circuit
(H_DELAY at p, H_PRIM, H_ARB(T)) with an environment offering exactly one pair (12, 18) satisfies `Spec.Correct`.

**What is proved (Lean, check.sh OK, standard axioms):** `CertN1.onN1_of_cert`: that statement, for any g > 0,
κ < 1 and reset `R ≥ ⌈(1+κ)g⌉·(15,600 + 87·3,881) + 1`, from ONE premise: in every such behaviour, at its request
edge `t1` (from `IslR`, a low boundary), there are a certificate `C` and an end time `T` with `EpN1 C x t1 T Δo`.

**`EpN1` field by field, and where each should come from** (counts are `cnt x t1 u s`, from the request edge):
| field | content | source |
|---|---|---|
| interA/B/S | a.ack/b.ack/start.ack count ≤ req count ≤ ack count + 1 | `CertSpec.inter_of_ord` + `happened_of_ideal` on C's `cntE` ideal (`timedA_follows` .1), `cntE_nd` |
| interO | out0.ack ≤ out0.req ≤ out0.ack + 1 | same |
| interP | end.ack ≤ req ≤ end.ack + 1 (req's fall after end.ack's rise, transitively via start.ack) | same, one chain step |
| ordA/B/S | an ack event's alternative fired by s ⇒ the request's same event fired by s | direct cause: trivial from `AltIn`; else `happened_of_ideal` |
| ordO, ordP | out0.req event k+1 ⇒ out0.ack event k; req event k+1 ⇒ end.ack event k | same |
| en | each change of a.ack, b.ack, start.ack, out0.req, req enabled at counts ≤ those at s-1, own count current | gates: `timedA_follows` .2 (`ChangeOKA`) + `CertSpec.enabled_of_changeOKA` with TBehX rd/lo1; req: the hEnvE premise |
| capO, rose | out0.req changes ≤ 2 times, has risen by T | cntE ideal (count ≤ len = 2); `timedA_live` (count = len at T) |
| endLow | every boundary node low from T | `timedA_live` (constant from T) + even lengths + parity (`EnvData.x_par`) |
| islEnd | every island member (`CViewPS.memI`) low from T | same, for the island members (exact nodes) |
| data | from Δo after the out0 rise while out0 is up: out0 bus = gcd of the operands at t1 + 1 | data claims on out0.data bits (`Holds`), claim values = bits of 6 |

The env side of C's certificate theorems (hEnvE for req/out0.ack/end.ack) is C's `AO/EnvHS`/`EnvData`. The quiet
start at t1 (TBehX.quiet) is fine for the FIRST episode after reset; `n ≥ 2` needs notes/A-S6-chaining.md.
