# B-reset-contract: the design-level reset contract of gcd_hw and its initial tokens

Probe Rst (shard B, gcd_hw capstone), 2026-10-27. Closes gap 8 of
`B-gcd-cells.md` and row C16 of `formal/out/gcd_hw_hypotheses.md` as far as
it can be closed without a route.

No route, no board, no toolchain run (`$TC` does not exist in this
container). Nothing below is a routed number and no nextpnr fingerprint
applies. The netlist facts come from bdc's emitted Verilog (re-emitted into
my scratchpad as `B-gcd-cells.md` describes, knobs unset) and from a
handshake-level Kleene scan of it, not from a synthesized or routed netlist.

## Files and check

- `formal/lean/Formal/Cells/ResetContract.lean` (about 810 lines, core Lean, no Mathlib).
  It imports `Prelim`, `CElemTiming`, `CTreeTimed`, `TernarySound` and
  `TernaryPhases`, all read-only. `CTreeTimed.olean` was missing, so I
  compiled it with `-o`.
- Check (about 5 s, no output):

      cd /home/user/asyncfpga3/formal/lean && PATH=$HOME/.elan/bin:$PATH LEAN_PATH=.lake/build/lib/lean ../slot.sh lean Formal/Cells/ResetContract.lean

  The file checks clean. It contains no `sorry`, no `admit` tactic, no
  `axiom` and no `native_decide`. The identifier `admits_ofBool_iff` comes
  from TernarySound. `#print axioms` (run locally, then deleted) gives:
  - `reset_binary`, `rig_reset_binary`, `first_change`, `arb_rstK`,
    `latch2_write_hi`: propext, Classical.choice, Quot.sound;
  - `c2n_frontier`: propext, Quot.sound;
  - `rig_frontier`, `neg_norst`: propext.
- Scratchpad only, not part of the repo:
  - the emitted kernel `.../scratchpad/rst/gcd_kernel.v`: `python3 bdc/emit.py
    cloud/fixtures/frontend/gcd/comp/handshake_transformed.mlir --no-top
    --probe n138`, 331 matched delays;
  - the scan `.../scratchpad/rst/reset_scan.py` and its output `scan_out.txt`
    (scratchpad = `/tmp/claude-0/-home-user-asyncfpga3/7f52a4bc-3f11-5919-b34a-537c5f812fdf/scratchpad`).

## 1. Every reset-carrying cell type: forced by rst, from any power-up state

gcd_hw uses these reset-carrying LUTs: `bd_c2n` (184 link and pipe
controllers, plus the rig's `uenv0`), `bd_c2n_set` (the rig's `uenv1`),
`bd_c2` (153, including the 18 arbiter acks), `bd_c3` (10, including the rig's
`ufork`), `bd_c4` (14), `bd_mux.uj0/uj1` (21 + 21), and `bd_arbiter.ustate`
O6 (9). The scan counts exactly these: 185 c2n, 1 c2n_set, 153 c2, 10 c3,
14 c4, 21 + 21 uj, and 9 arbiter q. For every one, with its real INIT and
pin map:

| theorem | statement |
|---|---|
| `c2_rstB`, `c2n_rstB`, `c2n_set_rstB`, `c3_rstB`, `c4_rstB`, `uj0_rstB`, `uj1_rstB`, `arb_rstB` | binary: when the rst pin is 1, the LUT gives the reset value (0, or 1 for `_set` and the arbiter q) for EVERY value of every other pin, the feedback pin included |
| `c2_rstK` ... `arb_rstK` | the same in Kleene semantics for every `f`/`t`/`x` on every other pin, so it also holds from all-X power-up. Proof: one `decide` on the all-`x` vector plus 7f's `lutK_mono` (`forced`) |

The timed form already existed per cell: `CElemTiming.c2_reset` and
`CTreeTimed.c3_reset`/`c4_reset`. This probe adds `c2n_reset` and
`c2n_set_reset`, which the JSON's `bd_c2n.reset_width` lacked; it cited only
the instance-level `c_reset_s1`. Hold rst at the pin for the loop bound
`Dmax = dlmax + dwmax`, from any power-up value. After that the cell keeps
its reset value through release for as long as its inputs do not enable it:
- `bd_c2n`: request 0 or next stage full;
- `uenv1`: `env_c0 = 1` or `in_ack = 0`.

**Delay lines and other stateless LUTs carry no reset.** These are
`bd_delay` sym and FASTRISE lines, `bd_delay_gated`, `uor`, `bd_steer`,
`bd_src`, the `bd_mux` uor, the arbiter's O5 and ugrant, and the rig's LUTs.
They "flush": once their drivers are at their reset values, they reach theirs
after their own depth. In the network theorem (section 2) this is the `rank`
of each comb node. The per-line form is the existing `H_RST_LINES`/`H_FLUSH`.

**The design level, `ResetSpec` / `reset_iter` / `reset_ternary` /
`reset_binary`.** These hold on 7f's LUT networks (`TernarySound.Circ`), with
GMW runs (unbounded per-pin wire delays, each gate holding or taking its LUT
value) and `Bounded D W`.

The single named obligation is `ResetSpec`:
- `H_IN`: rst is 1 during reset.
- `H_LOCAL`: each control LUT, with its lower-rank control pins at their reset
  values and EVERY other pin `x`, already gives its reset value.

Rank 0 is a reset cell (its forcing lemma). Rank r+1 is a stateless LUT whose
control pins have rank at most r. The data pins and the never-reset latch
outputs are `x` in this check, so `H_LOCAL` also expresses the guard condition
of section 4.

Under `ResetSpec`:
- `reset_ternary`: after `m + 1` Jacobi steps from all-X with `rst = t`, every
  control node of rank `< m` has its reset value. This is the Kleene form,
  from all-X.
- `reset_binary`: take EVERY bounded binary run, from ANY power-up state (no
  hypothesis on `v 0`), whose rst source is 1 on `(0, E]`. Every control node
  of rank `< m` shows its reset value on all of `[(m+1)(D+W+1), E]`.
  - The rst fanout skew is inside `W`: each rst pin reads the rst source
    through its own wire, at most `W` steps old.
  - The hold requirement is `E ≥ (rank_max + 2)(D + W + 1)`.
  - Physically: `R ≥` (max over reset pins of the rst arrival) + the cell loop
    bound + the longest control path from a reset cell to a reset cell input,
    delay lines included. Section 5 gives this in EndpointOK form.
  - The proof is TernaryPhases' `phase_cov` with window state all-X plus the
    rank induction.

**Concrete instance, `rigNet` (35 nodes, real INITs).** It contains:
- the rig ring: `uenv1`, `uenv0`, the `ufork` c3 ack tree, and two link
  stages, each a `bd_c2n` with a latch bit, a DACK FASTRISE chain and an
  rdly;
- a `bd_steer` whose select is link B's latch output (X), with `req1` as
  `res_req` and `req0` into a sink;
- a "zoo" that wires one instance of every other reset-carrying type to the
  ring's nets: a `bd_src` feeding a link, a `bd_mux` (uj0/uj1 with the select
  on the X latch, uor, uxa/uya), a gated-delay stage, a `bd_arbiter` (ustate
  O6/O5, ugrant O5/O6, ua1/ua2), and a `bd_c4`. The zoo's wiring is not a
  working circuit.

Results on `rigNet`:
- `rig_spec` holds; `decide` checks it.
- `rig_reset_ternary` and `rig_reset_binary`: the maximum rank is 4, so every
  control node is at its reset value from step `6(D+W+1)` on, in every
  bounded run from any power-up state.
- Negative controls, each of which must fail and does:
  - `neg_unguarded`: make the steer's `req1` an OR instead of an AND of
    request and select, and the X of the never-reset latch escapes into
    control, so the check is `false`.
  - `neg_norst`: tie one link controller's rst pin to 0, and its power-up X
    is never cleared, so the check is `false`.

**The whole gcd_hw, by the scan (not Lean).**
`reset_scan.py` flattens bdc_gcd plus the gcd_rig ring into 414 reset-carrying
state LUTs and 170 stateless control LUTs, with their real INITs and pin
maps; 60 data nets are tied to `x`.
- Every data net is `x`: steer selects, mux selects, the `muxn3` decode
  `ctl_req & (s==k)` (modelled as Kleene AND with an X), every latch, and the
  vector.
- Delay lines are their steady-state functions.
- The scan iterates the Kleene step with `rst = 1` from all-X. The fixed
  point comes after 4 handshake-level Jacobi steps: **0 control nodes X,
  every state node at its reset value.**

This is `H_LOCAL` checked on the real netlist structure. It is not a Lean
proof: the flattening is my Python reading of `cells/rtl` and of the
generated modules.

## 2. After release, before the first request: links empty, which tokens exist

**What "token" means here, in PipeTimedN's phase picture.**
- Each controller node `O i` (a `bd_c2n` `c`) has its edges at `τ i j`.
  Phase `j` has value `Vph j = (j even)`: even phases rise, odd phases fall.
  Datum `n` is phases `2n` and `2n+1`.
- At time `t`, let `J_i(t)` be the number of edges node `i` has made.
- On a channel from producer `p` to consumer `c`, the request at the
  consumer's pin carries `J_p` phases and the acknowledge carries `J_c`. The
  channel holds a token (a request phase not yet answered) iff
  `J_p − J_c = 1`. It is empty iff `J_p = J_c`.
- A link stage is empty iff its node is 0 with `J` even.

At release every link node has `J = 0` and every request is at
`Vph`-parity 0, except the request wires that are 1 at reset. **The initial
tokens are exactly the channels whose request is 1 while every acknowledge is
0.**

**The rig skeleton, in Lean.**
- `rig_frontier` (by `decide`): at the simultaneous-release state, where rst
  is 0 at every pin, every control net is at its reset value and data is X,
  exactly two control nodes are not at a fixed point. They are link A's
  controller (node 5, fed by `uenv1`'s token) and the source link's
  controller (node 18). Both have excitation 1, so both fill.
- `rig_post_definite`: every control node's post-release excitation is
  definite, although every latch and select is X.

**The whole gcd_hw, from the scan.**

The control nets that are 1 under reset:
- the rig's token `env_c` (`uenv1`). Through `ufork` (wires) it reaches
  `a_req`, `b_req` and `start_req`, and through the kernel forks (wires) it
  reaches `n1__0`, `n1__1_u`, `n0__0`, `n0__1` and the p_end channel.
  `p_end_req` = `start_req` combinationally, and `p_end_ack` = `p_end_req`
  through `upsnk`, so the p_end sink has ALREADY consumed its token during
  reset.
- the four `bd_src` requests (`usource3/5/7/13`: `req = ~ack = 1`), their
  forks (`n34_*`, `n66_*`, `n92_*`, `n153_*`, ...).
- the 9 arbiter state nodes (q = 1: priority state, not a token).

The frontier (state nodes whose post-release excitation differs from their
reset value) is 10 nodes, all `bd_c2n` stage-0 link controllers:
- `ulink_n1__1`: the rig token, on `a`'s fork branch into `ucmpi0`;
- `ulink_n36__0/1/2`, `ulink_n68__0/1`, `ulink_n94__0/1`,
  `ulink_n155__0/1`: the constant sources' tokens.

Every other state node is a fixed point.

So the precise statement is: **at release every link and pipe stage is empty
(`c = 0`, J = 0), every C-element is 0, every arbiter q is 1, and the only
tokens are**
- **the rig's ONE token**, presented on all three input channels (`a`, `b`,
  `start`), as the fork makes it;
- **the four constant sources' standing tokens**, which Dynamatic's `source`
  semantics make always available: `req = ~ack` re-offers at once.

"Exactly the rig's initial token" is true only if source channels are counted
as permanently full constants. The first activity after release is the 10
frontier links filling; 9 of them fill from sources and then wait at joins
for loop tokens. In the scan's first wave, firing `ulink_n1__1` enables
exactly three joins: `ucond_br9_j`, `ucond_br10_j` and `ucond_br11_j`, which
wait for the `a == 0` compare. The source frontiers enable nothing further.

**Timed release (window channels, Lean).**
- `c2n_frontier`: a link controller with the token at its request pin and
  the next stage empty is 0 while rst is high at ITS pin, from any power-up
  value once rst has lasted the loop bound. It is 1 from `r + dlmax` on,
  where `r` is the release at its own rst pin. It fires once. In
  `[r + dlmin, r + dlmax)` the non-FIFO window channel may show either value;
  a FIFO LUT shows one edge.
- No ordering between the rst select and the request select is needed,
  because the request is static.
- `c2n_reset`, `c2n_set_reset`, `CElemTiming.c2_reset` and
  `CTreeTimed.c3/c4_reset` give the non-frontier cells through release.
- `first_change` (generic): suppose min-delay potentials `P` are closed under
  the edges and bounded by `rel + dmin` at the frontier, and `H_CAUSAL` holds
  per node (derivable from `loop_causal` and `win_causal`). Then no node
  leaves its reset value before `P n`.
- `released_quiet`: suppose each reset cell's rst pin has released before
  the earliest frontier event can reach any of its pins (`H_RST_SKEW`). Then
  the design leaves reset in exactly the simultaneous-release state of
  `rig_frontier`/the scan.

**`H_RST_SKEW` is sufficient, not necessary.** The release races are covered
by `c2_race_holdK`, `c3_race_holdK`, `c4_race_holdK`, `c2n_race_holdK`,
`c2n_set_race_holdK`, `uj_race_holdK` and `race_movesK`:
- A cell that receives ONE input change while its rst is falling, with its
  other inputs at reset values, has a Kleene excitation equal to its reset
  value (`*_race_holdK`). That one-cell state is closed under the step, so by
  7f's `A_invariant` the cell does not move at all in any order of the two
  edges.
- A cell that the event ENABLES (the first wave: join with both inputs, link
  with a request) goes `x` during the race (`race_movesK`). Its new
  excitation is then forced (q-independent), so the follow lemma erases any
  transient once the inputs persist for the loop bound. That persistence is
  the cell's existing `pulse_width` / `env_latency` obligation.
- The one real hazard of late release is a lost event: an input that rises
  AND returns while the cell is still held. In a four-phase network every
  return needs the reader's acknowledge, so this can only happen on an
  unacknowledged branch. I state it as **H_NO_RETURN** and do not prove it
  for gcd_hw (see section 6). The checkable sufficient form is `H_RST_SKEW`.

## 3. Reset obligations as EndpointOK forms (for `cell_constraints.json`; NOT written)

These use the JSON's conventions (ps, `1C`; every pin term includes its site
pin; `margin_ps` 0, with the guardband applied by the checker).
`rst_src` = the `rig_rst` LUT output in gcd_hw.v (`~por_done | rst_sr[15]`).
`w_rst(X)` = the routed rst net from `rst_src` to pin `X`.

1. **`design.rst_hold`** (per reset-carrying LUT G: 185 c2n, 1 c2n_set, 153
   c2 (incl. the 18 arbiter acks, the 42 mux acks and the 6 muxn3 C-elements),
   10 c3, 14 c4, 42 uj, 9 ustate: 414 rst pins).
   - launch: `rst_src` rise.
   - data: `w_rst(G.I_rst)` hi + site_pin hi + lut_arc `I_rst -> O` hi
     (`dlmax`) + feedback_wire hi (`dwmax`) + feedback site_pin hi.
   - request: env `rst_width` (gcd_hw: 16 hk cycles from `rst_sr`; 24 more
     at POR) + `w_rst(G.I_rst)` lo.
   - lean: `c2n_reset`, `c2n_set_reset`, `CElemTiming.c2_reset`,
     `CTreeTimed.c3_reset`/`c4_reset`, the `*_rstB`/`*_rstK` forcing lemmas.
   - Sufficient. This generalises the existing `bd_c*.reset_width` (same
     form), which can cite these lemmas instead of the instance-level
     `c_reset_s1`.
2. **`design.rst_flush`** (per reset cell G and per non-rst pin p of G whose
   net is driven, through stateless LUTs and delay lines, by reset cell H).
   - launch: `rst_src` rise.
   - data: `w_rst(H.I_rst)` hi + site pin + H lut_arc hi + the longest control
     path H.O -> G.p hi (every LUT arc and wire, delay-line hops included).
   - request: `rst_width` + `w_rst(G.I_rst)` lo.
   - lean: `reset_binary` (in the GMW model; the depth is `rank`),
     `PipeTimedN.H_RST_LINES`/`PipePerPin.H_FLUSH` per line.
   - Sufficient. The longest such control path in gcd_hw is the 94-element
     `bd_delay_gated` of `uselect1` (plus `uor`, the fork wire and the join
     pin); `urdly` (CMPD = 16) is on the rig ring.
3. **`design.rst_release_skew`** (`H_RST_SKEW`; per frontier F and per reset
   cell G with a pin reachable from F).
   - launch: `rst_src` fall.
   - data: `w_rst(G.I_rst)` hi + site_pin hi.
   - request: `w_rst(F.I_rst)` lo + site_pin lo + F lut_arc `I3 -> O6` lo +
     the shortest path F.O -> G.p lo.
   - For gcd_hw the frontier is the 10 links above. The shortest paths are:
     - to the fork ack trees via the DACK FASTRISE side stage: about 1 LUT +
       2 wires. These are `*_race_holdK` cells, so the race is harmless even
       when this form fails.
     - to the first-wave joins `ucond_br9/10/11_j`: `ulink_n1__1.O ->
       ucmpi0.uor -> 30-hop gated line -> ufork2 (wires) -> join pins`.
   - lean: `first_change`, `released_quiet`. Sufficient only; see `H_NO_RETURN`.
   - A checker should evaluate it only for G in the first wave. For the
     others the Kleene race lemmas make it unnecessary.
4. **`gcd_rig.token_static`** (per frontier F).
   - The request pin of F carries 1 from before `rst_src` fall minus
     `w_rst(F)` lo, to F's first rise plus the loop bound.
   - This holds by construction: `env_c` is forced 1 during reset and held
     by `c2n_set_reset`; `bd_src` req = ~ack with ack = 0.
   - lean: `c2n_frontier` (`H_TOKEN`, `H_STAY`). This REPLACES
     `PipePerPin.H_RST_SEL(c)` for the frontier stages. That form, with
     `ρ 0 = R`, demands `ps.hi ≤ pr.lo`, a false requirement when the request
     has been static since power-up.
5. **`gcd_rig.idx_setup`** (per bit of `a_v`, `b_v`, and `g_v` at the compare).
   - launch: the hk-clock edge that moves `idx`.
   - data: clock-to-out + vector decode LUTs hi + route to the frontier
     latch's `d` pin (link `n1__1` lat) and to the direct `a_data`/`b_data`
     readers hi + latch setup.
   - request: `rst_width` + `rst_src` fall -> F rst pin lo + F arc lo.
   - Trivially met: 16 hk cycles.
6. **`bd_latch.first_write`**: no new id. It is the phase-0 instance of the
   existing `bd_pipe.boundary_I`/`data_lead`/`bd_latch.*.setup_*` ids. Section
   4 explains why that is all the never-reset latch needs.

## 4. `bd_latch` is not reset, and why that is harmless (exact condition)

TernaryOnBits found that data latches stay X until their first transaction.
Here, `latch_stays_x` shows an opaque latch with X feedback stays X, and
`latch_holdB` shows that in binary it holds its old value whatever `d` does.
On silicon that old value is the PREVIOUS window's data, not X.

**Condition NRBW (no read before first write).** For every `bd_latch` bit
L, with enable `c_L` (the stage controller, reset to 0):
- (a) **Guard.** Every LUT pin that reads `q_L`, or reads any net in the X
  cone of `q_L`, belongs to one of two kinds of LUT:
  - a LUT whose Kleene value, with its guarding request at its reset value 0
    and every data pin `x`, is definite (= its reset value). Proved for the
    real INITs:
    - `steer_guardK`: `bd_steer` req0/req1;
    - `uj0_guardK`, `uj1_guardK`: `bd_mux` joins, select pin;
    - `rig_cmp_guardK`: gcd_rig `uerr_d`, `uok_d`, `uabsn_d` (LUT2 8/4)
      and `ucmpb_d` (LUT3 90).
  - the next latch with `en = 0` (`latch_holdB`; the next stage's `c` is 0).

  The X cone of `q_L` is the yosys-inferred compute datapath, `bd_datamux`,
  and the amerge/muxn3 data muxes and index. The inferred readers need
  **H_GUARD_MAP**: yosys maps `sel[k] = ctl_req & (s == k)` (muxn3) so that
  `ctl_req` enters the LUT that computes `sel[k]`. Then Kleene gives 0 when
  `ctl_req = 0`, by `lutK_eq_f_iff`. An unguarded decomposition can give `x`.
  This is unproved; it needs the synthesized netlist.
- (b) **Write before read.** Every guard's first rise after release comes
  after `c_L`'s first rise (`latch_write`, `latch2_write_lo/hi`: a transparent
  latch with definite `d` is definite whatever its X feedback) plus the
  latch's `d -> q` arc and the cone's settle. This is the bundling constraint
  of the FIRST transaction: rule I/H at phase 0 (`Bundling.capture` with
  `Ton` = the first enable rise).

(a) is checked on the whole gcd_hw netlist structure by the scan: 0 control
nodes X with every data net X. On `rigNet` it is checked by `rig_spec` and
`rig_post_definite`. Its negative control is `neg_unguarded`. (b) is the
existing bundling obligation; reset adds nothing to it.

## 5. Theorems proved (namespace `Formal.Cells.ResetContract`)

| name | statement | hypotheses |
|---|---|---|
| `*_rstB` (8) | rst = 1 forces the reset value for all Boolean pins | none (decide on the real INIT) |
| `*_rstK` (8) | the same for all K3 pins (all-X power-up) | H_KLEENE_LUT (lutK semantics) |
| `c2_holdK`, `c2n_holdK('),` `c2n_firesK`, `c2n_set_holdK(')`, `c3_holdK`, `c4_holdK`, `arb_holdK`, `arb_quietK` | post-release hold/fire at reset-state inputs with one pin X | H_KLEENE_LUT |
| `steer_guardK`, `uj0/uj1_guardK(')`, `rig_cmp_guardK` | the guard of every reader of never-reset data | H_KLEENE_LUT |
| `*_race_holdK`, `race_movesK` | release races: rst and one input both X | H_KLEENE_LUT |
| `latch_stays_x`, `latch_holdB`, `latch_write`, `latch2_write_lo/hi` | latch not reset; the first write overwrites X | H_KLEENE_LUT |
| `Bst_mono`, `reset_iter`, `reset_ternary` | Kleene from all-X reaches the reset values by rank | `ResetSpec` (H_IN, H_LOCAL) |
| `reset_binary` | every bounded GMW run, any power-up state, rst held on (0,E]: control nodes at reset values on [(m+1)(D+W+1), E] | `ResetSpec`, `Bounded D W` (H_GATE_BOUND, H_WIRE_BOUND), `H_RST_HELD` |
| `rig_spec`, `rig_reset_ternary`, `rig_reset_binary` | the 35-node rig skeleton meets the spec; reset values from step 6(D+W+1) | as above |
| `rig_frontier`, `rig_post_definite` | frontier = {link A ctl, source link ctl}, both fire; all control excitations definite at release | none (decide) |
| `neg_unguarded`, `neg_norst` | negative controls: the check fails for an unguarded reader / a controller without reset | none |
| `c2n_set_eq` | INIT of `bd_c2n_set` = rst + maj(a, ~b, q) | none |
| `c2n_reset`, `c2n_set_reset` | timed reset and hold through release, any power-up | `LoopG` (H_LUT, H_FB, H_LOOP_POS), H_RST_PULSE, H_QUIET |
| `c2n_frontier` | frontier link controller fires once, within dlmax of its own release | `LoopG`, H_RST_HI, H_RST_LONG, H_RST_LO, H_TOKEN, H_STAY |
| `win_causal`, `loop_causal` | local causality of window channels / feedback cells | WinDelay / `LoopG`, H_FIX |
| `first_change`, `released_quiet` | min-delay potentials bound the first event; H_RST_SKEW gives the simultaneous-release state | H_SETTLED, H_CAUSAL, H_POS, H_POT_F, H_POT_E; H_RST_SKEW |

## 6. What did not work, what is unproved

- **The composition is not one Lean theorem.** Lean does not join (1) and
  (2):
  - (1) lives in the GMW model (unbounded per-pin delays plus upper bounds).
  - (2)'s timing lives in the window-channel model (lower bounds).
  - `first_change` takes `H_CAUSAL` as a hypothesis. `loop_causal` and
    `win_causal` are its per-cell ingredients, but I did not assemble them
    for a network.
  - Bridging the two models is shard A's `Bridge`/`Substrate` business.
- **The scan is not a proof.** The full-netlist results (0 X control nodes,
  10 frontier links, the first wave) come from my Python flattening of
  `cells/rtl` and of the generated modules. That includes my reading of
  delay lines as steady-state buffers and of the inferred `muxn3` decode as
  a Kleene AND. A Lean import of the emitted control netlist as a
  `TernarySound.Circ` would make `rig_spec`-style `decide` cover the real
  design; `TernaryOnBits` already does this for a routed `link_arb`. That is
  the natural next step. At 414 state plus 170 stateless control LUTs (4
  handshake-level Jacobi steps to the fixed point, with delay lines
  collapsed), it is feasible with TernaryOnBits' list iteration.
- **H_NO_RETURN** (no input of a still-held cell completes a pulse) is
  argued, not proved. It is what makes release skew harmless without
  `H_RST_SKEW`.
- **H_GUARD_MAP** for the yosys-inferred `muxn3` decode and the amerge index
  is unproved; it needs the synthesized netlist.
- **No route, so none of the EndpointOK forms is evaluated.** rst is a
  general-routed net with fanout 414 in the kernel and rig, so its skew is unknown.
  `H_RST_SKEW`'s request side for the first-wave joins includes a 30-hop
  gated line, so it is likely to hold. The 1-LUT paths to fork ack trees
  likely fail, which is harmless by the race lemmas.

## 7. Findings outside the theorems

1. **The rig's frontier is not in PipeTimedN's environment.** `EnvN`/`EnvP`
   require the first request to rise after release (`H_RST_EARLY : R ≤ ρ 0`,
   `H_REQ_LOW0`), and PipePerPin's `H_RST_SEL(c)` asks the rst select to
   release before the first request reaches its select. At all 10 gcd_hw
   frontier links the request is 1 throughout reset. With `ρ 0 = R`,
   `H_RST_SEL(c)` becomes `ps.hi ≤ pr.lo`, a per-pin band requirement that
   is spurious, because the request select has been static since power-up.
   `c2n_frontier` is the right statement for those stages: no ordering is
   needed.
2. **The 4 constant sources also put tokens in at release.** These are 9
   links. "One token in the ring" is true for the rig ring. The kernel at
   release holds the rig token plus the sources' standing tokens.
3. **gcd_hw.v's "stale result after reset" explanation is inconsistent with
   the reset contract.** The comment above `settled` says the previous
   vector's result is "still in flight" after reset release plus settle_sr.
   Under `reset_binary`, 16 hk cycles of rst (about 440 hops at the comment's
   own 27.5 hops/cycle; the longest control line is about 100 hops) leave NO
   request in flight anywhere, from any prior state. A mechanism consistent
   with the contract is the ASSERTION edge:
   - `idx` and `rst_sr` both load on the same `win_edge_d` hk edge, so the
     new `g_v` and the new `sel` (the sticky's vector index) arrive while
     the old result's `res_req` may still be high. rst has not yet reached
     the ring, and `urdly` adds 16 hops.
   - `armed` falls only via `settle_sr`, one hk cycle later, or via
     `settled` from `win_cnt` on the same edge.
   - That would set err (or ok) on the NEW vector from the OLD result. This
     is exactly the reported ok+err pairs, and the 2048-cycle `settled`
     window cures it by closing `armed` at the edge, not by draining.
   This is a hypothesis from reading the RTL, not a measurement. A test is
   to delay the `idx` update by one hk cycle after `rst_sr` asserts, with
   `settled` removed, and see whether the pairs return.
4. `p_end` is already consumed during reset (`p_end_ack = p_end_req = 1` via
   `upsnk`), so the start fork's ack tree has one input high at release. That
   is harmless (`c2_holdK`), but the p_end channel starts in phase "req high,
   ack high", not "empty".

## 7b. Verdict

**Works, with effort.**
- Done here: the per-cell contract (binary and all-X), the generic network
  theorem, a checked 35-node instance with negative controls, the timed
  frontier/hold lemmas, the potential theorem, and the release-race lemmas.
  The real netlist's reset state, frontier and guard condition were checked
  by an (unproved) scan.
- To finish:
  - import the emitted control netlist as a `Circ` and discharge `ResetSpec`
    by `decide`, reusing the TernaryOnBits machinery (about 1 day);
  - assemble `H_CAUSAL` from `loop_causal`/`win_causal` for a network (about
    half a day);
  - prove H_NO_RETURN from the four-phase discipline, or have the checker
    evaluate `design.rst_release_skew` on routes.
- What it buys: C16 moves from an unstated environment hypothesis to three
  checkable EndpointOK forms plus proved lemmas. The capstone can start from
  a precisely stated initial state: all links empty, the rig token on
  a/b/start, the source tokens, arbiter q = 1, and latches X behind proved
  guards.

## 8. Fidelity per primitive

- **LUT (every cell):** `lutB`/`lutK` of the REAL INIT and pin map from
  `cells/rtl` (O5 = low 32 bits over I0..I4 for LUT6_2).
  - Kleene results rest on H_KLEENE_LUT (a pass-transistor mux tree passes a
    definite value only when both legs agree).
  - In the GMW model (section 2), a gate takes its LUT value of any mixture
    of pin read times, so internal mux-tree transients are covered.
  - O5 and O6 of one LUT6_2 are separate nodes with their own pin reads. On
    silicon they share input buffers, so this over-approximates.
- **C-elements and the latch:** a LUT whose output feeds back to its own pin
  through a routed wire.
  - In the timed lemmas this is `LoopG`: a window LUT channel `[dlmin, dlmax]`
    plus a window feedback wire `[dwmin, dwmax]`, non-FIFO, the weakest
    bounded channel.
  - In the network model the feedback is an ordinary pin with its own read
    time.
- **rst:** an input node of the network; each rst pin reads it through its
  own wire. The skew is the wire bound `W` (section 2) or the per-pin release
  instants `rel` (section 4 lemmas).
- **Delay lines** (`bd_delay` sym and FASTRISE, `bd_delay_gated`, `uor`):
  individual LUT1/LUT2 nodes with their real INITs in `rigNet`. In the scan
  they are steady-state functions, which is valid only for the
  reset-state fixed point, not for timing.
- **Data / inferred logic** (fused datapaths, data muxes, decodes, index): X
  everywhere. Only the guard (Kleene AND with the request) is assumed for the
  inferred `muxn3` decode (H_GUARD_MAP).
