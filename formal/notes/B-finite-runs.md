# B-finite-runs (probe Bfin): the link class for terminating gcd runs

2026-10-29. Answers self-audit 5's MAJOR finding (`SelfAuditB8.physLink_req_alternates`,
`chW_fails_H_LINKS*`): Bfb2's `PhysLink` and the environments `Env1`/`EnvC`/`EnvG` index
phases by `ℕ → ℕ`, so they only allow runs in which every link handshakes forever, and C's
witness run `Wit.chW` (a = 12, b = 18, quiet after 476 ticks) violates the `H_LINKS` of both
end-to-end link theorems.

## Files (all checked with `/tmp/claude-0/btools/bcheck.py`, core Lean only)

| file | result | content |
|---|---|---|
| `formal/lean/Formal/Cells/FiniteRuns.lean` | **OK** | finite bridge, finite link stage, finite C-element, finite link-to-link channel, `FPhysLink`, `gcd_hw_safe_fin_links` |
| `formal/lean/Formal/Cells/FiniteRunsWit.lean` | **OK** | `gcd_hw_safe_net` restriction, event-list lemmas, the link checker `linkB` and its soundness, two small witnesses |
| `formal/lean/Formal/Cells/FiniteRunsWitData.lean` | **OK** | kernel checks on all 175 links of `chW` (4 chunks, about 2 min), the joint witness |

Scratch: `/tmp/claude-0/probes/Bfin/` (`an.py`: the Python pre-check of `chW`'s link
traces; `Ax.lean`: the axiom printout).

## (1) `gcd_hw_safe_net` has the same problem: yes

`gcdNetOK_req_alternates`: `GcdNetOK ch N` gives `PhysLink` on every link
(`physLink_of_net`), so every link's input request is high at some `t ≥ T` and low at some
`t ≥ T` for every `T`. `chW_no_gcdNet`: there is no `N` with `GcdNetOK chW N`. So none of
the three end-to-end theorems (`gcd_hw_safe_phys_links`, `gcd_hw_safe_chains`,
`gcd_hw_safe_net`) covers a run that finishes.

## (2) The finite form

`FPhases x c n`: `x` is 0 before `c 0` (always if `n = 0`), `Vph j` on `[c j, c (j+1))` for
`j + 1 < n`, and `Vph (n-1)` from `c (n-1)` on, forever. `FEnv1 … ρ α nr na Es Ea` is
`Env1` field by field, with the request making `nr` edges and the acknowledge `na` (any
finite numbers, 0 allowed), each pin constant after its last edge, and H_SND / H_RCV kept
per phase for every edge that follows a node edge (`j < nr`, `j ≤ na`). No count relation
is assumed: the node makes `n = min nr (na + 1)` edges. `FEnvG` does the same for an
`ι`-pin C-element (per-pin counts `m i`, `n` node edges, `H_STOP`: some pin never starts
phase `n`). `FPhysLink` is `PhysLink` verbatim with `FEnv1` in place of `Env1`.

Re-proved for the finite form: `fnode_steps`, `fchange_at`, `flutFb_of_fphases`,
`ffbFirst_of_fphases` (Bfb's generic bridge), `fs_phase`/`fs_pre`/`fs_gap` (the single-stage
causal argument), `flink_lutFb`, `flink_guar`, `fwire_steps`, `fwire_di`, `link_of_fphys`,
`fcelG_lutFb`, `flink_link_env`. The only new idea: in the last phase the "next edge" of a
pin that never moves again is replaced by an arbitrary bound `M > s`, so `exc_phase_w` gives
the excitation at every `s`. The last phase is constant whatever the other pin does later
(a C-element with one pin and its feedback at `v` stays at `v`), so no count relation
between request and acknowledge is needed.

NOT done: the finite forms of `link_segK`, `celG_segK`, `steer_segK`, `chain_env1`,
`net_closed_gen`, `mixed_closed`. The brief expected the strict-causality induction to
"go through unchanged with a finite index set per cell". It does not, for one reason:
`ag_time` times each (cell, segment) event by the segment's END, and in a quiet run the last
segment of every cell has no end. The last segments depend on each other: a link's last
node segment needs its pins' last segments, which need the neighbours' last node segments.
The finite segments (`k < n_c`) do go through as before. The last ones need a
time-truncated cell lemma ("pins correct on `[.., T)` gives the node correct on
`[.., T + lo)`"), proved again for every segK lemma (link, generic C-element, gated steer,
lutnf), with events (cell, last, T) timed by `T`. That is the open goal for
`gcd_hw_safe_chains` / `gcd_hw_safe_net` in finite form.

## (3) Restated: `gcd_hw_safe_fin_links`

C's `gcd_hw_circuit_safe` with `H_CELLS` of the 175 links replaced by `FPhysLink`. Same
conclusion as `gcd_hw_safe_phys_links`. Assumed per link: B's `Stage`, `Timing1`,
H_LUT_POS, H_PWR, two `Wire`s with H_WIRE_R/H_WIRE_SPREAD, the latch data fields, and
`FEnv1`. Still C's: `H_CELLS` of the 192 other operators, H_BUNDLE, H_CM_FORCED.

## (4) The decisive check: C's witness meets it

`chW_fin_links`: for every link operator `opAt o = .link i o'`, `FPhysLink (chW i) (chW o')`,
by a kernel-checked event-list checker `linkB` with proved soundness (`linkB_sound`). The
witness parameters: B's controller node is read off the run as the output request one tick
earlier (`cL y.rq`); LUT band `[1, 1]`; feedback wire `[1, 1]` (the feedback pin is the
output request trace itself); both outgoing wires `[1, 1]`; B's reset `R = 2`;
`Es = Ea = 3`; `ρ`, `α` read off the request and acknowledge event lists. The checker
verifies: `i.ack` and `o.req` have the same event list; the real `bd_c2n` LUT relation at
every tick (`[0, 480]` decided, constant after); the latch data fields at every tick; the
lists sorted; H_SND and H_RCV per phase (each node edge is `cph j + 1`). 34 of the 175
links never see a request (`idle_links`, the `n = 0` case). The Python pre-check found the
true minimum slacks to be `Es = 19`, `Ea = 3`.

`gcd_hw_fin_links_witness`: `chW` meets all hypotheses of `gcd_hw_safe_fin_links` together
(H_OTHER from C's `w_cells`, H_BUNDLE `w_held`, H_CM_FORCED from C's `gcd_hw_forced` with
the token run `yW`), and out0 latches a token carrying 6. `gcd_hw_fin_links_consistent`
applies the theorem to it. `chW_fin_not_phys`: on the same run `FPhysLink` holds on every
link while `PhysLink` fails on every channel pair. So the link-class theorem now has a joint
non-vacuity witness on a real terminating gcd run.

Other witnesses: `fcelG_witness(_lutFb)` (real `bd_c2`: pins rise once at 3 and 4 and
disagree at 3, node rises once at 5); `flink_link_witness(_env)` (one-token hand-over: A
rises at 5, B at 7, then quiet).

Degenerate parts, stated: the gcd witness is C's unit-delay simulation, so every B window is
met at width 0 (`lo = hi`), not at a prjxray band; `R = 2` is B's per-link reset, chosen for
the run (C's model has no reset line); the two small witnesses use unit delays and one
edge per signal.

## Axioms

`#print axioms` (`/tmp/claude-0/probes/Bfin/Ax.lean`): every headline theorem uses
propext, Classical.choice, Quot.sound; `idle_links` uses propext only. No sorry, admit,
native_decide.
