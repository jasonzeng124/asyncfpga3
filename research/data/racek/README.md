# The latch-fed steer race at formal's split corners: AUTO_RACE_KAPPA (2026-11-21)

**Why.** A latch-fed steer race (formal B21): a steer whose condition comes from a link's data latch, which opens when the
link's controller (ctl) rises, while its request runs from the same ctl through the link's request line and the steer's
join. Rule E does not size it, so v12's 10 % rule E guard does not reach it; the flow checks it with AUTO_RACE_Z=4.5 in
our draw model (research/tools/race_find.py / race_mc.py). Formal's census of every rule-CLEAN route of flows v10 / v11
(B32-B36) found this class the thinnest: v10 sqrtsub s4 (split slack +55 / +99 ps) and v11 test_flatten_array s2 (+1 /
+72 ps) lose its race-only adversary at kappa 0.03, although both passed our z check (test_flatten_array s2: 263 +- 56 ps,
z 4.72: both sides' routing share one band in our model; formal lets each side sit anywhere in its prjxray range).
Formal's ctl-term kappa_lo <= 0.125 predicted 9 of its 10 adversary failures inside kappa 0.20 (1 of 22 above 0.129).
The ring measurements' median model error is 8.5 %, so a failure at a few % is inside what our model cannot exclude.

**What.** research/tools/race_kappa.py: for every race race_find.py traces, kappa = min over the fast / slow corners of
(F - S) / (F + S), F = the request path at each arc's corner minimum, S = the condition path at its maximum -- formal's
"ctl term" (formal B37 confirms the definition). research/tools/auto/auto_size.sh AUTO_RACE_KAPPA=K (opt-in, with
AUTO_RACE_Z): a race below K pads its link's request line by race_kappa's element estimate (>= 1) and adds an R row (the
route is not clean), as a race below Z does.

**Checks.** race_kappa's split slacks against formal's published ones (B35): g10 lfsrfind s1 ucond_br4 +188 / +523 ps
here, +189 / +524 formal; g10 sqrtsub s1 +1763-1766 / +4169-4203 here, +1772 / +4212. race_pad.py without --kappa:
byte-identical outputs to the previous version on 33 saved race checks (Z 4.5 and Z 12).
static_local_routes.txt: kappa on the 30 local race checks under /tmp/bot/runs (mixed experiments): K = 0.13 would pad
one route of the 20 with races (sym2_spmv_1 race_6, 0.113).

**Not covered.** Formal B37: on 1046 of 1324 latch-held steer LUTs the binding term is a *feeder* term -- the compute's
own data path through the condition latch's D -> Q, against its matched line: rule A's pair (3 % residual guard at
our band corners), carried to a steer. Neither AUTO_GUARD_E nor AUTO_RACE_KAPPA reaches it; asked formal which adversary
failures it explains (FOR-FORMAL 19:06).

**Tests** (local; results below as they land): v10's environment + AUTO_RACE_KAPPA=0.13 on sqrtsub s4
(/tmp/bot/scripts/rk_launch.sh; control: v10's farm route sdf 89fc043c).
