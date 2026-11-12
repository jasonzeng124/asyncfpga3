"""C's 465 CapstoneNet channels -> gNet nodes (shard B, probe Bmap). Called as
`gcdnet_gen.py map OUTDIR LEANOUT` after `gcdnet_gen.py net OUTDIR`.

C's channel list is rebuilt by running C's own generator, formal/lean/Wip/C8m/netgen.py
(read-only; it runs bdc's parser and fusion plan through formal/tools/dfimport/mlir2lean.py),
in-process with its output redirected to OUTDIR/CapstoneNet.regen.lean, which is compared
with the committed formal/lean/Formal/Net/CapstoneNet.lean. Its `chans`, `members`, `links`,
`rules` give, per circuit channel, the RTL nets bdc's emit.py names for it:

* `gR.k` (segment k of the group whose source GcdHw channel is R): the group's members are
  R and possibly the output of one zero-delay comp (trunci/constant/extui, emitted by bdc as
  plain `assign`s). Member m with L = links[m] stages has the segments
  `vname(m)_u` (producer side, when L > 0), `ulink_vname(m).many.{r,a}[i]` (i = 1..L-1,
  inside a bd_pipe), `vname(m)` (consumer side). The group's segments are member 0's, then
  member 1's, with member 0's consumer side and member 1's producer side being ONE channel
  (both nets must resolve to the same node; checked);
* `jL` (branch rule L's joined channel): `u<cond_br name>_req` / `_ack` (the bd_join output
  that the bd_steer consumes);
* `zR` / `accR` (control_merge with result R): the bdc_amerge instance's `z_req` / `z_ack`,
  and for the 3-input cascade the internal `acc1_req` / `acc1_ack`.

A channel's request (acknowledge) node is the gNet node driving that net through pure
aliases (gcdnet_gen's net -> node table). A node is what C's wire is identified with (H_MAP's
reading: C's wire = the driver's output; the per-pin GMW lag is the reader's own).
"""
import json
import os
import re
import runpy
import sys

HERE = os.path.dirname(os.path.abspath(__file__))
ROOT = os.path.abspath(os.path.join(HERE, "..", ".."))
ONES = [0, 287, 308, 533, 606, 627, 825, 846, 1192, 1378, 1399, 1583, 1658, 1664, 3256, 3257, 3275]


def vname(ssa):  # bdc/emit.py's vname, imported to avoid a copy
    sys.path.insert(0, os.path.join(ROOT, "bdc"))
    import emit
    return emit.vname(ssa)


def run_netgen(outdir):
    dst = os.path.join(outdir, "CapstoneNet.regen.lean")
    saved = sys.argv
    sys.argv = ["netgen.py", dst]
    try:
        G = runpy.run_path(os.path.join(ROOT, "formal/lean/Wip/C8m/netgen.py"), run_name="netgen")
    finally:
        sys.argv = saved
    same = open(dst).read() == open(os.path.join(ROOT, "formal/lean/Formal/Net/CapstoneNet.lean")).read()
    return G, same


def chan_nets(G):
    g, chans, members, links, rules, src_of = G["g"], G["chans"], G["members"], G["links"], G["rules"], G["src_of"]
    K = "urig.udut."
    out = {}
    # groups
    em = g.em
    pre = {}
    for v in em.ch:
        pre.setdefault(g.A(v), []).append(v)
    for rep in sorted(members):
        segs = []
        for j, m in enumerate(members[rep]):
            L = links.get(m, 0)
            S = pre[g.chname[m]]
            lk = [v for v in S if v in em.linked]
            assert len(lk) == (1 if L > 0 else 0), (m, S, lk, L)
            ms = []
            if L > 0:
                x = vname(lk[0])
                assert em.depth.get(lk[0], 1) == L, (m, lk, L)
                ms.append([(K + x + "_u_req", K + x + "_u_ack")])
                for i in range(1, L):
                    ms.append([(K + f"ulink_{x}.many.r[{i}]", K + f"ulink_{x}.many.a[{i}]")])
                ms.append([(K + x + "_req", K + x + "_ack")])
                # the other SSA names of this GcdHw channel are plain assigns on one side
                side = [(K + vname(v) + "_req", K + vname(v) + "_ack") for v in S if v != lk[0]]
                ms[0] += [("?", t) for t in side]
            else:
                ms.append([(K + vname(v) + "_req", K + vname(v) + "_ack") for v in S])
            if j == 0:
                segs = ms
            else:  # zero-delay comp: member 0's consumer side = member 1's producer side
                segs[-1] = segs[-1] + ms[0]
                segs += ms[1:]
        names = [f"g{rep}.{k}" for k in range(len(segs))]
        nl = sum(links.get(c, 0) for c in members[rep])
        assert len(segs) == nl + 1, (rep, len(segs), nl)
        for nm, s in zip(names, segs):
            out[nm] = s
    for l, r in enumerate(rules):
        if r[0] == "branch":
            inst = "u" + r[5]
            out[f"j{l}"] = [(K + inst + "_req", K + inst + "_ack")]
    cms = {}
    for l, r in enumerate(rules):
        if r[0] == "cm":
            cms.setdefault(r[2], []).append(r[5].split(" input ")[0])
    for res, nms in cms.items():
        inst = K + "u" + nms[0]
        if len(nms) == 2:
            out[f"z{res}"] = [(inst + ".z_req", inst + ".z_ack")]
        elif len(nms) == 3:
            out[f"z{res}"] = [(inst + ".z_req", inst + ".z_ack")]
            out[f"acc{res}"] = [(inst + ".acc1_req", inst + ".acc1_ack")]
    return [(c, out[c]) for c in chans]


def resolve(segs_by_name, n2n):
    """'?' alternates (SSA names on either side of a link): put each with the segment of the
    same channel group whose request node it shares; it must share one."""
    res = []
    for nm, alts in segs_by_name:
        res.append([nm, [a for a in alts if a[0] != "?"], [a[1] for a in alts if a[0] == "?"]])
    byrep = {}
    for i, (nm, _, _) in enumerate(res):
        if nm.startswith("g"):
            byrep.setdefault(nm.split(".")[0], []).append(i)
    for i, (nm, alts, q) in enumerate(res):
        for t in q:
            hit = [j for j in byrep[nm.split(".")[0]] if n2n[res[j][1][0][0]] == n2n[t[0]]]
            assert len(hit) >= 1, (nm, t)
            res[hit[0]][1].append(t)
    return [(nm, alts) for nm, alts, _ in res]


def main(outdir, leanout):
    net = json.load(open(os.path.join(outdir, "net.json")))
    n2n = net["net2node"]
    names = {n["i"]: n["name"] for n in net["nodes"]}
    G, same = run_netgen(outdir)
    print(f"C's netgen.py regenerated CapstoneNet.lean: {'IDENTICAL to the committed file' if same else 'DIFFERS from the committed file'}")
    rows = []
    for c, (nm, alts) in enumerate(resolve(chan_nets(G), n2n)):
        rq = {n2n[a] for a, _ in alts}
        ak = {n2n[b] for _, b in alts}
        assert len(rq) == 1 and len(ak) == 1, (nm, alts, rq, ak)
        r, a = rq.pop(), ak.pop()
        assert isinstance(r, int) and isinstance(a, int), (nm, alts, r, a)
        rows.append((c, nm, r, a, alts[0]))
    NC = len(rows)
    hot = lambda c: c < 7
    bad = []
    for c, nm, r, a, _ in rows:
        ok = (r != 0 and a != 0 and (r in ONES) == hot(c) and (a in ONES) == (c == 3))
        if not ok:
            bad.append((c, nm, r, names[r], a, names[a]))
    print(f"map: {NC} channels; MapOK fails on {len(bad)}: {bad}")
    import collections
    cr = collections.Counter(r for _, _, r, _, _ in rows)
    print(f"distinct request nodes {len(cr)}, distinct acknowledge nodes {len({a for _, _, _, a, _ in rows})}")
    L = []
    w = L.append
    w("import Formal.Cells.ResetCapstone\n")
    w("/-!")
    w("# Probe Bmap: the C-channel -> gNet-node table (GENERATED)\n")
    w("Generated by `python3 -B formal/tools-B/gcdnet_gen.py net OUT && python3 -B")
    w("formal/tools-B/gcdnet_gen.py map OUT formal/lean/Formal/Cells/ResetCapstoneMapData.lean`")
    w(f"(bdc kernel sha256 `{net['kernel_sha256']}`). Do not edit by hand; see")
    w("`formal/notes/B-reset-capstone-map.md`.\n")
    w("Row `c` is C's circuit channel `c` (`CapNet.Gcd.chanNames`, checked below): the gNet node")
    w("driving its request wire and its acknowledge wire in the elaborated RTL, followed by the")
    w("RTL nets read (the gNet node's comment name in brackets).")
    w("-/\n")
    w("namespace Formal.Cells.ResetCapstoneMap\n")
    w("/-- C's channel names, in C's order (must equal `CapNet.Gcd.chanNames`). -/")
    w("def mapNames : List String := [" + ", ".join(f'"{nm}"' for _, nm, _, _, _ in rows) + "]\n")
    w("/-- Request node per channel. -/")
    w("def reqL : List Nat := [" + ", ".join(str(r) for _, _, r, _, _ in rows) + "]\n")
    w("/-- Acknowledge node per channel. -/")
    w("def ackL : List Nat := [" + ", ".join(str(a) for _, _, _, a, _ in rows) + "]\n")
    ops = G["ops"]
    R = [r for _, _, r, _, _ in rows]
    A = [a for _, _, _, a, _ in rows]
    RW = [3275 if c < 7 else 65 for c in range(NC)]
    AW = [3257 if c == 3 else 65 for c in range(NC)]
    out0 = 416
    crs, srcs = [], []
    for o in ops:
        if o[0] == "forkG":
            crs += list(o[2])
        elif o[0] == "forkH":
            crs += [x for x, _ in o[2]]
        elif o[0] == "src":
            srcs.append(o[1])

    def cas(R, A):
        out = []
        for o in ops:
            k = o[0]
            if k in ("join", "bjoin"):
                out += list(o[1])
            elif k == "sink":
                out += [] if o[1] in (out0, 3) else [o[1]]
            elif k in ("mux", "muxn"):
                out.append(o[1])
            elif k == "link":
                out += [o[1]] if A[o[1]] == R[o[2]] else []
        return out
    casT = cas(R, A)
    drv = [R[c] for c in range(NC) if c not in crs and c not in srcs] + [A[c] for c in range(NC) if c not in casT]
    assert len(set(drv)) == len(drv), "driven wires not injective"
    print(f"WireOK data: {len(crs)} fork-output requests, {len(casT)} copied acknowledges, {len(drv)} driven wires, injective")
    w("/-- Fork-output channels, in `ops` order (`ops.flatMap forkOuts`, checked). -/")
    w("def crsL : List Nat := [" + ", ".join(map(str, crs)) + "]\n")
    w("/-- Channels whose acknowledge is a copy, for `μT` (`ops.flatMap (copyAs μT)`, checked). -/")
    w("def casL : List Nat := [" + ", ".join(map(str, casT)) + "]\n")
    w("/-- The same for the witness map `μW` of ResetCapstone. -/")
    w("def casW : List Nat := [" + ", ".join(map(str, cas(RW, AW))) + "]\n")
    w("/-- The driven-wire nodes of `μT` (`drivenL μT`, checked). -/")
    w("def drvL : List Nat := [" + ", ".join(map(str, drv)) + "]\n")
    w("/-! Rows (channel: request node [driver] <- net ; acknowledge node [driver] <- net):")
    for c, nm, r, a, (rn, an) in rows:
        w(f"* {c} `{nm}`: {r} [{names[r]}] <- `{rn[len('urig.udut.'):] if rn.startswith('urig.udut.') else rn}` ; "
          f"{a} [{names[a]}] <- `{an[len('urig.udut.'):] if an.startswith('urig.udut.') else an}`")
    w("-/\n")
    w("end Formal.Cells.ResetCapstoneMap")
    open(leanout, "w").write("\n".join(L) + "\n")
    json.dump(dict(rows=[dict(c=c, name=nm, req=r, ack=a, nets=list(x)) for c, nm, r, a, x in rows]),
              open(os.path.join(outdir, "map.json"), "w"), indent=0)
    print(f"wrote {leanout}")
