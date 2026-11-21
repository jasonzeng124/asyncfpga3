"""BDC_AUTO=1: the hand recipes' storage choices as rules over the graph, with no instance named.

research/data/auto/README.md has the inventory this replaces and the evidence for each rule.  Off (unset or not "1"),
nothing here is called and bdc/emit.py's output is byte-identical to before this file existed.

What the event-graph search (research/tools/eventgraph/search.py) picked, per kernel, and the structure behind it:

  BDC_MERGE_OUT_LINK=ucontrol_merge0, BDC_MERGE_RES_LINK=ucontrol_merge0 (xorshift, collatz, collatz64, ipow):
      ucontrol_merge0 is, on all four, the arbitrated control_merge at the loop header: one input from the loop's entry,
      one from its own loop-back steer.  The arbiter's output cannot return to zero before its granted input does, and
      its output fork's acknowledge waits for the loop steer, which waits for the loop test.  Rule M:
      every arbitrated control_merge (2+ inputs) that lies on a cycle of the node graph (a loop header).
  BDC_FORK_OUT_LINK=n11__0 (xorshift):
      %11 = fork(mux2) is the loop-carried rounds value; %11#0 goes straight into its loop-back steer (cond_br8, data)
      and %11#1 into the loop test (cmpi1), whose result is that same steer's condition.  The fork's acknowledge waits
      for the steer's join, which waits for the test computed from the fork's other branch: the fork's return to zero
      rides the whole test.  Rule F: in a loop, a fork output read DIRECTLY as the data of a cond_br whose condition is
      reachable from a sibling output of the same fork without passing a mux / merge / control_merge / cond_br
      (inside one iteration).
  BDC_RING_COUNT_OLINKS=1: the ring floor counts the storage rule M adds (it is storage; the 3-stage floor holds).
  BDC_LINK_DEPTHS=ulink_n_trueResult_8=2 (xorshift only): NOT a rule here.  See the README: kernel-specific.
"""
import collections
import os
import re

AUTO = os.environ.get("BDC_AUTO", "0") == "1"

BARRIER_OPS = ("mux", "merge", "control_merge", "cond_br")
MEM_OPS = ("load", "store", "mem_controller", "lsq")


def _sccs(func):
    """node index -> True when the node is on a cycle of the node graph."""
    adj = collections.defaultdict(set)
    for i, node in enumerate(func.nodes):
        for r in node.results:
            for (c, _k) in func.consumers.get(r, []):
                adj[i].add(c)
    n = len(func.nodes)
    # iterative Tarjan
    index, low, onst, st, out, cnt = {}, {}, set(), [], {}, [0]
    for root in range(n):
        if root in index:
            continue
        work = [(root, iter(sorted(adj[root])))]
        index[root] = low[root] = cnt[0]; cnt[0] += 1; st.append(root); onst.add(root)
        while work:
            v, it = work[-1]
            pushed = False
            for w in it:
                if w not in index:
                    index[w] = low[w] = cnt[0]; cnt[0] += 1; st.append(w); onst.add(w)
                    work.append((w, iter(sorted(adj[w])))); pushed = True; break
                if w in onst:
                    low[v] = min(low[v], index[w])
            if pushed:
                continue
            work.pop()
            if work:
                low[work[-1][0]] = min(low[work[-1][0]], low[v])
            if low[v] == index[v]:
                comp = []
                while True:
                    w = st.pop(); onst.discard(w); comp.append(w)
                    if w == v:
                        break
                cyc = len(comp) > 1 or v in adj[v]
                for w in comp:
                    out[w] = cyc
    return out


def has_memory(func):
    return any(node.op in MEM_OPS for node in func.nodes)


def loop_header_merges(func, instname):
    """Rule M: instance names of the arbitrated control_merges that are on a cycle."""
    cyc = _sccs(func)
    return {instname(node, i) for i, node in enumerate(func.nodes)
            if node.op == "control_merge" and len(node.operands) >= 2 and cyc.get(i)}


def _reach_cond(func, starts, target):
    """True when value `target` is computed from any value in `starts` within one iteration: forward over consumers,
    not through a BARRIER op (the next iteration starts there)."""
    seen, todo = set(), list(starts)
    while todo:
        v = todo.pop()
        if v == target:
            return True
        if v in seen:
            continue
        seen.add(v)
        for (c, _k) in func.consumers.get(v, []):
            node = func.nodes[c]
            if node.op in BARRIER_OPS:
                continue
            todo.extend(node.results)
    return False


def steer_fork_outputs(func, vname):
    """Rule F: Verilog base names of fork outputs to latch."""
    cyc = _sccs(func)
    out = set()
    for i, node in enumerate(func.nodes):
        if node.op not in ("fork", "lazy_fork") or not cyc.get(i):
            continue
        for r in node.results:
            for (c, k) in func.consumers.get(r, []):
                cb = func.nodes[c]
                if cb.op != "cond_br" or k != 1:      # operand 0 is the condition, 1 the data
                    continue
                cond = cb.operands[0]
                sibs = [s for s in node.results if s != r]
                if _reach_cond(func, sibs, cond):
                    out.add(vname(r))
    return out


# ---- MLIR rewrites that have a proof ------------------------------------------------------------------------------
# A rewrite is applied only when its OUTPUT is byte-for-byte a file formal proved function-preserving (formal
# FOR-RESEARCH A6, Lean, every input: Formal.Rewrite.{XorshiftPredec.same_as_original, Collatz.same, Collatz64.same}).
# The pattern matchers themselves (research/tools/fifteen/pre_dec.py, pre_eq2.py) only ever match one kernel each, so
# this is "every proven rewrite is applied where it applies", not a general pass; the README says what a general one
# would need.
PROVEN = {
    "c3c2c89294cb8179033b51e00fc2b14b": "pre_dec (xorshift; formal A6 XorshiftPredec.same_as_original)",
    "98a5a519a519b1fce11851c9aeec9b34": "pre_eq2 (collatz; formal A6 Collatz.same)",
    "736d600347daa29e7c2128dab10d5008": "pre_eq2 (collatz64; formal A6 Collatz64.same)",
}
REWRITES = ("pre_dec.py", "pre_eq2.py")


# OFF unless BDC_AUTO_REWRITES=1 (owner, 2026-11-18, auditor T156): PROVEN is a list of three kernels' output files and
# the matchers match one kernel each, so applying them is a per-kernel setting, which the automatic path must not carry.
# BDC_AUTO=1 alone (the automatic column) copies the MLIR unchanged; BDC_AUTO_REWRITES=1 is the named variant "with the
# three proven rewrites" (every automatic route built before this change, board items 39-41 included, used it). A rewrite
# comes back into the automatic path as a PASS: a structure matched on any kernel, the pass proved, not an output file.
REWRITES_ON = os.environ.get("BDC_AUTO_REWRITES", "0") == "1"


def rewrite_mlir(src_path, dst_path, log=print):
    """Apply each proven rewrite whose output is in PROVEN; write the result (or the input unchanged) to dst_path."""
    import hashlib, shutil, subprocess, sys, tempfile
    if not REWRITES_ON:
        shutil.copyfile(src_path, dst_path)
        log("auto: MLIR rewrites off (BDC_AUTO_REWRITES=1 applies the three md5-keyed proven rewrites)")
        return []
    here = os.path.dirname(os.path.abspath(__file__))
    tools = os.path.join(here, "..", "research", "tools", "fifteen")
    cur = open(src_path, "rb").read()
    applied = []
    for rw in REWRITES:
        if not os.path.exists(os.path.join(tools, rw)):
            # a copy of bdc/ without research/tools/fifteen (research/data/alltable/run_default.sh's tree) skipped
            # every rewrite silently and built a different circuit under the same switch (suitek, 2026-11-18)
            raise SystemExit(f"auto: rewrite script {os.path.join(tools, rw)} not found: BDC_AUTO=1 needs "
                             "research/tools/fifteen beside bdc/ (refusing to build without its proven rewrites)")
        with tempfile.TemporaryDirectory() as td:
            a, b = os.path.join(td, "in.mlir"), os.path.join(td, "out.mlir")
            open(a, "wb").write(cur)
            p = subprocess.run([sys.executable, os.path.join(tools, rw), a, b], capture_output=True, text=True)
            if p.returncode != 0 or not os.path.exists(b):
                continue
            new = open(b, "rb").read()
            md5 = hashlib.md5(new).hexdigest()
            if md5 in PROVEN:
                cur = new; applied.append(PROVEN[md5])
            else:
                log(f"auto: {rw} matched but its output {md5} has no proof: not applied")
    open(dst_path, "wb").write(cur)
    log("auto: MLIR rewrites applied: " + ("; ".join(applied) if applied else "none"))
    return applied


if __name__ == "__main__":
    import sys
    if len(sys.argv) == 3:
        rewrite_mlir(sys.argv[1], sys.argv[2], log=lambda s: print(s, file=sys.stderr))
    else:
        sys.exit("usage: auto.py IN.mlir OUT.mlir   (the proven MLIR rewrites; storage rules run inside emit.py)")
