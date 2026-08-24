"""compute_fusion must refuse a value that has more than one consumer.

BDC_CONST_FOLD's two load-bearing questions -- "who eats this constant" and
"does this member's result leave the region" -- were both answered from a
first-consumer map built with setdefault, which keeps whichever consumer
happens to come first in node order and discards the rest.  Both answers are
wrong in the same silent way when a value is read twice: a constant gets
absorbed into one reader and deleted out from under the other, and a member
whose result is read both inside and outside the region is mistaken for purely
internal, so the region emits without that output.

The premise that makes fusion sound is that --handshake-materialize gives
every value exactly one consumer, forking wherever a value is read twice.
These tests are the negative control for that premise: they hand fusion a
graph where it is false and require it to decline.  A test that only ever ran
on real Dynamatic output could not distinguish "fusion checks this" from
"Dynamatic happens never to produce it".
"""
import os
import sys

sys.path[:0] = [os.path.join(os.path.dirname(__file__)),
                os.path.join(os.path.dirname(__file__), "hs")]
os.environ["BDC_CONST_FOLD"] = "1"
import emit  # noqa: E402


class N:
    """The only surface compute_fusion touches on a node."""
    def __init__(self, op, operands=(), results=(), attrs=None, line=0):
        self.op = op
        self.operands = list(operands)
        self.results = list(results)
        self.attrs = attrs or {}
        self.src_line = line


class F:
    def __init__(self, nodes):
        self.nodes = nodes


def _graph(extra_reader_of=None):
    """source -> constant -> xori, with an optional second reader of the
    constant.  The xori is fusable, so with one reader the constant folds."""
    nodes = [
        N("source", results=["s0"]),
        N("constant", operands=["s0"], results=["c0"], attrs={"value": 13}),
        N("source", results=["s1"]),
        N("constant", operands=["s1"], results=["x0"], attrs={"value": 7}),
        N("xori", operands=["x0", "c0"], results=["y"]),
        N("sink", operands=["y"]),
    ]
    if extra_reader_of is not None:
        nodes.append(N("sink", operands=[extra_reader_of]))
    return F(nodes)


def _absorbed(plan):
    return 1 in plan.skip


def test_single_consumer_constant_is_absorbed():
    plan = emit.compute_fusion(_graph())
    assert _absorbed(plan), (
        "a constant with exactly one fusable consumer must still fold -- "
        "if this fails the check is too strict and BDC_CONST_FOLD does "
        "nothing")


def test_shared_constant_is_not_absorbed():
    plan = emit.compute_fusion(_graph(extra_reader_of="c0"))
    assert not _absorbed(plan), (
        "a constant read by two nodes was absorbed anyway; absorbing deletes "
        "its channel, so the second reader is left waiting on a wire nobody "
        "drives")


def test_region_result_read_outside_is_caught():
    """The other half: a member's result read both inside and outside.

    `a` feeds the second xori (inside the region) AND a sink (outside).  The
    region already had an assert for "exactly one external result" -- but it
    counted external results through the first-consumer map, so when the
    inside reader sorted first the outside one was invisible and the assert
    passed on a region that was about to drop `a`.  The check below is the
    same assert; what changed is that it can now see the case it was written
    for.  `_old_sink_count` reproduces the previous accounting to show the
    difference is real and not a rename.
    """
    nodes = [
        N("source", results=["s0"]), N("constant", operands=["s0"],
                                       results=["k0"], attrs={"value": 1}),
        N("source", results=["s1"]), N("constant", operands=["s1"],
                                       results=["k1"], attrs={"value": 2}),
        N("xori", operands=["in", "k0"], results=["a"]),
        N("xori", operands=["a", "k1"], results=["b"]),
        N("sink", operands=["b"]),
        N("sink", operands=["a"]),          # the outside reader
    ]

    # What the first-consumer map used to say.
    first = {}
    for i, n in enumerate(nodes):
        for o in n.operands:
            first.setdefault(o, i)
    members = {4, 5}
    old_sinks = [i for i in members if first.get(nodes[i].results[0]) not in members]
    assert len(old_sinks) == 1, (
        "this test is pointless unless the OLD accounting saw only one "
        f"external result here; it saw {len(old_sinks)}")

    try:
        emit.compute_fusion(F(nodes))
    except emit.EmitError as e:
        assert "external result" in str(e), f"wrong EmitError: {e}"
        return
    raise AssertionError(
        "fusion accepted a region whose member result is read from outside; "
        "that output is dropped and the outside reader references a net that "
        "is never emitted")


if __name__ == "__main__":
    fails = 0
    for name, fn in sorted(globals().items()):
        if not name.startswith("test_"):
            continue
        try:
            fn()
            print(f"PASS  {name}")
        except AssertionError as e:
            fails += 1
            print(f"FAIL  {name}\n      {e}")
    print(f"\n{fails} failure(s)")
    sys.exit(1 if fails else 0)
