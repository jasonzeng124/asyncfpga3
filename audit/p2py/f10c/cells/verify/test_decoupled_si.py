import pytest

from decoupled_si import Model, INTERNAL


@pytest.mark.parametrize("broad", [0, 1])
def test_clean_under_the_one_timing_assumption(broad):
    r = Model(broad=bool(broad), ldn=0, rt="env").explore()
    assert r["hazards"] == []
    assert r["protocol"] == []
    assert r["opacity"] == []
    assert r["deadlocks"] == []
    assert r["unreturned"] == []
    assert r["decoupled"]


@pytest.mark.parametrize("broad", [0, 1])
def test_every_pure_si_hazard_is_a_stale_lt(broad):
    # Without the assumption the controller is not speed-independent, and
    # the docstring's claim is that every failure needs lt to lag a whole
    # round trip: either lt itself is the stale gate, or the stale gate is
    # one that only Lt's staleness can have enabled (Ld set through a
    # spurious open, B through that Ld).
    r = Model(broad=bool(broad), ldn=0, rt="none").explore()
    assert r["protocol"] == []
    assert r["opacity"] == []
    assert r["deadlocks"] == []
    assert r["unreturned"] == []
    assert r["hazards"]
    m = Model(broad=bool(broad), ldn=0, rt="none")
    for s, k, other in r["hazards"]:
        n = m.nxt(s)
        stale_lt = n["Lt"] != s["Lt"]
        assert stale_lt, (s, k, other)


def test_ldn_chain_only_adds_flush_hazards():
    # LDN=1 puts the FASTFALL chain S on lt; the only new hazard class is
    # lt falling while S is still rising, which a flushable chain absorbs.
    base = Model(broad=True, ldn=0, rt="env").explore()
    withs = Model(broad=True, ldn=1, rt="env").explore()
    assert base["hazards"] == []
    kinds = {(k, other) for _, k, other in withs["hazards"]}
    assert kinds <= {("Lt", "S"), ("Lt", "Ld")}
    assert withs["protocol"] == [] and withs["opacity"] == []
    assert withs["deadlocks"] == [] and withs["unreturned"] == []


def test_internal_names_match_the_rtl():
    assert INTERNAL == ["B", "A", "R", "S", "Ld", "Lt"]
