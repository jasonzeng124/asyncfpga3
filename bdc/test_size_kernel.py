"""bdc/size_kernel.py's merge, headroom and verdict logic, without routing."""
import pytest

import size_kernel as sk

DUT = """
module bdc_x #(parameter DELAY_ULINK_N30__1 = 0,
               parameter DELAY_ULINK_N11__1 = 6,
               parameter DELAY_UXORI1 = 13)
"""


def test_sizes_round_trip(tmp_path):
    p = tmp_path / "t.vh"
    sk.write_sizes(p, {"BD_SZ_UUT_UXORI1": 9, "BD_SZ_UUT_A": 1}, "hdr")
    text = p.read_text()
    assert text.startswith("// hdr\n")
    assert sk.read_sizes(text) == {"BD_SZ_UUT_A": 1, "BD_SZ_UUT_UXORI1": 9}


def test_merge_is_per_cell_max_and_never_lowers():
    cur = {"BD_SZ_UUT_UXORI1": 10, "BD_SZ_UUT_UCMPI0": 20}
    props = [{"BD_SZ_UUT_UXORI1": 7, "BD_SZ_UUT_UCMPI0": 22},
             {"BD_SZ_UUT_UXORI1": 12, "BD_SZ_UUT_UCMPI0": 18}]
    new, _ = sk.merge(cur, props, [], DUT)
    assert new == {"BD_SZ_UUT_UXORI1": 12, "BD_SZ_UUT_UCMPI0": 22}
    # every proposal below current: nothing moves down
    new, log = sk.merge(cur, [{"BD_SZ_UUT_UXORI1": 1, "BD_SZ_UUT_UCMPI0": 1}], [], DUT)
    assert new == cur and log == []


def test_a_cell_not_yet_sized_takes_the_max_proposal_even_below_placeholder():
    # this is the tightening step: DELAY_UXORI1 = 13 in dut.v, routes say 9/11
    new, _ = sk.merge({}, [{"BD_SZ_UUT_UXORI1": 9}, {"BD_SZ_UUT_UXORI1": 11}], [], DUT)
    assert new == {"BD_SZ_UUT_UXORI1": 11}


def test_rule_e_ask_is_current_plus_n_plus_one():
    cur = {"BD_SZ_UUT_ULINK_N11__1": 6}
    asks = sk.skew_asks(
        "   fix: 2 more bd_delay element(s) on ulink_n11__1 (419 ps ea)\n"
        "   fix: 1 more bd_delay element(s) on ulink_n11__1 (419 ps ea)\n")
    assert asks == [("BD_SZ_UUT_ULINK_N11__1", 2), ("BD_SZ_UUT_ULINK_N11__1", 1)]
    new, _ = sk.merge(cur, [], asks, DUT)
    assert new["BD_SZ_UUT_ULINK_N11__1"] == 9          # max(6+2+1, 6+1+1)


def test_rule_e_ask_on_an_unsized_link_uses_the_dut_default():
    # the T2 -> T3 bug the scratch merge fixed: an ask on a link with no macro
    new, _ = sk.merge({}, [], [("BD_SZ_UUT_ULINK_N30__1", 6)], DUT)
    assert new == {"BD_SZ_UUT_ULINK_N30__1": 7}         # 0 + 6 + 1


def test_rule_e_ask_with_no_macro_and_no_default_is_an_error():
    with pytest.raises(ValueError):
        sk.merge({}, [], [("BD_SZ_UUT_ULINK_NOPE", 1)], DUT)


def test_rule_e_ask_never_lowers_a_bigger_proposal():
    new, _ = sk.merge({"BD_SZ_UUT_ULINK_N11__1": 6},
                      [{"BD_SZ_UUT_ULINK_N11__1": 15}],
                      [("BD_SZ_UUT_ULINK_N11__1", 1)], DUT)
    assert new["BD_SZ_UUT_ULINK_N11__1"] == 15


def test_headroom_touches_compute_cells_only():
    s = {"BD_SZ_UUT_UXORI1": 9, "BD_SZ_UUT_UCONTROL_MERGE0": 5,
         "BD_SZ_UUT_ULINK_N11__1": 9, "BD_SZ_UUT_ULINK_N11__1_UACK": 0,
         "BD_SZ_UUT_ULINK_N12__1_SDELAY": 2, "BD_SZ_UPIPE_SDELAY": 1}
    h = sk.headroom(s)
    assert h["BD_SZ_UUT_UXORI1"] == 10 and h["BD_SZ_UUT_UCONTROL_MERGE0"] == 6
    for k in ("BD_SZ_UUT_ULINK_N11__1", "BD_SZ_UUT_ULINK_N11__1_UACK",
              "BD_SZ_UUT_ULINK_N12__1_SDELAY", "BD_SZ_UPIPE_SDELAY"):
        assert h[k] == s[k]


def test_tighten_sections_enforce_everything_but_the_rule_d_screen():
    log = ("A. the request\n  x  VIOLATION\n"
           "D. the select\n  y  VIOLATION\n  z  VIOLATION\n"
           "F. a fast-fall line\n  w chain not traceable -- not audited\n")
    sec = sk.tighten_sections(log)
    assert sec == {"A": 1, "D": 2, "F": 1}


def test_seed_verdict(tmp_path):
    (tmp_path / "tighten.log").write_text("A. x\n  ok\nD. y\n  VIOLATION\n")
    (tmp_path / "skew.log").write_text("118 select gates, 118 measured, 0 violated\n")
    rec = {"audits": {"arb_fork": {"violations": 0}},
           "routed_gls": {"fast": "pass", "stalled": "pass"}}
    v, clean = sk.seed_verdict(tmp_path, rec)
    assert clean and v["D(screen)"] == 1 and v["E"] == 0
    rec["routed_gls"]["fast"] = "FAIL"
    assert not sk.seed_verdict(tmp_path, rec)[1]
    (tmp_path / "skew.log").write_text("118 select gates, 118 measured, 2 violated\n")
    rec["routed_gls"]["fast"] = "pass"
    assert not sk.seed_verdict(tmp_path, rec)[1]


def test_per_iteration_slope():
    # 100 ns per round plus a 20 ns intercept, in ps
    xs = [0, 1, 2, 4, 3]
    ys = [20000 + 100000 * x for x in xs]
    assert sk.slope_ns(xs, ys) == pytest.approx(100.0)
    assert sk.slope_ns([None, None, 1], [1, 2, 3]) is None
