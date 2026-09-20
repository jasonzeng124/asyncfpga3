"""Exercise the route/accept search with deterministic timing oracles."""

import os
from pathlib import Path
import shutil
import subprocess

import pytest


def make_flow(tmp_path, source, oracle):
    verify = tmp_path / "verify"
    verify.mkdir()
    (tmp_path / "rtl").mkdir()
    (tmp_path / "rtl/empty.v").write_text("")
    shutil.copy2(Path(__file__).with_name("resize.sh"), verify / "resize.sh")
    (verify / "soak_top.v").write_text(source)
    driver = tmp_path / "flow.sh"
    driver.write_text("""#!/usr/bin/env bash
set -eu
mkdir -p "$BD_OUT"
cp "$BD_SIZES" "$BD_OUT/soak.sdf"
echo "seed ${NEXTPNR_SEED:-1}" >> "$BD_OUT/soak.sdf"
""")
    driver.chmod(0o755)
    (verify / "tighten.py").write_text(oracle)
    (verify / "skew.py").write_text(oracle)
    return tmp_path


@pytest.fixture
def flow(tmp_path):
    oracle = """import os
from pathlib import Path
import sys

words = dict(line.split()[-2:] for line in Path(sys.argv[-1]).read_text().splitlines())
size = int(words["BD_SZ_TEST"])
seed = int(words["seed"])
if "--emit" in sys.argv:
    Path(sys.argv[sys.argv.index("--emit") + 1]).write_text("`define BD_SZ_TEST 1\\n")
threshold = int(os.environ.get("THRESHOLD", "10"))
threshold += seed - 1
mode = os.environ.get("FAILURE", "")
skew = Path(__file__).stem == "skew"
if (mode == "baseline-skew" and skew and size == 96) or (
    size < threshold and (skew if mode == "skew" else not skew)
):
    print("VIOLATION")
    sys.exit(1)
"""
    return make_flow(tmp_path, "`define BD_SZ_TEST 96\n", oracle)


# Two delays whose routes are coupled: while B is long, A needs 5; once B is
# shrunk below 50 the route moves and A needs 8.  B itself needs 6.  The
# search visits keys in sorted order, so A is sized first, to its exact 5.
COUPLED = """import sys
from pathlib import Path

words = dict(line.split()[-2:] for line in Path(sys.argv[-1]).read_text().splitlines())
a, b = int(words["BD_SZ_A"]), int(words["BD_SZ_B"])
need_a, need_b = (8 if b < 50 else 5), 6
if "--emit" in sys.argv:
    Path(sys.argv[sys.argv.index("--emit") + 1]).write_text(
        f"`define BD_SZ_A {need_a}\\n`define BD_SZ_B {need_b}\\n")
if Path(__file__).stem == "tighten" and (a < need_a or b < need_b):
    print("VIOLATION")
    sys.exit(1)
"""


def run_coupled(tmp_path, source, oracle=COUPLED):
    flow = make_flow(tmp_path, source, oracle)
    out = flow / "build"
    result = subprocess.run(
        ["bash", str(flow / "verify/resize.sh")], text=True, capture_output=True,
        env={**os.environ, "BD_OUT": str(out)}, timeout=30,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    sizes = dict(line.split()[-2:]
                 for line in (out / "resize/sizes.vh").read_text().splitlines()
                 if line.startswith("`define"))
    return result.stdout, sizes, out


def test_veto_by_another_delay_pads_it_instead_of_reverting(tmp_path):
    # Every shrink of B breaks A.  Without repair B parks at 50, the smallest
    # length that leaves A's route alone; with it A takes the 3 links the new
    # route asks for and B gets its 6.
    stdout, sizes, out = run_coupled(
        tmp_path, "`define BD_SZ_A 96\n`define BD_SZ_B 96\n")
    assert sizes == {"BD_SZ_A": "8", "BD_SZ_B": "6"}
    assert "A                     5 -> 8   padded" in stdout
    assert "B                    96 -> 6   kept" in stdout
    assert (out / "resize/tighten_final.log").exists()
    assert "VIOLATION" not in (out / "resize/tighten_final.log").read_text()


def test_veto_by_another_delay_on_a_confirmation_seed_pads_it_too(tmp_path):
    # Same coupling, but A only comes up short on the second confirmation
    # route.  The tried delay B held on every route, so the answer is still
    # to pad A -- not to park B at 50 as if B's own length had been refuted.
    flow = make_flow(tmp_path, "`define BD_SZ_A 96\n`define BD_SZ_B 96\n",
                     COUPLED.replace(
                         "need_a, need_b = (8 if b < 50 else 5), 6",
                         "seed = int(words['seed'])\n"
                         "need_a, need_b = (8 if b < 50 and seed == 2 else 5), 6"))
    out = flow / "build"
    result = subprocess.run(
        ["bash", str(flow / "verify/resize.sh")], text=True, capture_output=True,
        env={**os.environ, "BD_OUT": str(out), "BD_RESIZE_SEEDS": "3"}, timeout=60,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    sizes = dict(line.split()[-2:]
                 for line in (out / "resize/sizes.vh").read_text().splitlines()
                 if line.startswith("`define"))
    assert sizes == {"BD_SZ_A": "8", "BD_SZ_B": "6"}
    assert "A                     5 -> 8   padded" in result.stdout
    for s in (2, 3):
        assert "VIOLATION" not in (out / f"resize/tighten_final_s{s}.log").read_text()


def test_padded_route_asking_for_more_is_padded_again(tmp_path):
    # A's need depends on its own length once B has moved the route: at 5 it
    # asks for 8, at 8 it asks for 9 (the padded route is a new route).  One
    # round of repair parks B at 50; the second round lands A at 9.
    stdout, sizes, _ = run_coupled(
        tmp_path, "`define BD_SZ_A 96\n`define BD_SZ_B 96\n",
        COUPLED.replace("(8 if b < 50 else 5)",
                        "(5 if b >= 50 else 8 if a < 8 else 9)"))
    assert sizes == {"BD_SZ_A": "9", "BD_SZ_B": "6"}
    assert "A                     5 -> 9   padded" in stdout
    assert "B                    96 -> 6   kept" in stdout


def test_repair_rounds_are_bounded(tmp_path):
    # A asks for one more link on every padded route, without end; the
    # search must stop trying after BD_RESIZE_REPAIR_ROUNDS and park B.
    flow = make_flow(tmp_path, "`define BD_SZ_A 96\n`define BD_SZ_B 96\n",
                     COUPLED.replace("(8 if b < 50 else 5)",
                                     "(5 if b >= 50 else a + 1)"))
    out = flow / "build"
    result = subprocess.run(
        ["bash", str(flow / "verify/resize.sh")], text=True, capture_output=True,
        env={**os.environ, "BD_OUT": str(out), "BD_RESIZE_REPAIR_ROUNDS": "2"},
        timeout=60,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    sizes = dict(line.split()[-2:]
                 for line in (out / "resize/sizes.vh").read_text().splitlines()
                 if line.startswith("`define"))
    assert sizes == {"BD_SZ_A": "5", "BD_SZ_B": "50"}
    assert "padded" not in result.stdout
    assert (out / "resize/flow_try_BD_SZ_B_6_r2.log").exists()
    assert not (out / "resize/flow_try_BD_SZ_B_6_r3.log").exists()


def test_pad_that_costs_more_than_the_shrink_saves_is_a_veto(tmp_path):
    # B's placeholder is 52, so its shrink to 6 saves 46 links, and A asks
    # for 55 more once the route moves.  The descent must refuse that trade
    # and settle where A's route is left alone.
    stdout, sizes, _ = run_coupled(
        tmp_path, "`define BD_SZ_A 96\n`define BD_SZ_B 52\n",
        COUPLED.replace("(8 if b < 50 else 5)", "(60 if b < 50 else 5)"))
    assert sizes == {"BD_SZ_A": "5", "BD_SZ_B": "50"}
    assert "padded" not in stdout


@pytest.mark.parametrize("failure", ["timing", "skew"])
@pytest.mark.parametrize("seeds", [1, 3])
def test_failed_shrink_recovers_intermediate_length(flow, failure, seeds):
    out = flow / "build"
    result = subprocess.run(
        ["bash", str(flow / "verify/resize.sh")], text=True, capture_output=True,
        env={**os.environ, "BD_OUT": str(out), "FAILURE": failure,
             "BD_RESIZE_SEEDS": str(seeds)}, timeout=30,
    )
    assert result.returncode == 0, result.stdout + result.stderr
    sizes = (out / "resize/sizes.vh").read_text()
    assert int(sizes.split()[-1]) == 10 + seeds - 1
    assert (out / "soak.sdf").read_text().startswith(sizes)
    assert (out / "resize/skew_final.log").exists()
    if seeds > 1:
        assert (out / f"resize/skew_final_s{seeds}.log").exists()


def test_baseline_skew_failure_stops_search(flow):
    result = subprocess.run(
        ["bash", str(flow / "verify/resize.sh")], text=True, capture_output=True,
        env={**os.environ, "BD_OUT": str(flow / "build"),
             "FAILURE": "baseline-skew", "BD_RESIZE_SEEDS": "3"}, timeout=30,
    )
    assert result.returncode != 0
    assert "baseline routes and passes" not in result.stdout
