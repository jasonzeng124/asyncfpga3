"""Exercise the route/accept search with deterministic timing oracles."""

import os
from pathlib import Path
import shutil
import subprocess

import pytest


@pytest.fixture
def flow(tmp_path):
    verify = tmp_path / "verify"
    verify.mkdir()
    (tmp_path / "rtl").mkdir()
    (tmp_path / "rtl/empty.v").write_text("")
    shutil.copy2(Path(__file__).with_name("resize.sh"), verify / "resize.sh")
    (verify / "soak_top.v").write_text("`define BD_SZ_TEST 96\n")
    driver = tmp_path / "flow.sh"
    driver.write_text("""#!/usr/bin/env bash
set -eu
mkdir -p "$BD_OUT"
cp "$BD_SIZES" "$BD_OUT/soak.sdf"
echo "seed ${NEXTPNR_SEED:-1}" >> "$BD_OUT/soak.sdf"
""")
    driver.chmod(0o755)
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
    (verify / "tighten.py").write_text(oracle)
    (verify / "skew.py").write_text(oracle)
    return tmp_path


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
