#!/usr/bin/env bash
# C-witgen: the generated Lean data equals the generators' output (exit 1 on drift).
set -euo pipefail
cd "$(dirname "$0")"
python3 gen_genwit.py --check
python3 gen_genwit.py ipow --check
python3 gen_neg3.py --check
