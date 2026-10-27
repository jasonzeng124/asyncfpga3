# C-12c: zone-based timed-automata checking (TChecker)

Status: IN PROGRESS (notes kept current as work proceeds).

## Tool acquisition (2026-10-27)

- `git clone --depth 1 https://github.com/ticktac-project/tchecker` into the
  scratchpad (`$S/ext/tchecker`): **works** (the clone was the route 12b could
  not try). Commit d711ace9ff754d8d952f5d491a31591115300c7f (2025-12-09).
- apt: flex 2.6.4, libboost-all-dev 1.83.0, catch2 3.4.0 installed; bison
  3.8.2, cmake 3.28.3, g++ (Ubuntu 24.04) already present.
- Build: cmake Release, `make -j2 install` into
  `formal/tools/zone/build/tchecker/` (gitignored `build/`).
